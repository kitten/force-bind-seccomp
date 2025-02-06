/*************************************************************************\
*                  Copyright (C) Michael Kerrisk, 2019.                   *
*                                                                         *
* This program is free software. You may use, modify, and redistribute it *
* under the terms of the GNU General Public License as published by the   *
* Free Software Foundation, either version 3 or (at your option) any      *
* later version. This program is distributed without any warranty.  See   *
* the file COPYING.gpl-v3 for details.                                    *
\*************************************************************************/

/* seccomp_user_notification.c

   Demonstrate the seccomp notification-to-user-space feature added in
   Linux 5.0.

   This program creates two child processes, the "target" and the "tracer".

   The target process uses seccomp(2) to install a BPF filter using the
   SECCOMP_FILTER_FLAG_NEW_LISTENER flag. This flag causes seccomp(2) to return
   a file descriptor that can be used to receive notifications when the filter
   performs a return with the action SECCOMP_RET_USER_NOTIF; the BPF filter
   employed in this example performs such a return when the target process
   calls mkdir(2).

   The target process passes the notification file descriptor returned by
   seccomp(2) to the tracer process via a UNIX domain socket.

   The target process then performs a series of mkdir(2) calls using the
   pathnames supplied as command-line arguments to the program. The effect
   of each SECCOMP_RET_USER_NOTIF action triggered by these system calls is:

   (a) the mkdir(2) system call in the target process is *not* executed;
   (b) a notification is generated on the notification file descriptor;
   (c) the target process remains blocked in the mkdir(2) system call until
       a response is sent on the notification file descriptor (this response
       will include information for a "faked" return value for the mkdir(2)
       call--either a success return value, or a -1 error return with a value
       to be assigned to 'errno').

   The tracer process receives the notification file descriptor that was sent
   by the target process over the UNIX domain socket. It then waits for
   notifications using the SECCOMP_IOCTL_NOTIF_RECV ioctl(2) operation. Each
   of these notifications returns a structure that includes the PID of the
   target process, and information (the same 'struct seccomp_data' that a
   seccomp BPF filter receives) describing the target process's system call.
   In this example program, these notifications will relate to the mkdir(2)
   calls made by the target process.

   From user space, the tracer is able to do some things that an in-kernel
   seccomp BPF filter can't do; in particular, it can inspect the target
   process's memory (via /proc/PID/mem) in order to find out the values
   referred to by pointer arguments (e.g., the pathname argument of mkdir(2)).
   The tracer then makes a decision based on the pathname, creating the
   specified directory on behalf of the target process only if the pathname
   starts with ("/tmp/").

   The tracer then performs a SECCOMP_IOCTL_NOTIF_SEND ioctl(2) operation,
   which provides a response for the target process's system call. This
   response can specify either a success return value for the system call, or
   an error return, including a value that will be placed in 'errno' in the
   target process.
*/
#define _GNU_SOURCE
#include <sys/types.h>
#include <sys/ptrace.h>
#include <sys/prctl.h>
#if defined(__x86_64__)
#include <sys/reg.h>
#include <sys/user.h>
#elif defined(__aarch64__)
#include <sys/user.h>
#include <sys/uio.h>
#include <asm/ptrace.h>
#include <asm/unistd.h>
#include <elf.h> /* For NT_PRSTATUS */
#endif
#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <sys/wait.h>
#include <stddef.h>
#include <stdbool.h>
#include <linux/audit.h>
#include <sys/syscall.h>
#include <sys/stat.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <sys/ioctl.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>
#include "scm_functions.h"

#ifndef NT_PRSTATUS
#define NT_PRSTATUS 1
#endif

#if defined(__x86_64__)
#define SC_NUMBER  (8 * ORIG_RAX)
#define SC_RETCODE (8 * RAX)
#elif defined(__aarch64__)
  /* On aarch64, the system call number is stored in x8 and the return value is in x0.
     Each register is 8 bytes; thus the offset for x8 is 8*8 and for x0 is 8*0. */
#define SC_NUMBER  (8 * 8)
#define SC_RETCODE (8 * 0)
#else
#define SC_NUMBER  (4 * ORIG_EAX)
#define SC_RETCODE (4 * EAX)
#endif

#if defined(__x86_64__)
#define ORIG_SYSCALL(regs) ((regs).orig_rax)
#elif defined(__aarch64__)
  /* For aarch64, the system call number is in regs[8] and return value in regs[0]
     where regs is an array in struct user_pt_regs. */
#define ORIG_SYSCALL(regs) ((regs).regs[8])
#endif

#include "ip_funcs.h"

#define errExit(msg)    do { perror(msg); exit(EXIT_FAILURE); \
                        } while (0)

static int
seccomp(unsigned int operation, unsigned int flags, void *args)
{
    return syscall(__NR_seccomp, operation, flags, args);
}

struct replaced_fds;
struct replaced_fds {
    int                  fd;
    struct replaced_fds *next;
};

/* Values from command-line options */

struct mapping;

struct mapping {
    struct sockaddr *addr;
    int prefix;
    struct sockaddr *replacement;
    int replacement_fd;
    struct mapping *next;
};

struct cmdLineOpts {
    bool require_ptrace;
    bool prevent_listen;
    bool quiet;
    bool verbose;
    struct mapping *map;
};

static int matchAllAddr(const struct mapping *map, struct sockaddr *sa, int *newfd, const struct cmdLineOpts *opts);

/* The following is the architecture-specific BPF boilerplate code for checking that
   the BPF program is running on the right architecture and ABI. At completion of these
   instructions, the accumulator contains the system call number. */

/* For x86-64 with the x32 ABI, all system call numbers have bit 30 set */
#define X32_SYSCALL_BIT         0x40000000

#define ARCH_CHECK_AND_LOAD_SYSCALL_NR                                                            \
        BPF_STMT(BPF_LD | BPF_W | BPF_ABS, (offsetof(struct seccomp_data, arch))),                \
        /* If architecture is AArch64, jump directly to the AArch64 block */                      \
        BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, AUDIT_ARCH_AARCH64, 6, 0),                            \
        /* Else if architecture is x86-64, jump to the x86 block (which performs an x32 check) */ \
        BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, AUDIT_ARCH_X86_64, 1, 0),                             \
        /* Unrecognized architecture: kill the process */                                         \
        BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_KILL_PROCESS),                                      \
        /* x86-64 block: load system call number */                                               \
        BPF_STMT(BPF_LD | BPF_W | BPF_ABS, (offsetof(struct seccomp_data, nr))),                  \
        /* For x86-64: if the system call number has the x32 bit set, kill the process */         \
        BPF_JUMP(BPF_JMP | BPF_JGE | BPF_K, X32_SYSCALL_BIT, 0, 1),                               \
        BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_KILL_PROCESS),                                      \
        /* Skip over the AArch64 block if coming from the x86-64 block */                         \
        BPF_JUMP(BPF_JMP | BPF_JA, 0, 0, 1),                                                      \
        /* AArch64 block: load system call number (no x32 check needed) */                        \
        BPF_STMT(BPF_LD | BPF_W | BPF_ABS, (offsetof(struct seccomp_data, nr)))

/* installNotifyFilter() installs a seccomp filter that generates user-space
   notifications (SECCOMP_RET_USER_NOTIF) when the process calls bind(2) or listen(2);
   all other system calls are allowed.
   The function returns a file descriptor from which the user-space notifications
   can be fetched.
*/
static int
installNotifyFilter(void)
{
    struct sock_filter filter[] = {
        ARCH_CHECK_AND_LOAD_SYSCALL_NR,

        /* bind() triggers notification to user-space tracer */
        BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_bind, 0, 1),
        BPF_STMT(BPF_RET + BPF_K, SECCOMP_RET_USER_NOTIF),

        /* listen() triggers notification to user-space tracer */
        BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_listen, 0, 1),
        BPF_STMT(BPF_RET + BPF_K, SECCOMP_RET_USER_NOTIF),

        /* Every other system call is allowed */
        BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW),
    };

    struct sock_fprog prog = {
        .len = (unsigned short) (sizeof(filter) / sizeof(filter[0])),
        .filter = filter,
    };

    int notifyFd;

    /* Install the filter with the SECCOMP_FILTER_FLAG_NEW_LISTENER flag; seccomp()
       returns a notification file descriptor as a result. */
    notifyFd = seccomp(SECCOMP_SET_MODE_FILTER,
                       SECCOMP_FILTER_FLAG_NEW_LISTENER, &prog);
    if (notifyFd == -1)
        errExit("seccomp-install-notify-filter");

    return notifyFd;
}


static void
installPtraceFilter(void)
{
    struct sock_filter filter[] = {
        ARCH_CHECK_AND_LOAD_SYSCALL_NR,

        /* bind() triggers notification to user-space tracer */
        BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_bind, 0, 1),
        BPF_STMT(BPF_RET + BPF_K, SECCOMP_RET_TRACE),

        /* listen() triggers notification to user-space tracer */
        BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_listen, 0, 1),
        BPF_STMT(BPF_RET + BPF_K, SECCOMP_RET_TRACE),

        /* Every other system call is allowed */
        BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW),
    };

    struct sock_fprog prog = {
        .len = (unsigned short) (sizeof(filter) / sizeof(filter[0])),
        .filter = filter,
    };

    ptrace(PTRACE_TRACEME, 0, 0, 0);

    /* To avoid the need for CAP_SYS_ADMIN */
    if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) == -1) {
        errExit("prctl(PR_SET_NO_NEW_PRIVS)");
    }

    if (prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &prog) == -1) {
        errExit("when setting seccomp filter");
    }
}

/* Handler for the SIGINT signal in the target process */

static void
handler(int sig)
{
    /* UNSAFE: This handler uses non-async-signal-safe functions
       (printf(); see TLPI Section 21.1.2) */

    printf("Target process: received signal\n");
}

/* Close a pair of sockets created by socketpair() */

static void
closeSocketPair(int sockPair[2])
{
    if (close(sockPair[0]) == -1)
        errExit("closeSocketPair-close-0");
    if (close(sockPair[1]) == -1)
        errExit("closeSocketPair-close-1");
}

/* Implementation of the target process; create a child process that:

   (1) installs a seccomp filter with the SECCOMP_FILTER_FLAG_NEW_LISTENER
       flag;
   (2) writes the seccomp notification file descriptor returned from the
       previous step onto the UNIX domain socket, 'sockPair[0]';
   (3) exec into the designated process.

   The function return value is the PID of the child process. */

static pid_t
targetProcess(int sockPair[2], char *argv[], struct cmdLineOpts *opts)
{
    pid_t targetPid;
    int notifyFd = 0;
    struct sigaction sa;

    targetPid = fork();
    if (targetPid == -1)
        errExit("fork");

    if (targetPid > 0)          /* In parent, return PID of child */
        return targetPid;

    /* Child falls through to here */
    /* Install a handler for the SIGINT signal */
    sa.sa_handler = handler;
    sa.sa_flags = 0;
    sigemptyset(&sa.sa_mask);
    if (sigaction(SIGINT, &sa, NULL) == -1)
        errExit("sigaction");

    /* Install seccomp filter(s) */

    if(opts->require_ptrace) {
        installPtraceFilter();

        /* Signal the tracing process we are ready
         * http://www.alfonsobeato.net/c/filter-and-modify-system-calls-with-seccomp-and-ptrace/
         * http://www.alfonsobeato.net/c/modifying-system-call-arguments-with-ptrace/
         */
        kill(getpid(), SIGSTOP);
    } else {
        if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0))
            errExit("prctl");

        notifyFd = installNotifyFilter();

        /* Pass the notification file descriptor to the tracing process over
           a UNIX domain socket */

        if (sendfd(sockPair[0], notifyFd) == -1)
            errExit("sendfd");

        /* Notification and socket FDs are no longer needed in target process */

        if (close(notifyFd) == -1)
            errExit("close-target-notify-fd");

        closeSocketPair(sockPair);
    }

    /* Exec into the designated process */

    if(execvp(argv[0], argv) == -1)
        errExit("execvp");
    exit(EXIT_FAILURE);
}

/* Check that the notification ID provided by a SECCOMP_IOCTL_NOTIF_RECV
   operation is still valid. It will no longer be valid if the process has
   terminated. This operation can be used when accessing /proc/PID files in
   the target process in order to avoid TOCTOU race conditions where the
   PID that is returned by SECCOMP_IOCTL_NOTIF_RECV terminates and is
   reused by another process. */

static void
checkNotificationIdIsValid(int notifyFd, __u64 id, char *tag, struct cmdLineOpts *opts)
{
    if (ioctl(notifyFd, SECCOMP_IOCTL_NOTIF_ID_VALID, &id) == -1) {
        fprintf(stderr, "Tracer: notification ID check (%s): target has died\n", tag);
    }
}

void
allocSeccompNotifBuffers(struct seccomp_notif **req, struct seccomp_notif_resp **resp, struct seccomp_notif_sizes *sizes)
{
    /* Discover the sizes of the structures that are used to receive
       notifications and send notification responses, and allocate
       buffers of those sizes. */

    if (seccomp(SECCOMP_GET_NOTIF_SIZES, 0, sizes) == -1)
        errExit("seccomp-SECCOMP_GET_NOTIF_SIZES");

    *req = malloc(sizes->seccomp_notif);
    if (*req == NULL)
        errExit("malloc-seccomp_notif");

    /* When allocating the response buffer, we must allow for the fact
       that the user-space binary may have been built with user-space
       headers where 'struct seccomp_notif_resp' is bigger than the
       response buffer expected by the (older) kernel. Therefore, we
       allocate a buffer that is the maximum of the two sizes. This
       ensures that if the supervisor places bytes into the response
       structure that are past the response size that the kernel expects,
       then the supervisor is not touching an invalid memory location. */

    size_t resp_size = sizes->seccomp_notif_resp;
    if (sizeof(struct seccomp_notif_resp) > resp_size)
        resp_size = sizeof(struct seccomp_notif_resp);

    *resp = malloc(resp_size);
    if (resp == NULL)
        errExit("malloc-seccomp_notif_resp");

}

ssize_t target_memcpy(void *buf, pid_t pid, intptr_t addr, size_t len) {
    struct iovec local[1];
    struct iovec remote[1];

    local[0].iov_base = buf;
    local[0].iov_len = len;
    remote[0].iov_base = (void*) addr;
    remote[0].iov_len = len;

    return process_vm_readv(pid, local, 1, remote, 1, 0);
}

/* Handle notifications that arrive via SECCOMP_RET_USER_NOTIF file
   descriptor, 'notifyFd'. */

static void
watchForNotifications(int notifyFd, struct cmdLineOpts *opts)
{
    struct replaced_fds *replaced_fds = NULL;
    struct seccomp_notif *req;
    struct seccomp_notif_resp *resp;
    struct seccomp_notif_sizes sizes;
    socklen_t addrlen;
    struct sockaddr *addr;
    char path[PATH_MAX];
    int procMem;        /* FD for /proc/PID/mem of target process */

    allocSeccompNotifBuffers(&req, &resp, &sizes);

    /* Loop handling notifications */

    for (;;) {
      /* Wait for next notification, returning info in '*req' */
      memset(req, 0, sizes.seccomp_notif); /* Required since Linux 5.5 */

      if (ioctl(notifyFd, SECCOMP_IOCTL_NOTIF_RECV, req) == -1) {
        if (errno == EINTR) continue;
        errExit("Tracer: ioctl-SECCOMP_IOCTL_NOTIF_RECV");
      }

      resp->id = req->id;
      resp->flags = SECCOMP_USER_NOTIF_FLAG_CONTINUE; /* Allow syscall */
      resp->val = 0; /* Success return value is 0 */
      resp->error = 0;

      switch(req->data.nr) {
          case __NR_listen: {
              int fd = req->data.args[0];
              if(opts->verbose) {
                printf("force-bind: notified of __NR_listen on FD %d\n", fd);
              }

              // Check if the file descriptor was replaced
              struct replaced_fds *rfd = replaced_fds;
              while(rfd) {
                  if(rfd->fd == fd) break;
                  rfd = rfd->next;
              }

              if(opts->prevent_listen && rfd) {
                  // Ignore syscall
                  resp->flags = 0;
                  if(opts->verbose) printf("force-bind: ignore listen(%lld, %lld)\n", req->data.args[0], req->data.args[1]);
              }
              break;
          }
          case __NR_bind: {
              /* Check that the process whose info we are accessing is still alive */
              checkNotificationIdIsValid(notifyFd, req->id, "post-open", opts);

              int socketfd = req->data.args[0];
              intptr_t addrptr = req->data.args[1];
              size_t addrlen = req->data.args[2];

              addr = malloc(addrlen);
              if (resp == NULL)
                errExit("Tracer: malloc");
              if (target_memcpy(&addr, req->pid, addrptr, addrlen) < 0)
                errExit("Tracer: target_memcpy");

              if(!opts->verbose) {
                char addrstring[PATH_MAX];
                printf("force-bind: notified of __NR_bind on %s\n",
                  get_ip_str(addr, addrstring, sizeof(addrstring)));
              }

              /* The response to the notification includes the notification ID */

              resp->id = req->id;
              resp->flags = 0; // Must be zero as at Linux 5.0
              resp->val = 0; // Success return value is 0
              resp->error = 0;

              if (addr->sa_family != AF_INET && addr->sa_family != AF_INET6) {

                /* In this branch, the bind() syscall was performed on addresses
                 * that are neither INET nor INET6, don't alter */

                /* Continue the syscall. This is not secure at all, but we don't
                 * care for now */

                resp->flags = SECCOMP_USER_NOTIF_FLAG_CONTINUE;
              } else {
                /* In this branch, the bind() syscall was performed on INET or
                 * INET6 addresses */

                struct sockaddr *replacement = malloc(addrlen);
                if (replacement == NULL)
                  errExit("Tracer: malloc");
                memcpy(replacement, addr, addrlen);

                int newfd;
                // FIXME: handle multiple replacement
                int matchres = matchAllAddr(opts->map, replacement, &newfd, opts);
                if (matchres < 0) {
                  resp->error = -matchres; // Pass on matching error
                } else if (matchres == 0) {
                  /* Continue the syscall. ideally we should filter the IP address and
                   * make sure it is allowed, but this is not yet implemented */
                  resp->flags = SECCOMP_USER_NOTIF_FLAG_CONTINUE;

                  if(!opts->quiet) {
                    char addrstring[PATH_MAX];
                    printf("force-bind: unmatched %s\n",
                      get_ip_str(addr, addrstring, sizeof(addrstring)),
                      socketfd);
                  }
                } else if (matchres == 2) {
                  struct seccomp_notif_addfd addfd;
                  addfd.id = req->id; /* Cookie from SECCOMP_IOCTL_NOTIF_RECV */
                  addfd.srcfd = newfd;
                  addfd.newfd = socketfd;
                  addfd.flags = SECCOMP_ADDFD_FLAG_SETFD;
                  addfd.newfd_flags = 0;
                  int targetFd = ioctl(notifyFd, SECCOMP_IOCTL_NOTIF_ADDFD, &addfd);
                  resp->error = (targetFd < 0) ? -errno : 0;
                  resp->val   = targetFd;

                  if(!opts->quiet) {
                    char addrstring[PATH_MAX];
                    printf("force-bind: replace %s with FD %d\n",
                      get_ip_str(addr, addrstring, sizeof(addrstring)),
                      socketfd);
                  }

                  struct replaced_fds *replace_fd = malloc(sizeof(struct replaced_fds));
                  if (replace_fd == NULL) {
                      fprintf(stderr, "force-bind: malloc failed\n");
                  } else {
                      bzero(replace_fd, sizeof(struct replaced_fds));
                      replace_fd->next = replaced_fds;
                      replace_fd->fd = targetFd;
                      replaced_fds = replace_fd;
                  }

                  close(newfd); /* No longer needed in supervisor after reassignment */
                } else if(matchres == 1) {
                  resp->flags = SECCOMP_USER_NOTIF_FLAG_CONTINUE;

                  /* Access the memory of the target process in order to discover
                     the syscall arguments */
                  snprintf(path, sizeof(path), "/proc/%d/mem", req->pid);
                  procMem = open(path, O_RDWR);
                  if (procMem == -1)
                    errExit("Tracer: open /proc/PID/mem O_RDWR");

                  if (lseek(procMem, addrptr, SEEK_SET) == -1)
                    errExit("Tracer: lseek /proc/PID/mem");

                  ssize_t s = read(procMem, addr, addrlen);
                  if (s == -1) {
                    errExit("Tracer: read /proc/PID/mem");
                  } else if (s == 0) {
                    errExit("Tracer: read returned EOF");
                  }

                  if(!opts->quiet) {
                    char addrstring[PATH_MAX];
                    char repladdrstring[PATH_MAX];
                    printf("force-bind: replace %s with %s\n",
                      get_ip_str(addr, addrstring, sizeof(addrstring)),
                      get_ip_str(replacement, repladdrstring, sizeof(repladdrstring)));
                  }

                  if (lseek(procMem, addrptr, SEEK_SET) == -1)
                    errExit("Tracer: lseek");

                  s = write(procMem, replacement, addrlen);
                  if (s == -1) {
                    errExit("read");
                  } else if (s != addrlen) {
                    errExit("Tracer: short write\n");
                  }

                  if (close(procMem) == -1)
                    errExit("Tracer: close /proc/PID/mem");
                }

                free(replacement);
              }

              free(addr);
              break;
          }

          default:
              fprintf(stderr, "seccomp: got unexpected syscall %d", req->data.nr);
              exit(EXIT_FAILURE);
        }

        /* Provide a response to the target process */
        if (ioctl(notifyFd, SECCOMP_IOCTL_NOTIF_SEND, resp) == -1) {
          if (errno == ENOENT) {
            fprintf(stderr, "Tracer: response failed with ENOENT; perhaps target "
                "process's syscall was interrupted by signal?\n");
          } else {
            perror("ioctl-SECCOMP_IOCTL_NOTIF_SEND");
          }
        }
    }
}

/* Implementation of the tracer process; create a child process that:

   (1) obtains the seccomp notification file descriptor from 'sockPair[1]';
   (2) handles notifications that arrive on that file descriptor.

   The function return value is the PID of the child process. */

static pid_t
tracerProcess(int sockPair[2], struct cmdLineOpts *opts)
{
  int notifyFd = recvfd(sockPair[1]);
  if (notifyFd == -1)
      errExit("recvfd");
  /* We no longer need the socket pair */
  closeSocketPair(sockPair);
  /* Handle notifications */
  watchForNotifications(notifyFd, opts);
}

static int
wait_for_ptrace(pid_t target, int *res_status, struct cmdLineOpts *opts){
    int status;
    while (1) {
        ptrace(PTRACE_CONT, target, 0, 0);
        waitpid(target, &status, 0);
        if (WIFSTOPPED(status) && WSTOPSIG(status) == SIGTRAP &&
            (status >> 8) == (SIGTRAP | (PTRACE_EVENT_SECCOMP << 8))) {
            return 0;
        }
        if (WIFEXITED(status)) {
            if(res_status) *res_status = status;
            return 1;
        }
    }
}

static void ptrace_read_bind_args(pid_t target,
#if defined(__x86_64__)
    struct user_regs_struct *regs,
#elif defined(__aarch64__)
    struct user_pt_regs *regs,
#endif
    int *sockfd, struct sockaddr **addr, socklen_t *addrlen) {
#if defined(__x86_64__)
    *sockfd          = (int) regs->rdi;
    intptr_t addrptr = (intptr_t) regs->rsi;
    *addrlen         = (socklen_t) regs->rdx;
#elif defined(__aarch64__)
    *sockfd          = (int) regs->regs[0];
    intptr_t addrptr = (intptr_t) regs->regs[1];
    *addrlen         = (socklen_t) regs->regs[2];
#endif

    /* Reserve extra space in case the addrlen is not a multiple of sizeof(long) */
    char buffer[*addrlen + sizeof(long)];

    /* Get the address from the process memory */
    for (int j = 0; j < *addrlen; j += sizeof(long)) {
        long word = ptrace(PTRACE_PEEKDATA, target, addrptr + j, NULL);
        memcpy(&buffer[j], &word, sizeof(long));
    }

    /* Prepare the address buffer */
    *addr = malloc(*addrlen);
    if (*addr == NULL)
        errExit("Tracer: malloc");

    /* Copy the address to the buffer */
    memcpy(*addr, buffer, *addrlen);
}

static bool ptrace_put_bind_args(pid_t target,
#if defined(__x86_64__)
    struct user_regs_struct *regs,
#elif defined(__aarch64__)
    struct user_pt_regs *regs,
#endif
    int sockfd, struct sockaddr* addr, socklen_t addrlen) {
#if defined(__x86_64__)
    int       t_sockfd  = regs->rdi;
    intptr_t  addrptr   = regs->rsi;
    socklen_t t_addrlen = regs->rdx;
#elif defined(__aarch64__)
    int       t_sockfd  = regs->regs[0];
    intptr_t  addrptr   = regs->regs[1];
    socklen_t t_addrlen = regs->regs[2];
#endif

    if (t_addrlen < addrlen) {
        return false;
    }

#if defined(__x86_64__)
    regs->rdi = sockfd;
    regs->rdx = addrlen;
#elif defined(__aarch64__)
    regs->regs[0] = sockfd;
    regs->regs[2] = addrlen;
#endif

    const char *buffer = (const char*) addr;

    /* Write the new address into the target process memory */
    for (int j = 0; j < addrlen; j += sizeof(long)) {
        size_t nextlen = j + sizeof(long);
        long word = 0;
        if (nextlen <= addrlen) {
            /* nominal case */
            word = *((const long*) &buffer[j]);
        } else if (nextlen > t_addrlen) {
            /* not enough room on the target to write a full word */
            word = ptrace(PTRACE_PEEKDATA, target, addrptr + j, NULL);
            memcpy(&word, &buffer[j], addrlen - j);
        } else {
            memcpy(&word, &buffer[j], addrlen - j);
        }
        ptrace(PTRACE_POKEDATA, target, addrptr + j, word);
    }
    return true;
}

static int process_ptrace(pid_t target, struct cmdLineOpts *opts) {
    struct replaced_fds *replaced_fds = NULL;
    int res_status = 0;
    while(1) {
        /* Wait for syscall interception */
        if (wait_for_ptrace(target, &res_status, opts) != 0) return res_status;
#if defined(__x86_64__)
        struct user_regs_struct regs;
        if(ptrace(PTRACE_GETREGS, target, 0, &regs) == -1)
            errExit("PTRACE_GETREGS");
#elif defined(__aarch64__)
        struct user_pt_regs regs;
        struct iovec iov;
        iov.iov_base = &regs;
        iov.iov_len = sizeof(regs);
        if (ptrace(PTRACE_GETREGSET, target, (void*)NT_PRSTATUS, &iov) == -1)
            errExit("PTRACE_GETREGSET");
#endif

        switch(ORIG_SYSCALL(regs)) {
            case __NR_bind: {
                int socketfd;
                socklen_t addrlen;
                struct sockaddr *addr;

                ptrace_read_bind_args(target, &regs, &socketfd, &addr, &addrlen);

                if (addr->sa_family != AF_INET && addr->sa_family != AF_INET6) {
                    /* For non-INET/INET6, do nothing */
                    break;
                } else {
                    struct sockaddr *replacement = malloc(addrlen);
                    if (replacement == NULL)
                        errExit("Tracer: malloc");
                    memcpy(replacement, addr, addrlen);

                    int sourcefd;
                    // FIXME: handle multiple replacement
                    int matchres = matchAllAddr(opts->map, replacement, &sourcefd, opts);
                    if(matchres < 0) {
                        int errnum = -matchres;
#if defined(__x86_64__)
                        regs.orig_rax = -1;
                        if(ptrace(PTRACE_SETREGS, target, 0, &regs) == -1)
                            errExit("PTRACE_SETREGS");
#elif defined(__aarch64__)
                        regs.regs[8] = -1;
                        iov.iov_base = &regs;
                        iov.iov_len = sizeof(regs);
                        if (ptrace(PTRACE_SETREGSET, target, (void*)NT_PRSTATUS, &iov) == -1)
                            errExit("PTRACE_SETREGSET");
#endif
                        ptrace(PTRACE_SYSCALL, target, 0, 0);
                        waitpid(target, 0, 0);
#if defined(__x86_64__)
                        regs.rax = -errnum;
                        if(ptrace(PTRACE_SETREGS, target, 0, &regs) == -1)
                            errExit("PTRACE_SETREGS");
#elif defined(__aarch64__)
                        regs.regs[0] = -errnum;
                        iov.iov_base = &regs;
                        iov.iov_len = sizeof(regs);
                        if (ptrace(PTRACE_SETREGSET, target, (void*)NT_PRSTATUS, &iov) == -1)
                            errExit("PTRACE_SETREGSET");
#endif
                    } else if(matchres == 1) {
                        // Replace network address in the target process memory
                        if(!ptrace_put_bind_args(target, &regs, socketfd, replacement, addrlen)) {
                            fprintf(stderr, "force-bind: short write, cannot fit %d bytes into %d\n", addrlen, (int)addrlen);
                            exit(EXIT_FAILURE);
                        }
#if defined(__x86_64__)
                        if(ptrace(PTRACE_SETREGS, target, 0, &regs) == -1)
                            errExit("PTRACE_SETREGS");
#elif defined(__aarch64__)
                        iov.iov_base = &regs;
                        iov.iov_len = sizeof(regs);
                        if (ptrace(PTRACE_SETREGSET, target, (void*)NT_PRSTATUS, &iov) == -1)
                           errExit("PTRACE_SETREGSET");
#endif
                    } else if(matchres == 2) {
                        struct replaced_fds *replace_fd = malloc(sizeof(struct replaced_fds));
                        if (replace_fd == NULL) {
                            fprintf(stderr, "force-bind: malloc failed\n");
                        } else {
                            bzero(replace_fd, sizeof(struct replaced_fds));
                            replace_fd->next = replaced_fds;
                            replace_fd->fd = socketfd;
                            replaced_fds = replace_fd;
                        }
                        /* Replace the syscall with dup2(sourcefd, socketfd) */
#if defined(__x86_64__)
                        regs.orig_rax = __NR_dup2;
                        regs.rdi      = sourcefd;
                        regs.rsi      = socketfd;
                        if(ptrace(PTRACE_SETREGS, target, 0, &regs) == -1)
                            errExit("PTRACE_SETREGS");
                        ptrace(PTRACE_SYSCALL, target, 0, 0);
                        waitpid(target, 0, 0);
                        if(ptrace(PTRACE_GETREGS, target, 0, &regs) == -1)
                            errExit("PTRACE_GETREGS");
                        if(regs.rax > 0) regs.rax = 0;
                        if(ptrace(PTRACE_SETREGS, target, 0, &regs) == -1)
                            errExit("PTRACE_SETREGS");
#elif defined(__aarch64__)
                        regs.regs[8] = __NR_dup3;
                        regs.regs[0] = sourcefd;
                        regs.regs[1] = socketfd;
                        regs.regs[2] = 0;
                        iov.iov_base = &regs;
                        iov.iov_len = sizeof(regs);
                        if (ptrace(PTRACE_SETREGSET, target, (void*)NT_PRSTATUS, &iov) == -1)
                           errExit("PTRACE_SETREGSET");
                        ptrace(PTRACE_SYSCALL, target, 0, 0);
                        waitpid(target, 0, 0);
                        iov.iov_base = &regs;
                        iov.iov_len = sizeof(regs);
                        if (ptrace(PTRACE_GETREGSET, target, (void*)NT_PRSTATUS, &iov) == -1)
                           errExit("PTRACE_GETREGSET");
                        if(regs.regs[0] > 0) regs.regs[0] = 0;
                        iov.iov_base = &regs;
                        iov.iov_len = sizeof(regs);
                        if (ptrace(PTRACE_SETREGSET, target, (void*)NT_PRSTATUS, &iov) == -1)
                           errExit("PTRACE_SETREGSET");
#endif
                    }

                    free(replacement);
                    free(addr);
                    break;
                }
            }
            case __NR_listen: {
                int fd;
#if defined(__x86_64__)
                fd = regs.rdi;
#elif defined(__aarch64__)
                fd = regs.regs[0];
#endif
                // Check if the file descriptor was replaced
                struct replaced_fds *rfd = replaced_fds;
                while(rfd) {
                    if(rfd->fd == fd) break;
                    rfd = rfd->next;
                }
                if(opts->prevent_listen && rfd) {
                    // Ignore listen syscall by replacing it with a no-op
#if defined(__x86_64__)
                    regs.orig_rax = -1;
                    if(ptrace(PTRACE_SETREGS, target, 0, &regs) == -1)
                        errExit("PTRACE_SETREGS");
                    ptrace(PTRACE_SYSCALL, target, 0, 0);
                    waitpid(target, 0, 0);
                    regs.rax = 0;
                    if(ptrace(PTRACE_SETREGS, target, 0, &regs) == -1)
                        errExit("PTRACE_SETREGS");
#elif defined(__aarch64__)
                    regs.regs[8] = -1;
                    iov.iov_base = &regs;
                    iov.iov_len = sizeof(regs);
                    if (ptrace(PTRACE_SETREGSET, target, (void*)NT_PRSTATUS, &iov) == -1)
                        errExit("PTRACE_SETREGSET");
                    ptrace(PTRACE_SYSCALL, target, 0, 0);
                    waitpid(target, 0, 0);
                    regs.regs[0] = 0;
                    iov.iov_base = &regs;
                    iov.iov_len = sizeof(regs);
                    if (ptrace(PTRACE_SETREGSET, target, (void*)NT_PRSTATUS, &iov) == -1)
                        errExit("PTRACE_SETREGSET");
#endif
                }
                break;
            }
        }
    }
}

static struct sockaddr *
copyAddr(struct addrinfo *info) {
    struct sockaddr *res = malloc(info->ai_addrlen);
    memcpy(res, info->ai_addr, info->ai_addrlen);
    return res;
}

static struct mapping*
parseMap(const char *map0, struct mapping *next, struct cmdLineOpts *opts, bool fullmatch) {
    int err;
    struct mapping *cur = malloc(sizeof(struct mapping));
    size_t maplen = map0 ? strlen(map0) : 0;
    char map[maplen+1];
    char *matchaddr = NULL;
    char *prefix = NULL;
    char *replace = NULL;

    bzero(cur, sizeof(struct mapping));
    cur->next = next;
    bzero(map, sizeof(map));
    if(map0) strncpy(map, map0, maplen);

    if (map0 && fullmatch){
        matchaddr = map;
        char *c = strchr(map, '/');
        if (c && *c) {
            prefix = c+1;
            *c = 0;
        }

        c = strchr(prefix ? prefix : map, '=');
        if (c && *c) {
            replace = c+1;
            *c = 0;
        }
    } else if(map0) {
        replace = map;
    }

    struct addrinfo hints = {
        .ai_flags = AI_PASSIVE,
        .ai_family = AF_UNSPEC
    };
    struct addrinfo *res;

    if(matchaddr && *matchaddr && matchaddr[0] != ':'){
        err = getaddrinfo2(matchaddr, &hints, &res);
        if(err) {
            fprintf(stderr, "Cannot parse match %s: %s\n", matchaddr, strerror(err));
            exit(EXIT_FAILURE);
        }
        cur->addr = copyAddr(res); // FIXME: handle ai_next
        freeaddrinfo(res);
    }

    if(replace && *replace){
        size_t len = strlen(replace);
        if (len > 3 && replace[0] == 'f' && replace[1] == 'd' && (replace[2] == '=' || replace[2] == '-')) {
            int fd = atoi(&replace[3]);
            cur->replacement_fd = fd;
            cur->replacement = NULL;
            //opts->require_ptrace = true;
        } else if (len > 3 && replace[0] == 's' && replace[1] == 'd' && (replace[2] == '=' || replace[2] == '-')) {
            int sd = atoi(&replace[3]);
            int fd = sd + 3;
            cur->replacement_fd = fd;
            cur->replacement = NULL;
            //opts->require_ptrace = true;
        } else {
            err = getaddrinfo2(replace, &hints, &res);
            if(err) {
                fprintf(stderr, "Cannot parse replacement %s: %s\n", replace, strerror(err));
                exit(EXIT_FAILURE);
            }
            cur->replacement = copyAddr(res); // FIXME: handle ai_next
            cur->replacement_fd = 0;
            freeaddrinfo(res);
        }
    }


    if(matchaddr && *matchaddr && matchaddr[0] == ':'){

        bool num = 0;

        if(!cur->replacement || cur->replacement->sa_family == AF_INET) {
            char matchaddr4[PATH_MAX];
            snprintf(matchaddr4, PATH_MAX, "0.0.0.0%s", matchaddr);
            err = getaddrinfo2(matchaddr4, &hints, &res);
            if(err) {
                fprintf(stderr, "Cannot parse IPv4 match %s: %s\n", matchaddr, strerror(err));
                exit(EXIT_FAILURE);
            }
            cur->addr = copyAddr(res);
            if(prefix) {
                cur->prefix = atoi(prefix);
            } else {
                cur->prefix = 32;
            }
            freeaddrinfo(res);
            num++;
        }

        if(!cur->replacement || cur->replacement->sa_family == AF_INET6) {
            if(num) {
                next = cur;
                cur = malloc(sizeof(struct mapping));
                memcpy(cur, next, sizeof(struct mapping));
                cur->next = next;
                num--;
            }

            char matchaddr6[PATH_MAX];
            snprintf(matchaddr6, PATH_MAX, "[::]%s", matchaddr);
            err = getaddrinfo2(matchaddr6, &hints, &res);
            if(err) {
                fprintf(stderr, "Cannot parse IPv6 match %s: %s\n", matchaddr, strerror(err));
                exit(EXIT_FAILURE);
            }
            cur->addr = copyAddr(res);
            if(prefix) {
                cur->prefix = atoi(prefix);
            } else {
                cur->prefix = 128;
            }
            freeaddrinfo(res);
            num++;
        }

    } else {

        if(prefix) {
            cur->prefix = atoi(prefix);
        } else if (cur->addr && cur->addr->sa_family == AF_INET) {
            cur->prefix = 32;
        } else if (cur->addr && cur->addr->sa_family == AF_INET6) {
            cur->prefix = 128;
        }


        if(cur->addr && cur->replacement && cur->addr->sa_family != cur->replacement->sa_family) {
            fprintf(stderr, "Not the same address family on both sides: %s", map0);
            exit(EXIT_FAILURE);
        }

    }

    return cur;
}

static struct in_addr
netAddrIpv4(int prefix, struct in_addr *addr) {
    in_addr_t netmask = 0;
    while(prefix--){
        netmask = (netmask << 1) | 1;
    }
    struct in_addr res = { .s_addr = netmask & addr->s_addr };
    return res;
}

static struct in6_addr
netAddrIpv6(int prefix, struct in6_addr *addr) {
    struct in6_addr netmask;
    for (long i = prefix, j = 0; i > 0; i -= 8, ++j) {
        netmask.s6_addr[j] = (i >= 8) ?
            0xff :
            ( 0xffU << ( 8 - i ) ) & 0xffU;
    }
    struct in6_addr res = {};
    for(int i = 0; i < 16; i++) {
        res.s6_addr[i] = res.s6_addr[i] & netmask.s6_addr[i];
    }
    return netmask;
}

static bool
matchAddr(const struct mapping *map, const struct sockaddr *sa, const struct cmdLineOpts *opts) {
    if (map->replacement && sa->sa_family != map->replacement->sa_family) return false;
    if (!map->addr) return true;
    if (sa->sa_family != map->addr->sa_family) return false;

    // FIXME: handle next address in map->addr

    switch(sa->sa_family) {
        case AF_INET: {
            struct sockaddr_in *addr = (struct sockaddr_in *) sa;
            struct sockaddr_in *map_addr = (struct sockaddr_in *) map->addr;

            /* check port number */
            if (addr->sin_port == 0) return false; // Never match outgoing connections
            if (map_addr->sin_port != 0 && map_addr->sin_port != addr->sin_port) return false;

            /* match any address that's marked as ANY */
            if (addr->sin_addr.s_addr == htonl(INADDR_ANY)) return true;

            /* check network IP */
            struct in_addr net_addr = netAddrIpv4(map->prefix, &addr->sin_addr);
            struct in_addr map_net_addr = netAddrIpv4(map->prefix, &map_addr->sin_addr);
            if (net_addr.s_addr != map_net_addr.s_addr) return false;

            return true;
        }

        case AF_INET6: {
            struct sockaddr_in6 *addr = (struct sockaddr_in6 *) sa;
            struct sockaddr_in6 *map_addr = (struct sockaddr_in6 *) map->addr;

            /* check port number */
            if (addr->sin6_port == 0) return false; // Never match outgoing connections
            if (map_addr->sin6_port != 0 && map_addr->sin6_port != addr->sin6_port) return false;

            /* check network IP */
            struct in6_addr net_addr = netAddrIpv6(map->prefix, &addr->sin6_addr);
            struct in6_addr map_net_addr = netAddrIpv6(map->prefix, &map_addr->sin6_addr);
            for(int i = 0; i < 16; ++i)
                if (net_addr.s6_addr[i] != map_net_addr.s6_addr[i]) return false;

            return true;
        }

        default:
            return false;
    }
}

static void
setReplacement(struct sockaddr *addr0, const struct sockaddr *repl0) {
    switch(addr0->sa_family) {
        case AF_INET: {
            struct sockaddr_in sa = *((struct sockaddr_in *) addr0);
            struct sockaddr_in *addr = (struct sockaddr_in *) addr0;
            struct sockaddr_in *repl = (struct sockaddr_in *) repl0;

            memcpy(addr, repl, sizeof(struct sockaddr_in));

            if(addr->sin_port == 0) {
                addr->sin_port = sa.sin_port;
            }
            break;
        }

        case AF_INET6: {
            struct sockaddr_in6 sa = *((struct sockaddr_in6 *) addr0);
            struct sockaddr_in6 *addr = (struct sockaddr_in6 *) addr0;
            struct sockaddr_in6 *repl = (struct sockaddr_in6 *) repl0;

            memcpy(addr, repl, sizeof(struct sockaddr_in6));

            if(addr->sin6_port == 0) {
                addr->sin6_port = sa.sin6_port;
            }
            break;
        }
    }
}

/**
 * Match the given `sa` address and replace it with the new address from the
 * `map` mappings or fill in `newfd` for file descriptor replacement.
 *
 * Return:
 *      0       -   does not match, continue syscall
 *      -errno  -   return -errno error
 *      1       -   match new address
 *      2       -   match file descriptor
 *
 * FIXME: for replacement (argument `sa`) a list should be provided to allow to
 * replace with multiple addresses
 */
static int
matchAllAddr(const struct mapping *map, struct sockaddr *sa, int *newfd, const struct cmdLineOpts *opts) {
    switch(sa->sa_family) {
        case AF_INET: {
            struct sockaddr_in *addr = (struct sockaddr_in *) sa;
            if (addr->sin_port == 0) return 0; // Never match outgoing connections
        }
        case AF_INET6: {
            struct sockaddr_in6 *addr = (struct sockaddr_in6 *) sa;
            if (addr->sin6_port == 0) return 0; // Never match outgoing connections
        }
    }

    char addr1[PATH_MAX], addr2[PATH_MAX], addr3[PATH_MAX];
    while(map) {
        if(opts->verbose) {
            if(map->replacement)
                printf("force-bind: try match %s with %s/%d (replace with %s)\n",
                    get_ip_str(sa, addr1, sizeof(addr1)),
                    get_ip_str(map->addr, addr2, sizeof(addr2)), map->prefix,
                    get_ip_str(map->replacement, addr3, sizeof(addr3)));
            else
                printf("force-bind: try match %s with %s/%d (replace with fd=%d)\n",
                    get_ip_str(sa, addr1, sizeof(addr1)),
                    get_ip_str(map->addr, addr2, sizeof(addr2)), map->prefix,
                    map->replacement_fd);
            // FIXME: handle the case where the bind should be blocked, and the
            // replaced address is empty
        }
        if(matchAddr(map, sa, opts)) {
            if(map->replacement) {
                if(opts->verbose) printf("force-bind: matched IP replacement\n");
                setReplacement(sa, map->replacement);
                return 1;
            } else if (map->replacement_fd) {
                if(opts->verbose) printf("force-bind: matched file descriptor\n");
                *newfd = map->replacement_fd;
                return 2;
            } else {
                return -EACCES;
            }
        }
        map = map->next;
    }
    if(opts->verbose) printf("force-bind: did not match %s\n",
            get_ip_str(sa, addr1, sizeof(addr1)));
    return 0;
}

/* Diagnose an error in command-line option or argument usage */

static void
usageError(char *msg, char *pname)
{
    if (msg != NULL)
        fprintf(stderr, "%s\n", msg);

    fprintf(stderr,
        "Usage: %s [options] TARGET_PROGRAM [ARGS ...]\n", pname);
    fprintf(stderr,
        "Options\n"
        "    -h                    Help\n"
        "    -V                    Version information\n"
        "    -m MATCH=ADDR         Replace bind() matching first MATCH with ADDR\n"
        "    -b ADDR               Replace all bind() with ADDR (if same family)\n"
        "    -d                    Deny all bind()\n"
        "    -v                    Verbose\n"
        "    -q                    Quiet\n"
        "    -L                    Block listen(2) for fd-N or sd-N sockets\n"
        "    -p                    Force seccomp-ptrace instead of seccomp user notif\n"
        "                          (might not work very well)\n"
        "\n"
        "Last rules (-m, -b, -d) are applied first so you can put your general policy\n"
        "first on your command-line and any following argument can override it.\n"
        "\n"
        "With the -m rule, MATCH pattern can be:\n"
        "\n"
        "    :PORT                 Matches both IPv4 and IPv6 listening on PORT\n"
        "    ADDR:PORT/PREFIX      Matches address with given port with the netmark\n"
        "                          corresponding to PREFIX applied first on both IPs\n"
        "                          IPv6 address must be enclosed in squared brackets.\n"
        "\n"
        "In the rules, ADDR can be:\n"
        "\n"
        "    IP:PORT               Changes the bind target to specified address\n"
        "    fd=N or fd-N          dup2() the specified inherited file descriptor\n"
        "                          in place\n"
        "    sd=N or sd-N          same as fd=N but for systemd file descriptor. sd=0\n"
        "                          is thus equivalent to fd=3\n"
        "\n"
        "Examples:\n"
        "\n"
        "  * force-bind -m 0.0.0.0:80/0=127.0.0.1:8080 progname args...\n"
        "\n"
        "    Replace binds from any IPv4 address port 80 to localhost-only port\n"
        "    8080. IPv6 binds are allowed.\n"
        "\n"
        "  * force-bind -d -m '[::]:80/0=[::1]:8080' progname args...\n"
        "\n"
        "    Replace binds from any IPv6 address port 80 to localhost-only port\n"
        "    8080. IPv4 binds are denied.\n"
        "\n"
        "  * force-bind -d -b '[::1]:8081' -b '127.0.0.1:8080' progname args...\n"
        "\n"
        "    Replace binds from any IPv6 address to localhost port 8081 and from\n"
        "    any IPv4 address to localhost port 8080.\n"
        "\n"
        "  * force-bind -m ':80=sd=0' -m ':80=fd=4' progname args...\n"
        "\n"
        "    Replace any bind to port 80 using first socket from systemd socket\n"
        "    activation. Any port 81 is replaced by passed file descriptor 4.\n"
        "\n"
        "Limitations:\n"
        "\n"
        "    When replacing a socket with an existing file descriptor (by fd number\n"
        "    or using systemd socket activation) and -L flag is used, then all\n"
        "    listen() syscalls on that file descriptor will be ignored. Than can\n"
        "    cause bugs if the file descriptor number is reused (listen calls will\n"
        "    still be blocked).\n"
        "\n");
#ifdef VERSION
    fprintf(stderr, "\nVersion: %s\n", VERSION);
#endif
}

/* Parse command-line options, returning option info in 'opts' */

static int
parseCommandLineOptions(int argc, char *argv[], struct cmdLineOpts *opts)
{
    int opt;

    bzero(opts, sizeof(struct cmdLineOpts));
    opts->map = NULL;
    opts->require_ptrace = false;
    opts->prevent_listen = false;

    int i;
    for(i = 1; argv[i]; i++){
        const char *arg = argv[i];
        if       (!strcmp("-m", arg) && argv[i+1]) { /* Mapping */
            opts->map = parseMap(argv[++i], opts->map, opts, true);

        } else if(!strcmp("-b", arg) && argv[i+1]) { /* Bind */
            opts->map = parseMap(argv[++i], opts->map, opts, false);

        } else if(!strcmp("-d", arg)) {              /* Deny */
            opts->map = parseMap(NULL, opts->map, opts, false);

        } else if(!strcmp("-L", arg)) {              /* block listen */
            opts->prevent_listen = true;

        } else if(!strcmp("-p", arg)) {              /* Ptrace */
            opts->require_ptrace = true;

        } else if(!strcmp("-q", arg)) {              /* Quiet */
            opts->quiet = true;

        } else if(!strcmp("-v", arg)) {              /* Verbose */
            opts->verbose = true;

        } else if(!strcmp("-V", arg)) {              /* Version */
#ifdef VERSION
            printf("Version: %s\n", VERSION);
            exit(EXIT_SUCCESS);
#else
            fprintf(stderr, "No version string available\n");
            exit(EXIT_FAILURE);
#endif

        } else if(!strcmp("-h", arg)) {              /* Help */
            usageError(NULL, argv[0]);
            exit(EXIT_SUCCESS);

        } else if(*arg == '-') {
            usageError("Bad option", argv[0]);
            exit(EXIT_FAILURE);

        } else {
            break;
        }
    }

    /* There should be at least one command-line argument after the options */

    if (!argv[i]) {
        usageError("At least one pathname argument should be supplied",
                argv[0]);
        exit(EXIT_FAILURE);
    }

    return i;
}

int
main(int argc, char *argv[])
{
    pid_t targetPid, tracerPid;
    int sockPair[2];
    struct cmdLineOpts opts;

    setbuf(stdout, NULL);

    int optind = parseCommandLineOptions(argc, argv, &opts);

    /* Create a UNIX domain socket that is used to pass the seccomp
       notification file descriptor from the target process to the tracer
       process. */

    if (socketpair(AF_UNIX, SOCK_STREAM, 0, sockPair) == -1)
        errExit("socketpair");

    /* Create a child process--the "target"--that installs seccomp filtering.
       The target process writes the seccomp notification file descriptor
       onto 'sockPair[0]' and then exec with the command-line arguments. */

    targetPid = targetProcess(sockPair, &argv[optind], &opts);

    /* Create the "tracer" as another child process. This allows the parent to
       wait on the target process and then either kill or wait on the tracer
       when the target terminates. The tracer reads the seccomp notification
       file descriptor from 'sockPair[1]' and then handles the notifications
       that arrive on that file descriptor. */

    if (opts.require_ptrace) {
        /* Wait for the target process to signal STOP
         */
        int status;
        waitpid(targetPid, &status, 0);
        ptrace(PTRACE_SETOPTIONS, targetPid, 0, PTRACE_O_TRACESECCOMP);
        exit(process_ptrace(targetPid, &opts));
    } else {
        tracerProcess(sockPair, &opts);
    }

    exit(EXIT_SUCCESS);
}
