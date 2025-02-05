TARGETS = force-bind target-mkdir target-bind

all: $(TARGETS)

force-bind: main.c scm_functions.c
	$(CC) $(CFLAGS) -o $@ $^

parent-socket-activate: parent_soocket_activate.c
	$(CC) $(CFLAGS) -o $@ $^

target-mkdir: target_mkdir.c
	$(CC) $(CFLAGS) -o $@ $^

target-bind: target_bind.c
	$(CC) $(CFLAGS) -o $@ $^

.PHONY: all
