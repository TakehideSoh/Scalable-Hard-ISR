CC      = clang
CFLAGS  = -std=c99 -g -Ofast -march=native -mtune=native -Wall -Wextra -pthread
OBJS    = bitset.o stack.o AVLtree.o runtime.o reconio.o search.o hashtable.o

TARGETS = recon recon_th

default: $(TARGETS)

clean:
	$(RM) $(OBJS) $(TARGETS)

recon: $(OBJS) recon.o
	$(CC) $(CFLAGS) -o $@ $^

recon_th: $(OBJS) recon_th.o
	$(CC) $(CFLAGS) -o $@ $^

%.o: %.c
	$(CC) $(CFLAGS) -c $<

# Header dependencies
AVLtree.o: AVLtree.h
bitset.o: bitset.h
recon.o: reconio.h runtime.h search.h task.h
recon_th.o: reconio.h runtime.h search.h task.h
runtime.o: bitset.h runtime.h task.h hashtable.h
reconio.o: bitset.h search.h reconio.h task.h
search.o: AVLtree.h bitset.h search.h task.h hashtable.h
stack.o: bitset.h runtime.h stack.h task.h
hashtable.o: hashtable.h
