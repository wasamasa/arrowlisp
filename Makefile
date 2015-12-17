# ArrowLISP Makefile, Unix version

V=	17
PL=
DATE=	20060917

PREFIX?=/usr/local
BINOWN?=bin
BINGRP?=bin

BINDIR=	$(PREFIX)/bin
LIBDIR=	$(PREFIX)/lib
INCDIR=	$(PREFIX)/include
SHRDIR=	$(PREFIX)/share/alisp
MANDIR=	$(PREFIX)/man/man7
DOCDIR=	$(PREFIX)/share/doc/alisp

LIBS=	base.l imath.l iter.l lisp.l nmath.l rmath.l

NODIST=	.distfiles

CFLAGS=		-g -O -I . -fPIC
LINTFLAGS=	-Wall -ansi -pedantic -Wmissing-prototypes

all:	alisp alisp-static alisp-image

alisp:	shell.c alisp.h libalisp.so
	cc $(CFLAGS) -o alisp shell.c libalisp.so

alisp-static:	shell.c alisp.h libalisp.a
	cc $(CFLAGS) -static -o alisp-static shell.c libalisp.a

libalisp.a:	alisp.o
	ar -r libalisp.a alisp.o

libalisp.so:	alisp.o
	cc -shared -o libalisp.so alisp.o

alisp.o:	alisp.c alisp.h
	$(CC) $(CFLAGS) -o alisp.o -c alisp.c

lint:
	$(CC) $(CFLAGS) $(LINTFLAGS) -o alisp alisp.c shell.c

alisp-image:	alisp-static base.l
	echo '(load base) (dump-image alisp-image)' \
		| ./alisp-static -bi -n 12K

test:	alisp-static
	rm -f delete-me
	ALISPSRC=. ./alisp-static -i <test.l | tee _test
	diff test.OK _test && rm _test delete-me

# Set $C to -c, if your system does not copy files by default.
C=
install: all
	strip alisp
	install -o $(BINOWN) -g $(BINGRP) -d -m 0755 $(SHRDIR)
	install -o $(BINOWN) -g $(BINGRP) -d -m 0755 $(DOCDIR)
	install -o $(BINOWN) -g $(BINGRP) $C -m 0755 alisp $(BINDIR)
	install -o $(BINOWN) -g $(BINGRP) $C -m 0755 libalisp.* $(LIBDIR)
	install -o $(BINOWN) -g $(BINGRP) $C -m 0644 alisp-image $(SHRDIR)
	install -o $(BINOWN) -g $(BINGRP) $C -m 0755 alisp.h $(INCDIR)
	install -o $(BINOWN) -g $(BINGRP) $C -m 0644 $(LIBS) $(SHRDIR)
	install -o $(BINOWN) -g $(BINGRP) $C -m 0644 src/*/*.l $(SHRDIR)
	install -o $(BINOWN) -g $(BINGRP) $C -m 0644 alisp.7 $(MANDIR)
	install -o $(BINOWN) -g $(BINGRP) $C -m 0644 LICENSE $(SHRDIR)
	install -o $(BINOWN) -g $(BINGRP) $C -m 0644 alisp.txt $(DOCDIR)

alisp-$(DATE).tar.gz: clean
	find . -type f >.distfiles
	mkdir alisp-$(DATE)
	tar cfT - .distfiles | tar xfC - alisp-$(DATE)
	(cd alisp-$(DATE); rm -rf $(NODIST))
	tar cf - alisp-$(DATE) | gzip -9c > alisp-$(DATE).tar.gz
	rm -r alisp-$(DATE)
	rm -f .distfiles

dist:		alisp-$(DATE).tar.gz

csums:
	txsum -u <_checksums >_checksums.new
	mv -i _checksums.new _checksums

clean:
	rm -f *.o *.a *.so *.core core alisp alisp-static alisp-image \
		___test___ alisp$V$(PL).tgz alisp-$(DATE).tar.gz delete-me
	rm -rf doc/library doc/prog

mksums:	clean
	find . -type f | grep -v _checksums | grep -v alisp$V$(PL).tgz \
		| sort | txsum -m >_checksums

distinfo:
	md5 alisp-$(DATE).tar.gz >freebsd-port/distinfo
	sha256 alisp-$(DATE).tar.gz >>freebsd-port/distinfo
	echo -n "SIZE (alisp-$(DATE).tar.gz) = " \
		>>freebsd-port/distinfo
	ls -l alisp-$(DATE).tar.gz | awk '{print $$5}' \
		>>freebsd-port/distinfo

arc:	clean
	tar cfz alisp$V$(PL).tgz *

