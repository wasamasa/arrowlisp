/*
 * ArrowLISP -- An interpreter for purely symbolic LISP
 * Copyright (C) 2005,2006 Nils M Holm <nmh@t3x.org>
 * This is the interpreter shell.
 * See the file LICENSE for conditions of use.
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <signal.h>
#include "alisp.h"

#define STRLEN	256

char	Image[STRLEN];
int	Nodes;
int	Batch;
int	LoudGC;

void	catchIntr(int sig);
int	getOptNum(int argc, char **argv, int *pi, int *pj, int *pk);
void	getOpts(int argc, char **argv);
void	help(void);
void	init(void);
void	license(void);
void	repl(void);
void	usage(void);

/* Print usage and fail */
void usage(void) {
	fprintf(stderr,
		"Usage: alisp [-L] [-bgi] [-n nodes] [image]\n");
}

int getOptNum(int argc, char **argv, int *pi, int *pj, int *pk) {
	int	n, c;

	if (++(*pi) >= argc) {
		usage();
		exit(1);
	}
	n = atoi(argv[*pi]);
	c = argv[*pi][strlen(argv[*pi])-1];
	switch (c) {
	case 'K':	n = n * 1024; break;
	case 'M':	n = n * 1024 * 1024; break;
	}
	*pj = *pk = 0;
	return n;
}

void help(void) {
	fputc('\n', stderr);
	usage();
	fprintf(stderr,
		"\n"
		"-b    batch mode (quiet, exit on first error)\n"
		"-g    report number of free nodes after each GC\n"
		"-i    init mode (do not load any image)\n"
		"-n #  number of nodes to allocate (default: %dK)\n"
		"-L    print license and exit\n"
		"\n"
		"default image: %s\n\n",
		ALISP_DFL_NODES/1024, ALISP_DFL_IMAGE);
}

void license(void) {
	char	**s;

	s = alisp_license();
	while (*s) {
		printf("%s\n", *s);
		s++;
	}
	exit(0);
}

/* Evaluate command line options */
void getOpts(int argc, char **argv) {
	char	*a;
	int	i, j, k;
	int	v;

	strncpy(Image, ALISP_DFL_IMAGE, strlen(ALISP_DFL_IMAGE));
	Image[STRLEN-1] = 0;
	Nodes = ALISP_DFL_NODES;
	LoudGC = 0;
	v = 0;
	i = 1;
	while (i < argc) {
		a = argv[i];
		if (a[0] != '-') break;
		k = strlen(a);
		for (j=1; j<k; j++) {
			switch (a[j]) {
			case 'b':
				Batch = 1;
				break;
			case 'n':
				Nodes = getOptNum(argc, argv, &i, &j, &k);
				break;
			case 'g':
				LoudGC = 1;
				break;
			case 'i':
				Image[0] = 0;
				break;
			case 'L':
				license();
				break;
			case '?':
			case 'h':
				help();
				exit(1);
				break;
			default:
				usage();
				exit(1);
			}
		}
		i = i+1;
	}
	if (i < argc) {
		strncpy(Image, a, strlen(a)+1);
		Image[STRLEN-1] = 0;
	}
	if (Nodes < ALISP_MIN_SIZE) {
		fprintf(stderr, "alisp: minimum pool size is %d\n",
			ALISP_MIN_SIZE);
		exit(1);
	}
}

void catchIntr(int sig) {
	sig = 0; /*LINT*/
	alisp_stop();
	signal(SIGINT, catchIntr);
}

void repl(void) {
	int	n;

	while(1) {
		alisp_reset();
		n = alisp_read();
		if (alisp_eof(n)) return;
		if (alisp_errflag()) {
			printf("* ");
			alisp_print_error();
			if (Batch) exit(1);
			continue;
		}
		n = alisp_eval(n);
		if (alisp_errflag()) {
			printf("* ");
			alisp_print_error();
			if (Batch) exit(1);
		}
		else {
			if (!Batch) printf("=> ");
			alisp_print(n);
			alisp_nl();
		}
	}
}

void init(void) {
	if (alisp_init(Nodes, LoudGC)) {
		fprintf(stderr, "alisp init failed (memory problem)\n");
		exit(1);
	}
}

/*
 * Here the fun begins
 */
int main(int argc, char **argv) {
	getOpts(argc, argv);
	init();
	getOpts(argc, argv);
	if (!Batch) {
		printf("ArrowLISP ");
		printf(ALISP_RELEASE);
		printf(" (C) 2006 Nils M Holm\n");
	}
	if (Image[0]) {
		if (alisp_load_image(Image)) {
			printf("* ");
			alisp_print_error();
			if (Batch) exit(1);
			alisp_fini();
			init();
			getOpts(argc, argv);
		}
	}
	else if (!Batch) {
		printf("Warning: no image loaded\n");
	}
	signal(SIGINT, catchIntr);
	repl();
	alisp_fini();
	return 0;
}
