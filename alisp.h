/*
 * ArrowLISP -- An interpreter for purely symbolic LISP
 * Copyright (C) 2005,2006 Nils M Holm <nmh@t3x.org>
 * See http://t3x.org/alisp/license.html for conditions of use.
 */

#define ALISP_MAJOR	17
#define ALISP_RELEASE	"2006-09-13"

/*
 * Number of nodes and vector cells.
 * Memory = Nodes * (2 * sizeof(int) + 1) 
 * (Recommended: 16-bit: 12280, >=32-bit: 131072)
 */
#define	ALISP_DFL_NODES	131072

/* The node pool should not be smaller than this. */
#define ALISP_MIN_SIZE	12280

/* Default image */
#define ALISP_DFL_IMAGE	"/usr/local/share/alisp/alisp-image"

/* For errors without specific source. */
#define ALISP_NOEXPR	-1

/* Counter for statistics. */
struct counter {
	int	n,	/* ones */
		n1k,	/* thousands */
		n1m,	/* millions */
		n1g;	/* billions */
};

/* GC statistics */
struct gc_stats {
	int	used,	/* nodes currently used */
		peak;	/* peak use */
};

/* Error reporting */
struct errorContext {
	char	*msg;	/* Most recent error message */
	char	*arg;	/* Additional information */
	int	expr;	/* Expression causing last error */
	char	*file;	/* File of last error */
	int	line;	/* Line number of last error */
	int	fun;	/* Function of last error */
	int	frame;	/* Call frame of last error */
};

#define alisp_eof(n)	((n) < 0)

int	alisp_dump_image(char *p);
struct errorContext
	*alisp_errctx(void);
int	alisp_errflag(void);
int	alisp_eval(int n);
void	alisp_fini(void);
int	alisp_init(int nodes, int trackGc);
char	**alisp_license(void);
int	alisp_load_image(char *p);
void	alisp_nl(void);
void	alisp_print(int n);
void	alisp_print_error(void);
int	alisp_read(void);
void	alisp_reset(void);
void	alisp_stop(void);
