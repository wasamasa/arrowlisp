/*
 * ArrowLISP -- An interpreter for purely symbolic LISP
 * Copyright (C) 1998-2006 Nils M Holm <nmh@t3x.org>
 * See the file LICENSE for conditions of use.
 */

#define DEBUG 0

#include <stdlib.h>
#ifdef __TURBOC__
 #include <io.h>
 #include <alloc.h>
#else
 #include <unistd.h>
 #ifndef __MINGW32__
  #ifndef __CYGWIN__
   #define setmode(fd, mode)
  #endif
 #endif
#endif
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <fcntl.h>

#define __ARROWLIB__
#include "alisp.h"

#define	TEXTLEN		256	/* Max. length for literal symbols */
#define MAXPATHL	256	/* Max. path length */

#define NROOTS	10	/* Number of GC roots */

/* Tag Masks */
#define	AFLAG	0x01	/* Atom flag (CAR = char, CDR = next) */
#define	MFLAG	0x02	/* Mark flag of garbage collector */
#define SFLAG	0x04	/* State flag of garbage collector */

#define	EOT	-1	/* EOT indicator */
#define	DOT	-2	/* Internal: dot character */
#define	RPAREN	-3	/* Internal: right parenthesis */

/* Evaluator states */
#define	MATOM	'0' 	/* Processing Atom */
#define	MLIST	'1' 	/* Processing List */
#define	MBETA	'2' 	/* Beta-reducing */
#define	MBIND	'3' 	/* Processing bindings of LET */
#define	MBINR	'4' 	/* Processing bindings of LETREC */
#define	MLETR	'5' 	/* Finish LET or LETREC */
#define	MCOND	'6' 	/* Processing predicates of COND */
#define	MCONJ	'7' 	/* Processing arguments of AND */
#define	MDISJ	'8' 	/* Processing arguments of OR */

/* Short cut */
#define NOEXPR	ALISP_NOEXPR

static int	PoolSize;		/* Size of node pool */
static int	NIL;			/* Not In List (or Pool) */
static int	*Car,			/* Vector holding CAR fields */
		*Cdr;			/* Vector holding CDR fields */
static char	*Tag;			/* Vector holding TAG fields */
static int	Parent;			/* Parent pointer used in GC */
static int	Free;			/* Freelist */
static int	*Root[NROOTS];		/* GC Roots */
static int	Tmp, Tmp2;		/* Temp. GC-safe locations */

static char	*Infile;		/* Input file name */
static FILE	*Input;			/* Current input stream */
static int	Rejected;		/* Unread character */
static int	Line;			/* Input line number */
static FILE	*Output;		/* Current output stream */
static char	DirName[MAXPATHL];	/* Source directory */
static char	ExpPath[MAXPATHL];	/* Expanded path of input file */
static char	DflPath[MAXPATHL];	/* Default path of input file */
static char	Path[MAXPATHL];		/* Path to input file */

static int	ErrFlag;		/* Error Flag */
static struct errorContext
		Error;			/* Error context */
static int	FatalFlag;		/* Fatal error flag */

static int	Symbols;		/* Symbol table */
static int	Packages;		/* Meta symbol table */
static int	SafeSymbols;		/* Safe copy of Symbols */
static int	Stack, Stack0;		/* Global stack, bottom of Stack */
static int	Mstack, Lstack;		/* Mode stack, List stack */
static int	Bstack;			/* Binding stack, used by LET/LETREC */
static int	Estack;			/* Env. stack, for fixing closures */
static int	Frame;			/* Current call frame */
static int	Function;		/* Name of current lambda function */
static int	Trace;			/* Function to trace */
static int	(*TraceHandler)(int n);	/* Trace handler */

static int	LexEnv;			/* Environment for creating closures */
static int	Bound;			/* Variables bound in a closure */

static int	Level;			/* Nesting level during input */
static int	LoadLev;		/* Number of nested LOADs */
static int	EvLev;			/* Number of nested EVALs */
static int	Quoted;			/* Quote flag of PRINT */
static int	MaxAtoms;		/* Memory use gauge */
static int	Ntrace;			/* Max fns to print in call trace */
static int	StatFlag;		/* Statistics flag */
static int	ClosureForm;		/* Ext. rep. of closures (0,1,2) */
static int	VerifyArrows;		/* Verify expr => nf */
static int	TrackGC;		/* Report node usage after GC */

struct counter	Reductions,		/* Reduction counter */
		Allocations,		/* Allocation counter */
		Collections;		/* Garbage collection counter */

/* Builtin symbol pointers (for fast lookup) */
static int	S_bottom, S_closure, S_false, S_lambda, S_primitive,
		S_quote, S_special, S_special_cbv, S_true, S_void,
		S_last;

/* Primitive function opcodes */
enum {	P_ATOM, P_BOTTOM, P_CAR, P_CDR, P_CONS, P_DEFINED, P_EQ,
	P_EXPLODE, P_GC, P_IMPLODE, P_QUIT, P_READ, P_RECURSIVE_BIND,
	P_SYMBOLS, P_VERIFY_ARROWS, P_WRITE, N_PRIMITIVES };

/* Primitive function pointers */
static int	(*Primitives[N_PRIMITIVES])(int);

/* Special form opcodes */
enum {	SF_AND, SF_APPLY, SF_CLOSURE_FORM, SF_COND, SF_DEFINE,
	SF_DUMP_IMAGE, SF_EVAL, SF_LAMBDA, SF_LET, SF_LETREC,
	SF_LOAD, SF_OR, SF_PACKAGE, SF_QUOTE, SF_STATS, SF_TRACE,
	N_SPECIALS };

/* Special form handler pointers */
static int	(*Specials[N_SPECIALS])(int, int *, int *, int *);

/* handle unused arg (lint) */
#define USE(arg)	arg = 0

/*
 * Prototypes
 */
static void	REL(void);
static void	_print(int n);
static int	_rdch(void);
static int	addPackage(int sym);
static int	addPrim(char *name, int opcode);
static int	addSpecial(char *name, int opcode, int cbv);
static int	addSym(char *s, int v);
static int	alloc3(int pcar, int pcdr, int ptag);
static int	atomic(int n);
static int	badArgLst(int n);
static void	bindArgs(int n, int name);
static void	bindLet(int env);
static void	bsave(int n);
static int	bunsave(int k);
static void	clearStats(void);
static int	closure(int n);
static void	collect(int n);
static int	copyBindings(void);
static void	count(struct counter *c, int k);
static char	*counterToStr(struct counter *c, char *buf);
static char	*defaultPath(char *s);
static int	doAnd(int n, int *pcf, int *pmode, int *pcbn);
static int	doApply(int n, int *pcf, int *pmode, int *pcbn);
static int	doAtom(int n);
static int	doBottom(int n);
static int	doCar(int n);
static int	doCdr(int n);
static int	doClosureForm(int n, int *pcf, int *pmode, int *pcbn);
static int	doCond(int n, int *pcf, int *pmode, int *pcbn);
static int	doCons(int n);
static int	doDefine(int n, int *pcf, int *pmode, int *pcbn);
static int	doDefined(int n);
static int	doDumpImage(int n, int *pcf, int *pmode, int *pcbn);
static int	doEq(int n);
static int	doEval(int n, int *pcf, int *pmode, int *pcbn);
static int	doExplode(int n);
static int	doGC(int n);
static int	doImplode(int n);
static int	doLambda(int n, int *pcf, int *pmode, int *pcbn);
static int	doLet(int n, int *pcf, int *pmode, int *pcbn);
static int	doLetrec(int n, int *pcf, int *pmode, int *pcbn);
static int	doLoad(int n, int *pcf, int *pmode, int *pcbn);
static int	doOr(int n, int *pcf, int *pmode, int *pcbn);
static int	doQuote(int n, int *pcf, int *pmode, int *pcbn);
static int	doRead(int n);
static int	doRecursiveBind(int n);
static int	doStats(int n, int *pcf, int *pmode, int *pcbn);
static int	doSymbols(int n);
static int	doTrace(int n, int *pcf, int *pmode, int *pcbn);
static int	doWrite(int n);
static int	equals(int n, int m);
static int	error(char *m, int n);
static int	eval(int n);
static int	evalClause(int n);
static int	evalLet(void);
static char	*expandPath(char *s);
static int	explodeStr(char *sym);
static void	fatal(char *m);
static int	findPackage(int sym);
static int	findPsym(char *s, int y);
static int	findSym(char *s);
static int	finishLet(int rec);
static void	fixAllClosures(int b);
static void	fixCachedClosures(void);
static void	fixClosuresOf(int n, int bindings);
static void	fixnil(int *p, int oldnil, int newnil);
static int	gc(void);
static void	getDirName(char *path, char *pfx);
static int	getPred(void);
static char	*symToStr(int n, char *b, int k);
static void	init1(void);
static void	init2(void);
static int	isAlist(int n);
static int	isBound(int n);
static int	isSymList(int m);
static int	load(char *p);
static int	localize(int n, int *exprp);
static void	lsave(int n);
static int	lunsave(int k);
static void	mark(int n);
static int	mkLexEnv(int term, int locals);
static void	msave(int v);
static int	munsave(void);
static int	newDefine(int n);
static int	nextLet(int n);
static void	nl(void);
static int	nreverse(int n);
static void	pr(char *s);
static int	primitive(int *np);
static void	printCallTrace(int n);
static int	printClosure(int n, int dot);
static void	printError(void);
static int	printCondensed(int n, int dot);
static int	printProc(int n, int dot);
static int	printQuote(int n, int dot);
static void	printTrace(int n);
static void	prnum(int n);
static int	quote(int n);
static int	rdch(void); int c;
static int	readCondensed(void);
static int	readList(void);
static void	resetCounter(struct counter *c);
static void	resetState(void);
static void	restoreBindings(int values);
static void	save(int n);
static int	setupCond(int n);
static int	setupLet(int n);
static int	setupLogOp(int n);
static int	special(int *np, int *pcf, int *pmode, int *pcbn);
static int	strToSym(char *s);
static void	subst(int old, int new, int *p);
static char	*symToStr(int n, char *b, int k);
static int	symbol(int c);
static void	tailCall(void);
static void	unbindArgs(void);
static int	unreadable(void);
static int	unsave(int k);
static void	updatePackages(int old, int new);
static void	verify(void);
static int	wrongArgs(int n);
static int	xread(void);

/* Emit newline sequence */
static void nl(void) {
	putc('\n', Output);
	if (Output == stdout) fflush(Output);
}

/* Print the string S through a buffered interface */
static void pr(char *s) {
	fputs(s, Output);
}

/* Print a number */
static void prnum(int n) {
	printf("%d", n);
}

/* Print function names on call stack */
static void printCallTrace(int frame) {
	int	s, n;

	s = frame;
	n = Ntrace;
	while (s != NIL) {
		if (!n || Cdr[s] == NIL || Car[Cdr[s]] == NIL) break;
		if (n == Ntrace) pr("* Trace:");
		n = n-1;
		pr(" ");
		Quoted = 1;
		_print(Car[Cdr[s]]);
		s = Car[s];
	}
	if (n != Ntrace) nl();
}

/* Register error context and set error flag */
static int error(char *m, int n) {
	if (ErrFlag) return NIL;
	Error.msg = m;
	Error.expr = n;
	Error.file = Infile;
	Error.line = Line;
	Error.fun = Function;
	Error.frame = Frame;
	ErrFlag = -1;
	return NIL;
}

/* Print error message registered by error() */
static void printError(void) {
	if (Error.file) {
		pr(Error.file);
		pr(": ");
	}
	prnum(Error.line);
	pr(": ");
	if (Error.fun != NIL) {
		Quoted = 1;
		_print(Error.fun);
	}
	else {
		pr("REPL");
	}
	pr(": ");
	pr(Error.msg);
	if (Error.expr != -1) {
		if (Error.msg[0]) pr(": ");
		Quoted = 1;
		_print(Error.expr);
	}
	nl();
	if (Error.arg) {
		pr("* ");
		pr(Error.arg); nl();
		Error.arg = NULL;
	}
	if (!FatalFlag && Error.frame != NIL)
		printCallTrace(Error.frame);
	ErrFlag = 0;
}

/* Print message M and halt the interpreter */
static void fatal(char *m) {
	ErrFlag = 0;
	FatalFlag = -1;
	error(m, NOEXPR);
	printError();
	pr("* Fatal error, aborting");
	nl();
	exit(1);
}

/* Reset counter. */
static void resetCounter(struct counter *c) {
	c->n = 0;
	c->n1k = 0;
	c->n1m = 0;
	c->n1g = 0;
}

/* Increment counter. */
static void count(struct counter *c, int k) {
	char	*msg = "statistics counter overflow";

	c->n = c->n+k;
	if (c->n >= 1000) {
		c->n = c->n - 1000;
		c->n1k = c->n1k + 1;
		if (c->n1k >= 1000) {
			c->n1k = 0;
			c->n1m = c->n1m+1;
			if (c->n1m >= 1000) {
				c->n1m = 0;
				c->n1g = c->n1g+1;
				if (c->n1g >= 1000) {
					error(msg, NOEXPR);
				}
			}
		}
	}
}

/* Print counter value to string */
static char *counterToStr(struct counter *c, char *buf) {
	int	i;

	i = 0;
	if (c->n1g) {
		sprintf(&buf[i], "%d,", c->n1g);
		i = strlen(buf);
	}
	if (c->n1m || c->n1g) {
		if (c->n1g)
			sprintf(&buf[i], "%03d,", c->n1m);
		else
			sprintf(&buf[i], "%d,", c->n1m);
		i = strlen(buf);
	}
	if (c->n1k || c->n1m || c->n1g) {
		if (c->n1g || c->n1m)
			sprintf(&buf[i], "%03d,", c->n1k);
		else
			sprintf(&buf[i], "%d,", c->n1k);
		i = strlen(buf);
	}
	if (c->n1g || c->n1m || c->n1k)
		sprintf(&buf[i], "%03d", c->n);
	else
		sprintf(&buf[i], "%d", c->n);
	return buf;
}

/*
 * Mark nodes which can be accessed through N.
 * This routine uses the Deutsch/Schorr/Waite algorithm
 * (aka pointer reversal algorithm) which marks the
 * nodes of a pool in constant space.
 * It uses the MFLAG and SFLAG to keep track of the
 * state of the current node.
 * Each visited node goes through these states:
 * M==0 S==0 unvisited, process CAR
 * M==1 S==1 CAR visited, process CDR
 * M==1 S==0 completely visited, return to parent
 */
static void mark(int n) {
	int	p;

	Parent = NIL;	/* Initially, there is no parent node */
	while (1) {
		/* Reached a leaf? */
		if (n == NIL || Tag[n] & MFLAG) {
			/* If the current node is a leaf and there is */
			/* no parent, the entire tree is marked. */
			if (Parent == NIL) break;
			if (Tag[Parent] & SFLAG) {
				/* State 2: the CDR of the parent has */
				/* not yet been marked (S of Parent set). */
				/* Swap CAR and CDR pointers and */
				/* proceed with CDR. Set State=3. */
				p = Cdr[Parent];
				Cdr[Parent] = Car[Parent];
				Car[Parent] = n;
				Tag[Parent] &= ~SFLAG;	/* S=0 */
				Tag[Parent] |=  MFLAG;	/* M=1 */
				n = p;
			}
			else {
				/* State 3: CAR and CDR of parent done. */
				/* Return to the parent and restore */
				/* parent of parent */
				p = Parent;
				Parent = Cdr[p];
				Cdr[p] = n;
				n = p;
			}
		}
		else {
			/* State 1: The current node has not yet been */
			/* visited. */
			if (Tag[n] & AFLAG) {
				/* If the node is an atom, go directly */
				/* to state 3: Save the parent in CDR, */
				/* make the current node the new parent */
				/* and move to its CDR. */
				p = Cdr[n];
				Cdr[n] = Parent;
				/* S is already 0 */
				/*Tag[n] &= ~SFLAG;*/	/* S=0 */
				Parent = n;
				n = p;
				Tag[Parent] |= MFLAG;	/* M=1 */
			}
			else {
				/* Go to state 2: like above, but save */
				/* the parent in CAR and proceed to CAR. */
				p = Car[n];
				Car[n] = Parent;
				Tag[n] |= MFLAG;	/* M=1 */
				Parent = n;
				n = p;
				Tag[Parent] |= SFLAG;	/* S=1 */
			}
		}
	}
}

/*
 * Mark and Sweep Garbage Collection.
 * First tag all nodes which can be accessed through
 * root registers (Root[]) and then reclaim untagged
 * nodes.
 */
static int gc(void) {
	int	i, k;

	k = 0;
#if DEBUG == 1
	pr("GC called");
	nl();
#endif
	for (i=0; i<NROOTS; i++) mark(Root[i][0]);
	if (ErrFlag) {
		mark(Error.expr);
		mark(Error.fun);
		mark(Error.frame);
	}
	Free = NIL;
	for (i=0; i<PoolSize; i++) {
		if (!(Tag[i] & MFLAG)) {
			Cdr[i] = Free;
			Free = i;
			k = k+1;
		}
		else {
			Tag[i] &= ~MFLAG;
		}
	}
	if (MaxAtoms < PoolSize-k) MaxAtoms = PoolSize-k;
	if (DEBUG || TrackGC) {
		prnum(k);
		pr(" nodes reclaimed");
		nl();
	}
	if (StatFlag) count(&Collections, 1);
	return k;
}

/* Allocate a fresh node and initialize with PCAR,PCDR,PTAG */
static int alloc3(int pcar, int pcdr, int ptag) {
	int	n;

	if (StatFlag) count(&Allocations, 1);
	if (Free == NIL) {
		gc();
		if (Free == NIL) fatal("alloc3(): out of nodes");
	}
	n = Free;
	Free = Cdr[Free];
	Car[n] = pcar;
	Cdr[n] = pcdr;
	Tag[n] = ptag;
	return n;
}

/* Allocate a fresh node and initialize with PCAR,PCDR */
#define alloc(pcar, pcdr) \
	alloc3((pcar), (pcdr), 0)

/* Save node N on the Stack. */
static void save(int n) {
	Tmp = n;	/* Otherwise alloc() might recycle this node */
	Stack = alloc(n, Stack);
	Tmp = NIL;
}

/* Pop K nodes off the Stack and return the last one */
static int unsave(int k) {
	int	n = NIL; /*LINT*/

	while (k) {
		if (Stack == NIL) fatal("unsave(): stack underflow");
		n = Car[Stack];
		Stack = Cdr[Stack];
		k = k-1;
	}
	return n;
}

/* Save value V on the M-Stack. */
static void msave(int v) {
	/* Since the Mstack holds integer values rather than */
	/* nodes, the values are packaged in the character */
	/* fields of atoms. */
	Car[Mstack] = alloc3(v, Car[Mstack], AFLAG);
}

/* Pop a value off the M-Stack and return it */
static int munsave(void) {
	int	v;

	if (Car[Mstack] == NIL) fatal("munsave(): m-stack underflow");
	v = Car[Car[Mstack]];		/* See msave() */
	Car[Mstack] = Cdr[Car[Mstack]];
	return v;
}

/* Save node N on the L-Stack */
static void lsave(int n) {
	Tmp = n;	/* Otherwise alloc() might recycle this node */
	Lstack = alloc(n, Lstack);
	Tmp = NIL;
}

/* Pop K nodes off the L-Stack and return the last one */
static int lunsave(int k) {
	int	n = NIL; /*LINT*/

	while (k) {
		if (Lstack == NIL) fatal("lunsave(): l-stack underflow");
		n = Car[Lstack];
		Lstack = Cdr[Lstack];
		k = k-1;
	}
	return n;
}

/* Save node N on the B-Stack */
static void bsave(int n) {
	Tmp = n;	/* Otherwise alloc() might recycle this node */
	Bstack = alloc(n, Bstack);
	Tmp = NIL;
}

/* Pop K nodes off the B-Stack and return the last one */
static int bunsave(int k) {
	int	n = NIL; /*LINT*/

	while (k) {
		if (Bstack == NIL) fatal("bunsave(): b-stack underflow");
		n = Car[Bstack];
		Bstack = Cdr[Bstack];
		k = k-1;
	}
	return n;
}

/*
 * Read a single character from the input stream
 * and return it. Rdch()==EOT indicates that the
 * input is exhausted.
 */
static int _rdch(void) {
	int	c;

	if (Rejected != EOT) {
		c = Rejected;
		Rejected = EOT;
		return c;
	}
	c = getc(Input);
	if (feof(Input)) return EOT;
	if (c == '\n') Line = Line+1;
	return c;
}

/* Read a character and convert it to lower case */
static int rdch(void) {
	return tolower(_rdch());
}

/*
 * Find a symbol named S in the symbol table Y.
 * When the symbol is found, return it.
 * Otherwise return NIL.
 */
static int findPsym(char *s, int y) {
	int	n, i;

	while (y != NIL) {
		n = Car[Car[y]];
		i = 0;
		while (n != NIL && s[i]) {
			if (s[i] != (Car[n] & 255)) break;
			n = Cdr[n];
			i = i+1;
		}
		if (n == NIL && !s[i]) return Car[y];
		y = Cdr[y];
	}
	return NIL;
}

/*
 * Find the symbol S in the symbol table of any
 * package in the package list.
 */
static int findSym(char *s) {
	int	p, y;

	/* First search the current package */
	y = findPsym(s, Symbols);
	if (y != NIL) return y;
	/* No match, search other packages. */
	p = Packages;
	while (p != NIL) {
		y = findPsym(s, Cdr[Car[p]]);
		if (y != NIL) return y;
		p = Cdr[p];
	}
	return NIL;
}

/* Update symbol table pointer in package list. */
static void updatePackages(int old, int new) {
	int	p;

	p = Packages;
	while (p != NIL) {
		if (Cdr[Car[p]] == old) {
			Cdr[Car[p]] = new;
			return;
		}
		p = Cdr[p];
	}
	if (Packages != NIL)
		fatal("updatePackages(): symbol table not in package list?");
}

/* Find a package. */
static int findPackage(int sym) {
	int	p;

	p = Packages;
	while (p != NIL) {
		if (Car[Car[p]] == sym) return Car[p];
		p = Cdr[p];
	}
	return NIL;
}

/* Add a package. */
static int addPackage(int sym) {
	int	y, p;

	y = findPackage(sym);
	if (y != NIL) return Cdr[y];
	p = alloc(sym, NIL);
	save(p);
	Packages = alloc(p, Packages);
	unsave(1);
	return Cdr[p];
}

/* Is N a 'real' (non-NIL) Atom? */
static int atomic(int n) {
	return n != NIL && Car[n] != NIL && (Tag[Car[n]] & AFLAG);
}

/* Substitute each OLD in *P with NEW. */
static void subst(int old, int new, int *p) {
	if (*p == NIL) return;
	if (atomic(*p)) {
		if (*p == old) *p = new;
		return;
	}
	subst(old, new, &Car[*p]);
	subst(old, new, &Cdr[*p]);
}

/* Make symbol N local to the current package. */
/* Also fix recursive references to N in EXPR. */
static int localize(int n, int *exprp) {
	int	y, osym;

	y = Symbols;
	while (y != NIL) {
		if (n == Car[y]) return n;
		y = Cdr[y];
	}
	osym = Symbols;
	Symbols = alloc(NIL, Symbols);
	Car[Symbols] = alloc(Car[n], S_void);
	updatePackages(osym, Symbols);
	subst(n, Car[Symbols], exprp);
	return Car[Symbols];
}

/* Explode a string to a list of nodes */
static int strToSym(char *s) {
	int	i, n, m, a;

	i = 0;
	if (s[i] == 0) return NIL;
	a = n = NIL;
	while (s[i]) {
		m = alloc3(s[i], NIL, AFLAG);
		if (n == NIL) {		/* Protect the first character */
			n = m;
			save(n);
		}
		else {			/* Just append the rest */
			Cdr[a] = m;
		}
		a = m;
		i = i+1;
	}
	unsave(1);
	return n;
}

/* Implode a list of nodes to a string */
static char *symToStr(int n, char *b, int k) {
	int	i;

	n = Car[n];
	for (i=0; i<k-1; i++) {
		if (n == NIL) break;
		b[i] = Car[n];
		n = Cdr[n];
	}
	if (n != NIL) {
		error("symToStr(): string too long", NOEXPR);
		return NULL;
	}
	b[i] = 0;
	return b;
}

/*
 * Add the symbol S to the symbol table. If
 * the symbol already exists, return the
 * existing symbol.
 * When adding a new symbol, initialize its
 * VALUE with V. If V=0, make the symbol
 * a constant (bind it to itself).
 * Return the symbol S.
 */
static int addSym(char *s, int v) {
	int	n, m, osym;

	n = findSym(s);
	if (n != NIL) return n;
	n = strToSym(s);
	save(n);
	m = alloc(n, v? v: n);
	save(m);
	osym = Symbols;
	Symbols = alloc(m, Symbols);
	unsave(2);
	updatePackages(osym, Symbols);
	return m;
}

/* Add primitive procedure */
static int addPrim(char *name, int opcode) {
	int	y;

	y = addSym(name, 0);
	Cdr[y] = alloc(S_primitive, NIL);
	Cdr[Cdr[y]] = alloc3(opcode, NIL, AFLAG);
	Cdr[Cdr[Cdr[y]]] = y;
	return y;
}

/* Add special form handler */
static int addSpecial(char *name, int opcode, int cbv) {
	int	y;

	y = addSym(name, 0);
	Cdr[y] = alloc(cbv? S_special_cbv: S_special, NIL);
	Cdr[Cdr[y]] = alloc3(opcode, NIL, AFLAG);
	Cdr[Cdr[Cdr[y]]] = y;
	return y;
}

/*
 * Read a list (S0 ... SN) and return (a pointer to) it.
 * This routine also recognizes pairs of the form (S0.S1).
 * For empty lists, it returns NIL.
 */
static int readList(void) {
	int	n,	/* Node read */
		m,	/* Ptr to list */
		a,	/* Used to append nodes to m */
		c;	/* Member counter */
	char	*badpair;

	badpair = "bad pair";
	Level = Level+1;
	m = alloc(NIL, NIL);	/* Root node */
	save(m);
	a = NIL;
	c = 0;
	while (1) {
		if (ErrFlag) {
			unsave(1);
			return NIL;
		}
		n = xread();
		if (n == EOT)  {
			if (LoadLev) return EOT;
			error("missing ')'", NOEXPR);
		}
		if (n == DOT) {
			if (c < 1) {
				error(badpair, NOEXPR);
				continue;
			}
			n = xread();
			Cdr[a] = n;
			if (n == RPAREN || xread() != RPAREN) {
				error(badpair, NOEXPR);
				continue;
			}
			unsave(1);
			Level = Level-1;
			return m;
		}
		if (n == RPAREN) break;
		if (a == NIL) 
			a = m;		/* First member: insert at root */
		else
			a = Cdr[a];	/* Following members: append */
		Car[a] = n;
		Cdr[a] = alloc(NIL, NIL); /* Alloc space for next member */
		c = c+1;
	}
	Level = Level-1;
	if (a != NIL) Cdr[a] = NIL;	/* Remove trailing empty node */
	unsave(1);
	return c? m: NIL;
}

/* Variables to dump to image file */
static int *ImageVars[] = {
	&ClosureForm, &VerifyArrows,
	&Packages, &Symbols, &Free, &S_bottom, &S_closure,
	&S_false, &S_lambda, &S_primitive, &S_quote, &S_special,
	&S_special_cbv, &S_true, &S_void, &S_last,
NULL };


/* Extract directory name of PATH into PFX */
static void getDirName(char *path, char *pfx) {
	char	*p;

	if (strlen(path) > 256) {
		error("load: path too long", NOEXPR);
		return;
	}
	strcpy(pfx, path);
	p = strrchr(pfx, '/');
	if (p == NULL)
		strcpy(pfx, ".");
	else
		*p = 0;
}

/* Expand leading '~/' and '=' in path names */
static char *expandPath(char *s) {
	char	*var, *r, *v;

	if (!strncmp(s, "~/", 2)) {
		var = "HOME";
		r = &s[2];
	}
	else if (!strncmp(s, "=", 1)) {
		var = "ALISPSRC";
		r = &s[1];
	}
	else
		return s;
	if ((v = getenv(var)) == NULL) return s;
	if (strlen(v) + strlen(r) + 4 >= MAXPATHL) {
		error("load: path too long", NOEXPR);
		return s;
	}
	sprintf(ExpPath, "%s/%s", v, r);
	return ExpPath;
}

/* Attach default path to file name */
char *defaultPath(char *s) {
	char	*asrc;

	if (s[0] != '=') return s;
	s += 1;
	asrc = getenv("ALISPSRC");
	if (asrc == NULL) return s;
	if (strlen(asrc) + strlen(s) + 4 > MAXPATHL) {
		error("load: path too long", NOEXPR);
		return s;
	}
	sprintf(DflPath, "%s/%s.l", asrc, s);
	return DflPath;
}

/*
 * Load S-expressions from the external file or device
 * named in the string P. Return 0 on success and -1
 * in case of an error.
 */
static int load(char *p) {
	FILE	*ofile, *nfile;
	int	r;
	char	*oname;
	char	*arg;
	int	oline;

	arg = p;
	if (LoadLev > 0) {
		if (strlen(p) + strlen(DirName) + 2 >= MAXPATHL) {
			error("load: path too long", NOEXPR);
			return -1;
		}
		if (*p != '.' && *p != '/')
			sprintf(Path, "%s/%s", DirName, p);
		else
			strcpy(Path, p);
		p = Path;
	}
	else {
		p = expandPath(p);
		getDirName(p, DirName);
	}
	strcat(p, ".l");
	if ((nfile = fopen(p, "r")) == NULL) {
		p = defaultPath(arg);
		if ((nfile = fopen(p, "r")) == NULL) {
			error("cannot open source file", NOEXPR);
			Error.arg = arg;
			return -1;
		}
	}
	LoadLev = LoadLev + 1;
	/* Save old I/O state */
	r = Rejected;
	/* Run the toplevel loop with redirected I/O */
	ofile = Input;
	Input = nfile;
	oline = Line;
	Line = 1;
	oname = Infile;
	Infile = p;
	REL();
	Infile = oname;
	Line = oline;
	/* Restore previous I/O state */
	Rejected = r;
	Input = ofile;
	LoadLev = LoadLev - 1;
	fclose(nfile);
	if (Level) error("unbalanced parentheses in loaded file", NOEXPR);
	return 0;
}

/* Is c a special character? */
#define specialChar(c) \
		((c) == ' ' || \
		 (c) == '\t' || \
		 (c) == '\n' || \
		 (c) == '\r' || \
		 (c) == '(' || \
		 (c) == ')' || \
		 (c) == ';' || \
		 (c) == '.' || \
		 (c) == '#' || \
		 (c) == '\'')

/* Read a condensed list */
static int readCondensed(void) {
	int	n, c, a;
	char	s[2];

	n = alloc(NIL, NIL);
	a = NIL;
	s[1] = 0;
	c = rdch();
	while (!specialChar(c)) {
		if (a == NIL) {
			a = n;
		}
		else {
			Cdr[a] = alloc(NIL, NIL);
			a = Cdr[a];
		}
		s[0] = c;
		Car[a] = addSym(s, S_void);
		c = rdch();
	}
	Rejected = c;
	return n;
}

/* Explode a string to a list of single-char symbols */
static int explodeStr(char *sym) {
	int	n, a, i;
	char	s[2];

	n = alloc(NIL, NIL);
	a = NIL;
	s[1] = 0;
	i = 0;
	while (sym[i]) {
		if (a == NIL) {
			a = n;
		}
		else {
			Cdr[a] = alloc(NIL, NIL);
			a = Cdr[a];
		}
		s[0] = sym[i];
		Car[a] = addSym(s, S_void);
		i += 1;
	}
	return n;
}

/* Quote an expression */
static int quote(int n) {
	int	q;

	save(n);
	q = alloc(S_quote, NIL);
	save(q);
	Cdr[q] = alloc(n, NIL);
	unsave(2);
	return q;
}

/* Read a symbol and add it to the global symbol table */
static int symbol(int c) {
	char	s[TEXTLEN];
	int	i;

	i = 0;
	while (!specialChar(c)) {
		if (i >= TEXTLEN-2) {
			error("symbol too long", NOEXPR);
			i = i-1;
		}
		s[i] = c;
		i = i+1;
		c = rdch();
	}
	s[i] = 0;
	Rejected = c;
	return addSym(s, S_void);
}

/* Check whether (EQUAL N M) */
static int equals(int n, int m) {
	if (n == m) return 1;
	if (n == NIL || m == NIL) return 0;
	if (Tag[n] & AFLAG || Tag[m] & AFLAG) return 0;
	return equals(Car[n], Car[m])
	    && equals(Cdr[n], Cdr[m]);
}

/* Verify most recently evaluated expression */
static void verify(void) {
	int	expected;

	expected = xread();
	if (expected != NIL && !atomic(expected))
		expected = Car[Cdr[expected]];
	if (!equals(expected, Cdr[S_last]))
		error("Verification failed; expected", expected);
}

/* Report an unreadable object */
static int unReadable(void) {
	#define	L 256
	int		c, i;
	static char	b[L];

	i = 0;
	b[0] = '{';
	while (c != '}' && c != EOT && i < L-2) {
		b[i++] = c;
		c = rdch();
	}
	b[i] = '}';
	b[i+1] = 0;
	Error.arg = b;
	return error("unreadable object", NOEXPR);
}

/*
 * Read an expression from the current input stream
 * and return (a pointer to) it.
 */
static int xread(void) {
	int	c;

	c = rdch();
	while (1) {	/* Skip spaces and comments */
		while (c == ' ' || c == '\t' || c == '\n' || c == '\r') {
			if (ErrFlag) return NIL;
			c = rdch();
		}
		if (c == '=' && Level == 0) {
			c = rdch();
			if (c != '>') {
				Rejected = c;
				c = '=';
				break;
			}
			if (VerifyArrows) verify();
		}
		else if (c != ';')
			break;
		while (c != '\n') c = rdch();
	}
	if (c == EOT) return EOT;
	if (c == '(') {
		return readList();
	}
	else if (c == '\'') {
		return quote(xread());
	}
	else if (c == '#') {
		return readCondensed();
	}
	else if (c == ')') {
		if (!Level) return error("unexpected ')'", NOEXPR);
		return RPAREN;
	}
	else if (c == '.') {
		if (!Level) return error("unexpected '.'", NOEXPR);
		return DOT;
	}
	else if (c == '{') {
		return unReadable();
	}
	else {
		return symbol(c);
	}
}

/* Common error reporting routines... */

static int wrongArgs(int n) {
	return error("wrong argument count", n);
}

static int badArgLst(int n) {
	return error("bad argument list", n);
}

/* Evaluate N=(CONS M M2) */
static int doCons(int n) {
	int	m, m2;

	m = Cdr[n];
	if (m == NIL || Cdr[m] == NIL || Cdr[Cdr[m]] != NIL)
		return wrongArgs(n);
	m2 = Car[Cdr[m]];
	m = alloc(Car[m], m2);
	return m;
}

/* Evaluate N=(CAR M) */
static int doCar(int n) {
	int	m;

	m = Cdr[n];
	if (m == NIL || Cdr[m] != NIL) return wrongArgs(n);
	if (atomic(Car[m]) || Car[m] == NIL)
		return error("car: cannot split atoms", Car[m]);
	m = Car[m];
	if (	Car[m] == S_primitive ||
		Car[m] == S_special ||
		Car[m] == S_special_cbv
	)
		error("car: internal type", m);
	return Car[m];
}

/* Evaluate N=(CDR M) */
static int doCdr(int n) {
	int	m;

	m = Cdr[n];
	if (m == NIL || Cdr[m] != NIL) return wrongArgs(n);
	if (atomic(Car[m]) || Car[m] == NIL)
		return error("cdr: cannot split atoms", Car[m]);
	m = Car[m];
	if (	Car[m] == S_primitive ||
		Car[m] == S_special ||
		Car[m] == S_special_cbv
	)
		error("cdr: internal type", m);
	return Cdr[m];
}

/* Evaluate N=(EQ M M2) */
static int doEq(int n) {
	int	m;

	m = Cdr[n];
	if (m == NIL || Cdr[m] == NIL || Cdr[Cdr[m]] != NIL)
		return wrongArgs(n);
	return Car[m] == Car[Cdr[m]]? S_true: S_false;
}

/* Evaluate N=(ATOM M) */
static int doAtom(int n) {
	int	m;

	m = Cdr[n];
	if (m == NIL || Cdr[m] != NIL) return wrongArgs(n);
	m = Car[m];
	return atomic(m) || m == NIL? S_true: S_false;
}

/* Evaluate N=(EXPLODE M) */
static int doExplode(int n) {
	int	m, y, a;
	char	s[2];

	m = Cdr[n];
	if (m == NIL || Cdr[m] != NIL) return wrongArgs(n);
	m = Car[m];
	if (m == NIL) return NIL;
	if (!atomic(m)) return error("explode: got non-symbol", m);
	y = alloc(NIL, NIL);
	save(y);
	a = y;
	m = Car[m];
	s[1] = 0;
	while (m != NIL) {
		s[0] = Car[m];
		Car[a] = addSym(s, S_void);
		m = Cdr[m];
		if (m != NIL) {
			Cdr[a] = alloc(NIL, NIL);
			a = Cdr[a];
		}
	}
	unsave(1);
	return y;
}

/* Evaluate N=(IMPLODE M) */
static int doImplode(int n) {
	int	m, i;
	char	s[TEXTLEN];

	m = Cdr[n];
	if (m == NIL || Cdr[m] != NIL) return wrongArgs(n);
	m = Car[m];
	if (m == NIL) return NIL;
	i = 0;
	while (m != NIL) {
		if (!atomic(Car[m]))
			return error("implode: non-symbol in argument",
				Car[m]);
		if (Cdr[Car[Car[m]]] != NIL)
			return error(
			  "implode: input symbol has multiple characters",
				Car[m]);
		if (i >= TEXTLEN-1)
			return error("implode: output symbol too long", m);
		s[i] = Car[Car[Car[m]]];
		i += 1;
		m = Cdr[m];
	}
	s[i] = 0;
	return addSym(s, S_void);
}

/* Extract clause from argument list of COND. */
/* Check the syntax of the clause. */
/* Return the predicate of the clause. */
static int getPred(void) {
	int	e;

	e = Car[Car[Bstack]];
	if (	atomic(e) || e == NIL ||
		Cdr[e] == NIL || Cdr[Cdr[e]] != NIL
	)
		return error("cond: bad clause", e);
	return Car[e];
}

/*
 * Setup context for evaluation of COND.
 * The context consists of a list of clauses.
 * Return the predicate of the first clause.
 */
static int setupCond(int n) {
	int	m;

	m = Cdr[n];
	if (m == NIL) return wrongArgs(n);
	bsave(m);
	return getPred();
}

/*
 * Evaluate next clause of COND.
 * N is the value of the current predicate.
 * If N=T, return the expression of the predicate.
 * If N=FALSE, return the predicate of the next clause.
 * When returning the expression of a predicate (N=T),
 * set the context on the Bstack to NIL to signal that
 * a true clause was found.
 */
static int evalClause(int n) {
	int	e;

	e = Car[Bstack];
	if (n == S_false) {
		Car[Bstack] = Cdr[e];
		if (Car[Bstack] == NIL)
			return error("cond: no default", NOEXPR);
		return getPred();
	}
	else {
		e = Car[Cdr[Car[e]]];
		Car[Bstack] = NIL;
		return e;
	}
}

/*
 * Setup context for evaluation of AND and OR.
 * Return the first expression of the form.
 */
static int setupLogOp(int n) {
	int	m;

	m = Cdr[n];
	if (m == NIL) return wrongArgs(n);
	bsave(m);
	return Car[m];
}

/*
 * Unbind the arguments of LAMBDA, LET and LETREC.
 * See also bindArgs().
 */
static void unbindArgs(void) {
	int	v;

	Frame = unsave(1);
	Function = unsave(1);
	v = bunsave(1);		/* Caller's namelist */
	while (v != NIL) {
		Cdr[Car[v]] = unsave(1);
		v = Cdr[v];
	}
}

/*
 * Check whether the symbol N is bound in the current
 * lexical environment.
 */
static int isBound(int n) {
	int	b;

	b = Bound;
	while (b != NIL) {
		if (atomic(b)) {
			if (n == b) return 1;
			break;
		}
		if (n == Car[b]) return 1;
		b = Cdr[b];
	}
	b = Car[LexEnv];
	while (b != NIL) {
		if (Car[Car[b]] == n) return 1;
		b = Cdr[b];
	}
	return 0;
}

/*
 * Recursively collect free variables and add their symbols
 * and values to the current lexical environment.
 */
static void collect(int n) {
	if (n == NIL || (Tag[n] & AFLAG)) return;
	if (atomic(n)) {
		if (isBound(n)) return;
		Car[LexEnv] = alloc(NIL, Car[LexEnv]);
		Car[Car[LexEnv]] = alloc(n, Car[n] == Cdr[n]? n: Cdr[n]);
		return;
	}
	/*
	 * Avoid inclusion of quoted forms.
	 * We cannot just check for Car[n] == S_quote,
	 * because this would also catch (list quote foo),
	 * where foo is a free variable.
	 * By checking Car[Car[n]], we make sure that
	 * quote is actually in a car position.
	 * NOTE: this also prevents (quote . (internal quote))
	 * from being included, but who wants to re-define
	 * QUOTE anyway?
	 */
	if (atomic(Car[n]) || Car[Car[n]] != S_quote)
		collect(Car[n]);
	collect(Cdr[n]);
}

/* Create lexical environment */
static int mkLexEnv(int term, int locals) {
	LexEnv = alloc(NIL, NIL);
	save(LexEnv);
	Bound = locals;
	collect(term);
	unsave(1);
	return Car[LexEnv];
}

/* Create a closure from a lambda expression */
static int closure(int n) {
	int	cl, env, args, term;

	if (ErrFlag) return NIL;
	cl = alloc(S_closure, NIL);
	save(cl);
	args = Car[Cdr[n]];
	Cdr[cl] = alloc(args, NIL);
	term = Car[Cdr[Cdr[n]]];
	Cdr[Cdr[cl]] = alloc(term, NIL);
	if (Cdr[Cdr[Cdr[n]]] == NIL) {
		env = mkLexEnv(term, args);
		save(env);
		if (env != NIL) {
			Cdr[Cdr[Cdr[cl]]] = alloc(env, NIL);
			if (Estack != NIL) Estack = alloc(env, Estack);
		}
		unsave(1);
	}
	else {
		Cdr[Cdr[Cdr[cl]]] = alloc(Car[Cdr[Cdr[Cdr[n]]]], NIL);
	}
	unsave(1);
	return cl;
}

/* Fix cached recursive bindings in closures */
static void fixCachedClosures(void) {
	int	a, ee, e;

	if (ErrFlag || Estack == NIL || Estack == S_true) return;
	a = Car[Bstack];
	while (a != NIL) {
		ee = Estack;
		while (ee != NIL && ee != S_true) {
			e = Car[ee];
			while (e != NIL) {
				if (Car[a] == Car[Car[e]]) {
					Cdr[Car[e]] = Cdr[Car[a]];
					break;
				}
				e = Cdr[e];
			}
			ee = Cdr[ee];
		}
		a = Cdr[a];
	}
}

/* Check whether N is an alist */
static int isAlist(int n) {
	if (atomic(n)) return 0;
	while (n != NIL) {
		if (atomic(Car[n]) || !atomic(Car[Car[n]]))
			return 0;
		n = Cdr[n];
	}
	return -1;
}

/* Check whether M is a list of symbols */
static int isSymList(int m) {   
	while (m != NIL) {
		if (!atomic(Car[m])) return 0;
		if (atomic(Cdr[m])) break;
		m = Cdr[m];
	}
	return 1;
}

/*
 * Fix references to symbols of BINDINGS
 * in all closures of N.
 */
static void fixClosuresOf(int n, int bindings) {
	int	ee, e;
	int	bb, b;

	if (n == NIL || atomic(n)) return;
	if (Car[n] == S_closure) {
		fixClosuresOf(Car[Cdr[Cdr[n]]], bindings);
		ee = Cdr[Cdr[Cdr[n]]];
		if (ee == NIL) return;
		ee = Car[ee];
		while (ee != NIL) {
			e = Car[ee];
			bb = bindings;
			while (bb != NIL) {
				b = Car[bb];
				if (Car[b] == Car[e])
					Cdr[e] = Cdr[b];
				bb = Cdr[bb];
			}
			ee = Cdr[ee];
		}
		return;
	}
	fixClosuresOf(Car[n], bindings);
	fixClosuresOf(Cdr[n], bindings);
}

/*
 * Fix recursive bindings in closures.
 * This is a version of fixCachedClosures
 * that does not use any cache (Estack).
 */
static void fixAllClosures(int b) {
	int	p;

	p = b;
	while (p != NIL) {
		fixClosuresOf(Cdr[Car[p]], b);
		p = Cdr[p];
	}
}

/* Evaluate N=(RECURSIVE-BIND M) */
static int doRecursiveBind(int n) {
	int	m, env;

	m = Cdr[n];
	if (m == NIL || Cdr[m] != NIL) return wrongArgs(n);
	env = Car[m];
	if (!isAlist(env))
		return error("recursive-bind: bad environment", env);
	fixAllClosures(env);
	return env;
}

/*
 * Set up a context for processing
 *     N=(LET ((MA1 eval[MX2]) ...) MN)
 * and N=(LETREC ((MA1 eval[MX2]) ...) MN).
 * Save
 * - the complete LET/LETREC expression on the Bstack
 * - the environment on the Bstack
 * - a list of new bindings on the Bstack (initially empty)
 * - two copies of the list of saved names on the Stack
 */
static int setupLet(int n) {
	int	m;

	m = Cdr[n];
	if (m == NIL || Cdr[m] == NIL || Cdr[Cdr[m]] != NIL)
		return wrongArgs(n);
	m = Car[m];
	if (atomic(m))
		return error("let/letrec: bad environment", m);
	bsave(n);	/* save entire LET/LETREC */
	bsave(m);	/* save environment */
	bsave(NIL);	/* list of bindings */
	bsave(NIL);	/* save empty name list */
	save(Estack);	/* get outer binding out of the way */
	Estack = NIL;
	return m;
}

/*
 * Process one binding of LET/LETREC:
 * bind value to name, advance to next binding.
 * Return:
 * non-NIL - more bindings in environment
 * NIL     - last binding done
 */
static int nextLet(int n) {
	int	m, p;

	m = Car[Cdr[Cdr[Bstack]]];	/* rest of environment */
	if (m == NIL) return NIL;
	p = Car[m];
	Tmp2 = n;
	Car[Cdr[Bstack]] = alloc(NIL, Car[Cdr[Bstack]]);
	Car[Car[Cdr[Bstack]]] = alloc(Car[p], n);
	Tmp2 = NIL;
	Car[Cdr[Cdr[Bstack]]] = Cdr[m];
	return Cdr[m];
}

/*
 * Evaluate value to bind inside of LET/LETREC:
 * - check syntax
 * - save name to bind to
 * - save original binding of name
 * - return (unevaluated) value
 */
static int evalLet(void) {
	int	m, p, v;

	m = Car[Cdr[Cdr[Bstack]]];
	p = Car[m];
	/* Each binding must have the form (atom expr) */
	if (	atomic(p) || Cdr[p] == NIL || atomic(Cdr[p]) ||
		Cdr[Cdr[p]] != NIL || !atomic(Car[p])
	) {
		/* In case of an error, get rid of the */
		/* partial environment. */
		v = bunsave(1);
		bunsave(3);
		bsave(v);
		Estack = unsave(1);
		save(Function);
		save(Frame);
		unbindArgs();
		return error("let/letrec: bad binding", p);
	}
	Car[Bstack] = alloc(Car[p], Car[Bstack]);	/* Save name */
	/* Evaluate the new value of the current symbol */
	return Car[Cdr[p]];
}

/* Reverse a list in situ */
static int nreverse(int n) {
	int	this, next, x;

	if (n == NIL) return NIL;
	this = n;
	next = Cdr[n];
	Cdr[this] = NIL;
	while (next != NIL) {
		x = Cdr[next];
		Cdr[next] = this;
		this = next;
		next = x;
	}
	return this;
}

/* Establish the bindings of LET/LETREC. */
static void bindLet(int env) {
	int	b;

	while (env != NIL) {
		b = Car[env];
		save(Cdr[Car[b]]);	/* Save old value */
		Cdr[Car[b]] = Cdr[b];	/* Bind new value */
		env = Cdr[env];
	}
}

/*
 * Finish processing bindings of LET/LETREC:
 * finish context and return term.
 */
static int finishLet(int rec) {
	int	m, v, b, e;

	Tmp2 = alloc(NIL, NIL);	/* Create safe storage */
	Cdr[Tmp2] = alloc(NIL, NIL);
	Cdr[Cdr[Tmp2]] = alloc(NIL, NIL);
	Cdr[Cdr[Cdr[Tmp2]]] = alloc(NIL, NIL);
	v = bunsave(1);
	b = bunsave(1);		/* get bindings */
	m = bunsave(2);		/* drop environment, get full LET/LETREC */
	b = nreverse(b);	/* needed for UNBINDARGS() */
	e = unsave(1);		/* outer Estack */
	Car[Tmp2] = b;		/* protect b, m, v, e */
	Car[Cdr[Tmp2]] = m;
	Car[Cdr[Cdr[Tmp2]]] = v;
	Cdr[Cdr[Cdr[Tmp2]]] = e;
	bindLet(b);
	bsave(v);
	if (rec) fixCachedClosures();
	Estack = e;
	save(Function);		/* required by UNBINDARGS() */
	save(Frame);
	Tmp2 = NIL;
	return Car[Cdr[Cdr[m]]];	/* return term of LET/LETREC */
}

/* Evaluate N=(BOTTOM ...) */
static int doBottom(int n) {
	save(n);
	n = alloc(S_bottom, Cdr[n]);
	unsave(1);
	return error("", n);
}

/* Copy names and values of the symbol table into an alist */
static int copyBindings(void) {
	int	y, p, ny, pk, q;

	pk = Packages;
	p = alloc(NIL, NIL);
	save(p);
	ny = p;
	q = NIL;
	while (pk != NIL) {
		y = Cdr[Car[pk]];
		while (y != NIL) {
			Car[p] = alloc(Car[y], Cdr[Car[y]]);
			y = Cdr[y];
			Cdr[p] = alloc(NIL, NIL);
			q = p;
			p = Cdr[p];
		}
		pk = Cdr[pk];
	}
	if (q != NIL) Cdr[q] = NIL;
	unsave(1);
	return Car[ny] == NIL? NIL: ny;
}

/* Restore values of the symbol table */
static void restoreBindings(int values) {
	int	b;

	while (values != NIL) {
		b = Car[values];
		Cdr[Car[b]] = Cdr[b];
		values = Cdr[values];
	}
}

/* Evaluate N=(READ) */
static int doRead(int n) {
	if (Cdr[n] != NIL) return wrongArgs(n);
	n = xread();
	if (alisp_eof(n)) {
		error("read: got EOT", NOEXPR);
		return NIL;
	}
	return n;
}

/* Evaluate N=(WRITE M) */
static int doWrite(int n) {
	int	m;

	m = Cdr[n];
	if (m == NIL || Cdr[m] != NIL) return wrongArgs(n);
	Quoted = 0;
	_print(Car[m]);
	nl();
	return Car[m];
}

/* Dump node pool to file */
static int dump_image(char *p) {
	int	fd, n, i;
	int	**v;
	char	magic[17];

	fd = open(p, O_CREAT | O_WRONLY, 0644);
	setmode(fd, O_BINARY);
	if (fd < 0) {
		error("cannot create file", NOEXPR);
		Error.arg = p;
		return -1;
	}
	strcpy(magic, "ALISP___________");
	magic[7] = sizeof(int);
	magic[8] = ALISP_MAJOR;
	n = 0x12345678;
	memcpy(&magic[10], &n, sizeof(int));
	write(fd, magic, 16);
	n = PoolSize;
	write(fd, &n, sizeof(int));
	v = ImageVars;
	i = 0;
	while (v[i]) {
		write(fd, v[i], sizeof(int));
		i = i+1;
	}
	if (	write(fd, Car, PoolSize*sizeof(int)) != PoolSize*sizeof(int) ||
		write(fd, Cdr, PoolSize*sizeof(int)) != PoolSize*sizeof(int) ||
		write(fd, Tag, PoolSize) != PoolSize
	) {
		error("dump failed", NOEXPR);
		close(fd);
		return -1;
	}
	close(fd);
	return 0;
}

/* Evaluate N=(DEFINED M) */
static int doDefined(int n) {
	int	m;

	m = Cdr[n];
	if (m == NIL || Cdr[m] != NIL) return wrongArgs(n);
	if (!atomic(Car[m])) return error("defined: got non-symbol", Car[m]);
	return Cdr[Car[m]] == S_void? S_false: S_true;
}

/* Evaluate N=(GC) */
static int doGC(int n) {
	int	m;
	char	s[20];

	m = Cdr[n];
	if (m != NIL) return wrongArgs(n);
	n = alloc(NIL, NIL);
	save(n);
	sprintf(s, "%d", gc());
	Car[n] = explodeStr(s);
	Cdr[n] = alloc(NIL, NIL);
	sprintf(s, "%d", MaxAtoms);
	MaxAtoms = 0;
	Car[Cdr[n]] = explodeStr(s);
	unsave(1);
	return n;
}

/* Evaluate N=(QUIT) */
static int doQuit(int n) {
	int	m;

	m = Cdr[n];
	if (m != NIL) return wrongArgs(n);
	alisp_fini();
	exit(0);
}

/* Evaluate N=(SYMBOLS) */
static int doSymbols(int n) {
	int	m;

	m = Cdr[n];
	if (m != NIL) return wrongArgs(n);
	return Symbols;
}

/* Evaluate N=(VERIFY-ARROWS N) */
static int doVerifyArrows(int n) {
	int	m;

	m = Cdr[n];
	if (m == NIL || Cdr[m] != NIL) return wrongArgs(n);
	m = Car[m];
	if (m != S_true && m != S_false)
		return error("verify-arrows: got non truth-value", m);
	VerifyArrows = m == S_true;
	return m;
}

/*
 * Check whether (CAR NP[0]) is a builtin procedure.
 * If it is one, run the corresponding routine, save
 * its result in NP[0], and return -1.
 * Return 0 if (CAR NP[0]) is not a builtin procedure.
 */
static int primitive(int *np) {
	int	n, y;
	int	(*op)(int);

	n = np[0];
	y = Car[n];
	if (ErrFlag) return 0;
	if (Car[y] == S_primitive) {
		op = Primitives[Car[Cdr[y]]];
	}
	else {
		return 0;
	}
	n = (*op)(n);
	np[0] = n;
	return -1;
}

/* Evaluate N=(AND ...) */
static int doAnd(int n, int *pcf, int *pmode, int *pcbn) {
	USE(pcbn);
	if (Cdr[n] == NIL) {
		return S_true;
	}
	else if (Cdr[Cdr[n]] == NIL) {
		*pcf = 1;
		return Car[Cdr[n]];
	}
	else {
		*pcf = 2;
		*pmode = MCONJ;
		return setupLogOp(n);
	}
}

/* Evaluate N=(APPLY M) */
static int doApply(int n, int *pcf, int *pmode, int *pcbn) {
	int	m, p;

	*pcf = 1;
	USE(pmode);
	*pcbn = 1;
	m = Cdr[n];
	if (m == NIL || Cdr[m] == NIL || Cdr[Cdr[m]] != NIL)
		return wrongArgs(n);
	if (Car[m] == NIL || atomic(Car[m]))
		return error("apply: got non-procedure", Car[m]);
	p = Car[Car[m]];
	if (	p != S_primitive &&
		p != S_special &&
		p != S_special_cbv &&
		p != S_closure
	)
		return error("apply: got non-procedure", Car[m]);
	p = Car[Cdr[m]];
	while (p != NIL) {
		if (atomic(p)) return
			error("apply: improper argument list", Car[Cdr[m]]);
		p = Cdr[p];
	}
	return alloc(Car[m], Car[Cdr[m]]);
}

/* Evaluate N=(COND M1 ...) */
static int doCond(int n, int *pcf, int *pmode, int *pcbn) {
	*pcf = 2;
	*pmode = MCOND;
	USE(pcbn);
	return setupCond(n);
}

/* Evaluate N=(DEFINE (M ...) M2) */
static int newDefine(int n) {
	int	m, y;

	m = Cdr[n];
	if (Car[m] == NIL)
		return error("define: missing function name",
			Car[m]);
	if (!isSymList(Car[m])) return badArgLst(Car[m]);
	y = Car[Car[m]];
	save(Car[Cdr[m]]);
	Tmp2 = alloc(S_lambda, NIL);
	Cdr[Tmp2] = alloc(Cdr[Car[m]], NIL);
	Cdr[Cdr[Tmp2]] = alloc(Car[Cdr[m]], NIL);
	Cdr[Cdr[Cdr[Tmp2]]] = alloc(NIL, NIL);
	y = localize(y, &Car[Cdr[m]]);
	Cdr[y] = eval(Tmp2);
	Tmp2 = NIL;
	unsave(1);
	return Car[Car[m]];
}

/*
 * Evaluate N=(DEFINE M eval[M2])
 * The name M already has been added to the
 * symbol table by READ().
 */
static int doDefine(int n, int *pcf, int *pmode, int *pcbn) {
	int	m, v, y;

	if (EvLev > 1) {
		error("define: limited to top level", NOEXPR);
		return NIL;
	}
	m = Cdr[n];
	if (m == NIL || Cdr[m] == NIL || Cdr[Cdr[m]] != NIL)
		return wrongArgs(n);
	y = Car[m];
	if (!atomic(y)) return newDefine(n);
	/* Protect the unevaluated expression */
	v = Car[Cdr[m]];
	save(v);
	/* If we are binding to a lambda expression, */
	/* add a null environment */
	if (!atomic(v) && Car[v] == S_lambda) {
		if (	Cdr[v] != NIL && Cdr[Cdr[v]] != NIL &&
			Cdr[Cdr[Cdr[v]]] == NIL
		) {
			Cdr[Cdr[Cdr[v]]] = alloc(NIL, NIL);
		}
	}
	y = localize(y, &Car[Cdr[m]]);
	/* Evaluate and bind second argument */
	Cdr[y] = eval(Car[Cdr[m]]);
	unsave(1);
	return y;
}

/* Evaluate an expression and return its normal form */
static int doEval(int n, int *pcf, int *pmode, int *pcbn) {
	int	m;

	*pcf = 1;
	USE(pmode);
	*pcbn = 0;
	m = Cdr[n];
	if (m == NIL || Cdr[m] != NIL) return wrongArgs(n);
	return (Car[m]);
}

/* Check LAMBDA syntax and create closure from lambda expression. */
static int doLambda(int n, int *pcf, int *pmode, int *pcbn) {
	int	m;

	m = Cdr[n];
	if (	m == NIL || Cdr[m] == NIL ||
		(Cdr[Cdr[m]] != NIL && Cdr[Cdr[Cdr[m]]] != NIL)
	)
		return wrongArgs(n);
	if (Cdr[Cdr[m]] != NIL && !isAlist(Car[Cdr[Cdr[m]]]))
		return error("lambda: bad environment",
			Car[Cdr[Cdr[m]]]);
	if (!atomic(Car[m]) && !isSymList(Car[m]))
		return badArgLst(Car[m]);
	return Car[n] == S_closure? n: closure(n);
}

/* Evaluate N=(LET ENV EXPR) */
static int doLet(int n, int *pcf, int *pmode, int *pcbn) {
	*pcf = 2;
	*pmode = MBIND;
	USE(pcbn);
	if (setupLet(n) != NIL)
		return evalLet();
	else
		return NIL;
}

/* Evaluate N=(LETREC ENV EXPR) */
static int doLetrec(int n, int *pcf, int *pmode, int *pcbn) {
	int	m;

	*pcf = 2;
	*pmode = MBINR;
	USE(pcbn);
	if (setupLet(n) != NIL)
		m = evalLet();
	else
		m = NIL;
	Estack = S_true;
	return m;
}

/* Evaluate N=(OR ...) */
static int doOr(int n, int *pcf, int *pmode, int *pcbn) {
	USE(pcbn);
	if (Cdr[n] == NIL) {
		return S_false;
	}
	else if (Cdr[Cdr[n]] == NIL) {
		*pcf = 1;
		return Car[Cdr[n]];
	}
	else {
		*pcf = 2;
		*pmode = MDISJ;
		return setupLogOp(n);
	}
}

/* Evaluate N=(QUOTE M) */
static int doQuote(int n, int *pcf, int *pmode, int *pcbn) {
	int	m;

	USE(pcf);
	USE(pmode);
	USE(pcbn);
	m = Cdr[n];
	if (m == NIL || Cdr[m] != NIL) return wrongArgs(n);
	return (Car[m]);
}

/* Evaluate N=(CLOSURE-FORM M) */
static int doClosureForm(int n, int *pcf, int *pmode, int *pcbn) {
	int		m;

	USE(pcf);
	USE(pmode);
	USE(pcbn);
	m = Cdr[n];
	if (m == NIL || Cdr[m] != NIL) return wrongArgs(n);
	if (!atomic(Car[m]))
		return error("closure-form: got non-symbol", Car[m]);
	if (Car[m] == addSym("args", S_void))
		ClosureForm = 0;
	else if (Car[m] == addSym("body", S_void))
		ClosureForm = 1;
	else if (Car[m] == addSym("env", S_void))
		ClosureForm = 2;
	else
		return S_false;
	return Car[m];
}

/* Evaluate N=(DUMP-IMAGE M) */
static int doDumpImage(int n, int *pcf, int *pmode, int *pcbn) {
	int		m;
	static char	buf[TEXTLEN], *s;

	USE(pcf);
	USE(pmode);
	USE(pcbn);
	m = Cdr[n];
	if (m == NIL || Cdr[m] != NIL) return wrongArgs(n);
	if (!atomic(Car[m])) return error("dump-image: got non-symbol",
					Car[m]);
	s = symToStr(Car[m], buf, TEXTLEN);
	if (s) dump_image(s);
	return S_true;
}

/* Evaluate N=(LOAD M) */
static int doLoad(int n, int *pcf, int *pmode, int *pcbn) {
	int	m;
	char	buf[TEXTLEN+1], *s;

	USE(pcf);
	USE(pmode);
	USE(pcbn);
	m = Cdr[n];
	if (m == NIL || Cdr[m] != NIL) return wrongArgs(n);
	if (!atomic(Car[m])) return error("load: got non-symbol", Car[m]);
	s = symToStr(Car[m], buf, TEXTLEN);
	if (s) {
		s = strdup(s);
		if (s == NULL) fatal("load: strdup() failed");
		load(s);
		free(s);
	}
	return S_true;
}

/* Evaluate N=(PACKAGE [N1]) */
static int doPackage(int n, int *pcf, int *pmode, int *pcbn) {
	int	m;

	USE(pcf);
	USE(pmode);
	USE(pcbn);
	m = Cdr[n];
	if (m != NIL && Cdr[m] != NIL)
		return wrongArgs(n);
	m = m == NIL? NIL: Car[m];
	Symbols = addPackage(m);
	return m;
}

/* Evaluate N=(STATS M) */
static int doStats(int n, int *pcf, int *pmode, int *pcbn) {
	int	m;
	char	buf[100];

	USE(pcf);
	USE(pmode);
	USE(pcbn);
	m = Cdr[n];
	if (m == NIL || Cdr[m] != NIL) return wrongArgs(n);
	resetCounter(&Allocations);
	resetCounter(&Reductions);
	resetCounter(&Collections);
	StatFlag = 1;
	n = eval(Car[m]);
	StatFlag = 0;
	save(n);
	n = alloc(n, NIL);
	save(n);
	Cdr[n] = alloc(NIL, NIL);
	Car[Cdr[n]] = explodeStr(counterToStr(&Reductions, buf));
	Cdr[Cdr[n]] = alloc(NIL, NIL);
	Car[Cdr[Cdr[n]]] = explodeStr(counterToStr(&Allocations, buf));
	Cdr[Cdr[Cdr[n]]] = alloc(NIL, NIL);
	Car[Cdr[Cdr[Cdr[n]]]] = explodeStr(counterToStr(&Collections, buf));
	unsave(2);
	return n;
}

/* Evaluate N=(TRACE M) */
static int doTrace(int n, int *pcf, int *pmode, int *pcbn) {
	int		m;
	static char	buf[TEXTLEN], *s;

	USE(pcf);
	USE(pmode);
	USE(pcbn);
	m = Cdr[n];
	if (m == NIL) {
		Trace = NIL;
		return S_true;
	}
	if (Cdr[m] != NIL) return wrongArgs(n);
	if (!atomic(Car[m])) return error("trace: got non-symbol", Car[m]);
	s = symToStr(Car[m], buf, TEXTLEN);
	if (!s) return S_false;
	Trace = findSym(s);
	return S_true;
}

/*
 * Check whether (CAR NP[0]) is a special form handler.
 * If it is one, run the corresponding routine, save
 * its result in NP[0], and return -1.
 * Return 0 if (CAR NP[0]) is not a SF handler .
 */
static int special(int *np, int *pcf, int *pmode, int *pcbn) {
	int	n, y;
	int	(*op)(int, int *, int *, int *);

	n = np[0];
	y = Car[n];
	if (ErrFlag) return 0;
	if (Car[y] == S_special || Car[y] == S_special_cbv) 
		op = Specials[Car[Cdr[y]]];
	else if (atomic(y) &&
		(Car[Cdr[y]] == S_special ||
		 Car[Cdr[y]] == S_special_cbv)
	)
		op = Specials[Car[Cdr[Cdr[y]]]];
	else
		return 0;
	np[0] = (*op)(n, pcf, pmode, pcbn);
	return -1;
}

/*
 * Bind the arguments of a LAMBDA function.
 * For a lambda application N=((LAMBDA (X1 ... Xn) S [ENV]) Y1 ... Yn)
 * this includes the following steps for j in {1,...,n}:
 *	1) save Xj in V
 *	2) save the value of Xj
 *	3) bind Xj to Yj
 * This routine results in  S' == S[X1/Y1] ... [Xn/Yn].
 * S->S' is performed in the context created above.
 * bindArgs() has no function result.
 */
static void bindArgs(int n, int name) {
	int	fa,	/* Formal arg list */
		aa,	/* Actual arg list */
		e;	/* S, as above */
	int	env;	/* Optional lexical environment */
	int	p;
	int	at;	/* Atomic argument list flag */

	if (ErrFlag) return;
	fa = Car[Cdr[Car[n]]];
	at = atomic(fa);
	aa = Cdr[n];
	p = Cdr[Cdr[Car[n]]];
	e = Car[p];
	env = Cdr[p] != NIL ? Car[Cdr[p]]: NIL;
	bsave(NIL);
	while ((fa != NIL && aa != NIL) || at) {
		if (!at) {
			/* Save name */
			Car[Bstack] = alloc(Car[fa], Car[Bstack]);
			save(Cdr[Car[fa]]);		/* Save value */
			Cdr[Car[fa]] = Car[aa];		/* Bind arg */
			fa = Cdr[fa];
			aa = Cdr[aa];
		}
		if (atomic(fa)) {	/* improper argument list */
			Car[Bstack] = alloc(fa, Car[Bstack]);	/* Save name */
			save(Cdr[fa]);	/* Save value */
			Cdr[fa] = aa;	/* Bind remaining arg list */
			fa = NIL;
			aa = NIL;
			break;
		}
	}
	while (env != NIL) {
		p = Car[env];
		Car[Bstack] = alloc(Car[p], Car[Bstack]);/* Save name */
		save(Cdr[Car[p]]);		/* Save value */
		Cdr[Car[p]] = Cdr[p];		/* Bind lex val */
		env = Cdr[env];
	}
	if (fa != NIL || aa != NIL) {
		wrongArgs(n);
		n = NIL;
	}
	else {
		n = e;
	}
	save(Function);
	Function = name;
	save(Frame);
	Frame = Stack;
}

/*
 * Print application of traced function N in the form
 *	+ (NAME A1 ... An)
 * print() cannot be used because it would print NAME in
 * its expanded (LAMBDA...) form.
 */
static void printTrace(int n) {
	if (TraceHandler) {
		(*TraceHandler)(n);
		return;
	}
	pr("+ ");
	pr("(");
	Quoted = 1;
	_print(Trace);
	while (1) {
		n = Cdr[n];
		if (n == NIL) break;
		pr(" ");
		_print(Car[n]);
	}
	pr(")"); nl();
}

/* Do tail call optimization */
static void tailCall(void) {
	int	m, y;

	m = Car[Mstack];
	/* Skip over callee's LET/LETREC frames, if any */
	while (m != NIL && Car[m] == MLETR) {
		m = Cdr[m];
	}
	/* Parent not beta-reducing? Give up. */
	if (m == NIL || Car[m] != MBETA)
		return;
	/* Yes, this is a tail call: */
	/* - remove callee's LET/LETREC frames. */
	/* - remove caller's call frame. */
	while (1) {
		Tmp2 = unsave(1); /* M */
		unbindArgs();
		unsave(1);
		y = munsave();
		save(Tmp2);
		Tmp2 = NIL;
		if (y == MBETA) break;
	}
}

/*
 * Evaluate the term N and return its normal form.
 * This is the heart of the interpreter:
 * An iterative EVAL function with tail-call optimization.
 */
static int eval(int n) {
	int	m,	/* Result node */
		m2,	/* Root of result lists */
		a,	/* Used to append to result */
		cbn;	/* Use call-by-name/quotation in next iteration */
	int	mode,	/* Current state */
		cf;	/* Continue flag */
	int	nm;	/* Name of function to apply */

	EvLev = EvLev + 1;
	save(n);
	save(Lstack);
	save(Bstack);
	save(Car[Mstack]);
	save(Stack0);
	Stack0 = Stack;
	mode = MATOM;
	cf = 0;
	cbn = 0;
	while (!ErrFlag) {
		if (StatFlag) count(&Reductions, 1);
		if (n == NIL) {			/* () -> () */
			m = NIL;
			cbn = 0;
		}
		else if (atomic(n)) {		/* Symbol -> Value */
			if (cbn) {
				m = n;
				cbn = 0;
			}
			else {
				m = Cdr[n] == Car[n]? n: Cdr[n];
				if (m == S_void) {
					error("symbol not bound", n);
					break;
				}
			}
		}
		else if (Car[n] == S_closure ||
			Car[n] == S_primitive ||
			Car[n] == S_special ||
			Car[n] == S_special_cbv ||
			cbn == 2
		) {
			m = n;
			cbn = 0;
		}
		else {				/* List (...) and Pair (X.Y) */
			/*
			 * This block is used to DESCEND into lists.
			 * The following nodes/variables will be saved:
			 *	1) the original list (on Stack)
			 *	2) the current state (on Mstack)
			 *	3) the root of the result list (on Lstack)
			 *	4) a ptr to the next free node
			 *		in the result list (on Lstack)
			 *	5) a ptr to the next member of
			 *		the original list (on Lstack)
			 */
			m = Car[n];
			if (atomic(Cdr[n])) {
				error("improper list in application", n);
				n = NIL;
			}
			save(n);	/* Save original list */
			msave(mode);
			/* Check call-by-name built-ins and flag */
			if ((atomic(m) && Car[Cdr[m]] == S_special) || cbn) {
				cbn = 0;
				lsave(NIL);
				lsave(NIL);
				lsave(n);	/* Root of result list */
				n = NIL;
			}
			else {
				a = alloc(NIL, NIL);
				lsave(a);
				lsave(Cdr[n]);
				lsave(a);	/* Root of result list */
				n = Car[n];
			}
			mode = MLIST;
			continue;
		}
		/*
		 * The following loop is used to ASCEND back to the
		 * root of a list, thereby performing BETA reduction
		 * and creating result lists.
		 */
		while (1) if (mode == MBETA || mode == MLETR) {
			/* Finish BETA reduction */
			unbindArgs();
			unsave(1);	/* Original list */
			mode = munsave();
		}
		else if (mode == MLIST) {	/* Append to list, reduce */
			n = Car[Cdr[Lstack]];	/* Next member */
			a = Car[Cdr[Cdr[Lstack]]];	/* Place to appnd to */
			m2 = lunsave(1);	/* Root of result list */
			if (a != NIL)		/* Append new member */
				Car[a] = m;
			if (n == NIL) {		/* End of list */
				m = m2;
				lunsave(2);	/* Drop N,A */
 				/* Drop orig. list, remember first element */
				nm = Car[unsave(1)];
				save(m);	/* Save result */
				if (Trace == nm) printTrace(m);
				if (primitive(&m))
					;	/* primitive fn */
				else if (special(&m, &cf, &mode, &cbn))
					n = m;	/* special form */
				else if (!atomic(Car[m]) &&
					Car[m] != NIL &&
					Car[Car[m]] == S_closure
				) {
					/* Application: */
					/*   reduce ((lambda...)...) */
					nm = atomic(nm)? nm: NIL;
					/* If the caller is also */
					/* beta-reducing, */
					/* this is a tail application. */
					tailCall();
					bindArgs(m, nm);
					/* N=S of ((LAMBDA (...) S) ...) */
					n = Car[Cdr[Cdr[Car[m]]]];
					cf = 2;
					mode = MBETA;
				}
				else {
					error("application of non-function",
						nm);
					n = NIL;
				}
				if (cf != 2) {
					unsave(1);	/* Drop result */
					mode = munsave();
				}
				/* Continue this evaluation. */
				/* Leave the ASCENDING loop and descend */
				/* once more into N. */
				if (cf) break;
			}
			else {		/* N =/= NIL: Append to list */
				lsave(m2);
				/* Create space for next argument */
				Cdr[a] = alloc(NIL, NIL);
				Car[Cdr[Cdr[Lstack]]] = Cdr[a];
				Car[Cdr[Lstack]] = Cdr[n];
				n = Car[n];	/* Evaluate next member */
				break;
			}
		}
		else if (mode == MCOND) {
			n = evalClause(m);
			if (Car[Bstack] == NIL) {
				unsave(1);	/* Original list */
				bunsave(1);
				mode = munsave();
			}
			cf = 1;
			break;
		}
		else if (mode == MCONJ || mode == MDISJ) {
			Car[Bstack] = Cdr[Car[Bstack]];
			if (	(m == S_false && mode == MCONJ) || 
				(m != S_false && mode == MDISJ) ||
				Car[Bstack] == NIL
			) {
				unsave(1);	/* Original list */
				bunsave(1);
				mode = munsave();
				n = m;
				cbn = 2;
			}
			else if (Cdr[Car[Bstack]] == NIL) {
				n = Car[Car[Bstack]];
				unsave(1);	/* Original list */
				bunsave(1);
				mode = munsave();
			}
			else {
				n = Car[Car[Bstack]];
			}
			cf = 1;
			break;
		}
		else if (mode == MBIND || mode == MBINR) {
			if (nextLet(m) == NIL) {
				n = finishLet(mode == MBINR);
				mode = MLETR;
			}
			else {
				n = evalLet();
			}
			cf = 1;
			break;
		}
		else {	/* Atom */
			break;
		}
		if (cf) {	/* Continue evaluation if requested */
			cf = 0;
			continue;
		}
		if (Stack == Stack0) break;
	}
	while (Stack != Stack0) unsave(1);
	Stack0 = unsave(1);
	Car[Mstack] = unsave(1);
	Bstack = unsave(1);
	Lstack = unsave(1);
	unsave(1);
	EvLev = EvLev - 1;
	return m;		/* Return normal form */
}

/* Print expressions of the form (QUOTE X) as 'X */
static int printQuote(int n, int dot) {
	if (	Car[n] == S_quote &&
		Cdr[n] != NIL &&
		Cdr[Cdr[n]] == NIL
	) {
		if (dot) pr(" . ");
		n = Car[Cdr[n]];
		if (n != S_true && n != S_false) pr("'");
		_print(n);
		return 1;
	}
	return 0;
}

/* Print a condensed list */
static int printCondensed(int n, int dot) {
	int	m;
	char	s[2];

	m = n;
	if (m == NIL) return 0;
	while (m != NIL) {
		if (!atomic(Car[m])) return 0;
		if (Cdr[Car[Car[m]]] != NIL) return 0;
		m = Cdr[m];
	}
	if (dot) pr(" . ");
	pr("#");
	m = n;
	s[1] = 0;
	while (m != NIL) {
		s[0] = Car[Car[Car[m]]];
		pr(s);
		m = Cdr[m];
	}
	return -1;
}

/* Print a closure */
static int printClosure(int n, int dot) {
	if (	Car[n] == S_closure &&
		Cdr[n] != NIL && !atomic(Cdr[n]) &&
		Cdr[Cdr[n]] != NIL && !atomic(Cdr[Cdr[n]])
	) {
		Quoted = 1;
		if (dot) pr(" . ");
		pr(ClosureForm==2? "(closure ": "{closure ");
		_print(Car[Cdr[n]]);
		if (ClosureForm > 0) {
			pr(" ");
			_print(Car[Cdr[Cdr[n]]]);
			if (ClosureForm > 1 && Cdr[Cdr[Cdr[n]]] != NIL) {
				pr(" ");
				_print(Car[Cdr[Cdr[Cdr[n]]]]);
			}
		}
		pr(ClosureForm==2? ")": "}");
		return -1;
	}
	return 0;
}

/* Print a special form handler */
static int printProc(int n, int dot) {
	if (	Car[n] != S_primitive &&
		Car[n] != S_special &&
		Car[n] != S_special_cbv
	)
		return 0;
	if (dot) pr(" . ");
	pr("{internal ");
	Quoted = 1;
	_print(Cdr[Cdr[n]]);
	pr("}");
	return -1;
}

/* Recursively print the term N */
static void _print(int n) {
	char	s[TEXTLEN+1];
	int	i;

	if (n == NIL) {
		pr("()");
	}
	else if (n == S_void) {
		pr("{void}");
	}
	else if (Tag[n] & AFLAG) {
		/* Characters are limited to the symbol table */
		pr("{unprintable form}");
	}
	else if (atomic(n)) {
		if (!Quoted) {
			pr("'");
			Quoted = 1;
		}
		i = 0;		/* Symbol */
		n = Car[n];
		while (n != NIL) {
			s[i] = Car[n];
			if (i > TEXTLEN-2) break;
			i += 1;
			n = Cdr[n];
		}
		s[i] = 0;
		pr(s);
	}
	else {	/* List */
		if (printClosure(n, 0)) return;
		if (printProc(n, 0)) return;
		if (!Quoted) {
			pr("'");
			Quoted = 1;
		}
		if (printQuote(n, 0)) return;
		if (printCondensed(n, 0)) return;
		pr("(");
		while (n != NIL) {
			_print(Car[n]);
			n = Cdr[n];
			if (atomic(n) || n == S_void) {
				pr(" . ");
				_print(n);
				n = NIL;
			}
			if (printClosure(n, 1)) break;
			if (printProc(n, 1)) break;
			if (printQuote(n, 1)) break;
			/* if (printCondensed(n, 1)) break; */
			if (n != NIL) pr(" ");
		}
		pr(")");
	}
}

/* Reset interpreter state */
static void resetState(void) {
	Stack = NIL;
	Lstack = NIL;
	Bstack = NIL;
	Estack = NIL;
	Frame = NIL;
	Function = NIL;
	EvLev = 0;
	Level = 0;
}

/* Initialize interpreter variables. */
static void init1() {
	/* Misc. variables */
	NIL = PoolSize;
	Level = 0;
	resetState();
	Mstack = NIL;
	ErrFlag = 0;
	Error.arg = NULL;
	FatalFlag = 0;
	Symbols = NIL;
	Packages = NIL;
	SafeSymbols = NIL;
	Tmp = NIL;
	Tmp2 = NIL;
	LoadLev = 0;
	Trace = NIL;
	TraceHandler = NULL;
	MaxAtoms = 0;
	Ntrace = 10;
	StatFlag = 0;
	ClosureForm = 0;
	VerifyArrows = 0;
	Line = 1;
	/* Initialize Freelist */
	Free = NIL;
	/* Clear input buffer */
	Infile = NULL;
	DirName[0] = 0;
	Input = stdin;
	Output = stdout;
	Rejected = EOT;
}

/*
 * Second stage of initialization:
 * protect registers from GC,
 * build the free list,
 * create builtin symbols.
 */
static void init2(void) {
	int	core;

	/* Protect root registers */
	Root[0] = &Symbols;
	Root[1] = &Stack;
	Root[2] = &Mstack;
	Root[3] = &Lstack;
	Root[4] = &Bstack;
	Root[5] = &Estack;
	Root[6] = &Tmp;
	Root[7] = &Tmp2;
	Root[8] = &SafeSymbols;
	Root[9] = &Packages;
	/* 
	 * Create builtin symbols.
	 * Tags (especially 'primitive and 'special*)
	 * must be defined before any primitives.
	 * First GC will be triggered HERE
	 */
	S_void = addSym("{void}", 0);
	S_special = addSym("{special}", 0);
	S_special_cbv = addSym("{special/cbv}", 0);
	S_primitive = addSym("{primitive}", 0);
	S_closure = addSym("closure", 0);
	addPrim("atom", P_ATOM);
	addSpecial("and", SF_AND, 0);
	addSpecial("apply", SF_APPLY, 1);
	S_bottom = addPrim("bottom", P_BOTTOM);
	addPrim("car", P_CAR);
	addPrim("cdr", P_CDR);
	addSpecial("closure-form", SF_CLOSURE_FORM, 0);
	addSpecial("cond", SF_COND, 0);
	addPrim("cons", P_CONS);
	addSpecial("define", SF_DEFINE, 0);
	addPrim("defined", P_DEFINED);
	addSpecial("dump-image", SF_DUMP_IMAGE, 0);
	addPrim("eq", P_EQ);
	addSpecial("eval", SF_EVAL, 1);
	addPrim("explode", P_EXPLODE);
	S_false = addSym(":f", 0);
	addPrim("gc", P_GC);
	addPrim("implode", P_IMPLODE);
	S_lambda = addSpecial("lambda", SF_LAMBDA, 0);
	addSpecial("let", SF_LET, 0);
	addSpecial("letrec", SF_LETREC, 0);
	addSpecial("load", SF_LOAD, 0);
	addSpecial("or", SF_OR, 0);
	addSpecial("package", SF_PACKAGE, 0);
	addPrim("quit", P_QUIT);
	S_quote = addSpecial("quote", SF_QUOTE, 0);
	addPrim("read", P_READ);
	addPrim("recursive-bind", P_RECURSIVE_BIND);
	addSpecial("stats", SF_STATS, 0);
	addPrim("symbols", P_SYMBOLS);
	S_true = addSym("t", 0);
	addSym(":t", S_true);
	addSpecial("trace", SF_TRACE, 0);
	addPrim("verify-arrows", P_VERIFY_ARROWS);
	addPrim("write", P_WRITE);
	S_last = addSym("**", 0);
	Mstack = alloc(NIL, NIL);
	Primitives[P_ATOM] = &doAtom;
	Primitives[P_BOTTOM] = &doBottom;
	Primitives[P_CAR] = &doCar;
	Primitives[P_CDR] = &doCdr;
	Primitives[P_CONS] = &doCons;
	Primitives[P_DEFINED] = &doDefined;
	Primitives[P_EQ] = &doEq;
	Primitives[P_EXPLODE] = &doExplode;
	Primitives[P_GC] = &doGC;
	Primitives[P_IMPLODE] = &doImplode;
	Primitives[P_QUIT] = &doQuit;
	Primitives[P_READ] = &doRead;
	Primitives[P_RECURSIVE_BIND] = &doRecursiveBind;
	Primitives[P_SYMBOLS] = &doSymbols;
	Primitives[P_VERIFY_ARROWS] = &doVerifyArrows;
	Primitives[P_WRITE] = &doWrite;
	Specials[SF_AND] = &doAnd;
	Specials[SF_APPLY] = &doApply;
	Specials[SF_CLOSURE_FORM] = &doClosureForm;
	Specials[SF_COND] = &doCond;
	Specials[SF_DEFINE] = &doDefine;
	Specials[SF_DUMP_IMAGE] = &doDumpImage;
	Specials[SF_EVAL] = &doEval;
	Specials[SF_LAMBDA] = &doLambda;
	Specials[SF_LET] = &doLet;
	Specials[SF_LETREC] = &doLetrec;
	Specials[SF_LOAD] = &doLoad;
	Specials[SF_OR] = &doOr;
	Specials[SF_PACKAGE] = &doPackage;
	Specials[SF_QUOTE] = &doQuote;
	Specials[SF_STATS] = &doStats;
	Specials[SF_TRACE] = &doTrace;
	core = addSym("alisp", 0);
	Packages = alloc(core, Symbols);
	Packages = alloc(Packages, NIL);
	Symbols = addPackage(NIL);
}

/* Reset the reduction counter */
static void clearStats(void) {
	resetCounter(&Reductions);
	resetCounter(&Allocations);
	resetCounter(&Collections);
}

/* Internal Read-Eval-Loop for loading source files */
static void REL(void) {
	int	n, evl;

	ErrFlag = 0;
	evl = EvLev;
	EvLev = 0;
	while(!ErrFlag) {
		n = xread();
		if (n == EOT) break;
		n = eval(n);
	}
	EvLev = evl;
}

/*
 * Fix NIL nodes of a pool.
 */
static void fixnil(int *p, int oldnil, int newnil) {
	int	i;

	for (i=0; i<PoolSize; i++)
		if (p[i] == oldnil)
			p[i] = newnil;
}

/* Dump image */
int alisp_dump_image(char *p) {
	return dump_image(p);
}

/* Load initial image */
int alisp_load_image(char *p) {
	int	fd, n, i;
	char	buf[17];
	int	**v;
	int	bad = 0;
	int	inodes;

	fd = open(p, O_RDONLY);
	setmode(fd, O_BINARY);
	if (fd < 0) {
		error("cannot open image", NOEXPR);
		Error.arg = p;
		return -1;
	}
	memset(Tag, 0, PoolSize);
	read(fd, buf, 16);
	if (memcmp(buf, "ALISP__", 7)) {
		error("bad image (magic match failed)", NOEXPR);
		bad = 1;
	}
	if (buf[7] != sizeof(int)) {
		error("bad image (wrong cell size)", NOEXPR);
		bad = 1;
	}
	if (buf[8] != ALISP_MAJOR) {
		error("bad image (wrong version)", NOEXPR);
		bad = 1;
	}
	memcpy(&n, &buf[10], sizeof(int));
	if (n != 0x12345678) {
		error("bad image (wrong architecture)", NOEXPR);
		bad = 1;
	}
	read(fd, &inodes, sizeof(int));
	if (inodes > PoolSize) {
		error("bad image (too many nodes)", NOEXPR);
		bad = 1;
	}
	v = ImageVars;
	i = 0;
	while (v[i]) {
		read(fd, v[i], sizeof(int));
		i = i+1;
	}
	if (	!bad &&
		(read(fd, Car, inodes*sizeof(int)) != inodes*sizeof(int) ||
		 read(fd, Cdr, inodes*sizeof(int)) != inodes*sizeof(int) ||
		 read(fd, Tag, inodes) != inodes)
	) {
		error("bad image (bad file size)", NOEXPR);
		bad = 1;
	}
	if (inodes != PoolSize) {
		fixnil(Car, inodes, NIL);
		fixnil(Cdr, inodes, NIL);
	}
	close(fd);
	if (bad) Error.arg = p;
	return ErrFlag;
}

/*
 * Initialize the interpreter and allocate pools of
 * the given sizes.
 */
int alisp_init(int nodes, int trackGc) {
	PoolSize = nodes? nodes: ALISP_DFL_NODES;
	TrackGC = trackGc;
	if (PoolSize < ALISP_MIN_SIZE) return -1;
	if (	(Car = (int *) malloc(PoolSize * sizeof(int))) == NULL ||
		(Cdr = (int *) malloc(PoolSize * sizeof(int))) == NULL ||
		(Tag = (char *) malloc(PoolSize)) == NULL
	) {
		if (Car) free(Car);
		if (Cdr) free(Cdr);
		if (Tag) free(Tag);
		Car = Cdr = NULL;
		Tag = NULL;
		return -1;
	}
	memset(Tag, 0, PoolSize);
	init1();
	init2();
	return 0;
}

/* Shut down the interpreter */
void alisp_fini() {
	if (Car) free(Car);
	if (Cdr) free(Cdr);
	if (Tag) free(Tag);
	Car = Cdr = NULL;
	Tag = NULL;
}

/* Stop the interpreter */
void alisp_stop(void) {
	error("interrupted", NOEXPR);
}

/* Error condition */
int alisp_errflag(void) {
	return ErrFlag;
}

/* Reset error flag */
void alisp_reset(void) {
	ErrFlag = 0;
}

/* Return error context */
struct errorContext *alisp_errctx(void) {
	return &Error;
}

/* Print external representation of an expression */
void alisp_print(int n) {
	Quoted = 0;
	_print(n);
}

/* nl() wrapper */
void alisp_nl(void) {
	nl();
}

/* Read external form of an expression */
int alisp_read(void) {
	Level = 0;
	return xread();
}

/* printError() wrapper */
void alisp_print_error(void) {
	printError();
}

/*
 * Evaluate an expression. If evaluation fails,
 * revert to previous state.
 */
int alisp_eval(int n) {
	save(n);
	SafeSymbols = copyBindings();
	if (StatFlag) clearStats();
	n = eval(Car[Stack]);
	unsave(1);
	if (!ErrFlag) {
		Cdr[S_last] = n;
		if (Stack != NIL)
			fatal("eval(): unbalanced stack");
	}
	else {
		restoreBindings(SafeSymbols);
		Symbols = addPackage(NIL);
	}
	resetState();
	while (Car[Mstack] != NIL) munsave();
	return n;
}

/* Return conditions of use */
char **alisp_license() {
	static char	*license_text[] = {
"ArrowLISP -- An Interpreter for Purely Symbolic LISP",
"Copyright (C) 1998-2006 Nils M Holm.  All rights reserved.",
"",
"Redistribution and use in source and binary forms, with or without",
"modification, are permitted provided that the following conditions",
"are met:",
"1. Redistributions of source code must retain the above copyright",
"   notice, this list of conditions and the following disclaimer.",
"2. Redistributions in binary form must reproduce the above copyright",
"   notice, this list of conditions and the following disclaimer in the",
"   documentation and/or other materials provided with the distribution.",
"",
"THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND",
"ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE",
"IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE",
"ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE",
"FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL",
"DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS",
"OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)",
"HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT",
"LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY",
"OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF",
"SUCH DAMAGE.",
	NULL};
	return license_text;
}
