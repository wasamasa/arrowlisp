; MEXPRC -- M-Expression to S-Expression Compiler
; Copyright (C) 2003-2006 Nils M Holm. All rights reserved.
;
; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions
; are met:
; 1. Redistributions of source code must retain the above copyright
;    notice, this list of conditions and the following disclaimer.
; 2. Redistributions in binary form must reproduce the above copyright
;    notice, this list of conditions and the following disclaimer in the
;    documentation and/or other materials provided with the distribution.
;
; THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
; ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
; IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
; ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
; FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
; OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
; HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
; LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
; OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
; SUCH DAMAGE.

; The M-EXPR-COMPILE function accepts a list of symbols representing
; a LISP program in M-expression form and compiles it to an S-expression.
; The M-EXPR-EVAL function compiles and evaluates an M-expr.
;
; M-EXPR-COMPILE currently does not perform much error checking.
;
; The M-expr language accepted by the compiler is (presumably) a subset
; of the M-expr language used in the "LISP 1.5 Programmer's Manual".

; Limitations:
; { and } are used instead of ( and ) in literal lists
; [ and ] are used instead of ( and ) to group expressions
; : is used instead of ; in conditional operators
; , is used instead of ; to separate list elements
; % is used as a prefix for constants instead of using upper
;   case for constants and lower case for variables

; ---example---
; (mexpr-compile '(f[x] := [x=1 -> 1 : f[x-1]*x]))
; => (define (f x) (cond ((= x '#1) '#1) (t (f (* (- x '#1) x)))))

(define mexprc t)

(require '=imath)

(define symbol-class '#abcdefghijklmnopqrstuvwxyz_)

(define number-class '#0123456789)

(define (first-char x) (car (explode x)))

(define (symbol-p x) (memq x symbol-class))

(define (number-p x) (memq x number-class))

; LEXICAL ANALYSIS IS DONE BELOW.
;
; Input of this stage is a flat list of symbols representing an
; M-expr. Output is a list of individual tokens. For instance,
;
; (f[x] := x=0-> 1: f[x-1]*x)
; gives
; (f [ x ] := x = 0 -> 1 : f [ x - 1 ] * x)
;
; Symbols like F[X] are called 'fragments'. Each fragment
; may contain multiple tokens. F[X] contains F,[,X,].

; Extract a multi-character token from the head of a source fragment.
; ARGUMENTS:
; FRAGMENT  - Fragment to process
; PREDICATE - Predicate matching characters of the token
;             to extract
; VALUE:
; (TOKEN REST-OF-FRAGMENT)
;
(define (extract-class fragment predicate)
  (letrec
    ((input (explode fragment))
    (x-class (lambda (sym input)
      (cond ((null input)
          (list (reverse sym) input))
        ((predicate (car input))
          (x-class (cons (car input) sym)
                   (cdr input)))
        (t (list (reverse sym) input))))))
    (x-class () input)))

(define (extract-symbol fragment)
  (extract-class fragment symbol-p))

(define (extract-number fragment)
  (extract-class fragment number-p))

; Extract a single-character token from the head of a source fragment.
; VALUE:
; (TOKEN REST-OF-FRAGMENT)
;
(define (extract-char fragment)
  (let ((input (explode fragment)))
    (list (list (car input)) (cdr input))))

; Extract a single- or double-character token from the head of a
; source fragment. If the second character of the fragment is
; contained in the ALT-TAILS argument, a two-character token is
; extracted and else a single character is extracted.
; ARGUMENTS:
; FRAGMENT  - Fragment to process
; ALT-TAILS - List of possible second characters
; VALUE:
; (TOKEN REST-OF-FRAGMENT)
;
(define (extract-alternative fragment alt-tails)
  (let ((input (explode fragment)))
    (cond ((null (cdr input))
        (extract-char fragment))
      ((memq (cadr input) alt-tails)
        (list (list (car input) (cadr input))
              (cddr input)))
      (t (extract-char fragment)))))

; Recognize tokens and extract them from the head of a source fragment.
;
(define (extract-token fragment)
  (let ((first (first-char fragment)))
    (cond
      ((eq first '[)
        (extract-char fragment))
      ((eq first '])
        (extract-char fragment))
      ((eq first '{)
        (extract-char fragment))
      ((eq first '})
        (extract-char fragment))
      ((eq first ',)
        (extract-char fragment))
      ((eq first '%)
        (extract-char fragment))
      ((eq first ':)
        (extract-alternative fragment '#=))
      ((eq first '+)
        (extract-char fragment))
      ((eq first '-)
        (extract-alternative fragment '#>))
      ((eq first '*)
        (extract-char fragment))
      ((eq first '=)
        (extract-char fragment))
      ((eq first '<)
        (extract-alternative fragment '#>=))
      ((eq first '>)
        (extract-alternative fragment '#=))
      ((eq first '/)
        (extract-alternative fragment '#\))
      ((eq first '\)
        (extract-alternative fragment '#/))
      ((eq first '^)
        (extract-char fragment))
      ((symbol-p first)
        (extract-symbol fragment))
      ((number-p first)
        (extract-number fragment))
      (t (bottom 'syntax 'error 'at fragment)))))

(define frag car)       ; fragment of input
(define rest cdr)       ; rest of input
(define restfrag cadr)  ; fragment of rest of input
(define restrest cddr)  ; rest of rest of input

; Extract the first token of the first fragment of a token list.
; If the first fragment is empty (NIL), move to the next
; fragment.
; ARGUMENTS:
; SOURCE - list of tokens
; VALUE:
; (EXTRACTED-TOKEN TOKEN-LIST)
;
(define (next-token source)
  (cond ((null (frag source))
      (cond ((null (rest source)) ())
        (t (let ((head (extract-token (restfrag source))))
             (cons (frag head)
                   (cons (implode (restfrag head))
                         (restrest source)))))))
    (t (let ((head (extract-token (frag source))))
         (cons (frag head)
               (cons (implode (restfrag head))
                     (rest source)))))))

; Lexer. Convert an M-expr to a token list.
;
(define (tokenize source)
  (letrec
    ((tok (lambda (src tlist)
      (let ((new-state (next-token src)))
        (cond ((null new-state) (reverse tlist))
          (t (tok (cdr new-state)
                  (cons (implode (car new-state))
                        tlist))))))))
    (tok source ())))

; SYNTAX ANALYSIS IS DONE BELOW.
;
; Input of this stage is a token list as generated during lexical
; analysis. Output is an S-expr that can be reduced using ArrowLISP.
; For instance,
;
; (F [ x ] : = X ^ 2)  -->  (DEFINE (F X) (EXPT X '#2))
;
; Most function of the syntax analysis phase of the compiler return
; partially translated PROGRAMs of the form
;
; (S-EXPR TOKEN-LIST)
;
; where S-EXPR is the S-expr generated from a part of the input program
; and TOKEN-LIST is a token list containing the rest (the not yet
; translated part) of the program. Most parser function expect input
; in the same form. For instance,
;
; (PARSE-TERM '(() #A*B+C))  =>  '((* A B) '#+C)
;
; While parsing a program, the S-EXPR part of a PROGRAM structure
; grows and the TOKEN-LIST part shrinks.

; Compose a PROGRAM structure.
(define (make-prog sexpr tlist) (list sexpr tlist))

; Functions used to decompose PROGRAM structures.
(define s-expr-of car)    ; S-expression built so far

(define rest-of cadr)     ; Not yet translated rest of program

; End of input program?
(define (end-of p) (null (rest-of p)))

; First token of rest of program.
(define (first-of-rest p)
  (cond ((end-of p) ())
    (t (caadr p))))

; Rest of rest of program (all but first token of rest).
(define (rest-of-rest p)
  (cond ((end-of p) ())
    (t (cdadr p))))

; Look ahead at second token in input stream.
(define (look-ahead p)
  (cond ((end-of p) ())
    ((null (rest-of-rest p)) ())
    (t (car (rest-of-rest p)))))

; Rest^3 of program (all but first two token of rest).
(define (rest-of-look-ahead p)
  (cond ((end-of p) ())
    ((null (rest-of-rest p)) ())
    (t (cdr (rest-of-rest p)))))

; Turn an expression into a quoted expression:
; X  -->  (QUOTE X)
(define (quoted x) (list 'quote x))

; Parse a list structure, turning it into a list:
; {a,b,c}  -->  (A B C)
; Input lists may contain atoms and lists.
;
(define (parse-list tlist)
  (letrec
    ((plist (lambda (tls skip lst top)
      ; tls  = input
      ; skip = skip next token (commas)
      ; lst  = output
      ; top  = processing top level list
      (cond ((eq (car tls) '})
          (cond (top (make-prog (quoted (reverse lst))
                                (cdr tls)))
            (t (make-prog (reverse lst)
                          (cdr tls)))))
        ((eq (car tls) '{)
          (let ((sublist (plist (cdr tls) :f () :f)))
            (plist (rest-of sublist) t
                   (cons (car sublist) lst) top)))
        (skip
          (cond ((eq (car tls) ',)
              (plist (cdr tls) :f lst top))
            (t (bottom ', 'expected 'at tls))))
        (t (plist (cdr tls) t
                  (cons (car tls) lst) top))))))
  (plist tlist :f () t)))

; Parse the actual argument list of a function, returning a list:
; [a+b,c*d]  -->  ((+ a b) (* c d))
; An actual argument list is a list of expressions.
;
(define (parse-actual-args  tlist)
  (letrec
    ((pargs (lambda (tls skip lst)
      (cond ((eq (car tls) '])
          (make-prog (reverse lst) (cdr tls)))
        (skip
          (cond ((eq (car tls) ',)
              (pargs (cdr tls) :f lst))
            (t (bottom ', 'expected 'at tls))))
        (t (let ((expr (parse-expr tls)))
             (pargs (rest-of expr) t
                    (cons (car expr) lst))))))))
    (pargs tlist :f ())))

; Parse the formal argument list of a function, returning a list:
; [a,b,c]  -->  (A B C)
; A formal argument list is a flat list of symbols.
;
(define (parse-formal-args  tlist)
  (letrec
    ((pargs (lambda (tls skip lst)
      (cond ((eq (car tls) '])
          (make-prog (reverse lst) (cdr tls)))
        (skip
          (cond ((eq (car tls) ',)
              (pargs (cdr tls) :f lst))
            (t (bottom ', 'expected 'at tls))))
        ((symbol-p (first-char (car tls)))
          (pargs (cdr tls) t (cons (car tls) lst)))
        (t (bottom 'symbol 'expected 'at tls))))))
    (pargs tlist :f ())))

; Parse a function call:
; f[a,b,c]  -->  (F A B C)
;
(define (parse-fun-call program)
  (let ((function (first-of-rest program))
        (args (parse-actual-args
                (rest-of-look-ahead program))))
    (make-prog (append (list function)
                       (s-expr-of args))
               (rest-of args))))

; Parse a parenthesized sub-expression:
; [expr]  -->  EXPR
;
(define (parse-parens program)
  (let ((expr (parse-expr (rest-of-rest program))))
    (cond ((neq (first-of-rest expr) '])
        (bottom '] 'expected 'at (rest-of expr)))
      (t (make-prog (s-expr-of expr)
                    (rest-of-rest expr))))))

; Parse the argument list of a lambda expression.
;
(define (parse-lambda-args program)
  (cond ((eq (first-of-rest program) '[)
      (parse-formal-args (rest-of-rest program)))
    (t (bottom 'argument 'list 'expected 'in 'lambda[]))))

; Compose a lambda expresssion.
; ARGS TERM --> (LAMBDA ARGS TERM)
;
(define (make-lambda args term)
  (list 'lambda args term))

; Parse an application of a lambda function:
; lambda[[f-args] term][a-args] --> ((LAMBDA (F-ARGS) TERM) A-ARGS)
;
(define (parse-lambda-app program)
  (let ((args (parse-actual-args
                (rest-of-rest program))))
    (make-prog (append (list (s-expr-of program))
                       (s-expr-of args))
               (rest-of args))))

; Parse a lambda expression.
; [lambda[f-args] term] --> (LAMBDA (F-ARGS) TERM)
;
(define (parse-lambda program)
  (cond ((neq (look-ahead program) '[)
      (bottom '[ 'expected 'after 'lambda))
    (t (let ((args (parse-lambda-args
                     (make-prog ()
                       (rest-of-look-ahead program)))))
      (let ((term (parse-expr (rest-of args))))
        (cond ((neq (first-of-rest term) '])
            (bottom 'missing 'closing '] 'in 'lambda[]))
          (t (make-prog
               (make-lambda (s-expr-of args)
                            (s-expr-of term))
               (rest-of-rest term)))))))))

; Create a case of a conditional expression.
;
(define (make-case pred expr) (list pred expr))

; Parse the cases of a conditional expression.
; VALUE:
; (list-of-cases rest-of-program)
; where the list of cases is suitable for building
; a COND expression.
;
(define (parse-cases program)
  (letrec
    ((pcases (lambda (cases prog)
      (let ((pred (parse-disj (make-prog () prog))))
        (cond ((neq (first-of-rest pred) '->)
            (make-prog (cons (make-case 't (s-expr-of pred))
                             cases)
                       (rest-of pred)))
          (t (let ((expr (parse-expr (rest-of-rest pred))))
               (cond ((eq (first-of-rest expr) ':)
                   (pcases (cons (make-case (s-expr-of pred)
                                            (s-expr-of expr))
                                 cases)
                           (rest-of-rest expr)))
                 (t (bottom ': 'expected 'in 'conditional 'before
                      (rest-of expr)))))))))))
    (let ((case-list (pcases () (rest-of program))))
      (make-prog (reverse (s-expr-of case-list))
                 (rest-of case-list)))))

; Create a (conditional) expression from a list
; of cases. If only one case is supplied, create
; an unconditional expression.
;
(define (make-cond-expr cases)
  (cond ((null (cdr cases))
      (cadar cases))
    (t (cons 'cond cases))))

; Parse a conditional expression:
; [P1-> X1: P2-> X2: ... : XN ]
; --> (COND (P1 X1) (P2 X2) ... (T XN))
;
(define (parse-cond-expr program)
  (cond ((neq (first-of-rest program) '[)
      (parse-disj program))
    (t (let ((cond-expr
              (parse-cases
                (make-prog () (rest-of-rest program)))))
         (cond ((neq (first-of-rest cond-expr) '])
             (bottom '] 'expected 'at 'end 'of
               'conditional 'expression))
           (t (make-prog
                (make-cond-expr (s-expr-of cond-expr))
                (rest-of-rest cond-expr))))))))

; Parse a factor of an M-expr.
;
(define (parse-factor program)
  (let ((first (first-char (first-of-rest program))))
    (cond ((null first)
        (bottom 'unexpected 'eof))

      ; NIL --> ()
      ((eq (first-of-rest program) 'nil)
        (make-prog () (rest-of-rest program)))

      ; TRUE --> T
      ((eq (first-of-rest program) 'true)
        (make-prog t (rest-of-rest program)))

      ; FALSE --> :F
      ((eq (first-of-rest program) 'false)
        (make-prog :F (rest-of-rest program)))

      ; LAMBDA[[X] T] --> (LAMBDA (X) T)
      ; LAMBDA[[X] T][Y] --> ((LAMBDA (X) T) Y)
      ((eq (first-of-rest program) 'lambda)
        (let ((lambda-term (parse-lambda program)))
          (cond ((eq (first-of-rest lambda-term) '[)
              (parse-lambda-app lambda-term))
            (t lambda-term))))

      ; SYMBOL --> SYMBOL
      ; SYMBOL [ ARGS ] --> (SYMBOL ARGS)
      ((symbol-p first)
        (cond ((eq (look-ahead program) '[)
            (parse-fun-call program))
          (t (make-prog (first-of-rest program)
            (rest-of-rest program)))))

      ; NUMBER --> '#NUMBER
      ((number-p first)
        (make-prog (quoted
                     (explode
                       (first-of-rest program)))
          (rest-of-rest program)))

      ; { ELEMENTS, ... } --> ( ELEMENTS ... )
      ((eq first '{)
        (parse-list (rest-of-rest program)))

      ; %FACTOR --> (QUOTE FACTOR)
      ((eq first '%)
        (let ((rhs (parse-factor
                     (make-prog ()
                       (rest-of-rest program)))))
          (make-prog (quoted (s-expr-of rhs))
                     (rest-of rhs))))

      ; [ EXPR ] --> EXPR
      ((eq first '[)
        (parse-cond-expr program))

      ; -FACTOR --> (- FACTOR)
      ((eq first '-)
        (let ((rhs (parse-factor
                     (make-prog ()
                       (rest-of-rest program)))))
          (make-prog (list '- (s-expr-of rhs))
            (rest-of rhs))))

      (t (bottom 'syntax 'error 'at (rest-of program))))))

; Parse a binary expression:
; X OP Y OP ... Z  -->  (FUNCTION (... (FUNCTION X Y) ...) Z)
; ARGUMENTS:
; PROGRAM       - Program to process
; OPS           - Association list of ops and functions
; PARENT-PARSER - Parser used to parse higher-precedence
;                 operations
;
; This is a generalization of the functions implementing the stages
; of recursive descent parsing.
; 
(define (parse-binary program ops parent-parser)
  (letrec
    ((lhs (parent-parser program))
    (collect (lambda (expr tlist)
      (let ((op (cond ((null tlist) :f)
                  (t (assoc (car tlist) ops)))))
        (cond ((null tlist)
            (make-prog expr ()))
          (op
            (let ((next (parent-parser
                          (make-prog ()
                            (cdr tlist)))))
              (collect (list (cdr op) expr (s-expr-of next))
                (rest-of next))))
          (t (make-prog expr tlist)))))))
      (collect (car lhs) (rest-of lhs))))

; Parse powers:
; X^Y  -->  (EXPT X Y)
;
(define (parse-power program)
  (parse-binary program
                '((^ . expt))
                parse-factor))

; Parse terms:
; X*Y  --> (* X Y)
; X/Y  --> (QUOTIENT X Y)
;
(define (parse-term program)
  (parse-binary program
                '((* . *) (/ . quotient))
                parse-power))

; Parse sums:
; X+Y  --> (+ X Y)
; X-Y  --> (- X Y)
;
(define (parse-sum program)
  (parse-binary program
                '((+ . +) (- . -))
                parse-term))

; Parse predicates:
; X=Y   --> (= X Y)
; X<>Y  --> ((LAMBDA (X Y) (NOT (= X Y))) X Y)
; X<Y   --> (< X Y)
; X>Y   --> (> X Y)
; X<=Y  --> (<= X Y)
; X>=Y  --> (>= X Y)
;
(define (parse-pred program)
  (parse-binary program
                '((= . =)
                  (<> . (lambda (x y) (not (= x y))))
                  (< . <)
                  (> . >)
                  (<= . <=)
                  (>= . >=))
                 parse-sum))

; Parse logical conjunctions:
; X/\Y  --> (AND X Y)
;
(define (parse-conj program)
  (parse-binary program
                '((/\ . and))
                parse-pred))

; Parse logical disjunctions:
; X\/Y  --> (OR X Y)
;
(define (parse-disj program)
  (parse-binary program
                '((\/ . or))
                parse-conj))

; Parse a token list representing an M-expr,
; returning a program of the form:
;
; (S-EXPR (REST OF TOKEN LIST))
;
(define (parse-expr tlist)
  (parse-disj (make-prog () tlist)))

; Accept a definition of the form
; F[ARGS] := EXPR
;
; Return a partial environment of the form
; (F (LAMBDA (ARGS) EXPR)) 
; in the CAR of the resulting PROGRAM.
;
(define (force-definition program)
  (let ((head (parse-expr (rest-of program))))
    (cond ((eq (first-of-rest head) ':=)
        (let ((term (parse-expr (rest-of-rest head))))
          (make-prog
            (list (car (s-expr-of head))
                  (list 'lambda ;XXX make-lambda
                         (cdr (s-expr-of head))
                         (s-expr-of term)))
            (rest-of term))))
      (t (bottom ':= 'expected 'at (rest-of program))))))

; Parse the WHERE clause of a compound definition:
; WHERE F[ARGS] := EXPR AND G[ARGS] := EXPR ...
; Return an environment for LABEL in the CAR of
; the resulting PROGRAM:
; ( (F (LAMBDA (ARGS) EXPR))
;   (G (LAMBDA (ARGS) EXPR)) )
;
(define (parse-compound program)
  (letrec
    ((compound (lambda (prog def-list)
      (let ((defn (force-definition (make-prog () prog))))
        (cond ((eq (first-of-rest defn) 'and)
            (compound (rest-of-rest defn)
                      (cons (s-expr-of defn) def-list)))
          (t (make-prog (reverse (cons (s-expr-of defn) def-list))
                        (rest-of defn))))))))
    (compound program ())))

; Create a LETREC out of an environment and a term.
; 
(define (make-letrec env term)
  (list 'letrec env term))

; Parse definitions of the forms
; F[ARGS] := EXPR
; and
; F[ARGS] := EXPR WHERE G[ARGS] := EXPR AND ...
;
; Upon entry, PRGORAM holds ((F ARGS) (:= EXPR))
; This function merely composes an application of
; DEFINE and returns it.
;
(define (parse-definition program)
  (let ((term (parse-expr (rest-of-rest program))))
    (cond ((eq (first-of-rest term) 'where)
        (let ((compound (parse-compound (rest-of-rest term))))
          (make-prog
            (list 'define
                   (s-expr-of program)
                   (make-letrec (s-expr-of compound)
                                (s-expr-of term)))
            (rest-of compound))))
      (t (make-prog
           (list 'define
             (s-expr-of program)
             (s-expr-of term))
           (rest-of term))))))

; Parse an M-expr (including definitions), returning
; an equivalent S-expr.
; The M-expr is represented by a list of tokens as
; returned by TOKENIZE.
;
(define (parse-program tlist)
  (let ((program (parse-expr tlist)))
  (cond ((eq (first-of-rest program) ':=)
      (parse-definition program))
    (t program))))

; Compile an M-expr to an S-expr.
;
(define (mexpr-compile source)
  (let ((program (parse-program
                   (tokenize source))))
    (cond
      ((end-of program)
        (car program))
      (t (bottom 'syntax 'error 'at
           (rest-of program))))))

; Compile and evaluate an M-expr.
;
(define (mexpr-eval source)
  (eval (mexpr-compile source)))
