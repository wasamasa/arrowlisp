; ArrowLISP LISP syntax wrapper
; Copyright (C) 2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; This package implements a wrapper that transforms
; LISP expressions to ArrowLISP and vice versa:
;
; (lisp->alisp '(- 1 4/3)) => '(- '#1 '(/ #4 #3))
; (alisp->lisp '(- '#1 '(/ #4 #3))) => '(- 1 4/3)
;
; (lisp-eval '(- 1 4/3)) => '-1/3
;
; Note: Each number in a LISP expression is represented
; by an ArrowLISP symbol, so the symbol table gets filled
; with symbols representing numbers.

(load rmath)

(define lisp t)

(package lisp)

(define (lisp->alisp expr)
  (letrec

    ((numeric (lambda (x)
      (letrec
        ((digits (lambda (x slash)
          (cond ((null x) t)
            ((digit (car x))
              (digits (cdr x) slash))
            ((and (eq (car x) '/) slash)
	      (digits (cdr x) :F))
	    (t :F)))))
        (cond ((not (atom x)) :F)
	  ((null x) :F)
	  (t (let ((xx (explode x)))
	       (cond ((or (eq (car xx) '+) (eq (car xx) '+))
		   (cond ((null (cdr xx)) :F)
		     (t (digits (cdr x) t))))
	         (t (digits xx t)))))))))

    (expand-rational (lambda (x)
      (letrec
        ((den (lambda (x)
	  (cond ((eq (car x) '/)
	      (cond ((null (cdr x)) '#1)
	        (t (cdr x))))
            (t (den (cdr x))))))
        (num (lambda (x)
	  (reverse (den (reverse x))))))
        (list 'quote (list '/ (num x) (den x))))))

    (expand-number (lambda (x)
      (let ((xx (explode x)))
	(cond ((memq '/ xx)
	    (expand-rational xx))
	  (t (list 'quote xx))))))

    (expand-nums (lambda (x)
      (cond ((numeric x)
          (expand-number x))
        ((atom x) x)
        (t (cons (expand-nums (car x))
                 (expand-nums (cdr x))))))))

    (expand-nums expr)))

(define (alisp->lisp expr)
  (letrec

    ((condense-rational (lambda (x)
      (implode (append (numerator x)
	               '#/ (denominator x)))))

    (condense-number (lambda (x)
      (cond ((integer-p x) (implode x))
	(t (condense-rational x)))))

    (condense-nums (lambda (x first)
      (cond ((atom x) x)
	((and first (eq (car x) 'quote)
	            (not (atom (cdr x)))
		    (number-p (cadr x)))
          (condense-number (cadr x)))
	((and first (number-p x))
	  (condense-number x))
	(t (cons (condense-nums (car x) t)
		 (condense-nums (cdr x) :F)))))))

    (condense-nums expr t)))
  
(define (lisp-eval expr)
  (alisp->lisp (eval (lisp->alisp expr))))

(package)

