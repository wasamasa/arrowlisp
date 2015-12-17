; ArrowLISP rational math functions
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; would use REQUIRE, but REQUIRE is in BASE
(cond ((defined 'base) :F)
  (t (load base)))

(require '=imath)

(define rmath t)

(package rmath)

(define (rational x)
  (cond ((eq (car x) '/) x)
    (t (list '/ x '#1))))

(define (rational-p x) (eq (car x) '/))

(define (numerator x) (cadr x))

(define (denominator x) (caddr x))

(define (r-zero x)
  (cond ((rational-p x) (r= x '#0))
    (t (i-zero x))))

(define (r-one x)
  (cond ((rational-p x) (r= x '#1))
    (t (i-one x))))

(define (least-terms x)
  (let ((cd (gcd (numerator x) (denominator x))))
    (cond ((r-one cd) x)
      (t (list '/
	   (quotient (numerator x) cd)
	   (quotient (denominator x) cd))))))

(define (decay x)
  (cond ((r-one (denominator x)) (numerator x))
    (t x)))

(define (r-normalize x)
  (letrec ((norm-sign (lambda (x)
      (let ((num (numerator x))
	    (den (denominator x)))
        (let ((pos (eq (i-negative num)
		       (i-negative den))))
        (list '/
	      (cond (pos (i-abs num))
		(t (cons '- (i-abs num))))
              (i-abs den)))))))
  (cond ((rational-p x)
      (decay (least-terms (norm-sign x))))
    (t (i-normalize x)))))

(define (integer x)
  (let ((xlt (+ '#0 x)))
    (cond ((rational-p xlt)
	(bottom (list 'integer x)))
      (t xlt))))

(define (r-abs x)
  (cond ((rational-p x)
      (list '/ (i-abs (numerator x))
	       (i-abs (denominator x))))
    (t (i-abs x))))

(define (equalize a b)
  (let ((num-a (numerator a))
        (num-b (numerator b))
        (den-a (denominator a))
        (den-b (denominator b)))
    (let ((cd (gcd den-a den-b)))
      (cond ((r-one cd)
          (list
            (list '/
                  (i* num-a den-b)
                  (i* den-a den-b))
            (list '/
              (i* num-b den-a)
              (i* den-b den-a))))
        (t (list
             (list '/
               (quotient (i* num-a den-b) cd)
               (quotient (i* den-a den-b) cd))
             (list '/
               (quotient (i* num-b den-a) cd)
               (quotient (i* den-b den-a) cd))))))))

(define (r+ a b)
  (let ((factors (equalize (rational a)
                           (rational b)))
    (radd (lambda (a b)
      (r-normalize
        (list '/
          (i+ (numerator a) (numerator b))
          (denominator a))))))
    (radd (car factors) (cadr factors))))

(define (r- a b)
  (let ((factors (equalize (rational a)
                           (rational b)))
    (rsub (lambda (a b)
      (r-normalize
        (list '/
          (i- (numerator a) (numerator b))
          (denominator a))))))
    (rsub (car factors) (cadr factors))))

(define (r* a b)
  (letrec
    ((rmul (lambda (a b)
      (r-normalize
        (list '/
          (i* (numerator a) (numerator b))
          (i* (denominator a) (denominator b)))))))
    (rmul (rational a) (rational b))))

(define (r/ a b)
  (letrec
    ((rdiv (lambda (a b)
      (r-normalize
        (list '/
          (i* (numerator a) (denominator b))
          (i* (denominator a) (numerator b)))))))
    (cond ((r-zero b) (bottom (list 'r/ a b)))
      (t (rdiv (rational a) (rational b))))))

(define (r< a b)
  (let ((factors (equalize (rational a)
                 (rational b))))
    (i< (numerator (car factors))
        (numerator (cadr factors)))))

(define (r> a b) (r< b a))

(define (r<= a b) (eq (r> a b) :F))

(define (r>= a b) (eq (r< a b) :F))

(define (r= a b)
  (cond ((or (rational-p a) (rational-p b))
      (equal (least-terms (rational a))
	     (least-terms (rational b))))
    (t (i= a b))))

(define (r-expt x y)
  (let ((xr (cond ((i-negative (integer y))
                (r/ '#1 (rational x)))
              (t (rational x)))))
    (letrec 
      ((square (lambda (x) (r* x x)))
      (exp (lambda (x y)
        (cond ((r-zero y) '#1)
          ((even y)
            (square (exp x (quotient y '#2))))
          (t (r* x (square (exp x (quotient y '#2)))))))))
      (exp xr (i-abs (integer y))))))

(define (r-negative x)
  (cond ((rational-p x)
      (i-negative (numerator (r-normalize x))))
    (t (i-negative x))))

(define (r-negate x)
  (cond ((rational-p x)
      (let ((nx (r-normalize x)))
	(list '/ (i-negate (numerator nx))
		 (denominator nx))))
    (t (i-negate x))))

(define (r-max . a)
  (apply min/max (cons r> a)))

(define (r-min . a)
  (apply min/max (cons r< a)))

(define (r-sqrt square precision)
  (let ((epsilon (list '/ '#1
                   (r-expt '#10 (natural precision)))))
    (letrec
      ((sqr (lambda (x)
        (cond ((r< (r-abs (r- (r* x x) square))
                   epsilon)
            x)
          (t (sqr (r/ (r+ x (r/ square x))
                      '#2)))))))
      (sqr (nsqrt (natural square))))))

(package)

(require '=iter)

(define * (arith-iterator rational r* '#1))

(define + (arith-iterator rational r+ '#0))

(define (- . x)
  (cond ((null x)
      (bottom '(too few arguments to rational -)))
    ((eq (cdr x) ()) (r-negate (car x)))
    (t (reduce (lambda (a b)
                 (r- (rational a) (rational b)))
               x '#0))))

(define / (arith-iterator rational r/ '#1))

(define < (arith-pred-iterator rational r<))

(define <= (arith-pred-iterator rational r<=))

(define = (arith-pred-iterator rational r=))

(define > (arith-pred-iterator rational r>))

(define >= (arith-pred-iterator rational r>=))

(define abs r-abs)

(define *epsilon* '#10)

(define expt r-expt)

(define (max . a) (apply min/max (cons r> a)))

(define (min . a) (apply min/max (cons r< a)))

(define negate r-negate)

(define negative r-negative)

(define one r-one)

(define (sqrt x) (r-sqrt x *epsilon*))

(define zero r-zero)
