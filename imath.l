; ArrowLISP integer math functions
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; would use REQUIRE, but REQUIRE is in BASE
(cond ((defined 'base) :F)
  (t (load base)))

(require '=nmath)

(define imath t)

(package imath)

(define (integer a)
  (cond ((eq (car a) '+) (cdr a))
    ((eq (car a) '-) a)
    ((digit (car a)) a)
    (t (bottom (list 'integer a)))))

(define (integer-p a)
  (or (digit (car a))
      (eq (car a) '+)
      (eq (car a) '-)))

(define (i-normalize x)
  (cond ((eq (car x) '+)
      (n-normalize (cdr x)))
    ((eq (car x) '-)
      (let ((d (n-normalize (cdr x))))
        (cond ((equal d '(0)) d)
          (t (cons '- d)))))
    (t (n-normalize x))))

(define (i-zero x)
  (let ((a (i-abs x)))
    (n-zero a)))

(define (i-one x)
  (let ((a (i-abs x)))
    (and (n-one a) (neq (car x) '-))))

(define (i-negative x) (eq (car x) '-))

(define (i-abs x)
  (cond ((i-negative x) (cdr x))
    ((eq (car x) '+) (cdr x))
    (t x)))

(define (i-negate x)
  (cond ((n-zero (i-abs x)) x)
    ((eq (car x) '-) (cdr x))
    ((eq (car x) '+) (cons '- (cdr x)))
    (t (cons '- x))))

(define (i+ a b)
  (cond ((and (not (i-negative a))
              (not (i-negative b)))
      (n+ (i-abs a) (i-abs b)))
    ((and (not (i-negative a))
          (i-negative b))
      (cond ((n> (i-abs a) (i-abs b))
          (n- (natural a) (i-abs b)))
        (t (i-negate (n- (i-abs b) (natural a))))))
    ((and (i-negative a)
          (not (i-negative b)))
      (cond ((n> (i-abs a) (i-abs b))
          (i-negate (n- (i-abs a) (natural b))))
        (t (n- (natural b) (i-abs a)))))
    (t (i-negate (n+ (i-abs a) (i-abs b))))))

(define (i- a b)
  (cond ((i-negative b)
      (i+ a (i-abs b)))
    ((i-negative a)
      (i+ a (i-negate b)))
    ((n< (i-abs a) (i-abs b))
      (i-negate (n- (i-abs b) (i-abs a))))
    (t (n- (i-abs a) (i-abs b)))))

(define (i< a b)
  (cond ((i-negative a)
    (cond ((not (i-negative b)) t)
      (t (n< (i-abs b) (i-abs a)))))
  ((i-negative b) :F)
  (t (n< (i-abs a) (i-abs b)))))

(define (i> a b) (i< b a))

(define (i<= a b) (eq (i> b a) :F))

(define (i>= a b) (eq (i< b a) :F))

(define (i= a b)
  (equal (i-normalize a)
         (i-normalize b)))

(define (i* a b)
  (cond
    ((zero a) '#0)
    ((eq (i-negative a) (i-negative b))
      (n* (i-abs a) (i-abs b)))
    (t (i-negate (n* (i-abs a) (i-abs b))))))

(define (i-divide a b)
  (letrec

    ((sign (lambda (x)
      (cond ((eq (i-negative a) (i-negative b)) x)
        (t (cons '- x)))))

    (rsign (lambda (x)
      (cond ((i-negative a) (cons '- x))
        (t x))))

    (idiv (lambda (a b)
      (cond ((n-zero b) (bottom '(divide by zero)))
        ((n< (i-abs a) (i-abs b))
          (list '#0 (rsign (i-abs a))))
        (t (let ((q (n-divide (i-abs a) (i-abs b))))
             (list (sign (car q))
               (rsign (cadr q)))))))))

    (idiv (integer a) (integer b))))

(define (i-quotient a b) (car (divide a b)))

(define (i-remainder a b) (cadr (divide a b)))

(define (modulo a b)
  (let ((rem (remainder a b)))
    (cond ((eq (i-negative a) (i-negative b))
        rem)
      (t (i+ b rem)))))

(define (i-expt x y)
  (letrec
    ((_i-expt (lambda (x y)
      (cond ((or (not (i-negative x))
                 (even y))
              (n-expt (i-abs x) y))
        (t (i-negate (n-expt (i-abs x) y)))))))
    (_i-expt (integer x) (natural y))))

(define (i-max . a)
  (apply min/max (cons i> a)))

(define (i-min . a)
  (apply min/max (cons i< a)))

(define (i-sqrt x)
  (cond ((i-negative x)
      (bottom (list 'i-sqrt x)))
    (t (n-sqrt x))))

(define (i-gcd a b)
  (n-gcd (i-abs a) (i-abs b)))

(define (i-lcm a b)
  (n-lcm (i-abs a) (i-abs b)))

(package)

(require '=iter)

(define * (arith-iterator integer i* '#1))

(define + (arith-iterator integer i+ '#0))

(define (- . x)
  (cond ((null x)
      (bottom '(too few arguments to integer -)))
    ((eq (cdr x) ()) (i-negate (car x)))
    (t (reduce (lambda (a b)
                 (i- (integer a) (integer b)))
               x '#0))))

(define < (arith-pred-iterator integer i<))

(define <= (arith-pred-iterator integer i<=))

(define = (arith-pred-iterator integer i=))

(define > (arith-pred-iterator integer i>))

(define >= (arith-pred-iterator integer i>=))

(define abs i-abs)

(define divide i-divide)

(define expt i-expt)

(define gcd (arith-iterator integer i-gcd '#0))

(define lcm (arith-iterator integer i-lcm '#0))

(define (max . a) (apply min/max (cons i> a)))

(define (min . a) (apply min/max (cons i< a)))

(define negate i-negate)

(define negative i-negative)

(define one i-one)

(define quotient i-quotient)

(define remainder i-remainder)

(define sqrt i-sqrt)

(define zero i-zero)
