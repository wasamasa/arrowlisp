; ArrowLISP natural math functions
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; would use REQUIRE, but REQUIRE is in BASE
(cond ((defined 'base) :F)
  (t (load base)))

(define nmath t)

(export '+ '- '/)

(package nmath)

(define 0 '0)
(define 1 '1)
(define 2 '2)
(define 3 '3)
(define 4 '4)
(define 5 '5)
(define 6 '6)
(define 7 '7)
(define 8 '8)
(define 9 '9)

(define *digits* '#0123456789)

(define (digit x) (neq (memq x *digits*) :F))

(define (succ x)
  (cond ((eq x 0) 1)
        ((eq x 1) 2)
        ((eq x 2) 3)
        ((eq x 3) 4)
        ((eq x 4) 5)
        ((eq x 5) 6)
        ((eq x 6) 7)
        ((eq x 7) 8)
        ((eq x 8) 9)
        ((eq x 9) :F)
        (t (bottom '(not a digit:) x))))

(define (pred x)
  (cond ((eq x 1) 0)
        ((eq x 2) 1)
        ((eq x 3) 2)
        ((eq x 4) 3)
        ((eq x 5) 4)
        ((eq x 6) 5)
        ((eq x 7) 6)
        ((eq x 8) 7)
        ((eq x 9) 8)
        ((eq x 0) :F)
        (t (bottom '(not a digit:) x))))

(define sums-of-digits '(
  ((0.0) (1.0) (2.0) (3.0) (4.0) (5.0) (6.0) (7.0) (8.0) (9.0) (0.1))
  ((1.0) (2.0) (3.0) (4.0) (5.0) (6.0) (7.0) (8.0) (9.0) (0.1) (1.1))
  ((2.0) (3.0) (4.0) (5.0) (6.0) (7.0) (8.0) (9.0) (0.1) (1.1) (2.1))
  ((3.0) (4.0) (5.0) (6.0) (7.0) (8.0) (9.0) (0.1) (1.1) (2.1) (3.1))
  ((4.0) (5.0) (6.0) (7.0) (8.0) (9.0) (0.1) (1.1) (2.1) (3.1) (4.1))
  ((5.0) (6.0) (7.0) (8.0) (9.0) (0.1) (1.1) (2.1) (3.1) (4.1) (5.1))
  ((6.0) (7.0) (8.0) (9.0) (0.1) (1.1) (2.1) (3.1) (4.1) (5.1) (6.1))
  ((7.0) (8.0) (9.0) (0.1) (1.1) (2.1) (3.1) (4.1) (5.1) (6.1) (7.1))
  ((8.0) (9.0) (0.1) (1.1) (2.1) (3.1) (4.1) (5.1) (6.1) (7.1) (8.1))
  ((9.0) (0.1) (1.1) (2.1) (3.1) (4.1) (5.1) (6.1) (7.1) (8.1) (9.1))
))

(define diffs-of-digits '(
  ((0.0) (9.1) (8.1) (7.1) (6.1) (5.1) (4.1) (3.1) (2.1) (1.1) (0.1))
  ((1.0) (0.0) (9.1) (8.1) (7.1) (6.1) (5.1) (4.1) (3.1) (2.1) (1.1))
  ((2.0) (1.0) (0.0) (9.1) (8.1) (7.1) (6.1) (5.1) (4.1) (3.1) (2.1))
  ((3.0) (2.0) (1.0) (0.0) (9.1) (8.1) (7.1) (6.1) (5.1) (4.1) (3.1))
  ((4.0) (3.0) (2.0) (1.0) (0.0) (9.1) (8.1) (7.1) (6.1) (5.1) (4.1))
  ((5.0) (4.0) (3.0) (2.0) (1.0) (0.0) (9.1) (8.1) (7.1) (6.1) (5.1))
  ((6.0) (5.0) (4.0) (3.0) (2.0) (1.0) (0.0) (9.1) (8.1) (7.1) (6.1))
  ((7.0) (6.0) (5.0) (4.0) (3.0) (2.0) (1.0) (0.0) (9.1) (8.1) (7.1))
  ((8.0) (7.0) (6.0) (5.0) (4.0) (3.0) (2.0) (1.0) (0.0) (9.1) (8.1))
  ((9.0) (8.0) (7.0) (6.0) (5.0) (4.0) (3.0) (2.0) (1.0) (0.0) (9.1))
))

(define (nth-digit x table)
  (cond ((eq x 0) (car table))
    (t (nth-digit (pred x) (cdr table)))))

(define (d+ a b carry)
  (let ((row (nth-digit b sums-of-digits)))
    (cond ((eq carry 1) (nth-digit a (cdr row)))
      (t (nth-digit a row)))))

(define (d- a b carry)
  (let ((row (nth-digit a diffs-of-digits)))
    (cond ((eq carry 1) (nth-digit b (cdr row)))
      (t (nth-digit b row)))))

(define (d< a b)
  (letrec ((dless (lambda (set)
      (cond ((null set) (bottom '(not digits:) a b))
         ((eq a (car set))
          (not (eq b (car set))))
        ((eq b (car set)) :F)
        (t (dless (cdr set)))))))
    (dless *digits*)))

(define (number-p x)
  (letrec ((lod-p (lambda (x)
      (cond ((null x) t)
        ((atom x) :f)
	(t (and (digit (car x))
	        (lod-p (cdr x)))))))
    (digits-p (lambda (x)
      (and (not (atom x))
	   (lod-p x)))))
    (cond ((atom x) :F)
      ((or (eq (car x) '-)
               (eq (car x) '+))
        (digits-p (cdr x)))
      ((eq (car x) '/)
        (and (not (atom (cdr x)))
             (number-p (cadr x))
             (not (atom (cddr x)))
             (number-p (caddr x))))
      (t (digits-p x)))))

(define (n-normalize x)
  (cond ((null (cdr x)) x)
    ((eq (car x) 0)
      (n-normalize (cdr x)))
    (t x)))

(define (natural x)
  (cond ((eq (car x) '+) (cdr x))
    ((eq (car x) '-)
      (bottom (list 'natural x)))
    ((digit (car x)) x)
    (t (bottom (list 'natural x)))))

(define (natural-p x) (digit (car x)))

(define (n< a b)
  (letrec
    ((d> (lambda (a b)
      (d< b a)))

    (lt (lambda (a b r)
      (cond ((and (null a) (null b)) r)
        ((null a) t)
        ((null b) :F)
        (t (lt (cdr a) (cdr b)
             (cond ((d< (car a) (car b)) t)
               ((d> (car a) (car b)) :F)
               (t r))))))))

    (lt (reverse a) (reverse b) :F)))

(define (n> a b) (n< b a))

(define (n<= a b) (eq (n> a b) :F))

(define (n>= a b) (eq (n< a b) :F))

(define (n= a b)
  (equal (n-normalize a)
	 (n-normalize b)))

(define (min/max op a . b)
  (letrec
    ((_max (lambda (a)
      (cond ((null (cdr a)) (car a))
        ((op (car a) (cadr a))
          (_max (cons (car a) (cddr a))))
        (t (_max (cdr a)))))))
    (cond ((null b) a)
      (t (_max (cons a b))))))

(define (n+ a b)
  (letrec

    ((add (lambda (a b c r)
      (cond ((null a)
          (cond
            ((null b)
              (cond
                ((eq c 0) r)  ; no carry
                (t (cons 1 r))))
            (t (let ((sum (d+ 0 (car b) c)))
                  (add () (cdr b) (cdr sum)
                    (cons (car sum) r))))))
        ((null b)
          (let ((sum (d+ (car a) 0 c)))
            (add (cdr a) () (cdr sum)
              (cons (car sum) r))))
        (t (let ((sum (d+ (car a) (car b) c)))
            (add (cdr a) (cdr b) (cdr sum)
              (cons (car sum) r))))))))

    (add (reverse a) (reverse b) 0 ())))

(define (n- a b)
  (letrec

    ((diff (lambda (a b c r)
      (cond ((null a)
          (cond
            ((null b)
              (cond
                ((eq c 0) r)
                (t (bottom '(negative difference)))))
            (t (bottom '(negative difference)))))
      ((null b)
        (cond
          ((eq c 0)
            (append (reverse a) r))
          (t (diff a '(1) 0 r))))
      (t (let ((delta (d- (car a) (car b) c)))
           (diff (cdr a) (cdr b) (cdr delta)
             (cons (car delta) r))))))))

    (n-normalize
      (diff (reverse a) (reverse b) 0 ()))))

(define (n-zero x)
  (and (eq (car x) 0)
       (null (cdr x))))

(define (n-one x)
  (and (eq (car x) 1)
       (null (cdr x))))

(define (n* a b)
  (letrec

    ((x10 (lambda (x)
        (append x '#0)))

    (addn (lambda (a b r)
      (cond ((n-zero b) r)
        (t (addn a (n- b '#1) (n+ a r))))))

    (tms (lambda (a b r)
      (cond ((null b) r)
        (t (tms (x10 a) (cdr b)
             (addn a (list (car b)) r)))))))

    ; avoid leading zeroes in result
    (cond ((n-zero a) '#0)
      (t (tms a (reverse b) '#0)))))

(define (n-divide a b)
  (letrec

    ; Equalize the divisor by shifting it to the left
    ; (multiplying it by 10) until it has the same number
    ; of digits as the dividend.
    ; Return: (new divisor . base 1 shift count)
    ((eql (lambda (a b r)
      (cond
        ((null a)
          (cons (reverse (car r)) (cdr r)))
        ((null b)
          (eql (cdr a) ()
            (cons (cons 0 (car r))
                  (cons 'i (cdr r)))))
        (t (eql (cdr a) (cdr b)
              (cons (cons (car b) (car r))
                    (cdr r)))))))

    ; Divide with quotient < 10
    ; Return (A/B*B . A/B)
    (div10 (lambda (a b r)
      (cond ((n< (car r) a)
          (div10 a b
            (cons (n+ (car r) b)
              (n+ (cdr r) '#1))))
        ((equal (car r) a) r)
        (t (cons (n- (car r) b)
             (n- (cdr r) '#1))))))

    ; X / 10
    (d10 (lambda (x)
      (reverse (cdr (reverse x)))))

    (x10 (lambda (x) (append x '#0)))

    (div (lambda (a b r)
      (cond ((null (cdr b))
          (list (n-normalize r) a))
        (t (let ((quot (div10 a (car b) (cons '#0 '#0))))
             (div (n- a (car quot))
               (cons (d10 (car b)) (cddr b))
               (n+ (x10 r) (cdr quot)))))))))

    (cond ((n-zero b)
        (bottom 'divide-by-zero))
      ((n< a b) (list '#0 a))
      (t (div a (eql a b '(() i)) '#0)))))

(define (n-quotient a b) (car (n-divide a b)))

(define (n-remainder a b) (cadr (n-divide a b)))

(define (even x)
  (neq (memq (car (reverse x)) '#02468) :F))

(define (odd x) (not (even x)))

(define (n-expt x y)
  (letrec
    ((square (lambda (x) (n* x x)))
    (_n-expt (lambda (y)
      (cond ((n-zero y) '#1)
        ((even y)
          (square (n-expt x (n-quotient y '#2))))
        (t (n* x (square (n-expt x (n-quotient y '#2)))))))))
    (_n-expt (natural y))))

(define (nsqrt square)
  (letrec
    ((sqr (lambda (x last)
      (cond ((equal last x) x)
        ((equal last (n+ x '#1))
          (cond ((n> (n* x x) square) (n- x '#1))
            (t x)))
        (t (sqr (n-quotient
                   (n+ x (n-quotient square x))
                   '#2)
                 x))))))
    (sqr square '#0)))

(define (length x)
  (letrec ((len (lambda (x r)
      (cond ((null x) r)
        (t (len (cdr x) (n+ r '#1)))))))
    (len x '#0)))

(define (n-gcd a b)
  (cond ((n-zero b) a)
    ((n-zero a) b)
    ((n< a b) (n-gcd a (n-remainder b a)))
    (t (n-gcd b (n-remainder a b)))))

(define (n-lcm a b)
  (let ((cd (n-gcd a b)))
    (n* cd
        (n* (n-quotient a cd)
            (n-quotient b cd)))))

(define (n-max . a) (apply min/max (cons n> a)))

(define (n-min . a) (apply min/max (cons n< a)))

(package)

(require '=iter)

(define * (arith-iterator natural n* '#1))

(define + (arith-iterator natural n+ '#0))

(define (- . x)
  (cond ((or (null x) (null (cdr x)))
      (bottom '(too few arguments to natural -)))
    (t (reduce (lambda (a b)
                 (n- (natural a) (natural b)))
               x '#0))))
(define < (arith-pred-iterator natural n<))

(define <= (arith-pred-iterator natural n<=))

(define = (arith-pred-iterator natural n=))

(define > (arith-pred-iterator natural n>))

(define >= (arith-pred-iterator natural n>=))

(define divide n-divide)

(define expt n-expt)

(define gcd (arith-iterator natural n-gcd '#0))

(define lcm (arith-iterator natural n-lcm '#0))

(define max n-max)

(define min n-min)

(define one n-one)

(define quotient n-quotient)

(define remainder n-remainder)

(define sqrt nsqrt)

(define zero n-zero)
