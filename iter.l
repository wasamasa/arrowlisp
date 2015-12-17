; ArrowLISP iterators
; Copyright (C) 2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

(define iter 't)

(package iter)

(define (arith-iterator coerce fn default)
  (lambda x
    (reduce 
      (lambda (a b)
        (fn (coerce a) (coerce b)))
      x default)))

(define (arith-pred-iterator coerce fn)
  (lambda (first . rest)
    (let ((comp (lambda (a b)
      (cond ((eq a t) t)
        ((fn (coerce a) (coerce b)) b)
        (t t)))))
      (cond ((null rest)
          (bottom '(too few arguments)))
        (t (neq (reduce comp (cons first rest) ())
                t))))))

(define (pred-iterator coerce fn)
  (lambda (first . rest)
    (let ((fail (cons 'fail ())))
      (let ((comp (lambda (a b)
        (cond ((eq a fail) fail)
          ((fn (coerce a) (coerce b)) b)
          (t fail)))))
        (cond ((null rest)
            (bottom '(too few arguments)))
          (t (neq (reduce comp (cons first rest) ())
                  fail)))))))

(package)
