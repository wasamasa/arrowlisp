; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Substitute variables in S-expressions.
; (sublis '(+ 1 2) '((1.i) (2.ii))) => '(+ i ii)

(define (sublis x env)
  (letrec
    ((value-of (lambda (x)
      (let ((v (assq x env)))
        (cond (v (cdr v))
          (t x))))))
    (cond ((null x) ())
      ((atom x) (value-of x))
      (t (cons (sublis (car x) env)
               (sublis (cdr x) env))))))
