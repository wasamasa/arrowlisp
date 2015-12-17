; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Compute the sum of a sequence of positive numbers:
; (sum '#2 '#5) => '#14

(require '=nmath)

(define (sum n m)
  (letrec
    ((_sum (lambda (n m)
      (let ((x (+ '#1 (- m n))))
        (+ (quotient (+ (* x x) x)
                     '#2)
           (* (- n '#1) x))))))
    (let ((nn (natural n))
          (nm (natural m)))
      (cond ((or (zero nn) (zero nm))
          (bottom 'sum n m))
        (_sum (min nn nm) (max nn nm))))))
