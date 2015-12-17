; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Extract the tail of a list where the first
; member of the tail has a given property:
; (some null '(a b () c d)) => '(() c d)

(define (some p x)
  (letrec
    ((_some (lambda (x)
      (cond ((null x) :F)
        ((p (car x)) x)
        (t (_some (cdr x)))))))
    (_some x)))
