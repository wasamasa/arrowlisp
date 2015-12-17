; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Check if an expression X is the head of an
; expression Y:
; (headp '(a b c) '(a b c d e f)) => 't

(define (headp x y)
  (cond ((null y) (null x))
    ((null x) t)
    (t (and (equal (car x) (car y))
            (headp (cdr x) (cdr y))))))
