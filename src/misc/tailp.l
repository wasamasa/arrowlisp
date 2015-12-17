; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Check if an expression X is equal to the tail
; of an expression Y:
; (tailp '(d e f) '(a b c d e f)) => 't

(define (tailp x y)
  (cond ((null y) (null x))
    (t (or (equal x y)
           (tailp x (cdr y))))))
