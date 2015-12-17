; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Recursively count the atoms of a list:
; (count '(a (b (c)))) => '#3

(require '=nmath)

(define (count x)
  (cond ((null x) '#0)
    ((atom x) '#1)
    (t (+ (count (car x))
          (count (cdr x))))))
