; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Extract the tail of a list beginning at the n'th
; member of that list:
; (nth '#2 '#abcdef) => '#cdef

(require '=nmath)

(define (nth n x)
  (cond ((null x) :F)
    ((zero n) x)
    (t (nth (- n '#1)
            (cdr x)))))
