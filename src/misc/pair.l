; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Build an association list from two lists:
; (pair '(1 2 3) '(i ii iii)) => '((1 . i) (2 . ii) (3 . iii))

(define (pair a b) (map cons a b))
