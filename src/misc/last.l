; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Extract the last member of a list:
; (last '(a b c d e f)) => 'f

(define (last x) (car (reverse x)))
