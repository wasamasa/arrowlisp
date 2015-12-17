; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Verify that all members of a list have
; a given property:
; (every atom '(a b c)) => 't

(define (every p x)
  (apply and (map p x)))
