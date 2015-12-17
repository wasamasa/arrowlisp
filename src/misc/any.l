; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Verify that at least one member of a list has
; a given property:
; (any atom '((a b c) x (d e f))) => 't

(define (any p x)
  (apply or (map p x)))
