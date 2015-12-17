; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Compute the union of two sets:
; (union '(aa ab ac) '(ab ad ae)) => '(aa ab ac ad ae)

(require '=unique)

(define (union a b)
  (unique (append a b)))
