; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Remove members from a list.
; (remove atom '(abc #123 def #456 ghi)) => '(#123 #456)

(define (remove p x)
  (filter (lambda (x) (not (p x))) x))
