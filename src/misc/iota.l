; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Generate a sequence of natural numbers:
; (iota '#5 '#10) => '(#5 #6 #7 #8 #9 #10)

(require '=imath)

(define (iota lo hi)
  (letrec
    ((j (lambda (x r)
      (cond ((< x lo) r)
        (t (j (- x '#1) (cons x r)))))))
    (j (natural hi) ())))
