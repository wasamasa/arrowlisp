; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Compute X!:
; (fact '#5) => '#120

(require '=nmath)

(define (fact n)
  (letrec
    ((r* (lambda (n k)
      (cond ((< k '#2) n)
        (t (let ((l (quotient k '#2)))
              (* (r* n l)
                 (r* (+ n l) (- k l)))))))))
    (r* '#1 (natural n))))
