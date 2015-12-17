; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Compute the product of a sequence of numbers:
; (product '#5 '#7) => '#210

(require '=nmath)

(define (product lo hi)
  (letrec
    ((prod (lambda (x lim res)
      (cond ((> x lim) res)
        (t (prod (+ '#1 x) lim
                 (* res x)))))))
    (let ((n-lo (natural lo))
          (n-hi (natural hi)))
      (prod (min n-lo n-hi) (max n-lo n-hi) '#1))))
