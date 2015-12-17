; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Compute A hyperN B:
; (hyper '#4 '#3 '#3) => '#7625597484987
; A, B, and N must all be natural.

(require '=nmath)

(define (hyper n a b)
  (cond ((equal n '#0) (+ '#1 b))
    ((equal n '#1) (+ a b))
    ((one b) a)
    ((equal n '#2) (* a b))
    ((equal n '#3) (expt a b))
    ((equal n '#4) (expt a (hyper n a (- b '#1))))
    ((> n '#4) (hyper (- n '#1) a (hyper n a (- b '#1))))))
