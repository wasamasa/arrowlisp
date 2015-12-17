; ArrowLISP Example Program
; Copyright (C) 2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Create a generator:
; (load =nmath)
; (generator '#0 (lambda (x) (+ x '#1))) => '(#0 . (closure ()))
; ((cdr **) => '(#1 . (closure ()))
; ((cdr **) => '(#2 . (closure ()))
; ((cdr **) => '(#3 . (closure ()))
; ...

(define (generator start step)
  (lambda ()
    (cons start
          (generator (step start) step))))
