; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Extract members matching a given predicate:
; (filter atom '(abc #123 def #456 ghi)) => '(abc def ghi)

(define (filter p a)
  (letrec
    ((flt (lambda (a b)
      (cond ((null a) b)
        ((p (car a)) (flt (cdr a) (cons (car a) b)))
        (t (flt (cdr a) b))))))
    (flt (reverse a) ())))
