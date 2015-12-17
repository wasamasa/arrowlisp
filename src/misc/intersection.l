; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Compute the intersection of two sets:
; (intersection '(aa ab ac) '(ab xx aa)) => '(aa ab)

(define (intersection a b)
  (letrec
    ((isec (lambda (a r)
      (cond ((null a) (reverse r))
        ((member (car a) b)
          (isec (cdr a) (cons (car a) r)))
        (t (isec (cdr a) r))))))
    (isec a ())))
