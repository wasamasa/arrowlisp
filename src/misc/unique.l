; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Transform a list into a set (a list containing
; only unique elements):
; (unique '(aa ab ac ad ab aa)) => '(aa ab ac ad)

(define (unique a)
  (letrec
    ((uniq (lambda (a r)
      (cond ((null a) (reverse r))
        ((member (car a) r) (uniq (cdr a) r))
        (t (uniq (cdr a) (cons (car a) r)))))))
    (uniq a ())))
