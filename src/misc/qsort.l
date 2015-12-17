; ArrowLISP Example Program
; Copyright (C) 2005,2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Sort a list using the Quicksort algorithm:
; (require '=nmath)
; (qsort <= '(#5 #1 #3 #2 #4)) => '(#1 #2 #3 #4 #5)

(define (qsort p a)
  (letrec

    ((filter (lambda (p a r)
      (cond ((null a) (reverse r))
        ((p (car a))
          (filter p (cdr a) (cons (car a) r)))
        (t (filter p (cdr a) r)))))

    (_qsort (lambda (a)
      (cond ((null a) a)
        (t (letrec
             ((left-part (lambda (x)
               (lambda (y) (not (p x y)))))
             (right-part (lambda (x)
               (lambda (y) (p x y)))))
             (append
               (_qsort (filter
                         (left-part (car a))
                         (cdr a) ()))
               (list (car a))
               (_qsort (filter
                         (right-part (car a))
                         (cdr a) ())))))))))

    (_qsort a)))

