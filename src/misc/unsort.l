; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Generate some entropy by un-sorting a list of
; natural numbers:
; (require '=iota)
; (unsort (iota '#1 '#10) '#5)

(require '=nmath)

(define (unsort a seed)
  (letrec

  ; Extract the n'th element of a list
  ((nth (lambda (a n)
    (cond ((zero n) (car a))
      (t (nth (cdr a) (- n '#1))))))

  ; Generate a list with the n'th element removed
  (nonth (lambda (a n r)
    (cond ((zero n) 
        (cond ((null a) (reverse r))
          (t (append (cdr a) (reverse r)))))
      (t (nonth (cdr a) (- n '#1)
           (cons (car a) r))))))

  ; Unsort list A of length K by first extracting element N,
  ; keep intermediate result in R
  (unsrt (lambda (a n k r)
    (cond ((zero k) (cons (car a) r))
      (t (unsrt (nonth a n ()) (remainder (car a) k)
          (- k '#1) (cons (nth a n) r)))))))

  (unsrt a seed (- (length a) '#1) ())))
