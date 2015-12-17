; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Sort a list using insertion sort:
; (require '=nmath)
; (isort > '(#1 #3 #0 #2 #4)) => '(#4 #3 #2 #1 #0)

(require '=insert)

(define (isort p a)
  (Letrec
    ((srt (lambda (a r)
      (cond ((null a) r)
        (t (srt (cdr a)
                (insert p (car a) r)))))))
    (srt a ())))
