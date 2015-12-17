; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Check whether the members of a list
; are in a given monotonic order:
; (require '=nmath)
; (orderedp > '(#9 #8 #7 #6 #5)) => 't

(define (orderedp p x)
  (letrec
    ((ordp (lambda (x)
      (cond ((or (null x) (null (cdr x))) t)
        (t (and (p (car x) (cadr x))
                (ordp (cdr x))))))))
    (ordp x)))
