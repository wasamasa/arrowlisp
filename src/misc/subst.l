; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Substitute OLD by NEW in EXPR:
; (subst 'x 'z '(a x (x) (x z)))) => '(a z #z #zz)

(define (subst old new expr)
  (letrec
    ((_subst (lambda (x)
      (cond ((equal old x) new)
        ((atom x) x)
        (t (cons (_subst (car x))
                 (_subst (cdr x))))))))
    (_subst expr)))
