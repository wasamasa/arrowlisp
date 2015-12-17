; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Solve the 'Towers of Hanoi':
; (hanoi '#iii) => '(#ab #ac #bc #ab #ca #cb #ab)

(define (hanoi n)
  (letrec
    ((_hanoi (lambda (from to via n)
      (cond ((null n) ())
        (t (append (_hanoi from via to (cdr n))
          (append (list (list from to))
            (_hanoi via to from (cdr n)))))))))
    (_hanoi 'a 'b 'c n)))
