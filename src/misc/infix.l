; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Convert arithmetic expressions from prefix to
; infix notation:
; (prefix->infix '(+ '#+2 (* '#+3 (expt '#+4 (+ '#+5 '#+6)))))
; => '#2+3*4^[5+6]

; Prefix expressions may contain variables
; [symbols like X], numbers [like '#+57], and
; these functions: +, - (unary or binary), *, /,
; EXPT. PREFIX->INFIX will insert parentheses
; ([ and ]) where required.

(define (prefix->infix x)
  (letrec

  ; Function->operator
  ((ops '((+.+) (-.-) (*.*) (/./) (expt.^)))

  ; Precedence of operators
  (precedence '((high) (expt) (* /) (+ -) (low)))

  (function-p (lambda (x)
    (memq x '(+ - * / expt))))

  (symbol-p (lambda (x)
    (memq x '#abcdefghijklmnopqrstuvwxyz)))

  ; Numbers are always quoted, eg (QUOTE #+5)
  (numeric-p (lambda (x)
    (and (not (atom x))
         (eq (car x) 'quote))))

  ; Has function X a higher precedence than Y?
  (higher-prec-p (lambda (x y)
    (letrec
      ((hp (lambda (x y l)
        (cond ((null l) :F)
          ((member x (car l))
            (not (member y (car l))))
          ((member y (car l)) :F)
          (t (hp x y (cdr l)))))))
      (hp x y precedence))))

  (parenthesize (lambda (x) (append '#[ x '#])))

  (infix (lambda (x op)
    (cond ((numeric-p x)
        ; Number: remove positive sign
        (cond ((eq (caadr x) '-) (cadr x))
          (t (cdadr x))))
      ((symbol-p x) (list x))
      ((and (eq (car x) '-)
            (not (atom (cdr x)))
            (null (cddr x)))
        (append '#- (infix (cadr x) 'high)))
      ; Binary function?
      ((and (not (atom x))
            (function-p (car x)))
        ; Convert prefix to infixix
        (let ((sub (append (infix (cadr x) (car x))
                           (list (cdr (assq (car x) ops)))
                           (infix (caddr x) (car x)))))
          ; If the surrounding operation has a higher
          ; precedence, parenthesize this expression
          (cond ((higher-prec-p op (car x))
              (parenthesize sub))
            (t sub))))
      (t (bottom (list 'syntax: x)))))))

  (infix x 'low)))
