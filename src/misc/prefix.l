; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Convert arithmetic expressions in infix notation
; to S-expressions:
; (infix->prefix '#12+34*56^[7+8])
; => '(+ '#12 (* '#34 (expt '#56 (+ '#7 '#8))))

; Infix expressions are represented by flat lists of
; variables (atoms) operators (atoms) and ArrowLISP-style
; numbers (eg #5).

; The following operators are recognized: +, - (both
; unary and binary), *, /, ^. Brackets ([, ]) are
; recoginzed as parentheses.

(require '=rmath)

(define (infix->prefix x)
  (letrec

  ((symbolp (lambda (x)
    (memq x '#abcdefghijklmnopqrstuvwxyz)))

  (numericp (lambda (x)
    (and (not (atom x))
         (eq (car x) 'quote))))

  (operatorp (lambda (x) (memq x '#^*/+-)))

  ; Extract a numeric value from the beginning of X.
  ; Return (N XR) where N is the value extracted and
  ; XR is the rest of X (X with N removed).
  (number (lambda (x r)
    (cond ((null x)
        (list (list 'quote (reverse r)) x))
      ((not (digit (car x)))
        (list (list 'quote (reverse r)) x))
      (t (number (cdr x) (cons (car x) r))))))

  ; These functions are used to extract parts
  ; of (EXPR REST) lists where EXPR is the prefix
  ; expression built so far and REST is the rest
  ; the source expression to parse
  (car-of-rest caadr)
  (cdr-of-rest cdadr)
  (expr car)
  (rest cadr)

  ; Parse factors:
  ; factor := [ sum ]
  ;   | - factor
  ; | Number
  ; | Symbol
  (factor (lambda (x)
    (cond ((null x) (list x ()))
      ; Parse parenthesized subexpressions
      ((eq (car x) '[)
        (let ((xsub (sum (cdr x))))
          (cond ((null (rest xsub)) (bottom 'missing-paren))
            ((eq (car-of-rest xsub) '])
              (list (expr xsub) (cdr-of-rest xsub)))
            (t (bottom 'missing-paren)))))
      ; Parse applications of unary minuses
      ((eq (car x) '-)
        (let ((fac (factor (cdr x))))
          (list (list '- (expr fac)) (rest fac))))
      ; Parse literal numbers
      ((digit (car x))
        (number x ()))
      ; Parse symbols
      (t (list (car x) (cdr x))))))

  ; Parse powers:
  ; power := factor
  ; | factor ^ power
  (power (lambda (x)
    (let ((left (factor x)))
      (cond ((null (rest left)) left)
        ((eq (car-of-rest left) '^)
          (let ((right (power (cdr-of-rest left))))
            (list (list 'expt (expr left) (expr right))
              (rest right))))
        (t left)))))

  ; Parse terms:
  ; term := power
  ; | power Symbol
  ; | power * term
  ; | power / term
  (term (lambda (x)
    (let ((left (power x)))
      (cond ((null (rest left)) left)
        ((symbolp (car-of-rest left))
          (let ((right (term (rest left))))
            (list (list '* (expr left) (expr right))
              (rest right))))
        ((eq (car-of-rest left) '*)
          (let ((right (term (cdr-of-rest left))))
            (list (list '* (expr left) (expr right))
              (rest right))))
        ((eq (car-of-rest left) '/)
          (let ((right (term (cdr-of-rest left))))
            (list (list '/ (expr left) (expr right))
              (rest right))))
        (t left)))))

  ; Parse sums:
  ; sum := term
  ; | term + sum
  ; | term - sum
  (sum (lambda (x)
    (let ((left (term x)))
      (cond ((null (rest left)) left)
        ((eq (car-of-rest left) '+)
          (let ((right (sum (cdr-of-rest left))))
            (list (list '+ (expr left) (expr right))
              (rest right))))
        ((eq (car-of-rest left) '-)
          (let ((right (sum (cdr-of-rest left))))
            (list (list '- (expr left) (expr right))
              (rest right))))
        (t left))))))

  ; Pass X to the recursive descent parser consisting of
  ; SUM, TERM, POWER, FACTOR. The parsing process returns a
  ; list of the form (EXPR REST) as described above. When the
  ; REST is NIL, the entire expression could be parsed
  ; successfully.
  (let ((px (sum x)))
    (cond ((not (null (rest px)))
        (bottom (list 'syntax: (cadr px))))
      (t (expr px))))))

