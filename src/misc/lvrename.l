; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Rename variables of lambda expressions
; (perform alpha convfersion):
; (lv-rename '(lambda (x) (lambda (x) x)))
; => (lambda (x:0) (lambda (x:1) x:1))

; BUGS: currently does not handle dotted argument lists.

(require '=nmath)

(define (lv-rename expr)
  (letrec

    ((add (lambda (name level)
      (implode (append (explode name) '#: level))))

    (ext-sub (lambda (sub vars level)
      (letrec
        ((add-var (lambda (name level alist)
          (cons (cons name (add name level)) alist))))
        (cond ((null vars) sub)
          ((atom vars) (add-var vars level sub))
          (t (ext-sub (add-var (car vars) level sub)
                      (cdr vars)
                      level))))))

    (ext-sub (lambda (sub vars level)
      (cond ((null vars) sub)
        (t (ext-sub (cons (cons (car vars)
                                (add (car vars) level))
                            sub)
                    (cdr vars)
                    level)))))

    (subst (lambda (name sub)
      (let ((v (assq name sub)))
        (cond (v (cdr v))
          (t name)))))

    (rename-vars (lambda (expr sub level)
      (cond ((atom expr) (subst expr sub))
        ((eq (car expr) 'quote) expr)
        ((eq (car expr) 'lambda)
          (let ((args (cadr expr))
                (body (caddr expr)))
            (let ((new-sub (ext-sub sub args level)))
          (list 'lambda
                 (rename-vars args new-sub level)
                     (rename-vars body new-sub
                                  (+ '#1 level))))))
        (t (map (lambda (x) (rename-vars x sub level))
                expr))))))

    (rename-vars expr () '#0)))
