; ArrowLISP Example Program
; Copyright (C) 2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Evaluate a pure LISP expression in a given environment:
; (xeval '(letrec ((foo (lambda (x)
;                   (cond ((eq x ()) 'foo)
;                     (t (foo (cdr x)))))))
;           (foo '#xxxxx)) ())
; => 'foo

; This is basically an interpreter for ArrowLISP modulo DEFINE.
; Yes, it is lexically scoped and tail-recursive.

(define (xeval x e)
  (letrec

    ((initial-env (list
      (cons 'closure        'closure)
      (cons ':t             ':t)
      (cons ':f             ':f)
      (cons 'and            '(%special . and))
      (cons 'apply          '(%special . apply))
      (cons 'cond           '(%special . cond))
      (cons 'define         '(%special . define))
      (cons 'eval           '(%special . eval))
      (cons 'lambda         '(%special . lambda))
      (cons 'let            '(%special . let))
      (cons 'letrec         '(%special . letrec))
      (cons 'or             '(%special . or))
      (cons 'quote          '(%special . quote))
      (cons 'atom           (cons '%primitive atom))
      (cons 'bottom         (cons '%primitive bottom))
      (cons 'car            (cons '%primitive car))
      (cons 'cdr            (cons '%primitive cdr))
      (cons 'cons           (cons '%primitive cons))
      (cons 'defined        (cons '%primitive defined))
      (cons 'eq             (cons '%primitive eq))
      (cons 'explode        (cons '%primitive explode))
      (cons 'implode        (cons '%primitive implode))
      (cons 'read           (cons '%primitive read))
      (cons 'recursive-bind (cons '%primitive recursive-bind))
      (cons 'write          (cons '%primitive write))))

    (value-of (lambda (x e)
      (let ((v (assq x e)))
        (cond (v (cdr v))
          (t (bottom 'undefined: x))))))

    (ev-list (lambda (x e)
      (cond ((null x) ())
        ((atom x) (bottom 'improper 'list
                    'in 'application: x))
        (t (cons (ev (car x) e)
                 (ev-list (cdr x) e))))))

    (check-args (lambda (a n)
      (cond ((null n) (null a))
        ((null a) :F)
        (t (check-args (cdr a)
                       (cdr n))))))

    (wrong-args (lambda (name args)
      (bottom 'wrong 'number 'of 'arguments:
        (cons name args))))

    (args-ok (lambda (name a n)
      (cond ((check-args a n) t)
        (t (wrong-args name a)))))

    (until (lambda (term a e)
      (cond ((null (cdr a)) (car a))
        ((atom a) (bottom 'improper 'list
                    'in 'and/or: a))
        (t (let ((v (ev (car a) e)))
              (cond ((eq (not v) (not term))
                  (list 'quote v))
                (t (until term (cdr a) e))))))))

    (do-and (lambda (a e)
      (cond ((null a) t)
        (t (until :F a e)))))

    (clause-p (lambda (x)
      (and (not (atom x))
           (not (atom (cdr x)))
           (null (cddr x)))))

    (do-cond (lambda (a e)
      (cond ((null a)
          (bottom 'no 'default 'in 'cond))
        ((atom a)
          (bottom 'improper 'list 'in 'cond))
        ((not (clause-p (car a)))
          (bottom 'bad 'clause 'in 'cond: (car a)))
        (t (let ((v (ev (caar a) e)))
             (cond (v (cadar a))
               (t (do-cond (cdr a) e))))))))

    (do-eval (lambda (args e)
      (and (args-ok 'eval args '#i)
           (ev (car args) e))))

    (lambda-args (lambda (a)
      (letrec
        ((args (lambda (a)
          (cond ((null a) ())
            ((atom a) (list a))
            (t (cons (car a) (args (cdr a))))))))
        (cond ((atom a) (list a))
          (t (args a))))))

    (add-free-var (lambda (fenv var e)
      (cond ((assq var fenv) fenv)
        (t (let ((v (assq var e)))
             (cond (v (cons v fenv))
               (t (cons (cons var '%void) fenv))))))))

    (capture (lambda (bound x e)
      (letrec
        ((collect (lambda (x free)
          (cond ((null x) free)
            ((atom x)
              (cond ((memq x bound) free)
                (t (add-free-var free x e))))
            (t (collect (car x)
                 (collect (cdr x) free)))))))
        (collect x ()))))

    (do-lambda (lambda (args e)
      (and (args-ok 'lambda args '#ii)
        (list 'closure (car args) (cadr args)
              (capture (lambda-args (car args))
                       (cadr args) e)))))

    (do-or (lambda (a e)
      (cond ((null a) :F)
        (t (until t a e)))))

    (do-quote (lambda (args)
      (and (args-ok 'quote args '#i)
           (car args))))

    (make-env (lambda (fa aa)
      (cond ((null fa)
          (cond ((null aa) ())
            (t (bottom 'too 'many 'arguments))))
        ((atom fa)
          (list (cons fa aa)))
        ((null aa)
          (t (bottom 'too 'few 'arguments)))
        (t (cons (cons (car fa) (car aa))
                 (make-env (cdr fa) (cdr aa)))))))

    (beta (lambda (expr fa aa lex-env e le fix)
      (ev2 expr e (append (fix (make-env fa aa)) lex-env le))))

    (do-let (lambda (args e le fix)
      (letrec
        ((formals (lambda (a)
          (map car a)))
        (actuals (lambda (a)
          (map cadr a))))
        (beta (cadr args)
              (formals (car args))
              (ev-list (actuals (car args)) le)
              () e le fix))))

    (apply-fn (lambda (fn args e le)
      (cond ((eq (car fn) '%primitive)
          (apply (cdr fn) args))
        ((eq (car fn) '%special)
          (apply-special (cdr fn) args e le))
        ((eq (car fn) 'closure)
          (beta (caddr fn) (cadr fn) args
            (cadddr fn) e le id))
        (t (bottom 'application 'of 
             'non-function: fn)))))

    (apply-special (lambda (fn args e le)
      (cond ((eq fn 'and)
          (ev2 (do-and args le) e le))
        ((eq fn 'apply) 
          (let ((args (ev-list args le)))
            (and (args-ok 'apply args '#ii)
              (apply-fn (car args) (cadr args) e e))))
        ((eq fn 'cond)
          (ev2 (do-cond args le) e le))
        ((eq fn 'eval)
          (ev2 (do-eval args le) e le))
        ((eq fn 'lambda)
          (do-lambda args le))
        ((eq fn 'let)
          (do-let args e le id))
        ((eq fn 'letrec)
          (do-let args e le recursive-bind))
        ((eq fn 'or)
          (ev2 (do-or args le) e le))
        ((eq fn 'quote)
          (do-quote args))
        (t (bottom 'internal: 'bad 'special-op: fn)))))

    (function-p (lambda (x)
      (or (eq (car x) '%primitive)
          (eq (car x) 'closure))))

    (special-p (lambda (x)
      (eq (car x) '%special)))

    (ev2 (lambda (x e le)
      (cond ((null x) ())
        ((atom x) (value-of x le))
        (t (let ((f (ev (car x) le)))
             (cond ((eq f 'closure) x)
               ((atom f) (bottom 'application 'of
                           'non-function: f))
               (t (let ((args (cond ((function-p f)
                                  (ev-list (cdr x) le))
                                (t (cdr x))))
                        (new-e (cond ((special-p f) le)
                                 (t e))))
                    (apply-fn f args e new-e)))))))))

    (ev (lambda (x e)
      (ev2 x e e))))

    (ev x (append e initial-env))))
