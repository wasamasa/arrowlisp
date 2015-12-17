; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; A simple PROLOG interpreter.

; This program is heavily based on a tiny PROLOG
; interpreter in MACLISP written by Ken Kahn.

(define (prolog q db)
  (letrec

  ; Is X a variable?
  ((var-p (lambda (x)
    (cond ((atom x) :F)
      (t (eq (car x) '?)))))

  ; Create an environment of unique names by
  ; appending ID to each variable.
  (newscope (lambda (x ident)
    (letrec
      ((new (lambda (x)
        (cond ((atom x) x)
          ((var-p x) (append x ident))
          (t (cons (new (car x)) (new (cdr x))))))))
        (new x))))

  ; Increment ID.
  (nextid (lambda (x) (list (cons 'i (car x)))))

  ; Find the value of a variable in a given environment.
  ; For unbound variables, return the variable itself.
  (value (lambda (x env)
    (cond ((var-p x)
        (let ((b (assoc x env)))
          (cond (b (value (cdr b) env))
            (t x))))
      (t x))))

  ; Unify two expressions X and Y in a given environment.
  ; If X and Y can be unified, return a new environment in
  ; which the variables of X and Y are bound.
  ; If the unification fails, return ().
  (unify (lambda (x y env)
    (let ((x (value x env))
          (y (value y env)))
      (cond
        ((var-p x) (cons (cons x y) env))
        ((var-p y) (cons (cons y x) env))

        ((atom x) (cond ((eq x y) env) (t ())))
        ((atom y) (cond ((eq x y) env) (t ())))

        (t (let ((newenv (unify (car x) (car y) env)))
              (cond ((null newenv) ())
                (t (unify (cdr x) (cdr y) newenv)))))))))

  ; Attempt to unify each goal with each rule.
  ; RULES  = list of rules (database)
  ; GOALS  = conjunction of goals
  ; ENV    = environment to unify in
  ; ID     = scope ID
  ; RESULT = list of results so far
  (try-rules (lambda (rules goals env ident result)
    (cond ((null rules) result)
      (t (let ((thisrule (newscope (car rules) ident)))
           (let ((newenv (unify (car goals)
                                (car thisrule) env)))
             (cond ((null newenv)
                 (try-rules (cdr rules) goals env ident result))
               (t (let ((res (prove (append (cdr thisrule)
                                            (cdr goals))
                                    newenv (nextid ident))))
                    (try-rules (cdr rules) goals env ident
                      (append result res)))))))))))

  ; Pretty-print results using TRACE
  (print (lambda (x) x))

  ; Create a list of bindings:
  ; ( (VAR-1 . VALUE-1) ... (VAR-N . VALUE-N) ).
  ; Each binding is prepresented by
  ; (VAR . VALUE),
  ; where VAR is the name and VALUE is the value
  ; of a variable bound in the outermost scope.
  (listenv (lambda (env)
    (letrec
      ((lsenv (lambda (e res)
        (cond ((null (cdr e)) (list (print res)))
          ; Variables of the outer scope have ID=()
          ((null (caddr (caar e)))
            (lsenv (cdr e)
              (cons (cons (cadr (caar e))
                          (value (caar e) env))
                    res)))
          (t (lsenv (cdr e) res))))))
      (lsenv env ()))))

  ; Prove a list of goals in a given environment.
  ; GOALS = list of goals
  ; ENV   = environment
  ; ID    = scope ID
  (prove (lambda (goals env ident)
    (cond ((null goals) (listenv env))  
      (t (try-rules db goals env ident ()))))))

  ; (()) is the initial environment because
  ; () would indicate failure in UNIFY.
  (prove (list (newscope q '(()))) '((())) '((i)))))

; This is a utility function to submit queries to
; a predefined database bound to *DATABASE*.
; Use (TRACE PRINT) to watch the output of QUERY.
(define (query q)
  (let ((result (prolog q *database*)))
  (cond ((equal result '(())) 'yes)
    (t 'no))))
