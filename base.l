; ArrowLISP base functions
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

(define base t)

'= ; export

(package base)

(define (null x) (eq x ()))

(define (id x) x)

(define (list . x) x)

(define (not a) (eq a :F))

(define (neq x y)
  (eq (eq x y) :F))

(define (caaaar x) (car (car (car (car x)))))
(define (caaadr x) (car (car (car (cdr x)))))
(define (caadar x) (car (car (cdr (car x)))))
(define (caaddr x) (car (car (cdr (cdr x)))))
(define (cadaar x) (car (cdr (car (car x)))))
(define (cadadr x) (car (cdr (car (cdr x)))))
(define (caddar x) (car (cdr (cdr (car x)))))
(define (cadddr x) (car (cdr (cdr (cdr x)))))
(define (cdaaar x) (cdr (car (car (car x)))))
(define (cdaadr x) (cdr (car (car (cdr x)))))
(define (cdadar x) (cdr (car (cdr (car x)))))
(define (cdaddr x) (cdr (car (cdr (cdr x)))))
(define (cddaar x) (cdr (cdr (car (car x)))))
(define (cddadr x) (cdr (cdr (car (cdr x)))))
(define (cdddar x) (cdr (cdr (cdr (car x)))))
(define (cddddr x) (cdr (cdr (cdr (cdr x)))))

(define (caaar x) (car (car (car x))))
(define (caadr x) (car (car (cdr x))))
(define (cadar x) (car (cdr (car x))))
(define (caddr x) (car (cdr (cdr x))))
(define (cdaar x) (cdr (car (car x))))
(define (cdadr x) (cdr (car (cdr x))))
(define (cddar x) (cdr (cdr (car x))))
(define (cdddr x) (cdr (cdr (cdr x))))

(define (caar x) (car (car x)))
(define (cadr x) (car (cdr x)))
(define (cdar x) (cdr (car x)))
(define (cddr x) (cdr (cdr x)))

(define (reduce f a default)
  (letrec
    ((_reduce (lambda (a res)
      (cond ((null a) res)
        (t (_reduce (cdr a)
             (f res (car a))))))))
    (cond ((null a) default)
      (t (_reduce (cdr a) (car a))))))

(define (reduce-r f a default)
  (letrec
    ((_reduce (lambda (a res)
      (cond ((null a) res)
        (t (_reduce (cdr a)
             (f (car a) res)))))))
    (cond ((null a) default)
      (t (let ((ra (reverse a)))
	   (_reduce (cdr ra) (car ra)))))))

(define (reverse a)
  (letrec
    ((_reverse (lambda (a b)
      (cond ((null a) b)
        (t (_reverse (cdr a) (cons (car a) b)))))))
    (_reverse a ())))

(define (append . a)
  (letrec
    ((append2 (lambda (a b)
      (cond ((null a) b)
        (t (append2 (cdr a) (cons (car a) b))))))
    (_append (lambda (a b)
      (cond ((null b) a)
        (t (append2 (reverse a) b))))))
    (reduce _append a ())))

(define (equal a b)
  (cond
    ((or (atom a) (atom b))
      (eq a b))
    (t (and (equal (car a) (car b))
            (equal (cdr a) (cdr b))))))

(define (assoc x a)
  (letrec
    ((_assoc (lambda (a)
      (cond ((null a) :F)
        ((equal (caar a) x) (car a))
        (t (_assoc (cdr a)))))))
    (_assoc a)))

(define (assq x a)
  (letrec
    ((_assq (lambda (a)
      (cond ((null a) :F)
        ((eq (caar a) x) (car a))
        (t (_assq (cdr a)))))))
    (_assq a)))

(define (listp x)
  (or (null x)
      (and (not (atom x))
           (listp (cdr x)))))

(define (map f . a)
  (letrec
    ((map-list (lambda (f a r)
      (cond ((null a) (reverse r))
        (t (map-list f (cdr a)
                     (cons (f (car a)) r))))))
    (carof (lambda (a)
      (map-list car a ())))
    (cdrof (lambda (a)
      (map-list cdr a ())))
    (any-null (lambda (a)
      (apply or (map-list null a ()))))
    (_map (lambda (a b)
      (cond ((any-null a) (reverse b))
        (t (_map (cdrof a)
              (cons (apply f (carof a)) b)))))))
    (cond ((null a)
        (bottom '(too few arguments to map)))
      (t (_map a ())))))

(define (member x a)
  (letrec
    ((_member (lambda (a)
      (cond ((null a) :F)
        ((equal (car a) x) a)
        (t (_member (cdr a)))))))
    (_member a)))

(define (memq x a)
  (letrec
    ((_memq (lambda (a)
      (cond ((null a) :F)
        ((eq (car a) x) a)
        (t (_memq (cdr a)))))))
    (_memq a)))

(define (require x)
  (letrec
    ((req (lambda (sym file)
      (cond ((defined sym) :F)
        (t (apply load (list file)))))))
    (let ((xx (explode x)))
      (cond ((eq (car xx) '=)
	  (req (implode (cdr xx)) x))
	(t (req x x))))))

(define (export . symbols) t)

(package)
