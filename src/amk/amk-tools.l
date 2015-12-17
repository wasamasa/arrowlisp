; ArrowLISP Micro KANREN Tools
; Copyright (C) 2006 Nils M Holm
;
; Based on "The Reasoned Schemer" by Daniel P. Friedman, et al.
;      and "Sokuza" Mini-KANREN by Oleg Kiselyov.
;
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; (require '=amk)

(define amk-tools 't)

(define vq (var 'q))

(define (conso a d p)
  (== (cons a d) p))

(define (caro p a)
  (let ((x (var 'x)))
    (conso a x p)))

(define (cdro p d)
  (let ((x (var 'x)))
    (conso x d p)))

(define (pairo p)
  (let ((x (var 'x))
        (y (var 'y)))
    (conso x y p)))

(define (eqo x y) (== x y))

(define (nullo a) (eqo a ()))

(define (eq-caro x p) (caro p x))

(define (membero x l)
  (disj* (conj* (eq-caro x l) succeed)
         (let ((vt (var 't)))
           (conj* (cdro l vt) 
                  (lambda (s) ((membero x vt) s))))))

(define (rev-membero x l)
  (disj* (let ((vt (var 't)))
           (conj* (cdro l vt) 
                  (lambda (s) ((rev-membero x vt) s))))
         (conj* (eq-caro x l) succeed)))

(define (reverseo l r)
  (rev-membero r l))

(define (appendo x y r)
  (disj*   
    (conj* (== x ()) (== y r))
    (let ((vh (var 'h))
          (vt (var 't))
          (va (var 'a)))
      (conj*
        (conso vh vt x)
        (conso vh va r)
        (lambda (s) ((appendo vt y va) s))))))

(define (memo x l r)
  (disj* (conj* (eq-caro x l) (== l r))
         (let ((vt (var 't)))
           (conj* (cdro l vt) 
                  (lambda (s) ((memo x vt r) s))))))

(define (dupso x r)
   (let ((vt (var 't))
         (vh (var 'h)))
     (conj* (conso vh vt x)
            (disja* (memo vh vt r)
                    (lambda (s) ((dupso vt r) s))))))

