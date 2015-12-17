; ArrowLISP streams
; Copyright (C) 2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

(define streams 't)

(package streams)

(define (stream v first rest lim)
  (letrec
    ((stream (lambda (v)
      (lambda ()
        (cond ((lim v) :f)
          (t (cons (first v)
                   (stream (rest v)))))))))
    ((stream v))))

(define (list->stream v)
  (stream v car cdr null))

(define (stream->list s)
  (letrec
    ((stream->list (lambda (s lst)
      (cond (s (stream->list ((cdr s))
                             (cons (car s) lst)))
        (t (reverse lst))))))
    (stream->list s ())))

(define (map-stream f s)
  (stream s (lambda (s) (f (car s)))
            (lambda (s) ((cdr s)))
            (lambda (s) (eq :f s))))

(package)
