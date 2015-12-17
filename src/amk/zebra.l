; ArrowLISP Micro KANREN Example Program
; Copyright (C) 2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Solve the Zebra puzzle:
; alisp -n 1024K
; (load zebra)
; (zebra)

(require '=amk)
(require '=amk-tools)

(define (memb x l)
  (let ((vh (var 'h))
        (vt (var 't)))
    (disj* (conj* (caro l vh)
                  (== vh x))
           (conj* (cdro l vt)
                  (lambda (s) ((memb x vt) s))))))

(define (left-of x y l)
  (let ((vh (var 'h))
        (vt (var 't))
        (vz (var 'z)))
    (disj* (conj* (caro l vh)
                  (cdro l vt)
                  (caro vt vz)
                  (== vz y)
                  (== vh x))
           (conj* (cdro l vt)
                  (lambda (s) ((left-of x y vt) s))))))

(define (next-to x y l)
  (disj* (left-of x y l)
         (left-of y x l)))

(define (zebra)
  (arun* vq
    '(let ((h (var 'h)))
       (conj*
         (== h (list (list 'norwegian ,_ ,_ ,_ ,_)
                     ,_
                     (list ,_ ,_ 'milk ,_ ,_)
                     ,_
                     ,_))
         (memb (list 'englishman ,_ ,_ ,_ 'red) h)
         (left-of (list ,_ ,_ ,_ ,_ 'green)
                  (list ,_ ,_ ,_ ,_ 'ivory) h)
         (next-to (list 'norwegian ,_ ,_ ,_ ,_)
                  (list ,_ ,_ ,_ ,_ 'blue) h)
         (memb (list ,_ 'kools ,_ ,_ 'yellow) h)
         (memb (list 'spaniard ,_ ,_ 'dog ,_) h)
         (memb (list ,_ ,_ 'coffee ,_ 'green) h) 
         (memb (list 'ukrainian ,_ 'tea ,_ ,_) h)
         (memb (list ,_ 'luckystrikes 'orangejuice ,_ ,_) h)
         (memb (list 'japanese 'parliaments ,_ ,_ ,_) h)
         (memb (list ,_ 'oldgolds ,_ 'snails ,_) h)
         (next-to (list ,_ ,_ ,_ 'horse ,_)
                  (list ,_ 'kools ,_ ,_ ,_) h)
         (next-to (list ,_ ,_ ,_ 'fox ,_)
                  (list ,_ 'chesterfields ,_ ,_ ,_) h)
         (memb (list ,_ ,_ 'water ,_ ,_) h)
         (memb (list ,_ ,_ ,_ 'zebra ,_) h)
         (== vq h)))))

