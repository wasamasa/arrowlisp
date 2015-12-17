; ArrowLISP Example Program
; Copyright (C) 1998-2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Solve the N-queens problem using backtracking.
; (queens '#4)

(require '=nmath)

(define (queens board-size)
  (letrec

  ((column (lambda (x) (quotient x board-size)))

  (row (lambda (x) (remainder x board-size)))

  (incr (lambda (x) (+ '#1 x)))

  (decr (lambda (x) (- x '#1)))

  ; Can X attack Y horizontally or vertically?
  (can-attack-hv-p (lambda (x y)
    (or (= (row x) (row y))
        (= (column x) (column y)))))

  ; Compute |X-Y|
  (abs-diff (lambda (x y)
    (cond ((< x y) (- y x))
      (t (- x y)))))

  ; Can X attack Y diagonally?
  (can-attack-dia-p (lambda (x y)
    (= (abs-diff (column x) (column y))
       (abs-diff (row x) (row y)))))

  (can-attack-p (lambda (x y)
    (or (can-attack-hv-p x y)
        (can-attack-dia-p x y))))

  ; Test whether the square X
  ; is safe on a given board.
  (safe-place-p (lambda (x b)
    (cond ((null b) t)
      ((can-attack-p (car b) x) :F)
      (t (safe-place-p x (cdr b))))))

  ; Compute the number of the first square
  ; of the next column, where Q is any square
  ; of the current column
  (next-column (lambda (q)
    (* (quotient (+ q board-size)
                 board-size)
       board-size)))

  ; Solve N Queens:
  ; Q = next square to check
  ; C = current column
  ; B = board so far
  (n-queens (lambda (q c b)
    (cond ((equal c board-size) b)
      ((> (column q) c)
        (cond ((null b) ())
          (t (n-queens (incr (car b))
                       (decr c) (cdr b)))))
      ((safe-place-p q b)
        (n-queens (next-column q)
                  (incr c) (cons q b)))
      (t
        (n-queens (incr q) c b))))))

  (n-queens '#0 '#0 ())))
