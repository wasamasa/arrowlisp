; M-Expression Example Program
; Copyright (C) 2004,2005,2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Solve the Towers of Hanoi.

(require 'mexprc)

(mexpr-eval '(

  m_hanoi[n] :=
    solve[%LEFT, %MIDDLE, %RIGHT, n]
    where
      solve[from, to, via, n] :=
        [n=0-> nil:
          make_move[solve[from, via, to, n-1],
                    list[list[from, to]],
                    solve[via, to, from, n-1]]]
        and
        make_move[a, b, c] :=
          append[a, append[b, c]]

))
