; M-Expression Example Program
; Copyright (C) 2004,2005,2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Solve the N-Queens puzzle.

(require 'mexprc)

(mexpr-eval '(

  m_queens[size] :=
    n_queens[0, 0, nil]

    where n_queens[q, c, b] := [
      c = size-> b:
      column[q] <> c->
        [null[b]-> nil:
          n_queens[car[b]+1, c-1, cdr[b]]]:
      safe_place[q, b]->
        n_queens[next_column[q], c+1, cons[q, b]]:
      n_queens[q+1, c, b]]

    and column[x] := x/size

    and row[x] := remainder[x, size]

    and can_attack[x,y] :=
      [can_attack_hv[x,y]-> true:
        can_attack_dia[x,y]]

    and can_attack_hv[x,y] :=
      row[x] = row[y] \/ column[x] = column[y]

    and can_attack_dia[x,y] :=
      abs[column[x]-column[y]] = abs[row[x]-row[y]]

    and safe_place[x,b] := [
      null[b]-> true:
        can_attack[car[b], x]-> false:
          safe_place[x, cdr[b]]]

    and next_column[q] := [q+size] / size * size

))

