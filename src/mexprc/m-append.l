; M-Expression Example Program
; Copyright (C) 2004,2005,2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Append two lists.

(require '=mexprc)

(mexpr-eval '(

  m_append[a,b] :=
    r_append[reverse[a], b]
    where
      r_append[a,b] :=
        [null[a]-> b:
        r_append[cdr[a], cons[car[a], b]]]

))
