; M-Expression Example Program
; Copyright (C) 2004,2005,2006 Nils M Holm. All rights reserved.
; See the file LICENSE of the ArrowLISP distribution
; for conditions of use.

; Compute the factorial of an integer.

(require '=mexprc)

(mexpr-eval '(

  m_fac[x] := [x=0 -> 1 : m_fac[x-1] * x]

))
