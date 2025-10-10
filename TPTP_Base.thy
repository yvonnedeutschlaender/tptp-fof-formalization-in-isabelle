theory TPTP_Base
  imports Main FOF_Base

begin

datatype 'n name =
Name 'n

datatype role =
Axiom |
Lemma |
Theorem |
Conjecture

datatype ('n, 'v, 'f, 'p) annot_formula =
FOF "'n name" role "('v, 'f, 'p) formula"

datatype ('n, 'v, 'f, 'p) TPTP_file = 
Input "('n, 'v, 'f, 'p) annot_formula list"

end