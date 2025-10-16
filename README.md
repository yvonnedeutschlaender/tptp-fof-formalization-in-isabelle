# Formalization of a subset of TPTP FOF in Isabelle/HOL

This formalization was developed as part of my bachelor's thesis and specifies:
- a first-order logic based on TPTP FOF (FOF_Base.thy), 
- a function that simplifies formulas and its correctness (FOF_Simplify.thy), and 
- a function that converts formulas into conjunctive normal form and its correctness (FOF_Tseitin.thy). This function is based on the Tseitin transformation and converts formulas that are in negation normal form.

The additional theories include examples (FOF_Examples.thy), the specification of a subset of TPTP file syntax (TPTP_Base.thy), and the implementation of my idea of a Tseitin transformation function (TPTP_Tseitin_Failed_Proof.thy).

## License
This Isabelle/HOL formalization is licensed under a BSD-style license, as used in the Archive of Formal Proofs (AFP). 
See the [LICENSE](./LICENSE) file for details.