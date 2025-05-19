# An Agda Formalization of Nonassociative Lambek Calculus and Its Metatheory

The sequent calculus for the nonassociative Lambek calculus  has sequents with binary trees as antecedents, in which formulae are stored as leaves. The shape of the antecedents creates subtleties when proving logical properties, since in many cases one needs to analyze equalities involving sequentially-composed trees. We formally characterize these equalities and show how to employ the resulting technical lemma to prove cut admissibility and the Maehara interpolation properly, which implies Craig interpolation. We show that both the cut rule and the interpolation procedure are well-defined wrt. a certain notion of equivalence of derivations. We additionally prove a proof-relevant version of Maehara interpolation, exhibiting the interpolation procedure as a right inverse of the admissible cut rule.

The main file containing the whole development is [Main.agda](https://github.com/cswphilo/nonassociative-Lambek/blob/main/code/Main.agda).

The formalization uses Agda 2.6.2. 
