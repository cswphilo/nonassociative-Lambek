# An Agda Formalization of Nonassociative Lambek Calculus and Its Metatheory

The sequent calculus for the nonassociative Lambek calculus  has sequents with binary trees as antecedents, in which formulae are stored as leaves. The shape of the antecedents creates subtleties when proving logical properties, since in many cases one needs to analyze equalities involving sequentially-composed trees. We formally characterize these equalities and show how to employ the resulting technical lemma to prove cut admissibility and the Maehara interpolation properly, which implies Craig interpolation. We show that both the cut rule and the interpolation procedure are well-defined wrt. a certain notion of equivalence of derivations. We additionally prove a proof-relevant version of Maehara interpolation, exhibiting the interpolation procedure as a right inverse of the admissible cut rule.

The main file containing the whole development is [Main.agda](https://github.com/cswphilo/nonassociative-Lambek/blob/main/code/Main.agda).

From a practical perspective, it is worth mentioning that this Agda formalization is computationally intensive. The type-checking time for some files is quite substantial:

- the well-definedness proof $\mathsf{mip{\circeq}}$, [IntrpWellDefined.agda](https://github.com/cswphilo/nonassociative-Lambek/blob/main/code/IntrpWellDefined.agda) takes ~10 minutes to type-check, while
- the associativity and commutativity of $\mathsf{cut}$, [CutAssociativities.agda](https://github.com/cswphilo/nonassociative-Lambek/blob/main/code/CutAssociativities.agda) and
- the well-definedness proofs $\mathsf{cut{-}cong1}$ and $\mathsf{cut{-}cong2}$, [CutCongruence.agda](https://github.com/cswphilo/nonassociative-Lambek/blob/main/code/CutCongruence.agda) require >2 hours

on a MacBook Pro 2020 with 2 GHz Intel Core i5.

In future work, we plan to work on the code in order to reduce the compilation time.

The formalization uses Agda 2.7.0.1.
