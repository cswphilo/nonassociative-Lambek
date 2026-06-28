{-# OPTIONS --rewriting #-}

module Main where

open import Utilities

-- Formulae, trees and an alogorithm checking the relative positions
-- of U₁ and U₂ in sub p₁ U₁ ≡ sub p₂ U₂
import Fma

-- Equations of satisfied by the algorithm
import SubEqProperties

-- Sequent calculus
import SeqCalc

-- Cut-elimination
import Cut.Admissibility

-- Equations satisfied by the admissible cut rule
import Cut.CirceqEquations
import Cut.Equalities
import Cut.Congruence
import Cut.Associativity

-- Maehara interpolation 
import Interpolation.Maehara
import Interpolation.VarCondition

-- Well-definedness of Maehara interpolation
import Interpolation.WellDefined

-- Cut being the left inverse of Maehara interpolation
import Interpolation.ProofRelevant

-- Hilbert-style (axiomatic) presentation of nonassociative Lambek calculus
import Categorical.Free
import Categorical.Universal

-- The Hilbert-style calculus is sound and complete wrt. the sequent calculus
import Categorical.Soundness
import Categorical.Completeness

-- The sound and complt functions are each other's inverses.
import Categorical.SoundnessCompleteness
import Categorical.CompletenessSoundness
