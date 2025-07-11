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
import Cut

-- Equations satisfied by the admissible cut rule
import CutCirceqEquations
import CutEqualities
import CutCongruence
import CutAssociativities

-- Maehara interpolation 
import Interpolation
import VarCondition

-- Well-definedness of Maehara interpolation
import IntrpWellDefined

-- Cut being the left inverse of Maehara interpolation
import CutInterpolation
