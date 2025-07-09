{-# OPTIONS --rewriting #-}

module Subeq-1 where

open import Fma

subeq⁻¹ : ∀ {T₁ T₂ U₁ U₂} {p₁ : Path T₁} {p₂ : Path T₂}
  → SubEqCases p₁ p₂ U₁ U₂
  → sub p₁ U₁ ≡ sub p₂ U₂
subeq⁻¹ (1≡2 (same refl refl refl)) = refl
subeq⁻¹ (2>L1 (gt q refl refl refl)) = refl
subeq⁻¹ (2>R1 (gt q refl refl refl)) = refl
subeq⁻¹ (1>L2 (gt q refl refl refl)) = refl
subeq⁻¹ (1>R2 (gt q refl refl refl)) = refl
subeq⁻¹ (1/\2 (disj q q₁ q₂ refl refl refl refl)) = refl
subeq⁻¹ (2/\1 (disj q q₁ q₂ refl refl refl refl)) = refl