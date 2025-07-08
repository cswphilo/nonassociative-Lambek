{-# OPTIONS --rewriting #-}

module subeq-1 where

open import Fma

subeq-1 : ∀ {T₁ T₂ U₁ U₂} {p₁ : Path T₁} {p₂ : Path T₂}
  → SubEqCases p₁ p₂ U₁ U₂
  → sub p₁ U₁ ≡ sub p₂ U₂
subeq-1 (1≡2 (same refl refl refl)) = refl
subeq-1 (2>L1 (gt q refl refl refl)) = refl
subeq-1 (2>R1 (gt q refl refl refl)) = refl
subeq-1 (1>L2 (gt q refl refl refl)) = refl
subeq-1 (1>R2 (gt q refl refl refl)) = refl
subeq-1 (1/\2 (disj q q₁ q₂ refl refl refl refl)) = refl
subeq-1 (2/\1 (disj q q₁ q₂ refl refl refl refl)) = refl