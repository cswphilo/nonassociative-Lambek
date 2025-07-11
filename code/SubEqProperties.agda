{-# OPTIONS --rewriting #-}

module SubEqProperties where

open import Fma

-- Some lemmata about SubEq

sub≡ : ∀ {T U V} (p : Path T) → sub p U ≡ sub p V → U ≡ V
sub≡ ∙ refl = refl
sub≡ (p ◂ U) eq = sub≡ p (⊛eq eq .proj₁)
sub≡ (T ▸ p) eq = sub≡ p (⊛eq eq .proj₂)

subeq-1≡2 : ∀ {T} (p : Path T) (U : Tree)
  → subeq U U p p refl ≡ 1≡2 (same refl refl refl)
subeq-1≡2 ∙ U = refl
subeq-1≡2 (p ◂ V) U rewrite subeq-1≡2 p U = refl
subeq-1≡2 (T ▸ p) U rewrite subeq-1≡2 p U = refl

subeq-1/\2 : ∀ {T} (p : Path T) (U V : Tree) 
  → {W₁ W₂ : Tree} (p₁ : Path W₁) (p₂ : Path W₂) 
  → subeq U V (p ++ (p₁ ◂ sub p₂ V)) (p ++ (sub p₁ U ▸ p₂)) refl ≡ 1/\2 (disj p p₁ p₂ refl refl refl refl)
subeq-1/\2 ∙ U V p₁ p₂ = refl
subeq-1/\2 (p ◂ U₁) U V p₁ p₂ rewrite subeq-1/\2 p U V p₁ p₂ = refl
subeq-1/\2 (T ▸ p) U V p₁ p₂ rewrite subeq-1/\2 p U V p₁ p₂ = refl

subeq-2/\1 : ∀ {T} (p : Path T) (U V : Tree) 
  → {W₁ W₂ : Tree} (p₁ : Path W₁) (p₂ : Path W₂) 
  → subeq U V (p ++ (sub p₁ V ▸ p₂)) (p ++ (p₁ ◂ sub p₂ U)) refl ≡ 2/\1 (disj p p₁ p₂ refl refl refl refl)
subeq-2/\1 ∙ U V p₁ p₂ = refl
subeq-2/\1 (p ◂ U₁) U V p₁ p₂ rewrite subeq-2/\1 p U V p₁ p₂ = refl
subeq-2/\1 (T ▸ p) U V p₁ p₂ rewrite subeq-2/\1 p U V p₁ p₂ = refl

subeq-2>R1 : ∀ {T} (p : Path T) (W₁ : Tree) {W₂ : Tree} (U : Tree)
  → (q : Path W₂)
  → subeq (W₁ ⊛ sub q U) U p (p ++ (W₁ ▸ q)) refl ≡ 2>R1 (gt q refl refl refl)
subeq-2>R1 ∙ W₁ U q = refl
subeq-2>R1 (p ◂ U₁) W₁ U q rewrite subeq-2>R1 p W₁ U q = refl
subeq-2>R1 (T ▸ p) W₁ U q rewrite subeq-2>R1 p W₁ U q = refl

subeq-2>L1 : ∀ {T} (p : Path T) {W₁ : Tree} (W₂ : Tree) (U : Tree)
  → (q : Path W₁)
  → subeq (sub q U ⊛ W₂) U p (p ++ (q ◂ W₂)) refl ≡ 2>L1 (gt q refl refl refl)
subeq-2>L1 ∙ W₁ U q = refl
subeq-2>L1 (p ◂ U₁) W₁ U q rewrite subeq-2>L1 p W₁ U q = refl
subeq-2>L1 (T ▸ p) W₁ U q rewrite subeq-2>L1 p W₁ U q = refl

subeq-1>R2 : ∀ {T} (p : Path T) (W₁ : Tree) {W₂ : Tree} (U : Tree)
  → (q : Path W₂)
  → subeq U (W₁ ⊛ sub q U) (p ++ (W₁ ▸ q)) p refl ≡ 1>R2 (gt q refl refl refl)
subeq-1>R2 ∙ W₁ U q = refl
subeq-1>R2 (p ◂ U₁) W₁ U q rewrite subeq-1>R2 p W₁ U q = refl
subeq-1>R2 (T ▸ p) W₁ U q rewrite subeq-1>R2 p W₁ U q = refl

subeq-1>L2 : ∀ {T} (p : Path T) {W₁ : Tree} (W₂ : Tree) (U : Tree)
  → (q : Path W₁)
  → subeq U (sub q U ⊛ W₂) (p ++ (q ◂ W₂)) p refl ≡ 1>L2 (gt q refl refl refl)
subeq-1>L2 ∙ W₁ U q = refl
subeq-1>L2 (p ◂ U₁) W₁ U q rewrite subeq-1>L2 p W₁ U q = refl
subeq-1>L2 (T ▸ p) W₁ U q rewrite subeq-1>L2 p W₁ U q = refl

