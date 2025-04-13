{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module Equations where

open import Relation.Binary.PropositionalEquality hiding ([_]; _≗_) 
open import Data.Product
open import Data.Empty
open import Fma
open import SeqCalc
open import Cut
open import Interpolation

cut-cong1 : ∀ {T U A C} (p : Path T)
  → {f f' : U ⊢ A} 
  → (g : sub p (η A) ⊢ C)
  → (eq : f ≗ f')
  → cut p f g ≗ cut p f' g

cut⇒R-cong1 : ∀ {T U W A B C} (p : Path T)
  → {f f' : η A ⊛ U ⊢ B} (g : W ⊢ C)
  → (eq : W ≡ sub p (η (A ⇒ B)))
  → (eq' : f ≗ f')
  → cut⇒R p f g eq ≗ cut⇒R p f' g eq

cut⇐R-cong1 : ∀ {T U W A B C} (p : Path T)
  → {f f' : U ⊛ η A ⊢ B} (g : W ⊢ C)
  → (eq : W ≡ sub p (η (B ⇐ A)))
  → (eq' : f ≗ f')
  → cut⇐R p f g eq ≗ cut⇐R p f' g eq

cut⊗R-cong1 : ∀ {T U V W A B C} (p : Path T)
  → {f f' : U ⊢ A} {f₁ f₁' : V ⊢ B}
  → (g : W ⊢ C)
  → (eq : W ≡ sub p (η (A ⊗ B)))
  → (eq' : f ≗ f')
  → (eq'' : f₁ ≗ f₁')
  → cut⊗R p f f₁ g eq ≗ cut⊗R p f' f₁' g eq

cut-cong2 : ∀ {T U A C} (p : Path T)
  → (f : U ⊢ A) 
  → {g g' : sub p (η A) ⊢ C}
  → (eq : g ≗ g')
  → cut p f g ≗ cut p f g'

cut⇒R-cong2 : ∀ {T U W A B C} (p : Path T)
  → (f : η A ⊛ U ⊢ B) {g g' : W ⊢ C}
  → (eq : W ≡ sub p (η (A ⇒ B)))
  → (eq' : g ≗ g')
  → cut⇒R p f g eq ≗ cut⇒R p f g' eq

cut⇐R-cong2 : ∀ {T U W A B C} (p : Path T)
  → (f : U ⊛ η A ⊢ B) {g g' : W ⊢ C}
  → (eq : W ≡ sub p (η (B ⇐ A)))
  → (eq' : g ≗ g')
  → cut⇐R p f g eq ≗ cut⇐R p f g' eq

cut⊗R-cong2 : ∀ {T U V W A B C} (p : Path T)
  → (f : U ⊢ A) (f₁ : V ⊢ B)
  → {g g' : W ⊢ C}
  → (eq : W ≡ sub p (η (A ⊗ B)))
  → (eq' : g ≗ g')
  → cut⊗R p f f₁ g eq ≗ cut⊗R p f f₁ g' eq

cut-cong1 p g eq = {!   !}
cut⇒R-cong1 p g eq eq' = {!   !}
cut⇐R-cong1 p g eq eq' = {!   !}
cut⊗R-cong1 p g eq eq' eq'' = {!   !}

cut-cong2 p ax eq = eq
cut-cong2 p (⇒R f) eq = cut⇒R-cong2 p f refl eq
cut-cong2 p (⇐R f) eq = cut⇐R-cong2 p f refl eq
cut-cong2 p (⇒L p₁ f f₁) eq = ⇒L refl (cut-cong2 p f₁ eq)
cut-cong2 p (⇐L p₁ f f₁) eq = ⇐L refl (cut-cong2 p f₁ eq)
cut-cong2 p (⊗R f f₁) eq = cut⊗R-cong2 p f f₁ refl eq
cut-cong2 p (⊗L p₁ f) eq = ⊗L (cut-cong2 p f eq)

cut⇒R-cong2 p f eq refl = refl
cut⇒R-cong2 p f eq (~ eq') = ~ (cut⇒R-cong2 p f eq eq')
cut⇒R-cong2 p f eq (eq' ∘ eq'') = {!   !}
cut⇒R-cong2 p f refl (⇒R eq') = ⇒R (cut⇒R-cong2 (_ ▸ p) f refl eq')
cut⇒R-cong2 p f refl (⇐R eq') = ⇐R (cut⇒R-cong2 (p ◂ _) f refl eq')
cut⇒R-cong2 p f eq (⇒L eq' eq'') = {!   !}
cut⇒R-cong2 p f eq (⇐L eq' eq'') = {!   !}
cut⇒R-cong2 p f eq (⊗R eq' eq'') = {!   !}
cut⇒R-cong2 p f eq (⊗L eq') = {!   !}
cut⇒R-cong2 p f eq ⇒L⇒R = {!   !}
cut⇒R-cong2 p f eq ⇐L⇒R = {!   !}
cut⇒R-cong2 p f eq ⊗L⇒R = {!   !}
cut⇒R-cong2 p f eq ⇒L⇐R = {!   !}
cut⇒R-cong2 p f eq ⇐L⇐R = {!   !}
cut⇒R-cong2 p f eq ⊗L⇐R = {!   !}
cut⇒R-cong2 p f eq ⇒L⊗R₁ = {!   !}
cut⇒R-cong2 p f eq ⇒L⊗R₂ = {!   !}
cut⇒R-cong2 p f eq ⇐L⊗R₁ = {!   !}
cut⇒R-cong2 p f eq ⇐L⊗R₂ = {!   !}
cut⇒R-cong2 p f eq ⊗L⊗R₁ = {!   !}
cut⇒R-cong2 p f eq ⊗L⊗R₂ = {!   !}
cut⇒R-cong2 p f eq ⊗L⊗L = {!   !}
cut⇒R-cong2 p f eq ⊗L⇒L₁ = {!   !}
cut⇒R-cong2 p f eq ⊗L⇒L₂1/\2 = {!   !}
cut⇒R-cong2 p f eq ⊗L⇒L₂2/\1 = {!   !}
cut⇒R-cong2 p f eq ⊗L⇐L₁ = {!   !}
cut⇒R-cong2 p f eq ⊗L⇐L₂1/\2 = {!   !}
cut⇒R-cong2 p f eq (⊗L⇐L₂2/\1 {p = q} {q₁} {q₂}) = {!   !}
-- with subeq _ _ (q ++ (sub q₁ (η (_ ⇐ _) ⊛ _) ▸ q₂)) p eq | subeq _ _ (q ++ (q₁ ◂ sub q₂ (η (_ ⊗ _)))) p eq 
-- ... | 1/\2 (disj q₃ q₄ q₅ eqT₁ eqT₂ eqp₁ eqp₂) | 2>L1 (gt q₆ refl eqU refl) = {! eqU  !}
-- ... | 1/\2 x | 2>R1 x₁ = {!   !}
-- ... | 1/\2 x | 1/\2 x₁ = {!   !}
-- ... | 1/\2 x | 2/\1 x₁ = {!   !}
-- ... | 2/\1 x | 2>L1 x₁ = {!   !}
-- ... | 2/\1 x | 2>R1 x₁ = {!   !}
-- ... | 2/\1 x | 1/\2 x₁ = {!   !}
-- ... | 2/\1 (disj q₃ q₄ q₅ eqT₁ eqT₂ eqp₁ eqp₂) | 2/\1 (disj q₆ q₇ q₈ eqT₃ eqT₄ eqp₃ eqp₄) = {!   !}
cut⇒R-cong2 p f eq ⇒L⇒L = {!   !}
cut⇒R-cong2 p f eq ⇒L⇒L₂ = {!   !}
cut⇒R-cong2 p f eq ⇒L⇐L = {!   !}
cut⇒R-cong2 p f eq ⇒L⇐L₂ = {!   !}
cut⇒R-cong2 p f eq ⇐L⇒L = {!   !}
cut⇒R-cong2 p f eq ⇐L⇒L₂ = {!   !}
cut⇒R-cong2 p f eq ⇐L⇐L = {!   !}
cut⇒R-cong2 p f eq ⇐L⇐L₂ = {!   !}


cut⇐R-cong2 p f eq eq' = {!   !}

cut⊗R-cong2 p f f₁ eq eq' = {! f  !}

cut⇒R≗ : ∀ {T} (p : Path T) {U : Tree} {A C D : Fma}
  →  (h : U ⊢ D) (g : η A ⊛ sub p (η D) ⊢ C)
  → cut p h (⇒R g) ≗ ⇒R (cut (η A ▸ p) h g)
cut⇒R≗ p  ax g = refl
cut⇒R≗ p (⇒R h) g = refl
cut⇒R≗ p (⇐R h) g = refl
cut⇒R≗ p (⇒L p' h h') g = ⇒L refl (cut⇒R≗ p h' g) ∘ ⇒L⇒R
cut⇒R≗ p (⇐L p' h h') g = ⇐L refl (cut⇒R≗ p h' g) ∘ ⇐L⇒R
cut⇒R≗ p (⊗R h h') g = refl
cut⇒R≗ p (⊗L p' h) g = ⊗L (cut⇒R≗ p  h g) ∘ ⊗L⇒R

cut⇐R≗ : ∀ {T} (p : Path T) {U : Tree} {A C D : Fma}
  →  (h : U ⊢ D) (g : sub p (η D) ⊛ η A ⊢ C)
  → cut p h (⇐R g) ≗ ⇐R (cut (p ◂ η A) h g)
cut⇐R≗ p ax g = refl
cut⇐R≗ p (⇒R h) g = refl
cut⇐R≗ p (⇐R h) g = refl
cut⇐R≗ p (⇒L p' h h') g = ⇒L refl (cut⇐R≗ p h' g) ∘ ⇒L⇐R
cut⇐R≗ p (⇐L p' h h') g = ⇐L refl (cut⇐R≗ p h' g) ∘ ⇐L⇐R
cut⇐R≗ p (⊗R h h') g = refl
cut⇐R≗ p (⊗L p' h) g = ⊗L (cut⇐R≗ p h g) ∘ ⊗L⇐R

cut⊗R≗₁ : ∀ {T} (p : Path T) {U V : Tree} {A B D : Fma}
  →  (h : U ⊢ D) (g : sub p (η D) ⊢ A) (g' : V ⊢ B)
  → cut (p ◂ V) h (⊗R g g') ≗ ⊗R (cut p h g) g'
cut⊗R≗₁ p ax g g' = refl
cut⊗R≗₁ p (⇒R h) g g' = refl
cut⊗R≗₁ p (⇐R h) g g' = refl
cut⊗R≗₁ p (⇒L p' h h') g g' = ⇒L refl (cut⊗R≗₁ p h' g g') ∘ ⇒L⊗R₁
cut⊗R≗₁ p (⇐L p' h h') g g' = ⇐L refl (cut⊗R≗₁ p h' g g') ∘ ⇐L⊗R₁
cut⊗R≗₁ p (⊗R h h') g g' = refl
cut⊗R≗₁ p (⊗L p' h) g g' = ⊗L (cut⊗R≗₁ p h g g') ∘ ⊗L⊗R₁

cut⊗R≗₂ : ∀ {T} (p : Path T) {U V : Tree} {A B D : Fma}
  →  (h : U ⊢ D) (g : V ⊢ A) (g' : sub p (η D) ⊢ B)
  → cut (V ▸ p) h (⊗R g g') ≗ ⊗R g (cut p h g')
cut⊗R≗₂ p ax g g' = refl
cut⊗R≗₂ p (⇒R h) g g' = refl
cut⊗R≗₂ p (⇐R h) g g' = refl
cut⊗R≗₂ p (⇒L p' h h') g g' = ⇒L refl (cut⊗R≗₂ p h' g g') ∘ ⇒L⊗R₂
cut⊗R≗₂ p (⇐L p' h h') g g' = ⇐L refl (cut⊗R≗₂ p h' g g') ∘ ⇐L⊗R₂
cut⊗R≗₂ p (⊗R h h') g g' = refl
cut⊗R≗₂ p (⊗L p' h) g g' = ⊗L (cut⊗R≗₂ p h g g') ∘ ⊗L⊗R₂

cut⇒L≗ : ∀ {T} (p : Path T) {U : Tree} {A B C D : Fma}
  → {V : Tree} (q : Path V)
  → (f : sub p (η B) ⊢ C) (h : U ⊢ D) (g : sub q (η D) ⊢ A)
  → cut (p ++ (q ◂ η (A ⇒ B))) h (⇒L p g f)
  ≗
  ⇒L p (cut q h g) f
cut⇒L≗ f h g = {!   !}

cut⇐L≗ : ∀ {T} (p : Path T) {U : Tree} {A B C D : Fma}
  → {V : Tree} (q : Path V)
  → (f : sub p (η B) ⊢ C) (h : U ⊢ D) (g : sub q (η D) ⊢ A)
  → cut (p ++ (η (B ⇐ A) ▸ q)) h (⇐L p g f)
  ≗
  ⇐L p (cut q h g) f
cut⇐L≗ f h g = {!   !}

cut⇒L≗1/\2 : ∀ {T} (p : Path T) {U V : Tree} {A B C D : Fma} 
  → {W₁ W₂ : Tree} (p₁ : Path W₁) (p₂ : Path W₂)
  → (f : V ⊢ A) (h : U ⊢ D) (g : sub p (sub p₁ (η D) ⊛ sub p₂ (η B)) ⊢ C)
  → cut (p ++ (p₁ ◂ sub p₂ (V ⊛ η (A ⇒ B)))) h ((⇒L (p ++ (sub p₁ (η D) ▸ p₂)) f g))
    ≗
    ⇒L (p ++ (sub p₁ U ▸ p₂)) f (cut (p ++ (p₁ ◂ sub p₂ (η B))) h g)
cut⇒L≗1/\2 p p₁ p₂ f h g = {!   !}

cut⇒L≗2/\1 : ∀ {T} (p : Path T) {U V : Tree} {A B C D : Fma} 
  → {W₁ W₂ : Tree} (p₁ : Path W₁) (p₂ : Path W₂)
  → (f : V ⊢ A) (h : U ⊢ D) (g : sub p (sub p₁ (η B) ⊛ sub p₂ (η D)) ⊢ C)
  → cut (p ++ (sub p₁ (V ⊛ η (A ⇒ B)) ▸ p₂)) h ((⇒L (p ++ (p₁ ◂ sub p₂ (η D))) f g))
    ≗
    ⇒L (p ++ (p₁ ◂ sub p₂ U)) f (cut (p ++ (sub p₁ (η B) ▸ p₂)) h g)
cut⇒L≗2/\1 p p₁ p₂ f h g = {!   !}

cut⇐L≗1/\2 : ∀ {T} (p : Path T) {U V : Tree} {A B C D : Fma} 
  → {W₁ W₂ : Tree} (p₁ : Path W₁) (p₂ : Path W₂)
  → (f : V ⊢ A) (h : U ⊢ D) (g : sub p (sub p₁ (η D) ⊛ sub p₂ (η B)) ⊢ C)
  → cut (p ++ (p₁ ◂ sub p₂ (η (B ⇐ A) ⊛ V))) h ((⇐L (p ++ (sub p₁ (η D) ▸ p₂)) f g))
    ≗
    ⇐L (p ++ (sub p₁ U ▸ p₂)) f (cut (p ++ (p₁ ◂ sub p₂ (η B))) h g)
cut⇐L≗1/\2 p p₁ p₂ f h g = {!   !}


cut⇐L≗2/\1 : ∀ {T} (p : Path T) {U V : Tree} {A B C D : Fma} 
  → {W₁ W₂ : Tree} (p₁ : Path W₁) (p₂ : Path W₂)
  → (f : V ⊢ A) (h : U ⊢ D) (g : sub p (sub p₁ (η B) ⊛ sub p₂ (η D)) ⊢ C)
  → cut (p ++ (sub p₁ (η (B ⇐ A) ⊛ V) ▸ p₂)) h ((⇐L (p ++ (p₁ ◂ sub p₂ (η D))) f g))
    ≗
    ⇐L (p ++ (p₁ ◂ sub p₂ U)) f (cut (p ++ (sub p₁ (η B) ▸ p₂)) h g)
cut⇐L≗2/\1 p p₁ p₂ f h g = {!   !}


cut⊗L≗1/\2 : ∀ {T} (p : Path T) {U : Tree} {A B C D : Fma} 
  → {W₁ W₂ : Tree} (p₁ : Path W₁) (p₂ : Path W₂)
  → (h : U ⊢ D) (g : sub p (sub p₁ (η D) ⊛ (sub p₂ (η A ⊛ η B))) ⊢ C)
  → cut (p ++ (p₁ ◂ sub p₂ (η (A ⊗ B)))) h ((⊗L (p ++ (sub p₁ (η D) ▸ p₂)) g)) 
    ≗ 
    ⊗L (p ++ (sub p₁ U ▸ p₂)) (cut (p ++ (p₁ ◂ (sub p₂ (η A ⊛ η B)))) h g)
cut⊗L≗1/\2 p p₁ p₂ ax g = refl
cut⊗L≗1/\2 p p₁ p₂ (⇒R h) g = {!   !}
cut⊗L≗1/\2 p p₁ p₂ (⇐R h) g = {!   !}
cut⊗L≗1/\2 p p₁ p₂ (⇒L p₃ h h₁) g = {!   !}
cut⊗L≗1/\2 p p₁ p₂ (⇐L p₃ h h₁) g = {!   !}
cut⊗L≗1/\2 p p₁ p₂ (⊗R h h₁) g = {!   !}
cut⊗L≗1/\2 p p₁ p₂ (⊗L p₃ h) g = {!   !}

cut⊗L≗2/\1 : ∀ {T} (p : Path T) {U : Tree} {A B C D : Fma} 
  → {W₁ W₂ : Tree} (p₁ : Path W₁) (p₂ : Path W₂)
  → (h : U ⊢ D) (g : sub p ((sub p₁ (η A ⊛ η B)) ⊛ sub p₂ (η D)) ⊢ C)
  → cut (p ++ (sub p₁ (η (A ⊗ B)) ▸ p₂)) h ((⊗L (p ++ (p₁ ◂ sub p₂ (η D))) g)) 
    ≗ 
    ⊗L (p ++ (p₁ ◂ sub p₂ U)) (cut (p ++ (sub p₁ (η A ⊛ η B) ▸ p₂)) h g)
cut⊗L≗2/\1 p p₁ p₂ h g = {!   !}