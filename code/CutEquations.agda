{-# OPTIONS --rewriting #-}

module CutEquations where

open import Relation.Binary.PropositionalEquality hiding ([_]; _≗_) 
open import Data.Product
open import Data.Empty
open import Fma
open import SeqCalc
open import Cut
open import SubEqProperties

cutax-right : ∀ {X T}
  → (f : T ⊢ at X) 
  → cut ∙ f ax ≗ f
cutax-right ax = refl
cutax-right (⇒L p f f₁) = ⇒L refl (cutax-right f₁)
cutax-right (⇐L p f f₁) = ⇐L refl (cutax-right f₁)
cutax-right (⊗L p f) = ⊗L (cutax-right f)

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
cut⇒L≗ p q f ax g = refl
cut⇒L≗ p {A = A'} {B'} q f (⇒R {A = A} {B} h) g 
  rewrite subeq-2>L1 p (η (A' ⇒ B')) (η (A ⇒ B)) q = refl
cut⇒L≗ p {A = A'} {B'} q f (⇐R {A = A} {B} h) g 
  rewrite subeq-2>L1 p (η (A' ⇒ B')) (η (B ⇐ A)) q = refl
cut⇒L≗ p q f (⇒L p₁ h h₁) g = ⇒L refl (cut⇒L≗ p q f h₁ g) ∘ ⇒L⇒L
cut⇒L≗ p q f (⇐L p₁ h h₁) g = ⇐L refl (cut⇒L≗ p q f h₁ g) ∘ ⇐L⇒L
cut⇒L≗ p {A = A'} {B'} q f (⊗R {A = A} {B} h h₁) g 
  rewrite subeq-2>L1 p (η (A' ⇒ B')) (η (A ⊗ B)) q = refl
cut⇒L≗ p q f (⊗L p₁ h) g = ⊗L (cut⇒L≗ p q f h g) ∘ ⊗L⇒L₁

cut⇐L≗ : ∀ {T} (p : Path T) {U : Tree} {A B C D : Fma}
  → {V : Tree} (q : Path V)
  → (f : sub p (η B) ⊢ C) (h : U ⊢ D) (g : sub q (η D) ⊢ A)
  → cut (p ++ (η (B ⇐ A) ▸ q)) h (⇐L p g f)
  ≗
  ⇐L p (cut q h g) f
cut⇐L≗ p q f ax g = refl
cut⇐L≗ p {A = A'} {B'} q f (⇒R {A = A} {B} h) g 
  rewrite subeq-2>R1 p (η (B' ⇐ A')) (η (A ⇒ B)) q = refl
cut⇐L≗ p {A = A'} {B'} q f (⇐R {A = A} {B} h) g 
  rewrite subeq-2>R1 p (η (B' ⇐ A')) (η (B ⇐ A)) q = refl
cut⇐L≗ p q f (⇒L p₁ h h₁) g = ⇒L refl (cut⇐L≗ p q f h₁ g) ∘ ⇒L⇐L
cut⇐L≗ p q f (⇐L p₁ h h₁) g = ⇐L refl (cut⇐L≗ p q f h₁ g) ∘ ⇐L⇐L
cut⇐L≗ p {A = A'} {B'} q f (⊗R {A = A} {B} h h₁) g 
  rewrite subeq-2>R1 p (η (B' ⇐ A')) (η (A ⊗ B)) q = refl
cut⇐L≗ p q f (⊗L p₁ h) g = ⊗L (cut⇐L≗ p q f h g) ∘ ⊗L⇐L₁

cut⇒L≗1/\2 : ∀ {T} (p : Path T) {U V : Tree} {A B C D : Fma} 
  → {W₁ W₂ : Tree} (p₁ : Path W₁) (p₂ : Path W₂)
  → (f : V ⊢ A) (h : U ⊢ D) (g : sub p (sub p₁ (η D) ⊛ sub p₂ (η B)) ⊢ C)
  → cut (p ++ (p₁ ◂ sub p₂ (V ⊛ η (A ⇒ B)))) h ((⇒L (p ++ (sub p₁ (η D) ▸ p₂)) f g))
    ≗
    ⇒L (p ++ (sub p₁ U ▸ p₂)) f (cut (p ++ (p₁ ◂ sub p₂ (η B))) h g)
cut⇒L≗1/\2 p p₁ p₂ f ax g = refl
cut⇒L≗1/\2 p {V = V} {A'} {B'} p₁ p₂ f (⇒R {A = A} {B} h) g 
  rewrite subeq-2/\1 p (V ⊛ η (A' ⇒ B')) (η (A ⇒ B)) p₁ p₂ = refl
cut⇒L≗1/\2 p {V = V} {A'} {B'} p₁ p₂ f (⇐R {A = A} {B} h) g 
  rewrite subeq-2/\1 p (V ⊛ η (A' ⇒ B')) (η (B ⇐ A)) p₁ p₂ = refl
cut⇒L≗1/\2 p p₁ p₂ f (⇒L p₃ h h₁) g = ⇒L refl (cut⇒L≗1/\2 p p₁ p₂ f h₁ g) ∘ ⇒L⇒L₂ {p = p}
cut⇒L≗1/\2 p p₁ p₂ f (⇐L p₃ h h₁) g = ⇐L refl (cut⇒L≗1/\2 p p₁ p₂ f h₁ g) ∘ ⇐L⇒L₂ {p = p}
cut⇒L≗1/\2 p {V = V} {A'} {B'} p₁ p₂ f (⊗R {A = A} {B} h h₁) g 
  rewrite subeq-2/\1 p (V ⊛ η (A' ⇒ B')) (η (A ⊗ B)) p₁ p₂ = refl
cut⇒L≗1/\2 p p₁ p₂ f (⊗L p₃ h) g = ⊗L (cut⇒L≗1/\2 p p₁ p₂ f h g) ∘ ⊗L⇒L₂1/\2 {p = p}

cut⇒L≗2/\1 : ∀ {T} (p : Path T) {U V : Tree} {A B C D : Fma} 
  → {W₁ W₂ : Tree} (p₁ : Path W₁) (p₂ : Path W₂)
  → (f : V ⊢ A) (h : U ⊢ D) (g : sub p (sub p₁ (η B) ⊛ sub p₂ (η D)) ⊢ C)
  → cut (p ++ (sub p₁ (V ⊛ η (A ⇒ B)) ▸ p₂)) h ((⇒L (p ++ (p₁ ◂ sub p₂ (η D))) f g))
    ≗
    ⇒L (p ++ (p₁ ◂ sub p₂ U)) f (cut (p ++ (sub p₁ (η B) ▸ p₂)) h g)
cut⇒L≗2/\1 p p₁ p₂ f ax g = refl
cut⇒L≗2/\1 p {V = V} {A'} {B'} p₁ p₂ f (⇒R {A = A} {B} h) g 
  rewrite subeq-1/\2 p (V ⊛ η (A' ⇒ B')) (η (A ⇒ B)) p₁ p₂ = refl
cut⇒L≗2/\1 p {V = V} {A'} {B'} p₁ p₂ f (⇐R {A = A} {B} h) g 
  rewrite subeq-1/\2 p (V ⊛ η (A' ⇒ B')) (η (B ⇐ A)) p₁ p₂ = refl
cut⇒L≗2/\1 p p₁ p₂ f (⇒L p₃ h h₁) g = ⇒L refl (cut⇒L≗2/\1 p p₁ p₂ f h₁ g) ∘ (~ ⇒L⇒L₂ {p = p})
cut⇒L≗2/\1 p p₁ p₂ f (⇐L p₃ h h₁) g = ⇐L refl (cut⇒L≗2/\1 p p₁ p₂ f h₁ g) ∘ (~ ⇒L⇐L₂ {p = p})
cut⇒L≗2/\1 p {V = V} {A'} {B'} p₁ p₂ f (⊗R {A = A} {B} h h₁) g 
  rewrite subeq-1/\2 p (V ⊛ η (A' ⇒ B')) (η (A ⊗ B)) p₁ p₂ = refl
cut⇒L≗2/\1 p p₁ p₂ f (⊗L p₃ h) g = ⊗L (cut⇒L≗2/\1 p p₁ p₂ f h g) ∘ ⊗L⇒L₂2/\1 {p = p}

cut⇐L≗1/\2 : ∀ {T} (p : Path T) {U V : Tree} {A B C D : Fma} 
  → {W₁ W₂ : Tree} (p₁ : Path W₁) (p₂ : Path W₂)
  → (f : V ⊢ A) (h : U ⊢ D) (g : sub p (sub p₁ (η D) ⊛ sub p₂ (η B)) ⊢ C)
  → cut (p ++ (p₁ ◂ sub p₂ (η (B ⇐ A) ⊛ V))) h ((⇐L (p ++ (sub p₁ (η D) ▸ p₂)) f g))
    ≗
    ⇐L (p ++ (sub p₁ U ▸ p₂)) f (cut (p ++ (p₁ ◂ sub p₂ (η B))) h g)
cut⇐L≗1/\2 p p₁ p₂ f ax g = refl
cut⇐L≗1/\2 p {V = V} {A'} {B'} p₁ p₂ f (⇒R {A = A} {B} h) g 
  rewrite subeq-2/\1 p (η (B' ⇐ A') ⊛ V) (η (A ⇒ B)) p₁ p₂ = refl
cut⇐L≗1/\2 p {V = V} {A'} {B'} p₁ p₂ f (⇐R {A = A} {B} h) g 
  rewrite subeq-2/\1 p (η (B' ⇐ A') ⊛ V) (η (B ⇐ A)) p₁ p₂ = refl
cut⇐L≗1/\2 p p₁ p₂ f (⇒L p₃ h h₁) g = ⇒L refl (cut⇐L≗1/\2 p p₁ p₂ f h₁ g) ∘ ⇒L⇐L₂ {p = p}
cut⇐L≗1/\2 p p₁ p₂ f (⇐L p₃ h h₁) g = ⇐L refl (cut⇐L≗1/\2 p p₁ p₂ f h₁ g) ∘ ⇐L⇐L₂ {p = p}
cut⇐L≗1/\2 p {V = V} {A'} {B'} p₁ p₂ f (⊗R {A = A} {B} h h₁) g 
  rewrite subeq-2/\1 p (η (B' ⇐ A') ⊛ V) (η (A ⊗ B)) p₁ p₂ = refl
cut⇐L≗1/\2 p p₁ p₂ f (⊗L p₃ h) g = ⊗L (cut⇐L≗1/\2 p p₁ p₂ f h g) ∘ ⊗L⇐L₂1/\2 {p = p}

cut⇐L≗2/\1 : ∀ {T} (p : Path T) {U V : Tree} {A B C D : Fma} 
  → {W₁ W₂ : Tree} (p₁ : Path W₁) (p₂ : Path W₂)
  → (f : V ⊢ A) (h : U ⊢ D) (g : sub p (sub p₁ (η B) ⊛ sub p₂ (η D)) ⊢ C)
  → cut (p ++ (sub p₁ (η (B ⇐ A) ⊛ V) ▸ p₂)) h ((⇐L (p ++ (p₁ ◂ sub p₂ (η D))) f g))
    ≗
    ⇐L (p ++ (p₁ ◂ sub p₂ U)) f (cut (p ++ (sub p₁ (η B) ▸ p₂)) h g)
cut⇐L≗2/\1 p p₁ p₂ f ax g = refl
cut⇐L≗2/\1 p {V = V} {A'} {B'} p₁ p₂ f (⇒R {A = A} {B} h) g 
  rewrite subeq-1/\2 p (η (B' ⇐ A') ⊛ V) (η (A ⇒ B)) p₁ p₂ = refl
cut⇐L≗2/\1 p {V = V} {A'} {B'} p₁ p₂ f (⇐R {A = A} {B} h) g 
  rewrite subeq-1/\2 p (η (B' ⇐ A') ⊛ V) (η (B ⇐ A)) p₁ p₂ = refl
cut⇐L≗2/\1 p p₁ p₂ f (⇒L p₃ h h₁) g = ⇒L refl (cut⇐L≗2/\1 p p₁ p₂ f h₁ g) ∘ (~ ⇐L⇒L₂ {p = p})
cut⇐L≗2/\1 p p₁ p₂ f (⇐L p₃ h h₁) g = ⇐L refl (cut⇐L≗2/\1 p p₁ p₂ f h₁ g) ∘ (~ ⇐L⇐L₂ {p = p})
cut⇐L≗2/\1 p {V = V} {A'} {B'} p₁ p₂ f (⊗R {A = A} {B} h h₁) g 
  rewrite subeq-1/\2 p (η (B' ⇐ A') ⊛ V) (η (A ⊗ B)) p₁ p₂ = refl
cut⇐L≗2/\1 p p₁ p₂ f (⊗L p₃ h) g = ⊗L (cut⇐L≗2/\1 p p₁ p₂ f h g) ∘ ⊗L⇐L₂2/\1 {p = p}

cut⊗L≗1/\2 : ∀ {T} (p : Path T) {U : Tree} {A B C D : Fma} 
  → {W₁ W₂ : Tree} (p₁ : Path W₁) (p₂ : Path W₂)
  → (h : U ⊢ D) (g : sub p (sub p₁ (η D) ⊛ (sub p₂ (η A ⊛ η B))) ⊢ C)
  → cut (p ++ (p₁ ◂ sub p₂ (η (A ⊗ B)))) h ((⊗L (p ++ (sub p₁ (η D) ▸ p₂)) g)) 
    ≗ 
    ⊗L (p ++ (sub p₁ U ▸ p₂)) (cut (p ++ (p₁ ◂ (sub p₂ (η A ⊛ η B)))) h g)
cut⊗L≗1/\2 p p₁ p₂ ax g = refl
cut⊗L≗1/\2 p {A = A'} {B'} p₁ p₂ (⇒R {A = A} {B} h) g 
  rewrite subeq-2/\1 p (η (A' ⊗ B')) (η (A ⇒ B)) p₁ p₂ = refl
cut⊗L≗1/\2 p {A = A'} {B'} p₁ p₂ (⇐R {A = A} {B} h) g 
  rewrite subeq-2/\1 p (η (A' ⊗ B')) (η (B ⇐ A)) p₁ p₂ = refl
cut⊗L≗1/\2 p p₁ p₂ (⇒L p₃ h h₁) g = ⇒L refl (cut⊗L≗1/\2 p p₁ p₂ h₁ g) ∘ (~ ⊗L⇒L₂2/\1 {p = p})
cut⊗L≗1/\2 p p₁ p₂ (⇐L p₃ h h₁) g = ⇐L refl (cut⊗L≗1/\2 p p₁ p₂ h₁ g) ∘ (~ ⊗L⇐L₂2/\1 {p = p})
cut⊗L≗1/\2 p {A = A'} {B'} p₁ p₂ (⊗R {A = A} {B} h h₁) g 
  rewrite subeq-2/\1 p (η (A' ⊗ B')) (η (A ⊗ B)) p₁ p₂ = refl
cut⊗L≗1/\2 p p₁ p₂ (⊗L p₃ h) g = ⊗L (cut⊗L≗1/\2 p p₁ p₂ h g) ∘ (~ ⊗L⊗L {p = p})

cut⊗L≗2/\1 : ∀ {T} (p : Path T) {U : Tree} {A B C D : Fma} 
  → {W₁ W₂ : Tree} (p₁ : Path W₁) (p₂ : Path W₂)
  → (h : U ⊢ D) (g : sub p ((sub p₁ (η A ⊛ η B)) ⊛ sub p₂ (η D)) ⊢ C)
  → cut (p ++ (sub p₁ (η (A ⊗ B)) ▸ p₂)) h ((⊗L (p ++ (p₁ ◂ sub p₂ (η D))) g)) 
    ≗ 
    ⊗L (p ++ (p₁ ◂ sub p₂ U)) (cut (p ++ (sub p₁ (η A ⊛ η B) ▸ p₂)) h g)
cut⊗L≗2/\1 p p₁ p₂ ax g = refl
cut⊗L≗2/\1 p {A = A'} {B'} p₁ p₂ (⇒R {A = A} {B} h) g 
  rewrite subeq-1/\2 p (η (A' ⊗ B')) (η (A ⇒ B)) p₁ p₂ = refl
cut⊗L≗2/\1 p {A = A'} {B'} p₁ p₂ (⇐R {A = A} {B} h) g 
  rewrite subeq-1/\2 p (η (A' ⊗ B')) (η (B ⇐ A)) p₁ p₂ = refl
cut⊗L≗2/\1 p p₁ p₂ (⇒L p₃ h h₁) g = ⇒L refl (cut⊗L≗2/\1 p p₁ p₂ h₁ g) ∘ (~ ⊗L⇒L₂1/\2 {p = p})
cut⊗L≗2/\1 p p₁ p₂ (⇐L p₃ h h₁) g = ⇐L refl (cut⊗L≗2/\1 p p₁ p₂ h₁ g) ∘ (~ ⊗L⇐L₂1/\2 {p = p})
cut⊗L≗2/\1 p {A = A'} {B'} p₁ p₂ (⊗R {A = A} {B} h h₁) g 
  rewrite subeq-1/\2 p (η (A' ⊗ B')) (η (A ⊗ B)) p₁ p₂ = refl
cut⊗L≗2/\1 p p₁ p₂ (⊗L p₃ h) g = ⊗L (cut⊗L≗2/\1 p p₁ p₂ h g) ∘ (⊗L⊗L {p = p})
