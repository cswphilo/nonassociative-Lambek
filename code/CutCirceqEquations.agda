{-# OPTIONS --rewriting #-}

module CutCirceqEquations where

open import Relation.Binary.PropositionalEquality hiding ([_]; _≗_) 
open import Data.Product
open import Data.Empty
open import Fma
open import SeqCalc
open import Cut
open import SubEqProperties

{-
Equivalences of derivations on the permuation of Cut and Left rules 
-}

cut⇒L≗ : ∀ {T U V W A B C D} (p : Path T) (q : Path U)
  → {f : V ⊢ A}
  → (h : sub q (η B) ⊢ D)
  → (g : W ⊢ C)
  → (eq : W ≡ sub p (η D))
  → cut p (⇒L q f h) (subst-cxt eq g) refl ≗ ⇒L (p ++ q) f (cut p h (subst-cxt eq g) refl)
cut⇒L≗ p q h (⇒R g) refl = ⇒R (cut⇒L≗ (_ ▸ p) q h g refl) ∘ (~ ⇒L⇒R)
cut⇒L≗ p q h (⇐R g) refl = ⇐R (cut⇒L≗ (p ◂ _) q h g refl) ∘ (~ ⇒L⇐R)
cut⇒L≗ {D = D} p q h (⇒L {U = U} {A} {B} p₁ g g₁) eq with subeq (U ⊛ η (A ⇒ B)) (η D) p₁ p eq
cut⇒L≗ {D = D} p q h (⇒L {U = U} {A} {B} p₁ g g₁) refl | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η D) q₁ = ⇒L (cut⇒L≗ q₁ q h g refl) refl ∘ (~ ⇒L⇒L)
cut⇒L≗ {D = D} p q h (⇒L {U = U} {A} {B} p₁ g g₁) refl | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 p₁ U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p₁ U (η (A ⇒ B)) ∙ = refl
cut⇒L≗ {D = D} p q h (⇒L {U = U} {A} {B} p₁ g g₁) refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 q₁ (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ = ⇒L refl (cut⇒L≗ (q₁ ++ (sub q₂ (η B) ▸ q₃)) q h g₁ refl) ∘ (⇒L⇒L₂ {p = q₁})
cut⇒L≗ {D = D} p q h (⇒L {U = U} {A} {B} p₁ g g₁) refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ = ⇒L refl (cut⇒L≗ (q₁ ++ (q₂ ◂ sub q₃ (η B))) q h g₁ refl) ∘ (~ ⇒L⇒L₂ {p = q₁})
cut⇒L≗ {D = D} p q h (⇐L {U = U} {A} {B} p₁ g g₁) eq with subeq (η (B ⇐ A) ⊛ U) (η D) p₁ p eq
cut⇒L≗ {D = D} p q h (⇐L {U = U} {A} {B} p₁ g g₁) refl | 2>L1 (gt ∙ refl refl refl)
  rewrite subeq-2>L1 p₁ U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p₁ U (η (B ⇐ A)) ∙ = refl
cut⇒L≗ {D = D} p q h (⇐L {U = U} {A} {B} p₁ g g₁) refl | 2>R1 (gt q₁ refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η D) q₁ = ⇐L (cut⇒L≗ q₁ q h g refl) refl ∘ (~ ⇒L⇐L)
cut⇒L≗ {D = D} p q h (⇐L {U = U} {A} {B} p₁ g g₁) refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ = ⇐L refl (cut⇒L≗ (q₁ ++ (sub q₂ (η B) ▸ q₃)) q h g₁ refl) ∘ (⇐L⇒L₂ {p = q₁})
cut⇒L≗ {D = D} p q h (⇐L {U = U} {A} {B} p₁ g g₁) refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ = ⇐L refl (cut⇒L≗ (q₁ ++ (q₂ ◂ sub q₃ (η B))) q h g₁ refl) ∘ (~ ⇒L⇐L₂ {p = q₁})
cut⇒L≗ (p ◂ U) q h (⊗R g g₁) refl = ⊗R (cut⇒L≗ p q h g refl) refl ∘ (~ ⇒L⊗R₁)
cut⇒L≗ (T ▸ p) q h (⊗R g g₁) refl = ⊗R refl (cut⇒L≗ p q h g₁ refl) ∘ (~ ⇒L⊗R₂)
cut⇒L≗ {D = D} p q h (⊗L {A = A} {B} p₁ g) eq with subeq (η (A ⊗ B)) (η D) p₁ p eq
cut⇒L≗ {D = D} p q h (⊗L {A = A} {B} p₁ g) refl | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = refl
cut⇒L≗ {D = D} p q h (⊗L {A = A} {B} p₁ g) refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (A ⊗ B)) (η D) q₂ q₃ = ⊗L (cut⇒L≗ (q₁ ++ (sub q₂ (η A ⊛ η B) ▸ q₃)) q h g refl) ∘ (⊗L⇒L₂1/\2 {p = q₁})
cut⇒L≗ {D = D} p q h (⊗L {A = A} {B} p₁ g) refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (A ⊗ B)) (η D) q₂ q₃ = ⊗L (cut⇒L≗ (q₁ ++ (q₂ ◂ sub q₃ (η A ⊛ η B))) q h g refl) ∘ (⊗L⇒L₂2/\1 {p = q₁})
cut⇒L≗ ∙ q h ax refl = refl

cut⇐L≗ : ∀ {T U V W A B C D} (p : Path T) (q : Path U)
  → {f : V ⊢ A}
  → (h : sub q (η B) ⊢ D)
  → (g : W ⊢ C)
  → (eq : W ≡ sub p (η D))
  → cut p (⇐L q f h) (subst-cxt eq g) refl ≗ ⇐L (p ++ q) f (cut p h (subst-cxt eq g) refl)
cut⇐L≗ p q h (⇒R g) refl = ⇒R (cut⇐L≗ (_ ▸ p) q h g refl) ∘ (~ ⇐L⇒R)
cut⇐L≗ p q h (⇐R g) refl = ⇐R (cut⇐L≗ (p ◂ _) q h g refl) ∘ (~ ⇐L⇐R)
cut⇐L≗ {D = D} p q h (⇒L {U = U} {A} {B} p₁ g g₁) eq with subeq (U ⊛ η (A ⇒ B)) (η D) p₁ p eq
cut⇐L≗ {D = D} p q h (⇒L {U = U} {A} {B} p₁ g g₁) refl | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η D) q₁ = ⇒L (cut⇐L≗ q₁ q h g refl) refl ∘ (~ ⇐L⇒L) 
cut⇐L≗ {D = D} p q h (⇒L {U = U} {A} {B} p₁ g g₁) refl | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 p₁ U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p₁ U (η (A ⇒ B)) ∙ = refl
cut⇐L≗ {D = D} p q h (⇒L {U = U} {A} {B} p₁ g g₁) refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 q₁ (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ = ⇒L refl (cut⇐L≗ (q₁ ++ (sub q₂ (η B) ▸ q₃)) q h g₁ refl) ∘ (⇒L⇐L₂ {p = q₁}) 
cut⇐L≗ {D = D} p q h (⇒L {U = U} {A} {B} p₁ g g₁) refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ = ⇒L refl (cut⇐L≗ (q₁ ++ (q₂ ◂ sub q₃ (η B))) q h g₁ refl) ∘ (~ ⇐L⇒L₂ {p = q₁})
cut⇐L≗ {D = D} p q h (⇐L {U = U} {A} {B} p₁ g g₁) eq with subeq (η (B ⇐ A) ⊛ U) (η D) p₁ p eq
cut⇐L≗ {D = D} p q h (⇐L {U = U} {A} {B} p₁ g g₁) refl | 2>L1 (gt ∙ refl refl refl)
  rewrite subeq-2>L1 p₁ U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p₁ U (η (B ⇐ A)) ∙ = refl
cut⇐L≗ {D = D} p q h (⇐L {U = U} {A} {B} p₁ g g₁) refl | 2>R1 (gt q₁ refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η D) q₁ = ⇐L (cut⇐L≗ q₁ q h g refl) refl ∘ (~ ⇐L⇐L) 
cut⇐L≗ {D = D} p q h (⇐L {U = U} {A} {B} p₁ g g₁) refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ = ⇐L refl (cut⇐L≗ (q₁ ++ (sub q₂ (η B) ▸ q₃)) q h g₁ refl) ∘ (⇐L⇐L₂ {p = q₁})
cut⇐L≗ {D = D} p q h (⇐L {U = U} {A} {B} p₁ g g₁) refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ = ⇐L refl (cut⇐L≗ (q₁ ++ (q₂ ◂ sub q₃ (η B))) q h g₁ refl) ∘ (~ ⇐L⇐L₂ {p = q₁})
cut⇐L≗ (p ◂ U) q h (⊗R g g₁) refl = ⊗R (cut⇐L≗ p q h g refl) refl ∘ (~ ⇐L⊗R₁)
cut⇐L≗ (T ▸ p) q h (⊗R g g₁) refl = ⊗R refl (cut⇐L≗ p q h g₁ refl) ∘ (~ ⇐L⊗R₂)
cut⇐L≗ {D = D} p q h (⊗L {A = A} {B} p₁ g) eq with subeq (η (A ⊗ B)) (η D) p₁ p eq
cut⇐L≗ {D = D} p q h (⊗L {A = A} {B} p₁ g) refl | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = refl
cut⇐L≗ {D = D} p q h (⊗L {A = A} {B} p₁ g) refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (A ⊗ B)) (η D) q₂ q₃ = ⊗L (cut⇐L≗ (q₁ ++ (sub q₂ (η A ⊛ η B) ▸ q₃)) q h g refl) ∘ (⊗L⇐L₂1/\2 {p = q₁}) 
cut⇐L≗ {D = D} p q h (⊗L {A = A} {B} p₁ g) refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (A ⊗ B)) (η D) q₂ q₃ = ⊗L (cut⇐L≗ (q₁ ++ (q₂ ◂ sub q₃ (η A ⊛ η B))) q h g refl) ∘ (⊗L⇐L₂2/\1 {p = q₁})
cut⇐L≗ ∙ q h ax refl = refl


cut⊗L≗ : ∀ {T U W A B C D} (p : Path T) (q : Path U)
  → (h : sub q (η A ⊛ η B) ⊢ D)
  → (g : W ⊢ C)
  → (eq : W ≡ sub p (η D))
  → cut p (⊗L q h) (subst-cxt eq g) refl ≗ ⊗L (p ++ q) (cut p h (subst-cxt eq g) refl)
cut⊗L≗ p q h (⇒R g) refl = ⇒R (cut⊗L≗ (η _ ▸ p) q h g refl) ∘ (~ ⊗L⇒R)
cut⊗L≗ p q h (⇐R g) refl = ⇐R (cut⊗L≗ (p ◂ η _) q h g refl) ∘ (~ ⊗L⇐R)
cut⊗L≗ {D = D} p q h (⇒L {U = U} {A} {B} p₁ g g₁) eq with subeq (U ⊛ η (A ⇒ B)) (η D) p₁ p eq
cut⊗L≗ {D = D} p q h (⇒L {U = U} {A} {B} p₁ g g₁) refl | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η D) q₁ = ⇒L (cut⊗L≗ q₁ q h g refl) refl ∘ (~ ⊗L⇒L₁)
cut⊗L≗ {D = D} p q h (⇒L {U = U} {A} {B} p₁ g g₁) refl | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 p₁ U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p₁ U (η (A ⇒ B)) ∙ = refl
cut⊗L≗ {D = D} p q h (⇒L {U = U} {A} {B} p₁ g g₁) refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ = ⇒L refl (cut⊗L≗ (q₁ ++ (sub q₂ (η B) ▸ q₃)) q h g₁ refl) ∘ (~ ⊗L⇒L₂2/\1 {p = q₁})
cut⊗L≗ {D = D} p q h (⇒L {U = U} {A} {B} p₁ g g₁) refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ = ⇒L refl (cut⊗L≗ (q₁ ++ (q₂ ◂ sub q₃ (η B))) q h g₁ refl) ∘ (~ ⊗L⇒L₂1/\2 {p = q₁})
cut⊗L≗ {D = D} p q h (⇐L {U = U} {A} {B} p₁ g g₁) eq with subeq (η (B ⇐ A) ⊛ U) (η D) p₁ p eq
cut⊗L≗ {D = D} p q h (⇐L {U = U} {A} {B} p₁ g g₁) refl | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 p₁ U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p₁ U (η (B ⇐ A)) ∙ = refl
cut⊗L≗ {D = D} p q h (⇐L {U = U} {A} {B} p₁ g g₁) refl | 2>R1 (gt q₁ refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η D) q₁ = ⇐L (cut⊗L≗ q₁ q h g refl) refl ∘ (~ ⊗L⇐L₁)
cut⊗L≗ {D = D} p q h (⇐L {U = U} {A} {B} p₁ g g₁) refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ = ⇐L refl (cut⊗L≗ (q₁ ++ (sub q₂ (η B) ▸ q₃)) q h g₁ refl) ∘ (~ ⊗L⇐L₂2/\1 {p = q₁})
cut⊗L≗ {D = D} p q h (⇐L {U = U} {A} {B} p₁ g g₁) refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ = ⇐L refl (cut⊗L≗ (q₁ ++ (q₂ ◂ sub q₃ (η B))) q h g₁ refl) ∘ (~ ⊗L⇐L₂1/\2 {p = q₁})
cut⊗L≗ (p ◂ U) q h (⊗R g g₁) refl = ⊗R (cut⊗L≗ p q h g refl) refl ∘ (~ ⊗L⊗R₁)
cut⊗L≗ (T ▸ p) q h (⊗R g g₁) refl = ⊗R refl (cut⊗L≗ p q h g₁ refl) ∘ (~ ⊗L⊗R₂)
cut⊗L≗ {D = D} p q h (⊗L {A = A} {B} p₁ g) eq with subeq (η (A ⊗ B)) (η D) p₁ p eq
cut⊗L≗ {D = .(A ⊗ B)} p q h (⊗L {A = A} {B} .p g) refl | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = refl
cut⊗L≗ {D = D} ._ q h (⊗L {A = A} {B} ._ g) refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (A ⊗ B)) (η D) q₂ q₃ = ⊗L (cut⊗L≗ (q₁ ++ (sub q₂ (η A ⊛ η B) ▸ q₃)) q h g refl) ∘ (~ ⊗L⊗L {p = q₁})
cut⊗L≗ {D = D} ._ q h (⊗L {A = A} {B} ._ g) refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (A ⊗ B)) (η D) q₂ q₃ = ⊗L (cut⊗L≗ (q₁ ++ (q₂ ◂ sub q₃ (η A ⊛ η B))) q h g refl) ∘ (⊗L⊗L {p = q₁})
cut⊗L≗ ∙ q h ax refl = refl

cut⇒L⇒R : ∀ {T U V A B A' B'} (p : Path T)
  → (f : U ⊢ (A ⇒ B)) {g : V ⊢ A} 
  → {h : (η A' ⊛ sub p (η B)) ⊢ B'}
  → cut⇒L p f g (⇒R h) ≗ ⇒R (cut⇒L (η A' ▸ p) f g h)
cut⇒L⇒R p (⇒R f) = refl
cut⇒L⇒R p (⇒L p₁ f f₁) = ⇒L refl (cut⇒L⇒R p f₁) ∘ ⇒L⇒R
cut⇒L⇒R p (⇐L p₁ f f₁) = ⇐L refl (cut⇒L⇒R p f₁) ∘ ⇐L⇒R
cut⇒L⇒R p (⊗L p₁ f) = ⊗L (cut⇒L⇒R p f) ∘ ⊗L⇒R

cut⇒L⇐R : ∀ {T U V A B A' B'} (p : Path T)
  → (f : U ⊢ (A ⇒ B)) {g : V ⊢ A} 
  → {h : (sub p (η B) ⊛ η A') ⊢ B'}
  → cut⇒L p f g (⇐R h) ≗ ⇐R (cut⇒L (p ◂ η A') f g h)
cut⇒L⇐R p (⇒R f) = refl
cut⇒L⇐R p (⇒L p₁ f f₁) = ⇒L refl (cut⇒L⇐R p f₁) ∘ ⇒L⇐R
cut⇒L⇐R p (⇐L p₁ f f₁) = ⇐L refl (cut⇒L⇐R p f₁) ∘ ⇐L⇐R
cut⇒L⇐R p (⊗L p₁ f) = ⊗L (cut⇒L⇐R p f) ∘ ⊗L⇐R

cut⇒L⊗R₁ : ∀ {T U V W A B A' B'} (p : Path T)
  → (f : U ⊢ (A ⇒ B)) {g : V ⊢ A} 
  → {h : sub p (η B) ⊢ A'}
  → {k : W ⊢ B'}
  → cut⇒L (p ◂ _) f g (⊗R h k) ≗ ⊗R (cut⇒L p f g h) k
cut⇒L⊗R₁ p (⇒R f) = refl
cut⇒L⊗R₁ p (⇒L p₁ f f₁) = ⇒L refl (cut⇒L⊗R₁ p f₁) ∘ ⇒L⊗R₁
cut⇒L⊗R₁ p (⇐L p₁ f f₁) = ⇐L refl (cut⇒L⊗R₁ p f₁) ∘ ⇐L⊗R₁
cut⇒L⊗R₁ p (⊗L p₁ f) = ⊗L (cut⇒L⊗R₁ p f) ∘ ⊗L⊗R₁

cut⇒L⊗R₂ : ∀ {T U V W A B A' B'} (p : Path T)
  → (f : U ⊢ (A ⇒ B)) {g : V ⊢ A} 
  → {h : W ⊢ A'}
  → {k : sub p (η B) ⊢ B'}
  → cut⇒L (_ ▸ p) f g (⊗R h k) ≗ ⊗R h (cut⇒L p f g k)
cut⇒L⊗R₂ p (⇒R f) = refl
cut⇒L⊗R₂ p (⇒L p₁ f f₁) = ⇒L refl (cut⇒L⊗R₂ p f₁) ∘ ⇒L⊗R₂
cut⇒L⊗R₂ p (⇐L p₁ f f₁) = ⇐L refl (cut⇒L⊗R₂ p f₁) ∘ ⇐L⊗R₂
cut⇒L⊗R₂ p (⊗L p₁ f) = ⊗L (cut⇒L⊗R₂ p f) ∘ ⊗L⊗R₂

cut⇐L⇒R : ∀ {T U V A B A' B'} (p : Path T)
  → (f : U ⊢ (B ⇐ A)) {g : V ⊢ A} 
  → {h : (η A' ⊛ sub p (η B)) ⊢ B'}
  → cut⇐L p f g (⇒R h) ≗ ⇒R (cut⇐L (η A' ▸ p) f g h)
cut⇐L⇒R p (⇐R f) = refl
cut⇐L⇒R p (⇒L p₁ f f₁) = ⇒L refl (cut⇐L⇒R p f₁) ∘ ⇒L⇒R
cut⇐L⇒R p (⇐L p₁ f f₁) = ⇐L refl (cut⇐L⇒R p f₁) ∘ ⇐L⇒R
cut⇐L⇒R p (⊗L p₁ f) = ⊗L (cut⇐L⇒R p f) ∘ ⊗L⇒R

cut⇐L⇐R : ∀ {T U V A B A' B'} (p : Path T)
  → (f : U ⊢ (B ⇐ A)) {g : V ⊢ A} 
  → {h : (sub p (η B) ⊛ η A') ⊢ B'}
  → cut⇐L p f g (⇐R h) ≗ ⇐R (cut⇐L (p ◂ η A') f g h)
cut⇐L⇐R p (⇐R f) = refl
cut⇐L⇐R p (⇒L p₁ f f₁) = ⇒L refl (cut⇐L⇐R p f₁) ∘ ⇒L⇐R
cut⇐L⇐R p (⇐L p₁ f f₁) = ⇐L refl (cut⇐L⇐R p f₁) ∘ ⇐L⇐R
cut⇐L⇐R p (⊗L p₁ f) = ⊗L (cut⇐L⇐R p f) ∘ ⊗L⇐R


cut⇐L⊗R₁ : ∀ {T U V W A B A' B'} (p : Path T)
  → (f : U ⊢ (B ⇐ A)) {g : V ⊢ A}
  → {h : sub p (η B) ⊢ A'}
  → {k : W ⊢ B'}
  → cut⇐L (p ◂ _) f g (⊗R h k) ≗ ⊗R (cut⇐L p f g h) k
cut⇐L⊗R₁ p (⇐R f) = refl
cut⇐L⊗R₁ p (⇒L p₁ f f₁) = ⇒L refl (cut⇐L⊗R₁ p f₁) ∘ ⇒L⊗R₁
cut⇐L⊗R₁ p (⇐L p₁ f f₁) = ⇐L refl (cut⇐L⊗R₁ p f₁) ∘ ⇐L⊗R₁
cut⇐L⊗R₁ p (⊗L p₁ f) = ⊗L (cut⇐L⊗R₁ p f) ∘ ⊗L⊗R₁

cut⇐L⊗R₂ : ∀ {T U V W A B A' B'} (p : Path T)
  → (f : U ⊢ (B ⇐ A)) {g : V ⊢ A}
  → {h : W ⊢ A'}
  → {k : sub p (η B) ⊢ B'}
  → cut⇐L (_ ▸ p) f g (⊗R h k) ≗ ⊗R h (cut⇐L p f g k)
cut⇐L⊗R₂ p (⇐R f) = refl
cut⇐L⊗R₂ p (⇒L p₁ f f₁) = ⇒L refl (cut⇐L⊗R₂ p f₁) ∘ ⇒L⊗R₂
cut⇐L⊗R₂ p (⇐L p₁ f f₁) = ⇐L refl (cut⇐L⊗R₂ p f₁) ∘ ⇐L⊗R₂
cut⇐L⊗R₂ p (⊗L p₁ f) = ⊗L (cut⇐L⊗R₂ p f) ∘ ⊗L⊗R₂

cut⊗L⇒R : ∀ {T U A B A' B'} (p : Path T)
  → (f : U ⊢ (A ⊗ B))
  → {g : (η A' ⊛ sub p (η A ⊛ η B)) ⊢ B'}
  → cut⊗L p f (⇒R g) ≗ ⇒R (cut⊗L (η A' ▸ p) f g)
cut⊗L⇒R p (⇒L p₁ f f₁) = ⇒L refl (cut⊗L⇒R p f₁) ∘ ⇒L⇒R
cut⊗L⇒R p (⇐L p₁ f f₁) = ⇐L refl (cut⊗L⇒R p f₁) ∘ ⇐L⇒R
cut⊗L⇒R p (⊗R f f₁) = refl
cut⊗L⇒R p (⊗L p₁ f) = ⊗L (cut⊗L⇒R p f) ∘ ⊗L⇒R

cut⊗L⇐R : ∀ {T U A B A' B'} (p : Path T)
  → (f : U ⊢ (A ⊗ B))
  → {g : (sub p (η A ⊛ η B) ⊛ η A') ⊢ B'}
  → cut⊗L p f (⇐R g) ≗ ⇐R (cut⊗L (p ◂ η A') f g)
cut⊗L⇐R p (⇒L p₁ f f₁) = ⇒L refl (cut⊗L⇐R p f₁) ∘ ⇒L⇐R
cut⊗L⇐R p (⇐L p₁ f f₁) = ⇐L refl (cut⊗L⇐R p f₁) ∘ ⇐L⇐R
cut⊗L⇐R p (⊗R f f₁) = refl
cut⊗L⇐R p (⊗L p₁ f) = ⊗L (cut⊗L⇐R p f) ∘ ⊗L⇐R

cut⊗L⊗R₁ : ∀ {T U V A B A' B'} (p : Path T)
  → (f : U ⊢ (A ⊗ B)) {g : sub p (η A ⊛ η B) ⊢ A'}
  → {h : V ⊢ B'}
  → cut⊗L (p ◂ _) f (⊗R g h) ≗ ⊗R (cut⊗L p f g) h
cut⊗L⊗R₁ p (⇒L p₁ f f₁) = ⇒L refl (cut⊗L⊗R₁ p f₁) ∘ ⇒L⊗R₁
cut⊗L⊗R₁ p (⇐L p₁ f f₁) = ⇐L refl (cut⊗L⊗R₁ p f₁) ∘ ⇐L⊗R₁
cut⊗L⊗R₁ p (⊗R f f₁) = refl
cut⊗L⊗R₁ p (⊗L p₁ f) = ⊗L (cut⊗L⊗R₁ p f) ∘ ⊗L⊗R₁

cut⊗L⊗R₂ : ∀ {T U V A B A' B'} (p : Path T)
  → (f : U ⊢ (A ⊗ B)) {g : V ⊢ A'} 
  → {h :  sub p (η A ⊛ η B) ⊢ B'}
  → cut⊗L (_ ▸ p) f (⊗R g h) ≗ ⊗R g (cut⊗L p f h)
cut⊗L⊗R₂ p (⇒L p₁ f f₁) = ⇒L refl (cut⊗L⊗R₂ p f₁) ∘ ⇒L⊗R₂
cut⊗L⊗R₂ p (⇐L p₁ f f₁) = ⇐L refl (cut⊗L⊗R₂ p f₁) ∘ ⇐L⊗R₂
cut⊗L⊗R₂ p (⊗R f f₁) = refl
cut⊗L⊗R₂ p (⊗L p₁ f) = ⊗L (cut⊗L⊗R₂ p f) ∘ ⊗L⊗R₂

cut⊗L⊗L₁ : ∀ {T U V W A B A' B' C} 
  → (p₁ : Path T) (p₂ : Path U) (p₃ : Path V) 
  → (f : W ⊢ (A ⊗ B)) 
  → {g : sub p₁ (sub p₂ (η A ⊛ η B) ⊛ sub p₃ (η A' ⊛ η B')) ⊢ C}
  → cut⊗L (p₁ ++ (p₂ ◂ _)) f (⊗L (p₁ ++ (_ ▸ p₃)) g) ≗ ⊗L (p₁ ++ (_ ▸ p₃)) (cut⊗L (p₁ ++ (p₂ ◂ _)) f g)
cut⊗L⊗L₁ p₁ p₂ p₃ (⇒L p f f₁) = ⇒L refl (cut⊗L⊗L₁ p₁ p₂ p₃ f₁) ∘ (~ ⊗L⇒L₂2/\1 {p = p₁})
cut⊗L⊗L₁ p₁ p₂ p₃ (⇐L p f f₁) = ⇐L refl (cut⊗L⊗L₁ p₁ p₂ p₃ f₁) ∘ (~ ⊗L⇐L₂2/\1 {p = p₁})
cut⊗L⊗L₁ {A = A} {B} {A'} {B'} p₁ p₂ p₃ (⊗R {U = U} f f₁) 
  rewrite subeq-2/\1 p₁ (η (A' ⊗ B')) (η B) (p₂ ++ (η A ▸ ∙)) p₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η A) (p₂ ++ (∙ ◂ U)) p₃ = refl
cut⊗L⊗L₁ p₁ p₂ p₃ (⊗L p f) = ⊗L (cut⊗L⊗L₁ p₁ p₂ p₃ f) ∘ (~ ⊗L⊗L {p = p₁})

cut⊗L⊗L₂ : ∀ {T U V W A B A' B' C} 
  → (p₁ : Path T) (p₂ : Path U) (p₃ : Path V) 
  → (f : W ⊢ (A' ⊗ B')) 
  → {g : sub p₁ (sub p₂ (η A ⊛ η B) ⊛ sub p₃ (η A' ⊛ η B')) ⊢ C}
  → cut⊗L (p₁ ++ (_ ▸ p₃)) f (⊗L (p₁ ++ (p₂ ◂ _)) g) ≗ ⊗L (p₁ ++ (p₂ ◂ _)) (cut⊗L (p₁ ++ (_ ▸ p₃)) f g)
cut⊗L⊗L₂ p₁ p₂ p₃ (⇒L p f f₁) = ⇒L refl (cut⊗L⊗L₂ p₁ p₂ p₃ f₁) ∘ (~ ⊗L⇒L₂1/\2 {p = p₁})
cut⊗L⊗L₂ p₁ p₂ p₃ (⇐L p f f₁) = ⇐L refl (cut⊗L⊗L₂ p₁ p₂ p₃ f₁) ∘ (~ ⊗L⇐L₂1/\2 {p = p₁})
cut⊗L⊗L₂ {A = A} {B} {A'} {B'} p₁ p₂ p₃ (⊗R {U = U} f f₁) 
  rewrite subeq-1/\2 p₁ (η (A ⊗ B)) (η B') p₂ (p₃ ++ (η A' ▸ ∙)) |
          subeq-1/\2 p₁ (η (A ⊗ B)) (η A') p₂ (p₃ ++ (∙ ◂ U)) = refl
cut⊗L⊗L₂ p₁ p₂ p₃ (⊗L p f) = ⊗L (cut⊗L⊗L₂ p₁ p₂ p₃ f) ∘ (⊗L⊗L {p = p₁})

cut⊗L⇒L-vass₁ : ∀ {T U V A B A' B' C}
  → (p : Path T) (q : Path U)
  → (f : V ⊢ (A' ⊗ B'))
  → {g : sub q (η A' ⊛ η B') ⊢ A} {h : sub p (η B) ⊢ C}
  → cut⊗L (p ++ (q ◂ η (A ⇒ B))) f (⇒L p g h) ≗ ⇒L p (cut⊗L q f g) h
cut⊗L⇒L-vass₁ p q (⇒L p₁ f f₁) = ⇒L refl (cut⊗L⇒L-vass₁ p q f₁) ∘ ⇒L⇒L
cut⊗L⇒L-vass₁ p q (⇐L p₁ f f₁) = ⇐L refl (cut⊗L⇒L-vass₁ p q f₁) ∘ ⇐L⇒L
cut⊗L⇒L-vass₁ {A = A} {B} {A'} {B'} p q (⊗R {U = U} f f₁) 
  rewrite subeq-2>L1 p (η (A ⇒ B)) (η B') (q ++ (η A' ▸ ∙)) |
          subeq-2>L1 p (η (A ⇒ B)) (η A') (q ++ (∙ ◂ U)) = refl
cut⊗L⇒L-vass₁ p q (⊗L p₁ f) = ⊗L (cut⊗L⇒L-vass₁ p q f) ∘ ⊗L⇒L₁

cut⊗L⇒L-vass₂ : ∀ {T U V A B A' B' C}
  → (p : Path T) (q : Path U)
  → (f : V ⊢ (A ⇒ B))
  → {g : sub q (η A' ⊛ η B') ⊢ A} {h : sub p (η B) ⊢ C}
  → cut⇒L p f (⊗L q g) h ≗ ⊗L (p ++ (q ◂ _)) (cut⇒L p f g h)
cut⊗L⇒L-vass₂ p q (⇒R f) {g} {h} = cut⊗L≗ (p ++ (∙ ◂ _)) q g (cut p f h refl) refl
cut⊗L⇒L-vass₂ p q (⇒L p₁ f f₁) = ⇒L refl (cut⊗L⇒L-vass₂ p q f₁) ∘ (~ ⊗L⇒L₂1/\2 {p = p})
cut⊗L⇒L-vass₂ p q (⇐L p₁ f f₁) = ⇐L refl (cut⊗L⇒L-vass₂ p q f₁) ∘ (~ ⊗L⇐L₂1/\2 {p = p})
cut⊗L⇒L-vass₂ p q (⊗L p₁ f) = ⊗L (cut⊗L⇒L-vass₂ p q f) ∘ ⊗L⊗L {p = p}

cut⊗L⇐L-vass₁ : ∀ {T U V A B A' B' C}
  → (p : Path T) (q : Path U)
  → (f : V ⊢ (A' ⊗ B'))
  → {g : sub q (η A' ⊛ η B') ⊢ A} {h : sub p (η B) ⊢ C}
  → cut⊗L (p ++ (_ ▸ q)) f (⇐L p g h) ≗ ⇐L p (cut⊗L q f g) h
cut⊗L⇐L-vass₁ p q (⇒L p₁ f f₁) = ⇒L refl (cut⊗L⇐L-vass₁ p q f₁) ∘ ⇒L⇐L
cut⊗L⇐L-vass₁ p q (⇐L p₁ f f₁) = ⇐L refl (cut⊗L⇐L-vass₁ p q f₁) ∘ ⇐L⇐L 
cut⊗L⇐L-vass₁ {A = A} {B} {A'} {B'} p q (⊗R {U = U} f f₁) 
  rewrite subeq-2>R1 p (η (B ⇐ A)) (η B') (q ++ (η A' ▸ ∙)) |
          subeq-2>R1 p (η (B ⇐ A)) (η A') (q ++ (∙ ◂ U)) = refl
cut⊗L⇐L-vass₁ p q (⊗L p₁ f) = ⊗L (cut⊗L⇐L-vass₁ p q f) ∘ ⊗L⇐L₁

cut⊗L⇐L-vass₂ : ∀ {T U V A B A' B' C}
  → (p : Path T) (q : Path U)
  → (f : V ⊢ (B ⇐ A))
  → {g : sub q (η A' ⊛ η B') ⊢ A} {h : sub p (η B) ⊢ C}
  → cut⇐L p f (⊗L q g) h ≗ ⊗L (p ++ (_ ▸ q)) (cut⇐L p f g h)
cut⊗L⇐L-vass₂ p q (⇐R f) {g} {h} = cut⊗L≗ (p ++ (_ ▸ ∙)) q g (cut p f h refl) refl
cut⊗L⇐L-vass₂ p q (⇒L p₁ f f₁) = ⇒L refl (cut⊗L⇐L-vass₂ p q f₁) ∘ (~ ⊗L⇒L₂2/\1 {p = p})
cut⊗L⇐L-vass₂ p q (⇐L p₁ f f₁) = ⇐L refl (cut⊗L⇐L-vass₂ p q f₁) ∘ (~ ⊗L⇐L₂2/\1 {p = p})
cut⊗L⇐L-vass₂ p q (⊗L p₁ f) = ⊗L (cut⊗L⇐L-vass₂ p q f) ∘ (~ ⊗L⊗L {p = p})

cut⊗L⇒L1/\2-hass₁ : ∀ {T U V W₁ W₂ A B A' B' C}
  → (p₁ : Path T) (p₂ : Path U) (p₃ : Path V)
  → (f : W₁ ⊢ (A ⇒ B)) {g : W₂ ⊢ A}
  → {h : sub p₁ (sub p₂ (η A' ⊛ η B') ⊛ sub p₃ (η B)) ⊢ C}
  → cut⇒L (p₁ ++ (_ ▸ p₃)) f g (⊗L (p₁ ++ (p₂ ◂ _)) h) 
    ≗ ⊗L (p₁ ++ (p₂ ◂ _)) (cut⇒L (p₁ ++ (_ ▸ p₃)) f g h)  
cut⊗L⇒L1/\2-hass₁ {W₁ = W₁} {A = A} {B} {A'} {B'} p₁ p₂ p₃ (⇒R f) 
  rewrite subeq-1/\2 p₁ (η (A' ⊗ B')) (η B) p₂ p₃ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η A) p₂ (p₃ ++ (∙ ◂ W₁)) = refl
cut⊗L⇒L1/\2-hass₁ p₁ p₂ p₃ (⇒L p f f₁) = ⇒L refl (cut⊗L⇒L1/\2-hass₁ p₁ p₂ p₃ f₁) ∘ (~ ⊗L⇒L₂1/\2 {p = p₁})
cut⊗L⇒L1/\2-hass₁ p₁ p₂ p₃ (⇐L p f f₁) = ⇐L refl (cut⊗L⇒L1/\2-hass₁ p₁ p₂ p₃ f₁) ∘ (~ ⊗L⇐L₂1/\2 {p = p₁})
cut⊗L⇒L1/\2-hass₁ p₁ p₂ p₃ (⊗L p f) = ⊗L (cut⊗L⇒L1/\2-hass₁ p₁ p₂ p₃ f) ∘ ⊗L⊗L {p = p₁}     

cut⊗L⇒L1/\2-hass₂ : ∀ {T U V W₁ W₂ A B A' B' C}
  → (p₁ : Path T) (p₂ : Path U) (p₃ : Path V)
  → (f : W₁ ⊢ A' ⊗ B') {g : W₂ ⊢ A}
  → {h : sub p₁ (sub p₂ (η A' ⊛ η B') ⊛ sub p₃ (η B)) ⊢ C}
  → cut⊗L (p₁ ++ (p₂ ◂ _)) f (⇒L (p₁ ++ (_ ▸ p₃)) g h)
      ≗ ⇒L (p₁ ++ (_ ▸ p₃)) g (cut⊗L (p₁ ++ (p₂ ◂ _)) f h)
cut⊗L⇒L1/\2-hass₂ p₁ p₂ p₃ (⇒L p f f₁) = ⇒L refl (cut⊗L⇒L1/\2-hass₂ p₁ p₂ p₃ f₁) ∘ ⇒L⇒L₂ {p = p₁}
cut⊗L⇒L1/\2-hass₂ p₁ p₂ p₃ (⇐L p f f₁) = ⇐L refl (cut⊗L⇒L1/\2-hass₂ p₁ p₂ p₃ f₁) ∘ ⇐L⇒L₂ {p = p₁}
cut⊗L⇒L1/\2-hass₂ {W₂ = W₂} {A} {B} {A'} {B'} p₁ p₂ p₃ (⊗R {U = U} f f₁) 
  rewrite subeq-2/\1 p₁ (W₂ ⊛ η (A ⇒ B)) (η B') (p₂ ++ (η A' ▸ ∙)) p₃ |
          subeq-2/\1 p₁ (W₂ ⊛ η (A ⇒ B)) (η A') (p₂ ++ (∙ ◂ U)) p₃ = refl
cut⊗L⇒L1/\2-hass₂ p₁ p₂ p₃ (⊗L p f) = ⊗L (cut⊗L⇒L1/\2-hass₂ p₁ p₂ p₃ f) ∘ ⊗L⇒L₂1/\2 {p = p₁}   

cut⊗L⇐L1/\2-hass₁ : ∀ {T U V W₁ W₂ A B A' B' C}
  → (p₁ : Path T) (p₂ : Path U) (p₃ : Path V)
  → (f : W₁ ⊢ (B ⇐ A)) {g : W₂ ⊢ A}
  → {h : sub p₁ (sub p₂ (η A' ⊛ η B') ⊛ sub p₃ (η B)) ⊢ C}
  → cut⇐L (p₁ ++ (_ ▸ p₃)) f g (⊗L (p₁ ++ (p₂ ◂ _)) h) 
    ≗ ⊗L (p₁ ++ (p₂ ◂ _)) (cut⇐L (p₁ ++ (_ ▸ p₃)) f g h)  
cut⊗L⇐L1/\2-hass₁ {W₁ = W₁} {A = A} {B} {A'} {B'} p₁ p₂ p₃ (⇐R f) 
  rewrite subeq-1/\2 p₁ (η (A' ⊗ B')) (η B) p₂ p₃ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η A) p₂ (p₃ ++ (W₁ ▸ ∙)) = refl
cut⊗L⇐L1/\2-hass₁ p₁ p₂ p₃ (⇒L p f f₁) = ⇒L refl (cut⊗L⇐L1/\2-hass₁ p₁ p₂ p₃ f₁) ∘ (~ ⊗L⇒L₂1/\2 {p = p₁})
cut⊗L⇐L1/\2-hass₁ p₁ p₂ p₃ (⇐L p f f₁) = ⇐L refl (cut⊗L⇐L1/\2-hass₁ p₁ p₂ p₃ f₁) ∘ (~ ⊗L⇐L₂1/\2 {p = p₁})
cut⊗L⇐L1/\2-hass₁ p₁ p₂ p₃ (⊗L p f) = ⊗L (cut⊗L⇐L1/\2-hass₁ p₁ p₂ p₃ f) ∘ ⊗L⊗L {p = p₁}        

cut⊗L⇐L1/\2-hass₂ : ∀ {T U V W₁ W₂ A B A' B' C}
  → (p₁ : Path T) (p₂ : Path U) (p₃ : Path V)
  → (f : W₁ ⊢ A' ⊗ B') {g : W₂ ⊢ A}
  → {h : sub p₁ (sub p₂ (η A' ⊛ η B') ⊛ sub p₃ (η B)) ⊢ C}
  → cut⊗L (p₁ ++ (p₂ ◂ _)) f (⇐L (p₁ ++ (_ ▸ p₃)) g h)
      ≗ ⇐L (p₁ ++ (_ ▸ p₃)) g (cut⊗L (p₁ ++ (p₂ ◂ _)) f h)
cut⊗L⇐L1/\2-hass₂ p₁ p₂ p₃ (⇒L p f f₁) = ⇒L refl (cut⊗L⇐L1/\2-hass₂ p₁ p₂ p₃ f₁) ∘ ⇒L⇐L₂ {p = p₁}
cut⊗L⇐L1/\2-hass₂ p₁ p₂ p₃ (⇐L p f f₁) = ⇐L refl (cut⊗L⇐L1/\2-hass₂ p₁ p₂ p₃ f₁) ∘ ⇐L⇐L₂ {p = p₁}
cut⊗L⇐L1/\2-hass₂ {W₂ = W₂} {A} {B} {A'} {B'} p₁ p₂ p₃ (⊗R {U = U} f f₁) 
  rewrite subeq-2/\1 p₁ (η (B ⇐ A) ⊛ W₂) (η B') (p₂ ++ (η A' ▸ ∙)) p₃ |
          subeq-2/\1 p₁ (η (B ⇐ A) ⊛ W₂) (η A') (p₂ ++ (∙ ◂ U)) p₃ = refl
cut⊗L⇐L1/\2-hass₂ p₁ p₂ p₃ (⊗L p f) = ⊗L (cut⊗L⇐L1/\2-hass₂ p₁ p₂ p₃ f) ∘ ⊗L⇐L₂1/\2 {p = p₁}   

cut⊗L⇒L2/\1-hass₁ : ∀ {T U V W₁ W₂ A B A' B' C}
  → (p₁ : Path T) (p₂ : Path U) (p₃ : Path V)
  → (f : W₁ ⊢ (A ⇒ B)) {g : W₂ ⊢ A}
  → {h : sub p₁ (sub p₂ (η B) ⊛ sub p₃ (η A' ⊛ η B')) ⊢ C}
  → cut⇒L (p₁ ++ (p₂ ◂ _)) f g (⊗L (p₁ ++ (_ ▸ p₃)) h) 
    ≗ ⊗L (p₁ ++ (_ ▸ p₃)) (cut⇒L (p₁ ++ (p₂ ◂ _)) f g h)  
cut⊗L⇒L2/\1-hass₁ {W₁ = W₁} {A = A} {B} {A'} {B'} p₁ p₂ p₃ (⇒R f) 
  rewrite subeq-2/\1 p₁ (η (A' ⊗ B')) (η B) p₂ p₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η A) (p₂ ++ (∙ ◂ W₁)) p₃ = refl
cut⊗L⇒L2/\1-hass₁ p₁ p₂ p₃ (⇒L p f f₁) = ⇒L refl (cut⊗L⇒L2/\1-hass₁ p₁ p₂ p₃ f₁) ∘ (~ ⊗L⇒L₂2/\1 {p = p₁})
cut⊗L⇒L2/\1-hass₁ p₁ p₂ p₃ (⇐L p f f₁) = ⇐L refl (cut⊗L⇒L2/\1-hass₁ p₁ p₂ p₃ f₁) ∘ (~ ⊗L⇐L₂2/\1 {p = p₁})
cut⊗L⇒L2/\1-hass₁ p₁ p₂ p₃ (⊗L p f) = ⊗L (cut⊗L⇒L2/\1-hass₁ p₁ p₂ p₃ f) ∘ (~ ⊗L⊗L {p = p₁})     

cut⊗L⇒L2/\1-hass₂ : ∀ {T U V W₁ W₂ A B A' B' C}
  → (p₁ : Path T) (p₂ : Path U) (p₃ : Path V)
  → (f : W₁ ⊢ A' ⊗ B') {g : W₂ ⊢ A}
  → {h : sub p₁ (sub p₂ (η B) ⊛ sub p₃ (η A' ⊛ η B')) ⊢ C}
  → cut⊗L (p₁ ++ (_ ▸ p₃)) f (⇒L (p₁ ++ (p₂ ◂ _)) g h)
      ≗ ⇒L (p₁ ++ (p₂ ◂ _)) g (cut⊗L (p₁ ++ (_ ▸ p₃)) f h)
cut⊗L⇒L2/\1-hass₂ p₁ p₂ p₃ (⇒L p f f₁) = ⇒L refl (cut⊗L⇒L2/\1-hass₂ p₁ p₂ p₃ f₁) ∘ (~ ⇒L⇒L₂ {p = p₁}) 
cut⊗L⇒L2/\1-hass₂ p₁ p₂ p₃ (⇐L p f f₁) = ⇐L refl (cut⊗L⇒L2/\1-hass₂ p₁ p₂ p₃ f₁) ∘ (~ ⇒L⇐L₂ {p = p₁})
cut⊗L⇒L2/\1-hass₂ {W₂ = W₂} {A} {B} {A'} {B'} p₁ p₂ p₃ (⊗R {U = U} f f₁) 
  rewrite subeq-1/\2 p₁ (W₂ ⊛ η (A ⇒ B)) (η B') p₂ (p₃ ++ (η A' ▸ ∙)) |
          subeq-1/\2 p₁ (W₂ ⊛ η (A ⇒ B)) (η A') p₂ (p₃ ++ (∙ ◂ U)) = refl
cut⊗L⇒L2/\1-hass₂ p₁ p₂ p₃ (⊗L p f) = ⊗L (cut⊗L⇒L2/\1-hass₂ p₁ p₂ p₃ f) ∘ ⊗L⇒L₂2/\1 {p = p₁}   

cut⊗L⇐L2/\1-hass₁ : ∀ {T U V W₁ W₂ A B A' B' C}
  → (p₁ : Path T) (p₂ : Path U) (p₃ : Path V)
  → (f : W₁ ⊢ (B ⇐ A)) {g : W₂ ⊢ A}
  → {h : sub p₁ (sub p₂ (η B) ⊛ sub p₃ (η A' ⊛ η B')) ⊢ C}
  → cut⇐L (p₁ ++ (p₂ ◂ _)) f g (⊗L (p₁ ++ (_ ▸ p₃)) h) 
    ≗ ⊗L (p₁ ++ (_ ▸ p₃)) (cut⇐L (p₁ ++ (p₂ ◂ _)) f g h)  
cut⊗L⇐L2/\1-hass₁ {W₁ = W₁} {A = A} {B} {A'} {B'} p₁ p₂ p₃ (⇐R f) 
  rewrite subeq-2/\1 p₁ (η (A' ⊗ B')) (η B) p₂ p₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η A) (p₂ ++ (W₁ ▸ ∙)) p₃ = refl
cut⊗L⇐L2/\1-hass₁ p₁ p₂ p₃ (⇒L p f f₁) = ⇒L refl (cut⊗L⇐L2/\1-hass₁ p₁ p₂ p₃ f₁) ∘ (~ ⊗L⇒L₂2/\1 {p = p₁})
cut⊗L⇐L2/\1-hass₁ p₁ p₂ p₃ (⇐L p f f₁) = ⇐L refl (cut⊗L⇐L2/\1-hass₁ p₁ p₂ p₃ f₁) ∘ (~ ⊗L⇐L₂2/\1 {p = p₁})
cut⊗L⇐L2/\1-hass₁ p₁ p₂ p₃ (⊗L p f) = ⊗L (cut⊗L⇐L2/\1-hass₁ p₁ p₂ p₃ f) ∘ (~ ⊗L⊗L {p = p₁})      

cut⊗L⇐L2/\1-hass₂ : ∀ {T U V W₁ W₂ A B A' B' C}
  → (p₁ : Path T) (p₂ : Path U) (p₃ : Path V)
  → (f : W₁ ⊢ A' ⊗ B') {g : W₂ ⊢ A}
  → {h : sub p₁ (sub p₂ (η B) ⊛ sub p₃ (η A' ⊛ η B')) ⊢ C}
  → cut⊗L (p₁ ++ (_ ▸ p₃)) f (⇐L (p₁ ++ (p₂ ◂ _)) g h)
      ≗ ⇐L (p₁ ++ (p₂ ◂ _)) g (cut⊗L (p₁ ++ (_ ▸ p₃)) f h)
cut⊗L⇐L2/\1-hass₂ p₁ p₂ p₃ (⇒L p f f₁) = ⇒L refl (cut⊗L⇐L2/\1-hass₂ p₁ p₂ p₃ f₁) ∘ (~ ⇐L⇒L₂ {p = p₁}) 
cut⊗L⇐L2/\1-hass₂ p₁ p₂ p₃ (⇐L p f f₁) = ⇐L refl (cut⊗L⇐L2/\1-hass₂ p₁ p₂ p₃ f₁) ∘ (~ ⇐L⇐L₂ {p = p₁})
cut⊗L⇐L2/\1-hass₂ {W₂ = W₂} {A} {B} {A'} {B'} p₁ p₂ p₃ (⊗R {U = U} f f₁) 
  rewrite subeq-1/\2 p₁ (η (B ⇐ A) ⊛ W₂) (η B') p₂ (p₃ ++ (η A' ▸ ∙)) |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ W₂) (η A') p₂ (p₃ ++ (∙ ◂ U)) = refl
cut⊗L⇐L2/\1-hass₂ p₁ p₂ p₃ (⊗L p f) = ⊗L (cut⊗L⇐L2/\1-hass₂ p₁ p₂ p₃ f) ∘ ⊗L⇐L₂2/\1 {p = p₁}   

cut⇒L⇒L-vass₁ : ∀ {T U V W A B A' B' C} 
  → (p : Path T) (q : Path U)
  → (f : V ⊢ A' ⇒ B') {g : W ⊢ A'}
  → {h : sub p (η B') ⊢ A} {k : sub q (η B) ⊢ C}
  → cut⇒L (q ++ (p ◂ _)) f g (⇒L q h k) ≗ ⇒L q (cut⇒L p f g h) k
cut⇒L⇒L-vass₁ {V = V} {A = A} {B} {A'} {B'} p q (⇒R f) 
  rewrite subeq-2>L1 q (η (A ⇒ B)) (η B') p |
          subeq-2>L1 q (η (A ⇒ B)) (η A') (p ++ (∙ ◂ V)) = refl
cut⇒L⇒L-vass₁ p q (⇒L p₁ f f₁) = ⇒L refl (cut⇒L⇒L-vass₁ p q f₁) ∘ ⇒L⇒L {r = q}
cut⇒L⇒L-vass₁ p q (⇐L p₁ f f₁) = ⇐L refl (cut⇒L⇒L-vass₁ p q f₁) ∘ ⇐L⇒L {r = q}
cut⇒L⇒L-vass₁ p q (⊗L p₁ f) = ⊗L (cut⇒L⇒L-vass₁ p q f) ∘ ⊗L⇒L₁ {p' = q}

cut⇒L⇒L-vass₂ : ∀ {T U V W A B A' B' C} 
  → (p : Path T) (q : Path U)
  → (f : V ⊢ A ⇒ B) {g : W ⊢ A'}
  → {h : sub p (η B') ⊢ A} {k : sub q (η B) ⊢ C}
  → cut⇒L q f (⇒L p g h) k ≗ ⇒L (q ++ (p ◂ _)) g (cut⇒L q f h k)
cut⇒L⇒L-vass₂ {V = V} {A = A} {B} {A'} {B'} p q (⇒R f) {g} {h} {k} = cut⇒L≗ (q ++ (∙ ◂ V)) p h (cut q f k refl) refl
cut⇒L⇒L-vass₂ p q (⇒L p₁ f f₁) = ⇒L refl (cut⇒L⇒L-vass₂ p q f₁) ∘ (~ ⇒L⇒L₂ {p = q})
cut⇒L⇒L-vass₂ p q (⇐L p₁ f f₁) = ⇐L refl (cut⇒L⇒L-vass₂ p q f₁) ∘ (~ ⇒L⇐L₂ {p = q})
cut⇒L⇒L-vass₂ p q (⊗L p₁ f) = ⊗L (cut⇒L⇒L-vass₂ p q f) ∘ ⊗L⇒L₂2/\1 {p = q}

cut⇒L⇐L-vass₁ : ∀ {T U V W A B A' B' C} 
  → (p : Path T) (q : Path U)
  → (f : V ⊢ A' ⇒ B') {g : W ⊢ A'}
  → {h : sub p (η B') ⊢ A} {k : sub q (η B) ⊢ C}
  → cut⇒L (q ++ (_ ▸ p)) f g (⇐L q h k) ≗ ⇐L q (cut⇒L p f g h) k
cut⇒L⇐L-vass₁ {V = V} {A = A} {B} {A'} {B'} p q (⇒R f) 
  rewrite subeq-2>R1 q (η (B ⇐ A)) (η B') p |
          subeq-2>R1 q (η (B ⇐ A)) (η A') (p ++ (∙ ◂ V)) = refl
cut⇒L⇐L-vass₁ p q (⇒L p₁ f f₁) = ⇒L refl (cut⇒L⇐L-vass₁ p q f₁) ∘ ⇒L⇐L {r = q}
cut⇒L⇐L-vass₁ p q (⇐L p₁ f f₁) = ⇐L refl (cut⇒L⇐L-vass₁ p q f₁) ∘ ⇐L⇐L {r = q}
cut⇒L⇐L-vass₁ p q (⊗L p₁ f) = ⊗L (cut⇒L⇐L-vass₁ p q f) ∘ ⊗L⇐L₁ {p' = q}

cut⇒L⇐L-vass₂ : ∀ {T U V W A B A' B' C} 
  → (p : Path T) (q : Path U)
  → (f : V ⊢ A ⇒ B) {g : W ⊢ A'}
  → {h : sub p (η B') ⊢ A} {k : sub q (η B) ⊢ C}
  → cut⇒L q f (⇐L p g h) k ≗ ⇐L (q ++ (p ◂ _)) g (cut⇒L q f h k)
cut⇒L⇐L-vass₂ {V = V} {A = A} {B} {A'} {B'} p q (⇒R f) {g} {h} {k} = cut⇐L≗ (q ++ (∙ ◂ V)) p h (cut q f k refl) refl
cut⇒L⇐L-vass₂ p q (⇒L p₁ f f₁) = ⇒L refl (cut⇒L⇐L-vass₂ p q f₁) ∘ (~ ⇐L⇒L₂ {p = q})
cut⇒L⇐L-vass₂ p q (⇐L p₁ f f₁) = ⇐L refl (cut⇒L⇐L-vass₂ p q f₁) ∘ (~ ⇐L⇐L₂ {p = q})
cut⇒L⇐L-vass₂ p q (⊗L p₁ f) = ⊗L (cut⇒L⇐L-vass₂ p q f) ∘ ⊗L⇐L₂2/\1 {p = q}

cut⇐L⇒L-vass₁ : ∀ {T U V W A B A' B' C} 
  → (p : Path T) (q : Path U)
  → (f : V ⊢ B' ⇐ A') {g : W ⊢ A'}
  → {h : sub p (η B') ⊢ A} {k : sub q (η B) ⊢ C}
  → cut⇐L (q ++ (p ◂ _)) f g (⇒L q h k) ≗ ⇒L q (cut⇐L p f g h) k
cut⇐L⇒L-vass₁ {V = V} {A = A} {B} {A'} {B'} p q (⇐R f) 
  rewrite subeq-2>L1 q (η (A ⇒ B)) (η B') p |
          subeq-2>L1 q (η (A ⇒ B)) (η A') (p ++ (V ▸ ∙)) = refl
cut⇐L⇒L-vass₁ p q (⇒L p₁ f f₁) = ⇒L refl (cut⇐L⇒L-vass₁ p q f₁) ∘ ⇒L⇒L {r = q}
cut⇐L⇒L-vass₁ p q (⇐L p₁ f f₁) = ⇐L refl (cut⇐L⇒L-vass₁ p q f₁) ∘ ⇐L⇒L {r = q}
cut⇐L⇒L-vass₁ p q (⊗L p₁ f) = ⊗L (cut⇐L⇒L-vass₁ p q f) ∘ ⊗L⇒L₁ {p' = q}

cut⇐L⇒L-vass₂ : ∀ {T U V W A B A' B' C} 
  → (p : Path T) (q : Path U)
  → (f : V ⊢ B ⇐ A) {g : W ⊢ A'}
  → {h : sub p (η B') ⊢ A} {k : sub q (η B) ⊢ C}
  → cut⇐L q f (⇒L p g h) k ≗ ⇒L (q ++ (_ ▸ p)) g (cut⇐L q f h k)
cut⇐L⇒L-vass₂ {V = V} {A = A} {B} {A'} {B'} p q (⇐R f) {g} {h} {k} = cut⇒L≗ (q ++ (V ▸ ∙)) p h (cut q f k refl) refl
cut⇐L⇒L-vass₂ p q (⇒L p₁ f f₁) = ⇒L refl (cut⇐L⇒L-vass₂ p q f₁) ∘ ⇒L⇒L₂ {p = q}
cut⇐L⇒L-vass₂ p q (⇐L p₁ f f₁) = ⇐L refl (cut⇐L⇒L-vass₂ p q f₁) ∘ ⇐L⇒L₂ {p = q} 
cut⇐L⇒L-vass₂ p q (⊗L p₁ f) = ⊗L (cut⇐L⇒L-vass₂ p q f) ∘ ⊗L⇒L₂1/\2 {p = q}


cut⇐L⇐L-vass₁ : ∀ {T U V W A B A' B' C} 
  → (p : Path T) (q : Path U)
  → (f : V ⊢ B' ⇐ A') {g : W ⊢ A'}
  → {h : sub p (η B') ⊢ A} {k : sub q (η B) ⊢ C}
  → cut⇐L (q ++ (_ ▸ p)) f g (⇐L q h k) ≗ ⇐L q (cut⇐L p f g h) k
cut⇐L⇐L-vass₁ {V = V} {A = A} {B} {A'} {B'} p q (⇐R f) 
  rewrite subeq-2>R1 q (η (B ⇐ A)) (η B') p |
          subeq-2>R1 q (η (B ⇐ A)) (η A') (p ++ (V ▸ ∙)) = refl
cut⇐L⇐L-vass₁ p q (⇒L p₁ f f₁) = ⇒L refl (cut⇐L⇐L-vass₁ p q f₁) ∘ ⇒L⇐L {r = q}
cut⇐L⇐L-vass₁ p q (⇐L p₁ f f₁) = ⇐L refl (cut⇐L⇐L-vass₁ p q f₁) ∘ ⇐L⇐L {r = q}
cut⇐L⇐L-vass₁ p q (⊗L p₁ f) = ⊗L (cut⇐L⇐L-vass₁ p q f) ∘ ⊗L⇐L₁ {p' = q}

cut⇐L⇐L-vass₂ : ∀ {T U V W A B A' B' C} 
  → (p : Path T) (q : Path U)
  → (f : V ⊢ B ⇐ A) {g : W ⊢ A'}
  → {h : sub p (η B') ⊢ A} {k : sub q (η B) ⊢ C}
  → cut⇐L q f (⇐L p g h) k ≗ ⇐L (q ++ (_ ▸ p)) g (cut⇐L q f h k)
cut⇐L⇐L-vass₂ {V = V} {A = A} {B} {A'} {B'} p q (⇐R f) {g} {h} {k} = cut⇐L≗ (q ++ (V ▸ ∙)) p h (cut q f k refl) refl
cut⇐L⇐L-vass₂ p q (⇒L p₁ f f₁) = ⇒L refl (cut⇐L⇐L-vass₂ p q f₁) ∘ ⇒L⇐L₂ {p = q}
cut⇐L⇐L-vass₂ p q (⇐L p₁ f f₁) = ⇐L refl (cut⇐L⇐L-vass₂ p q f₁) ∘ ⇐L⇐L₂ {p = q} 
cut⇐L⇐L-vass₂ p q (⊗L p₁ f) = ⊗L (cut⇐L⇐L-vass₂ p q f) ∘ ⊗L⇐L₂1/\2 {p = q}

cut⇒L⇒L-hass₁ : ∀ {T U V W₁ W₂ W₃ A B A' B' C}
  → (p₁ : Path T) (p₂ : Path U) (p₃ : Path V)
  → (f : W₁ ⊢ A' ⇒ B') 
  → {g : W₂ ⊢ A} {h : W₃ ⊢ A'}
  → {k : sub p₁ (sub p₂ (η B) ⊛ sub p₃ (η B')) ⊢ C}
  → cut⇒L (p₁ ++ (_ ▸ p₃)) f h (⇒L (p₁ ++ (p₂ ◂ _)) g k)
      ≗ ⇒L (p₁ ++ (p₂ ◂ _)) g (cut⇒L (p₁ ++ (_ ▸ p₃)) f h k)
cut⇒L⇒L-hass₁ {W₁ = W₁} {W₂} {A = A} {B} {A'} {B'} p₁ p₂ p₃ (⇒R f) 
  rewrite subeq-1/\2 p₁ (W₂ ⊛ η (A ⇒ B)) (η B') p₂ p₃ |
          subeq-1/\2 p₁ (W₂ ⊛ η (A ⇒ B)) (η A') p₂ (p₃ ++ (∙ ◂ W₁)) = refl
cut⇒L⇒L-hass₁ p₁ p₂ p₃ (⇒L p f f₁) = ⇒L refl (cut⇒L⇒L-hass₁ p₁ p₂ p₃ f₁) ∘ (~ ⇒L⇒L₂ {p = p₁})
cut⇒L⇒L-hass₁ p₁ p₂ p₃ (⇐L p f f₁) = ⇐L refl (cut⇒L⇒L-hass₁ p₁ p₂ p₃ f₁) ∘ (~ ⇒L⇐L₂ {p = p₁})
cut⇒L⇒L-hass₁ p₁ p₂ p₃ (⊗L p f) = ⊗L (cut⇒L⇒L-hass₁ p₁ p₂ p₃ f) ∘ ⊗L⇒L₂2/\1 {p = p₁}    

cut⇒L⇒L-hass₂ : ∀ {T U V W₁ W₂ W₃ A B A' B' C}
  → (p₁ : Path T) (p₂ : Path U) (p₃ : Path V)
  → (f : W₁ ⊢ A ⇒ B) 
  → {g : W₂ ⊢ A} {h : W₃ ⊢ A'}
  → {k : sub p₁ (sub p₂ (η B) ⊛ sub p₃ (η B')) ⊢ C}
  → cut⇒L (p₁ ++ (p₂ ◂ _)) f g (⇒L (p₁ ++ (_ ▸ p₃)) h k)
      ≗ ⇒L (p₁ ++ (_ ▸ p₃)) h (cut⇒L (p₁ ++ (p₂ ◂ _)) f g k)
cut⇒L⇒L-hass₂ {W₁ = W₁} {W₂} {W₃} {A} {B} {A'} {B'} p₁ p₂ p₃ (⇒R f) 
  rewrite subeq-2/\1 p₁ (W₃ ⊛ η (A' ⇒ B')) (η B) p₂ p₃ |
          subeq-2/\1 p₁ (W₃ ⊛ η (A' ⇒ B')) (η A) (p₂ ++ (∙ ◂ W₁)) p₃ = refl
cut⇒L⇒L-hass₂ p₁ p₂ p₃ (⇒L p f f₁) = ⇒L refl (cut⇒L⇒L-hass₂ p₁ p₂ p₃ f₁) ∘ ⇒L⇒L₂ {p = p₁}
cut⇒L⇒L-hass₂ p₁ p₂ p₃ (⇐L p f f₁) = ⇐L refl (cut⇒L⇒L-hass₂ p₁ p₂ p₃ f₁) ∘ ⇐L⇒L₂ {p = p₁}
cut⇒L⇒L-hass₂ p₁ p₂ p₃ (⊗L p f) = ⊗L (cut⇒L⇒L-hass₂ p₁ p₂ p₃ f) ∘ ⊗L⇒L₂1/\2 {p = p₁}    
 

cut⇒L⇐L-hass₁ : ∀ {T U V W₁ W₂ W₃ A B A' B' C}
  → (p₁ : Path T) (p₂ : Path U) (p₃ : Path V)
  → (f : W₁ ⊢ A' ⇒ B') 
  → {g : W₂ ⊢ A} {h : W₃ ⊢ A'}
  → {k : sub p₁ (sub p₂ (η B) ⊛ sub p₃ (η B')) ⊢ C}
  → cut⇒L (p₁ ++ (_ ▸ p₃)) f h (⇐L (p₁ ++ (p₂ ◂ _)) g k)
      ≗ ⇐L (p₁ ++ (p₂ ◂ _)) g (cut⇒L (p₁ ++ (_ ▸ p₃)) f h k)
cut⇒L⇐L-hass₁ {W₁ = W₁} {W₂} {A = A} {B} {A'} {B'} p₁ p₂ p₃ (⇒R f) 
  rewrite subeq-1/\2 p₁ (η (B ⇐ A) ⊛ W₂) (η B') p₂ p₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ W₂) (η A') p₂ (p₃ ++ (∙ ◂ W₁)) = refl
cut⇒L⇐L-hass₁ p₁ p₂ p₃ (⇒L p f f₁) = ⇒L refl (cut⇒L⇐L-hass₁ p₁ p₂ p₃ f₁) ∘ (~ ⇐L⇒L₂ {p = p₁})
cut⇒L⇐L-hass₁ p₁ p₂ p₃ (⇐L p f f₁) = ⇐L refl (cut⇒L⇐L-hass₁ p₁ p₂ p₃ f₁) ∘ (~ ⇐L⇐L₂ {p = p₁})
cut⇒L⇐L-hass₁ p₁ p₂ p₃ (⊗L p f) = ⊗L (cut⇒L⇐L-hass₁ p₁ p₂ p₃ f) ∘ ⊗L⇐L₂2/\1 {p = p₁}      

cut⇒L⇐L-hass₂ : ∀ {T U V W₁ W₂ W₃ A B A' B' C}
  → (p₁ : Path T) (p₂ : Path U) (p₃ : Path V)
  → (f : W₁ ⊢ A ⇒ B) 
  → {g : W₂ ⊢ A} {h : W₃ ⊢ A'}
  → {k : sub p₁ (sub p₂ (η B) ⊛ sub p₃ (η B')) ⊢ C}
  → cut⇒L (p₁ ++ (p₂ ◂ _)) f g (⇐L (p₁ ++ (_ ▸ p₃)) h k)
      ≗ ⇐L (p₁ ++ (_ ▸ p₃)) h (cut⇒L (p₁ ++ (p₂ ◂ _)) f g k)
cut⇒L⇐L-hass₂ {W₁ = W₁} {W₂} {W₃} {A} {B} {A'} {B'} p₁ p₂ p₃ (⇒R f) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ W₃) (η B) p₂ p₃ |
          subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ W₃) (η A) (p₂ ++ (∙ ◂ W₁)) p₃ = refl
cut⇒L⇐L-hass₂ p₁ p₂ p₃ (⇒L p f f₁) = ⇒L refl (cut⇒L⇐L-hass₂ p₁ p₂ p₃ f₁) ∘ ⇒L⇐L₂ {p = p₁}
cut⇒L⇐L-hass₂ p₁ p₂ p₃ (⇐L p f f₁) = ⇐L refl (cut⇒L⇐L-hass₂ p₁ p₂ p₃ f₁) ∘ ⇐L⇐L₂ {p = p₁}
cut⇒L⇐L-hass₂ p₁ p₂ p₃ (⊗L p f) = ⊗L (cut⇒L⇐L-hass₂ p₁ p₂ p₃ f) ∘ ⊗L⇐L₂1/\2 {p = p₁}   

cut⇐L⇒L-hass₁ : ∀ {T U V W₁ W₂ W₃ A B A' B' C}
  → (p₁ : Path T) (p₂ : Path U) (p₃ : Path V)
  → (f : W₁ ⊢ B' ⇐ A') 
  → {g : W₂ ⊢ A} {h : W₃ ⊢ A'}
  → {k : sub p₁ (sub p₂ (η B) ⊛ sub p₃ (η B')) ⊢ C}
  → cut⇐L (p₁ ++ (_ ▸ p₃)) f h (⇒L (p₁ ++ (p₂ ◂ _)) g k)
      ≗ ⇒L (p₁ ++ (p₂ ◂ _)) g (cut⇐L (p₁ ++ (_ ▸ p₃)) f h k)
cut⇐L⇒L-hass₁ {W₁ = W₁} {W₂} {A = A} {B} {A'} {B'} p₁ p₂ p₃ (⇐R f) 
  rewrite subeq-1/\2 p₁ (W₂ ⊛ η (A ⇒ B)) (η B') p₂ p₃ |
          subeq-1/\2 p₁ (W₂ ⊛ η (A ⇒ B)) (η A') p₂ (p₃ ++ (W₁ ▸ ∙)) = refl
cut⇐L⇒L-hass₁ p₁ p₂ p₃ (⇒L p f f₁) = ⇒L refl (cut⇐L⇒L-hass₁ p₁ p₂ p₃ f₁) ∘ (~ ⇒L⇒L₂ {p = p₁})
cut⇐L⇒L-hass₁ p₁ p₂ p₃ (⇐L p f f₁) = ⇐L refl (cut⇐L⇒L-hass₁ p₁ p₂ p₃ f₁) ∘ (~ ⇒L⇐L₂ {p = p₁})
cut⇐L⇒L-hass₁ p₁ p₂ p₃ (⊗L p f) = ⊗L (cut⇐L⇒L-hass₁ p₁ p₂ p₃ f) ∘ ⊗L⇒L₂2/\1 {p = p₁}      

cut⇐L⇒L-hass₂ : ∀ {T U V W₁ W₂ W₃ A B A' B' C}
  → (p₁ : Path T) (p₂ : Path U) (p₃ : Path V)
  → (f : W₁ ⊢ B ⇐ A) 
  → {g : W₂ ⊢ A} {h : W₃ ⊢ A'}
  → {k : sub p₁ (sub p₂ (η B) ⊛ sub p₃ (η B')) ⊢ C}
  → cut⇐L (p₁ ++ (p₂ ◂ _)) f g (⇒L (p₁ ++ (_ ▸ p₃)) h k)
      ≗ ⇒L (p₁ ++ (_ ▸ p₃)) h (cut⇐L (p₁ ++ (p₂ ◂ _)) f g k)
cut⇐L⇒L-hass₂ {W₁ = W₁} {W₂} {W₃} {A} {B} {A'} {B'} p₁ p₂ p₃ (⇐R f) 
  rewrite subeq-2/\1 p₁ (W₃ ⊛ η (A' ⇒ B')) (η B) p₂ p₃ |
          subeq-2/\1 p₁ (W₃ ⊛ η (A' ⇒ B')) (η A) (p₂ ++ (W₁ ▸ ∙)) p₃ = refl
cut⇐L⇒L-hass₂ p₁ p₂ p₃ (⇒L p f f₁) = ⇒L refl (cut⇐L⇒L-hass₂ p₁ p₂ p₃ f₁) ∘ ⇒L⇒L₂ {p = p₁}
cut⇐L⇒L-hass₂ p₁ p₂ p₃ (⇐L p f f₁) = ⇐L refl (cut⇐L⇒L-hass₂ p₁ p₂ p₃ f₁) ∘ ⇐L⇒L₂ {p = p₁}
cut⇐L⇒L-hass₂ p₁ p₂ p₃ (⊗L p f) = ⊗L (cut⇐L⇒L-hass₂ p₁ p₂ p₃ f) ∘ ⊗L⇒L₂1/\2 {p = p₁}    

cut⇐L⇐L-hass₁ : ∀ {T U V W₁ W₂ W₃ A B A' B' C}
  → (p₁ : Path T) (p₂ : Path U) (p₃ : Path V)
  → (f : W₁ ⊢ B' ⇐ A') 
  → {g : W₂ ⊢ A} {h : W₃ ⊢ A'}
  → {k : sub p₁ (sub p₂ (η B) ⊛ sub p₃ (η B')) ⊢ C}
  → cut⇐L (p₁ ++ (_ ▸ p₃)) f h (⇐L (p₁ ++ (p₂ ◂ _)) g k)
      ≗ ⇐L (p₁ ++ (p₂ ◂ _)) g (cut⇐L (p₁ ++ (_ ▸ p₃)) f h k)
cut⇐L⇐L-hass₁ {W₁ = W₁} {W₂} {A = A} {B} {A'} {B'} p₁ p₂ p₃ (⇐R f) 
  rewrite subeq-1/\2 p₁ (η (B ⇐ A) ⊛ W₂) (η B') p₂ p₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ W₂) (η A') p₂ (p₃ ++ (W₁ ▸ ∙)) = refl
cut⇐L⇐L-hass₁ p₁ p₂ p₃ (⇒L p f f₁) = ⇒L refl (cut⇐L⇐L-hass₁ p₁ p₂ p₃ f₁) ∘ (~ ⇐L⇒L₂ {p = p₁})
cut⇐L⇐L-hass₁ p₁ p₂ p₃ (⇐L p f f₁) = ⇐L refl (cut⇐L⇐L-hass₁ p₁ p₂ p₃ f₁) ∘ (~ ⇐L⇐L₂ {p = p₁})
cut⇐L⇐L-hass₁ p₁ p₂ p₃ (⊗L p f) = ⊗L (cut⇐L⇐L-hass₁ p₁ p₂ p₃ f) ∘ ⊗L⇐L₂2/\1 {p = p₁}     

cut⇐L⇐L-hass₂ : ∀ {T U V W₁ W₂ W₃ A B A' B' C}
  → (p₁ : Path T) (p₂ : Path U) (p₃ : Path V)
  → (f : W₁ ⊢ B ⇐ A) 
  → {g : W₂ ⊢ A} {h : W₃ ⊢ A'}
  → {k : sub p₁ (sub p₂ (η B) ⊛ sub p₃ (η B')) ⊢ C}
  → cut⇐L (p₁ ++ (p₂ ◂ _)) f g (⇐L (p₁ ++ (_ ▸ p₃)) h k)
      ≗ ⇐L (p₁ ++ (_ ▸ p₃)) h (cut⇐L (p₁ ++ (p₂ ◂ _)) f g k)
cut⇐L⇐L-hass₂ {W₁ = W₁} {W₂} {W₃} {A} {B} {A'} {B'} p₁ p₂ p₃ (⇐R f) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ W₃) (η B) p₂ p₃ |
          subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ W₃) (η A) (p₂ ++ (W₁ ▸ ∙)) p₃ = refl
cut⇐L⇐L-hass₂ p₁ p₂ p₃ (⇒L p f f₁) = ⇒L refl (cut⇐L⇐L-hass₂ p₁ p₂ p₃ f₁) ∘ ⇒L⇐L₂ {p = p₁}
cut⇐L⇐L-hass₂ p₁ p₂ p₃ (⇐L p f f₁) = ⇐L refl (cut⇐L⇐L-hass₂ p₁ p₂ p₃ f₁) ∘ ⇐L⇐L₂ {p = p₁}
cut⇐L⇐L-hass₂ p₁ p₂ p₃ (⊗L p f) = ⊗L (cut⇐L⇐L-hass₂ p₁ p₂ p₃ f) ∘ ⊗L⇐L₂1/\2 {p = p₁}       