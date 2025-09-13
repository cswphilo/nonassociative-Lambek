{-# OPTIONS --rewriting #-}

module CompltSound where 

open import Fma
open import SeqCalc
open import FCat
open import Cut
open import CutCongruence
open import FormulaeAxiom
open import Sound
open import Complt

⊗L* : ∀ {T} {C}
  → (f : T ⊢ C)
  → η [ T ] ⊢ C
⊗L* ax = ax
⊗L* (⇒R f) = ⇒R (cut ∙ (⊗R axA axA) (⊗L* f) refl)
⊗L* (⇐R f) = ⇐R (cut ∙ (⊗R axA axA) (⊗L* f) refl)
⊗L* (⇒L {U = U} {A} {B} p f g) = cut ∙ (complt (f2T[f] {U = U ⊛ η (A ⇒ B)} {η B} p (π⇒-1 id ∘ sound f ⊗ id))) (⊗L* g) refl
⊗L* (⇐L {U = U} {A} {B} p f g) = cut ∙ (complt (f2T[f] {U = η (B ⇐ A) ⊛ U} {η B} p (π⇐-1 id ∘ id ⊗ sound f))) (⊗L* g) refl
⊗L* (⊗R f g) = cut ∙ axA (⊗L ∙ (⊗R (⊗L* f) (⊗L* g))) refl
⊗L* (⊗L {A = A} {B} p f) = cut ∙ (complt (f2T[f] {U = η (A ⊗ B)} {η A ⊛ η B} p id)) (⊗L* f) refl

-- complt is a left inverse of sound.
compltsound : ∀ {T} {C} 
  → (f : T ⊢ C)
  → complt (sound f) ≗ ⊗L* f
compltsound ax = refl
compltsound (⇒R f) = ⇒R (cut-cong2 ∙ (⊗R axA axA) refl (compltsound f))
compltsound (⇐R f) = ⇐R (cut-cong2 ∙ (⊗R axA axA) refl (compltsound f))
compltsound (⇒L p f g) = cut-cong2 ∙ (complt (f2T[f] p (π⇒-1 id ∘ (sound f ⊗ id)))) refl (compltsound g)
compltsound (⇐L p f g) = cut-cong2 ∙ (complt (f2T[f] p (π⇐-1 id ∘ (id ⊗ sound f)))) refl (compltsound g)
compltsound (⊗R f g) = 
  ⊗L (⊗R (compltsound f ∘ (~ axA-cut-left-unit ∙ (⊗L* f) refl)) 
           (compltsound g ∘ (~ axA-cut-left-unit ∙ (⊗L* g) refl)))
compltsound (⊗L p f) = cut-cong2 ∙ (complt (f2T[f] p id)) refl (compltsound f)