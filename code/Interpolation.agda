{-# OPTIONS --rewriting #-}

module Interpolation where

open import Relation.Binary.PropositionalEquality
open import Data.Product 
open import Fma
open import SeqCalc

-- =======================================
-- Maehara interpolation for NL
-- =======================================

record MIP (T : Tree) (p : Path T) (U : Tree) (C : Fma) : Set where
  constructor intrp
  field
    D : Fma
    g : sub p (η D) ⊢ C
    h : U ⊢ D


mip : ∀ {T} (p : Path T) U {V C}
  → (f : V ⊢ C) (eq : V ≡ sub p U) 
  → MIP T p U C
mip p _ (⇒R f) refl =
  let intrp D g h = mip (_ ▸ p) _ f refl
   in intrp D (⇒R g) h
mip p _ (⇐R f) refl = 
  let intrp D g h = mip (p ◂ _) _ f refl
   in intrp D (⇐R g) h
mip p U (⇒L p' f f') eq with subeq _ _ p p' (sym eq)
... | 2>L1 (gt q refl refl refl) = 
  let intrp D g h = mip p _ f' refl
  in intrp D g (⇒L (q ◂ _) f h)
... | 2>R1 (gt q refl refl refl) = 
  let intrp D g h = mip p _ f' refl
  in intrp D g (⇒L (_ ▸ q) f h)
... | 1/\2 (disj q q₁ q₂ refl refl refl refl) = 
  let intrp D g h = mip (q ++ (q₁ ◂ _)) U f' refl
  in intrp D (⇒L (q ++ (_ ▸ q₂)) f g) h
... | 2/\1 (disj q q₁ q₂ refl refl refl refl) =
  let intrp D g h = mip (q ++ (_ ▸ q₂)) _ f' refl
  in intrp D (⇒L (q ++ (q₁ ◂ _)) f g) h
... | 1≡2 (same refl refl refl) =
  let intrp D g h = mip p' _ f' refl
   in intrp D g (⇒L ∙ f h)
... | 1>L2 (gt q refl refl refl) =
  let intrp D g h = mip q _ f refl
   in intrp D (⇒L p' g f') h
... | 1>R2 (gt ∙ refl refl refl) = 
  let intrp D k l = mip ∙ _ f refl
      intrp E g h = mip p' _ f' refl
  in intrp (D ⇒ E) (⇒L p' l g) (⇒R (⇒L ∙ k h))
mip p _ (⇐L p' f f') eq with subeq _ _ p p' (sym eq)
... | 2>L1 (gt q refl refl refl) =
  let intrp D g h = mip p _ f' refl
   in intrp D g (⇐L (q ◂ _) f h)
... | 2>R1 (gt q refl refl refl) =
  let intrp D g h = mip p _ f' refl
   in intrp D g (⇐L (_ ▸ q) f h)
... | 1≡2 (same refl refl refl) =
  let intrp D g h = mip p' _ f' refl
   in intrp D g (⇐L ∙ f h)
... | 1>L2 (gt ∙ refl refl refl) =
  let intrp D k l = mip ∙ _ f refl
      intrp E g h = mip p' _ f' refl
   in intrp (E ⇐ D) (⇐L p' l g) (⇐R (⇐L ∙ k h))
... | 1>R2 (gt q refl refl refl) =
  let intrp D g h = mip q _ f refl
   in intrp D (⇐L p' g f') h
... | 1/\2 (disj q q₁ q₂ refl refl refl refl) =
  let intrp D g h = mip (q ++ (q₁ ◂ _)) _ f' refl
   in intrp D (⇐L (q ++ (_ ▸ q₂)) f g) h
... | 2/\1 (disj q q₁ q₂ refl refl refl refl) =
  let intrp D g h = mip (q ++ (_ ▸ q₂)) _ f' refl
   in intrp D (⇐L (q ++ (q₁ ◂ _)) f g) h
mip ∙ ._ (⊗R f f') refl = 
  let intrp D g h = mip ∙ _ f refl
      intrp E k l = mip ∙ _ f' refl
   in intrp (D ⊗ E) (⊗L ∙ (⊗R g k)) (⊗R h l)
mip (p ◂ U₁) U (⊗R f f') refl =
  let intrp D g h = mip p _ f refl
  in intrp D (⊗R g f') h
mip (T ▸ p) U (⊗R f f') refl =
  let intrp D g h = mip p _ f' refl
  in intrp D (⊗R f g) h
mip p U (⊗L p₁ f) eq with subeq _ _ p p₁ (sym eq)
... | 1≡2 (same refl refl refl) =
  let intrp D g h = mip p _ f refl
  in intrp D g (⊗L ∙ h)
... | 2>L1 (gt q refl refl refl) = 
  let intrp D g h = mip p _ f refl
  in intrp D g (⊗L (q ◂ _) h) 
... | 2>R1 (gt q refl refl refl) = 
  let intrp D g h = mip p _ f refl
  in intrp D g (⊗L (_ ▸ q) h) 
... | 1/\2 (disj q q₁ q₂ refl refl refl refl) =
  let intrp D g h = mip (q ++ (q₁ ◂ _)) _ f refl
  in intrp D (⊗L (q ++ (_ ▸ q₂)) g) h
... | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 
  let intrp D g h = mip (q ++ (_ ▸ q₂)) _ f refl
  in intrp D (⊗L (q ++ (q₁ ◂ _)) g) h
mip ∙ _ ax refl = intrp _ ax ax