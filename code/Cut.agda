{-# OPTIONS --rewriting #-}

module Cut where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Empty
open import Fma
open import SeqCalc

-- =======================================
-- Cut admissibility for NL
-- =======================================

cut : ∀ {T U A C} (p : Path T)
  → (f : U ⊢ A) (g : sub p (η A) ⊢ C)
  → sub p U ⊢ C

cut⇒R : ∀ {T U W A B C} (p : Path T)
  → (f : η A ⊛ U ⊢ B) (g : W ⊢ C)
  → W ≡ sub p (η (A ⇒ B))
  → sub p U ⊢ C

cut⇐R : ∀ {T U W A B C} (p : Path T)
  → (f : U ⊛ η A ⊢ B) (g : W ⊢ C)
  → W ≡ sub p (η (B ⇐ A))
  → sub p U ⊢ C

cut⊗R : ∀ {T U V W A B C} (p : Path T)
  → (f : U ⊢ A) (f₁ : V ⊢ B)
  → (g : W ⊢ C)
  → W ≡ sub p (η (A ⊗ B))
  → sub p (U ⊛ V) ⊢ C

cut p (⇒R f) g = cut⇒R p f g refl
cut p (⇐R f) g = cut⇐R p f g refl
cut p (⇒L q f f') g = ⇒L (p ++ q) f (cut p f' g)
cut p (⇐L q f f') g = ⇐L (p ++ q) f (cut p f' g)
cut p (⊗L q f) g = ⊗L (p ++ q) (cut p f g)
cut p (⊗R f f') g = cut⊗R p f f' g refl
cut _ ax g = g

cut⇒R p f (⇒R g) refl = ⇒R (cut⇒R (_ ▸ p) f g refl)
cut⇒R p f (⇐R g) refl = ⇐R (cut⇒R (p ◂ _) f g refl)
cut⇒R p f (⇒L p' g g') eq with subeq _ _ p' p eq
... | 2>L1 (gt q refl refl refl) = ⇒L p' (cut⇒R q f g refl) g'
... | 2>R1 (gt ∙ refl refl refl) = cut p' (cut (∙ ◂ _) g f) g'
... | 1/\2 (disj q q₁ q₂ refl refl refl refl) =
  ⇒L (q ++ (q₁ ◂ _)) g (cut⇒R (q ++ (_ ▸ q₂)) f g' refl)
... | 2/\1 (disj q q₁ q₂ refl refl refl refl) =
  ⇒L (q ++ (_ ▸ q₂)) g (cut⇒R (q ++ (q₁ ◂ _)) f g' refl)
cut⇒R p f (⇐L p' g g') eq with subeq _ _ p' p eq
... | 2>L1 (gt ∙ refl () refl)
... | 2>R1 (gt q refl refl refl) = ⇐L p' (cut⇒R q f g refl) g'
... | 1/\2 (disj q q₁ q₂ refl refl refl refl) =
  ⇐L (q ++ (q₁ ◂ _)) g (cut⇒R (q ++ (_ ▸ q₂)) f g' refl)
... | 2/\1 (disj q q₁ q₂ refl refl refl refl) =
  ⇐L (q ++ (_ ▸ q₂)) g (cut⇒R (q ++ (q₁ ◂ _)) f g' refl)
cut⇒R (p ◂ U) f (⊗R g g') refl = ⊗R (cut⇒R p f g refl) g'
cut⇒R (T ▸ p) f (⊗R g g') refl = ⊗R g (cut⇒R p f g' refl)
cut⇒R p f (⊗L p' g) eq with subeq _ _ p' p eq
... | 1/\2 (disj q q₁ q₂ refl refl refl refl) = 
  ⊗L (q ++ (q₁ ◂ _)) (cut⇒R (q ++ (_ ▸ q₂)) f g refl)
... | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 
  ⊗L (q ++ (_ ▸ q₂)) (cut⇒R (q ++ (q₁ ◂ _)) f g refl)
cut⇒R ∙ f ax ()

cut⇐R p f (⇒R g) refl = ⇒R (cut⇐R (_ ▸ p) f g refl)
cut⇐R p f (⇐R g) refl = ⇐R (cut⇐R (p ◂ _) f g refl)
cut⇐R p f (⇒L p' g g') eq with subeq _ _ p' p eq
... | 2>L1 (gt q refl refl refl) = ⇒L p' (cut⇐R q f g refl) g' 
... | 2>R1 (gt ∙ refl () refl)
... | 1/\2 (disj q q₁ q₂ refl refl refl refl) =
  ⇒L (q ++ (q₁ ◂ _)) g (cut⇐R (q ++ (_ ▸ q₂)) f g' refl)
... | 2/\1 (disj q q₁ q₂ refl refl refl refl) =
  ⇒L (q ++ (_ ▸ q₂)) g (cut⇐R (q ++ (q₁ ◂ _)) f g' refl) 
cut⇐R p f (⇐L p' g g') eq with subeq _ _ p' p eq
... | 2>L1 (gt ∙ refl refl refl) = cut p' (cut (_ ▸ ∙) g f) g'
... | 2>R1 (gt q refl refl refl) = ⇐L p' (cut⇐R q f g refl) g' 
... | 1/\2 (disj q q₁ q₂ refl refl refl refl) =
  ⇐L (q ++ (q₁ ◂ _)) g (cut⇐R (q ++ (_ ▸ q₂)) f g' refl)
... | 2/\1 (disj q q₁ q₂ refl refl refl refl) =
  ⇐L (q ++ (_ ▸ q₂)) g (cut⇐R (q ++ (q₁ ◂ _)) f g' refl) 
cut⇐R (p ◂ U) f (⊗R g g') refl = ⊗R (cut⇐R p f g refl) g'
cut⇐R (T ▸ p) f (⊗R g g') refl = ⊗R g (cut⇐R p f g' refl)
cut⇐R p f (⊗L p' g) eq with subeq _ _ p' p eq
... | 1/\2 (disj q q₁ q₂ refl refl refl refl) = 
  ⊗L (q ++ (q₁ ◂ _)) (cut⇐R (q ++ (_ ▸ q₂)) f g refl)
... | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 
  ⊗L (q ++ (_ ▸ q₂)) (cut⇐R (q ++ (q₁ ◂ _)) f g refl)
cut⇐R ∙ f ax ()

cut⊗R p f f' (⇒R g) refl = ⇒R (cut⊗R (_ ▸ p) f f' g refl)
cut⊗R p f f' (⇐R g) refl = ⇐R (cut⊗R (p ◂ _) f f' g refl)
cut⊗R p f f' (⇒L p' g g') eq with subeq _ _ p' p eq
... | 2>L1 (gt q refl refl refl) = 
  ⇒L p' (cut⊗R q f f' g refl) g'
... | 2>R1 (gt ∙ refl () eqp)
... | 1/\2 (disj q q₁ q₂ refl refl refl refl) = 
  ⇒L (q ++ (q₁ ◂ _)) g (cut⊗R (q ++ (_ ▸ q₂)) f f' g' refl)
... | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 
  ⇒L (q ++ (_ ▸ q₂)) g (cut⊗R (q ++ (q₁ ◂ _)) f f' g' refl)
cut⊗R p f f' (⇐L p' g g') eq with subeq _ _ p' p eq
... | 2>L1 (gt ∙ refl () eqp)
... | 2>R1 (gt q refl refl refl) = 
  ⇐L p' (cut⊗R q f f' g refl) g'
... | 1/\2 (disj q q₁ q₂ refl refl refl refl) = 
  ⇐L (q ++ (q₁ ◂ _)) g (cut⊗R (q ++ (_ ▸ q₂)) f f' g' refl)
... | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 
  ⇐L (q ++ (_ ▸ q₂)) g (cut⊗R (q ++ (q₁ ◂ _)) f f' g' refl)
cut⊗R (p ◂ U) f f' (⊗R g g') refl = ⊗R (cut⊗R p f f' g refl) g'
cut⊗R (T ▸ p) f f' (⊗R g g') refl = ⊗R g (cut⊗R p f f' g' refl)
cut⊗R p f f' (⊗L p' g) eq with subeq _ _ p' p eq
... | 1≡2 (same refl refl refl) = 
  cut (p ++ (∙ ◂ _)) f (cut (p ++ (_ ▸ ∙)) f' g)
... | 1/\2 (disj q q₁ q₂ refl refl refl refl) = 
  ⊗L (q ++ (q₁ ◂ _)) (cut⊗R (q ++ (_ ▸ q₂)) f f' g refl)
... | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 
  ⊗L (q ++ (_ ▸ q₂)) (cut⊗R (q ++ (q₁ ◂ _))  f f' g refl)
cut⊗R ∙ f f' ax ()