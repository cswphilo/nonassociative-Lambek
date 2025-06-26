{-# OPTIONS --rewriting #-}

module Cut where

open import Fma
open import SeqCalc

-- =======================================
-- Cut admissibility for NL
-- =======================================

cut : ∀ {T U W C D} (p : Path T)
  → (f : U ⊢ D) (g : W ⊢ C)
  → (eq : W ≡ sub p (η D))
  → sub p U ⊢ C

cut⇐L : ∀ {T U V A B C} (p : Path T)
 → (f : U ⊢ B ⇐ A)
 → (g : V ⊢ A) (h : sub p (η B) ⊢ C)
 → sub p (U ⊛ V) ⊢ C
cut⇐L p (⇐R f) g h = cut (p ++ (_ ▸ ∙)) g (cut p f h refl) refl
cut⇐L p (⇒L p₁ f f₁) g h = ⇒L (p ++ (p₁ ◂ _)) f (cut⇐L p f₁ g h)
cut⇐L p (⇐L p₁ f f₁) g h = ⇐L (p ++ (p₁ ◂ _)) f (cut⇐L p f₁ g h)
cut⇐L p (⊗L p₁ f) g h = ⊗L (p ++ (p₁ ◂ _)) (cut⇐L p f g h)

cut⇒L : ∀ {T U V A B C} (p : Path T)
 → (f : U ⊢ A ⇒ B)
 → (g : V ⊢ A) (h : sub p (η B) ⊢ C)
 → sub p (V ⊛ U) ⊢ C
cut⇒L p (⇒R f) g h = cut (p ++ (∙ ◂ _)) g (cut p f h refl) refl
cut⇒L p (⇒L p₁ f f₁) g h = ⇒L (p ++ (_ ▸ p₁)) f (cut⇒L p f₁ g h)
cut⇒L p (⇐L p₁ f f₁) g h = ⇐L (p ++ (_ ▸ p₁)) f (cut⇒L p f₁ g h)
cut⇒L p (⊗L p₁ f) g h = ⊗L (p ++ (_ ▸ p₁)) (cut⇒L p f g h)

cut⊗L : ∀ {T U A B C} (p : Path T)
 → (f : U ⊢ (A ⊗ B)) (g : sub p (η A ⊛ η B) ⊢ C)
 → sub p U ⊢ C
cut⊗L p (⇒L p₁ f f₁) g = ⇒L (p ++ p₁) f (cut⊗L p f₁ g)
cut⊗L p (⇐L p₁ f f₁) g = ⇐L (p ++ p₁) f (cut⊗L p f₁ g)
cut⊗L p (⊗R f f₁) g = cut (p ++ (∙ ◂ _)) f (cut (p ++ (_ ▸ ∙)) f₁ g refl) refl
cut⊗L p (⊗L p₁ f) g = ⊗L (p ++ p₁) (cut⊗L p f g)

{-
Main proof of cut
-}

cut p f (⇒R g) refl = ⇒R (cut (_ ▸ p) f g refl)
cut p f (⇐R g) refl = ⇐R (cut (p ◂ _) f g refl)
cut p f (⇒L p₁ g g₁) eq with subeq _ _ p₁ p eq
cut ._ f (⇒L p₁ g g₁) refl | 2>L1 (gt q refl refl refl) = ⇒L p₁ (cut q f g refl) g₁
cut ._ f (⇒L p₁ g g₁) refl | 2>R1 (gt ∙ refl refl refl) = cut⇒L p₁ f g g₁
cut ._ f (⇒L ._ g g₁) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⇒L (q ++ (q₁ ◂ _)) g (cut (q ++ (_ ▸ q₂)) f g₁ refl)
cut ._ f (⇒L ._ g g₁) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⇒L (q ++ (_ ▸ q₂)) g (cut (q ++ (q₁ ◂ _)) f g₁ refl)
cut p f (⇐L p₁ g g₁) eq with subeq _ _ p₁ p eq
cut ._ f (⇐L p₁ g g₁) refl | 2>L1 (gt ∙ refl refl refl) = cut⇐L p₁ f g g₁
cut ._ f (⇐L p₁ g g₁) refl | 2>R1 (gt q refl refl refl) = ⇐L p₁ (cut q f g refl) g₁
cut ._ f (⇐L ._ g g₁) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⇐L (q ++ (q₁ ◂ _)) g (cut (q ++ (_ ▸ q₂)) f g₁ refl)
cut ._ f (⇐L ._ g g₁) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⇐L (q ++ (_ ▸ q₂)) g (cut (q ++ (q₁ ◂ _)) f g₁ refl)
cut (p ◂ U) f (⊗R g g₁) refl = ⊗R (cut p f g refl) g₁
cut (T ▸ p) f (⊗R g g₁) refl = ⊗R g (cut p f g₁ refl)
cut p f (⊗L p₁ g) eq with subeq _ _ p₁ p eq
cut p f (⊗L p g) refl | 1≡2 (same refl refl refl) = cut⊗L p f g
cut ._ f (⊗L ._ g) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⊗L (q ++ (q₁ ◂ _)) (cut (q ++ (_ ▸ q₂)) f g refl)
cut ._ f (⊗L ._ g) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⊗L (q ++ (_ ▸ q₂)) (cut (q ++ (q₁ ◂ _)) f g refl)
cut ∙ f ax refl = f 
