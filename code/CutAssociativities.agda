{-# OPTIONS --rewriting #-}

module CutAssociativities where

open import Fma
open import SeqCalc
open import Cut
open import CutEqualities
open import SubEqProperties

{-
Associativity (cut-vass) and Commutativity (cut-hass) of Cut
-}

cut-vass : ∀ {T U V W₁ W₂ C D E} (p : Path T) (q : Path U)
  → (f : V ⊢ D) (g : W₁ ⊢ E) (h : W₂ ⊢ C)
  → (eq₁ : W₁ ≡ sub p (η D)) (eq₂ : W₂ ≡ sub q (η E))
  → cut q (cut p f g eq₁) h eq₂ ≡ cut (q ++ p) f (cut q g h eq₂) (cong (λ x → sub q x) eq₁)

cut⇒L-vass : ∀ {T U V W₁ W₂ W₃ A B C D} (p : Path T) (q : Path U)
  → (f : V ⊢ D) (g : W₁ ⊢ A ⇒ B) 
  → (h : W₂ ⊢ A) (k : W₃ ⊢ C)
  → (eq₁ : W₁ ≡ sub p (η D)) (eq₂ : W₃ ≡ sub q (η B))
  → cut⇒L q (cut p f g eq₁) h (subst-cxt eq₂ k) ≡ cut (q ++ (_ ▸ p)) f (cut⇒L q g h (subst-cxt eq₂ k)) (cong (λ x → sub q x) (cong₂ _⊛_ refl eq₁))

cut⇒L-cut⇒L-vass : ∀ {T U V W₁ W₂ A B A' B' C} (p : Path T) (q : Path U)
  → (f : V ⊢ A ⇒ B) (g : W₁ ⊢ A) (h : sub p (η B) ⊢ A' ⇒ B') (k : W₂ ⊢ A') (l : sub q (η B') ⊢ C)
  → cut⇒L q (cut⇒L p f g h) k l ≡ cut⇒L (q ++ (_ ▸ p)) f g (cut⇒L q h k l)
cut⇒L-cut⇒L-vass p q (⇒R f) g h k l = 
  trans (cut⇒L-vass (p ++ (∙ ◂ _)) q g (cut p f h refl) k l refl refl) 
        (cong (λ x → cut (q ++ (_ ▸ (p ++ (∙ ◂ _)))) g x refl) (cut⇒L-vass p q f h k l refl refl))
cut⇒L-cut⇒L-vass p q (⇒L p₁ f f₁) g h k l = cong (λ x → ⇒L (q ++ (_ ▸ (p ++ (_ ▸ p₁)))) f x) (cut⇒L-cut⇒L-vass p q f₁ g h k l)
cut⇒L-cut⇒L-vass p q (⇐L p₁ f f₁) g h k l = cong (λ x → ⇐L (q ++ (_ ▸ (p ++ (_ ▸ p₁)))) f x) (cut⇒L-cut⇒L-vass p q f₁ g h k l)
cut⇒L-cut⇒L-vass p q (⊗L p₁ f) g h k l = cong (λ x → ⊗L (q ++ (_ ▸ (p ++ (_ ▸ p₁)))) x) (cut⇒L-cut⇒L-vass p q f g h k l)

cut⇒L-cut⇐L-vass : ∀ {T U V W₁ W₂ A B A' B' C} (p : Path T) (q : Path U)
  → (f : V ⊢ B ⇐ A) (g : W₁ ⊢ A) (h : sub p (η B) ⊢ A' ⇒ B') (k : W₂ ⊢ A') (l : sub q (η B') ⊢ C)
  → cut⇒L q (cut⇐L p f g h) k l ≡ cut⇐L (q ++ (_ ▸ p)) f g (cut⇒L q h k l)
cut⇒L-cut⇐L-vass p q (⇐R f) g h k l = 
  trans (cut⇒L-vass (p ++ (_ ▸ ∙)) q g (cut p f h refl) k l refl refl) 
        (cong (λ x → cut (q ++ (_ ▸ (p ++ (_ ▸ ∙)))) g x refl) (cut⇒L-vass p q f h k l refl refl))
cut⇒L-cut⇐L-vass p q (⇒L p₁ f f₁) g h k l = cong (λ x → ⇒L (q ++ (_ ▸ (p ++ (p₁ ◂ _)))) f x) (cut⇒L-cut⇐L-vass p q f₁ g h k l)
cut⇒L-cut⇐L-vass p q (⇐L p₁ f f₁) g h k l = cong (λ x → ⇐L (q ++ (_ ▸ (p ++ (p₁ ◂ _)))) f x) (cut⇒L-cut⇐L-vass p q f₁ g h k l)
cut⇒L-cut⇐L-vass p q (⊗L p₁ f) g h k l = cong (λ x → ⊗L (q ++ (_ ▸ (p ++ (p₁ ◂ _)))) x) (cut⇒L-cut⇐L-vass p q f g h k l)

cut⇒L-cut⊗L-vass : ∀ {T U V W A B A' B' C} (p : Path T) (q : Path U)
  → (f : V ⊢ A ⊗ B) (g : sub p (η A ⊛ η B) ⊢ A' ⇒ B') (h : W ⊢ A') (k : sub q (η B') ⊢ C)
  → cut⇒L q (cut⊗L p f g) h k ≡ cut⊗L (q ++ (_ ▸ p)) f (cut⇒L q g h k)
cut⇒L-cut⊗L-vass p q (⇒L p₁ f f₁) g h k = cong (λ x → ⇒L (q ++ (_ ▸ (p ++ p₁))) f x) (cut⇒L-cut⊗L-vass p q f₁ g h k)
cut⇒L-cut⊗L-vass p q (⇐L p₁ f f₁) g h k = cong (λ x → ⇐L (q ++ (_ ▸ (p ++ p₁))) f x) (cut⇒L-cut⊗L-vass p q f₁ g h k)
cut⇒L-cut⊗L-vass p q (⊗R f f₁) g h k = 
  trans (cut⇒L-vass (p ++ (∙ ◂ _)) q f (cut (p ++ (_ ▸ ∙)) f₁ g refl) h k refl refl) 
        (cong (λ x → cut (q ++ (_ ▸ (p ++ (∙ ◂ _)))) f x refl)  (cut⇒L-vass (p ++ (_ ▸ ∙)) q f₁ g h k refl refl))       
cut⇒L-cut⊗L-vass p q (⊗L p₁ f) g h k = cong (λ x → ⊗L (q ++ (_ ▸ (p ++ p₁))) x) (cut⇒L-cut⊗L-vass p q f g h k)

cut⇐L-vass : ∀ {T U V W₁ W₂ W₃ A B C D} (p : Path T) (q : Path U)
  → (f : V ⊢ D) (g : W₁ ⊢ B ⇐ A) 
  → (h : W₂ ⊢ A) (k : W₃ ⊢ C)
  → (eq₁ : W₁ ≡ sub p (η D)) (eq₂ : W₃ ≡ sub q (η B))
  → cut⇐L q (cut p f g eq₁) h (subst-cxt eq₂ k) ≡ cut (q ++ (p ◂ _)) f (cut⇐L q g h (subst-cxt eq₂ k)) (cong (λ x → sub q x) (cong₂ _⊛_ eq₁ refl))

cut⇐L-cut⇒L-vass : ∀ {T U V W₁ W₂ A B A' B' C} (p : Path T) (q : Path U)
  → (f : V ⊢ A ⇒ B) (g : W₁ ⊢ A) (h : sub p (η B) ⊢ B' ⇐ A') (k : W₂ ⊢ A') (l : sub q (η B') ⊢ C)
  → cut⇐L q (cut⇒L p f g h) k l ≡ cut⇒L (q ++ (p ◂ _)) f g (cut⇐L q h k l)
cut⇐L-cut⇒L-vass p q (⇒R f) g h k l = 
  trans (cut⇐L-vass (p ++ (∙ ◂ _)) q g (cut p f h refl) k l refl refl) 
        (cong (λ x → cut (q ++ ((p ++ (∙ ◂ _)) ◂ _)) g x refl) (cut⇐L-vass p q f h k l refl refl))
cut⇐L-cut⇒L-vass p q (⇒L p₁ f f₁) g h k l = cong (λ x → ⇒L (q ++ ((p ++ (_ ▸ p₁)) ◂ _)) f x) (cut⇐L-cut⇒L-vass p q f₁ g h k l)
cut⇐L-cut⇒L-vass p q (⇐L p₁ f f₁) g h k l = cong (λ x → ⇐L (q ++ ((p ++ (_ ▸ p₁)) ◂ _)) f x) (cut⇐L-cut⇒L-vass p q f₁ g h k l)
cut⇐L-cut⇒L-vass p q (⊗L p₁ f) g h k l = cong (λ x → ⊗L (q ++ ((p ++ (_ ▸ p₁)) ◂ _)) x) (cut⇐L-cut⇒L-vass p q f g h k l)

cut⇐L-cut⇐L-vass : ∀ {T U V W₁ W₂ A B A' B' C} (p : Path T) (q : Path U)
  → (f : V ⊢ B ⇐ A) (g : W₁ ⊢ A) (h : sub p (η B) ⊢ B' ⇐ A') (k : W₂ ⊢ A') (l : sub q (η B') ⊢ C)
  → cut⇐L q (cut⇐L p f g h) k l ≡ cut⇐L (q ++ (p ◂ _)) f g (cut⇐L q h k l)
cut⇐L-cut⇐L-vass p q (⇐R f) g h k l = 
  trans (cut⇐L-vass (p ++ (_ ▸ ∙)) q g (cut p f h refl) k l refl refl) 
        (cong (λ x → cut (q ++ ((p ++ (_ ▸ ∙)) ◂ _)) g x refl) (cut⇐L-vass p q f h k l refl refl))
cut⇐L-cut⇐L-vass p q (⇒L p₁ f f₁) g h k l = cong (λ x → ⇒L (q ++ ((p ++ (p₁ ◂ _)) ◂ _)) f x) (cut⇐L-cut⇐L-vass p q f₁ g h k l)
cut⇐L-cut⇐L-vass p q (⇐L p₁ f f₁) g h k l = cong (λ x → ⇐L (q ++ ((p ++ (p₁ ◂ _)) ◂ _)) f x) (cut⇐L-cut⇐L-vass p q f₁ g h k l)
cut⇐L-cut⇐L-vass p q (⊗L p₁ f) g h k l = cong (λ x → ⊗L (q ++ ((p ++ (p₁ ◂ _)) ◂ _)) x) (cut⇐L-cut⇐L-vass p q f g h k l)

cut⇐L-cut⊗L-vass : ∀ {T U V W A B A' B' C} (p : Path T) (q : Path U)
  → (f : V ⊢ A ⊗ B) (g : sub p (η A ⊛ η B) ⊢ B' ⇐ A') (h : W ⊢ A') (k : sub q (η B') ⊢ C)
  → cut⇐L q (cut⊗L p f g) h k ≡ cut⊗L (q ++ (p ◂ _)) f (cut⇐L q g h k)
cut⇐L-cut⊗L-vass p q (⇒L p₁ f f₁) g h k = cong (λ x → ⇒L (q ++ ((p ++ p₁) ◂ _)) f x) (cut⇐L-cut⊗L-vass p q f₁ g h k)
cut⇐L-cut⊗L-vass p q (⇐L p₁ f f₁) g h k = cong (λ x → ⇐L (q ++ ((p ++ p₁) ◂ _)) f x) (cut⇐L-cut⊗L-vass p q f₁ g h k)
cut⇐L-cut⊗L-vass p q (⊗R f f₁) g h k = 
  trans (cut⇐L-vass (p ++ (∙ ◂ _)) q f (cut (p ++ (_ ▸ ∙)) f₁ g refl) h k refl refl) 
        (cong (λ x → cut (q ++ ((p ++ (∙ ◂ _)) ◂ _)) f x refl)  (cut⇐L-vass (p ++ (_ ▸ ∙)) q f₁ g h k refl refl))       
cut⇐L-cut⊗L-vass p q (⊗L p₁ f) g h k = cong (λ x → ⊗L (q ++ ((p ++ p₁) ◂ _)) x) (cut⇐L-cut⊗L-vass p q f g h k)

cut⊗L-vass : ∀ {T U V W₁ W₂ A B C D} (p : Path T) (q : Path U)
  → (f : V ⊢ D) (g : W₁ ⊢ A ⊗ B) (h : W₂ ⊢ C)
  → (eq₁ : W₁ ≡ sub p (η D)) (eq₂ : W₂ ≡ sub q (η A ⊛ η B))
  → cut⊗L q (cut p f g eq₁) (subst-cxt eq₂ h) ≡ cut (q ++ p) f (cut⊗L q g (subst-cxt eq₂ h)) (cong (λ x → (sub q x)) eq₁)

cut⊗L-cut⇒L-vass : ∀ {T U V W A B A' B' C} (p : Path T) (q : Path U)
  → (f : V ⊢ A ⇒ B) (g : W ⊢ A) (h : sub p (η B) ⊢ A' ⊗ B') (k : sub q (η A' ⊛ η B') ⊢ C)
  → cut⊗L q (cut⇒L p f g h) k ≡ cut⇒L (q ++ p) f g (cut⊗L q h k)
cut⊗L-cut⇒L-vass p q (⇒R f) g h k = 
  trans (cut⊗L-vass (p ++ (∙ ◂ _)) q g (cut p f h refl) k refl refl) 
        (cong (λ x → cut (q ++ (p ++ (∙ ◂ _))) g x refl) (cut⊗L-vass p q f h k refl refl))
cut⊗L-cut⇒L-vass p q (⇒L p₁ f f₁) g h k = cong (λ x → ⇒L (q ++ (p ++ (_ ▸ p₁))) f x) (cut⊗L-cut⇒L-vass p q f₁ g h k)
cut⊗L-cut⇒L-vass p q (⇐L p₁ f f₁) g h k = cong (λ x → ⇐L (q ++ (p ++ (_ ▸ p₁))) f x) (cut⊗L-cut⇒L-vass p q f₁ g h k)
cut⊗L-cut⇒L-vass p q (⊗L p₁ f) g h k = cong (λ x → ⊗L (q ++ (p ++ (_ ▸ p₁))) x) (cut⊗L-cut⇒L-vass p q f g h k)

cut⊗L-cut⇐L-vass : ∀ {T U V W A B A' B' C} (p : Path T) (q : Path U)
  → (f : V ⊢ B ⇐ A) (g : W ⊢ A) (h : sub p (η B) ⊢ A' ⊗ B') (k : sub q (η A' ⊛ η B') ⊢ C)
  → cut⊗L q (cut⇐L p f g h) k ≡ cut⇐L (q ++ p) f g (cut⊗L q h k)
cut⊗L-cut⇐L-vass p q (⇐R f) g h k = 
  trans (cut⊗L-vass (p ++ (_ ▸ ∙)) q g (cut p f h refl) k refl refl) 
        (cong (λ x → cut (q ++ (p ++ (_ ▸ ∙))) g x refl) (cut⊗L-vass p q f h k refl refl))
cut⊗L-cut⇐L-vass p q (⇒L p₁ f f₁) g h k = cong (λ x → ⇒L (q ++ (p ++ (p₁ ◂ _))) f x) (cut⊗L-cut⇐L-vass p q f₁ g h k)
cut⊗L-cut⇐L-vass p q (⇐L p₁ f f₁) g h k = cong (λ x → ⇐L (q ++ (p ++ (p₁ ◂ _))) f x) (cut⊗L-cut⇐L-vass p q f₁ g h k)
cut⊗L-cut⇐L-vass p q (⊗L p₁ f) g h k = cong (λ x → ⊗L (q ++ (p ++ (p₁ ◂ _))) x) (cut⊗L-cut⇐L-vass p q f g h k)

cut⊗L-cut⊗L-vass : ∀ {T U V A B A' B' C} (p : Path T) (q : Path U)
  → (f : V ⊢ A ⊗ B) (g : sub p (η A ⊛ η B) ⊢ A' ⊗ B') (h : sub q (η A' ⊛ η B') ⊢ C)
  → cut⊗L q (cut⊗L p f g) h ≡ cut⊗L (q ++ p) f (cut⊗L q g h)
cut⊗L-cut⊗L-vass p q (⇒L p₁ f f₁) g h = cong (λ x → ⇒L (q ++ (p ++ p₁)) f x) (cut⊗L-cut⊗L-vass p q f₁ g h)
cut⊗L-cut⊗L-vass p q (⇐L p₁ f f₁) g h = cong (λ x → ⇐L (q ++ (p ++ p₁)) f x) (cut⊗L-cut⊗L-vass p q f₁ g h)
cut⊗L-cut⊗L-vass p q (⊗R f f₁) g h = 
  trans (cut⊗L-vass (p ++ (∙ ◂ _)) q f (cut (p ++ (_ ▸ ∙)) f₁ g refl) h refl refl) 
        (cong (λ x → cut (q ++ (p ++ (∙ ◂ _))) f x refl) (cut⊗L-vass (p ++ (_ ▸ ∙)) q f₁ g h refl refl))
cut⊗L-cut⊗L-vass p q (⊗L p₁ f) g h = cong (λ x → ⊗L (q ++ (p ++ p₁)) x) (cut⊗L-cut⊗L-vass p q f g h)

cut-hass : ∀ {T U V W₁ W₂ W₃ C D E} (p₁ : Path W₁) (p₂ : Path W₂) (p₃ : Path W₃)
  → (f : T ⊢ D) (g : U ⊢ E) (h : V ⊢ C)
  → (eq : V ≡ sub p₁ (sub p₂ (η D) ⊛ sub p₃ (η E)))
  → cut (p₁ ++ (p₂ ◂ _)) f (cut (p₁ ++ (_ ▸ p₃)) g h eq) refl ≡ cut (p₁ ++ (_ ▸ p₃)) g (cut (p₁ ++ (p₂ ◂ _)) f h eq) refl

cut⇒L-hass₁ : ∀ {T U V W₁ W₂ W₃ A B C E} (p₁ : Path W₁) (p₂ : Path W₂) (p₃ : Path W₃)
  → (f : T ⊢ A ⇒ B) (g : U ⊢ E) (h : V ⊢ A) 
  → (k : sub p₁ (sub p₂ (η B) ⊛ sub p₃ (η E)) ⊢ C)
  → cut⇒L (p₁ ++ (p₂ ◂ _)) f h (cut (p₁ ++ (_ ▸ p₃)) g k refl)
      ≡ cut (p₁ ++ (_ ▸ p₃)) g (cut⇒L (p₁ ++ (p₂ ◂ _)) f h k) refl
cut⇒L-hass₁ p₁ p₂ p₃ (⇒R f) g h k = 
  trans (cong (λ x → cut (p₁ ++ ((p₂ ++ (∙ ◂ _)) ◂ _)) h x refl) (cut-hass p₁ p₂ p₃ f g k refl)) 
        (cut-hass p₁ (p₂ ++ (∙ ◂ _)) p₃ h g (cut (p₁ ++ (p₂ ◂ _)) f k refl) refl)
cut⇒L-hass₁ {V = V} {E = E} p₁ p₂ p₃ (⇒L {U = U} {A = A} {B} p f f₁) g h k 
  rewrite subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η E) (p₂ ++ (V ▸ p)) p₃ = 
    cong (λ x → ⇒L (p₁ ++ ((p₂ ++ (_ ▸ p)) ◂ _)) f x) (cut⇒L-hass₁ p₁ p₂ p₃ f₁ g h k)
cut⇒L-hass₁ {V = V} {E = E} p₁ p₂ p₃ (⇐L {U = U} {A = A} {B} p f f₁) g h k 
  rewrite subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η E) (p₂ ++ (V ▸ p)) p₃ = 
    cong (λ x → ⇐L (p₁ ++ ((p₂ ++ (_ ▸ p)) ◂ _)) f x) (cut⇒L-hass₁ p₁ p₂ p₃ f₁ g h k)
cut⇒L-hass₁ {V = V} {E = E} p₁ p₂ p₃ (⊗L {A = A} {B} p f) g h k 
  rewrite subeq-1/\2 p₁ (η (A ⊗ B)) (η E) (p₂ ++ (V ▸ p)) p₃ =
    cong (λ x → ⊗L (p₁ ++ ((p₂ ++ (_ ▸ p)) ◂ _)) x) (cut⇒L-hass₁ p₁ p₂ p₃ f g h k)

cut⇒L-hass₂ : ∀ {T U V W₁ W₂ W₃ A B C D} (p₁ : Path W₁) (p₂ : Path W₂) (p₃ : Path W₃)
  → (f : T ⊢ D) (g : U ⊢ A ⇒ B)(h : V ⊢ A) 
  → (k : sub p₁ (sub p₂ (η D) ⊛ sub p₃ (η B)) ⊢ C)
  → cut⇒L (p₁ ++ (_ ▸ p₃)) g h (cut (p₁ ++ (p₂ ◂ _)) f k refl)
      ≡ cut (p₁ ++ (p₂ ◂ _)) f (cut⇒L (p₁ ++ (_ ▸ p₃)) g h k) refl
cut⇒L-hass₂ p₁ p₂ p₃ f (⇒R g) h k = 
  sym (trans (cut-hass p₁ p₂ (p₃ ++ (∙ ◂ _)) f h (cut (p₁ ++ (_ ▸ p₃)) g k refl) refl) 
             (cong (λ x → cut (p₁ ++ (_ ▸ (p₃ ++ (∙ ◂ _)))) h x refl) (cut-hass p₁ p₂ p₃ f g k refl)))
cut⇒L-hass₂ {V = V} {D = D} p₁ p₂ p₃ f (⇒L {U = U} {A} {B} p g g₁) h k
  rewrite subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η D) p₂ (p₃ ++ (V ▸ p)) = 
    cong (λ x → ⇒L (p₁ ++ (_ ▸ (p₃ ++ (_ ▸ p)))) g x) (cut⇒L-hass₂ p₁ p₂ p₃ f g₁ h k)
cut⇒L-hass₂ {V = V} {D = D} p₁ p₂ p₃ f (⇐L {U = U} {A} {B} p g g₁) h k
  rewrite subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η D) p₂ (p₃ ++ (V ▸ p)) = 
    cong (λ x → ⇐L (p₁ ++ (_ ▸ (p₃ ++ (_ ▸ p)))) g x) (cut⇒L-hass₂ p₁ p₂ p₃ f g₁ h k)
cut⇒L-hass₂ {V = V} {D = D} p₁ p₂ p₃ f (⊗L {A = A} {B} p g) h k
  rewrite subeq-2/\1 p₁ (η (A ⊗ B)) (η D) p₂ (p₃ ++ (V ▸ p)) = 
    cong (λ x → ⊗L (p₁ ++ (_ ▸ (p₃ ++ (_ ▸ p)))) x) (cut⇒L-hass₂ p₁ p₂ p₃ f g h k)

cut⇒L-hass₃ : ∀ {T U W₁ W₂ A B C D} (p : Path W₁) (q : Path W₂)
  → (f : T ⊢ D) (g : U ⊢ A ⇒ B) 
  → (h : sub p (η D) ⊢ A) (k : sub q (η B) ⊢ C)
  → cut⇒L q g (cut p f h refl) k 
      ≡ cut (q ++ (p ◂ _)) f (cut⇒L q g h k) refl
cut⇒L-hass₃ p q f (⇒R g) h k = cut-vass p (q ++ (∙ ◂ _)) f h (cut q g k refl) refl refl
cut⇒L-hass₃ {D = D} p q f (⇒L {U = U} {A} {B} p₁ g g₁) h k 
  rewrite subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η D) p p₁ = cong (λ x → ⇒L (q ++ (_ ▸ p₁)) g x) (cut⇒L-hass₃ p q f g₁ h k)
cut⇒L-hass₃ {D = D} p q f (⇐L {U = U} {A} {B} p₁ g g₁) h k 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η D) p p₁ = cong (λ x → ⇐L (q ++ (_ ▸ p₁)) g x) (cut⇒L-hass₃ p q f g₁ h k)
cut⇒L-hass₃ {D = D} p q f (⊗L {A = A} {B} p₁ g) h k 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η D) p p₁ = cong (λ x → ⊗L (q ++ (_ ▸ p₁)) x) (cut⇒L-hass₃ p q f g h k)

cut⇐L-hass₁ : ∀ {T U V W₁ W₂ W₃ A B C E} (p₁ : Path W₁) (p₂ : Path W₂) (p₃ : Path W₃)
  → (f : T ⊢ B ⇐ A) (g : U ⊢ E) (h : V ⊢ A) 
  → (k : sub p₁ (sub p₂ (η B) ⊛ sub p₃ (η E)) ⊢ C)
  → cut⇐L (p₁ ++ (p₂ ◂ _)) f h (cut (p₁ ++ (_ ▸ p₃)) g k refl)
      ≡ cut (p₁ ++ (_ ▸ p₃)) g (cut⇐L (p₁ ++ (p₂ ◂ _)) f h k) refl
cut⇐L-hass₁ p₁ p₂ p₃ (⇐R f) g h k = 
  trans (cong (λ x → cut (p₁ ++ ((p₂ ++ (_ ▸ ∙)) ◂ _)) h x refl) (cut-hass p₁ p₂ p₃ f g k refl)) 
        (cut-hass p₁ (p₂ ++ (_ ▸ ∙)) p₃ h g (cut (p₁ ++ (p₂ ◂ _)) f k refl) refl)
cut⇐L-hass₁ {V = V} {E = E} p₁ p₂ p₃ (⇒L {U = U} {A = A} {B} p f f₁) g h k 
  rewrite subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η E) (p₂ ++ (p ◂ V)) p₃ = 
    cong (λ x → ⇒L (p₁ ++ ((p₂ ++ (p ◂ _)) ◂ _)) f x) (cut⇐L-hass₁ p₁ p₂ p₃ f₁ g h k)
cut⇐L-hass₁ {V = V} {E = E} p₁ p₂ p₃ (⇐L {U = U} {A = A} {B} p f f₁) g h k 
  rewrite subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η E) (p₂ ++ (p ◂ V)) p₃ = 
    cong (λ x → ⇐L (p₁ ++ ((p₂ ++ (p ◂ _)) ◂ _)) f x) (cut⇐L-hass₁ p₁ p₂ p₃ f₁ g h k)
cut⇐L-hass₁ {V = V} {E = E} p₁ p₂ p₃ (⊗L {A = A} {B} p f) g h k 
  rewrite subeq-1/\2 p₁ (η (A ⊗ B)) (η E) (p₂ ++ (p ◂ V)) p₃ =
    cong (λ x → ⊗L (p₁ ++ ((p₂ ++ (p ◂ _)) ◂ _)) x) (cut⇐L-hass₁ p₁ p₂ p₃ f g h k)

cut⇐L-hass₂ : ∀ {T U V W₁ W₂ W₃ A B C D} (p₁ : Path W₁) (p₂ : Path W₂) (p₃ : Path W₃)
  → (f : T ⊢ D) (g : U ⊢ B ⇐ A) (h : V ⊢ A) 
  → (k : sub p₁ (sub p₂ (η D) ⊛ sub p₃ (η B)) ⊢ C)
  → cut⇐L (p₁ ++ (_ ▸ p₃)) g h (cut (p₁ ++ (p₂ ◂ _)) f k refl)
      ≡ cut (p₁ ++ (p₂ ◂ _)) f (cut⇐L (p₁ ++ (_ ▸ p₃)) g h k) refl
cut⇐L-hass₂ p₁ p₂ p₃ f (⇐R g) h k = 
  sym (trans (cut-hass p₁ p₂ (p₃ ++ (_ ▸ ∙)) f h (cut (p₁ ++ (_ ▸ p₃)) g k refl) refl )
             (cong (λ x → cut (p₁ ++ (_ ▸ (p₃ ++ (_ ▸ ∙)))) h x refl) (cut-hass p₁ p₂ p₃ f g k refl)))
cut⇐L-hass₂ {V = V} {D = D} p₁ p₂ p₃ f (⇒L {U = U} {A} {B} p g g₁) h k
  rewrite subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η D) p₂ (p₃ ++ (p ◂ V)) = 
    cong (λ x → ⇒L (p₁ ++ (_ ▸ (p₃ ++ (p ◂ _)))) g x) (cut⇐L-hass₂ p₁ p₂ p₃ f g₁ h k)
cut⇐L-hass₂ {V = V} {D = D} p₁ p₂ p₃ f (⇐L {U = U} {A} {B} p g g₁) h k
  rewrite subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η D) p₂ (p₃ ++ (p ◂ V)) = 
    cong (λ x → ⇐L (p₁ ++ (_ ▸ (p₃ ++ (p ◂ _)))) g x) (cut⇐L-hass₂ p₁ p₂ p₃ f g₁ h k)
cut⇐L-hass₂ {V = V} {D = D} p₁ p₂ p₃ f (⊗L {A = A} {B} p g) h k
  rewrite subeq-2/\1 p₁ (η (A ⊗ B)) (η D) p₂ (p₃ ++ (p ◂ V)) = 
    cong (λ x → ⊗L (p₁ ++ (_ ▸ (p₃ ++ (p ◂ _)))) x) (cut⇐L-hass₂ p₁ p₂ p₃ f g h k)

cut⇐L-hass₃ : ∀ {T U W₁ W₂ A B C E} (p : Path W₁) (q : Path W₂)
  → (f : T ⊢ B ⇐ A) (g : U ⊢ E) 
  → (h : sub p (η E) ⊢ A) (k : sub q (η B) ⊢ C)
  → cut⇐L q f (cut p g h refl) k 
      ≡ cut (q ++ (_ ▸ p)) g (cut⇐L q f h k) refl
cut⇐L-hass₃ p q (⇐R f) g h k = cut-vass p (q ++ (_ ▸ ∙)) g h (cut q f k refl) refl refl
cut⇐L-hass₃ {E = E} p q (⇒L {U = U} {A} {B} p₁ f f₁) g h k 
  rewrite subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η E) p₁ p = cong (λ x → ⇒L (q ++ (p₁ ◂ _)) f x) (cut⇐L-hass₃ p q f₁ g h k)
cut⇐L-hass₃ {E = E} p q (⇐L {U = U} {A} {B} p₁ f f₁) g h k 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η E) p₁ p = cong (λ x → ⇐L (q ++ (p₁ ◂ _)) f x) (cut⇐L-hass₃ p q f₁ g h k)
cut⇐L-hass₃ {E = E} p q (⊗L {A = A} {B} p₁ f) g h k 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η E) p₁ p = cong (λ x → ⊗L (q ++ (p₁ ◂ _)) x) (cut⇐L-hass₃ p q f g h k)

cut⊗L-hass₁ : ∀ {T U W₁ W₂ W₃ A B C E} (p₁ : Path W₁) (p₂ : Path W₂) (p₃ : Path W₃)
  → (f : T ⊢ E) (g : U ⊢ A ⊗ B) (h : sub p₁ (sub p₂ (η A ⊛ η B) ⊛ sub p₃ (η E)) ⊢ C)
  → cut⊗L (p₁ ++ (p₂ ◂ _)) g (cut (p₁ ++ (_ ▸ p₃)) f h refl) 
    ≡ cut (p₁ ++ (_ ▸ p₃)) f (cut⊗L (p₁ ++ (p₂ ◂ _)) g h) refl
cut⊗L-hass₁ {E = E} p₁ p₂ p₃ f (⇒L {U = U} {A} {B} p g g₁) h 
  rewrite subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η E) (p₂ ++ p) p₃ = cong (λ x → ⇒L (p₁ ++ ((p₂ ++ p) ◂ _)) g x) (cut⊗L-hass₁ p₁ p₂ p₃ f g₁ h)
cut⊗L-hass₁ {E = E} p₁ p₂ p₃ f (⇐L {U = U} {A} {B} p g g₁) h 
  rewrite subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η E) (p₂ ++ p) p₃ = cong (λ x → ⇐L (p₁ ++ ((p₂ ++ p) ◂ _)) g x) (cut⊗L-hass₁ p₁ p₂ p₃ f g₁ h)
cut⊗L-hass₁ p₁ p₂ p₃ f (⊗R g g₁) h = 
  trans (cong (λ x → cut (p₁ ++ ((p₂ ++ (∙ ◂ _)) ◂ _)) g x refl) (cut-hass p₁ (p₂ ++ (_ ▸ ∙)) p₃ g₁ f h refl)) 
             (cut-hass p₁ (p₂ ++ (∙ ◂ _)) p₃ g f (cut (p₁ ++ ((p₂ ++ (_ ▸ ∙)) ◂ _)) g₁ h refl) refl)
cut⊗L-hass₁ {E = E} p₁ p₂ p₃ f (⊗L {A = A} {B} p g) h 
  rewrite subeq-1/\2 p₁ (η (A ⊗ B)) (η E) (p₂ ++ p) p₃ = cong (λ x → ⊗L (p₁ ++ ((p₂ ++ p) ◂ _)) x) (cut⊗L-hass₁ p₁ p₂ p₃ f g h)

cut⊗L-hass₂ : ∀ {T U W₁ W₂ W₃ A B C D} (p₁ : Path W₁) (p₂ : Path W₂) (p₃ : Path W₃)
  → (f : T ⊢ D) (g : U ⊢ A ⊗ B) (h : sub p₁ (sub p₂ (η D) ⊛ sub p₃ (η A ⊛ η B)) ⊢ C)
  → cut⊗L (p₁ ++ (_ ▸ p₃)) g (cut (p₁ ++ (p₂ ◂ _)) f h refl) 
    ≡ cut (p₁ ++ (p₂ ◂ _)) f (cut⊗L (p₁ ++ (_ ▸ p₃)) g h) refl
cut⊗L-hass₂ {D = D} p₁ p₂ p₃ f (⇒L {U = U} {A} {B} p g g₁) h 
  rewrite subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η D) p₂ (p₃ ++ p) = cong (λ x → ⇒L (p₁ ++ (_ ▸ (p₃ ++ p))) g x) (cut⊗L-hass₂ p₁ p₂ p₃ f g₁ h)
cut⊗L-hass₂ {D = D} p₁ p₂ p₃ f (⇐L {U = U} {A} {B} p g g₁) h 
  rewrite subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η D) p₂ (p₃ ++ p) = cong (λ x → ⇐L (p₁ ++ (_ ▸ (p₃ ++ p))) g x) (cut⊗L-hass₂ p₁ p₂ p₃ f g₁ h)
cut⊗L-hass₂ p₁ p₂ p₃ f (⊗R g g₁) h = 
  sym (trans (cut-hass p₁ p₂ (p₃ ++ (∙ ◂ _)) f g (cut (p₁ ++ (_ ▸ (p₃ ++ (_ ▸ ∙)))) g₁ h refl) refl) 
             (cong (λ x → cut (p₁ ++ (_ ▸ (p₃ ++ (∙ ◂ _)))) g x refl) (cut-hass p₁ p₂ (p₃ ++ (_ ▸ ∙))  f g₁ h refl)))
cut⊗L-hass₂ {D = D} p₁ p₂ p₃ f (⊗L {A = A} {B} p g) h 
  rewrite subeq-2/\1 p₁ (η (A ⊗ B)) (η D) p₂ (p₃ ++ p) = cong (λ x → ⊗L (p₁ ++ (_ ▸ (p₃ ++ p))) x) (cut⊗L-hass₂ p₁ p₂ p₃ f g h)


{-
Proof of cut-vass
-}

cut-vass p q f g (⇒R h) refl refl = cong ⇒R (cut-vass p (_ ▸ q) f g h refl refl)
cut-vass p q f g (⇐R h) refl refl = cong ⇐R (cut-vass p (q ◂ _) f g h refl refl)
cut-vass p q f g (⇒L p₁ h h₁) eq₁ eq₂ with subeq _ _ p₁ q eq₂
cut-vass {D = D} p q f g (⇒L {A = A} {B} p₁ h h₁) refl refl | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η D) (q₁ ++ p) = 
  cong (λ x → ⇒L p₁ x h₁) (cut-vass p q₁ f g h refl refl)
cut-vass p q f g (⇒L p₁ h h₁) refl refl | 2>R1 (gt ∙ refl refl refl) = cut⇒L-vass p p₁ f g h h₁ refl refl
cut-vass {D = D} p q f g (⇒L {U = U} {A} {B} p₁ h h₁) refl refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (U ⊛ η (A ⇒ B)) (η D) q₂ (q₃ ++ p) = 
    cong (λ x → ⇒L (q₁ ++ (q₂ ◂ _)) h x) (cut-vass p (q₁ ++ (_ ▸ q₃)) f g h₁ refl refl)
cut-vass {D = D} p q f g (⇒L {U = U} {A} {B} p₁ h h₁) refl refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (U ⊛ η (A ⇒ B)) (η D) (q₂ ++ p) q₃ = 
    cong (λ x → ⇒L (q₁ ++ (_ ▸ q₃)) h x) (cut-vass p (q₁ ++ (q₂ ◂ _)) f g h₁ refl refl)
cut-vass p q f g (⇐L p₁ h h₁) eq₁ eq₂ with subeq _ _ p₁ q eq₂
cut-vass p q f g (⇐L p₁ h h₁) refl refl | 2>L1 (gt ∙ refl refl refl) = cut⇐L-vass p p₁ f g h h₁ refl refl
cut-vass {D = D} p q f g (⇐L {A = A} {B} p₁ h h₁) refl refl | 2>R1 (gt q₁ refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η D) (q₁ ++ p) = 
  cong (λ x → ⇐L p₁ x h₁) (cut-vass p q₁ f g h refl refl)
cut-vass {D = D} p q f g (⇐L {U = U} {A} {B} p₁ h h₁) refl refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (B ⇐ A) ⊛ U) (η D) q₂ (q₃ ++ p) = 
    cong (λ x → ⇐L (q₁ ++ (q₂ ◂ _)) h x) (cut-vass p (q₁ ++ (_ ▸ q₃)) f g h₁ refl refl)
cut-vass {D = D} p q f g (⇐L {U = U} {A} {B} p₁ h h₁) refl refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (B ⇐ A) ⊛ U) (η D) (q₂ ++ p) q₃ = 
    cong (λ x → ⇐L (q₁ ++ (_ ▸ q₃)) h x) (cut-vass p (q₁ ++ (q₂ ◂ _)) f g h₁ refl refl)
cut-vass p (q ◂ U) f g (⊗R h h₁) refl refl = cong₂ ⊗R (cut-vass p q f g h refl refl) refl
cut-vass p (T ▸ q) f g (⊗R h h₁) refl refl = cong₂ ⊗R refl (cut-vass p q f g h₁ refl refl)
cut-vass p q f g (⊗L p₁ h) eq₁ eq₂ with subeq _ _ p₁ q eq₂
cut-vass p q f g (⊗L p₁ h) refl refl | 1≡2 (same refl refl refl) = cut⊗L-vass p q f g h refl refl
cut-vass {D = D} p q f g (⊗L {A = A} {B} p₁ h) refl refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 q₁ (η (A ⊗ B)) (η D) q₂ (q₃ ++ p) = 
    cong (λ x → ⊗L (q₁ ++ (q₂ ◂ _)) x) (cut-vass p (q₁ ++ (_ ▸ q₃)) f g h refl refl)
cut-vass {D = D} p q f g (⊗L {A = A} {B} p₁ h) refl refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (A ⊗ B)) (η D) (q₂ ++ p) q₃ = 
    cong (λ x → ⊗L (q₁ ++ (_ ▸ q₃)) x) (cut-vass p (q₁ ++ (q₂ ◂ _)) f g h refl refl)
cut-vass p ∙ f g ax refl refl = refl


cut⇒L-vass p q f (⇒R g) h k refl refl = 
  trans (cong (λ x → cut (q ++ (∙ ◂ _)) h x refl) (cut-vass (_ ▸ p) q f g k refl refl)) 
        (cut-hass q ∙ p h f (cut q g k refl) refl)
cut⇒L-vass p q f (⇒L p₁ g g₁) h k eq₁ refl with subeq _ _ p₁ p eq₁
cut⇒L-vass {W₂ = W₂} {D = D} p q f (⇒L {A = A} {B} p₁ g g₁) h k refl refl | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 (q ++ (W₂ ▸ p₁)) (η (A ⇒ B)) (η D) q₁ = refl
cut⇒L-vass {W₂ = W₂} p q f (⇒L {U = U} {A = A} {B} p₁ g g₁) h k refl refl | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 (q ++ (W₂ ▸ p₁)) U (η (A ⇒ B)) ∙ = cut⇒L-cut⇒L-vass p₁ q f g g₁ h k
cut⇒L-vass {W₂ = W₂} {D = D} p q f (⇒L {U = U} {A = A} {B} p₁ g g₁) h k refl refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (q ++ (W₂ ▸ q₁)) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ = 
    cong (λ x → ⇒L (q ++ (W₂ ▸ (q₁ ++ (q₂ ◂ _)))) g x) (cut⇒L-vass (q₁ ++ (_ ▸ q₃)) q f g₁ h k refl refl)
cut⇒L-vass {W₂ = W₂} {D = D} p q f (⇒L {U = U} {A = A} {B} p₁ g g₁) h k refl refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (q ++ (W₂ ▸ q₁)) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ = 
    cong (λ x → ⇒L (q ++ (W₂ ▸ (q₁ ++ (_ ▸ q₃)))) g x) (cut⇒L-vass (q₁ ++ (q₂ ◂ _)) q f g₁ h k refl refl)
cut⇒L-vass p q f (⇐L p₁ g g₁) h k eq₁ refl with subeq _ _ p₁ p eq₁
cut⇒L-vass {W₂ = W₂} p q f (⇐L {U = U} {A = A} {B} p₁ g g₁) h k refl refl | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 (q ++ (W₂ ▸ p₁)) U (η (B ⇐ A)) ∙ = cut⇒L-cut⇐L-vass p₁ q f g g₁ h k
cut⇒L-vass {W₂ = W₂} {D = D} p q f (⇐L {A = A} {B} p₁ g g₁) h k refl refl | 2>R1 (gt q₁ refl refl refl) 
  rewrite subeq-2>R1 (q ++ (W₂ ▸ p₁)) (η (B ⇐ A)) (η D) q₁ = refl
cut⇒L-vass {W₂ = W₂} {D = D} p q f (⇐L {U = U} {A = A} {B} p₁ g g₁) h k refl refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (q ++ (W₂ ▸ q₁)) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ = 
    cong (λ x → ⇐L (q ++ (W₂ ▸ (q₁ ++ (q₂ ◂ _)))) g x) (cut⇒L-vass (q₁ ++ (_ ▸ q₃)) q f g₁ h k refl refl)
cut⇒L-vass {W₂ = W₂} {D = D} p q f (⇐L {U = U} {A = A} {B} p₁ g g₁) h k refl refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (q ++ (W₂ ▸ q₁)) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ = 
    cong (λ x → ⇐L (q ++ (W₂ ▸ (q₁ ++ (_ ▸ q₃)))) g x) (cut⇒L-vass (q₁ ++ (q₂ ◂ _)) q f g₁ h k refl refl)
cut⇒L-vass p q f (⊗L p₁ g) h k eq₁ refl with subeq _ _ p₁ p eq₁
cut⇒L-vass {W₂ = W₂} p q f (⊗L {A = A} {B} p₁ g) h k refl refl | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 (q ++ (W₂ ▸ p)) (η (A ⊗ B)) = cut⇒L-cut⊗L-vass p q f g h k
cut⇒L-vass {W₂ = W₂} {D = D} p q f (⊗L {A = A} {B} p₁ g) h k refl refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (q ++ (W₂ ▸ q₁)) (η (A ⊗ B)) (η D) q₂ q₃ = 
    cong (λ x → ⊗L (q ++ (W₂ ▸ (q₁ ++ (q₂ ◂ _)))) x) (cut⇒L-vass (q₁ ++ (_ ▸ q₃)) q f g h k refl refl)
cut⇒L-vass {W₂ = W₂} {D = D} p q f (⊗L {A = A} {B} p₁ g) h k refl refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (q ++ (W₂ ▸ q₁)) (η (A ⊗ B)) (η D) q₂ q₃ = 
    cong (λ x → ⊗L (q ++ (W₂ ▸ (q₁ ++ (_ ▸ q₃)))) x) (cut⇒L-vass (q₁ ++ (q₂ ◂ _)) q f g h k refl refl)


cut⇐L-vass p q f (⇐R g) h k refl refl = 
  trans (cong (λ x → cut (q ++ (_ ▸ ∙)) h x refl) (cut-vass (p ◂ _) q f g k refl refl)) 
        (sym (cut-hass q p ∙ f h (cut q g k refl) refl))
cut⇐L-vass p q f (⇒L p₁ g g₁) h k eq₁ refl with subeq _ _ p₁ p eq₁
cut⇐L-vass {W₂ = W₂} {D = D} p q f (⇒L {A = A} {B} p₁ g g₁) h k refl refl | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 (q ++ (p₁ ◂ W₂)) (η (A ⇒ B)) (η D) q₁ = refl
cut⇐L-vass {W₂ = W₂} p q f (⇒L {U = U} {A = A} {B} p₁ g g₁) h k refl refl | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 (q ++ (p₁ ◂ W₂)) U (η (A ⇒ B)) ∙ = cut⇐L-cut⇒L-vass p₁ q f g g₁ h k
cut⇐L-vass {W₂ = W₂} {D = D} p q f (⇒L {U = U} {A = A} {B} p₁ g g₁) h k refl refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (q ++ (q₁ ◂ W₂)) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ = 
    cong (λ x → ⇒L (q ++ ((q₁ ++ (q₂ ◂ _)) ◂ W₂)) g x) (cut⇐L-vass (q₁ ++ (_ ▸ q₃)) q f g₁ h k refl refl)
cut⇐L-vass {W₂ = W₂} {D = D} p q f (⇒L {U = U} {A = A} {B} p₁ g g₁) h k refl refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (q ++ (q₁ ◂ W₂)) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ = 
    cong (λ x → ⇒L (q ++ ((q₁ ++ (_ ▸ q₃)) ◂ W₂)) g x) (cut⇐L-vass (q₁ ++ (q₂ ◂ _)) q f g₁ h k refl refl)
cut⇐L-vass p q f (⇐L p₁ g g₁) h k eq₁ refl with subeq _ _ p₁ p eq₁
cut⇐L-vass {W₂ = W₂} p q f (⇐L {U = U} {A = A} {B} p₁ g g₁) h k refl refl | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 (q ++ (p₁ ◂ W₂)) U (η (B ⇐ A)) ∙ = cut⇐L-cut⇐L-vass p₁ q f g g₁ h k
cut⇐L-vass {W₂ = W₂} {D = D} p q f (⇐L {A = A} {B} p₁ g g₁) h k refl refl | 2>R1 (gt q₁ refl refl refl) 
  rewrite subeq-2>R1 (q ++ (p₁ ◂ W₂)) (η (B ⇐ A)) (η D) q₁ = refl
cut⇐L-vass {W₂ = W₂} {D = D} p q f (⇐L {U = U} {A = A} {B} p₁ g g₁) h k refl refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (q ++ (q₁ ◂ W₂)) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ = 
    cong (λ x → ⇐L (q ++ ((q₁ ++ (q₂ ◂ _)) ◂ W₂)) g x) (cut⇐L-vass (q₁ ++ (_ ▸ q₃)) q f g₁ h k refl refl)
cut⇐L-vass {W₂ = W₂} {D = D} p q f (⇐L {U = U} {A = A} {B} p₁ g g₁) h k refl refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (q ++ (q₁ ◂ W₂)) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ = 
    cong (λ x → ⇐L (q ++ ((q₁ ++ (_ ▸ q₃)) ◂ W₂)) g x) (cut⇐L-vass (q₁ ++ (q₂ ◂ _)) q f g₁ h k refl refl)
cut⇐L-vass p q f (⊗L p₁ g) h k eq₁ refl with subeq _ _ p₁ p eq₁
cut⇐L-vass {W₂ = W₂} p q f (⊗L {A = A} {B} p₁ g) h k refl refl | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 (q ++ (p ◂ W₂)) (η (A ⊗ B)) = cut⇐L-cut⊗L-vass p q f g h k
cut⇐L-vass {W₂ = W₂} {D = D} p q f (⊗L {A = A} {B} p₁ g) h k refl refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (q ++ (q₁ ◂ W₂)) (η (A ⊗ B)) (η D) q₂ q₃ = 
    cong (λ x → ⊗L (q ++ ((q₁ ++ (q₂ ◂ _)) ◂ W₂)) x) (cut⇐L-vass (q₁ ++ (_ ▸ q₃)) q f g h k refl refl)
cut⇐L-vass {W₂ = W₂} {D = D} p q f (⊗L {A = A} {B} p₁ g) h k refl refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (q ++ (q₁ ◂ W₂)) (η (A ⊗ B)) (η D) q₂ q₃ = 
    cong (λ x → ⊗L (q ++ ((q₁ ++ (_ ▸ q₃)) ◂ W₂)) x) (cut⇐L-vass (q₁ ++ (q₂ ◂ _)) q f g h k refl refl)


cut⊗L-vass p q f (⇒L p₁ g g₁) h eq₁ refl with subeq _ _ p₁ p eq₁
cut⊗L-vass {D = D} p q f (⇒L {U = U} {A = A} {B} p₁ g g₁) h refl refl | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 (q ++ p₁) (η (A ⇒ B)) (η D) q₁ = refl
cut⊗L-vass p q f (⇒L {U = U} {A = A} {B} p₁ g g₁) h refl refl | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 (q ++ p₁) U (η (A ⇒ B)) ∙ = cut⊗L-cut⇒L-vass p₁ q f g g₁ h
cut⊗L-vass {D = D} p q f (⇒L {U = U} {A = A} {B} p₁ g g₁) h refl refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (q ++ q₁) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ = 
    cong (λ x → ⇒L (q ++ (q₁ ++ (q₂ ◂ _))) g x) (cut⊗L-vass (q₁ ++ (_ ▸ q₃)) q f g₁ h refl refl)
cut⊗L-vass {D = D} p q f (⇒L {U = U} {A = A} {B} p₁ g g₁) h refl refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (q ++ q₁) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ = 
    cong (λ x → ⇒L (q ++ (q₁ ++ (_ ▸ q₃))) g x) (cut⊗L-vass (q₁ ++ (q₂ ◂ _)) q f g₁ h refl refl)
cut⊗L-vass p q f (⇐L p₁ g g₁) h eq₁ refl with subeq _ _ p₁ p eq₁
cut⊗L-vass p q f (⇐L {U = U} {A = A} {B} p₁ g g₁) h refl refl | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 (q ++ p₁) U (η (B ⇐ A)) ∙ = cut⊗L-cut⇐L-vass p₁ q f g g₁ h
cut⊗L-vass {D = D} p q f (⇐L {U = U} {A = A} {B} p₁ g g₁) h refl refl | 2>R1 (gt q₁ refl refl refl) 
  rewrite subeq-2>R1 (q ++ p₁) (η (B ⇐ A)) (η D) q₁ = refl
cut⊗L-vass {D = D} p q f (⇐L {U = U} {A = A} {B} p₁ g g₁) h refl refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (q ++ q₁) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ = 
    cong (λ x → ⇐L (q ++ (q₁ ++ (q₂ ◂ _))) g x) (cut⊗L-vass (q₁ ++ (_ ▸ q₃)) q f g₁ h refl refl)
cut⊗L-vass {D = D} p q f (⇐L {U = U} {A = A} {B} p₁ g g₁) h refl refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (q ++ q₁) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ = 
    cong (λ x → ⇐L (q ++ (q₁ ++ (_ ▸ q₃))) g x) (cut⊗L-vass (q₁ ++ (q₂ ◂ _)) q f g₁ h refl refl)
cut⊗L-vass (p ◂ U) q f (⊗R g g₁) h refl refl = cut-vass p (q ++ (∙ ◂ _)) f g (cut (q ++ (η _ ▸ ∙)) g₁ h refl) refl refl
cut⊗L-vass (T ▸ p) q f (⊗R g g₁) h refl refl =
  trans (cut-hass q ∙ ∙ g  (cut p f g₁ refl) h refl) 
        (trans 
          (cut-vass p (q ++ (_ ▸ ∙)) f g₁ (cut (q ++ (∙ ◂ η _)) g h refl) refl refl) 
          (sym (cong (λ x → cut (q ++ (T ▸ p)) f x refl) (cut-hass q ∙ ∙ g g₁ h refl))))
cut⊗L-vass p q f (⊗L p₁ g) h eq₁ refl with subeq _ _ p₁ p eq₁
cut⊗L-vass p q f (⊗L {A = A} {B} p₁ g) h refl refl | 1≡2 (same refl refl refl)
  rewrite subeq-1≡2 (q ++ p) (η (A ⊗ B)) = cut⊗L-cut⊗L-vass p q f g h
cut⊗L-vass {D = D} p q f (⊗L {A = A} {B} p₁ g) h refl refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (q ++ q₁) (η (A ⊗ B)) (η D) q₂ q₃ = 
    cong (λ x → ⊗L (q ++ (q₁ ++ (q₂ ◂ _))) x) (cut⊗L-vass (q₁ ++ (_ ▸ q₃)) q f g h refl refl)
cut⊗L-vass {D = D} p q f (⊗L {A = A} {B} p₁ g) h refl refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (q ++ q₁) (η (A ⊗ B)) (η D) q₂ q₃ = 
    cong (λ x → ⊗L (q ++ (q₁ ++ (_ ▸ q₃))) x) (cut⊗L-vass (q₁ ++ (q₂ ◂ _)) q f g h refl refl)
 

{-
Proof of cut-hass
-}

cut-hass p₁ p₂ p₃ f g (⇒R h) refl = cong ⇒R (cut-hass (_ ▸ p₁) p₂ p₃ f g h refl)
cut-hass p₁ p₂ p₃ f g (⇐R h) refl = cong ⇐R (cut-hass (p₁ ◂ _) p₂ p₃ f g h refl)

cut-hass p₁ p₂ p₃ f g (⇒L p h h₁) eq with subeq _ _ p p₁ eq
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⇒L {A = A} {B} p h h₁) refl | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p (η (A ⇒ B)) (η D) (q ++ (p₂ ◂ sub p₃ (η E))) |
          subeq-2>L1 p (η (A ⇒ B)) (η E) (q ++ (sub p₂ T ▸ p₃)) |
          subeq-2>L1 p (η (A ⇒ B)) (η E) (q ++ (sub p₂ (η D) ▸ p₃)) |
          subeq-2>L1 p (η (A ⇒ B)) (η D) (q ++ (p₂ ◂ sub p₃ U)) = 
            cong (λ x → ⇒L p x h₁) (cut-hass q p₂ p₃ f g h refl)
... | 2>R1 (gt ∙ eqT () eqp)
... | 1>L2 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⇒L {A = A} {B} ._ h h₁) refl | 1>L2 (gt q refl refl refl) | 1>L2 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (q ◂ sub p₃ (η E))) (η (A ⇒ B)) (η D) q₁ |
          subeq-1/\2 p₁ (sub q₁ T ⊛ η (A ⇒ B)) (η E) q p₃ |
          subeq-1/\2 p₁ (sub q₁ (η D) ⊛ η (A ⇒ B)) (η E) q p₃ |
          subeq-2>L1 (p₁ ++ (q ◂ sub p₃ U)) (η (A ⇒ B)) (η D) q₁ = refl 
cut-hass {U = U} {E = E} p₁ p₂ p₃ f g (⇒L {U = U₁} {A = A} {B} ._ h h₁) refl | 1>L2 (gt q refl refl refl) | 1>R2 (gt ∙ refl refl refl)
  rewrite subeq-2>R1 (p₁ ++ (q ◂ sub p₃ (η E))) U₁ (η (A ⇒ B)) ∙ |
          subeq-1/\2 p₁ (U₁ ⊛ η (A ⇒ B)) (η E) q p₃ |
          subeq-2>R1 (p₁ ++ (q ◂ sub p₃ U)) U₁ (η (A ⇒ B)) ∙ = cut⇒L-hass₁ p₁ q p₃ f g h h₁
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⇒L {U = U₁} {A = A} {B} ._ h h₁) refl | 1>L2 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η E))) (U₁ ⊛ η (A ⇒ B)) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (U₁ ⊛ η (A ⇒ B)) (η E) (q₁ ++ (sub q₂ T ▸ q₃)) p₃ |
          subeq-1/\2 p₁ (U₁ ⊛ η (A ⇒ B)) (η E) (q₁ ++ (sub q₂ (η D) ▸ q₃)) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ U)) (U₁ ⊛ η (A ⇒ B)) (η D) q₂ q₃ = 
            cong (λ x → ⇒L (p₁ ++ ((q₁ ++ (_ ▸ q₃)) ◂ _)) h x) (cut-hass p₁ (q₁ ++ (q₂ ◂ _)) p₃ f g h₁ refl)
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⇒L {U = U₁} {A = A} {B} ._ h h₁) refl | 1>L2 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η E))) (U₁ ⊛ η (A ⇒ B)) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (U₁ ⊛ η (A ⇒ B)) (η E) (q₁ ++ (q₂ ◂ sub q₃ T)) p₃ |
          subeq-1/\2 p₁ (U₁ ⊛ η (A ⇒ B)) (η E) (q₁ ++ (q₂ ◂ sub q₃ (η D))) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ U)) (U₁ ⊛ η (A ⇒ B)) (η D) q₂ q₃ = 
            cong (λ x → ⇒L (p₁ ++ ((q₁ ++ (q₂ ◂ _)) ◂ _)) h x) (cut-hass p₁ (q₁ ++ (_ ▸ q₃)) p₃ f g h₁ refl)
cut-hass p₁ p₂ p₃ f g (⇒L p h h₁) eq | 1>R2 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⇒L {A = A} {B} ._ h h₁) refl | 1>R2 (gt q refl refl refl) | 1>L2 (gt q₁ refl refl refl) 
  rewrite subeq-2/\1 p₁ (sub q₁ (η E) ⊛ η (A ⇒ B)) (η D) p₂ q |
          subeq-2>L1 (p₁ ++ (sub p₂ T ▸ q)) (η (A ⇒ B)) (η E) q₁ |
          subeq-2>L1 (p₁ ++ (sub p₂ (η D) ▸ q)) (η (A ⇒ B)) (η E) q₁ |
          subeq-2/\1 p₁ (sub q₁ U ⊛ η (A ⇒ B)) (η D) p₂ q = refl
cut-hass {T} {D = D} p₁ p₂ p₃ f g (⇒L {U = U} {A = A} {B} ._ h h₁) refl | 1>R2 (gt q refl refl refl) | 1>R2 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (η D) ▸ q)) U (η (A ⇒ B)) ∙ |
          subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η D) p₂ q |
          subeq-2>R1 (p₁ ++ (sub p₂ T ▸ q)) U (η (A ⇒ B)) ∙ = sym (cut⇒L-hass₂ p₁ p₂ q f g h h₁)
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⇒L {U = U₁} {A = A} {B} ._ h h₁) refl | 1>R2 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ (U₁ ⊛ η (A ⇒ B)) (η D) p₂ (q₁ ++ (sub q₂ (η E) ▸ q₃)) |
          subeq-2/\1 (p₁ ++ (sub p₂ T ▸ q₁)) (U₁ ⊛ η (A ⇒ B)) (η E) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (sub p₂ (η D) ▸ q₁)) (U₁ ⊛ η (A ⇒ B)) (η E) q₂ q₃ |
          subeq-2/\1 p₁ (U₁ ⊛ η (A ⇒ B)) (η D) p₂ (q₁ ++ (sub q₂ U ▸ q₃)) =
            cong (λ x → ⇒L (p₁ ++ (_ ▸ (q₁ ++ (_ ▸ q₃)))) h x) (cut-hass p₁ p₂ (q₁ ++ (q₂ ◂ _)) f g h₁ refl)
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⇒L {U = U₁} {A = A} {B} ._ h h₁) refl | 1>R2 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (U₁ ⊛ η (A ⇒ B)) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η E))) |
          subeq-1/\2 (p₁ ++ (sub p₂ T ▸ q₁)) (U₁ ⊛ η (A ⇒ B)) (η E) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (sub p₂ (η D) ▸ q₁)) (U₁ ⊛ η (A ⇒ B)) (η E) q₂ q₃ |
          subeq-2/\1 p₁ (U₁ ⊛ η (A ⇒ B)) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ U)) =
            cong (λ x → ⇒L (p₁ ++ (_ ▸ (q₁ ++ (q₂ ◂ _)))) h x) (cut-hass p₁ p₂ (q₁ ++ (_ ▸ q₃)) f g h₁ refl)
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⇒L {U = U₁} {A = A} {B} p h h₁) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (U₁ ⊛ η (A ⇒ B)) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η E))) |
          subeq-1/\2 q (U₁ ⊛ η (A ⇒ B)) (η E) q₁ (q₂ ++ (sub p₂ T ▸ p₃)) |
          subeq-1/\2 q (U₁ ⊛ η (A ⇒ B)) (η E) q₁ (q₂ ++ (sub p₂ (η D) ▸ p₃)) |
          subeq-1/\2 q (U₁ ⊛ η (A ⇒ B)) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ U)) =
            cong (λ x → ⇒L (q ++ (q₁ ◂ _)) h x) (cut-hass (q ++ (_ ▸ q₂)) p₂ p₃ f g h₁ refl)
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⇒L {U = U₁} {A = A} {B} p h h₁) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U₁ ⊛ η (A ⇒ B)) (η D) (q₁ ++ (p₂ ◂ sub p₃ (η E))) q₂ |
          subeq-2/\1 q (U₁ ⊛ η (A ⇒ B)) (η E) (q₁ ++ (sub p₂ T ▸ p₃)) q₂ |
          subeq-2/\1 q (U₁ ⊛ η (A ⇒ B)) (η E) (q₁ ++ (sub p₂ (η D) ▸ p₃)) q₂ |
          subeq-2/\1 q (U₁ ⊛ η (A ⇒ B)) (η D) (q₁ ++ (p₂ ◂ sub p₃ U)) q₂ = 
            cong (λ x → ⇒L (q ++ (_ ▸ q₂)) h x) (cut-hass (q ++ (q₁ ◂ _)) p₂ p₃ f g h₁ refl)
cut-hass {T} {D = D} p₁ p₂ ∙ f g (⇒L {A = A} {B} p h h₁) refl | 1≡2 (same refl refl refl)
  rewrite subeq-2>R1 p₁ (sub p₂ (η D)) (η (A ⇒ B)) ∙ |
          subeq-2>L1 p₁ (η (A ⇒ B)) (η D) p₂ |
          subeq-2>R1 p₁ (sub p₂ T) (η (A ⇒ B)) ∙ = sym (cut⇒L-hass₃ p₂ p₁ f g h h₁)

cut-hass p₁ p₂ p₃ f g (⇐L p h h₁) eq with subeq _ _ p p₁ eq
... | 2>L1 (gt ∙ eqT () eqp)
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⇐L {A = A} {B} p h h₁) refl | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 p (η (B ⇐ A)) (η D) (q ++ (p₂ ◂ sub p₃ (η E))) |
          subeq-2>R1 p (η (B ⇐ A)) (η E) (q ++ (sub p₂ T ▸ p₃)) |
          subeq-2>R1 p (η (B ⇐ A)) (η E) (q ++ (sub p₂ (η D) ▸ p₃)) |
          subeq-2>R1 p (η (B ⇐ A)) (η D) (q ++ (p₂ ◂ sub p₃ U)) = 
            cong (λ x → ⇐L p x h₁) (cut-hass q p₂ p₃ f g h refl)
... | 1>L2 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut-hass {U = U} {E = E} p₁ p₂ p₃ f g (⇐L {U = U₁} {A = A} {B} ._ h h₁) refl | 1>L2 (gt q refl refl refl) | 1>L2 (gt ∙ refl refl refl)
  rewrite subeq-2>L1 (p₁ ++ (q ◂ sub p₃ (η E))) U₁ (η (B ⇐ A)) ∙ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U₁) (η E) q p₃ |
          subeq-2>L1 (p₁ ++ (q ◂ sub p₃ U)) U₁ (η (B ⇐ A)) ∙ = cut⇐L-hass₁ p₁ q p₃ f g h h₁
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⇐L {A = A} {B} ._ h h₁) refl | 1>L2 (gt q refl refl refl) | 1>R2 (gt q₁ refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (q ◂ sub p₃ (η E))) (η (B ⇐ A)) (η D) q₁ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ sub q₁ T) (η E) q p₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ sub q₁ (η D)) (η E) q p₃ |
          subeq-2>R1 (p₁ ++ (q ◂ sub p₃ U)) (η (B ⇐ A)) (η D) q₁ = refl
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⇐L {U = U₁} {A = A} {B} ._ h h₁) refl | 1>L2 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η E))) (η (B ⇐ A) ⊛ U₁) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U₁) (η E) (q₁ ++ (sub q₂ T ▸ q₃)) p₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U₁) (η E) (q₁ ++ (sub q₂ (η D) ▸ q₃)) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ U)) (η (B ⇐ A) ⊛ U₁) (η D) q₂ q₃ = 
            cong (λ x → ⇐L (p₁ ++ ((q₁ ++ (_ ▸ q₃)) ◂ _)) h x) (cut-hass p₁ (q₁ ++ (q₂ ◂ _)) p₃ f g h₁ refl)
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⇐L {U = U₁} {A = A} {B} ._ h h₁) refl | 1>L2 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η E))) (η (B ⇐ A) ⊛ U₁) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U₁) (η E) (q₁ ++ (q₂ ◂ sub q₃ T)) p₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U₁) (η E) (q₁ ++ (q₂ ◂ sub q₃ (η D))) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ U)) (η (B ⇐ A) ⊛ U₁) (η D) q₂ q₃ = 
            cong (λ x → ⇐L (p₁ ++ ((q₁ ++ (q₂ ◂ _)) ◂ _)) h x) (cut-hass p₁ (q₁ ++ (_ ▸ q₃)) p₃ f g h₁ refl)
cut-hass p₁ p₂ p₃ f g (⇐L p h h₁) eq | 1>R2 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut-hass {T} {D = D} p₁ p₂ p₃ f g (⇐L {U = U} {A = A} {B} ._ h h₁) refl | 1>R2 (gt q refl refl refl) | 1>L2 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (η D) ▸ q)) U (η (B ⇐ A)) ∙ |
          subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η D) p₂ q |
          subeq-2>L1 (p₁ ++ (sub p₂ T ▸ q)) U (η (B ⇐ A)) ∙ = sym (cut⇐L-hass₂ p₁ p₂ q f g h h₁)
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⇐L {A = A} {B} ._ h h₁) refl | 1>R2 (gt q refl refl refl) | 1>R2 (gt q₁ refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B ⇐ A) ⊛ sub q₁ (η E)) (η D) p₂ q |
          subeq-2>R1 (p₁ ++ (sub p₂ T ▸ q)) (η (B ⇐ A)) (η E) q₁ |
          subeq-2>R1 (p₁ ++ (sub p₂ (η D) ▸ q)) (η (B ⇐ A)) (η E) q₁ |
          subeq-2/\1 p₁ (η (B ⇐ A) ⊛ sub q₁ U) (η D) p₂ q = refl
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⇐L {U = U₁} {A = A} {B} ._ h h₁) refl | 1>R2 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U₁) (η D) p₂ (q₁ ++ (sub q₂ (η E) ▸ q₃)) |
          subeq-2/\1 (p₁ ++ (sub p₂ T ▸ q₁)) (η (B ⇐ A) ⊛ U₁) (η E) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (sub p₂ (η D) ▸ q₁)) (η (B ⇐ A) ⊛ U₁) (η E) q₂ q₃ |
          subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U₁) (η D) p₂ (q₁ ++ (sub q₂ U ▸ q₃)) = 
            cong (λ x → ⇐L (p₁ ++ (_ ▸ (q₁ ++ (_ ▸ q₃)))) h x) (cut-hass p₁ p₂ (q₁ ++ (q₂ ◂ _)) f g h₁ refl)
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⇐L {U = U₁} {A = A} {B} ._ h h₁) refl | 1>R2 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U₁) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η E))) |
          subeq-1/\2 (p₁ ++ (sub p₂ T ▸ q₁)) (η (B ⇐ A) ⊛ U₁) (η E) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (sub p₂ (η D) ▸ q₁)) (η (B ⇐ A) ⊛ U₁) (η E) q₂ q₃ |
          subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U₁) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ U)) = 
            cong (λ x → ⇐L (p₁ ++ (_ ▸ (q₁ ++ (q₂ ◂ _)))) h x) (cut-hass p₁ p₂ (q₁ ++ (_ ▸ q₃)) f g h₁ refl)
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⇐L {U = U₁} {A = A} {B} p h h₁) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U₁) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η E))) |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U₁) (η E) q₁ (q₂ ++ (sub p₂ T ▸ p₃)) |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U₁) (η E) q₁ (q₂ ++ (sub p₂ (η D) ▸ p₃)) |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U₁) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ U)) = 
            cong (λ x → ⇐L (q ++ (q₁ ◂ _)) h x) (cut-hass (q ++ (_ ▸ q₂)) p₂ p₃ f g h₁ refl)
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⇐L {U = U₁} {A = A} {B} p h h₁) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U₁) (η D) (q₁ ++ (p₂ ◂ sub p₃ (η E))) q₂ |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U₁) (η E) (q₁ ++ (sub p₂ T ▸ p₃)) q₂ |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U₁) (η E) (q₁ ++ (sub p₂ (η D) ▸ p₃)) q₂ |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U₁) (η D) (q₁ ++ (p₂ ◂ sub p₃ U)) q₂ = 
            cong (λ x → ⇐L (q ++ (_ ▸ q₂)) h x) (cut-hass (q ++ (q₁ ◂ _)) p₂ p₃ f g h₁ refl)
cut-hass {U = U} {E = E} p₁ ∙ p₃ f g (⇐L {A = A} {B} p h h₁) refl | 1≡2 (same refl refl refl)
  rewrite subeq-2>L1 p₁ (sub p₃ (η E)) (η (B ⇐ A)) ∙ |
          subeq-2>R1 p₁ (η (B ⇐ A)) (η E) p₃ |
          subeq-2>L1 p₁ (sub p₃ U) (η (B ⇐ A)) ∙ = cut⇐L-hass₃ p₃ p₁ f g h h₁

cut-hass ∙ p₂ p₃ f g (⊗R h h₁) refl = refl
cut-hass (p₁ ◂ U) p₂ p₃ f g (⊗R h h₁) refl = cong₂ ⊗R (cut-hass p₁ p₂ p₃ f g h refl) refl
cut-hass (T ▸ p₁) p₂ p₃ f g (⊗R h h₁) refl = cong₂ ⊗R refl (cut-hass p₁ p₂ p₃ f g h₁ refl)

cut-hass p₁ p₂ p₃ f g (⊗L p h) eq with subeq _ _ p p₁ eq
cut-hass p₁ p₂ p₃ f g (⊗L p h) eq | 1>L2 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut-hass {U = U} {E = E} p₁ p₂ p₃ f g (⊗L {A = A} {B} ._ h) refl | 1>L2 (gt q refl refl refl) | 1≡2 (same refl refl refl)
  rewrite subeq-1≡2 (p₁ ++ (p₂ ◂ sub p₃ (η E))) (η (A ⊗ B)) |
          subeq-1/\2 p₁ (η (A ⊗ B)) (η E) p₂ p₃ |
          subeq-1≡2 (p₁ ++ (p₂ ◂ sub p₃ U)) (η (A ⊗ B)) = cut⊗L-hass₁ p₁ p₂ p₃ g f h
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⊗L {A = A} {B} ._ h) refl | 1>L2 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η E))) (η (A ⊗ B)) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (η (A ⊗ B)) (η E) (q₁ ++ (sub q₂ T ▸ q₃)) p₃ |
          subeq-1/\2 p₁ (η (A ⊗ B)) (η E) (q₁ ++ (sub q₂ (η D) ▸ q₃)) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ U)) (η (A ⊗ B)) (η D) q₂ q₃ = 
            cong (λ x → ⊗L (p₁ ++ ((q₁ ++ (_ ▸ q₃)) ◂ _)) x) (cut-hass p₁ (q₁ ++ (q₂ ◂ _)) p₃ f g h refl)
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⊗L {A = A} {B} ._ h) refl | 1>L2 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η E))) (η (A ⊗ B)) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (η (A ⊗ B)) (η E) (q₁ ++ (q₂ ◂ sub q₃ T)) p₃ |
          subeq-1/\2 p₁ (η (A ⊗ B)) (η E) (q₁ ++ (q₂ ◂ sub q₃ (η D))) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ U)) (η (A ⊗ B)) (η D) q₂ q₃ = 
            cong (λ x → ⊗L (p₁ ++ ((q₁ ++ (q₂ ◂ _)) ◂ _)) x) (cut-hass p₁ (q₁ ++ (_ ▸ q₃)) p₃ f g h refl)
cut-hass p₁ p₂ p₃ f g (⊗L p h) eq | 1>R2 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut-hass {T} {D = D} p₁ p₂ p₃ f g (⊗L {A = A} {B} ._ h) refl | 1>R2 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 (p₁ ++ (sub p₂ (η D) ▸ p₃)) (η (A ⊗ B)) |
          subeq-2/\1 p₁ (η (A ⊗ B)) (η D) p₂ p₃ |
          subeq-1≡2 (p₁ ++ (sub p₂ T ▸ p₃)) (η (A ⊗ B)) = sym (cut⊗L-hass₂ p₁ p₂ p₃ f g h)
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⊗L {A = A} {B} ._ h) refl | 1>R2 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (A ⊗ B)) (η D) p₂ (q₁ ++ (sub q₂ (η E) ▸ q₃)) |
          subeq-2/\1 (p₁ ++ (sub p₂ T ▸ q₁)) (η (A ⊗ B)) (η E) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (sub p₂ (η D) ▸ q₁)) (η (A ⊗ B)) (η E) q₂ q₃ |
          subeq-2/\1 p₁ (η (A ⊗ B)) (η D) p₂ (q₁ ++ (sub q₂ U ▸ q₃)) = 
            cong (λ x → ⊗L (p₁ ++ (_ ▸ (q₁ ++ (_ ▸ q₃)))) x) (cut-hass p₁ p₂ (q₁ ++ (q₂ ◂ _)) f g h refl)
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⊗L {A = A} {B} ._ h) refl | 1>R2 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (A ⊗ B)) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η E))) |
          subeq-1/\2 (p₁ ++ (sub p₂ T ▸ q₁)) (η (A ⊗ B)) (η E) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (sub p₂ (η D) ▸ q₁)) (η (A ⊗ B)) (η E) q₂ q₃ |
          subeq-2/\1 p₁ (η (A ⊗ B)) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ U)) = 
            cong (λ x → ⊗L (p₁ ++ (_ ▸ (q₁ ++ (q₂ ◂ _)))) x) (cut-hass p₁ p₂ (q₁ ++ (_ ▸ q₃)) f g h refl)
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⊗L {A = A} {B} p h) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η E))) |
          subeq-1/\2 q (η (A ⊗ B)) (η E) q₁ (q₂ ++ (sub p₂ T ▸ p₃)) |
          subeq-1/\2 q (η (A ⊗ B)) (η E) q₁ (q₂ ++ (sub p₂ (η D) ▸ p₃)) |
          subeq-1/\2 q (η (A ⊗ B)) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ U)) = 
            cong (λ x → ⊗L (q ++ (q₁ ◂ _)) x) (cut-hass (q ++ (_ ▸ q₂)) p₂ p₃ f g h refl)
cut-hass {T} {U} {D = D} {E} p₁ p₂ p₃ f g (⊗L {A = A} {B} p h) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η D) (q₁ ++ (p₂ ◂ sub p₃ (η E))) q₂ |
          subeq-2/\1 q (η (A ⊗ B)) (η E) (q₁ ++ (sub p₂ T ▸ p₃)) q₂ |
          subeq-2/\1 q (η (A ⊗ B)) (η E) (q₁ ++ (sub p₂ (η D) ▸ p₃)) q₂ |
          subeq-2/\1 q (η (A ⊗ B)) (η D) (q₁ ++ (p₂ ◂ sub p₃ U)) q₂ = 
            cong (λ x → ⊗L (q ++ (_ ▸ q₂)) x) (cut-hass (q ++ (q₁ ◂ _)) p₂ p₃ f g h refl)

cut-hass ∙ p₂ p₃ f g ax ()
 
