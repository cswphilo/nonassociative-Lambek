{-# OPTIONS --rewriting #-}

module CutEqualities where

open import Relation.Binary.PropositionalEquality hiding ([_]; _≗_) 
open import Data.Product
open import Data.Empty
open import Fma
open import SeqCalc
open import Cut
open import SubEqProperties

cut⇒L-2>L1 : ∀ {T U A B C E F} (p : Path T)
  → (h : U ⊢ E) (g : η E ⊢ A)
  → (h₁ : η B ⊢ F) (g₁ : sub p (η F) ⊢ C)
  → cut (p ++ (∙ ◂ η (A ⇒ B))) h (⇒L p g (cut p h₁ g₁ refl)) refl ≡ ⇒L p (cut ∙ h g refl) (cut p h₁ g₁ refl)
cut⇒L-2>L1 {A = A} {B} {E = E} p h g h₁ g₁ 
  rewrite subeq-2>L1 p (η (A ⇒ B)) (η E) ∙ = refl

cut⇐L-2>R1 : ∀ {T U A B C E F} (p : Path T)
  → (h : U ⊢ E) (g : η E ⊢ A)
  → (h₁ : η B ⊢ F) (g₁ : sub p (η F) ⊢ C)
  → cut (p ++ (η (B ⇐ A) ▸ ∙)) h (⇐L p g (cut p h₁ g₁ refl)) refl ≡ ⇐L p (cut ∙ h g refl) (cut p h₁ g₁ refl)
cut⇐L-2>R1 {A = A} {B} {E = E} p h g h₁ g₁ 
  rewrite subeq-2>R1 p (η (B ⇐ A)) (η E) ∙ = refl

cut⇒L-vass-left : ∀ {T U V W A B A' B' C} (p : Path T) (q : Path W)
  → (f : U ⊢ A') (g : sub p (η B) ⊢ C)
  → (h : V ⊢ A) (k : sub q (η B') ⊛ η A ⊢ B)
  → ⇒L (p ++ (q ◂ _)) f (cut (p ++ (_ ▸ ∙)) h (cut p k g refl) refl)
    ≡ cut (p ++ (sub q (U ⊛ η (A' ⇒ B')) ▸ ∙)) h (⇒L (p ++ (q ◂ η A)) f (cut p k g refl)) refl
cut⇒L-vass-left {U = U} {A = A} {A' = A'} {B'} p q f g h k 
  rewrite subeq-1/\2 p (U ⊛ η (A' ⇒ B')) (η A) q ∙ = refl 

cut⇒L-vass-right : ∀ {T U V W A B A' B' C} (p : Path T) (q : Path W)
  → (f : U ⊢ A') (g : sub p (η B) ⊢ C)
  → (h : V ⊢ A) (k : η A ⊛ sub q (η B') ⊢ B)
  → ⇒L (p ++ (_ ▸ q)) f (cut (p ++ (∙ ◂ _)) h (cut p k g refl) refl)
    ≡ cut (p ++ (∙ ◂ sub q (U ⊛ η (A' ⇒ B')))) h (⇒L (p ++ (η A ▸ q)) f (cut p k g refl)) refl
cut⇒L-vass-right {U = U} {A = A} {A' = A'} {B'} p q f g h k 
  rewrite subeq-2/\1 p (U ⊛ η (A' ⇒ B')) (η A) ∙ q = refl

cut⇒L-hass : ∀ {T U V W A B A' B' C} (p : Path T) (q : Path W)
  → (f : U ⊢ A') (g : sub p (η A ⊛ η B) ⊢ C)
  → (h : V ⊢ A) (k : sub q (η B') ⊢ B)
  → ⇒L (p ++ (_ ▸ q)) f (cut (p ++ (∙ ◂ _)) h (cut (p ++ (_ ▸ ∙)) k g refl) refl) 
    ≡ cut (p ++ (∙ ◂ sub q (U ⊛ η (A' ⇒ B')))) h (⇒L (p ++ (η A ▸ q)) f (cut (p ++ (η A ▸ ∙)) k g refl)) refl
cut⇒L-hass {U = U} {A = A} {B} {A'} {B'} p q f g h k 
  rewrite subeq-2/\1 p (U ⊛ η (A' ⇒ B')) (η A) ∙ q = refl

cut⇐L-vass-left : ∀ {T U V W A B A' B' C} (p : Path T) (q : Path W)
  → (f : U ⊢ A') (g : sub p (η B) ⊢ C)
  → (h : V ⊢ A) (k : sub q (η B') ⊛ η A ⊢ B)
  → ⇐L (p ++ (q ◂ _)) f (cut (p ++ (_ ▸ ∙)) h (cut p k g refl) refl)
    ≡ cut (p ++ (sub q (η (B' ⇐ A') ⊛ U) ▸ ∙)) h (⇐L (p ++ (q ◂ η A)) f (cut p k g refl)) refl
cut⇐L-vass-left {U = U} {A = A} {A' = A'} {B'} p q f g h k 
  rewrite subeq-1/\2 p (η (B' ⇐ A') ⊛ U) (η A) q ∙ = refl

cut⇐L-vass-right : ∀ {T U V W A B A' B' C} (p : Path T) (q : Path W)
  → (f : U ⊢ A') (g : sub p (η B) ⊢ C)
  → (h : V ⊢ A) (k : η A ⊛ sub q (η B') ⊢ B)
  → ⇐L (p ++ (_ ▸ q)) f (cut (p ++ (∙ ◂ _)) h (cut p k g refl) refl)
    ≡ cut (p ++ (∙ ◂ sub q (η (B' ⇐ A') ⊛ U))) h (⇐L (p ++ (η A ▸ q)) f (cut p k g refl)) refl
cut⇐L-vass-right {U = U} {A = A} {A' = A'} {B'} p q f g h k 
  rewrite subeq-2/\1 p (η (B' ⇐ A') ⊛ U) (η A) ∙ q = refl

cut⇐L-hass : ∀ {T U V W A B A' B' C} (p : Path T) (q : Path W)
  → (f : U ⊢ A') (g : sub p (η A ⊛ η B) ⊢ C)
  → (h : V ⊢ A) (k : sub q (η B') ⊢ B)
  → ⇐L (p ++ (_ ▸ q)) f (cut (p ++ (∙ ◂ _)) h (cut (p ++ (_ ▸ ∙)) k g refl) refl) 
    ≡ cut (p ++ (∙ ◂ sub q (η (B' ⇐ A') ⊛ U))) h (⇐L (p ++ (η A ▸ q)) f (cut (p ++ (η A ▸ ∙)) k g refl)) refl
cut⇐L-hass {U = U} {A = A} {B} {A'} {B'} p q f g h k 
  rewrite subeq-2/\1 p (η (B' ⇐ A') ⊛ U) (η A) ∙ q = refl
  
cut⊗L-vass-left : ∀ {T U V A B A' B' C} (p : Path T) (q : Path U)
  → (f : V ⊢ A) (g : sub p (η B) ⊢ C)
  → (h : sub q (η A' ⊛ η B') ⊛ η A ⊢ B)
  → ⊗L (p ++ (q ◂ _)) (cut (p ++ (_ ▸ ∙)) f (cut p h g refl) refl) 
    ≡ cut (p ++ (sub q (η (A' ⊗ B')) ▸ ∙)) f (⊗L (p ++ (q ◂ η A)) (cut p h g refl)) refl 
cut⊗L-vass-left {A = A} {A' = A'} {B'} p q f g h 
  rewrite subeq-1/\2 p (η (A' ⊗ B')) (η A) q ∙ = refl

cut⊗L-vass-right : ∀ {T U V A B A' B' C} (p : Path T) (q : Path U)
  → (f : V ⊢ A) (g : sub p (η B) ⊢ C)
  → (h : η A ⊛ sub q (η A' ⊛ η B') ⊢ B)
  → ⊗L (p ++ (_ ▸ q)) (cut (p ++ (∙ ◂ _)) f (cut p h g refl) refl) 
    ≡ cut (p ++ (∙ ◂ sub q (η (A' ⊗ B')))) f (⊗L (p ++ (η A ▸ q)) (cut p h g refl)) refl 
cut⊗L-vass-right {A = A} {A' = A'} {B'} p q f g h 
  rewrite subeq-2/\1 p (η (A' ⊗ B')) (η A) ∙ q = refl

cut⊗L-hass : ∀ {T U V A B A' B' C} (p : Path T) (q : Path U)
  → (f : V ⊢ A) (g : sub p (η A ⊛ η B) ⊢ C)
  → (h : sub q (η A' ⊛ η B') ⊢ B)
  → ⊗L (p ++ (_ ▸ q)) (cut (p ++ (∙ ◂ _)) f (cut (p ++ (_ ▸ ∙ )) h g refl) refl)
    ≡ cut (p ++ (∙ ◂ sub q (η (A' ⊗ B')))) f (⊗L (p ++ (η A ▸ q)) (cut (p ++ (_ ▸ ∙ )) h g refl)) refl 
cut⊗L-hass {A = A} {A' = A'} {B'} p q f g h 
  rewrite subeq-2/\1 p (η (A' ⊗ B')) (η A) ∙ q = refl

cut-unit : ∀ {T X W C} (p : Path T)
  → (g : W ⊢ C)
  → (eq : W ≡ sub p (η (at X))) 
  → cut p ax (subst-cxt eq g) refl ≡ (subst-cxt eq g)
cut-unit p (⇒R g) refl = cong ⇒R (cut-unit (_ ▸ p) g refl)
cut-unit p (⇐R g) refl = cong ⇐R (cut-unit (p ◂ _) g refl)
cut-unit {X = X} p (⇒L {U = U} {A} {B} p₁ g g₁) eq with subeq (U ⊛ η (A ⇒ B)) (η (at X)) p₁ p eq
cut-unit {X = X} p (⇒L {U = U} {A} {B} p₁ g g₁) refl | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η (at X)) q = cong (λ x → ⇒L p₁ x g₁) (cut-unit q g refl)
... | 2>R1 (gt ∙ eqT () eqp)
cut-unit {X = X} p (⇒L {U = U} {A} {B} p₁ g g₁) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (at X)) q₁ q₂ = 
    cong (λ x → ⇒L (q ++ (q₁ ◂ sub q₂ (η (at X)))) g x) (cut-unit (q ++ (sub q₁ (η B) ▸ q₂)) g₁ refl)
cut-unit {X = X} p (⇒L {U = U} {A} {B} p₁ g g₁) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (at X)) q₁ q₂ = 
    cong (λ x → ⇒L (q ++ (sub q₁ (η (at X)) ▸ q₂)) g x) (cut-unit (q ++ (q₁ ◂ sub q₂ (η B))) g₁ refl)
cut-unit {X = X} p (⇐L {U = U} {A} {B} p₁ g g₁) eq with subeq (η (B ⇐ A) ⊛ U) (η (at X)) p₁ p eq
... | 2>L1 (gt ∙ eqT () eqp)
cut-unit {X = X} p (⇐L {U = U} {A} {B} p₁ g g₁) refl | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η (at X)) q = cong (λ x → ⇐L p₁ x g₁) (cut-unit q g refl)
cut-unit {X = X} p (⇐L {U = U} {A} {B} p₁ g g₁) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (at X)) q₁ q₂ = 
    cong (λ x → ⇐L (q ++ (q₁ ◂ sub q₂ (η (at X)))) g x) (cut-unit (q ++ (sub q₁ (η B) ▸ q₂)) g₁ refl)
cut-unit {X = X} p (⇐L {U = U} {A} {B} p₁ g g₁) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (at X)) q₁ q₂ = 
    cong (λ x → ⇐L (q ++ (sub q₁ (η (at X)) ▸ q₂)) g x) (cut-unit (q ++ (q₁ ◂ sub q₂ (η B))) g₁ refl)
cut-unit (p ◂ U) (⊗R g g₁) refl = cong (λ x → ⊗R x g₁) (cut-unit p g refl)
cut-unit (T ▸ p) (⊗R g g₁) refl = cong (λ x → ⊗R g x) (cut-unit p g₁ refl)
cut-unit {X = X} p (⊗L {A = A} {B} p₁ g) eq with subeq (η (A ⊗ B)) (η (at X)) p₁ p eq
cut-unit {X = X} p (⊗L {A = A} {B} p₁ g) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η (at X)) q₁ q₂ = 
    cong (λ x → ⊗L (q ++ (q₁ ◂ sub q₂ (η (at X)) )) x) (cut-unit (q ++ (sub q₁ (η A ⊛ η B) ▸ q₂)) g refl)
cut-unit {X = X} p (⊗L {A = A} {B} p₁ g) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η (at X)) q₁ q₂ = 
    cong (λ x → ⊗L (q ++ (sub q₁ (η (at X)) ▸ q₂)) x) (cut-unit (q ++ (q₁ ◂ sub q₂ (η A ⊛ η B))) g refl)
cut-unit ∙ ax refl = refl