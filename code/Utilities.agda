{-# OPTIONS --rewriting #-}

module Utilities where

record Σ {a} (A : Set a) (B : A → Set a) : Set a where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

infixr 4 _,_
infixr 2 _×_

_×_ : ∀ {a} (A : Set a) (B : Set a) → Set a
A × B = Σ A λ _ → B

infix 4 _≡_

data _≡_ {ℓ} {A : Set ℓ} (a : A) : A → Set where
  refl : a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}

sym : ∀{ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

cong : ∀{ℓ}{ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B)
  → ∀ {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀{ℓ}{ℓ'} {A : Set ℓ} (P : A → Set ℓ')
  → ∀ {x y} → x ≡ y → P x → P y
subst P refl p = p

{-# BUILTIN REWRITE _≡_ #-}

