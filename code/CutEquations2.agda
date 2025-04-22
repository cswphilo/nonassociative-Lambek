{-# OPTIONS --rewriting #-}

module CutEquations2 where

open import Relation.Binary.PropositionalEquality hiding ([_]; _≗_) 
open import Data.Product
open import Data.Empty
open import Fma
open import SeqCalc
open import Cut
open import SubEqProperties
open import CutEquations

cut-cong1 : ∀ {T U W A C} (p : Path T)
  → {f f' : U ⊢ A} 
  → (g : W ⊢ C)
  → (eq : W ≡ sub p (η A))
  → (eq' : f ≗ f')
  → cut p f (subst-cxt eq g) ≗ cut p f' (subst-cxt eq g)

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


cut-cong1 p {f} {f'} (⇒R g) refl eq' = cut⇒R≗ p f g ∘ (⇒R (cut-cong1 (η _ ▸ p) g refl eq') ∘ (~ cut⇒R≗ p f' g))
cut-cong1 p {f} {f'} (⇐R g) refl eq' = cut⇐R≗ p f g ∘ (⇐R (cut-cong1 (p ◂ η _) g refl eq') ∘ (~ cut⇐R≗ p f' g))
cut-cong1 p (⇒L p₁ g g₁) eq eq' with subeq _ _ p₁ p eq
cut-cong1 ._ {f} {f'} (⇒L p₁ g g₁) refl eq' | 2>L1 (gt q refl refl refl) = 
  cut⇒L≗ p₁ q g₁ f g 
  ∘ (⇒L (cut-cong1 q g refl eq') refl 
  ∘ (~ cut⇒L≗ p₁ q g₁ f' g))
cut-cong1 ._ (⇒L p₁ g g₁) refl refl | 2>R1 (gt ∙ refl refl refl) = refl
cut-cong1 ._ (⇒L p₁ g g₁) refl (~ eq') | 2>R1 (gt ∙ refl refl refl) = ~ cut-cong1 _ (⇒L p₁ g g₁) refl eq'
cut-cong1 ._ (⇒L p₁ g g₁) refl (eq' ∘ eq'') | 2>R1 (gt ∙ refl refl refl) = 
  cut-cong1 _ (⇒L p₁ g g₁) refl eq' ∘ cut-cong1 _ (⇒L p₁ g g₁) refl  eq''
cut-cong1 ._ (⇒L {U = U} {A = A} {B} p₁ g g₁) refl (⇒R eq') | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 p₁ U (η (A ⇒ B)) ∙ = cut-cong1 p₁ g₁ refl (cut-cong2 (∙ ◂ _) g eq')
cut-cong1 ._ (⇒L p₁ g g₁) refl (⇒L eq' eq'') | 2>R1 (gt ∙ refl refl refl) = ⇒L eq' (cut-cong1 (p₁ ++ (_ ▸ ∙)) (⇒L p₁ g g₁) refl eq'')
cut-cong1 ._ (⇒L p₁ g g₁) refl (⇐L eq' eq'') | 2>R1 (gt ∙ refl refl refl) = ⇐L eq' (cut-cong1 (p₁ ++ (_ ▸ ∙)) (⇒L p₁ g g₁) refl eq'')
cut-cong1 ._ (⇒L p₁ g g₁) refl (⊗L eq') | 2>R1 (gt ∙ refl refl refl) = ⊗L (cut-cong1 (p₁ ++ (_ ▸ ∙)) (⇒L p₁ g g₁) refl eq')
cut-cong1 ._ (⇒L {U = U} {A = A} {B} p₁ g g₁) refl (⇒L⇒R {p = p} {f} {g = g₂}) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 p₁ U (η (A ⇒ B)) ∙ = ~ cut-cong1 p₁ g₁ refl (cut⇒L≗1/\2 ∙ ∙ p f g g₂)
cut-cong1 ._ (⇒L {U = U} {A = A} {B} p₁ g g₁) refl (⇐L⇒R {p = p} {f} {g = g₂}) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 p₁ U (η (A ⇒ B)) ∙ = ~ cut-cong1 p₁ g₁ refl (cut⇐L≗1/\2 ∙ ∙ p f g g₂) 
cut-cong1 ._ (⇒L {U = U} {A = A} {B} p₁ g g₁) refl (⊗L⇒R {p = p} {f}) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 p₁ U (η (A ⇒ B)) ∙ = ~ cut-cong1 p₁ g₁ refl (cut⊗L≗1/\2 ∙ ∙ p g f)
cut-cong1 ._ (⇒L p₁ g g₁) refl (⊗L⊗L {p = p}) | 2>R1 (gt ∙ refl refl refl) = ⊗L⊗L {p = p₁ ++ (_ ▸ p)}
cut-cong1 ._ (⇒L p₁ g g₁) refl (⊗L⇒L₁ {p' = p'}) | 2>R1 (gt ∙ refl refl refl) = ⊗L⇒L₁ {p' = p₁ ++ (_ ▸ p')}
cut-cong1 ._ (⇒L p₁ g g₁) refl (⊗L⇒L₂1/\2 {p = p}) | 2>R1 (gt ∙ refl refl refl) = ⊗L⇒L₂1/\2 {p = p₁ ++ (_ ▸ p)}
cut-cong1 ._ (⇒L p₁ g g₁) refl (⊗L⇒L₂2/\1 {p = p}) | 2>R1 (gt ∙ refl refl refl) = ⊗L⇒L₂2/\1 {p = p₁ ++ (_ ▸ p)}
cut-cong1 ._ (⇒L p₁ g g₁) refl (⊗L⇐L₁ {p' = p'}) | 2>R1 (gt ∙ refl refl refl) = ⊗L⇐L₁ {p' = p₁ ++ (_ ▸ p')}
cut-cong1 ._ (⇒L p₁ g g₁) refl (⊗L⇐L₂1/\2 {p = p}) | 2>R1 (gt ∙ refl refl refl) = ⊗L⇐L₂1/\2 {p = p₁ ++ (_ ▸ p)}
cut-cong1 ._ (⇒L p₁ g g₁) refl (⊗L⇐L₂2/\1 {p = p}) | 2>R1 (gt ∙ refl refl refl) = ⊗L⇐L₂2/\1 {p = p₁ ++ (_ ▸ p)}
cut-cong1 ._ (⇒L p₁ g g₁) refl (⇒L⇒L {r = r}) | 2>R1 (gt ∙ refl refl refl) = ⇒L⇒L {r = p₁ ++ (_ ▸ r)}
cut-cong1 ._ (⇒L p₁ g g₁) refl (⇒L⇒L₂ {p = p}) | 2>R1 (gt ∙ refl refl refl) = ⇒L⇒L₂ {p = p₁ ++ (_ ▸ p)}
cut-cong1 ._ (⇒L p₁ g g₁) refl (⇒L⇐L {r = r}) | 2>R1 (gt ∙ refl refl refl) = ⇒L⇐L {r = p₁ ++ (_ ▸ r)}
cut-cong1 ._ (⇒L p₁ g g₁) refl (⇒L⇐L₂ {p = p}) | 2>R1 (gt ∙ refl refl refl) = ⇒L⇐L₂ {p = p₁ ++ (_ ▸ p)}
cut-cong1 ._ (⇒L p₁ g g₁) refl (⇐L⇒L {r = r}) | 2>R1 (gt ∙ refl refl refl) = ⇐L⇒L {r = p₁ ++ (_ ▸ r)}
cut-cong1 ._ (⇒L p₁ g g₁) refl (⇐L⇒L₂ {p = p}) | 2>R1 (gt ∙ refl refl refl) = ⇐L⇒L₂ {p = p₁ ++ (_ ▸ p)}
cut-cong1 ._ (⇒L p₁ g g₁) refl (⇐L⇐L {r = r}) | 2>R1 (gt ∙ refl refl refl) = ⇐L⇐L {r = p₁ ++ (_ ▸ r)}
cut-cong1 ._ (⇒L p₁ g g₁) refl (⇐L⇐L₂ {p = p}) | 2>R1 (gt ∙ refl refl refl) = ⇐L⇐L₂ {p = p₁ ++ (_ ▸ p)}
cut-cong1 ._ {f} {f'} (⇒L {A = A} {B} ._ g g₁) refl eq' | 1/\2 (disj q q₁ q₂ refl refl refl refl) = 
  cut⇒L≗2/\1 q q₁ q₂ g f g₁ 
  ∘ (⇒L refl (cut-cong1 (q ++ (sub q₁ (η _) ▸ q₂)) g₁ refl eq') 
  ∘ (~ cut⇒L≗2/\1 q q₁ q₂ g f' g₁))
cut-cong1 ._ {f} {f'} (⇒L {A = A} {B} ._ g g₁) refl eq' | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 
  cut⇒L≗1/\2 q q₁ q₂ g f g₁ 
  ∘ (⇒L refl (cut-cong1 (q ++ (q₁ ◂ sub q₂ (η _))) g₁ refl eq') 
  ∘ (~ cut⇒L≗1/\2 q q₁ q₂ g f' g₁))
cut-cong1 p (⇐L p₁ g g₁) eq eq' with subeq _ _ p₁ p eq
cut-cong1 ._ (⇐L p₁ g g₁) refl refl | 2>L1 (gt ∙ refl refl refl) = refl
cut-cong1 ._ (⇐L p₁ g g₁) refl (~ eq') | 2>L1 (gt ∙ refl refl refl) = ~ cut-cong1 _ (⇐L p₁ g g₁) refl eq'
cut-cong1 ._ (⇐L p₁ g g₁) refl (eq' ∘ eq'') | 2>L1 (gt ∙ refl refl refl) = 
  cut-cong1 _ (⇐L p₁ g g₁) refl eq' ∘ cut-cong1 _ (⇐L p₁ g g₁) refl  eq''
cut-cong1 ._ (⇐L {U = U} {A = A} {B} p₁ g g₁) refl (⇐R eq') | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 p₁ U (η (B ⇐ A)) ∙ = cut-cong1 p₁ g₁ refl (cut-cong2 (_ ▸ ∙) g eq')
cut-cong1 ._ (⇐L p₁ g g₁) refl (⇒L eq' eq'') | 2>L1 (gt ∙ refl refl refl) = ⇒L eq' (cut-cong1 (p₁ ++ (∙ ◂ _)) (⇐L p₁ g g₁) refl eq'')
cut-cong1 ._ (⇐L p₁ g g₁) refl (⇐L eq' eq'') | 2>L1 (gt ∙ refl refl refl) = ⇐L eq' (cut-cong1 (p₁ ++ (∙ ◂ _)) (⇐L p₁ g g₁) refl eq'')
cut-cong1 ._ (⇐L p₁ g g₁) refl (⊗L eq') | 2>L1 (gt ∙ refl refl refl) = ⊗L (cut-cong1 (p₁ ++ (∙ ◂ _)) (⇐L p₁ g g₁) refl eq')
cut-cong1 ._ (⇐L {U = U} {A = A} {B} p₁ g g₁) refl (⇒L⇐R {p = p} {f} {g = g₂}) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 p₁ U (η (B ⇐ A)) ∙ = ~ cut-cong1 p₁ g₁ refl (cut⇒L≗2/\1 ∙ p ∙ f g g₂)
cut-cong1 ._ (⇐L {U = U} {A = A} {B} p₁ g g₁) refl (⇐L⇐R {p = p} {f} {g = g₂}) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 p₁ U (η (B ⇐ A)) ∙ = ~ cut-cong1 p₁ g₁ refl (cut⇐L≗2/\1 ∙ p ∙ f g g₂)
cut-cong1 ._ (⇐L {U = U} {A = A} {B} p₁ g g₁) refl (⊗L⇐R {p = p} {f}) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 p₁ U (η (B ⇐ A)) ∙ = ~ cut-cong1 p₁ g₁ refl (cut⊗L≗2/\1 ∙ p ∙ g f)
cut-cong1 ._ (⇐L p₁ g g₁) refl (⊗L⊗L {p = p}) | 2>L1 (gt ∙ refl refl refl) = ⊗L⊗L {p = p₁ ++ (p ◂ _)}
cut-cong1 ._ (⇐L p₁ g g₁) refl (⊗L⇒L₁ {p' = p'}) | 2>L1 (gt ∙ refl refl refl) = ⊗L⇒L₁ {p' = p₁ ++ (p' ◂ _)}
cut-cong1 ._ (⇐L p₁ g g₁) refl (⊗L⇒L₂1/\2 {p = p}) | 2>L1 (gt ∙ refl refl refl) = ⊗L⇒L₂1/\2 {p = p₁ ++ (p ◂ _)}
cut-cong1 ._ (⇐L p₁ g g₁) refl (⊗L⇒L₂2/\1 {p = p}) | 2>L1 (gt ∙ refl refl refl) = ⊗L⇒L₂2/\1 {p = p₁ ++ (p ◂ _)}
cut-cong1 ._ (⇐L p₁ g g₁) refl (⊗L⇐L₁ {p' = p'}) | 2>L1 (gt ∙ refl refl refl) = ⊗L⇐L₁ {p' = p₁ ++ (p' ◂ _)}
cut-cong1 ._ (⇐L p₁ g g₁) refl (⊗L⇐L₂1/\2 {p = p}) | 2>L1 (gt ∙ refl refl refl) = ⊗L⇐L₂1/\2 {p = p₁ ++ (p ◂ _)}
cut-cong1 ._ (⇐L p₁ g g₁) refl (⊗L⇐L₂2/\1 {p = p}) | 2>L1 (gt ∙ refl refl refl) = ⊗L⇐L₂2/\1 {p = p₁ ++ (p ◂ _)}
cut-cong1 ._ (⇐L p₁ g g₁) refl (⇒L⇒L {r = r}) | 2>L1 (gt ∙ refl refl refl) = ⇒L⇒L {r = p₁ ++ (r ◂ _)}
cut-cong1 ._ (⇐L p₁ g g₁) refl (⇒L⇒L₂ {p = p}) | 2>L1 (gt ∙ refl refl refl) = ⇒L⇒L₂ {p = p₁ ++ (p ◂ _)}
cut-cong1 ._ (⇐L p₁ g g₁) refl (⇒L⇐L {r = r}) | 2>L1 (gt ∙ refl refl refl) = ⇒L⇐L {r = p₁ ++ (r ◂ _)}
cut-cong1 ._ (⇐L p₁ g g₁) refl (⇒L⇐L₂ {p = p}) | 2>L1 (gt ∙ refl refl refl) = ⇒L⇐L₂ {p = p₁ ++ (p ◂ _)}
cut-cong1 ._ (⇐L p₁ g g₁) refl (⇐L⇒L {r = r}) | 2>L1 (gt ∙ refl refl refl) = ⇐L⇒L {r = p₁ ++ (r ◂ _)}
cut-cong1 ._ (⇐L p₁ g g₁) refl (⇐L⇒L₂ {p = p}) | 2>L1 (gt ∙ refl refl refl) = ⇐L⇒L₂ {p = p₁ ++ (p ◂ _)}
cut-cong1 ._ (⇐L p₁ g g₁) refl (⇐L⇐L {r = r}) | 2>L1 (gt ∙ refl refl refl) = ⇐L⇐L {r = p₁ ++ (r ◂ _)}
cut-cong1 ._ (⇐L p₁ g g₁) refl (⇐L⇐L₂ {p = p}) | 2>L1 (gt ∙ refl refl refl) = ⇐L⇐L₂ {p = p₁ ++ (p ◂ _)}
cut-cong1 ._ {f} {f'} (⇐L p₁ g g₁) refl eq' | 2>R1 (gt q refl refl refl) = 
  cut⇐L≗ p₁ q g₁ f g 
  ∘ (⇐L (cut-cong1 q g refl eq') refl 
  ∘ (~ cut⇐L≗ p₁ q g₁ f' g))
cut-cong1 ._ {f} {f'} (⇐L {A = A} {B} ._ g g₁) refl eq' | 1/\2 (disj q q₁ q₂ refl refl refl refl) = 
  cut⇐L≗2/\1 q q₁ q₂ g f g₁ 
  ∘ (⇐L refl (cut-cong1 (q ++ (sub q₁ (η _) ▸ q₂)) g₁ refl eq') 
  ∘ (~ cut⇐L≗2/\1 q q₁ q₂ g f' g₁))
cut-cong1 ._ {f} {f'} (⇐L {A = A} {B} ._ g g₁) refl eq' | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 
  cut⇐L≗1/\2 q q₁ q₂ g f g₁ 
  ∘ (⇐L refl (cut-cong1 (q ++ (q₁ ◂ sub q₂ (η _))) g₁ refl eq') 
  ∘ (~ cut⇐L≗1/\2 q q₁ q₂ g f' g₁))
cut-cong1 (p ◂ U) {f} {f'} (⊗R g g₁) refl eq' = cut⊗R≗₁ p f g g₁ ∘ (⊗R (cut-cong1 p g refl eq') refl ∘ (~ cut⊗R≗₁ p f' g g₁))
cut-cong1 (T ▸ p) {f} {f'} (⊗R g g₁) refl eq' = cut⊗R≗₂ p f g g₁ ∘ (⊗R refl (cut-cong1 p g₁ refl eq') ∘ (~ cut⊗R≗₂ p f' g g₁))
cut-cong1 p (⊗L p₁ g) eq eq' with subeq _ _ p₁ p eq
cut-cong1 p (⊗L p g) refl refl | 1≡2 (same refl refl refl) = refl
cut-cong1 p (⊗L p g) refl (~ eq') | 1≡2 (same refl refl refl) = ~ cut-cong1 p (⊗L p g) refl eq'
cut-cong1 p (⊗L p g) refl (eq' ∘ eq'') | 1≡2 (same refl refl refl) = 
  cut-cong1 p (⊗L p g) refl eq' ∘ cut-cong1 p (⊗L p g) refl eq''
cut-cong1 p (⊗L p g) refl (⇒L eq' eq'') | 1≡2 (same refl refl refl) = ⇒L eq' (cut-cong1 p (⊗L p g) refl eq'')
cut-cong1 p (⊗L p g) refl (⇐L eq' eq'') | 1≡2 (same refl refl refl) = ⇐L eq' (cut-cong1 p (⊗L p g) refl eq'')
cut-cong1 p (⊗L p g) refl (⊗R {A = A} {B} {f' = f'} {g₁} eq' eq'') | 1≡2 (same refl refl refl)
  rewrite subeq-1≡2 p (η (A ⊗ B)) = 
    cut-cong1 (p ++ (∙ ◂ _)) (cut (p ++ (η A ▸ ∙)) g₁ g) refl eq' 
    ∘ cut-cong2 (p ++ (∙ ◂ _)) f' (cut-cong1 (p ++ (η _ ▸ ∙)) g refl eq'')
cut-cong1 p (⊗L p g) refl (⊗L eq') | 1≡2 (same refl refl refl) = ⊗L (cut-cong1 p (⊗L p g) refl eq')
cut-cong1 p (⊗L {A = A} {B} p g) refl ⇒L⊗R₁ | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) = refl
cut-cong1 p (⊗L {A = A} {B} p g) refl (⇒L⊗R₂ {p = p₁} {f} {g₁} {h}) | 1≡2 (same refl refl refl)
  rewrite subeq-1≡2 p (η (A ⊗ B)) = ~ cut⇒L≗1/\2 p ∙ p₁ f g₁ (cut (p ++ (η A ▸ ∙)) h g)
cut-cong1 p (⊗L {A = A} {B} p g) refl ⇐L⊗R₁ | 1≡2 (same refl refl refl)
  rewrite subeq-1≡2 p (η (A ⊗ B)) = refl
cut-cong1 p (⊗L {A = A} {B} p g) refl (⇐L⊗R₂ {p = p₁} {f} {g₁} {h}) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) = ~ cut⇐L≗1/\2 p ∙ p₁ f g₁ (cut (p ++ (η A ▸ ∙)) h g)
cut-cong1 p (⊗L {A = A} {B} p g) refl ⊗L⊗R₁ | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) = refl
cut-cong1 p (⊗L {A = A} {B} p g) refl (⊗L⊗R₂ {p = p₁} {f = f} {g₁}) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) = ~ cut⊗L≗1/\2 p ∙ p₁ f (cut (p ++ (η A ▸ ∙)) g₁ g)
cut-cong1 p (⊗L p g) refl (⊗L⊗L {p = p₁}) | 1≡2 (same refl refl refl) = ⊗L⊗L {p = p ++ p₁}
cut-cong1 p (⊗L p g) refl (⊗L⇒L₁ {p' = p'}) | 1≡2 (same refl refl refl) = ⊗L⇒L₁ {p' = p ++ p'}
cut-cong1 p (⊗L p g) refl (⊗L⇒L₂1/\2 {p = p₁}) | 1≡2 (same refl refl refl) = ⊗L⇒L₂1/\2 {p = p ++ p₁}
cut-cong1 p (⊗L p g) refl (⊗L⇒L₂2/\1 {p = p₁}) | 1≡2 (same refl refl refl) = ⊗L⇒L₂2/\1 {p = p ++ p₁}
cut-cong1 p (⊗L p g) refl (⊗L⇐L₁ {p' = p'}) | 1≡2 (same refl refl refl) = ⊗L⇐L₁ {p' = p ++ p'}
cut-cong1 p (⊗L p g) refl (⊗L⇐L₂1/\2 {p = p₁}) | 1≡2 (same refl refl refl) = ⊗L⇐L₂1/\2 {p = p ++ p₁}
cut-cong1 p (⊗L p g) refl (⊗L⇐L₂2/\1 {p = p₁}) | 1≡2 (same refl refl refl) = ⊗L⇐L₂2/\1 {p = p ++ p₁}
cut-cong1 p (⊗L p g) refl (⇒L⇒L {r = r}) | 1≡2 (same refl refl refl) = ⇒L⇒L {r = p ++ r}
cut-cong1 p (⊗L p g) refl (⇒L⇒L₂ {p = p₁}) | 1≡2 (same refl refl refl) = ⇒L⇒L₂ {p = p ++ p₁}
cut-cong1 p (⊗L p g) refl (⇒L⇐L {r = r}) | 1≡2 (same refl refl refl) = ⇒L⇐L {r = p ++ r}
cut-cong1 p (⊗L p g) refl (⇒L⇐L₂ {p = p₁}) | 1≡2 (same refl refl refl) = ⇒L⇐L₂ {p = p ++ p₁}
cut-cong1 p (⊗L p g) refl (⇐L⇒L {r = r}) | 1≡2 (same refl refl refl) = ⇐L⇒L {r = p ++ r}
cut-cong1 p (⊗L p g) refl (⇐L⇒L₂ {p = p₁}) | 1≡2 (same refl refl refl) = ⇐L⇒L₂ {p = p ++ p₁}
cut-cong1 p (⊗L p g) refl (⇐L⇐L {r = r}) | 1≡2 (same refl refl refl) = ⇐L⇐L {r = p ++ r}
cut-cong1 p (⊗L p g) refl (⇐L⇐L₂ {p = p₁}) | 1≡2 (same refl refl refl) = ⇐L⇐L₂ {p = p ++ p₁}
cut-cong1 ._ {f} {f'} (⊗L ._ g) refl eq' | 1/\2 (disj q q₁ q₂ refl refl refl refl) = 
  cut⊗L≗2/\1 q q₁ q₂ f g 
  ∘ (⊗L (cut-cong1 (q ++ (sub q₁ (η _ ⊛ η _) ▸ q₂)) g refl eq') 
  ∘ (~ cut⊗L≗2/\1 q q₁ q₂ f' g))
cut-cong1 ._ {f} {f'} (⊗L ._ g) refl eq' | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 
  cut⊗L≗1/\2 q q₁ q₂ f g 
  ∘ (⊗L (cut-cong1 (q ++ (q₁ ◂ sub q₂ (η _ ⊛ η _))) g refl eq') 
  ∘ (~ cut⊗L≗1/\2 q q₁ q₂ f' g))
cut-cong1 ∙ {f} {f'} ax refl eq' = cutax-right f ∘ (eq' ∘ (~ cutax-right f'))

cut⇒R-cong1 p (⇒R g) refl eq' = ⇒R (cut⇒R-cong1 (η _ ▸ p) g refl eq')
cut⇒R-cong1 p (⇐R g) refl eq' = ⇐R (cut⇒R-cong1 (p ◂ η _) g refl eq')
cut⇒R-cong1 p (⇒L p₁ g g₁) eq eq' with subeq _ _ p₁ p eq
cut⇒R-cong1 p (⇒L p₁ g g₁) refl eq' | 2>L1 (gt q refl refl refl) = ⇒L (cut⇒R-cong1 q g refl eq') refl
cut⇒R-cong1 ._ (⇒L p₁ g g₁) refl eq' | 2>R1 (gt ∙ refl refl refl) = cut-cong1 p₁ g₁ refl (cut-cong2 (∙ ◂ _) g eq') 
cut⇒R-cong1 ._ (⇒L ._ g g₁) refl eq' | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⇒L refl (cut⇒R-cong1 (q ++ (sub q₁ (η _) ▸ q₂)) g₁ refl eq')
cut⇒R-cong1 ._ (⇒L ._ g g₁) refl eq' | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⇒L refl (cut⇒R-cong1 (q ++ (q₁ ◂ sub q₂ (η _))) g₁ refl eq')
cut⇒R-cong1 p (⇐L p₁ g g₁) eq eq' with subeq _ _ p₁ p eq
cut⇒R-cong1 p (⇐L p₁ g g₁) eq eq' | 2>L1 (gt ∙ eqT () eqp)
cut⇒R-cong1 ._ (⇐L p₁ g g₁) refl eq' | 2>R1 (gt q refl refl refl) = ⇐L (cut⇒R-cong1 q g refl eq') refl
cut⇒R-cong1 ._ (⇐L ._ g g₁) refl eq' | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⇐L refl (cut⇒R-cong1 (q ++ (sub q₁ (η _) ▸ q₂)) g₁ refl eq')
cut⇒R-cong1 ._ (⇐L ._ g g₁) refl eq' | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⇐L refl (cut⇒R-cong1 (q ++ (q₁ ◂ sub q₂ (η _))) g₁ refl eq')
cut⇒R-cong1 (p ◂ U) (⊗R g g₁) refl eq' = ⊗R (cut⇒R-cong1 p g refl eq') refl
cut⇒R-cong1 (T ▸ p) (⊗R g g₁) refl eq' = ⊗R refl (cut⇒R-cong1 p g₁ refl eq')
cut⇒R-cong1 p (⊗L p₁ g) eq eq' with subeq _ _ p₁ p eq
cut⇒R-cong1 ._ (⊗L ._ g) refl eq' | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⊗L (cut⇒R-cong1 (q ++ (sub q₁ (η _ ⊛ η _) ▸ q₂)) g refl eq')
cut⇒R-cong1 ._ (⊗L ._ g) refl eq' | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⊗L (cut⇒R-cong1 (q ++ (q₁ ◂ sub q₂ (η _ ⊛ η _))) g refl eq')
cut⇒R-cong1 ∙ ax () eq'

cut⇐R-cong1 p (⇒R g) refl eq' = ⇒R (cut⇐R-cong1 (η _ ▸ p) g refl eq')
cut⇐R-cong1 p (⇐R g) refl eq' = ⇐R (cut⇐R-cong1 (p ◂ η _) g refl eq')
cut⇐R-cong1 p (⇒L p₁ g g₁) eq eq' with subeq _ _ p₁ p eq
cut⇐R-cong1 p (⇒L p₁ g g₁) refl eq' | 2>L1 (gt q refl refl refl) = ⇒L (cut⇐R-cong1 q g refl eq') refl
cut⇐R-cong1 ._ (⇒L p₁ g g₁) eq eq' | 2>R1 (gt ∙ refl () refl) 
cut⇐R-cong1 ._ (⇒L ._ g g₁) refl eq' | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⇒L refl (cut⇐R-cong1 (q ++ (sub q₁ (η _) ▸ q₂)) g₁ refl eq')
cut⇐R-cong1 ._ (⇒L ._ g g₁) refl eq' | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⇒L refl (cut⇐R-cong1 (q ++ (q₁ ◂ sub q₂ (η _))) g₁ refl eq')
cut⇐R-cong1 p (⇐L p₁ g g₁) eq eq' with subeq _ _ p₁ p eq
cut⇐R-cong1 p (⇐L p₁ g g₁) refl eq' | 2>L1 (gt ∙ refl refl refl) = cut-cong1 p₁ g₁ refl (cut-cong2 (_ ▸ ∙) g eq')
cut⇐R-cong1 ._ (⇐L p₁ g g₁) refl eq' | 2>R1 (gt q refl refl refl) = ⇐L (cut⇐R-cong1 q g refl eq') refl
cut⇐R-cong1 ._ (⇐L ._ g g₁) refl eq' | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⇐L refl (cut⇐R-cong1 (q ++ (sub q₁ (η _) ▸ q₂)) g₁ refl eq')
cut⇐R-cong1 ._ (⇐L ._ g g₁) refl eq' | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⇐L refl (cut⇐R-cong1 (q ++ (q₁ ◂ sub q₂ (η _))) g₁ refl eq')
cut⇐R-cong1 (p ◂ U) (⊗R g g₁) refl eq' = ⊗R (cut⇐R-cong1 p g refl eq') refl
cut⇐R-cong1 (T ▸ p) (⊗R g g₁) refl eq' = ⊗R refl (cut⇐R-cong1 p g₁ refl eq')
cut⇐R-cong1 p (⊗L p₁ g) eq eq' with subeq _ _ p₁ p eq
cut⇐R-cong1 ._ (⊗L ._ g) refl eq' | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⊗L (cut⇐R-cong1 (q ++ (sub q₁ (η _ ⊛ η _) ▸ q₂)) g refl eq')
cut⇐R-cong1 ._ (⊗L ._ g) refl eq' | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⊗L (cut⇐R-cong1 (q ++ (q₁ ◂ sub q₂ (η _ ⊛ η _))) g refl eq')
cut⇐R-cong1 ∙ ax () eq'

cut⊗R-cong1 p (⇒R g) refl eq' eq'' = ⇒R (cut⊗R-cong1 (η _ ▸ p) g refl eq' eq'')
cut⊗R-cong1 p (⇐R g) refl eq' eq'' = ⇐R (cut⊗R-cong1 (p ◂ η _) g refl eq' eq'')
cut⊗R-cong1 p (⇒L p₁ g g₁) eq eq' eq'' with subeq _ _ p₁ p eq
cut⊗R-cong1 p (⇒L p₁ g g₁) refl eq' eq'' | 2>L1 (gt q refl refl refl) = ⇒L (cut⊗R-cong1 q g refl eq' eq'') refl
cut⊗R-cong1 ._ (⇒L p₁ g g₁) eq eq' eq'' | 2>R1 (gt ∙ refl () refl) 
cut⊗R-cong1 ._ (⇒L ._ g g₁) refl eq' eq'' | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⇒L refl (cut⊗R-cong1 (q ++ (sub q₁ (η _) ▸ q₂)) g₁ refl eq' eq'')
cut⊗R-cong1 ._ (⇒L ._ g g₁) refl eq' eq'' | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⇒L refl (cut⊗R-cong1 (q ++ (q₁ ◂ sub q₂ (η _))) g₁ refl eq' eq'')
cut⊗R-cong1 p (⇐L p₁ g g₁) eq eq' eq'' with subeq _ _ p₁ p eq
cut⊗R-cong1 ._ (⇐L p₁ g g₁) eq eq' eq'' | 2>L1 (gt ∙ refl () refl)
cut⊗R-cong1 ._ (⇐L p₁ g g₁) refl eq' eq'' | 2>R1 (gt q refl refl refl) = ⇐L (cut⊗R-cong1 q g refl eq' eq'') refl
cut⊗R-cong1 ._ (⇐L ._ g g₁) refl eq' eq'' | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⇐L refl (cut⊗R-cong1 (q ++ (sub q₁ (η _) ▸ q₂)) g₁ refl eq' eq'')
cut⊗R-cong1 ._ (⇐L ._ g g₁) refl eq' eq'' | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⇐L refl (cut⊗R-cong1 (q ++ (q₁ ◂ sub q₂ (η _))) g₁ refl eq' eq'')
cut⊗R-cong1 (p ◂ U) (⊗R g g₁) refl eq' eq'' = ⊗R (cut⊗R-cong1 p g refl eq' eq'') refl
cut⊗R-cong1 (T ▸ p) (⊗R g g₁) refl eq' eq'' = ⊗R refl (cut⊗R-cong1 p g₁ refl eq' eq'')
cut⊗R-cong1 p (⊗L p₁ g) eq eq' eq'' with subeq _ _ p₁ p eq
cut⊗R-cong1 .p₁ {f' = f'} {f₁ = f₁} (⊗L p₁ g) refl eq' eq'' | 1≡2 (same refl refl refl) = 
  cut-cong1 (p₁ ++ (∙ ◂ _)) (cut (p₁ ++ (η _ ▸ ∙)) f₁ g) refl eq' ∘ cut-cong2 (p₁ ++ (∙ ◂ _)) f' (cut-cong1 (p₁ ++ (η _ ▸ ∙)) g refl eq'')
cut⊗R-cong1 ._ (⊗L ._ g) refl eq' eq'' | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⊗L (cut⊗R-cong1 (q ++ (sub q₁ (η _ ⊛ η _) ▸ q₂)) g refl eq' eq'')
cut⊗R-cong1 ._ (⊗L ._ g) refl eq' eq'' | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⊗L (cut⊗R-cong1 (q ++ (q₁ ◂ sub q₂ (η _ ⊛ η _))) g refl eq' eq'')
cut⊗R-cong1 ∙ ax () eq' eq''


cut-cong2 p ax eq = eq
cut-cong2 p (⇒R f) eq = cut⇒R-cong2 p f refl eq
cut-cong2 p (⇐R f) eq = cut⇐R-cong2 p f refl eq
cut-cong2 p (⇒L p₁ f f₁) eq = ⇒L refl (cut-cong2 p f₁ eq)
cut-cong2 p (⇐L p₁ f f₁) eq = ⇐L refl (cut-cong2 p f₁ eq)
cut-cong2 p (⊗R f f₁) eq = cut⊗R-cong2 p f f₁ refl eq
cut-cong2 p (⊗L p₁ f) eq = ⊗L (cut-cong2 p f eq)

cut⇒R-cong2 p f eq refl = refl
cut⇒R-cong2 p f eq (~ eq') = ~ (cut⇒R-cong2 p f eq eq')
cut⇒R-cong2 p f eq (eq' ∘ eq'') = cut⇒R-cong2 p f eq eq' ∘ cut⇒R-cong2 p f eq eq''
cut⇒R-cong2 p f refl (⇒R eq') = ⇒R (cut⇒R-cong2 (_ ▸ p) f refl eq')
cut⇒R-cong2 p f refl (⇐R eq') = ⇐R (cut⇒R-cong2 (p ◂ _) f refl eq')
cut⇒R-cong2 p f eq (⇒L {p = p₁} eq' eq'') with subeq _ _ p₁ p eq
cut⇒R-cong2 ._ f refl (⇒L {p = _} eq' eq'') | 2>L1 (gt q refl refl refl) = ⇒L (cut⇒R-cong2 q f refl eq') eq''
cut⇒R-cong2 ._ f refl (⇒L {p = p₁} {f₁} eq' eq'') | 2>R1 (gt ∙ refl refl refl) = 
  cut-cong2 p₁ (cut (∙ ◂ _) f₁ f) eq'' ∘ cut-cong1 p₁ _ refl (cut-cong1 (∙ ◂ _) f refl eq')
cut⇒R-cong2 ._ f refl (⇒L {B = B} eq' eq'') | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⇒L eq' (cut⇒R-cong2 (q ++ (sub q₁ (η B) ▸ q₂)) f refl eq'')
cut⇒R-cong2 ._ f refl (⇒L {B = B} eq' eq'') | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⇒L eq' (cut⇒R-cong2 (q ++ (q₁ ◂ sub q₂ (η B))) f refl eq'')
cut⇒R-cong2 p f eq (⇐L {p = p₁} eq' eq'') with subeq _ _ p₁ p eq
cut⇒R-cong2 ._ f eq (⇐L eq' eq'') | 2>L1 (gt ∙ refl () refl)
cut⇒R-cong2 ._ f refl (⇐L eq' eq'') | 2>R1 (gt q refl refl refl) = ⇐L (cut⇒R-cong2 q f refl eq') eq''
cut⇒R-cong2 ._ f refl (⇐L {B = B} eq' eq'') | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⇐L eq' (cut⇒R-cong2 (q ++ (sub q₁ (η B) ▸ q₂)) f refl eq'')
cut⇒R-cong2 ._ f refl (⇐L {B = B} eq' eq'') | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⇐L eq' (cut⇒R-cong2 (q ++ (q₁ ◂ sub q₂ (η B))) f refl eq'')
cut⇒R-cong2 (p ◂ U) f refl (⊗R eq' eq'') = ⊗R (cut⇒R-cong2 p f refl eq') eq''
cut⇒R-cong2 (T ▸ p) f refl (⊗R eq' eq'') = ⊗R eq' (cut⇒R-cong2 p f refl eq'')
cut⇒R-cong2 p f eq (⊗L {p = p₁} eq') with subeq _ _ p₁ p eq
cut⇒R-cong2 ._ f refl (⊗L {A = A} {B} eq') | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⊗L (cut⇒R-cong2 (q ++ (sub q₁ (η A ⊛ η B) ▸ q₂)) f refl eq')
cut⇒R-cong2 ._ f refl (⊗L {A = A} {B} eq') | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⊗L (cut⇒R-cong2 (q ++ (q₁ ◂ sub q₂ (η A ⊛ η B))) f refl eq')
cut⇒R-cong2 p f eq (⇒L⇒R {p = p₁}) with subeq _ _ p₁ p eq
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇒L⇒R {A = A} {B} {p = p₁}) | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η (A' ⇒ B')) q = ⇒L⇒R
cut⇒R-cong2 ._ f refl (⇒L⇒R {U = U₁} {A} {B} {p = p₁} {f'}) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 p₁ U₁ (η (A ⇒ B)) ∙ = cut⇒R≗ p₁ (cut (∙ ◂ _) f' f) _
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇒L⇒R {U = U₁} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U₁ ⊛ η (A ⇒ B)) (η (A' ⇒ B')) q₁ q₂ = ⇒L⇒R
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇒L⇒R {U = U₁} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U₁ ⊛ η (A ⇒ B)) (η (A' ⇒ B')) q₁ q₂ = ⇒L⇒R
cut⇒R-cong2 p f eq (⇐L⇒R {p = p₁}) with subeq _ _ p₁ p eq
cut⇒R-cong2 ._ f eq (⇐L⇒R) | 2>L1 (gt ∙ refl () refl)
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇐L⇒R {A = A} {B} {p = p₁}) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η (A' ⇒ B')) q = ⇐L⇒R
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇐L⇒R {U = U₁} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U₁) (η (A' ⇒ B')) q₁ q₂ = ⇐L⇒R
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇐L⇒R {U = U₁} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U₁) (η (A' ⇒ B')) q₁ q₂ = ⇐L⇒R
cut⇒R-cong2 p f eq (⊗L⇒R {p = p₁}) with subeq _ _ p₁ p eq
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⊗L⇒R {A = A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η (A' ⇒ B')) q₁ q₂ = ⊗L⇒R
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⊗L⇒R {A = A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η (A' ⇒ B')) q₁ q₂ = ⊗L⇒R
cut⇒R-cong2 p f eq (⇒L⇐R {p = p₁}) with subeq _ _ p₁ p eq
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇒L⇐R {U = U₁} {A} {B} {p = p₁}) | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η (A' ⇒ B')) q = ⇒L⇐R
cut⇒R-cong2 ._ f refl (⇒L⇐R {U = U₁} {A} {B} {p = p₁} {f'}) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 p₁ U₁ (η (A ⇒ B)) ∙ = cut⇐R≗ p₁ (cut (∙ ◂ _) f' f) _
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇒L⇐R {U = U₁} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U₁ ⊛ η (A ⇒ B)) (η (A' ⇒ B')) q₁ q₂ = ⇒L⇐R
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇒L⇐R {U = U₁} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U₁ ⊛ η (A ⇒ B)) (η (A' ⇒ B')) q₁ q₂ = ⇒L⇐R
cut⇒R-cong2 p f eq (⇐L⇐R {p = p₁}) with subeq _ _ p₁ p eq
cut⇒R-cong2 ._ f eq (⇐L⇐R) | 2>L1 (gt ∙ refl () refl)
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇐L⇐R {A = A} {B} {p = p₁}) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η (A' ⇒ B')) q = ⇐L⇐R
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇐L⇐R {U = U₁} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U₁) (η (A' ⇒ B')) q₁ q₂ = ⇐L⇐R
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇐L⇐R {U = U₁} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U₁) (η (A' ⇒ B')) q₁ q₂ = ⇐L⇐R
cut⇒R-cong2 p f eq (⊗L⇐R {p = p₁}) with subeq _ _ p₁ p eq
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⊗L⇐R {A = A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η (A' ⇒ B')) q₁ q₂ = ⊗L⇐R
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⊗L⇐R {A = A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η (A' ⇒ B')) q₁ q₂ = ⊗L⇐R
cut⇒R-cong2 p f eq (⇒L⊗R₁ {V = V} {p = p₁}) with subeq _ _ (p₁ ◂ V) p eq
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇒L⊗R₁ {A = A} {B} {p = p₁}) | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η (A' ⇒ B')) q = ⇒L⊗R₁
cut⇒R-cong2 ._ f refl (⇒L⊗R₁ {U = U₁} {A = A} {B} {p = p₁} {f'}) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 p₁ U₁ (η (A ⇒ B)) ∙ = cut⊗R≗₁ p₁ (cut (∙ ◂ _) f' f) _ _
cut⇒R-cong2 ._ f refl (⇒L⊗R₁) | 1/\2 (disj ∙ q₁ q₂ refl refl refl refl) = ⇒L⊗R₁
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇒L⊗R₁ {U = U₁} {A = A} {B}) | 1/\2 (disj (q ◂ U) q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U₁ ⊛ η (A ⇒ B)) (η (A' ⇒ B')) q₁ q₂ = ⇒L⊗R₁
cut⇒R-cong2 p f eq (⇒L⊗R₁) | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl () refl)
cut⇒R-cong2 ._ f eq (⇒L⊗R₁) | 2/\1 (disj ∙ q₁ q₂ refl refl refl ())
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇒L⊗R₁ {U = U₁} {A = A} {B}) | 2/\1 (disj (q ◂ U) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U₁ ⊛ η (A ⇒ B)) (η (A' ⇒ B')) q₁ q₂ = ⇒L⊗R₁
cut⇒R-cong2 ._ f eq (⇒L⊗R₁) | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl ())
cut⇒R-cong2 p f eq (⇒L⊗R₂ {V = V} {p = p₁}) with subeq _ _ (V ▸ p₁) p eq
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇒L⊗R₂ {A = A} {B} {p = p₁}) | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η (A' ⇒ B')) q = ⇒L⊗R₂
cut⇒R-cong2 ._ f refl (⇒L⊗R₂ {U = U₁} {A = A} {B} {p = p₁} {f'}) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 p₁ U₁ (η (A ⇒ B)) ∙ = cut⊗R≗₂ p₁ (cut (∙ ◂ _) f' f) _ _ 
cut⇒R-cong2 ._ f eq ⇒L⊗R₂ | 1/\2 (disj ∙ q₁ q₂ refl refl () refl)
cut⇒R-cong2 ._ f eq ⇒L⊗R₂ | 1/\2 (disj (q ◂ U) q₁ q₂ refl refl () refl) 
cut⇒R-cong2 {A = A'} {B'} p f refl (⇒L⊗R₂ {U = U₁} {A = A} {B}) | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U₁ ⊛ η (A ⇒ B)) (η (A' ⇒ B')) q₁ q₂ = ⇒L⊗R₂
cut⇒R-cong2 ._ f refl ⇒L⊗R₂ | 2/\1 (disj ∙ q₁ q₂ refl refl refl refl) = ⇒L⊗R₂
cut⇒R-cong2 ._ f eq ⇒L⊗R₂ | 2/\1 (disj (q ◂ U) q₁ q₂ refl refl refl ()) 
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇒L⊗R₂ {U = U₁} {A = A} {B}) | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U₁ ⊛ η (A ⇒ B)) (η (A' ⇒ B')) q₁ q₂ = ⇒L⊗R₂
cut⇒R-cong2 p f eq (⇐L⊗R₁ {V = V} {p = p₁}) with subeq _ _ (p₁ ◂ V) p eq
cut⇒R-cong2 ._ f eq (⇐L⊗R₁) | 2>L1 (gt ∙ refl () refl)
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇐L⊗R₁ {U = U₁} {A = A} {B} {p = p₁} {f'}) | 2>R1 (gt q refl refl refl)
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η (A' ⇒ B')) q = ⇐L⊗R₁
cut⇒R-cong2 ._ f refl (⇐L⊗R₁) | 1/\2 (disj ∙ q₁ q₂ refl refl refl refl) = ⇐L⊗R₁
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇐L⊗R₁ {U = U₁} {A = A} {B}) | 1/\2 (disj (q ◂ U) q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U₁) (η (A' ⇒ B')) q₁ q₂ = ⇐L⊗R₁
cut⇒R-cong2 p f eq (⇐L⊗R₁) | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl () refl)
cut⇒R-cong2 ._ f eq (⇐L⊗R₁) | 2/\1 (disj ∙ q₁ q₂ refl refl refl ())
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇐L⊗R₁ {U = U₁} {A = A} {B}) | 2/\1 (disj (q ◂ U) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U₁) (η (A' ⇒ B')) q₁ q₂ = ⇐L⊗R₁
cut⇒R-cong2 ._ f eq (⇐L⊗R₁) | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl ())
cut⇒R-cong2 p f eq (⇐L⊗R₂ {V = V} {p = p₁}) with subeq _ _ (V ▸ p₁) p eq
cut⇒R-cong2 ._ f eq (⇐L⊗R₂ {U = U₁} {A = A} {B} {p = p₁} {f'}) | 2>L1 (gt ∙ refl () refl) 
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇐L⊗R₂ {A = A} {B} {p = p₁}) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η (A' ⇒ B')) q = ⇐L⊗R₂
cut⇒R-cong2 ._ f eq (⇐L⊗R₂) | 1/\2 (disj ∙ q₁ q₂ refl refl () refl)
cut⇒R-cong2 ._ f eq (⇐L⊗R₂) | 1/\2 (disj (q ◂ U) q₁ q₂ refl refl () refl) 
cut⇒R-cong2 {A = A'} {B'} p f refl (⇐L⊗R₂ {U = U₁} {A = A} {B}) | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U₁) (η (A' ⇒ B')) q₁ q₂ = ⇐L⊗R₂
cut⇒R-cong2 ._ f refl (⇐L⊗R₂) | 2/\1 (disj ∙ q₁ q₂ refl refl refl refl) = ⇐L⊗R₂
cut⇒R-cong2 ._ f eq (⇐L⊗R₂) | 2/\1 (disj (q ◂ U) q₁ q₂ refl refl refl ()) 
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⇐L⊗R₂ {U = U₁} {A = A} {B}) | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U₁) (η (A' ⇒ B')) q₁ q₂ = ⇐L⊗R₂
cut⇒R-cong2 p f eq (⊗L⊗R₁ {U = U} {p = p₁}) with subeq _ _ (p₁ ◂ U) p eq
cut⇒R-cong2 ._ f refl ⊗L⊗R₁ | 1/\2 (disj ∙ q₁ q₂ refl refl refl refl) = ⊗L⊗R₁
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⊗L⊗R₁ {A = A} {B}) | 1/\2 (disj (q ◂ U) q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η (A' ⇒ B')) q₁ q₂ = ⊗L⊗R₁
cut⇒R-cong2 p f eq ⊗L⊗R₁ | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl () eqp₂)
cut⇒R-cong2 ._ f eq ⊗L⊗R₁ | 2/\1 (disj ∙ q₁ q₂ refl refl refl ())
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⊗L⊗R₁ {A = A} {B} {p = _}) | 2/\1 (disj (q ◂ U) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η (A' ⇒ B')) q₁ q₂ = ⊗L⊗R₁
cut⇒R-cong2 ._ f eq ⊗L⊗R₁ | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl ())
cut⇒R-cong2 p f eq (⊗L⊗R₂ {U = U} {p = p₁}) with subeq _ _ (U ▸ p₁) p eq
cut⇒R-cong2 ._ f eq ⊗L⊗R₂ | 1/\2 (disj ∙ q₁ q₂ refl refl () refl)
cut⇒R-cong2 ._ f eq ⊗L⊗R₂ | 1/\2 (disj (q ◂ U) q₁ q₂ refl refl () refl) 
cut⇒R-cong2 {A = A'} {B'} p f refl (⊗L⊗R₂ {A = A} {B}) | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η (A' ⇒ B')) q₁ q₂ = ⊗L⊗R₂
cut⇒R-cong2 ._ f refl ⊗L⊗R₂ | 2/\1 (disj ∙ q₁ q₂ refl refl refl refl) = ⊗L⊗R₂
cut⇒R-cong2 ._ f eq ⊗L⊗R₂ | 2/\1 (disj (q ◂ U) q₁ q₂ refl refl refl ()) 
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⊗L⊗R₂ {A = A} {B}) | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η (A' ⇒ B')) q₁ q₂ = ⊗L⊗R₂
cut⇒R-cong2 p f eq (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) with subeq _ _ p₁ p eq
cut⇒R-cong2 {A = A''} {B''} p f eq (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q eqT eqU eqp) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (sub q₂ (η (A ⊗ B)) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (η (A ⊗ B)) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (η (A ⊗ B)) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (sub q₂ (η A ⊛ η B) ▸ q₃)) p₃ = ⊗L⊗L {p = p₁} {q₁ ++ (q₂ ◂ _)} {p₃}       
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η (A ⊗ B)))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (η (A ⊗ B)) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (η (A ⊗ B)) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η A ⊛ η B))) p₃ = ⊗L⊗L {p = p₁} {q₁ ++ (_ ▸ q₃)} {p₃}
cut⇒R-cong2 {A = A''} {B''} p f eq (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q eqT eqU eqp) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 p₁ (η (A ⊗ B)) (η (A'' ⇒ B'')) p₂ (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η A ⊛ η B) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (sub p₂ (η (A ⊗ B)) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (A ⊗ B)) (η (A'' ⇒ B'')) p₂ (q₁ ++ (sub q₂ (η A' ⊛ η  B') ▸ q₃)) = ⊗L⊗L {p = p₁} {p₂} {q₁ ++ (q₂ ◂ _)}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 p₁ (η (A ⊗ B)) (η (A'' ⇒ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η A ⊛ η B) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (sub p₂ (η (A ⊗ B)) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (A ⊗ B)) (η (A'' ⇒ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η  B'))) = ⊗L⊗L {p = p₁} {p₂} {q₁ ++ (_ ▸ q₃)}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η (A'' ⇒ B'')) (q₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (sub p₂ (η A ⊛ η B) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (sub p₂ (η (A ⊗ B)) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (A ⊗ B)) (η (A'' ⇒ B'')) (q₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) q₂ = (⊗L⊗L {p = q ++ (q₁ ◂ _)})        
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η (A'' ⇒ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₁ (q₂ ++ (sub p₂ (η A ⊛ η B) ▸ p₃)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₁ (q₂ ++ (sub p₂ (η (A ⊗ B)) ▸ p₃)) |
          subeq-2/\1 q (η (A ⊗ B)) (η (A'' ⇒ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) = (⊗L⊗L {p = q ++ (_ ▸ q₂)})
cut⇒R-cong2 p f eq (⊗L⇒L₁ {p' = p'}) with subeq _ _ p' p eq
cut⇒R-cong2 {A = A''} {B''} ._ f eq (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = p} {p'}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p q (⊛eq eqU .proj₁)
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = ._} {p'}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 (p' ++ (q₁ ◂ η (A ⇒ B))) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2>L1 p' (η (A ⇒ B)) (η (A'' ⇒ B'')) (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) = ⊗L⇒L₁
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = ._} {p'}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 (p' ++ (q₁ ◂ η (A ⇒ B))) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2>L1 p' (η (A ⇒ B)) (η (A'' ⇒ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) = ⊗L⇒L₁
cut⇒R-cong2 {A = A'} {B'} ._ f refl (⊗L⇒L₁ {A' = A} {B} {p = p} {p'}) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-1/\2 p' (η (A ⊗ B)) (η (A' ⇒ B'))  p ∙ |
          subeq-2>R1 p' (sub p (η A ⊛ η B)) (η (A' ⇒ B')) ∙ = refl
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = p}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (p ◂ η (A ⇒ B))) q₂ |
          subeq-1/\2 q (sub p (η A' ⊛ η B') ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ q₂ = ⊗L⇒L₁
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = p}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₁ (q₂ ++ (p ◂ η (A ⇒ B))) |
          subeq-2/\1 q (sub p (η A' ⊛ η B') ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ q₂ = ⊗L⇒L₁        
cut⇒R-cong2 p f eq (⊗L⇒L₂1/\2 {p = p₁}) with subeq _ _ p₁ p eq
cut⇒R-cong2 p f eq (⊗L⇒L₂1/\2 {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η B))) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (U ⊛ η (A ⇒ B)))) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) p₃ = ⊗L⇒L₂1/\2 {p = p₁}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η B))) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (U ⊛ η (A ⇒ B)))) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) p₃ = ⊗L⇒L₂1/\2 {p = p₁}         
cut⇒R-cong2 ._ f eq (⊗L⇒L₂1/\2 {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂) 
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂1/\2 {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) (η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) p₂ (p₃ ++ (q₁ ◂ η (A ⇒ B))) |
          subeq-2>L1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) (η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ = ⊗L⇒L₂1/\2 {p = p₁}
cut⇒R-cong2 ._ f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f'}) | 2>R1 (gt ._ refl refl refl) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) U (η (A ⇒ B)) ∙ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A ⇒ B)) p₂ (p₃ ++ (U ▸ ∙)) |
          subeq-2>R1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) U (η (A ⇒ B)) ∙ = ~ cut⊗L≗2/\1 p₁ p₂ p₃ (cut (∙ ◂ _) f' f) _
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q₁)) (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) p₂ (q₁ ++ (sub q₂ (η B) ▸ q₃)) |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) p₂ (q₁ ++ (sub q₂ (U ⊛ η (A ⇒ B)) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q₁)) (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₂ q₃ = ⊗L⇒L₂1/\2 {p = p₁}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q₁)) (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η B))) |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (U ⊛ η (A ⇒ B)))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q₁)) (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₂ q₃ = ⊗L⇒L₂1/\2 {p = p₁}          
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) (q₁ ++ (sub p₁ (η (A' ⊗ B')) ▸ p₂)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (p₁ ◂ sub p₂ (η B))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (p₁ ◂ sub p₂ (U ⊛ η (A ⇒ B)))) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) (q₁ ++ (sub p₁ (η A' ⊛ η B') ▸ p₂)) q₂ = (⊗L⇒L₂1/\2 {p = q ++ (q₁ ◂ _)})
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 2/\1 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ (q₂ ++ (sub p₁ (η (A' ⊗ B')) ▸ p₂)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η B))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (U ⊛ η (A ⇒ B)))) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ (q₂ ++ (sub p₁ (η A' ⊛ η B') ▸ p₂)) = (⊗L⇒L₂1/\2 {p = q ++ (_ ▸ q₂)})         
cut⇒R-cong2 p f eq (⊗L⇒L₂2/\1 {p = p₁}) with subeq _ _ p₁ p eq
cut⇒R-cong2 p f eq (⊗L⇒L₂2/\1 {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂2/\1 {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) (η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) (p₂ ++ (q₁ ◂ η (A ⇒ B))) p₃ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) (η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ = ⊗L⇒L₂2/\1 {p = p₁}
cut⇒R-cong2 ._ f refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f'}) | 2>L1 (gt ._ refl refl refl) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) U (η (A ⇒ B)) ∙ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A ⇒ B)) (p₂ ++ (U ▸ ∙)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) U (η (A ⇒ B)) ∙ = ~ cut⊗L≗1/\2 p₁ p₂ p₃ (cut (∙ ◂ _) f' f) _
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (sub q₂ (η B) ▸ q₃)) p₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (sub q₂ (U ⊛ η (A ⇒ B)) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₂ q₃ = ⊗L⇒L₂2/\1 {p = p₁} 
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η B))) p₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (q₂ ◂ sub q₃ (U ⊛ η (A ⇒ B)))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₂ q₃ = ⊗L⇒L₂2/\1 {p = p₁}         
cut⇒R-cong2 ._ f eq (⊗L⇒L₂2/\1 {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂) 
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) p₂ (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) p₂ (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) = ⊗L⇒L₂2/\1 {p = p₁}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) = ⊗L⇒L₂2/\1 {p = p₁}         
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) (q₁ ++ (p₁ ◂ sub p₂ (η (A' ⊗ B')))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (sub p₁ (η B) ▸ p₂)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (sub p₁ (U ⊛ η (A ⇒ B)) ▸ p₂)) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) (q₁ ++ (p₁ ◂ sub p₂ (η A' ⊛ η B'))) q₂ = ⊗L⇒L₂2/\1 {p = q ++ (q₁ ◂ _)} 
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 2/\1 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η (A' ⊗ B')))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₁ (q₂ ++ (sub p₁ (η B) ▸ p₂)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₁ (q₂ ++ (sub p₁ (U ⊛ η (A ⇒ B)) ▸ p₂)) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η A' ⊛ η B'))) = ⊗L⇒L₂2/\1 {p = q ++ (_ ▸ q₂)} 
cut⇒R-cong2 p f eq (⊗L⇐L₁ {p' = p'}) with subeq _ _ p' p eq
cut⇒R-cong2 ._ f eq ⊗L⇐L₁ | 2>L1 (gt ∙ refl () refl)
cut⇒R-cong2 {A = A'} {B'} ._ f eq (⊗L⇐L₁ {A' = A} {B} {p = p}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p q (⊛eq eqU .proj₂)
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = ._} {p'}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 (p' ++ (η (B ⇐ A) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2>R1 p' (η (B ⇐ A)) (η (A'' ⇒ B'')) (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) = ⊗L⇐L₁
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = ._} {p'}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 (p' ++ (η (B ⇐ A) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2>R1 p' (η (B ⇐ A)) (η (A'' ⇒ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) = ⊗L⇐L₁
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = p}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (η (B ⇐ A) ▸ p)) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ sub p (η A' ⊛ η B')) (η (A'' ⇒ B'')) q₁ q₂ = ⊗L⇐L₁
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = p}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₁ (q₂ ++ (η (B ⇐ A) ▸ p)) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ sub p (η A' ⊛ η B')) (η (A'' ⇒ B'')) q₁ q₂ = ⊗L⇐L₁
cut⇒R-cong2 p f eq (⊗L⇐L₂1/\2 {p = p₁}) with subeq _ _ p₁ p eq
cut⇒R-cong2 p f eq (⊗L⇐L₂1/\2 {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η B))) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (B ⇐ A) ⊛ U))) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) p₃ = ⊗L⇐L₂1/\2 {p = p₁}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η B))) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (B ⇐ A) ⊛ U))) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) p₃ = ⊗L⇐L₂1/\2 {p = p₁}         
cut⇒R-cong2 ._ f eq (⊗L⇐L₂1/\2 {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂) 
cut⇒R-cong2 ._ f eq (⊗L⇐L₂1/\2) | 2>R1 (gt ._ refl eqU refl) | 2>L1 (gt ∙ refl () refl) 
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt ._ refl refl refl) | 2>R1 (gt q refl refl refl)
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) (η (B ⇐ A)) (η (A'' ⇒ B'')) q |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) p₂ (p₃ ++ (η (B ⇐ A) ▸ q)) |
          subeq-2>R1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) (η (B ⇐ A)) (η (A'' ⇒ B'')) q = ⊗L⇐L₂1/\2 {p = p₁}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q₁)) (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) p₂ (q₁ ++ (sub q₂ (η B) ▸ q₃)) |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) p₂ (q₁ ++ (sub q₂ (η (B ⇐ A) ⊛ U) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q₁)) (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₂ q₃ = ⊗L⇐L₂1/\2 {p = p₁}

cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q₁)) (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η B))) |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (B ⇐ A) ⊛ U))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q₁)) (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₂ q₃ = ⊗L⇐L₂1/\2 {p = p₁}
          
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) (q₁ ++ (sub p₁ (η (A' ⊗ B')) ▸ p₂)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (p₁ ◂ sub p₂ (η B))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (p₁ ◂ sub p₂ (η (B ⇐ A) ⊛ U))) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) (q₁ ++ (sub p₁ (η A' ⊛ η B') ▸ p₂)) q₂ = (⊗L⇐L₂1/\2 {p = q ++ (q₁ ◂ _)})

cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 2/\1 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₁ (q₂ ++ (sub p₁ (η (A' ⊗ B')) ▸ p₂)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η B))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η (B ⇐ A) ⊛ U))) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₁ (q₂ ++ (sub p₁ (η A' ⊛ η B') ▸ p₂)) = (⊗L⇐L₂1/\2 {p = q ++ (_ ▸ q₂)})
          

cut⇒R-cong2 p f eq (⊗L⇐L₂2/\1 {p = p₁}) with subeq _ _ p₁ p eq
cut⇒R-cong2 p f eq (⊗L⇐L₂2/\1 {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⇒R-cong2 ._ f eq (⊗L⇐L₂2/\1) | 2>L1 (gt ._ refl eqU refl) | 2>L1 (gt ∙ refl () refl) 
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f'}) | 2>L1 (gt ._ refl refl refl) | 2>R1 (gt q refl refl refl)
  rewrite subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) (η (B ⇐ A)) (η (A'' ⇒ B'')) q |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) (p₂ ++ (η (B ⇐ A) ▸ q)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) (η (B ⇐ A)) (η (A'' ⇒ B'')) q = ⊗L⇐L₂2/\1 {p = p₁}


cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (sub q₂ (η B) ▸ q₃)) p₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (sub q₂ (η (B ⇐ A) ⊛ U) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₂ q₃ = ⊗L⇐L₂2/\1 {p = p₁} 
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η B))) p₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η (B ⇐ A) ⊛ U))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₂ q₃ = ⊗L⇐L₂2/\1 {p = p₁}
          
cut⇒R-cong2 ._ f eq (⊗L⇐L₂2/\1 {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂) 
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) p₂ (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) p₂ (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) = ⊗L⇐L₂2/\1 {p = p₁}

cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) = ⊗L⇐L₂2/\1 {p = p₁}
          
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) (q₁ ++ (p₁ ◂ sub p₂ (η (A' ⊗ B')))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (sub p₁ (η B) ▸ p₂)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) (q₁ ++ (sub p₁ (η (B ⇐ A) ⊛ U) ▸ p₂)) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) (q₁ ++ (p₁ ◂ sub p₂ (η A' ⊛ η B'))) q₂ = ⊗L⇐L₂2/\1 {p = q ++ (q₁ ◂ _)} 

cut⇒R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 2/\1 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η (A' ⊗ B')))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₁ (q₂ ++ (sub p₁ (η B) ▸ p₂)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⇒ B'')) q₁ (q₂ ++ (sub p₁ (η (B ⇐ A) ⊛ U) ▸ p₂)) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η A' ⊛ η B'))) = ⊗L⇐L₂2/\1 {p = q ++ (_ ▸ q₂)} 

cut⇒R-cong2  p f eq (⇒L⇒L {r = r}) with subeq _ _ r p eq
cut⇒R-cong2 p f eq (⇒L⇒L {q = q} {r}) | 2>L1 (gt q₁ refl eqU refl) with subeq _ _ q q₁ (⊛eq eqU .proj₁)
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L {A = A} {B} {A'} {B'} {q = q} {r = r}) | 2>L1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 q (η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ |
          subeq-2>L1 (r ++ (q ◂ η (A ⇒ B))) (η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ = ⇒L⇒L
cut⇒R-cong2 {U = U} ._ f refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r = r} {f'}) | 2>L1 (gt ._ refl refl refl) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 (r ++ (q ◂ η (A ⇒ B))) T (η (A' ⇒ B')) ∙ |
          subeq-2>R1 q T (η (A' ⇒ B')) ∙ = cut⇒L≗ r q _ (cut (∙ ◂ U) f' f) _ 
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q (T ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 (r ++ (q ◂ η (A ⇒ B))) (T ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2>L1 r (η (A ⇒ B)) (η (A'' ⇒ B'')) (q ++ (sub q₂ (η B') ▸ q₃)) =  ⇒L⇒L
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q (T ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 (r ++ (q ◂ η (A ⇒ B))) (T ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2>L1 r (η (A ⇒ B)) (η (A'' ⇒ B'')) (q ++ (q₂ ◂ sub q₃ (η B'))) = ⇒L⇒L
cut⇒R-cong2 ._ f refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-1/\2 r (T ⊛ η (A' ⇒ B')) (η (A ⇒ B))  q ∙ |
          subeq-2>R1 r (sub q (η B')) (η (A ⇒ B)) ∙ = refl
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (T ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) (q₂ ++ (q ◂ η (A ⇒ B))) q₃ |
          subeq-1/\2 q₁ (sub q (η B') ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₂ q₃ = ⇒L⇒L
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (T ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₂ (q₃ ++ (q ◂ η (A ⇒ B))) |
          subeq-2/\1 q₁ (sub q (η B') ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₂ q₃ = ⇒L⇒L

cut⇒R-cong2 p f eq (⇒L⇒L₂ {p = p₁}) with subeq _ _ p₁ p eq
cut⇒R-cong2 p f eq (⇒L⇒L₂ {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl ) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) (p₂ ++ (q₁ ◂ η (A ⇒ B))) p₃ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) (η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ = ⇒L⇒L₂ {p = p₁}
cut⇒R-cong2 ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f'}) | 2>L1 (gt ._ refl refl refl) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A ⇒ B)) (p₂ ++ (U ▸ ∙)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) U (η (A ⇒ B)) ∙ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) U (η (A ⇒ B)) ∙ = cut⇒L≗1/\2 p₁ p₂ p₃ _ (cut (∙ ◂ _) f' f) _
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) (q ++ (sub q₁ (U ⊛ η (A ⇒ B)) ▸ q₂)) p₃ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (η B'))) (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) (q ++ (sub q₁ (η B) ▸ q₂)) p₃ = ⇒L⇒L₂ {p = p₁}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) (q ++ (q₁ ◂ sub q₂ (U ⊛ η (A ⇒ B)))) p₃ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (η B'))) (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) (q ++ (q₁ ◂ sub q₂ (η B))) p₃ = ⇒L⇒L₂ {p = p₁}
  
cut⇒R-cong2 p f eq (⇒L⇒L₂ {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L₂ {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) (η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) p₂ (p₃ ++ (q₁ ◂ η (A' ⇒ B'))) |
          subeq-2>L1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ = ⇒L⇒L₂ {p = p₁}
cut⇒R-cong2 ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f' = f'}) | 2>R1 (gt ._ refl refl refl) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) V (η (A' ⇒ B')) ∙ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A' ⇒ B')) p₂ (p₃ ++ (V ▸ ∙)) |
          subeq-2>R1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) V (η (A' ⇒ B')) ∙ = ~ cut⇒L≗2/\1 p₁ p₂ p₃ _ (cut (∙ ◂ _) f' f) _
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) p₂ (q ++ (sub q₁ (η B') ▸ q₂)) | 
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) p₂ (q ++ (sub q₁ (V ⊛ η (A' ⇒ B')) ▸ q₂)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ q₂ = ⇒L⇒L₂ {p = p₁}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) p₂ (q ++ (q₁ ◂ sub q₂ (η B'))) | 
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) p₂ (q ++ (q₁ ◂ sub q₂ (V ⊛ η (A' ⇒ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ q₂ = ⇒L⇒L₂ {p = p₁}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) (q₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) (q₁ ++ (p₂ ◂ sub p₃ (η B'))) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) (q₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) q₂ |
          subeq-1/\2 q (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = ⇒L⇒L₂ {p = q ++ (q₁ ◂ _)}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ (q₂ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B'))) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) |
          subeq-2/\1 q (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = ⇒L⇒L₂ {p = q ++ (_ ▸ q₂)}

cut⇒R-cong2  p f eq (⇒L⇐L {r = r}) with subeq _ _ r p eq
cut⇒R-cong2 ._ f eq (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>L1 (gt ∙ refl () refl) 
cut⇒R-cong2 p f eq (⇒L⇐L {q = q} {r}) | 2>R1 (gt q₁ refl eqU refl) with subeq _ _ q q₁ (⊛eq eqU .proj₂)
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L {A = A} {B} {A'} {B'} {q = q} {r = r}) | 2>R1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 q (η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ |
          subeq-2>L1 (r ++ (η (B ⇐ A) ▸ q)) (η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ = ⇒L⇐L
cut⇒R-cong2 {U = U} ._ f refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r = r} {f'}) | 2>R1 (gt ._ refl refl refl) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 (r ++ (η (B ⇐ A) ▸ q)) T (η (A' ⇒ B')) ∙ |
          subeq-2>R1 q T (η (A' ⇒ B')) ∙ = cut⇐L≗ r q _ (cut (∙ ◂ U) f' f) _
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q (T ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 (r ++ (η (B ⇐ A) ▸ q)) (T ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2>R1 r (η (B ⇐ A)) (η (A'' ⇒ B'')) (q ++ (sub q₂ (η B') ▸ q₃)) = ⇒L⇐L
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q (T ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 (r ++ (η (B ⇐ A) ▸ q)) (T ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2>R1 r (η (B ⇐ A)) (η (A'' ⇒ B'')) (q ++ (q₂ ◂ sub q₃ (η B'))) = ⇒L⇐L

cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (T ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) (q₂ ++ (η (B ⇐ A) ▸ q)) q₃ |
          subeq-1/\2 q₁ (η (B ⇐ A) ⊛ sub q (η B')) (η (A'' ⇒ B'')) q₂ q₃ =  ⇒L⇐L 
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (T ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₂ (q₃ ++ (η (B ⇐ A) ▸ q)) |
          subeq-2/\1 q₁ (η (B ⇐ A) ⊛ sub q (η B')) (η (A'' ⇒ B'')) q₂ q₃ = ⇒L⇐L 

cut⇒R-cong2 p f eq (⇒L⇐L₂ {p = p₁}) with subeq _ _ p₁ p eq
cut⇒R-cong2 p f eq (⇒L⇐L₂ {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl ) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) (p₂ ++ (q₁ ◂ η (A ⇒ B))) p₃ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) (η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ = ⇒L⇐L₂ {p = p₁}
cut⇒R-cong2 ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f'}) | 2>L1 (gt ._ refl refl refl) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A ⇒ B)) (p₂ ++ (U ▸ ∙)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) U (η (A ⇒ B)) ∙ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) U (η (A ⇒ B)) ∙ = cut⇐L≗1/\2 p₁ p₂ p₃ _ (cut (∙ ◂ _) f' f) _
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) (q ++ (sub q₁ (U ⊛ η (A ⇒ B)) ▸ q₂)) p₃ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (η B'))) (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) (q ++ (sub q₁ (η B) ▸ q₂)) p₃ = ⇒L⇐L₂ {p = p₁}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) (q ++ (q₁ ◂ sub q₂ (U ⊛ η (A ⇒ B)))) p₃ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (η B'))) (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) (q ++ (q₁ ◂ sub q₂ (η B))) p₃ = ⇒L⇐L₂ {p = p₁}
  
cut⇒R-cong2 p f eq (⇒L⇐L₂ {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut⇒R-cong2 ._ f eq (⇒L⇐L₂) | 2>R1 (gt ._ refl eqU refl) | 2>L1 (gt ∙ refl () refl)
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f' = f'}) | 2>R1 (gt ._ refl refl refl) | 2>R1 (gt q refl refl refl)
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) (η (B' ⇐ A')) (η (A'' ⇒ B'')) q |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) p₂ (p₃ ++ (η (B' ⇐ A') ▸ q)) |
          subeq-2>R1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (B' ⇐ A')) (η (A'' ⇒ B'')) q = ⇒L⇐L₂ {p = p₁} 
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) p₂ (q ++ (sub q₁ (η B') ▸ q₂)) | 
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) p₂ (q ++ (sub q₁ (η (B' ⇐ A') ⊛ V) ▸ q₂)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) q₁ q₂ = ⇒L⇐L₂ {p = p₁}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) p₂ (q ++ (q₁ ◂ sub q₂ (η B'))) | 
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) p₂ (q ++ (q₁ ◂ sub q₂ (η (B' ⇐ A') ⊛ V))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) q₁ q₂ = ⇒L⇐L₂ {p = p₁}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) (q₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) (q₁ ++ (p₂ ◂ sub p₃ (η B'))) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) (q₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) q₂ |
          subeq-1/\2 q (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = ⇒L⇐L₂ {p = q ++ (q₁ ◂ _)}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) q₁ (q₂ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B'))) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) |
          subeq-2/\1 q (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = ⇒L⇐L₂ {p = q ++ (_ ▸ q₂)}

cut⇒R-cong2  p f eq (⇐L⇒L {r = r}) with subeq _ _ r p eq
cut⇒R-cong2 p f eq (⇐L⇒L {q = q} {r}) | 2>L1 (gt q₁ refl eqU refl) with subeq _ _ q q₁ (⊛eq eqU .proj₁)
cut⇒R-cong2 ._ f eq (⇐L⇒L) | 2>L1 (gt ._ refl eqU refl) | 2>L1 (gt ∙ refl () refl)
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r = r} {f'}) | 2>L1 (gt ._ refl refl refl) | 2>R1 (gt q₁ refl refl refl) 
  rewrite subeq-2>R1 q (η (B' ⇐ A')) (η (A'' ⇒ B'')) q₁ |
          subeq-2>R1 (r ++ (q ◂ η (A ⇒ B))) (η (B' ⇐ A')) (η (A'' ⇒ B'')) q₁ = ⇐L⇒L
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B' ⇐ A') ⊛ T) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 (r ++ (q ◂ η (A ⇒ B))) (η (B' ⇐ A') ⊛ T) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2>L1 r (η (A ⇒ B)) (η (A'' ⇒ B'')) (q ++ (sub q₂ (η B') ▸ q₃)) =  ⇐L⇒L
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B' ⇐ A') ⊛ T) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 (r ++ (q ◂ η (A ⇒ B))) (η (B' ⇐ A') ⊛ T) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2>L1 r (η (A ⇒ B)) (η (A'' ⇒ B'')) (q ++ (q₂ ◂ sub q₃ (η B'))) = ⇐L⇒L
cut⇒R-cong2 ._ f refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-1/\2 r (η (B' ⇐ A') ⊛ T) (η (A ⇒ B))  q ∙ |
          subeq-2>R1 r (sub q (η B')) (η (A ⇒ B)) ∙ = refl
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (B' ⇐ A') ⊛ T) (η (A'' ⇒ B'')) (q₂ ++ (q ◂ η (A ⇒ B))) q₃ |
          subeq-1/\2 q₁ (sub q (η B') ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₂ q₃ = ⇐L⇒L
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (B' ⇐ A') ⊛ T) (η (A'' ⇒ B'')) q₂ (q₃ ++ (q ◂ η (A ⇒ B))) |
          subeq-2/\1 q₁ (sub q (η B') ⊛ η (A ⇒ B)) (η (A'' ⇒ B'')) q₂ q₃ = ⇐L⇒L

cut⇒R-cong2 p f eq (⇐L⇒L₂ {p = p₁}) with subeq _ _ p₁ p eq
cut⇒R-cong2 p f eq (⇐L⇒L₂ {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl ) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⇒R-cong2 ._ f eq (⇐L⇒L₂) | 2>L1 (gt ._ refl eqU refl) | 2>L1 (gt ∙ refl () refl)

cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f'}) | 2>L1 (gt ._ refl refl refl) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) (p₂ ++ (η (B ⇐ A) ▸ q)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (η (B ⇐ A)) (η (A'' ⇒ B'')) q |
          subeq-2/\1 p₁ (η B') (η (A'' ⇒ B'')) (p₂ ++ (η (B ⇐ A) ▸ q)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) (η (B ⇐ A)) (η (A'' ⇒ B'')) q = ⇐L⇒L₂ {p = p₁}

cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) (q ++ (sub q₁ (η (B ⇐ A) ⊛ U) ▸ q₂)) p₃ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (η B'))) (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) (q ++ (sub q₁ (η B) ▸ q₂)) p₃ = ⇐L⇒L₂ {p = p₁}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) (q ++ (q₁ ◂ sub q₂ (η (B ⇐ A) ⊛ U))) p₃ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (η B'))) (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) (q ++ (q₁ ◂ sub q₂ (η B))) p₃ = ⇐L⇒L₂ {p = p₁}
  
cut⇒R-cong2 p f eq (⇐L⇒L₂ {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L₂ {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) (η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) p₂ (p₃ ++ (q₁ ◂ η (A' ⇒ B'))) |
          subeq-2>L1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ = ⇐L⇒L₂ {p = p₁}
cut⇒R-cong2 ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f' = f'}) | 2>R1 (gt ._ refl refl refl) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) V (η (A' ⇒ B')) ∙ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A' ⇒ B')) p₂ (p₃ ++ (V ▸ ∙)) |
          subeq-2>R1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) V (η (A' ⇒ B')) ∙ = ~ cut⇐L≗2/\1 p₁ p₂ p₃ _ (cut (∙ ◂ _) f' f) _ 
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) p₂ (q ++ (sub q₁ (η B') ▸ q₂)) | 
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) p₂ (q ++ (sub q₁ (V ⊛ η (A' ⇒ B')) ▸ q₂)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ q₂ = ⇐L⇒L₂ {p = p₁}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) p₂ (q ++ (q₁ ◂ sub q₂ (η B'))) | 
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) p₂ (q ++ (q₁ ◂ sub q₂ (V ⊛ η (A' ⇒ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ q₂ = ⇐L⇒L₂ {p = p₁}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) (q₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) (q₁ ++ (p₂ ◂ sub p₃ (η B'))) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) (q₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) q₂ |
          subeq-1/\2 q (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = ⇐L⇒L₂ {p = q ++ (q₁ ◂ _)}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ (q₂ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B'))) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) |
          subeq-2/\1 q (V ⊛ η (A' ⇒ B')) (η (A'' ⇒ B'')) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = ⇐L⇒L₂ {p = q ++ (_ ▸ q₂)}
cut⇒R-cong2  p f eq (⇐L⇐L {r = r}) with subeq _ _ r p eq
cut⇒R-cong2 ._ f eq ⇐L⇐L | 2>L1 (gt ∙ refl () refl) 
cut⇒R-cong2 p f eq (⇐L⇐L {q = q} {r}) | 2>R1 (gt q₁ refl eqU refl) with subeq _ _ q q₁ (⊛eq eqU .proj₂)
cut⇒R-cong2 ._ f eq (⇐L⇐L) | 2>R1 (gt ._ refl eqU refl) | 2>L1 (gt ∙ refl () refl)
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r = r} {f'}) | 2>R1 (gt ._ refl refl refl) | 2>R1 (gt q₁ refl refl refl) 
  rewrite subeq-2>R1 q (η (B' ⇐ A')) (η (A'' ⇒ B'')) q₁ |
          subeq-2>R1 (r ++ (η (B ⇐ A) ▸ q)) (η (B' ⇐ A')) (η (A'' ⇒ B'')) q₁ = ⇐L⇐L
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B' ⇐ A') ⊛ T) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-1/\2 (r ++ (η (B ⇐ A) ▸ q)) (η (B' ⇐ A') ⊛ T) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2>R1 r (η (B ⇐ A)) (η (A'' ⇒ B'')) (q ++ (sub q₂ (η B') ▸ q₃)) =   ⇐L⇐L
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B' ⇐ A') ⊛ T) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2/\1 (r ++ (η (B ⇐ A) ▸ q)) (η (B' ⇐ A') ⊛ T) (η (A'' ⇒ B'')) q₂ q₃ |
          subeq-2>R1 r (η (B ⇐ A)) (η (A'' ⇒ B'')) (q ++ (q₂ ◂ sub q₃ (η B'))) =  ⇐L⇐L
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (B' ⇐ A') ⊛ T) (η (A'' ⇒ B'')) (q₂ ++ (η (B ⇐ A) ▸ q)) q₃ |
          subeq-1/\2 q₁ (η (B ⇐ A) ⊛ sub q (η B')) (η (A'' ⇒ B'')) q₂ q₃ = ⇐L⇐L
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (B' ⇐ A') ⊛ T) (η (A'' ⇒ B'')) q₂ (q₃ ++ (η (B ⇐ A) ▸ q)) |
          subeq-2/\1 q₁ (η (B ⇐ A) ⊛ sub q (η B')) (η (A'' ⇒ B'')) q₂ q₃ = ⇐L⇐L

cut⇒R-cong2 p f eq (⇐L⇐L₂ {p = p₁}) with subeq _ _ p₁ p eq
cut⇒R-cong2 p f eq (⇐L⇐L₂ {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl ) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⇒R-cong2 ._ f eq (⇐L⇐L₂) | 2>L1 (gt ._ refl eqU refl) | 2>L1 (gt ∙ refl () refl)

cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f'}) | 2>L1 (gt ._ refl refl refl) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) (p₂ ++ (η (B ⇐ A) ▸ q)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (η (B ⇐ A)) (η (A'' ⇒ B'')) q |
          subeq-2/\1 p₁ (η B') (η (A'' ⇒ B'')) (p₂ ++ (η (B ⇐ A) ▸ q)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) (η (B ⇐ A)) (η (A'' ⇒ B'')) q = ⇐L⇐L₂ {p = p₁}

cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) (q ++ (sub q₁ (η (B ⇐ A) ⊛ U) ▸ q₂)) p₃ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (η B'))) (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) (q ++ (sub q₁ (η B) ▸ q₂)) p₃ = ⇐L⇐L₂ {p = p₁}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) (q ++ (q₁ ◂ sub q₂ (η (B ⇐ A) ⊛ U))) p₃ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (η B'))) (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) (q ++ (q₁ ◂ sub q₂ (η B))) p₃ = ⇐L⇐L₂ {p = p₁}
  
cut⇒R-cong2 p f eq (⇐L⇐L₂ {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut⇒R-cong2 ._ f eq (⇐L⇐L₂) | 2>R1 (gt ._ refl eqU refl) | 2>L1 (gt ∙ refl () refl) 
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f' = f'}) | 2>R1 (gt ._ refl refl refl) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) (η (B' ⇐ A')) (η (A'' ⇒ B'')) q |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) p₂ (p₃ ++ (η (B' ⇐ A') ▸ q)) |
          subeq-1/\2 p₁ (η B) (η (A'' ⇒ B'')) p₂ (p₃ ++ (η (B' ⇐ A') ▸ q)) |
          subeq-2>R1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (B' ⇐ A')) (η (A'' ⇒ B'')) q = ⇐L⇐L₂ {p = p₁}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) p₂ (q ++ (sub q₁ (η B') ▸ q₂)) | 
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) p₂ (q ++ (sub q₁ (η (B' ⇐ A') ⊛ V) ▸ q₂)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) q₁ q₂ = ⇐L⇐L₂ {p = p₁}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) q₁ q₂ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) p₂ (q ++ (q₁ ◂ sub q₂ (η B'))) | 
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) p₂ (q ++ (q₁ ◂ sub q₂ (η (B' ⇐ A') ⊛ V))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) q₁ q₂ = ⇐L⇐L₂ {p = p₁}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) (q₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) (q₁ ++ (p₂ ◂ sub p₃ (η B'))) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) (q₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) q₂ |
          subeq-1/\2 q (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = ⇐L⇐L₂ {p = q ++ (q₁ ◂ _)}
cut⇒R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) q₁ (q₂ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B'))) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (A'' ⇒ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) |
          subeq-2/\1 q (η (B' ⇐ A') ⊛ V) (η (A'' ⇒ B'')) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = ⇐L⇐L₂ {p = q ++ (_ ▸ q₂)}

cut⇐R-cong2 p f eq refl = refl
cut⇐R-cong2 p f eq (~ eq') = ~ (cut⇐R-cong2 p f eq eq')
cut⇐R-cong2 p f eq (eq' ∘ eq'') = cut⇐R-cong2 p f eq eq' ∘ cut⇐R-cong2 p f eq eq''
cut⇐R-cong2 p f refl (⇒R eq') = ⇒R (cut⇐R-cong2 (_ ▸ p) f refl eq')
cut⇐R-cong2 p f refl (⇐R eq') = ⇐R (cut⇐R-cong2 (p ◂ _) f refl eq')
cut⇐R-cong2 p f eq (⇒L {p = p₁} eq' eq'') with subeq _ _ p₁ p eq
cut⇐R-cong2 ._ f refl (⇒L {p = _} eq' eq'') | 2>L1 (gt q refl refl refl) = ⇒L (cut⇐R-cong2 q f refl eq') eq''
cut⇐R-cong2 ._ f eq (⇒L eq' eq'') | 2>R1 (gt ∙ refl () refl) 
cut⇐R-cong2 ._ f refl (⇒L {B = B} eq' eq'') | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⇒L eq' (cut⇐R-cong2 (q ++ (sub q₁ (η B) ▸ q₂)) f refl eq'')
cut⇐R-cong2 ._ f refl (⇒L {B = B} eq' eq'') | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⇒L eq' (cut⇐R-cong2 (q ++ (q₁ ◂ sub q₂ (η B))) f refl eq'')
cut⇐R-cong2 p f eq (⇐L {p = p₁} eq' eq'') with subeq _ _ p₁ p eq
cut⇐R-cong2 {U = U} ._ f refl (⇐L {p = p₁} {f' = f'} eq' eq'') | 2>L1 (gt ∙ refl refl refl) = 
  cut-cong1 p₁ _ refl (cut-cong1 (U ▸ ∙) f refl eq') ∘ cut-cong2 p₁ (cut (U ▸ ∙) f' f) eq''
cut⇐R-cong2 ._ f refl (⇐L eq' eq'') | 2>R1 (gt q refl refl refl) = ⇐L (cut⇐R-cong2 q f refl eq') eq''
cut⇐R-cong2 ._ f refl (⇐L {B = B} eq' eq'') | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⇐L eq' (cut⇐R-cong2 (q ++ (sub q₁ (η B) ▸ q₂)) f refl eq'')
cut⇐R-cong2 ._ f refl (⇐L {B = B} eq' eq'') | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⇐L eq' (cut⇐R-cong2 (q ++ (q₁ ◂ sub q₂ (η B))) f refl eq'')
cut⇐R-cong2 (p ◂ U) f refl (⊗R eq' eq'') = ⊗R (cut⇐R-cong2 p f refl eq') eq''
cut⇐R-cong2 (T ▸ p) f refl (⊗R eq' eq'') = ⊗R eq' (cut⇐R-cong2 p f refl eq'')
cut⇐R-cong2 p f eq (⊗L {p = p₁} eq') with subeq _ _ p₁ p eq
cut⇐R-cong2 ._ f refl (⊗L {A = A} {B} eq') | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⊗L (cut⇐R-cong2 (q ++ (sub q₁ (η A ⊛ η B) ▸ q₂)) f refl eq')
cut⇐R-cong2 ._ f refl (⊗L {A = A} {B} eq') | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⊗L (cut⇐R-cong2 (q ++ (q₁ ◂ sub q₂ (η A ⊛ η B))) f refl eq')

cut⇐R-cong2 p f eq (⇒L⇒R {p = p₁}) with subeq _ _ p₁ p eq
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇒L⇒R {A = A} {B} {p = p₁}) | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η (B' ⇐ A')) q = ⇒L⇒R
cut⇐R-cong2 ._ f eq ⇒L⇒R | 2>R1 (gt ∙ refl () refl) 
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇒L⇒R {U = U₁} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U₁ ⊛ η (A ⇒ B)) (η (B' ⇐ A')) q₁ q₂ = ⇒L⇒R
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇒L⇒R {U = U₁} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U₁ ⊛ η (A ⇒ B)) (η (B' ⇐ A')) q₁ q₂ = ⇒L⇒R
cut⇐R-cong2 p f eq (⇐L⇒R {p = p₁}) with subeq _ _ p₁ p eq
cut⇐R-cong2 {A = A} {B} ._ f refl (⇐L⇒R {U = U₁} {p = p₁} {f'}) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 p₁ U₁ (η (B ⇐ A)) ∙ = cut⇒R≗ p₁ (cut (_ ▸ ∙) f' f) _
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇐L⇒R {A = A} {B} {p = p₁}) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η (B' ⇐ A')) q = ⇐L⇒R

cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇐L⇒R {U = U₁} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U₁) (η (B' ⇐ A')) q₁ q₂ = ⇐L⇒R
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇐L⇒R {U = U₁} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U₁) (η (B' ⇐ A')) q₁ q₂ = ⇐L⇒R

cut⇐R-cong2 p f eq (⊗L⇒R {p = p₁}) with subeq _ _ p₁ p eq
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⊗L⇒R {A = A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η (B' ⇐ A')) q₁ q₂ = ⊗L⇒R
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⊗L⇒R {A = A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η (B' ⇐ A')) q₁ q₂ = ⊗L⇒R
cut⇐R-cong2 p f eq (⇒L⇐R {p = p₁}) with subeq _ _ p₁ p eq
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇒L⇐R {U = U₁} {A} {B} {p = p₁}) | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η (B' ⇐ A')) q = ⇒L⇐R
cut⇐R-cong2 ._ f eq (⇒L⇐R {U = U₁} {A} {B} {p = p₁} {f'}) | 2>R1 (gt ∙ refl () refl) 
  -- rewrite subeq-2>R1 p₁ U₁ (η (A ⇒ B)) ∙ = cut⇐R≗ p₁ (cut (∙ ◂ _) f' f) _
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇒L⇐R {U = U₁} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U₁ ⊛ η (A ⇒ B)) (η (B' ⇐ A')) q₁ q₂ = ⇒L⇐R
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇒L⇐R {U = U₁} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U₁ ⊛ η (A ⇒ B)) (η (B' ⇐ A')) q₁ q₂ = ⇒L⇐R

cut⇐R-cong2 p f eq (⇐L⇐R {p = p₁}) with subeq _ _ p₁ p eq
cut⇐R-cong2 ._ f refl (⇐L⇐R {U = U₁} {A = A} {B} {p = p₁} {f'}) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 p₁ U₁ (η (B ⇐ A)) ∙ = cut⇐R≗ p₁ (cut (_ ▸ ∙) f' f) _
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇐L⇐R {A = A} {B} {p = p₁}) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η (B' ⇐ A')) q = ⇐L⇐R
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇐L⇐R {U = U₁} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U₁) (η (B' ⇐ A')) q₁ q₂ = ⇐L⇐R
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇐L⇐R {U = U₁} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U₁) (η (B' ⇐ A')) q₁ q₂ = ⇐L⇐R

cut⇐R-cong2 p f eq (⊗L⇐R {p = p₁}) with subeq _ _ p₁ p eq
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⊗L⇐R {A = A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η (B' ⇐ A')) q₁ q₂ = ⊗L⇐R
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⊗L⇐R {A = A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η (B' ⇐ A')) q₁ q₂ = ⊗L⇐R

cut⇐R-cong2 p f eq (⇒L⊗R₁ {V = V} {p = p₁}) with subeq _ _ (p₁ ◂ V) p eq
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇒L⊗R₁ {A = A} {B} {p = p₁}) | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η (B' ⇐ A')) q = ⇒L⊗R₁
cut⇐R-cong2 ._ f eq ⇒L⊗R₁ | 2>R1 (gt ∙ refl () refl) 
cut⇐R-cong2 ._ f refl (⇒L⊗R₁) | 1/\2 (disj ∙ q₁ q₂ refl refl refl refl) = ⇒L⊗R₁
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇒L⊗R₁ {U = U₁} {A = A} {B}) | 1/\2 (disj (q ◂ U) q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U₁ ⊛ η (A ⇒ B)) (η (B' ⇐ A')) q₁ q₂ = ⇒L⊗R₁
cut⇐R-cong2 p f eq (⇒L⊗R₁) | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl () refl)
cut⇐R-cong2 ._ f eq (⇒L⊗R₁) | 2/\1 (disj ∙ q₁ q₂ refl refl refl ())
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇒L⊗R₁ {U = U₁} {A = A} {B}) | 2/\1 (disj (q ◂ U) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U₁ ⊛ η (A ⇒ B)) (η (B' ⇐ A')) q₁ q₂ = ⇒L⊗R₁
cut⇐R-cong2 ._ f eq (⇒L⊗R₁) | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl ())

cut⇐R-cong2 p f eq (⇒L⊗R₂ {V = V} {p = p₁}) with subeq _ _ (V ▸ p₁) p eq
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇒L⊗R₂ {A = A} {B} {p = p₁}) | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η (B' ⇐ A')) q = ⇒L⊗R₂
cut⇐R-cong2 ._ f eq ⇒L⊗R₂ | 2>R1 (gt ∙ refl () refl) 
cut⇐R-cong2 ._ f eq ⇒L⊗R₂ | 1/\2 (disj ∙ q₁ q₂ refl refl () refl)
cut⇐R-cong2 ._ f eq ⇒L⊗R₂ | 1/\2 (disj (q ◂ U) q₁ q₂ refl refl () refl) 
cut⇐R-cong2 {A = A'} {B'} p f refl (⇒L⊗R₂ {U = U₁} {A = A} {B}) | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U₁ ⊛ η (A ⇒ B)) (η (B' ⇐ A')) q₁ q₂ = ⇒L⊗R₂
cut⇐R-cong2 ._ f refl ⇒L⊗R₂ | 2/\1 (disj ∙ q₁ q₂ refl refl refl refl) = ⇒L⊗R₂
cut⇐R-cong2 ._ f eq ⇒L⊗R₂ | 2/\1 (disj (q ◂ U) q₁ q₂ refl refl refl ()) 
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇒L⊗R₂ {U = U₁} {A = A} {B}) | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U₁ ⊛ η (A ⇒ B)) (η (B' ⇐ A')) q₁ q₂ = ⇒L⊗R₂
  
cut⇐R-cong2 p f eq (⇐L⊗R₁ {V = V} {p = p₁}) with subeq _ _ (p₁ ◂ V) p eq
cut⇐R-cong2 ._ f refl (⇐L⊗R₁ {U = U} {A = A} {B} {p = p₁} {f'}) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 p₁ U (η (B ⇐ A)) ∙ = cut⊗R≗₁ p₁ (cut (_ ▸ ∙) f' f) _ _
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇐L⊗R₁ {U = U₁} {A = A} {B} {p = p₁} {f'}) | 2>R1 (gt q refl refl refl)
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η (B' ⇐ A')) q = ⇐L⊗R₁
cut⇐R-cong2 ._ f refl (⇐L⊗R₁) | 1/\2 (disj ∙ q₁ q₂ refl refl refl refl) = ⇐L⊗R₁
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇐L⊗R₁ {U = U₁} {A = A} {B}) | 1/\2 (disj (q ◂ U) q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U₁) (η (B' ⇐ A')) q₁ q₂ = ⇐L⊗R₁
cut⇐R-cong2 p f eq (⇐L⊗R₁) | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl () refl)
cut⇐R-cong2 ._ f eq (⇐L⊗R₁) | 2/\1 (disj ∙ q₁ q₂ refl refl refl ())
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇐L⊗R₁ {U = U₁} {A = A} {B}) | 2/\1 (disj (q ◂ U) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U₁) (η (B' ⇐ A')) q₁ q₂ = ⇐L⊗R₁
cut⇐R-cong2 ._ f eq (⇐L⊗R₁) | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl ())

cut⇐R-cong2 p f eq (⇐L⊗R₂ {V = V} {p = p₁}) with subeq _ _ (V ▸ p₁) p eq
cut⇐R-cong2 ._ f refl (⇐L⊗R₂ {U = U₁} {V} {A = A} {B} {p = p₁} {f'}) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 p₁ U₁ (η (B ⇐ A)) ∙ = cut⊗R≗₂ p₁ (cut (_ ▸ ∙) f' f) _ _
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇐L⊗R₂ {A = A} {B} {p = p₁}) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η (B' ⇐ A')) q = ⇐L⊗R₂
cut⇐R-cong2 ._ f eq (⇐L⊗R₂) | 1/\2 (disj ∙ q₁ q₂ refl refl () refl)
cut⇐R-cong2 ._ f eq (⇐L⊗R₂) | 1/\2 (disj (q ◂ U) q₁ q₂ refl refl () refl) 
cut⇐R-cong2 {A = A'} {B'} p f refl (⇐L⊗R₂ {U = U₁} {A = A} {B}) | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U₁) (η (B' ⇐ A')) q₁ q₂ = ⇐L⊗R₂
cut⇐R-cong2 ._ f refl (⇐L⊗R₂) | 2/\1 (disj ∙ q₁ q₂ refl refl refl refl) = ⇐L⊗R₂
cut⇐R-cong2 ._ f eq (⇐L⊗R₂) | 2/\1 (disj (q ◂ U) q₁ q₂ refl refl refl ()) 
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⇐L⊗R₂ {U = U₁} {A = A} {B}) | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U₁) (η (B' ⇐ A')) q₁ q₂ = ⇐L⊗R₂


cut⇐R-cong2 p f eq (⊗L⊗R₁ {U = U} {p = p₁}) with subeq _ _ (p₁ ◂ U) p eq
cut⇐R-cong2 ._ f refl ⊗L⊗R₁ | 1/\2 (disj ∙ q₁ q₂ refl refl refl refl) = ⊗L⊗R₁
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⊗L⊗R₁ {A = A} {B}) | 1/\2 (disj (q ◂ U) q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η (B' ⇐ A')) q₁ q₂ = ⊗L⊗R₁
cut⇐R-cong2 p f eq ⊗L⊗R₁ | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl () eqp₂)
cut⇐R-cong2 ._ f eq ⊗L⊗R₁ | 2/\1 (disj ∙ q₁ q₂ refl refl refl ())
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⊗L⊗R₁ {A = A} {B} {p = _}) | 2/\1 (disj (q ◂ U) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η (B' ⇐ A')) q₁ q₂ = ⊗L⊗R₁
cut⇐R-cong2 ._ f eq ⊗L⊗R₁ | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl ())

cut⇐R-cong2 p f eq (⊗L⊗R₂ {U = U} {p = p₁}) with subeq _ _ (U ▸ p₁) p eq
cut⇐R-cong2 ._ f eq ⊗L⊗R₂ | 1/\2 (disj ∙ q₁ q₂ refl refl () refl)
cut⇐R-cong2 ._ f eq ⊗L⊗R₂ | 1/\2 (disj (q ◂ U) q₁ q₂ refl refl () refl) 
cut⇐R-cong2 {A = A'} {B'} p f refl (⊗L⊗R₂ {A = A} {B}) | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η (B' ⇐ A')) q₁ q₂ = ⊗L⊗R₂
cut⇐R-cong2 ._ f refl ⊗L⊗R₂ | 2/\1 (disj ∙ q₁ q₂ refl refl refl refl) = ⊗L⊗R₂
cut⇐R-cong2 ._ f eq ⊗L⊗R₂ | 2/\1 (disj (q ◂ U) q₁ q₂ refl refl refl ()) 
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⊗L⊗R₂ {A = A} {B}) | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η (B' ⇐ A')) q₁ q₂ = ⊗L⊗R₂

cut⇐R-cong2 p f eq (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) with subeq _ _ p₁ p eq
cut⇐R-cong2 {A = A''} {B''} p f eq (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q eqT eqU eqp) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (sub q₂ (η (A ⊗ B)) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (η (A ⊗ B)) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (η (A ⊗ B)) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (sub q₂ (η A ⊛ η B) ▸ q₃)) p₃ = ⊗L⊗L {p = p₁} {q₁ ++ (q₂ ◂ _)} {p₃}
          
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (q₂ ◂ sub q₃ (η (A ⊗ B)))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (η (A ⊗ B)) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (η (A ⊗ B)) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (q₂ ◂ sub q₃ (η A ⊛ η B))) p₃ = ⊗L⊗L {p = p₁} {q₁ ++ (_ ▸ q₃)} {p₃}

cut⇐R-cong2 {A = A''} {B''} p f eq (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q eqT eqU eqp) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 p₁ (η (A ⊗ B)) (η (B'' ⇐ A'')) p₂ (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η A ⊛ η B) ▸ q₁)) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (sub p₂ (η (A ⊗ B)) ▸ q₁)) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (A ⊗ B)) (η (B'' ⇐ A'')) p₂ (q₁ ++ (sub q₂ (η A' ⊛ η  B') ▸ q₃)) = ⊗L⊗L {p = p₁} {p₂} {q₁ ++ (q₂ ◂ _)}

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 p₁ (η (A ⊗ B)) (η (B'' ⇐ A'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η A ⊛ η B) ▸ q₁)) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (sub p₂ (η (A ⊗ B)) ▸ q₁)) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (A ⊗ B)) (η (B'' ⇐ A'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η  B'))) = ⊗L⊗L {p = p₁} {p₂} {q₁ ++ (_ ▸ q₃)}

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η (B'' ⇐ A'')) (q₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (sub p₂ (η A ⊛ η B) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (sub p₂ (η (A ⊗ B)) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (A ⊗ B)) (η (B'' ⇐ A'')) (q₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) q₂ = (⊗L⊗L {p = q ++ (q₁ ◂ _)})
          
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η (B'' ⇐ A'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₁ (q₂ ++ (sub p₂ (η A ⊛ η B) ▸ p₃)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₁ (q₂ ++ (sub p₂ (η (A ⊗ B)) ▸ p₃)) |
          subeq-2/\1 q (η (A ⊗ B)) (η (B'' ⇐ A'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) = (⊗L⊗L {p = q ++ (_ ▸ q₂)})

cut⇐R-cong2 p f eq (⊗L⇒L₁ {p' = p'}) with subeq _ _ p' p eq
cut⇐R-cong2 {A = A''} {B''} ._ f eq (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = p} {p'}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p q (⊛eq eqU .proj₁)
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = ._} {p'}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 (p' ++ (q₁ ◂ η (A ⇒ B))) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2>L1 p' (η (A ⇒ B)) (η (B'' ⇐ A'')) (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) = ⊗L⇒L₁
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = ._} {p'}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 (p' ++ (q₁ ◂ η (A ⇒ B))) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2>L1 p' (η (A ⇒ B)) (η (B'' ⇐ A'')) (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) = ⊗L⇒L₁

cut⇐R-cong2 ._ f eq ⊗L⇒L₁ | 2>R1 (gt ∙ refl () refl) 

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = p}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (p ◂ η (A ⇒ B))) q₂ |
          subeq-1/\2 q (sub p (η A' ⊛ η B') ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ q₂ = ⊗L⇒L₁
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = p}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₁ (q₂ ++ (p ◂ η (A ⇒ B))) |
          subeq-2/\1 q (sub p (η A' ⊛ η B') ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ q₂ = ⊗L⇒L₁
          
cut⇐R-cong2 p f eq (⊗L⇒L₂1/\2 {p = p₁}) with subeq _ _ p₁ p eq
cut⇐R-cong2 p f eq (⊗L⇒L₂1/\2 {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η B))) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (U ⊛ η (A ⇒ B)))) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) p₃ = ⊗L⇒L₂1/\2 {p = p₁}
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η B))) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (U ⊛ η (A ⇒ B)))) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) p₃ = ⊗L⇒L₂1/\2 {p = p₁}
          
cut⇐R-cong2 ._ f eq (⊗L⇒L₂1/\2 {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂) 
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂1/\2 {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) (η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) p₂ (p₃ ++ (q₁ ◂ η (A ⇒ B))) |
          subeq-2>L1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) (η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ = ⊗L⇒L₂1/\2 {p = p₁}
cut⇐R-cong2 ._ f eq ⊗L⇒L₂1/\2 | 2>R1 (gt ._ refl eqU refl) | 2>R1 (gt ∙ refl () refl) 

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q₁)) (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) p₂ (q₁ ++ (sub q₂ (η B) ▸ q₃)) |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) p₂ (q₁ ++ (sub q₂ (U ⊛ η (A ⇒ B)) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q₁)) (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₂ q₃ = ⊗L⇒L₂1/\2 {p = p₁}

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q₁)) (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η B))) |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (U ⊛ η (A ⇒ B)))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q₁)) (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₂ q₃ = ⊗L⇒L₂1/\2 {p = p₁}
          
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) (q₁ ++ (sub p₁ (η (A' ⊗ B')) ▸ p₂)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (p₁ ◂ sub p₂ (η B))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (p₁ ◂ sub p₂ (U ⊛ η (A ⇒ B)))) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) (q₁ ++ (sub p₁ (η A' ⊛ η B') ▸ p₂)) q₂ = (⊗L⇒L₂1/\2 {p = q ++ (q₁ ◂ _)})

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 2/\1 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ (q₂ ++ (sub p₁ (η (A' ⊗ B')) ▸ p₂)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η B))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (U ⊛ η (A ⇒ B)))) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ (q₂ ++ (sub p₁ (η A' ⊛ η B') ▸ p₂)) = (⊗L⇒L₂1/\2 {p = q ++ (_ ▸ q₂)})
          
cut⇐R-cong2 p f eq (⊗L⇒L₂2/\1 {p = p₁}) with subeq _ _ p₁ p eq
cut⇐R-cong2 p f eq (⊗L⇒L₂2/\1 {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂2/\1 {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) (η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) (p₂ ++ (q₁ ◂ η (A ⇒ B))) p₃ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) (η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ = ⊗L⇒L₂2/\1 {p = p₁}
cut⇐R-cong2 ._ f eq ⊗L⇒L₂2/\1 | 2>L1 (gt ._ refl eqU refl) | 2>R1 (gt ∙ refl () refl) 

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (sub q₂ (η B) ▸ q₃)) p₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (sub q₂ (U ⊛ η (A ⇒ B)) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₂ q₃ = ⊗L⇒L₂2/\1 {p = p₁} 
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (q₂ ◂ sub q₃ (η B))) p₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (q₂ ◂ sub q₃ (U ⊛ η (A ⇒ B)))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₂ q₃ = ⊗L⇒L₂2/\1 {p = p₁}
          
cut⇐R-cong2 ._ f eq (⊗L⇒L₂2/\1 {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂) 
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) p₂ (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q₁)) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) p₂ (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) = ⊗L⇒L₂2/\1 {p = p₁}

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q₁)) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) = ⊗L⇒L₂2/\1 {p = p₁}
          
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) (q₁ ++ (p₁ ◂ sub p₂ (η (A' ⊗ B')))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (sub p₁ (η B) ▸ p₂)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (sub p₁ (U ⊛ η (A ⇒ B)) ▸ p₂)) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) (q₁ ++ (p₁ ◂ sub p₂ (η A' ⊛ η B'))) q₂ = ⊗L⇒L₂2/\1 {p = q ++ (q₁ ◂ _)} 

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 2/\1 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η (A' ⊗ B')))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₁ (q₂ ++ (sub p₁ (η B) ▸ p₂)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₁ (q₂ ++ (sub p₁ (U ⊛ η (A ⇒ B)) ▸ p₂)) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η A' ⊛ η B'))) = ⊗L⇒L₂2/\1 {p = q ++ (_ ▸ q₂)} 
          

cut⇐R-cong2 p f eq (⊗L⇐L₁ {p' = p'}) with subeq _ _ p' p eq
cut⇐R-cong2 {A = A'} {B'} ._ f refl (⊗L⇐L₁ {A' = A} {B} {p = p} {p'}) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2/\1 p' (η (A ⊗ B)) (η (B' ⇐ A')) ∙ p |
          subeq-2>L1 p' (sub p (η A ⊛ η B)) (η (B' ⇐ A')) ∙ = refl
cut⇐R-cong2 {A = A'} {B'} ._ f eq (⊗L⇐L₁ {A' = A} {B} {p = p}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p q (⊛eq eqU .proj₂)
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = ._} {p'}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 (p' ++ (η (B ⇐ A) ▸ q₁)) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2>R1 p' (η (B ⇐ A)) (η (B'' ⇐ A'')) (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) = ⊗L⇐L₁
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = ._} {p'}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 (p' ++ (η (B ⇐ A) ▸ q₁)) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2>R1 p' (η (B ⇐ A)) (η (B'' ⇐ A'')) (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) = ⊗L⇐L₁

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = p}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (η (B ⇐ A) ▸ p)) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ sub p (η A' ⊛ η B')) (η (B'' ⇐ A'')) q₁ q₂ = ⊗L⇐L₁
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = p}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₁ (q₂ ++ (η (B ⇐ A) ▸ p)) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ sub p (η A' ⊛ η B')) (η (B'' ⇐ A'')) q₁ q₂ = ⊗L⇐L₁

cut⇐R-cong2 p f eq (⊗L⇐L₂1/\2 {p = p₁}) with subeq _ _ p₁ p eq
cut⇐R-cong2 p f eq (⊗L⇐L₂1/\2 {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η B))) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (B ⇐ A) ⊛ U))) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) p₃ = ⊗L⇐L₂1/\2 {p = p₁}
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η B))) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (B ⇐ A) ⊛ U))) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) p₃ = ⊗L⇐L₂1/\2 {p = p₁}
          
cut⇐R-cong2 ._ f eq (⊗L⇐L₂1/\2 {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂) 
cut⇐R-cong2 ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f'}) | 2>R1 (gt ._ refl refl refl) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) U (η (B ⇐ A)) ∙ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (B ⇐ A)) p₂ (p₃ ++ (∙ ◂ U)) |
          subeq-2>L1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) U (η (B ⇐ A)) ∙ = ~ cut⊗L≗2/\1 p₁ p₂ p₃ (cut (_ ▸ ∙) f' f) _

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt ._ refl refl refl) | 2>R1 (gt q refl refl refl)
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) (η (B ⇐ A)) (η (B'' ⇐ A'')) q |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) p₂ (p₃ ++ (η (B ⇐ A) ▸ q)) |
          subeq-2>R1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) (η (B ⇐ A)) (η (B'' ⇐ A'')) q = ⊗L⇐L₂1/\2 {p = p₁}

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q₁)) (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) p₂ (q₁ ++ (sub q₂ (η B) ▸ q₃)) |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) p₂ (q₁ ++ (sub q₂ (η (B ⇐ A) ⊛ U) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q₁)) (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₂ q₃ = ⊗L⇐L₂1/\2 {p = p₁}

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q₁)) (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η B))) |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (B ⇐ A) ⊛ U))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q₁)) (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₂ q₃ = ⊗L⇐L₂1/\2 {p = p₁}
          
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) (q₁ ++ (sub p₁ (η (A' ⊗ B')) ▸ p₂)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (p₁ ◂ sub p₂ (η B))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (p₁ ◂ sub p₂ (η (B ⇐ A) ⊛ U))) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) (q₁ ++ (sub p₁ (η A' ⊛ η B') ▸ p₂)) q₂ = (⊗L⇐L₂1/\2 {p = q ++ (q₁ ◂ _)})

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 2/\1 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₁ (q₂ ++ (sub p₁ (η (A' ⊗ B')) ▸ p₂)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η B))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η (B ⇐ A) ⊛ U))) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₁ (q₂ ++ (sub p₁ (η A' ⊛ η B') ▸ p₂)) = (⊗L⇐L₂1/\2 {p = q ++ (_ ▸ q₂)})
          

cut⇐R-cong2 p f eq (⊗L⇐L₂2/\1 {p = p₁}) with subeq _ _ p₁ p eq
cut⇐R-cong2 p f eq (⊗L⇐L₂2/\1 {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⇐R-cong2 ._ f refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f'}) | 2>L1 (gt ._ refl refl refl) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) U (η (B ⇐ A)) ∙ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (B ⇐ A)) (p₂ ++ (∙ ◂ U)) p₃ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) U (η (B ⇐ A)) ∙  = ~ cut⊗L≗1/\2 p₁ p₂ p₃ (cut (_ ▸ ∙) f' f) _
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2>R1 (gt q refl refl refl)
  rewrite subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) (η (B ⇐ A)) (η (B'' ⇐ A'')) q |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) (p₂ ++ (η (B ⇐ A) ▸ q)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) (η (B ⇐ A)) (η (B'' ⇐ A'')) q = ⊗L⇐L₂2/\1 {p = p₁}


cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (sub q₂ (η B) ▸ q₃)) p₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (sub q₂ (η (B ⇐ A) ⊛ U) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₂ q₃ = ⊗L⇐L₂2/\1 {p = p₁} 
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (q₂ ◂ sub q₃ (η B))) p₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (q₂ ◂ sub q₃ (η (B ⇐ A) ⊛ U))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₂ q₃ = ⊗L⇐L₂2/\1 {p = p₁}
          
cut⇐R-cong2 ._ f eq (⊗L⇐L₂2/\1 {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂) 
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) p₂ (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q₁)) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) p₂ (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) = ⊗L⇐L₂2/\1 {p = p₁}

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q₁)) (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) = ⊗L⇐L₂2/\1 {p = p₁}
          
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) (q₁ ++ (p₁ ◂ sub p₂ (η (A' ⊗ B')))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (sub p₁ (η B) ▸ p₂)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) (q₁ ++ (sub p₁ (η (B ⇐ A) ⊛ U) ▸ p₂)) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) (q₁ ++ (p₁ ◂ sub p₂ (η A' ⊛ η B'))) q₂ = ⊗L⇐L₂2/\1 {p = q ++ (q₁ ◂ _)} 

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 2/\1 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η (A' ⊗ B')))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₁ (q₂ ++ (sub p₁ (η B) ▸ p₂)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (B'' ⇐ A'')) q₁ (q₂ ++ (sub p₁ (η (B ⇐ A) ⊛ U) ▸ p₂)) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η A' ⊛ η B'))) = ⊗L⇐L₂2/\1 {p = q ++ (_ ▸ q₂)} 

cut⇐R-cong2  p f eq (⇒L⇒L {r = r}) with subeq _ _ r p eq
cut⇐R-cong2 p f eq (⇒L⇒L {q = q} {r}) | 2>L1 (gt q₁ refl eqU refl) with subeq _ _ q q₁ (⊛eq eqU .proj₁)
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L {A = A} {B} {A'} {B'} {q = q} {r = r}) | 2>L1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 q (η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ |
          subeq-2>L1 (r ++ (q ◂ η (A ⇒ B))) (η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ = ⇒L⇒L
cut⇐R-cong2 ._ f eq ⇒L⇒L | 2>L1 (gt ._ refl eqU refl) | 2>R1 (gt ∙ refl () refl) 
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q (T ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 (r ++ (q ◂ η (A ⇒ B))) (T ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2>L1 r (η (A ⇒ B)) (η (B'' ⇐ A'')) (q ++ (sub q₂ (η B') ▸ q₃)) =  ⇒L⇒L
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q (T ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 (r ++ (q ◂ η (A ⇒ B))) (T ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2>L1 r (η (A ⇒ B)) (η (B'' ⇐ A'')) (q ++ (q₂ ◂ sub q₃ (η B'))) = ⇒L⇒L
cut⇐R-cong2 ._ f eq ⇒L⇒L | 2>R1 (gt ∙ refl () refl) 
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (T ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) (q₂ ++ (q ◂ η (A ⇒ B))) q₃ |
          subeq-1/\2 q₁ (sub q (η B') ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₂ q₃ = ⇒L⇒L
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (T ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₂ (q₃ ++ (q ◂ η (A ⇒ B))) |
          subeq-2/\1 q₁ (sub q (η B') ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₂ q₃ = ⇒L⇒L

cut⇐R-cong2 p f eq (⇒L⇒L₂ {p = p₁}) with subeq _ _ p₁ p eq
cut⇐R-cong2 p f eq (⇒L⇒L₂ {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl ) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) (p₂ ++ (q₁ ◂ η (A ⇒ B))) p₃ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) (η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ = ⇒L⇒L₂ {p = p₁}
cut⇐R-cong2 ._ f eq ⇒L⇒L₂ | 2>L1 (gt ._ refl eqU refl) | 2>R1 (gt ∙ refl () refl) 
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) (q ++ (sub q₁ (U ⊛ η (A ⇒ B)) ▸ q₂)) p₃ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (η B'))) (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) (q ++ (sub q₁ (η B) ▸ q₂)) p₃ = ⇒L⇒L₂ {p = p₁}
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) (q ++ (q₁ ◂ sub q₂ (U ⊛ η (A ⇒ B)))) p₃ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (η B'))) (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) (q ++ (q₁ ◂ sub q₂ (η B))) p₃ = ⇒L⇒L₂ {p = p₁}
  
cut⇐R-cong2 p f eq (⇒L⇒L₂ {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L₂ {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) (η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) p₂ (p₃ ++ (q₁ ◂ η (A' ⇒ B'))) |
          subeq-2>L1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ = ⇒L⇒L₂ {p = p₁}
cut⇐R-cong2 ._ f eq ⇒L⇒L₂ | 2>R1 (gt ._ refl eqU refl) | 2>R1 (gt ∙ refl () refl) 
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) p₂ (q ++ (sub q₁ (η B') ▸ q₂)) | 
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) p₂ (q ++ (sub q₁ (V ⊛ η (A' ⇒ B')) ▸ q₂)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ q₂ = ⇒L⇒L₂ {p = p₁}
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) p₂ (q ++ (q₁ ◂ sub q₂ (η B'))) | 
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) p₂ (q ++ (q₁ ◂ sub q₂ (V ⊛ η (A' ⇒ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ q₂ = ⇒L⇒L₂ {p = p₁}
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) (q₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) (q₁ ++ (p₂ ◂ sub p₃ (η B'))) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) (q₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) q₂ |
          subeq-1/\2 q (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = ⇒L⇒L₂ {p = q ++ (q₁ ◂ _)}
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ (q₂ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B'))) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) |
          subeq-2/\1 q (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = ⇒L⇒L₂ {p = q ++ (_ ▸ q₂)}

cut⇐R-cong2  p f eq (⇒L⇐L {r = r}) with subeq _ _ r p eq
cut⇐R-cong2 {U = U} ._ f refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r} {f'}) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2/\1 r (T ⊛ η (A' ⇒ B')) (η (B ⇐ A)) ∙ q |
          subeq-2>L1 r (sub q (η B')) (η (B ⇐ A)) ∙ = refl
cut⇐R-cong2 p f eq (⇒L⇐L {q = q} {r}) | 2>R1 (gt q₁ refl eqU refl) with subeq _ _ q q₁ (⊛eq eqU .proj₂)
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L {A = A} {B} {A'} {B'} {q = q} {r = r}) | 2>R1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 q (η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ |
          subeq-2>L1 (r ++ (η (B ⇐ A) ▸ q)) (η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ = ⇒L⇐L
cut⇐R-cong2 ._ f eq ⇒L⇐L | 2>R1 (gt ._ refl eqU refl) | 2>R1 (gt ∙ refl () refl) 
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q (T ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 (r ++ (η (B ⇐ A) ▸ q)) (T ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2>R1 r (η (B ⇐ A)) (η (B'' ⇐ A'')) (q ++ (sub q₂ (η B') ▸ q₃)) = ⇒L⇐L
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q (T ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 (r ++ (η (B ⇐ A) ▸ q)) (T ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2>R1 r (η (B ⇐ A)) (η (B'' ⇐ A'')) (q ++ (q₂ ◂ sub q₃ (η B'))) = ⇒L⇐L

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (T ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) (q₂ ++ (η (B ⇐ A) ▸ q)) q₃ |
          subeq-1/\2 q₁ (η (B ⇐ A) ⊛ sub q (η B')) (η (B'' ⇐ A'')) q₂ q₃ =  ⇒L⇐L 
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (T ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₂ (q₃ ++ (η (B ⇐ A) ▸ q)) |
          subeq-2/\1 q₁ (η (B ⇐ A) ⊛ sub q (η B')) (η (B'' ⇐ A'')) q₂ q₃ = ⇒L⇐L 

cut⇐R-cong2 p f eq (⇒L⇐L₂ {p = p₁}) with subeq _ _ p₁ p eq
cut⇐R-cong2 p f eq (⇒L⇐L₂ {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl ) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) (p₂ ++ (q₁ ◂ η (A ⇒ B))) p₃ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) (η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ = ⇒L⇐L₂ {p = p₁}
cut⇐R-cong2 ._ f eq ⇒L⇐L₂ | 2>L1 (gt ._ refl eqU refl) | 2>R1 (gt ∙ refl () refl) 
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) (q ++ (sub q₁ (U ⊛ η (A ⇒ B)) ▸ q₂)) p₃ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (η B'))) (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) (q ++ (sub q₁ (η B) ▸ q₂)) p₃ = ⇒L⇐L₂ {p = p₁}
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) (q ++ (q₁ ◂ sub q₂ (U ⊛ η (A ⇒ B)))) p₃ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (η B'))) (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) (q ++ (q₁ ◂ sub q₂ (η B))) p₃ = ⇒L⇐L₂ {p = p₁}
  
cut⇐R-cong2 p f eq (⇒L⇐L₂ {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut⇐R-cong2 ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f' = f'}) | 2>R1 (gt ._ refl refl refl) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) V (η (B' ⇐ A')) ∙ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (B' ⇐ A')) p₂ (p₃ ++ (∙ ◂ V)) |
          subeq-2>L1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) V (η (B' ⇐ A')) ∙ = ~ cut⇒L≗2/\1 p₁ p₂ p₃ _ (cut (_ ▸ ∙) f' f)  _
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f' = f'}) | 2>R1 (gt ._ refl refl refl) | 2>R1 (gt q refl refl refl)
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) (η (B' ⇐ A')) (η (B'' ⇐ A'')) q |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) p₂ (p₃ ++ (η (B' ⇐ A') ▸ q)) |
          subeq-2>R1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (B' ⇐ A')) (η (B'' ⇐ A'')) q = ⇒L⇐L₂ {p = p₁} 
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) p₂ (q ++ (sub q₁ (η B') ▸ q₂)) | 
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) p₂ (q ++ (sub q₁ (η (B' ⇐ A') ⊛ V) ▸ q₂)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) q₁ q₂ = ⇒L⇐L₂ {p = p₁}
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) p₂ (q ++ (q₁ ◂ sub q₂ (η B'))) | 
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) p₂ (q ++ (q₁ ◂ sub q₂ (η (B' ⇐ A') ⊛ V))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) q₁ q₂ = ⇒L⇐L₂ {p = p₁}
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) (q₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) (q₁ ++ (p₂ ◂ sub p₃ (η B'))) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) (q₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) q₂ |
          subeq-1/\2 q (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = ⇒L⇐L₂ {p = q ++ (q₁ ◂ _)}
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) q₁ (q₂ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B'))) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) |
          subeq-2/\1 q (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = ⇒L⇐L₂ {p = q ++ (_ ▸ q₂)}

cut⇐R-cong2  p f eq (⇐L⇒L {r = r}) with subeq _ _ r p eq
cut⇐R-cong2 p f eq (⇐L⇒L {q = q} {r}) | 2>L1 (gt q₁ refl eqU refl) with subeq _ _ q q₁ (⊛eq eqU .proj₁)
cut⇐R-cong2 ._ f refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r = r} {f'}) | 2>L1 (gt ._ refl refl refl) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 (r ++ (q ◂ η (A ⇒ B))) T (η (B' ⇐ A')) ∙ |
          subeq-2>L1 q T (η (B' ⇐ A')) ∙ = cut⇒L≗ r q _ (cut (_ ▸ ∙) f' f) _
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r = r} {f'}) | 2>L1 (gt ._ refl refl refl) | 2>R1 (gt q₁ refl refl refl) 
  rewrite subeq-2>R1 q (η (B' ⇐ A')) (η (B'' ⇐ A'')) q₁ |
          subeq-2>R1 (r ++ (q ◂ η (A ⇒ B))) (η (B' ⇐ A')) (η (B'' ⇐ A'')) q₁ = ⇐L⇒L
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B' ⇐ A') ⊛ T) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 (r ++ (q ◂ η (A ⇒ B))) (η (B' ⇐ A') ⊛ T) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2>L1 r (η (A ⇒ B)) (η (B'' ⇐ A'')) (q ++ (sub q₂ (η B') ▸ q₃)) =  ⇐L⇒L
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B' ⇐ A') ⊛ T) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 (r ++ (q ◂ η (A ⇒ B))) (η (B' ⇐ A') ⊛ T) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2>L1 r (η (A ⇒ B)) (η (B'' ⇐ A'')) (q ++ (q₂ ◂ sub q₃ (η B'))) = ⇐L⇒L
cut⇐R-cong2 ._ f eq ⇐L⇒L | 2>R1 (gt ∙ refl () refl) 
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (B' ⇐ A') ⊛ T) (η (B'' ⇐ A'')) (q₂ ++ (q ◂ η (A ⇒ B))) q₃ |
          subeq-1/\2 q₁ (sub q (η B') ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₂ q₃ = ⇐L⇒L
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (B' ⇐ A') ⊛ T) (η (B'' ⇐ A'')) q₂ (q₃ ++ (q ◂ η (A ⇒ B))) |
          subeq-2/\1 q₁ (sub q (η B') ⊛ η (A ⇒ B)) (η (B'' ⇐ A'')) q₂ q₃ = ⇐L⇒L

cut⇐R-cong2 p f eq (⇐L⇒L₂ {p = p₁}) with subeq _ _ p₁ p eq
cut⇐R-cong2 p f eq (⇐L⇒L₂ {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl ) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⇐R-cong2 ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f'}) | 2>L1 (gt ._ refl refl refl) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (B ⇐ A)) (p₂ ++ (∙ ◂ U)) p₃ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) U (η (B ⇐ A)) ∙  |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) U (η (B ⇐ A)) ∙ = cut⇒L≗1/\2  p₁ p₂ p₃ _ (cut (_ ▸ ∙) f' f) _

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f'}) | 2>L1 (gt ._ refl refl refl) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) (p₂ ++ (η (B ⇐ A) ▸ q)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (η (B ⇐ A)) (η (B'' ⇐ A'')) q |
          subeq-2/\1 p₁ (η B') (η (B'' ⇐ A'')) (p₂ ++ (η (B ⇐ A) ▸ q)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) (η (B ⇐ A)) (η (B'' ⇐ A'')) q = ⇐L⇒L₂ {p = p₁}

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) (q ++ (sub q₁ (η (B ⇐ A) ⊛ U) ▸ q₂)) p₃ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (η B'))) (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) (q ++ (sub q₁ (η B) ▸ q₂)) p₃ = ⇐L⇒L₂ {p = p₁}
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) (q ++ (q₁ ◂ sub q₂ (η (B ⇐ A) ⊛ U))) p₃ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (η B'))) (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) (q ++ (q₁ ◂ sub q₂ (η B))) p₃ = ⇐L⇒L₂ {p = p₁}
  
cut⇐R-cong2 p f eq (⇐L⇒L₂ {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L₂ {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) (η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) p₂ (p₃ ++ (q₁ ◂ η (A' ⇒ B'))) |
          subeq-2>L1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ = ⇐L⇒L₂ {p = p₁}
cut⇐R-cong2 ._ f eq ⇐L⇒L₂ | 2>R1 (gt ._ refl eqU refl) | 2>R1 (gt ∙ refl () refl) 
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) p₂ (q ++ (sub q₁ (η B') ▸ q₂)) | 
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) p₂ (q ++ (sub q₁ (V ⊛ η (A' ⇒ B')) ▸ q₂)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ q₂ = ⇐L⇒L₂ {p = p₁}
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) p₂ (q ++ (q₁ ◂ sub q₂ (η B'))) | 
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) p₂ (q ++ (q₁ ◂ sub q₂ (V ⊛ η (A' ⇒ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ q₂ = ⇐L⇒L₂ {p = p₁}
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) (q₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) (q₁ ++ (p₂ ◂ sub p₃ (η B'))) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) (q₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) q₂ |
          subeq-1/\2 q (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = ⇐L⇒L₂ {p = q ++ (q₁ ◂ _)}
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ (q₂ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B'))) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) |
          subeq-2/\1 q (V ⊛ η (A' ⇒ B')) (η (B'' ⇐ A'')) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = ⇐L⇒L₂ {p = q ++ (_ ▸ q₂)}

cut⇐R-cong2  p f eq (⇐L⇐L {r = r}) with subeq _ _ r p eq
cut⇐R-cong2 ._ f refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r = r} {f'}) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2/\1 r (η (B' ⇐ A') ⊛ T) (η (B ⇐ A)) ∙ q |
          subeq-2>L1 r (sub q (η B')) (η (B ⇐ A)) ∙ = refl
cut⇐R-cong2 p f eq (⇐L⇐L {q = q} {r}) | 2>R1 (gt q₁ refl eqU refl) with subeq _ _ q q₁ (⊛eq eqU .proj₂)
cut⇐R-cong2 ._ f refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r = r} {f'}) | 2>R1 (gt ._ refl refl refl) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 (r ++ (η (B ⇐ A) ▸ q)) T (η (B' ⇐ A')) ∙ |
          subeq-2>L1 q T (η (B' ⇐ A')) ∙ = cut⇐L≗ r q _ (cut (_ ▸ ∙) f' f) _
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r = r} {f'}) | 2>R1 (gt ._ refl refl refl) | 2>R1 (gt q₁ refl refl refl) 
  rewrite subeq-2>R1 q (η (B' ⇐ A')) (η (B'' ⇐ A'')) q₁ |
          subeq-2>R1 (r ++ (η (B ⇐ A) ▸ q)) (η (B' ⇐ A')) (η (B'' ⇐ A'')) q₁ = ⇐L⇐L
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B' ⇐ A') ⊛ T) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-1/\2 (r ++ (η (B ⇐ A) ▸ q)) (η (B' ⇐ A') ⊛ T) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2>R1 r (η (B ⇐ A)) (η (B'' ⇐ A'')) (q ++ (sub q₂ (η B') ▸ q₃)) =   ⇐L⇐L
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B' ⇐ A') ⊛ T) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2/\1 (r ++ (η (B ⇐ A) ▸ q)) (η (B' ⇐ A') ⊛ T) (η (B'' ⇐ A'')) q₂ q₃ |
          subeq-2>R1 r (η (B ⇐ A)) (η (B'' ⇐ A'')) (q ++ (q₂ ◂ sub q₃ (η B'))) =  ⇐L⇐L
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (B' ⇐ A') ⊛ T) (η (B'' ⇐ A'')) (q₂ ++ (η (B ⇐ A) ▸ q)) q₃ |
          subeq-1/\2 q₁ (η (B ⇐ A) ⊛ sub q (η B')) (η (B'' ⇐ A'')) q₂ q₃ = ⇐L⇐L
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (B' ⇐ A') ⊛ T) (η (B'' ⇐ A'')) q₂ (q₃ ++ (η (B ⇐ A) ▸ q)) |
          subeq-2/\1 q₁ (η (B ⇐ A) ⊛ sub q (η B')) (η (B'' ⇐ A'')) q₂ q₃ = ⇐L⇐L

cut⇐R-cong2 p f eq (⇐L⇐L₂ {p = p₁}) with subeq _ _ p₁ p eq
cut⇐R-cong2 p f eq (⇐L⇐L₂ {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl ) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⇐R-cong2 ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f'}) | 2>L1 (gt ._ refl refl refl) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (B ⇐ A)) (p₂ ++ (∙ ◂ U)) p₃ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) U (η (B ⇐ A)) ∙ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) U (η (B ⇐ A)) ∙ = cut⇐L≗1/\2 p₁ p₂ p₃ _ (cut (_ ▸ ∙) f' f) _

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f'}) | 2>L1 (gt ._ refl refl refl) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) (p₂ ++ (η (B ⇐ A) ▸ q)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (η (B ⇐ A)) (η (B'' ⇐ A'')) q |
          subeq-2/\1 p₁ (η B') (η (B'' ⇐ A'')) (p₂ ++ (η (B ⇐ A) ▸ q)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) (η (B ⇐ A)) (η (B'' ⇐ A'')) q = ⇐L⇐L₂ {p = p₁}

cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) (q ++ (sub q₁ (η (B ⇐ A) ⊛ U) ▸ q₂)) p₃ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (η B'))) (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) (q ++ (sub q₁ (η B) ▸ q₂)) p₃ = ⇐L⇐L₂ {p = p₁}
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) (q ++ (q₁ ◂ sub q₂ (η (B ⇐ A) ⊛ U))) p₃ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (η B'))) (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) (q ++ (q₁ ◂ sub q₂ (η B))) p₃ = ⇐L⇐L₂ {p = p₁}
  
cut⇐R-cong2 p f eq (⇐L⇐L₂ {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut⇐R-cong2 ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f' = f'}) | 2>R1 (gt ._ refl refl refl) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) V (η (B' ⇐ A')) ∙ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (B' ⇐ A')) p₂ (p₃ ++ (∙ ◂ V)) |
          subeq-2>L1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) V (η (B' ⇐ A')) ∙ = ~ cut⇐L≗2/\1 p₁ p₂ p₃ _ (cut (_ ▸ ∙) f' f) _
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f' = f'}) | 2>R1 (gt ._ refl refl refl) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) (η (B' ⇐ A')) (η (B'' ⇐ A'')) q |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) p₂ (p₃ ++ (η (B' ⇐ A') ▸ q)) |
          subeq-1/\2 p₁ (η B) (η (B'' ⇐ A'')) p₂ (p₃ ++ (η (B' ⇐ A') ▸ q)) |
          subeq-2>R1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (B' ⇐ A')) (η (B'' ⇐ A'')) q = ⇐L⇐L₂ {p = p₁}
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) p₂ (q ++ (sub q₁ (η B') ▸ q₂)) | 
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) p₂ (q ++ (sub q₁ (η (B' ⇐ A') ⊛ V) ▸ q₂)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) q₁ q₂ = ⇐L⇐L₂ {p = p₁}
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) q₁ q₂ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) p₂ (q ++ (q₁ ◂ sub q₂ (η B'))) | 
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) p₂ (q ++ (q₁ ◂ sub q₂ (η (B' ⇐ A') ⊛ V))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) q₁ q₂ = ⇐L⇐L₂ {p = p₁}
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) (q₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) (q₁ ++ (p₂ ◂ sub p₃ (η B'))) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) (q₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) q₂ |
          subeq-1/\2 q (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = ⇐L⇐L₂ {p = q ++ (q₁ ◂ _)}
cut⇐R-cong2 {A = A''} {B''} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) q₁ (q₂ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B'))) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (B'' ⇐ A'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) |
          subeq-2/\1 q (η (B' ⇐ A') ⊛ V) (η (B'' ⇐ A'')) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = ⇐L⇐L₂ {p = q ++ (_ ▸ q₂)}


cut⊗R-cong2 p f f₁ eq refl = refl
cut⊗R-cong2 p f f₁ eq (~ eq') = ~ (cut⊗R-cong2 p f f₁ eq eq')
cut⊗R-cong2 p f f₁ eq (eq' ∘ eq'') = cut⊗R-cong2 p f f₁ eq eq' ∘ cut⊗R-cong2 p f f₁ eq eq''
cut⊗R-cong2 p f f₁ refl (⇒R eq') = ⇒R (cut⊗R-cong2 (_ ▸ p) f f₁ refl eq')
cut⊗R-cong2 p f f₁ refl (⇐R eq') = ⇐R (cut⊗R-cong2 (p ◂ _) f f₁ refl eq')
cut⊗R-cong2 p f f₁ eq (⇒L {p = p₁} eq' eq'') with subeq _ _ p₁ p eq
cut⊗R-cong2 ._ f f₁ refl (⇒L {p = _} eq' eq'') | 2>L1 (gt q refl refl refl) = ⇒L (cut⊗R-cong2 q f f₁ refl eq') eq''
cut⊗R-cong2 ._ f f₁ eq (⇒L eq' eq'') | 2>R1 (gt ∙ refl () refl) 
cut⊗R-cong2 ._ f f₁ refl (⇒L {B = B} eq' eq'') | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⇒L eq' (cut⊗R-cong2 (q ++ (sub q₁ (η B) ▸ q₂)) f f₁ refl eq'')
cut⊗R-cong2 ._ f f₁ refl (⇒L {B = B} eq' eq'') | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⇒L eq' (cut⊗R-cong2 (q ++ (q₁ ◂ sub q₂ (η B))) f f₁ refl eq'')

cut⊗R-cong2 p f f₁ eq (⇐L {p = p₁} eq' eq'') with subeq _ _ p₁ p eq
cut⊗R-cong2 ._ f f₁ eq (⇐L eq' eq'') | 2>L1 (gt ∙ refl () refl)
cut⊗R-cong2 ._ f f₁ refl (⇐L eq' eq'') | 2>R1 (gt q refl refl refl) = ⇐L (cut⊗R-cong2 q f f₁ refl eq') eq''
cut⊗R-cong2 ._ f f₁ refl (⇐L {B = B} eq' eq'') | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⇐L eq' (cut⊗R-cong2 (q ++ (sub q₁ (η B) ▸ q₂)) f f₁ refl eq'')
cut⊗R-cong2 ._ f f₁ refl (⇐L {B = B} eq' eq'') | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⇐L eq' (cut⊗R-cong2 (q ++ (q₁ ◂ sub q₂ (η B))) f f₁ refl eq'')


cut⊗R-cong2 (p ◂ U) f f₁ refl (⊗R eq' eq'') = ⊗R (cut⊗R-cong2 p f f₁ refl eq') eq''
cut⊗R-cong2 (T ▸ p) f f₁ refl (⊗R eq' eq'') = ⊗R eq' (cut⊗R-cong2 p f f₁ refl eq'')
cut⊗R-cong2 p f f₁ eq (⊗L {p = p₁} eq') with subeq _ _ p₁ p eq
cut⊗R-cong2 ._ f f₁ refl (⊗L {A = A} {B} {p = p₁} eq') | 1≡2 (same refl refl refl) = cut-cong2 (p₁ ++ (∙ ◂ _)) f (cut-cong2 (p₁ ++ (η A ▸ ∙)) f₁ eq')
cut⊗R-cong2 ._ f f₁ refl (⊗L {A = A} {B} eq') | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⊗L (cut⊗R-cong2 (q ++ (sub q₁ (η A ⊛ η B) ▸ q₂)) f f₁ refl eq')
cut⊗R-cong2 ._ f f₁ refl (⊗L {A = A} {B} eq') | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⊗L (cut⊗R-cong2 (q ++ (q₁ ◂ sub q₂ (η A ⊛ η B))) f f₁ refl eq')
cut⊗R-cong2 p f f₁ eq (⇒L⇒R {p = p₁}) with subeq _ _ p₁ p eq
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇒L⇒R {A = A} {B} {p = p₁}) | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η (A' ⊗ B')) q = ⇒L⇒R
cut⊗R-cong2 ._ f f₁ eq ⇒L⇒R | 2>R1 (gt ∙ refl () refl) 
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇒L⇒R {U = U₁} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U₁ ⊛ η (A ⇒ B)) (η (A' ⊗ B')) q₁ q₂ = ⇒L⇒R
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇒L⇒R {U = U₁} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U₁ ⊛ η (A ⇒ B)) (η (A' ⊗ B')) q₁ q₂ = ⇒L⇒R
cut⊗R-cong2 p f f₁ eq (⇐L⇒R {p = p₁}) with subeq _ _ p₁ p eq
cut⊗R-cong2 ._ f f₁ eq (⇐L⇒R) | 2>L1 (gt ∙ refl () refl)
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇐L⇒R {A = A} {B} {p = p₁}) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η (A' ⊗ B')) q = ⇐L⇒R

cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇐L⇒R {U = U₁} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U₁) (η (A' ⊗ B')) q₁ q₂ = ⇐L⇒R
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇐L⇒R {U = U₁} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U₁) (η (A' ⊗ B')) q₁ q₂ = ⇐L⇒R

cut⊗R-cong2 p f f₁ eq (⊗L⇒R {p = p₁}) with subeq _ _ p₁ p eq
cut⊗R-cong2 ._ f f₁ refl (⊗L⇒R {A = A} {B} {p = p₁}) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p₁ (η (A ⊗ B)) = cut-cong2 (p₁ ++ (∙ ◂ _)) f (cut⇒R≗ (p₁ ++ (η A ▸ ∙)) f₁ _) ∘ cut⇒R≗ (p₁ ++ (∙ ◂ _)) f _
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⊗L⇒R {A = A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η (A' ⊗ B')) q₁ q₂ = ⊗L⇒R
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⊗L⇒R {A = A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η (A' ⊗ B')) q₁ q₂ = ⊗L⇒R
cut⊗R-cong2 p f f₁ eq (⇒L⇐R {p = p₁}) with subeq _ _ p₁ p eq
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇒L⇐R {U = U₁} {A} {B} {p = p₁}) | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η (A' ⊗ B')) q = ⇒L⇐R
cut⊗R-cong2 ._ f f₁ eq ⇒L⇐R | 2>R1 (gt ∙ refl () refl) 
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇒L⇐R {U = U₁} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U₁ ⊛ η (A ⇒ B)) (η (A' ⊗ B')) q₁ q₂ = ⇒L⇐R
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇒L⇐R {U = U₁} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U₁ ⊛ η (A ⇒ B)) (η (A' ⊗ B')) q₁ q₂ = ⇒L⇐R

cut⊗R-cong2 p f f₁ eq (⇐L⇐R {p = p₁}) with subeq _ _ p₁ p eq
cut⊗R-cong2 ._ f f₁ eq (⇐L⇐R) | 2>L1 (gt ∙ refl () refl)
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇐L⇐R {A = A} {B} {p = p₁}) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η (A' ⊗ B')) q = ⇐L⇐R
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇐L⇐R {U = U₁} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U₁) (η (A' ⊗ B')) q₁ q₂ = ⇐L⇐R
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇐L⇐R {U = U₁} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U₁) (η (A' ⊗ B')) q₁ q₂ = ⇐L⇐R

cut⊗R-cong2 p f f₁ eq (⊗L⇐R {p = p₁}) with subeq _ _ p₁ p eq
cut⊗R-cong2 ._ f f₁ refl (⊗L⇐R {A = A} {B} {p = p₁}) | 1≡2 (same refl refl refl)
  rewrite subeq-1≡2 p₁ (η (A ⊗ B)) = cut-cong2 (p₁ ++ (∙ ◂ _)) f (cut⇐R≗ (p₁ ++ (η A ▸ ∙)) f₁ _) ∘ cut⇐R≗ (p₁ ++ (∙ ◂ _)) f _
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⊗L⇐R {A = A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η (A' ⊗ B')) q₁ q₂ = ⊗L⇐R
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⊗L⇐R {A = A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η (A' ⊗ B')) q₁ q₂ = ⊗L⇐R

cut⊗R-cong2 p f f₁ eq (⇒L⊗R₁ {V = V} {p = p₁}) with subeq _ _ (p₁ ◂ V) p eq
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇒L⊗R₁ {A = A} {B} {p = p₁}) | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η (A' ⊗ B')) q = ⇒L⊗R₁
cut⊗R-cong2 ._ f f₁ eq ⇒L⊗R₁ | 2>R1 (gt ∙ refl () refl) 
cut⊗R-cong2 ._ f f₁ refl (⇒L⊗R₁) | 1/\2 (disj ∙ q₁ q₂ refl refl refl refl) = ⇒L⊗R₁
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇒L⊗R₁ {U = U₁} {A = A} {B}) | 1/\2 (disj (q ◂ U) q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U₁ ⊛ η (A ⇒ B)) (η (A' ⊗ B')) q₁ q₂ = ⇒L⊗R₁
cut⊗R-cong2 p f f₁ eq (⇒L⊗R₁) | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl () refl)
cut⊗R-cong2 ._ f f₁ eq (⇒L⊗R₁) | 2/\1 (disj ∙ q₁ q₂ refl refl refl ())
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇒L⊗R₁ {U = U₁} {A = A} {B}) | 2/\1 (disj (q ◂ U) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U₁ ⊛ η (A ⇒ B)) (η (A' ⊗ B')) q₁ q₂ = ⇒L⊗R₁
cut⊗R-cong2 ._ f f₁ eq (⇒L⊗R₁) | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl ())

cut⊗R-cong2 p f f₁ eq (⇒L⊗R₂ {V = V} {p = p₁}) with subeq _ _ (V ▸ p₁) p eq
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇒L⊗R₂ {A = A} {B} {p = p₁}) | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η (A' ⊗ B')) q = ⇒L⊗R₂
cut⊗R-cong2 ._ f f₁ eq ⇒L⊗R₂ | 2>R1 (gt ∙ refl () refl) 
cut⊗R-cong2 ._ f f₁ eq ⇒L⊗R₂ | 1/\2 (disj ∙ q₁ q₂ refl refl () refl)
cut⊗R-cong2 ._ f f₁ eq ⇒L⊗R₂ | 1/\2 (disj (q ◂ U) q₁ q₂ refl refl () refl) 
cut⊗R-cong2 {A = A'} {B'} p f f₁ refl (⇒L⊗R₂ {U = U₁} {A = A} {B}) | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U₁ ⊛ η (A ⇒ B)) (η (A' ⊗ B')) q₁ q₂ = ⇒L⊗R₂
cut⊗R-cong2 ._ f f₁ refl ⇒L⊗R₂ | 2/\1 (disj ∙ q₁ q₂ refl refl refl refl) = ⇒L⊗R₂
cut⊗R-cong2 ._ f f₁ eq ⇒L⊗R₂ | 2/\1 (disj (q ◂ U) q₁ q₂ refl refl refl ()) 
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇒L⊗R₂ {U = U₁} {A = A} {B}) | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U₁ ⊛ η (A ⇒ B)) (η (A' ⊗ B')) q₁ q₂ = ⇒L⊗R₂
  
cut⊗R-cong2 p f f₁ eq (⇐L⊗R₁ {V = V} {p = p₁}) with subeq _ _ (p₁ ◂ V) p eq
cut⊗R-cong2 ._ f f₁ eq (⇐L⊗R₁) | 2>L1 (gt ∙ refl () refl)
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇐L⊗R₁ {U = U₁} {A = A} {B} {p = p₁} {f'}) | 2>R1 (gt q refl refl refl)
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η (A' ⊗ B')) q = ⇐L⊗R₁
cut⊗R-cong2 ._ f f₁ refl (⇐L⊗R₁) | 1/\2 (disj ∙ q₁ q₂ refl refl refl refl) = ⇐L⊗R₁
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇐L⊗R₁ {U = U₁} {A = A} {B}) | 1/\2 (disj (q ◂ U) q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U₁) (η (A' ⊗ B')) q₁ q₂ = ⇐L⊗R₁
cut⊗R-cong2 p f f₁ eq (⇐L⊗R₁) | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl () refl)
cut⊗R-cong2 ._ f f₁ eq (⇐L⊗R₁) | 2/\1 (disj ∙ q₁ q₂ refl refl refl ())
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇐L⊗R₁ {U = U₁} {A = A} {B}) | 2/\1 (disj (q ◂ U) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U₁) (η (A' ⊗ B')) q₁ q₂ = ⇐L⊗R₁
cut⊗R-cong2 ._ f f₁ eq (⇐L⊗R₁) | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl ())

cut⊗R-cong2 p f f₁ eq (⇐L⊗R₂ {V = V} {p = p₁}) with subeq _ _ (V ▸ p₁) p eq
cut⊗R-cong2 ._ f f₁ eq (⇐L⊗R₂ {U = U₁} {A = A} {B} {p = p₁} {f'}) | 2>L1 (gt ∙ refl () refl) 
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇐L⊗R₂ {A = A} {B} {p = p₁}) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η (A' ⊗ B')) q = ⇐L⊗R₂
cut⊗R-cong2 ._ f f₁ eq (⇐L⊗R₂) | 1/\2 (disj ∙ q₁ q₂ refl refl () refl)
cut⊗R-cong2 ._ f f₁ eq (⇐L⊗R₂) | 1/\2 (disj (q ◂ U) q₁ q₂ refl refl () refl) 
cut⊗R-cong2 {A = A'} {B'} p f f₁ refl (⇐L⊗R₂ {U = U₁} {A = A} {B}) | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U₁) (η (A' ⊗ B')) q₁ q₂ = ⇐L⊗R₂
cut⊗R-cong2 ._ f f₁ refl (⇐L⊗R₂) | 2/\1 (disj ∙ q₁ q₂ refl refl refl refl) = ⇐L⊗R₂
cut⊗R-cong2 ._ f f₁ eq (⇐L⊗R₂) | 2/\1 (disj (q ◂ U) q₁ q₂ refl refl refl ()) 
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⇐L⊗R₂ {U = U₁} {A = A} {B}) | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U₁) (η (A' ⊗ B')) q₁ q₂ = ⇐L⊗R₂


cut⊗R-cong2 p f f₁ eq (⊗L⊗R₁ {U = U} {p = p₁}) with subeq _ _ (p₁ ◂ U) p eq
cut⊗R-cong2 ._ f f₁ refl (⊗L⊗R₁ {U = U} {A = A} {B} {p = p₁}) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p₁ (η (A ⊗ B)) = 
    cut-cong2 ((p₁ ++ (∙ ◂ _)) ◂ U) f (cut⊗R≗₁ (p₁ ++ (η A ▸ ∙)) f₁ _ _) ∘ cut⊗R≗₁ (p₁ ++ (∙ ◂ _)) f _ _
cut⊗R-cong2 ._ f f₁ refl ⊗L⊗R₁ | 1/\2 (disj ∙ q₁ q₂ refl refl refl refl) = ⊗L⊗R₁
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⊗L⊗R₁ {A = A} {B}) | 1/\2 (disj (q ◂ U) q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η (A' ⊗ B')) q₁ q₂ = ⊗L⊗R₁
cut⊗R-cong2 p f f₁ eq ⊗L⊗R₁ | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl () eqp₂)
cut⊗R-cong2 ._ f f₁ eq ⊗L⊗R₁ | 2/\1 (disj ∙ q₁ q₂ refl refl refl ())
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⊗L⊗R₁ {A = A} {B} {p = _}) | 2/\1 (disj (q ◂ U) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η (A' ⊗ B')) q₁ q₂ = ⊗L⊗R₁
cut⊗R-cong2 ._ f f₁ eq ⊗L⊗R₁ | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl ())

cut⊗R-cong2 p f f₁ eq (⊗L⊗R₂ {U = U} {p = p₁}) with subeq _ _ (U ▸ p₁) p eq
cut⊗R-cong2 ._ f f₁ refl (⊗L⊗R₂ {U = U} {A = A} {B} {p = p₁}) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p₁ (η (A ⊗ B)) = cut-cong2 (U ▸ (p₁ ++ (∙ ◂ _))) f (cut⊗R≗₂ (p₁ ++ (η A ▸ ∙)) f₁ _ _) ∘ cut⊗R≗₂ (p₁ ++ (∙ ◂ _)) f _ _ 
cut⊗R-cong2 ._ f f₁ eq ⊗L⊗R₂ | 1/\2 (disj ∙ q₁ q₂ refl refl () refl)
cut⊗R-cong2 ._ f f₁ eq ⊗L⊗R₂ | 1/\2 (disj (q ◂ U) q₁ q₂ refl refl () refl) 
cut⊗R-cong2 {A = A'} {B'} p f f₁ refl (⊗L⊗R₂ {A = A} {B}) | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η (A' ⊗ B')) q₁ q₂ = ⊗L⊗R₂
cut⊗R-cong2 ._ f f₁ refl ⊗L⊗R₂ | 2/\1 (disj ∙ q₁ q₂ refl refl refl refl) = ⊗L⊗R₂
cut⊗R-cong2 ._ f f₁ eq ⊗L⊗R₂ | 2/\1 (disj (q ◂ U) q₁ q₂ refl refl refl ()) 
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ refl (⊗L⊗R₂ {A = A} {B}) | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η (A' ⊗ B')) q₁ q₂ = ⊗L⊗R₂

cut⊗R-cong2 p f f₁ eq (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) with subeq _ _ p₁ p eq
cut⊗R-cong2 {A = A''} {B''} p f f₁ eq (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⊗R-cong2 p f f₁ refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 (p₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) (η (A ⊗ B)) |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A ⊗ B)) q p₃ |
          subeq-1≡2 (p₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) (η (A ⊗ B)) = 
            (~ cut⊗L≗1/\2 p₁ (q ++ (∙ ◂ _)) p₃ f _) ∘ cut-cong2 (p₁ ++ ((q ++ (∙ ◂ _)) ◂ sub p₃ (η (A' ⊗ B')))) f (~ cut⊗L≗1/\2 p₁ (q ++ (η A ▸ ∙)) p₃ f₁ _)
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (sub q₂ (η (A ⊗ B)) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (η (A ⊗ B)) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (η (A ⊗ B)) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (sub q₂ (η A ⊛ η B) ▸ q₃)) p₃ = ⊗L⊗L {p = p₁} {q₁ ++ (q₂ ◂ _)} {p₃}
          
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η (A ⊗ B)))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (η (A ⊗ B)) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (η (A ⊗ B)) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η A ⊛ η B))) p₃ = ⊗L⊗L {p = p₁} {q₁ ++ (_ ▸ q₃)} {p₃}

cut⊗R-cong2 {A = A''} {B''} p f f₁ eq (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut⊗R-cong2 p f f₁ refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1/\2 p₁ (η (A ⊗ B)) (η (A' ⊗ B')) p₂ p₃ |
          subeq-1≡2 (p₁ ++ (sub p₂ (η A ⊛ η B) ▸ q)) (η (A' ⊗ B')) |
          subeq-1≡2 (p₁ ++ (sub p₂ (η (A ⊗  B)) ▸ q)) (η (A' ⊗ B')) = 
            cut-cong2 (p₁ ++ (sub p₂ (η (A ⊗ B)) ▸ (q ++ (∙ ◂ _)))) f (cut⊗L≗2/\1 p₁ p₂ (q ++ (η A' ▸ ∙)) f₁ _) ∘ cut⊗L≗2/\1 p₁ p₂ (q ++ (∙ ◂ _)) f _
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 p₁ (η (A ⊗ B)) (η (A'' ⊗ B'')) p₂ (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η A ⊛ η B) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (sub p₂ (η (A ⊗ B)) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (A ⊗ B)) (η (A'' ⊗ B'')) p₂ (q₁ ++ (sub q₂ (η A' ⊛ η  B') ▸ q₃)) = ⊗L⊗L {p = p₁} {p₂} {q₁ ++ (q₂ ◂ _)}

cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 p₁ (η (A ⊗ B)) (η (A'' ⊗ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η A ⊛ η B) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (sub p₂ (η (A ⊗ B)) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (A ⊗ B)) (η (A'' ⊗ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η  B'))) = ⊗L⊗L {p = p₁} {p₂} {q₁ ++ (_ ▸ q₃)}

cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η (A'' ⊗ B'')) (q₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (sub p₂ (η A ⊛ η B) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (sub p₂ (η (A ⊗ B)) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (A ⊗ B)) (η (A'' ⊗ B'')) (q₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) q₂ = (⊗L⊗L {p = q ++ (q₁ ◂ _)})
          
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η (A'' ⊗ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₁ (q₂ ++ (sub p₂ (η A ⊛ η B) ▸ p₃)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₁ (q₂ ++ (sub p₂ (η (A ⊗ B)) ▸ p₃)) |
          subeq-2/\1 q (η (A ⊗ B)) (η (A'' ⊗ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) = (⊗L⊗L {p = q ++ (_ ▸ q₂)})

cut⊗R-cong2 p f f₁ eq (⊗L⇒L₁ {p' = p'}) with subeq _ _ p' p eq
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ eq (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = p} {p'}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p q (⊛eq eqU .proj₁)
cut⊗R-cong2 ._ f f₁ refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = p} {p'}) | 2>L1 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 q (η (A' ⊗ B')) |
          subeq-1≡2 (p' ++ (q ◂ η (A ⇒ B))) (η (A' ⊗ B')) = 
            cut-cong2 (p' ++ ((q ++ (∙ ◂ _)) ◂ η (A ⇒ B))) f (cut⇒L≗ p' (q ++ (η A' ▸ ∙)) _ f₁ _) ∘ cut⇒L≗ p' (q ++ (∙ ◂ _)) _ f _
          -- cut-cong2 (p' ++ ((q ++ (∙ ◂ _)) ◂ η (A ⇒ B))) f _ ∘ {! cut⇒L≗ p' (q ++ (∙ ◂ _)) _ f₁ _  !}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = ._} {p'}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 (p' ++ (q₁ ◂ η (A ⇒ B))) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2>L1 p' (η (A ⇒ B)) (η (A'' ⊗ B'')) (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) = ⊗L⇒L₁
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = ._} {p'}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 (p' ++ (q₁ ◂ η (A ⇒ B))) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2>L1 p' (η (A ⇒ B)) (η (A'' ⊗ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) = ⊗L⇒L₁

cut⊗R-cong2 ._ f f₁ eq ⊗L⇒L₁ | 2>R1 (gt ∙ refl () refl) 
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = p}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (p ◂ η (A ⇒ B))) q₂ |
          subeq-1/\2 q (sub p (η A' ⊛ η B') ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ q₂ = ⊗L⇒L₁
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = p}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₁ (q₂ ++ (p ◂ η (A ⇒ B))) |
          subeq-2/\1 q (sub p (η A' ⊛ η B') ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ q₂ = ⊗L⇒L₁
          
cut⊗R-cong2 p f f₁ eq (⊗L⇒L₂1/\2 {p = p₁}) with subeq _ _ p₁ p eq
cut⊗R-cong2 p f f₁ eq (⊗L⇒L₂1/\2 {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⊗R-cong2 ._ f f₁ refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η (A' ⊗ B')) q p₃ |
          subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (U ⊛ η (A ⇒ B))))(η (A' ⊗ B')) |
          subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (η B)))(η (A' ⊗ B')) = 
            cut-cong2 (p₁ ++ ((q ++ (∙ ◂ _)) ◂ sub p₃ (U ⊛ η (A ⇒ B)))) f (cut⇒L≗1/\2 p₁ (q ++ (η A' ▸ ∙)) p₃  _ f₁ _) ∘ cut⇒L≗1/\2 p₁ (q ++ (∙ ◂ _)) p₃ _ f _
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η B))) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (U ⊛ η (A ⇒ B)))) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) p₃ = ⊗L⇒L₂1/\2 {p = p₁}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η B))) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (U ⊛ η (A ⇒ B)))) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) p₃ = ⊗L⇒L₂1/\2 {p = p₁}
          
cut⊗R-cong2 ._ f f₁ eq (⊗L⇒L₂1/\2 {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂) 
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇒L₂1/\2 {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) (η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) p₂ (p₃ ++ (q₁ ◂ η (A ⇒ B))) |
          subeq-2>L1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) (η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ = ⊗L⇒L₂1/\2 {p = p₁}
cut⊗R-cong2 ._ f f₁ eq ⊗L⇒L₂1/\2 | 2>R1 (gt ._ refl eqU refl) | 2>R1 (gt ∙ refl () refl) 
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q₁)) (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) p₂ (q₁ ++ (sub q₂ (η B) ▸ q₃)) |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) p₂ (q₁ ++ (sub q₂ (U ⊛ η (A ⇒ B)) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q₁)) (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₂ q₃ = ⊗L⇒L₂1/\2 {p = p₁}

cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q₁)) (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η B))) |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (U ⊛ η (A ⇒ B)))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q₁)) (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₂ q₃ = ⊗L⇒L₂1/\2 {p = p₁}
          
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) (q₁ ++ (sub p₁ (η (A' ⊗ B')) ▸ p₂)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (p₁ ◂ sub p₂ (η B))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (p₁ ◂ sub p₂ (U ⊛ η (A ⇒ B)))) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) (q₁ ++ (sub p₁ (η A' ⊛ η B') ▸ p₂)) q₂ = (⊗L⇒L₂1/\2 {p = q ++ (q₁ ◂ _)})

cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 2/\1 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ (q₂ ++ (sub p₁ (η (A' ⊗ B')) ▸ p₂)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η B))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (U ⊛ η (A ⇒ B)))) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ (q₂ ++ (sub p₁ (η A' ⊛ η B') ▸ p₂)) = (⊗L⇒L₂1/\2 {p = q ++ (_ ▸ q₂)})
          
cut⊗R-cong2 p f f₁ eq (⊗L⇒L₂2/\1 {p = p₁}) with subeq _ _ p₁ p eq
cut⊗R-cong2 p f f₁ eq (⊗L⇒L₂2/\1 {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇒L₂2/\1 {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) (η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) (p₂ ++ (q₁ ◂ η (A ⇒ B))) p₃ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) (η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ = ⊗L⇒L₂2/\1 {p = p₁}
cut⊗R-cong2 ._ f f₁ eq ⊗L⇒L₂2/\1 | 2>L1 (gt ._ refl eqU refl) | 2>R1 (gt ∙ refl () refl) 
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (sub q₂ (η B) ▸ q₃)) p₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (sub q₂ (U ⊛ η (A ⇒ B)) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₂ q₃ = ⊗L⇒L₂2/\1 {p = p₁} 
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η B))) p₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (q₂ ◂ sub q₃ (U ⊛ η (A ⇒ B)))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₂ q₃ = ⊗L⇒L₂2/\1 {p = p₁}
          
cut⊗R-cong2 ._ f f₁ eq (⊗L⇒L₂2/\1 {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂) 
cut⊗R-cong2 ._ f f₁ refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A' ⊗ B')) p₂ q |
          subeq-1≡2 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q)) (η (A' ⊗ B')) |
          subeq-1≡2 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (A' ⊗ B')) = 
            cut-cong2 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ (q ++ (∙ ◂ _)))) f (cut⇒L≗2/\1 p₁ p₂ (q ++ (η A' ▸ ∙))  _ f₁ _) ∘ cut⇒L≗2/\1 p₁ p₂ (q ++ (∙ ◂ _)) _ f _
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) p₂ (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) p₂ (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) = ⊗L⇒L₂2/\1 {p = p₁}

cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) = ⊗L⇒L₂2/\1 {p = p₁}
          
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) (q₁ ++ (p₁ ◂ sub p₂ (η (A' ⊗ B')))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (sub p₁ (η B) ▸ p₂)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (sub p₁ (U ⊛ η (A ⇒ B)) ▸ p₂)) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) (q₁ ++ (p₁ ◂ sub p₂ (η A' ⊛ η B'))) q₂ = ⊗L⇒L₂2/\1 {p = q ++ (q₁ ◂ _)} 

cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 2/\1 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η (A' ⊗ B')))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₁ (q₂ ++ (sub p₁ (η B) ▸ p₂)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₁ (q₂ ++ (sub p₁ (U ⊛ η (A ⇒ B)) ▸ p₂)) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η A' ⊛ η B'))) = ⊗L⇒L₂2/\1 {p = q ++ (_ ▸ q₂)} 
          

cut⊗R-cong2 p f f₁ eq (⊗L⇐L₁ {p' = p'}) with subeq _ _ p' p eq
cut⊗R-cong2 ._ f f₁ eq ⊗L⇐L₁ | 2>L1 (gt ∙ refl () refl)
cut⊗R-cong2 {A = A'} {B'} ._ f f₁ eq (⊗L⇐L₁ {A' = A} {B} {p = p}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p q (⊛eq eqU .proj₂)
cut⊗R-cong2 ._ f f₁ refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = ._} {p'}) | 2>R1 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 (p' ++ (η (B ⇐ A) ▸ q)) (η (A' ⊗ B')) |
          subeq-1≡2 q (η (A' ⊗ B')) = 
            cut-cong2 (p' ++ (η (B ⇐ A) ▸ (q ++ (∙ ◂ _)))) f (cut⇐L≗ p' (q ++ (η A' ▸ ∙)) _ f₁ _) ∘ cut⇐L≗ p' (q ++ (∙ ◂ _)) _ f _
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = ._} {p'}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 (p' ++ (η (B ⇐ A) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2>R1 p' (η (B ⇐ A)) (η (A'' ⊗ B'')) (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) = ⊗L⇐L₁
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = ._} {p'}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 (p' ++ (η (B ⇐ A) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2>R1 p' (η (B ⇐ A)) (η (A'' ⊗ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) = ⊗L⇐L₁

cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = p}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (η (B ⇐ A) ▸ p)) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ sub p (η A' ⊛ η B')) (η (A'' ⊗ B'')) q₁ q₂ = ⊗L⇐L₁
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = p}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₁ (q₂ ++ (η (B ⇐ A) ▸ p)) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ sub p (η A' ⊛ η B')) (η (A'' ⊗ B'')) q₁ q₂ = ⊗L⇐L₁

cut⊗R-cong2 p f f₁ eq (⊗L⇐L₂1/\2 {p = p₁}) with subeq _ _ p₁ p eq
cut⊗R-cong2 p f f₁ eq (⊗L⇐L₂1/\2 {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⊗R-cong2 ._ f f₁ refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η (A' ⊗ B')) q p₃ |
          subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (η (B ⇐ A) ⊛ U))) (η (A' ⊗ B')) |
          subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (η B))) (η (A' ⊗ B')) = 
            cut-cong2 (p₁ ++ ((q ++ (∙ ◂ _)) ◂ sub p₃ (η (B ⇐ A) ⊛ U))) f (cut⇐L≗1/\2 p₁ (q ++ (η A' ▸ ∙)) p₃ _ f₁ _) ∘ cut⇐L≗1/\2 p₁ (q ++ (∙ ◂ _)) p₃ _ f _
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η B))) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (B ⇐ A) ⊛ U))) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) p₃ = ⊗L⇐L₂1/\2 {p = p₁}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η B))) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (B ⇐ A) ⊛ U))) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) p₃ = ⊗L⇐L₂1/\2 {p = p₁}
          
cut⊗R-cong2 ._ f f₁ eq (⊗L⇐L₂1/\2 {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂) 
cut⊗R-cong2 ._ f f₁ eq (⊗L⇐L₂1/\2) | 2>R1 (gt ._ refl eqU refl) | 2>L1 (gt ∙ refl () refl) 

cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt ._ refl refl refl) | 2>R1 (gt q refl refl refl)
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) (η (B ⇐ A)) (η (A'' ⊗ B'')) q |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) p₂ (p₃ ++ (η (B ⇐ A) ▸ q)) |
          subeq-2>R1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) (η (B ⇐ A)) (η (A'' ⊗ B'')) q = ⊗L⇐L₂1/\2 {p = p₁}

cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q₁)) (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) p₂ (q₁ ++ (sub q₂ (η B) ▸ q₃)) |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) p₂ (q₁ ++ (sub q₂ (η (B ⇐ A) ⊛ U) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q₁)) (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₂ q₃ = ⊗L⇐L₂1/\2 {p = p₁}

cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q₁)) (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η B))) |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (B ⇐ A) ⊛ U))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q₁)) (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₂ q₃ = ⊗L⇐L₂1/\2 {p = p₁}
          
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) (q₁ ++ (sub p₁ (η (A' ⊗ B')) ▸ p₂)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (p₁ ◂ sub p₂ (η B))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (p₁ ◂ sub p₂ (η (B ⇐ A) ⊛ U))) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) (q₁ ++ (sub p₁ (η A' ⊛ η B') ▸ p₂)) q₂ = (⊗L⇐L₂1/\2 {p = q ++ (q₁ ◂ _)})

cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 2/\1 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₁ (q₂ ++ (sub p₁ (η (A' ⊗ B')) ▸ p₂)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η B))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η (B ⇐ A) ⊛ U))) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₁ (q₂ ++ (sub p₁ (η A' ⊛ η B') ▸ p₂)) = (⊗L⇐L₂1/\2 {p = q ++ (_ ▸ q₂)})
          

cut⊗R-cong2 p f f₁ eq (⊗L⇐L₂2/\1 {p = p₁}) with subeq _ _ p₁ p eq
cut⊗R-cong2 p f f₁ eq (⊗L⇐L₂2/\1 {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⊗R-cong2 ._ f f₁ eq (⊗L⇐L₂2/\1) | 2>L1 (gt ._ refl eqU refl) | 2>L1 (gt ∙ refl () refl) 
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f'}) | 2>L1 (gt ._ refl refl refl) | 2>R1 (gt q refl refl refl)
  rewrite subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) (η (B ⇐ A)) (η (A'' ⊗ B'')) q |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) (p₂ ++ (η (B ⇐ A) ▸ q)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) (η (B ⇐ A)) (η (A'' ⊗ B'')) q = ⊗L⇐L₂2/\1 {p = p₁}


cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (sub q₂ (η B) ▸ q₃)) p₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (sub q₂ (η (B ⇐ A) ⊛ U) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₂ q₃ = ⊗L⇐L₂2/\1 {p = p₁} 
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η B))) p₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (q₂ ◂ sub q₃ (η (B ⇐ A) ⊛ U))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₂ q₃ = ⊗L⇐L₂2/\1 {p = p₁}
          
cut⊗R-cong2 ._ f f₁ eq (⊗L⇐L₂2/\1 {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂) 
cut⊗R-cong2 ._ f f₁ refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A' ⊗ B')) p₂ q |
          subeq-1≡2 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q)) (η (A' ⊗ B')) |
          subeq-1≡2 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (A' ⊗ B')) = 
            cut-cong2 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ (q ++ (∙ ◂ _)))) f (cut⇐L≗2/\1 p₁ p₂ (q ++ (η A' ▸ ∙)) _ f₁ _) ∘ cut⇐L≗2/\1 p₁ p₂ (q ++ (∙ ◂ _)) _ f _
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) p₂ (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) p₂ (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) = ⊗L⇐L₂2/\1 {p = p₁}

cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q₁)) (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) = ⊗L⇐L₂2/\1 {p = p₁}
          
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) (q₁ ++ (p₁ ◂ sub p₂ (η (A' ⊗ B')))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (sub p₁ (η B) ▸ p₂)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) (q₁ ++ (sub p₁ (η (B ⇐ A) ⊛ U) ▸ p₂)) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) (q₁ ++ (p₁ ◂ sub p₂ (η A' ⊛ η B'))) q₂ = ⊗L⇐L₂2/\1 {p = q ++ (q₁ ◂ _)} 

cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = ._} {p₁} {p₂}) | 2/\1 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η (A' ⊗ B')))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₁ (q₂ ++ (sub p₁ (η B) ▸ p₂)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η (A'' ⊗ B'')) q₁ (q₂ ++ (sub p₁ (η (B ⇐ A) ⊛ U) ▸ p₂)) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₁ (q₂ ++ (p₁ ◂ sub p₂ (η A' ⊛ η B'))) = ⊗L⇐L₂2/\1 {p = q ++ (_ ▸ q₂)} 

cut⊗R-cong2  p f f₁ eq (⇒L⇒L {r = r}) with subeq _ _ r p eq
cut⊗R-cong2 p f f₁ eq (⇒L⇒L {q = q} {r}) | 2>L1 (gt q₁ refl eqU refl) with subeq _ _ q q₁ (⊛eq eqU .proj₁)
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇒L {A = A} {B} {A'} {B'} {q = q} {r = r}) | 2>L1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 q (η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ |
          subeq-2>L1 (r ++ (q ◂ η (A ⇒ B))) (η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ = ⇒L⇒L
cut⊗R-cong2 ._ f f₁ eq ⇒L⇒L | 2>L1 (gt ._ refl eqU refl) | 2>R1 (gt ∙ refl () refl) 
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q (T ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 (r ++ (q ◂ η (A ⇒ B))) (T ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2>L1 r (η (A ⇒ B)) (η (A'' ⊗ B'')) (q ++ (sub q₂ (η B') ▸ q₃)) =  ⇒L⇒L
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q (T ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 (r ++ (q ◂ η (A ⇒ B))) (T ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2>L1 r (η (A ⇒ B)) (η (A'' ⊗ B'')) (q ++ (q₂ ◂ sub q₃ (η B'))) = ⇒L⇒L
cut⊗R-cong2 ._ f f₁ eq ⇒L⇒L | 2>R1 (gt ∙ refl () refl) 
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (T ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) (q₂ ++ (q ◂ η (A ⇒ B))) q₃ |
          subeq-1/\2 q₁ (sub q (η B') ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₂ q₃ = ⇒L⇒L
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (T ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₂ (q₃ ++ (q ◂ η (A ⇒ B))) |
          subeq-2/\1 q₁ (sub q (η B') ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₂ q₃ = ⇒L⇒L

cut⊗R-cong2 p f f₁ eq (⇒L⇒L₂ {p = p₁}) with subeq _ _ p₁ p eq
cut⊗R-cong2 p f f₁ eq (⇒L⇒L₂ {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl ) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) (p₂ ++ (q₁ ◂ η (A ⇒ B))) p₃ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) (η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ = ⇒L⇒L₂ {p = p₁}
cut⊗R-cong2 ._ f f₁ eq ⇒L⇒L₂ | 2>L1 (gt ._ refl eqU refl) | 2>R1 (gt ∙ refl () refl) 
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) (q ++ (sub q₁ (U ⊛ η (A ⇒ B)) ▸ q₂)) p₃ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (η B'))) (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) (q ++ (sub q₁ (η B) ▸ q₂)) p₃ = ⇒L⇒L₂ {p = p₁}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) (q ++ (q₁ ◂ sub q₂ (U ⊛ η (A ⇒ B)))) p₃ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (η B'))) (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) (q ++ (q₁ ◂ sub q₂ (η B))) p₃ = ⇒L⇒L₂ {p = p₁}
  
cut⊗R-cong2 p f f₁ eq (⇒L⇒L₂ {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇒L₂ {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) (η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) p₂ (p₃ ++ (q₁ ◂ η (A' ⇒ B'))) |
          subeq-2>L1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ = ⇒L⇒L₂ {p = p₁}
cut⊗R-cong2 ._ f f₁ eq ⇒L⇒L₂ | 2>R1 (gt ._ refl eqU refl) | 2>R1 (gt ∙ refl () refl) 
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) p₂ (q ++ (sub q₁ (η B') ▸ q₂)) | 
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) p₂ (q ++ (sub q₁ (V ⊛ η (A' ⇒ B')) ▸ q₂)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ q₂ = ⇒L⇒L₂ {p = p₁}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) p₂ (q ++ (q₁ ◂ sub q₂ (η B'))) | 
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) p₂ (q ++ (q₁ ◂ sub q₂ (V ⊛ η (A' ⇒ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ q₂ = ⇒L⇒L₂ {p = p₁}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) (q₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) (q₁ ++ (p₂ ◂ sub p₃ (η B'))) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) (q₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) q₂ |
          subeq-1/\2 q (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = ⇒L⇒L₂ {p = q ++ (q₁ ◂ _)}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ (q₂ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B'))) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) |
          subeq-2/\1 q (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = ⇒L⇒L₂ {p = q ++ (_ ▸ q₂)}

cut⊗R-cong2  p f f₁ eq (⇒L⇐L {r = r}) with subeq _ _ r p eq
cut⊗R-cong2 ._ f f₁ eq (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>L1 (gt ∙ refl () refl) 
cut⊗R-cong2 p f f₁ eq (⇒L⇐L {q = q} {r}) | 2>R1 (gt q₁ refl eqU refl) with subeq _ _ q q₁ (⊛eq eqU .proj₂)
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇐L {A = A} {B} {A'} {B'} {q = q} {r = r}) | 2>R1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 q (η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ |
          subeq-2>L1 (r ++ (η (B ⇐ A) ▸ q)) (η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ = ⇒L⇐L
cut⊗R-cong2 ._ f f₁ eq ⇒L⇐L | 2>R1 (gt ._ refl eqU refl) | 2>R1 (gt ∙ refl () refl) 
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q (T ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 (r ++ (η (B ⇐ A) ▸ q)) (T ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2>R1 r (η (B ⇐ A)) (η (A'' ⊗ B'')) (q ++ (sub q₂ (η B') ▸ q₃)) = ⇒L⇐L
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q (T ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 (r ++ (η (B ⇐ A) ▸ q)) (T ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2>R1 r (η (B ⇐ A)) (η (A'' ⊗ B'')) (q ++ (q₂ ◂ sub q₃ (η B'))) = ⇒L⇐L

cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (T ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) (q₂ ++ (η (B ⇐ A) ▸ q)) q₃ |
          subeq-1/\2 q₁ (η (B ⇐ A) ⊛ sub q (η B')) (η (A'' ⊗ B'')) q₂ q₃ =  ⇒L⇐L 
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (T ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₂ (q₃ ++ (η (B ⇐ A) ▸ q)) |
          subeq-2/\1 q₁ (η (B ⇐ A) ⊛ sub q (η B')) (η (A'' ⊗ B'')) q₂ q₃ = ⇒L⇐L 
 
cut⊗R-cong2 p f f₁ eq (⇒L⇐L₂ {p = p₁}) with subeq _ _ p₁ p eq
cut⊗R-cong2 p f f₁ eq (⇒L⇐L₂ {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl ) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) (p₂ ++ (q₁ ◂ η (A ⇒ B))) p₃ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) (η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ = ⇒L⇐L₂ {p = p₁}
cut⊗R-cong2 ._ f f₁ eq ⇒L⇐L₂ | 2>L1 (gt ._ refl eqU refl) | 2>R1 (gt ∙ refl () refl) 
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) (q ++ (sub q₁ (U ⊛ η (A ⇒ B)) ▸ q₂)) p₃ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (η B'))) (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) (q ++ (sub q₁ (η B) ▸ q₂)) p₃ = ⇒L⇐L₂ {p = p₁}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) (q ++ (q₁ ◂ sub q₂ (U ⊛ η (A ⇒ B)))) p₃ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (η B'))) (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) (q ++ (q₁ ◂ sub q₂ (η B))) p₃ = ⇒L⇐L₂ {p = p₁}
  
cut⊗R-cong2 p f f₁ eq (⇒L⇐L₂ {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut⊗R-cong2 ._ f f₁ eq (⇒L⇐L₂) | 2>R1 (gt ._ refl eqU refl) | 2>L1 (gt ∙ refl () refl)
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f' = f'}) | 2>R1 (gt ._ refl refl refl) | 2>R1 (gt q refl refl refl)
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) (η (B' ⇐ A')) (η (A'' ⊗ B'')) q |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) p₂ (p₃ ++ (η (B' ⇐ A') ▸ q)) |
          subeq-2>R1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (B' ⇐ A')) (η (A'' ⊗ B'')) q = ⇒L⇐L₂ {p = p₁} 
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) p₂ (q ++ (sub q₁ (η B') ▸ q₂)) | 
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) p₂ (q ++ (sub q₁ (η (B' ⇐ A') ⊛ V) ▸ q₂)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) q₁ q₂ = ⇒L⇐L₂ {p = p₁}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) p₂ (q ++ (q₁ ◂ sub q₂ (η B'))) | 
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) p₂ (q ++ (q₁ ◂ sub q₂ (η (B' ⇐ A') ⊛ V))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) q₁ q₂ = ⇒L⇐L₂ {p = p₁}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) (q₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) (q₁ ++ (p₂ ◂ sub p₃ (η B'))) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) (q₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) q₂ |
          subeq-1/\2 q (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = ⇒L⇐L₂ {p = q ++ (q₁ ◂ _)}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) q₁ (q₂ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B'))) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) |
          subeq-2/\1 q (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = ⇒L⇐L₂ {p = q ++ (_ ▸ q₂)}

cut⊗R-cong2  p f f₁ eq (⇐L⇒L {r = r}) with subeq _ _ r p eq
cut⊗R-cong2 p f f₁ eq (⇐L⇒L {q = q} {r}) | 2>L1 (gt q₁ refl eqU refl) with subeq _ _ q q₁ (⊛eq eqU .proj₁)
cut⊗R-cong2 ._ f f₁ eq ⇐L⇒L | 2>L1 (gt ._ refl eqU refl) | 2>L1 (gt ∙ refl () refl)
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r = r} {f'}) | 2>L1 (gt ._ refl refl refl) | 2>R1 (gt q₁ refl refl refl) 
  rewrite subeq-2>R1 q (η (B' ⇐ A')) (η (A'' ⊗ B'')) q₁ |
          subeq-2>R1 (r ++ (q ◂ η (A ⇒ B))) (η (B' ⇐ A')) (η (A'' ⊗ B'')) q₁ = ⇐L⇒L
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B' ⇐ A') ⊛ T) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 (r ++ (q ◂ η (A ⇒ B))) (η (B' ⇐ A') ⊛ T) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2>L1 r (η (A ⇒ B)) (η (A'' ⊗ B'')) (q ++ (sub q₂ (η B') ▸ q₃)) =  ⇐L⇒L
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B' ⇐ A') ⊛ T) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 (r ++ (q ◂ η (A ⇒ B))) (η (B' ⇐ A') ⊛ T) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2>L1 r (η (A ⇒ B)) (η (A'' ⊗ B'')) (q ++ (q₂ ◂ sub q₃ (η B'))) = ⇐L⇒L
cut⊗R-cong2 ._ f f₁ eq ⇐L⇒L | 2>R1 (gt ∙ refl () refl) 
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (B' ⇐ A') ⊛ T) (η (A'' ⊗ B'')) (q₂ ++ (q ◂ η (A ⇒ B))) q₃ |
          subeq-1/\2 q₁ (sub q (η B') ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₂ q₃ = ⇐L⇒L
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (B' ⇐ A') ⊛ T) (η (A'' ⊗ B'')) q₂ (q₃ ++ (q ◂ η (A ⇒ B))) |
          subeq-2/\1 q₁ (sub q (η B') ⊛ η (A ⇒ B)) (η (A'' ⊗ B'')) q₂ q₃ = ⇐L⇒L

cut⊗R-cong2 p f f₁ eq (⇐L⇒L₂ {p = p₁}) with subeq _ _ p₁ p eq
cut⊗R-cong2 p f f₁ eq (⇐L⇒L₂ {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl ) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⊗R-cong2 ._ f f₁ eq (⇐L⇒L₂) | 2>L1 (gt ._ refl eqU refl) | 2>L1 (gt ∙ refl () refl)

cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f'}) | 2>L1 (gt ._ refl refl refl) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) (p₂ ++ (η (B ⇐ A) ▸ q)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (η (B ⇐ A)) (η (A'' ⊗ B'')) q |
          subeq-2/\1 p₁ (η B') (η (A'' ⊗ B'')) (p₂ ++ (η (B ⇐ A) ▸ q)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) (η (B ⇐ A)) (η (A'' ⊗ B'')) q = ⇐L⇒L₂ {p = p₁}

cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) (q ++ (sub q₁ (η (B ⇐ A) ⊛ U) ▸ q₂)) p₃ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (η B'))) (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) (q ++ (sub q₁ (η B) ▸ q₂)) p₃ = ⇐L⇒L₂ {p = p₁}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) (q ++ (q₁ ◂ sub q₂ (η (B ⇐ A) ⊛ U))) p₃ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (η B'))) (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) (q ++ (q₁ ◂ sub q₂ (η B))) p₃ = ⇐L⇒L₂ {p = p₁}
  
cut⊗R-cong2 p f f₁ eq (⇐L⇒L₂ {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇒L₂ {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) (η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) p₂ (p₃ ++ (q₁ ◂ η (A' ⇒ B'))) |
          subeq-2>L1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ = ⇐L⇒L₂ {p = p₁}
cut⊗R-cong2 ._ f f₁ eq ⇐L⇒L₂ | 2>R1 (gt ._ refl eqU refl) | 2>R1 (gt ∙ refl () refl) 
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) p₂ (q ++ (sub q₁ (η B') ▸ q₂)) | 
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) p₂ (q ++ (sub q₁ (V ⊛ η (A' ⇒ B')) ▸ q₂)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ q₂ = ⇐L⇒L₂ {p = p₁}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) p₂ (q ++ (q₁ ◂ sub q₂ (η B'))) | 
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) p₂ (q ++ (q₁ ◂ sub q₂ (V ⊛ η (A' ⇒ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q)) (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ q₂ = ⇐L⇒L₂ {p = p₁}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) (q₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) (q₁ ++ (p₂ ◂ sub p₃ (η B'))) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) (q₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) q₂ |
          subeq-1/\2 q (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = ⇐L⇒L₂ {p = q ++ (q₁ ◂ _)}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ (q₂ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B'))) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) |
          subeq-2/\1 q (V ⊛ η (A' ⇒ B')) (η (A'' ⊗ B'')) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = ⇐L⇒L₂ {p = q ++ (_ ▸ q₂)}
cut⊗R-cong2  p f f₁ eq (⇐L⇐L {r = r}) with subeq _ _ r p eq
cut⊗R-cong2 ._ f f₁ eq ⇐L⇐L | 2>L1 (gt ∙ refl () refl) 
cut⊗R-cong2 p f f₁ eq (⇐L⇐L {q = q} {r}) | 2>R1 (gt q₁ refl eqU refl) with subeq _ _ q q₁ (⊛eq eqU .proj₂)
cut⊗R-cong2 ._ f f₁ eq (⇐L⇐L) | 2>R1 (gt ._ refl eqU refl) | 2>L1 (gt ∙ refl () refl)
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r = r} {f'}) | 2>R1 (gt ._ refl refl refl) | 2>R1 (gt q₁ refl refl refl) 
  rewrite subeq-2>R1 q (η (B' ⇐ A')) (η (A'' ⊗ B'')) q₁ |
          subeq-2>R1 (r ++ (η (B ⇐ A) ▸ q)) (η (B' ⇐ A')) (η (A'' ⊗ B'')) q₁ = ⇐L⇐L
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B' ⇐ A') ⊛ T) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-1/\2 (r ++ (η (B ⇐ A) ▸ q)) (η (B' ⇐ A') ⊛ T) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2>R1 r (η (B ⇐ A)) (η (A'' ⊗ B'')) (q ++ (sub q₂ (η B') ▸ q₃)) =   ⇐L⇐L
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B' ⇐ A') ⊛ T) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2/\1 (r ++ (η (B ⇐ A) ▸ q)) (η (B' ⇐ A') ⊛ T) (η (A'' ⊗ B'')) q₂ q₃ |
          subeq-2>R1 r (η (B ⇐ A)) (η (A'' ⊗ B'')) (q ++ (q₂ ◂ sub q₃ (η B'))) =  ⇐L⇐L
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (B' ⇐ A') ⊛ T) (η (A'' ⊗ B'')) (q₂ ++ (η (B ⇐ A) ▸ q)) q₃ |
          subeq-1/\2 q₁ (η (B ⇐ A) ⊛ sub q (η B')) (η (A'' ⊗ B'')) q₂ q₃ = ⇐L⇐L
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (B' ⇐ A') ⊛ T) (η (A'' ⊗ B'')) q₂ (q₃ ++ (η (B ⇐ A) ▸ q)) |
          subeq-2/\1 q₁ (η (B ⇐ A) ⊛ sub q (η B')) (η (A'' ⊗ B'')) q₂ q₃ = ⇐L⇐L

cut⊗R-cong2 p f f₁ eq (⇐L⇐L₂ {p = p₁}) with subeq _ _ p₁ p eq
cut⊗R-cong2 p f f₁ eq (⇐L⇐L₂ {p = p₁} {p₂}) | 2>L1 (gt q refl eqU refl ) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut⊗R-cong2 ._ f f₁ eq (⇐L⇐L₂) | 2>L1 (gt ._ refl eqU refl) | 2>L1 (gt ∙ refl () refl)

cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f'}) | 2>L1 (gt ._ refl refl refl) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) (p₂ ++ (η (B ⇐ A) ▸ q)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (η (B ⇐ A)) (η (A'' ⊗ B'')) q |
          subeq-2/\1 p₁ (η B') (η (A'' ⊗ B'')) (p₂ ++ (η (B ⇐ A) ▸ q)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) (η (B ⇐ A)) (η (A'' ⊗ B'')) q = ⇐L⇐L₂ {p = p₁}

cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) (q ++ (sub q₁ (η (B ⇐ A) ⊛ U) ▸ q₂)) p₃ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (η B'))) (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-1/\2 (p₁ ++ (q ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) (q ++ (sub q₁ (η B) ▸ q₂)) p₃ = ⇐L⇐L₂ {p = p₁}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) (q ++ (q₁ ◂ sub q₂ (η (B ⇐ A) ⊛ U))) p₃ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (η B'))) (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-2/\1 (p₁ ++ (q ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) (q ++ (q₁ ◂ sub q₂ (η B))) p₃ = ⇐L⇐L₂ {p = p₁}
  
cut⊗R-cong2 p f f₁ eq (⇐L⇐L₂ {p = p₁} {p₂ = p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut⊗R-cong2 ._ f f₁ eq (⇐L⇐L₂) | 2>R1 (gt ._ refl eqU refl) | 2>L1 (gt ∙ refl () refl) 
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃} {f' = f'}) | 2>R1 (gt ._ refl refl refl) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) (η (B' ⇐ A')) (η (A'' ⊗ B'')) q |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) p₂ (p₃ ++ (η (B' ⇐ A') ▸ q)) |
          subeq-1/\2 p₁ (η B) (η (A'' ⊗ B'')) p₂ (p₃ ++ (η (B' ⇐ A') ▸ q)) |
          subeq-2>R1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (B' ⇐ A')) (η (A'' ⊗ B'')) q = ⇐L⇐L₂ {p = p₁}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) p₂ (q ++ (sub q₁ (η B') ▸ q₂)) | 
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) p₂ (q ++ (sub q₁ (η (B' ⇐ A') ⊛ V) ▸ q₂)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) q₁ q₂ = ⇐L⇐L₂ {p = p₁}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) q₁ q₂ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) p₂ (q ++ (q₁ ◂ sub q₂ (η B'))) | 
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) p₂ (q ++ (q₁ ◂ sub q₂ (η (B' ⇐ A') ⊛ V))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) q₁ q₂ = ⇐L⇐L₂ {p = p₁}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) (q₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) (q₁ ++ (p₂ ◂ sub p₃ (η B'))) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) (q₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) q₂ |
          subeq-1/\2 q (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = ⇐L⇐L₂ {p = q ++ (q₁ ◂ _)}
cut⊗R-cong2 {A = A''} {B''} ._ f f₁ refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) q₁ (q₂ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B'))) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (A'' ⊗ B'')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) |
          subeq-2/\1 q (η (B' ⇐ A') ⊛ V) (η (A'' ⊗ B'')) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = ⇐L⇐L₂ {p = q ++ (_ ▸ q₂)}