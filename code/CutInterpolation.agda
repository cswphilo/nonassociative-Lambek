{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module CutInterpolation where

open import Relation.Binary.PropositionalEquality hiding ([_]; _≗_) 
open import Data.Product
open import Data.Empty
open import Fma
open import SeqCalc
open import Cut
open import Interpolation
open import SubEqProperties
open import Equations

sub∙ : ∀ {T} (p : Path T) → sub p ∙ ≡ T
sub∙ ∙ = refl
sub∙ (p ◂ U) = cong (_⊛ _) (sub∙ p)
sub∙ (T ▸ p) = cong (_ ⊛_) (sub∙ p)

{-# REWRITE sub∙ #-}

++∙ : ∀ {T} (p : Path T) → p ++ ∙ ≡ p
++∙ ∙ = refl
++∙ (p ◂ U) = cong (_◂ U) (++∙ p)
++∙ (T ▸ p) = cong (T ▸_) (++∙ p)

{-# REWRITE ++∙ #-}
-- right unitality of ++


cut-intrp : ∀ {T} (p : Path T) U {V C}
  → (f : V ⊢ C) (eq : V ≡ sub p U) 
  →  cut p (MIP.h (mip p U f eq)) (MIP.g (mip p U f eq)) ≗ subst-cxt eq f
  
cut-intrp p U (⇒R f) refl = 
  cut⇒R≗ p (MIP.h (mip (_ ▸ p) U f refl)) (MIP.g (mip (_ ▸ p) U f refl)) 
  ∘ ⇒R (cut-intrp (_ ▸ p) U f refl)
  
cut-intrp p U (⇐R f) refl = 
  cut⇐R≗ p (MIP.h (mip (p ◂ _) U f refl)) (MIP.g (mip (p ◂ _) U f refl)) 
  ∘ ⇐R (cut-intrp (p ◂ _) U f refl)

cut-intrp p U (⇒L {U = U₁} {A} {B} p₁ f f₁) eq with subeq U (U₁ ⊛ η (A ⇒ B)) p p₁ (sym eq)
cut-intrp p ._ (⇒L {U = U₁} {A} {B} ._ f f₁) refl | 1≡2 (same refl refl refl) = ⇒L refl (cut-intrp p _ f₁ refl)
cut-intrp p ._ (⇒L {U = U₁} {A} {B} ._ f f₁) refl | 2>L1 (gt q refl refl refl) = ⇒L refl (cut-intrp p _ f₁ refl)
cut-intrp p ._ (⇒L {U = U₁} {A} {B} ._ f f₁) refl | 2>R1 (gt q refl refl refl) = ⇒L refl (cut-intrp p _ f₁ refl)

cut-intrp ._ U (⇒L {U = ._} {A} {B} p₁ f f₁) refl | 1>L2 (gt q refl refl refl) = 
  cut⇒L≗ p₁ q f₁ (MIP.h (mip q U f refl)) (MIP.g (mip q U f refl)) 
  ∘ ⇒L (cut-intrp _ U f refl) refl

cut-intrp ._ ._ (⇒L {U = U₁} {A} {B} p₁ f f₁) refl | 1>R2 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 p₁ U₁ (η (MIP.D (mip ∙ U₁ f refl) ⇒ MIP.D (mip p₁ (η B) f₁ refl))) ∙ = 
    cut-cong1 p₁ (MIP.g (mip p₁ (η B) f₁ refl)) (cut⇒L≗ ∙ ∙ (MIP.h (mip p₁ (η B) f₁ refl)) (MIP.h (mip ∙ U₁ f refl)) (MIP.g (mip ∙ U₁ f refl))) 
    ∘ ⇒L (cut-intrp ∙ _ f refl) (cut-intrp p₁ _ f₁ refl)

cut-intrp ._ U (⇒L {U = U₁} {A} {B} ._ f f₁) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) =
  cut⇒L≗1/\2 q q₁ q₂ f (MIP.h (mip (q ++ (q₁ ◂ sub q₂ (η B))) U f₁ refl)) (MIP.g (mip (q ++ (q₁ ◂ sub q₂ (η B))) U f₁ refl)) 
  ∘ ⇒L refl (cut-intrp _ U f₁ refl)
cut-intrp ._ U (⇒L {U = U₁} {A} {B} ._ f f₁) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 
  cut⇒L≗2/\1 q q₁ q₂ f (MIP.h (mip (q ++ (sub q₁ (η B) ▸ q₂)) U f₁ refl)) (MIP.g (mip (q ++ (sub q₁ (η B) ▸ q₂)) U f₁ refl)) 
  ∘ ⇒L refl (cut-intrp _ U f₁ refl)

cut-intrp p U (⇐L {U = U₁} {A} {B} p₁ f f₁) eq with subeq U (η (B ⇐ A) ⊛ U₁) p p₁ (sym eq)
cut-intrp p ._ (⇐L {U = U₁} {A} {B} ._ f f₁) refl | 1≡2 (same refl refl refl) = ⇐L refl (cut-intrp p _ f₁ refl)
cut-intrp p ._ (⇐L {U = U₁} {A} {B} ._ f f₁) refl | 2>L1 (gt q refl refl refl) = ⇐L refl (cut-intrp p _ f₁ refl)
cut-intrp p ._ (⇐L {U = U₁} {A} {B} ._ f f₁) refl | 2>R1 (gt q refl refl refl) = ⇐L refl (cut-intrp p _ f₁ refl)

cut-intrp ._ ._ (⇐L {U = U₁} {A} {B} p₁ f f₁) refl | 1>L2 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 p₁ U₁ (η (MIP.D (mip p₁ (η B) f₁ refl) ⇐ MIP.D (mip ∙ U₁ f refl))) ∙ = 
    cut-cong1 p₁ (MIP.g (mip p₁ (η B) f₁ refl)) (cut⇐L≗ ∙ ∙ (MIP.h (mip p₁ (η B) f₁ refl)) (MIP.h (mip ∙ U₁ f refl)) (MIP.g (mip ∙ U₁ f refl))) 
    ∘ ⇐L (cut-intrp ∙ _ f refl) (cut-intrp p₁ _ f₁ refl)

cut-intrp ._ U (⇐L {U = ._} {A} {B} p₁ f f₁) refl | 1>R2 (gt q refl refl refl) = 
  cut⇐L≗ p₁ q f₁ (MIP.h (mip q U f refl)) (MIP.g (mip q U f refl)) 
  ∘ ⇐L (cut-intrp _ U f refl) refl
cut-intrp ._ U (⇐L {U = U₁} {A} {B} ._ f f₁) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) =
  cut⇐L≗1/\2 q q₁ q₂ f (MIP.h (mip (q ++ (q₁ ◂ sub q₂ (η B))) U f₁ refl)) (MIP.g (mip (q ++ (q₁ ◂ sub q₂ (η B))) U f₁ refl)) 
  ∘ ⇐L refl (cut-intrp _ U f₁ refl)
cut-intrp ._ U (⇐L {U = U₁} {A} {B} ._ f f₁) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 
  cut⇐L≗2/\1 q q₁ q₂ f (MIP.h (mip (q ++ (sub q₁ (η B) ▸ q₂)) U f₁ refl)) (MIP.g (mip (q ++ (sub q₁ (η B) ▸ q₂)) U f₁ refl)) 
  ∘ ⇐L refl (cut-intrp _ U f₁ refl)

cut-intrp ∙ ._ (⊗R {T} {U} f f₁) refl = 
  cut-cong2 (∙ ◂ U) (MIP.h (mip ∙ T f refl))  (cut⊗R≗₂ ∙ (MIP.h (mip ∙ U f₁ refl)) (MIP.g (mip ∙ T f refl)) (MIP.g (mip ∙ U f₁ refl))) 
  ∘ (cut⊗R≗₁ ∙ (MIP.h (mip ∙ T f refl)) (MIP.g (mip ∙ T f refl)) (cut ∙ (MIP.h (mip ∙ U f₁ refl)) (MIP.g (mip ∙ U f₁ refl))) 
  ∘ ⊗R (cut-intrp ∙ _ f refl) (cut-intrp ∙ _ f₁ refl))
cut-intrp (p ◂ U₁) U (⊗R f f₁) refl = 
  cut⊗R≗₁ p (MIP.h (mip p U f refl)) (MIP.g (mip p U f refl)) f₁ 
  ∘ ⊗R (cut-intrp p _ f refl) refl
cut-intrp (T ▸ p) U (⊗R f f₁) refl = 
  cut⊗R≗₂ p (MIP.h (mip p U f₁ refl)) f (MIP.g (mip p U f₁ refl)) 
  ∘ ⊗R refl (cut-intrp p _ f₁ refl)

cut-intrp p U (⊗L {A = A} {B} p₁ f) eq with subeq U (η (A ⊗ B)) p p₁ (sym eq)
cut-intrp p ._ (⊗L ._ f) refl | 1≡2 (same refl refl refl) = ⊗L (cut-intrp p _ f refl)
cut-intrp p ._ (⊗L ._ f) refl | 2>L1 (gt q refl refl refl) = ⊗L (cut-intrp p _ f refl)
cut-intrp p ._(⊗L ._ f) refl | 2>R1 (gt q refl refl refl) = ⊗L (cut-intrp p _ f refl)
cut-intrp ._ U (⊗L  ._ f) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) = 
  cut⊗L≗1/\2  q q₁ q₂ (MIP.h (mip (q ++ (q₁ ◂ sub q₂ (η _ ⊛ η _))) U f refl)) (MIP.g (mip (q ++ (q₁ ◂ sub q₂ (η _ ⊛ η _))) U f refl))  
  ∘ ⊗L (cut-intrp _ U f refl) 
cut-intrp ._ U (⊗L ._ f) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 
  cut⊗L≗2/\1 q q₁ q₂ (MIP.h (mip (q ++ (sub q₁ (η _ ⊛ η _) ▸ q₂)) U f refl)) (MIP.g (mip (q ++ (sub q₁ (η _ ⊛ η _) ▸ q₂)) U f refl)) 
  ∘ ⊗L (cut-intrp _ U f refl)
cut-intrp ∙ ._ ax refl = refl         