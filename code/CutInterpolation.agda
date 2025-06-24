{-# OPTIONS --rewriting  #-}

module CutInterpolation where

open import Relation.Binary.PropositionalEquality hiding ([_]; _≗_) 
open import Data.Product
open import Data.Empty
open import Fma
open import SeqCalc
open import Cut
open import Interpolation
open import SubEqProperties
open import CutEqualities
open import CutCirceqEquations
open import CutCongruence

{-
Proof-relevant interpolation for NL, i.e.
Maehara interpolation procedure is a right inverse of Cut
-}

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
  →  cut p (MIP.h (mip p U f eq)) (MIP.g (mip p U f eq)) refl ≗ subst-cxt eq f
cut-intrp p U (⇒R f) refl = ⇒R (cut-intrp (_ ▸ p) U f refl)
cut-intrp p U (⇐R f) refl = ⇐R (cut-intrp (p ◂ _) U f refl)
cut-intrp p U (⇒L {U = U₁} {A} {B} p₁ f f₁) eq with subeq U (U₁ ⊛ η (A ⇒ B)) p p₁ (sym eq)
cut-intrp p ._ (⇒L {U = U₁} {A} {B} ._ f f₁) refl | 1≡2 (same refl refl refl) = 
  cut⇒L≗ p ∙ (MIP.h (mip p (η B) f₁ refl)) (MIP.g (mip p (η B) f₁ refl)) refl 
  ∘ ⇒L refl (cut-intrp p _ f₁ refl)
cut-intrp p ._ (⇒L {U = U₁} {A} {B} ._ f f₁) refl | 2>L1 (gt {W₂ = W₂} q refl refl refl) = 
  cut⇒L≗ p (q ◂ _) (MIP.h (mip p (sub q (η B) ⊛ W₂) f₁ refl)) (MIP.g (mip p (sub q (η B) ⊛ W₂) f₁ refl)) refl 
  ∘ ⇒L refl (cut-intrp p _ f₁ refl)
cut-intrp p ._ (⇒L {U = U₁} {A} {B} ._ f f₁) refl | 2>R1 (gt {W₁} q refl refl refl) = 
  cut⇒L≗ p (_ ▸ q) (MIP.h (mip p (W₁ ⊛ sub q (η B)) f₁ refl)) (MIP.g (mip p (W₁ ⊛ sub q (η B)) f₁ refl)) refl 
  ∘ ⇒L refl (cut-intrp p _ f₁ refl)
cut-intrp p U (⇒L {U = U₁} {A} {B} p₁ f f₁) refl | 1>L2 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η (mip q U f refl .MIP.D)) q = ⇒L (cut-intrp q U f refl) refl
cut-intrp ._ ._ (⇒L {U = U₁} {A} {B} p₁ f f₁) refl | 1>R2 (gt ∙ refl refl refl)
  rewrite subeq-2>R1 p₁ U₁ (η (mip ∙ U₁ f refl .MIP.D ⇒ mip p₁ (η B) f₁ refl .MIP.D)) ∙ = 
            cut-cong2 (p₁ ++ (∙ ◂ η (A ⇒ B))) (MIP.h (mip ∙ U₁ f refl)) refl (cut⇒L≗ p₁ ∙ (MIP.h (mip p₁ (η B) f₁ refl)) (MIP.g (mip p₁ (η B) f₁ refl)) refl) 
            ∘ (≡to≗ (cut⇒L-2>L1 p₁ (MIP.h (mip ∙ U₁ f refl)) (MIP.g (mip ∙ U₁ f refl)) (MIP.h (mip p₁ (η B) f₁ refl)) (MIP.g (mip p₁ (η B) f₁ refl))) 
            ∘ ⇒L (cut-intrp ∙ U₁ f refl) (cut-intrp p₁ (η B) f₁ refl))
cut-intrp p U (⇒L {U = U₁} {A} {B} p₁ f f₁) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U₁ ⊛ η (A ⇒ B)) (η (mip (q ++ (q₁ ◂ sub q₂ (η B))) U f₁ refl .MIP.D)) q₁ q₂ = 
    ⇒L refl (cut-intrp (q ++ (q₁ ◂ sub q₂ (η B))) U f₁ refl)
cut-intrp p U (⇒L {U = U₁} {A} {B} p₁ f f₁) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U₁ ⊛ η (A ⇒ B)) (η (mip (q ++ (sub q₁ (η B) ▸ q₂)) U f₁ refl .MIP.D)) q₁ q₂ = 
    ⇒L refl (cut-intrp (q ++ (sub q₁ (η B) ▸ q₂)) U f₁ refl)
cut-intrp p U (⇐L {U = U₁} {A} {B} p₁ f f₁) eq with subeq U (η (B ⇐ A) ⊛ U₁) p p₁ (sym eq)
cut-intrp p ._ (⇐L {U = U₁} {A} {B} ._ f f₁) refl | 1≡2 (same refl refl refl) = 
  cut⇐L≗ p ∙ (MIP.h (mip p (η B) f₁ refl)) (MIP.g (mip p (η B) f₁ refl)) refl 
  ∘ ⇐L refl (cut-intrp p _ f₁ refl)
cut-intrp p ._ (⇐L {U = U₁} {A} {B} ._ f f₁) refl | 2>L1 (gt {W₂ = W₂} q refl refl refl) = 
  cut⇐L≗ p (q ◂ _) (MIP.h (mip p (sub q (η B) ⊛ W₂) f₁ refl)) (MIP.g (mip p (sub q (η B) ⊛ W₂) f₁ refl)) refl 
  ∘ ⇐L refl (cut-intrp p _ f₁ refl)
cut-intrp p ._ (⇐L {U = U₁} {A} {B} ._ f f₁) refl | 2>R1 (gt {W₁} q refl refl refl) = 
  cut⇐L≗ p (_ ▸ q) (MIP.h (mip p (W₁ ⊛ sub q (η B)) f₁ refl)) (MIP.g (mip p (W₁ ⊛ sub q (η B)) f₁ refl)) refl 
  ∘ ⇐L refl (cut-intrp p _ f₁ refl)
cut-intrp .(p₁ ++ (∙ ◂ U₁)) .(η (B ⇐ A)) (⇐L {U = U₁} {A} {B} p₁ f f₁) refl | 1>L2 (gt ∙ refl refl refl)
  rewrite subeq-2>L1 p₁ U₁ (η (MIP.D (mip p₁ (η B) f₁ refl) ⇐ MIP.D (mip ∙ U₁ f refl))) ∙ = 
    cut-cong2 (p₁ ++ (η (B ⇐ A) ▸ ∙)) (MIP.h (mip ∙ U₁ f refl)) refl (cut⇐L≗ p₁ ∙ (MIP.h (mip p₁ (η B) f₁ refl)) (MIP.g (mip p₁ (η B) f₁ refl)) refl) 
    ∘ (≡to≗ (cut⇐L-2>R1 p₁ (MIP.h (mip ∙ U₁ f refl)) (MIP.g (mip ∙ U₁ f refl)) (MIP.h (mip p₁ (η B) f₁ refl)) (MIP.g (mip p₁ (η B) f₁ refl))) 
    ∘ ⇐L (cut-intrp ∙ U₁ f refl) (cut-intrp p₁ (η B) f₁ refl))
cut-intrp p U (⇐L {U = U₁} {A} {B} p₁ f f₁) refl | 1>R2 (gt q refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η (mip q U f refl .MIP.D)) q = ⇐L (cut-intrp q U f refl) refl
cut-intrp p U (⇐L {U = U₁} {A} {B} p₁ f f₁) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U₁) (η (mip (q ++ (q₁ ◂ sub q₂ (η B))) U f₁ refl .MIP.D)) q₁ q₂ = 
    ⇐L refl (cut-intrp (q ++ (q₁ ◂ sub q₂ (η B))) U f₁ refl)
cut-intrp p U (⇐L {U = U₁} {A} {B} p₁ f f₁) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U₁) (η (mip (q ++ (sub q₁ (η B) ▸ q₂)) U f₁ refl .MIP.D)) q₁ q₂ = 
    ⇐L refl (cut-intrp (q ++ (sub q₁ (η B) ▸ q₂)) U f₁ refl)
cut-intrp ∙ U (⊗R f f₁) refl = ⊗R (cut-intrp ∙ _ f refl) (cut-intrp ∙ _ f₁ refl)
cut-intrp (p ◂ U₁) U (⊗R f f₁) refl = ⊗R (cut-intrp p U f refl) refl
cut-intrp (T ▸ p) U (⊗R f f₁) refl = ⊗R refl (cut-intrp p U f₁ refl)
cut-intrp p U (⊗L {A = A} {B} p₁ f) eq with subeq U (η (A ⊗ B)) p p₁ (sym eq)
cut-intrp p ._ (⊗L {A = A} {B} ._ f) refl | 1≡2 (same refl refl refl) = 
  cut⊗L≗ p ∙ (MIP.h (mip p (η A ⊛ η B) f refl)) (MIP.g (mip p (η A ⊛ η B) f refl)) refl 
  ∘ ⊗L (cut-intrp p _ f refl)
cut-intrp p ._ (⊗L {A = A} {B} ._ f) refl | 2>L1 (gt q refl refl refl) = 
  cut⊗L≗ p (q ◂ _) (MIP.h (mip p (sub q (η A ⊛ η B) ⊛ _) f refl)) (MIP.g (mip p (sub q (η A ⊛ η B) ⊛ _) f refl)) refl 
  ∘ ⊗L (cut-intrp p _ f refl)
cut-intrp p ._ (⊗L {A = A} {B} ._ f) refl | 2>R1 (gt q refl refl refl) = 
  cut⊗L≗ p (_ ▸ q) (MIP.h (mip p (_ ⊛ sub q (η A ⊛ η B)) f refl)) (MIP.g (mip p (_ ⊛ sub q (η A ⊛ η B)) f refl)) refl 
  ∘ ⊗L (cut-intrp p _ f refl)
cut-intrp ._ U (⊗L {A = A} {B} ._ f) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η (MIP.D (mip (q ++ (q₁ ◂ sub q₂ (η A ⊛ η B))) U f refl))) q₁ q₂ = 
    ⊗L (cut-intrp (q ++ (q₁ ◂ sub q₂ (η A ⊛ η B))) U f refl)
cut-intrp ._ U (⊗L {A = A} {B} ._ f) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η (MIP.D (mip (q ++ (sub q₁ (η A ⊛ η B) ▸ q₂)) U f refl))) q₁ q₂ = 
    ⊗L (cut-intrp (q ++ (sub q₁ (η A ⊛ η B) ▸ q₂)) U f refl)
cut-intrp ∙ ._ ax refl = refl     
