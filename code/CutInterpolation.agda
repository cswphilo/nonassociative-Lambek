{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module CutInterpolation where

open import Relation.Binary.PropositionalEquality hiding ([_]; _≗_) 
open import Data.Product
open import Data.Empty
open import Fma
open import SeqCalc
open import Cut
open import Interpolation

sub∙ : (T : Tree) → sub ∙ T ≡ T
sub∙ ∙ = refl
sub∙ (η x) = refl
sub∙ (T ⊛ T₁) = refl
-- {-# REWRITE sub∙ #-}

-- ++∙ : ∀ {T} (p : Path T) → p ++ ∙ ≡ {! sub∙ T  !} 

cut-cong : ∀ {T U A C} (p : Path T)
  → (f : U ⊢ A) 
  → {g g' : sub p (η A) ⊢ C}
  → (eq : g ≗ g')
  → cut p f g ≗ cut p f g'

cut⇒R-cong : ∀ {T U W A B C} (p : Path T)
  → (f : η A ⊛ U ⊢ B) {g g' : W ⊢ C}
  → (eq : W ≡ sub p (η (A ⇒ B)))
  → (eq' : g ≗ g')
  → cut⇒R p f g eq ≗ cut⇒R p f g' eq

cut⇐R-cong : ∀ {T U W A B C} (p : Path T)
  → (f : U ⊛ η A ⊢ B) {g g' : W ⊢ C}
  → (eq : W ≡ sub p (η (B ⇐ A)))
  → (eq' : g ≗ g')
  → cut⇐R p f g eq ≗ cut⇐R p f g' eq

cut⊗R-cong : ∀ {T U V W A B C} (p : Path T)
  → (f : U ⊢ A) (f₁ : V ⊢ B)
  → {g g' : W ⊢ C}
  → (eq : W ≡ sub p (η (A ⊗ B)))
  → (eq' : g ≗ g')
  → cut⊗R p f f₁ g eq ≗ cut⊗R p f f₁ g' eq

cut-cong p ax eq = eq
cut-cong p (⇒R f) eq = cut⇒R-cong p f refl eq
cut-cong p (⇐R f) eq = cut⇐R-cong p f refl eq
cut-cong p (⇒L p₁ f f₁) eq = ⇒L refl (cut-cong p f₁ eq)
cut-cong p (⇐L p₁ f f₁) eq = ⇐L refl (cut-cong p f₁ eq)
cut-cong p (⊗R f f₁) eq = cut⊗R-cong p f f₁ refl eq
cut-cong p (⊗L p₁ f) eq = ⊗L (cut-cong p f eq)

cut⇒R-cong p f eq refl = refl
cut⇒R-cong p f eq (~ eq') = ~ (cut⇒R-cong p f eq eq')
cut⇒R-cong p f eq (eq' ∘ eq'') = {!   !}
cut⇒R-cong p f refl (⇒R eq') = ⇒R (cut⇒R-cong (_ ▸ p) f refl eq')
cut⇒R-cong p f refl (⇐R eq') = ⇐R (cut⇒R-cong (p ◂ _) f refl eq')
cut⇒R-cong p f eq (⇒L eq' eq'') = {!   !}
cut⇒R-cong p f eq (⇐L eq' eq'') = {!   !}
cut⇒R-cong p f eq (⊗R eq' eq'') = {!   !}
cut⇒R-cong p f eq (⊗L eq') = {!   !}
cut⇒R-cong p f eq ⇒L⇒R = {!   !}
cut⇒R-cong p f eq ⇐L⇒R = {!   !}
cut⇒R-cong p f eq ⊗L⇒R = {!   !}
cut⇒R-cong p f eq ⇒L⇐R = {!   !}
cut⇒R-cong p f eq ⇐L⇐R = {!   !}
cut⇒R-cong p f eq ⊗L⇐R = {!   !}
cut⇒R-cong p f eq ⇒L⊗R₁ = {!   !}
cut⇒R-cong p f eq ⇒L⊗R₂ = {!   !}
cut⇒R-cong p f eq ⇐L⊗R₁ = {!   !}
cut⇒R-cong p f eq ⇐L⊗R₂ = {!   !}
cut⇒R-cong p f eq ⊗L⊗R₁ = {!   !}
cut⇒R-cong p f eq ⊗L⊗R₂ = {!   !}
cut⇒R-cong p f eq ⊗L⊗L = {!   !}
cut⇒R-cong p f eq ⊗L⇒L₁ = {!   !}
cut⇒R-cong p f eq ⊗L⇒L₂1/\2 = {!   !}
cut⇒R-cong p f eq ⊗L⇒L₂2/\1 = {!   !}
cut⇒R-cong p f eq ⊗L⇐L₁ = {!   !}
cut⇒R-cong p f eq ⊗L⇐L₂1/\2 = {!   !}
cut⇒R-cong p f eq (⊗L⇐L₂2/\1 {p = q} {q₁} {q₂}) = {!   !}
-- with subeq _ _ (q ++ (sub q₁ (η (_ ⇐ _) ⊛ _) ▸ q₂)) p eq | subeq _ _ (q ++ (q₁ ◂ sub q₂ (η (_ ⊗ _)))) p eq 
-- ... | 1/\2 (disj q₃ q₄ q₅ eqT₁ eqT₂ eqp₁ eqp₂) | 2>L1 (gt q₆ refl eqU refl) = {! eqU  !}
-- ... | 1/\2 x | 2>R1 x₁ = {!   !}
-- ... | 1/\2 x | 1/\2 x₁ = {!   !}
-- ... | 1/\2 x | 2/\1 x₁ = {!   !}
-- ... | 2/\1 x | 2>L1 x₁ = {!   !}
-- ... | 2/\1 x | 2>R1 x₁ = {!   !}
-- ... | 2/\1 x | 1/\2 x₁ = {!   !}
-- ... | 2/\1 (disj q₃ q₄ q₅ eqT₁ eqT₂ eqp₁ eqp₂) | 2/\1 (disj q₆ q₇ q₈ eqT₃ eqT₄ eqp₃ eqp₄) = {!   !}
cut⇒R-cong p f eq ⇒L⇒L = {!   !}
cut⇒R-cong p f eq ⇒L⇒L₂1/\2 = {!   !}
cut⇒R-cong p f eq ⇒L⇒L₂2/\1 = {!   !}
cut⇒R-cong p f eq ⇒L⇐L = {!   !}
cut⇒R-cong p f eq ⇒L⇐L₂1/\2 = {!   !}
cut⇒R-cong p f eq ⇒L⇐L₂2/\1 = {!   !}
cut⇒R-cong p f eq ⇐L⇒L = {!   !}
cut⇒R-cong p f eq ⇐L⇒L₂1/\2 = {!   !}
cut⇒R-cong p f eq ⇐L⇒L₂2/\1 = {!   !}
cut⇒R-cong p f eq ⇐L⇐L = {!   !}
cut⇒R-cong p f eq ⇐L⇐L₂1/\2 = {!   !}
cut⇒R-cong p f eq ⇐L⇐L₂2/\1 = {!   !}


cut⇐R-cong p f eq eq' = {!   !}

cut⊗R-cong p f f₁ eq eq' = {! f  !}

cut⇒R≗ : ∀ {T} (p : Path T) {U : Tree} {A C D : Fma}
  →  (h : U ⊢ D) (g : η A ⊛ sub p (η D) ⊢ C)
  → cut p h (⇒R g) ≗ ⇒R (cut (η A ▸ p) h g)
cut⇒R≗ p  ax g = refl
cut⇒R≗ p (⇒R h) g = refl
cut⇒R≗ p (⇐R h) g = refl
cut⇒R≗ p (⇒L p' h h') g = ⇒L refl (cut⇒R≗ p h' g) ∘ ⇒L⇒R
cut⇒R≗ p (⇐L p' h h') g = ⇐L refl (cut⇒R≗ p h' g) ∘ ⇐L⇒R
cut⇒R≗ p (⊗R h h') g = refl
cut⇒R≗ p (⊗L p' h) g = ⊗L (cut⇒R≗ p  h g) ∘ ⊗L⇒R

cut⇐R≗ : ∀ {T} (p : Path T) {U : Tree} {A C D : Fma}
  →  (h : U ⊢ D) (g : sub p (η D) ⊛ η A ⊢ C)
  → cut p h (⇐R g) ≗ ⇐R (cut (p ◂ η A) h g)
cut⇐R≗ p ax g = refl
cut⇐R≗ p (⇒R h) g = refl
cut⇐R≗ p (⇐R h) g = refl
cut⇐R≗ p (⇒L p' h h') g = ⇒L refl (cut⇐R≗ p h' g) ∘ ⇒L⇐R
cut⇐R≗ p (⇐L p' h h') g = ⇐L refl (cut⇐R≗ p h' g) ∘ ⇐L⇐R
cut⇐R≗ p (⊗R h h') g = refl
cut⇐R≗ p (⊗L p' h) g = ⊗L (cut⇐R≗ p h g) ∘ ⊗L⇐R

cut⊗R≗₁ : ∀ {T} (p : Path T) {U V : Tree} {A B D : Fma}
  →  (h : U ⊢ D) (g : sub p (η D) ⊢ A) (g' : V ⊢ B)
  → cut (p ◂ V) h (⊗R g g') ≗ ⊗R (cut p h g) g'
cut⊗R≗₁ p ax g g' = refl
cut⊗R≗₁ p (⇒R h) g g' = refl
cut⊗R≗₁ p (⇐R h) g g' = refl
cut⊗R≗₁ p (⇒L p' h h') g g' = ⇒L refl (cut⊗R≗₁ p h' g g') ∘ ⇒L⊗R₁
cut⊗R≗₁ p (⇐L p' h h') g g' = ⇐L refl (cut⊗R≗₁ p h' g g') ∘ ⇐L⊗R₁
cut⊗R≗₁ p (⊗R h h') g g' = refl
cut⊗R≗₁ p (⊗L p' h) g g' = ⊗L (cut⊗R≗₁ p h g g') ∘ ⊗L⊗R₁

cut⊗R≗₂ : ∀ {T} (p : Path T) {U V : Tree} {A B D : Fma}
  →  (h : U ⊢ D) (g : V ⊢ A) (g' : sub p (η D) ⊢ B)
  → cut (V ▸ p) h (⊗R g g') ≗ ⊗R g (cut p h g')
cut⊗R≗₂ p ax g g' = refl
cut⊗R≗₂ p (⇒R h) g g' = refl
cut⊗R≗₂ p (⇐R h) g g' = refl
cut⊗R≗₂ p (⇒L p' h h') g g' = ⇒L refl (cut⊗R≗₂ p h' g g') ∘ ⇒L⊗R₂
cut⊗R≗₂ p (⇐L p' h h') g g' = ⇐L refl (cut⊗R≗₂ p h' g g') ∘ ⇐L⊗R₂
cut⊗R≗₂ p (⊗R h h') g g' = refl
cut⊗R≗₂ p (⊗L p' h) g g' = ⊗L (cut⊗R≗₂ p h g g') ∘ ⊗L⊗R₂

cut⊗L≗1/\2 : ∀ {T} (p : Path T) {U : Tree} {A B C D : Fma} 
  → {W₁ W₂ : Tree} (p₁ : Path W₁) (p₂ : Path W₂)
  → (h : U ⊢ D) (g : sub p (sub p₁ (η D) ⊛ (sub p₂ (η A ⊛ η B))) ⊢ C)
  → cut (p ++ (p₁ ◂ sub p₂ (η (A ⊗ B)))) h ((⊗L (p ++ (sub p₁ (η D) ▸ p₂)) g)) 
    ≗ 
    ⊗L (p ++ (sub p₁ U ▸ p₂)) (cut (p ++ (p₁ ◂ (sub p₂ (η A ⊛ η B)))) h g)
cut⊗L≗1/\2 p p₁ p₂ ax g = refl
cut⊗L≗1/\2 p p₁ p₂ (⇒R h) g = {!   !}
cut⊗L≗1/\2 p p₁ p₂ (⇐R h) g = {!   !}
cut⊗L≗1/\2 p p₁ p₂ (⇒L p₃ h h₁) g = {!   !}
cut⊗L≗1/\2 p p₁ p₂ (⇐L p₃ h h₁) g = {!   !}
cut⊗L≗1/\2 p p₁ p₂ (⊗R h h₁) g = {!   !}
cut⊗L≗1/\2 p p₁ p₂ (⊗L p₃ h) g = {!   !}

cut⊗L≗2/\1 : ∀ {T} (p : Path T) {U : Tree} {A B C D : Fma} 
  → {W₁ W₂ : Tree} (p₁ : Path W₁) (p₂ : Path W₂)
  → (h : U ⊢ D) (g : sub p ((sub p₁ (η A ⊛ η B)) ⊛ sub p₂ (η D)) ⊢ C)
  → cut (p ++ (sub p₁ (η (A ⊗ B)) ▸ p₂)) h ((⊗L (p ++ (p₁ ◂ sub p₂ (η D))) g)) 
    ≗ 
    ⊗L (p ++ (p₁ ◂ sub p₂ U)) (cut (p ++ (sub p₁ (η A ⊛ η B) ▸ p₂)) h g)
cut⊗L≗2/\1 p p₁ p₂ h g = {!   !}

cut-intrp : ∀ {T} (p : Path T) U {V C}
  → (f : V ⊢ C) (eq : V ≡ sub p U) 
  →  cut p (MIP.h (mip p U f eq)) (MIP.g (mip p U f eq)) ≗ subst-cxt eq f
  
cut-intrp p U (⇒R f) refl = 
  cut⇒R≗ p (MIP.h (mip (_ ▸ p) U f refl)) (MIP.g (mip (_ ▸ p) U f refl)) 
  ∘ ⇒R (cut-intrp (_ ▸ p) U f refl)
  
cut-intrp p U (⇐R f) refl = 
  cut⇐R≗ p (MIP.h (mip (p ◂ _) U f refl)) (MIP.g (mip (p ◂ _) U f refl)) 
  ∘ ⇐R (cut-intrp (p ◂ _) U f refl)

cut-intrp p U (⇒L p₁ f f₁) eq = {!   !}
cut-intrp p U (⇐L p₁ f f₁) eq = {!   !}

cut-intrp ∙ ._ (⊗R {T} {U} f f₁) refl = 
  cut-cong (∙ ◂ U) (MIP.h (mip ∙ T f refl))  (cut⊗R≗₂ ∙ (MIP.h (mip ∙ U f₁ refl)) (MIP.g (mip ∙ T f refl)) (MIP.g (mip ∙ U f₁ refl))) 
  ∘ (cut⊗R≗₁ ∙ (MIP.h (mip ∙ T f refl)) (MIP.g (mip ∙ T f refl)) (cut ∙ (MIP.h (mip ∙ U f₁ refl)) (MIP.g (mip ∙ U f₁ refl))) 
  ∘ ⊗R (cut-intrp ∙ _ f refl) (cut-intrp ∙ _ f₁ refl))
cut-intrp (p ◂ U₁) U (⊗R f f₁) refl = 
  cut⊗R≗₁ p (MIP.h (mip p U f refl)) (MIP.g (mip p U f refl)) f₁ 
  ∘ ⊗R (cut-intrp p _ f refl) refl
cut-intrp (T ▸ p) U (⊗R f f₁) refl = 
  cut⊗R≗₂ p (MIP.h (mip p U f₁ refl)) f (MIP.g (mip p U f₁ refl)) 
  ∘ ⊗R refl (cut-intrp p _ f₁ refl)

cut-intrp p U (⊗L p₁ f) eq with subeq _ _ p p₁ (sym eq)
cut-intrp p .(η (A ⊗ B)) (⊗L {A = A} {B} .(subst Path refl p) f) refl | 1≡2 (same refl refl refl) =   
  ≡to≗ {! cong (λ x → ⊗L x (cut p (MIP.h (mip p (η A ⊛ η B) f refl)) (MIP.g (mip p (η A ⊛ η B) f refl)))) refl  !} ∘ ⊗L (cut-intrp p _ f refl)
cut-intrp p ._ (⊗L ._ f) refl | 2>L1 (gt q refl refl refl) = ⊗L (cut-intrp p _ f refl)
cut-intrp p ._(⊗L ._ f) refl | 2>R1 (gt q refl refl refl) = ⊗L (cut-intrp p _ f refl)
cut-intrp ._ U (⊗L ._ f) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) = 
  cut⊗L≗1/\2  q q₁ q₂ (MIP.h (mip (q ++ (q₁ ◂ sub q₂ (η _ ⊛ η _))) U f refl)) (MIP.g (mip (q ++ (q₁ ◂ sub q₂ (η _ ⊛ η _))) U f refl))  
  ∘ ⊗L (cut-intrp _ U f refl)
cut-intrp ._ U (⊗L ._ f) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 
  cut⊗L≗2/\1 q q₁ q₂ (MIP.h (mip (q ++ (sub q₁ (η _ ⊛ η _) ▸ q₂)) U f refl)) (MIP.g (mip (q ++ (sub q₁ (η _ ⊛ η _) ▸ q₂)) U f refl)) 
  ∘ ⊗L (cut-intrp _ U f refl)
cut-intrp ∙ ._ ax refl = refl   