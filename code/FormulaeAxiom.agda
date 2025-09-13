{-# OPTIONS --rewriting #-}

module FormulaeAxiom where

open import Fma
open import SeqCalc
open import Cut
open import CutCirceqEquations
open import CutCongruence
open import CutEqualities
  
axA : {A : Fma} → η A ⊢ A
axA {at x} = ax
axA {A ⇒ B} = ⇒R (⇒L ∙ axA axA)
axA {B ⇐ A} = ⇐R (⇐L ∙ axA axA)
axA {A ⊗ B} = ⊗L ∙ (⊗R axA axA)

-- These are duplicated functions as the ones in CutInterpolation.
-- This is utilize the REWRITEs locally in specific files 
-- instead of the whole project. 

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

axA-cut-left-unit : ∀ {T U A C}
  → (p : Path T)
  → (f : U ⊢ C)
  → (eq : U ≡ sub p (η A))
  → cut p axA f eq ≗ subst-cxt eq f

axA-cut-right-unit : ∀ {T A}
  → (f : T ⊢ A)
  → cut ∙ f axA refl ≗ f

axA-cut-left-unit p (⇒R f) refl = ⇒R (axA-cut-left-unit (_ ▸ p) f refl)
axA-cut-left-unit p (⇐R f) refl = ⇐R (axA-cut-left-unit (p ◂ _) f refl)
axA-cut-left-unit {A = A'} p (⇒L {U = U} {A} {B} p₁ f g) eq with subeq (U ⊛ η (A ⇒ B)) (η A') p₁ p eq
axA-cut-left-unit p (⇒L p₁ f g) refl | 2>L1 (gt q refl refl refl) = 
  ⇒L (axA-cut-left-unit q f refl) refl
axA-cut-left-unit p (⇒L {A = A} {B} p₁ f g) refl | 2>R1 (gt ∙ refl refl refl) = 
  cut-cong2 (p₁ ++ (∙ ◂ _)) f refl (cut⇒L≗ p₁ ∙ axA g refl) 
  ∘ (≡to≗ (cut⇒L-2>L1 p₁ f axA axA g) 
  ∘ ⇒L (axA-cut-right-unit f) (axA-cut-left-unit p₁ g refl))   
axA-cut-left-unit {A = A'} p (⇒L {U = U} {A} {B} p₁ f g) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⇒L refl (axA-cut-left-unit _ g refl)
axA-cut-left-unit {A = A'} p (⇒L {U = U} {A} {B} p₁ f g) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⇒L refl (axA-cut-left-unit _ g refl)
axA-cut-left-unit {A = A'} p (⇐L {U = U} {A} {B} p₁ f g) eq with subeq (η (B ⇐ A) ⊛ U) (η A') p₁ p eq
axA-cut-left-unit p (⇐L {A = A} {B} p₁ f g) refl | 2>L1 (gt ∙ refl refl refl) = 
  cut-cong2 (p₁ ++ (_ ▸ ∙)) f refl (cut⇐L≗ p₁ ∙ axA g refl) 
  ∘ (≡to≗ (cut⇐L-2>R1 p₁ f axA axA g) 
  ∘ ⇐L (axA-cut-right-unit f) (axA-cut-left-unit p₁ g refl))   
axA-cut-left-unit p (⇐L p₁ f g) refl | 2>R1 (gt q refl refl refl) = 
  ⇐L (axA-cut-left-unit q f refl) refl
axA-cut-left-unit {A = A'} p (⇐L {U = U} {A} {B} p₁ f g) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⇐L refl (axA-cut-left-unit _ g refl)
axA-cut-left-unit {A = A'} p (⇐L {U = U} {A} {B} p₁ f g) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⇐L refl (axA-cut-left-unit _ g refl)
axA-cut-left-unit (p ◂ U) (⊗R f g) refl = ⊗R (axA-cut-left-unit p f refl) refl
axA-cut-left-unit (T ▸ p) (⊗R f g) refl = ⊗R refl (axA-cut-left-unit p g refl)
axA-cut-left-unit {A = A'} p (⊗L {A = A} {B} p₁ f) eq with subeq (η (A ⊗ B)) (η A') p₁ p eq
axA-cut-left-unit {A = A'} p (⊗L {A = A} {B} p₁ f) refl | 1≡2 (same refl refl refl) = 
  ⊗L (cut-cong2 (p ++ (∙ ◂ _)) axA refl (axA-cut-left-unit (p ++ (_ ▸ ∙)) f refl) 
  ∘ axA-cut-left-unit (p ++ (∙ ◂ _)) f refl)
axA-cut-left-unit {A = A'} p (⊗L {A = A} {B} p₁ f) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⊗L (axA-cut-left-unit _ f refl)
axA-cut-left-unit {A = A'} p (⊗L {A = A} {B} p₁ f) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⊗L (axA-cut-left-unit _ f refl)
axA-cut-left-unit ∙ ax refl = refl

axA-cut-right-unit ax = refl
axA-cut-right-unit (⇒R {B = B} f) = 
  ⇒R (axA-cut-left-unit (∙ ◂ _) (cut ∙ f axA refl) refl ∘ axA-cut-right-unit f)
axA-cut-right-unit (⇐R {B = B} f) = 
  ⇐R (axA-cut-left-unit (_ ▸ ∙) (cut ∙ f axA refl) refl ∘ axA-cut-right-unit f)
axA-cut-right-unit {A = A} (⇒L p f g) = 
  cut⇒L≗ ∙ p g axA refl ∘ ⇒L refl (axA-cut-right-unit g)
axA-cut-right-unit {A = A} (⇐L p f g) = 
  cut⇐L≗ ∙ p g axA refl ∘ ⇐L refl (axA-cut-right-unit g)
axA-cut-right-unit (⊗R f g) = ⊗R (axA-cut-right-unit f) (axA-cut-right-unit g)
axA-cut-right-unit {A = A} (⊗L p f) = 
  cut⊗L≗ ∙ p f axA refl ∘ ⊗L (axA-cut-right-unit f)

-- ====================================
-- open import CutAssociativities
-- open import SubEqProperties

-- ⇐R-1 : ∀ {T A B} 
--   → (f : T ⊢ B ⇐ A)
--   → T ⊛ η A ⊢ B
-- ⇐R-1 (⇐R f) = f
-- ⇐R-1 (⇒L p f g) = ⇒L (p ◂ _) f (⇐R-1 g)
-- ⇐R-1 (⇐L p f g) = ⇐L (p ◂ _) f (⇐R-1 g)
-- ⇐R-1 (⊗L p f) = ⊗L (p ◂ _) (⇐R-1 f)

-- ⇐R-1≗ : ∀ {T A B}
--   → {f g : T ⊢ B ⇐ A}
--   → (eq : f ≗ g)
--   → ⇐R-1 f ≗ ⇐R-1 g
-- ⇐R-1≗ refl = refl
-- ⇐R-1≗ (~ eq) = ~ ⇐R-1≗ eq
-- ⇐R-1≗ (eq ∘ eq₁) = ⇐R-1≗ eq ∘ ⇐R-1≗ eq₁
-- ⇐R-1≗ (⇐R eq) = eq
-- ⇐R-1≗ (⇒L eq eq₁) = ⇒L eq (⇐R-1≗ eq₁)
-- ⇐R-1≗ (⇐L eq eq₁) = ⇐L eq (⇐R-1≗ eq₁)
-- ⇐R-1≗ (⊗L eq) = ⊗L (⇐R-1≗ eq)
-- ⇐R-1≗ ⇒L⇐R = refl
-- ⇐R-1≗ ⇐L⇐R = refl
-- ⇐R-1≗ ⊗L⇐R = refl
-- ⇐R-1≗ (⊗L⊗L {p = p}) = ⊗L⊗L {p = p ◂ _}
-- ⇐R-1≗ ⊗L⇒L₁ = ⊗L⇒L₁
-- ⇐R-1≗ (⊗L⇒L₂1/\2 {p = p}) = ⊗L⇒L₂1/\2 {p = p ◂ _}
-- ⇐R-1≗ (⊗L⇒L₂2/\1 {p = p}) = ⊗L⇒L₂2/\1 {p = p ◂ _}
-- ⇐R-1≗ ⊗L⇐L₁ = ⊗L⇐L₁
-- ⇐R-1≗ (⊗L⇐L₂1/\2 {p = p}) = ⊗L⇐L₂1/\2 {p = p ◂ _}
-- ⇐R-1≗ (⊗L⇐L₂2/\1 {p = p}) = ⊗L⇐L₂2/\1 {p = p ◂ _}
-- ⇐R-1≗ ⇒L⇒L = ⇒L⇒L
-- ⇐R-1≗ (⇒L⇒L₂ {p = p}) = ⇒L⇒L₂ {p = p ◂ _}
-- ⇐R-1≗ ⇒L⇐L = ⇒L⇐L
-- ⇐R-1≗ (⇒L⇐L₂ {p = p}) = ⇒L⇐L₂ {p = p ◂ _}
-- ⇐R-1≗ ⇐L⇒L = ⇐L⇒L
-- ⇐R-1≗ (⇐L⇒L₂ {p = p}) = ⇐L⇒L₂ {p = p ◂ _}
-- ⇐R-1≗ ⇐L⇐L = ⇐L⇐L
-- ⇐R-1≗ (⇐L⇐L₂ {p = p}) = ⇐L⇐L₂ {p = p ◂ _}

-- ⇒R-1 : ∀ {T A B} 
--   → (f : T ⊢ A ⇒ B)
--   → η A ⊛ T ⊢ B
-- ⇒R-1 (⇒R f) = f
-- ⇒R-1 (⇒L p f g) = ⇒L (_ ▸ p) f (⇒R-1 g)
-- ⇒R-1 (⇐L p f g) = ⇐L (_ ▸ p) f (⇒R-1 g)
-- ⇒R-1 (⊗L p f) = ⊗L (_ ▸ p) (⇒R-1 f)

-- ⇒R-1≗ : ∀ {T A B}
--   → {f g : T ⊢ A ⇒ B}
--   → (eq : f ≗ g)
--   → ⇒R-1 f ≗ ⇒R-1 g
-- ⇒R-1≗ refl = refl
-- ⇒R-1≗ (~ eq) = ~ ⇒R-1≗ eq
-- ⇒R-1≗ (eq ∘ eq₁) = ⇒R-1≗ eq ∘ ⇒R-1≗ eq₁
-- ⇒R-1≗ (⇒R eq) = eq
-- ⇒R-1≗ (⇒L eq eq₁) = ⇒L eq (⇒R-1≗ eq₁)
-- ⇒R-1≗ (⇐L eq eq₁) = ⇐L eq (⇒R-1≗ eq₁)
-- ⇒R-1≗ (⊗L eq) = ⊗L (⇒R-1≗ eq)
-- ⇒R-1≗ ⇒L⇒R = refl
-- ⇒R-1≗ ⇐L⇒R = refl
-- ⇒R-1≗ ⊗L⇒R = refl
-- ⇒R-1≗ (⊗L⊗L {p = p}) = ⊗L⊗L {p = _ ▸ p}
-- ⇒R-1≗ ⊗L⇒L₁ = ⊗L⇒L₁
-- ⇒R-1≗ (⊗L⇒L₂1/\2 {p = p}) = ⊗L⇒L₂1/\2 {p = _ ▸ p}
-- ⇒R-1≗ (⊗L⇒L₂2/\1 {p = p}) = ⊗L⇒L₂2/\1 {p = _ ▸ p}
-- ⇒R-1≗ ⊗L⇐L₁ = ⊗L⇐L₁
-- ⇒R-1≗ (⊗L⇐L₂1/\2 {p = p}) = ⊗L⇐L₂1/\2 {p = _ ▸ p}
-- ⇒R-1≗ (⊗L⇐L₂2/\1 {p = p}) = ⊗L⇐L₂2/\1 {p = _ ▸ p}
-- ⇒R-1≗ ⇒L⇒L = ⇒L⇒L
-- ⇒R-1≗ (⇒L⇒L₂ {p = p}) = ⇒L⇒L₂ {p = _ ▸ p}
-- ⇒R-1≗ ⇒L⇐L = ⇒L⇐L
-- ⇒R-1≗ (⇒L⇐L₂ {p = p}) = ⇒L⇐L₂ {p = _ ▸ p}
-- ⇒R-1≗ ⇐L⇒L = ⇐L⇒L
-- ⇒R-1≗ (⇐L⇒L₂ {p = p}) = ⇐L⇒L₂ {p = _ ▸ p}
-- ⇒R-1≗ ⇐L⇐L = ⇐L⇐L
-- ⇒R-1≗ (⇐L⇐L₂ {p = p}) = ⇐L⇐L₂ {p = _ ▸ p}


-- ⇒R⇒R-1 : ∀ {T A B} 
--   → (f : T ⊢ A ⇒ B)
--   → ⇒R (⇒R-1 f) ≗ f
-- ⇒R⇒R-1 (⇒R f) = refl
-- ⇒R⇒R-1 (⇒L p f g) = (~ ⇒L⇒R) ∘ ⇒L refl (⇒R⇒R-1 g)
-- ⇒R⇒R-1 (⇐L p f g) = (~ ⇐L⇒R) ∘ ⇐L refl (⇒R⇒R-1 g)
-- ⇒R⇒R-1 (⊗L p f) = (~ ⊗L⇒R) ∘ ⊗L (⇒R⇒R-1 f)

-- ⇐R⇐R-1 : ∀ {T A B} 
--   → (f : T ⊢ B ⇐ A)
--   → ⇐R (⇐R-1 f) ≗ f
-- ⇐R⇐R-1 (⇐R f) = refl
-- ⇐R⇐R-1 (⇒L p f g) = (~ ⇒L⇐R) ∘ ⇒L refl (⇐R⇐R-1 g)
-- ⇐R⇐R-1 (⇐L p f g) = (~ ⇐L⇐R) ∘ ⇐L refl (⇐R⇐R-1 g)
-- ⇐R⇐R-1 (⊗L p f) = (~ ⊗L⇐R) ∘ ⊗L (⇐R⇐R-1 f)

-- ⊗L-1 : ∀ {T U A B C}
--   → (p : Path T)
--   → (f : U ⊢ C)
--   → (eq : U ≡ sub p (η (A ⊗ B)))
--   → sub p (η A ⊛ η B) ⊢ C
-- ⊗L-1 p (⇒R f) refl = ⇒R (⊗L-1 (_ ▸ p) f refl)
-- ⊗L-1 p (⇐R f) refl = ⇐R (⊗L-1 (p ◂ _) f refl)
-- ⊗L-1 p (⇒L p₁ f g) eq with subeq _ _ p₁ p eq
-- ⊗L-1 p (⇒L p₁ f g) refl | 2>L1 (gt q refl refl refl) = ⇒L p₁ (⊗L-1 q f refl) g
-- ... | 2>R1 (gt ∙ eqT () eqp)
-- ⊗L-1 p (⇒L p₁ f g) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⇒L (q ++ (q₁ ◂ _)) f (⊗L-1 (q ++ (_ ▸ q₂)) g refl)
-- ⊗L-1 p (⇒L p₁ f g) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⇒L (q ++ (_ ▸ q₂)) f (⊗L-1 (q ++ (q₁ ◂ _)) g refl)
-- ⊗L-1 p (⇐L p₁ f g) eq with subeq _ _ p₁ p eq
-- ... | 2>L1 (gt ∙ eqT () eqp)
-- ⊗L-1 p (⇐L p₁ f g) refl | 2>R1 (gt q refl refl refl) = ⇐L p₁ (⊗L-1 q f refl) g
-- ⊗L-1 p (⇐L p₁ f g) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⇐L (q ++ (q₁ ◂ _)) f (⊗L-1 (q ++ (_ ▸ q₂)) g refl)
-- ⊗L-1 p (⇐L p₁ f g) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⇐L (q ++ (_ ▸ q₂)) f (⊗L-1 (q ++ (q₁ ◂ _)) g refl)
-- ⊗L-1 (p ◂ U) (⊗R f g) refl = ⊗R (⊗L-1 p f refl) g
-- ⊗L-1 (T ▸ p) (⊗R f g) refl = ⊗R f (⊗L-1 p g refl)
-- ⊗L-1 p (⊗L p₁ f) eq with subeq _ _ p₁ p eq
-- ⊗L-1 p (⊗L p₁ f) refl | 1≡2 (same refl refl refl) = f
-- ⊗L-1 p (⊗L p₁ f) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) = ⊗L (q ++ (q₁ ◂ _)) (⊗L-1 (q ++ (_ ▸ q₂)) f refl)
-- ⊗L-1 p (⊗L p₁ f) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) = ⊗L (q ++ (_ ▸ q₂)) (⊗L-1 (q ++ (q₁ ◂ _)) f refl)
-- ⊗L-1 ∙ ax ()

-- ⊗L-1≗ : ∀ {T U A B C}
--   → (p : Path T)
--   → {f g : U ⊢ C}
--   → (eq : U ≡ sub p (η (A ⊗ B)))
--   → (eq' : f ≗ g)
--   → ⊗L-1 p f eq ≗ ⊗L-1 p g eq
-- ⊗L-1≗ p eq refl = refl
-- ⊗L-1≗ p eq (~ eq') = ~ ⊗L-1≗ p eq eq'
-- ⊗L-1≗ p eq (eq' ∘ eq'') = ⊗L-1≗ p eq eq' ∘ ⊗L-1≗ p eq eq''
-- ⊗L-1≗ p refl (⇒R eq') = ⇒R (⊗L-1≗ (_ ▸ p) refl eq')
-- ⊗L-1≗ p refl (⇐R eq') = ⇐R (⊗L-1≗ (p ◂ _) refl eq')
-- ⊗L-1≗ p eq (⇒L eq' eq'') = {!   !}
-- ⊗L-1≗ p eq (⇐L eq' eq'') = {!   !}
-- ⊗L-1≗ (p ◂ U) refl (⊗R eq' eq'') = ⊗R (⊗L-1≗ p refl eq') eq''
-- ⊗L-1≗ (T ▸ p) refl (⊗R eq' eq'') = ⊗R eq' (⊗L-1≗ p refl eq'')
-- ⊗L-1≗ p eq (⊗L eq') = {!   !}
-- ⊗L-1≗ p eq ⇒L⇒R = {!   !}
-- ⊗L-1≗ p eq ⇐L⇒R = {!   !}
-- ⊗L-1≗ p eq ⊗L⇒R = {!   !}
-- ⊗L-1≗ p eq ⇒L⇐R = {!   !}
-- ⊗L-1≗ p eq ⇐L⇐R = {!   !}
-- ⊗L-1≗ p eq ⊗L⇐R = {!   !}
-- ⊗L-1≗ p eq ⇒L⊗R₁ = {!   !}
-- ⊗L-1≗ p eq ⇒L⊗R₂ = {!   !}
-- ⊗L-1≗ p eq ⇐L⊗R₁ = {!   !}
-- ⊗L-1≗ p eq ⇐L⊗R₂ = {!   !}
-- ⊗L-1≗ p eq ⊗L⊗R₁ = {!   !}
-- ⊗L-1≗ p eq ⊗L⊗R₂ = {!   !}
-- ⊗L-1≗ p eq ⊗L⊗L = {!   !}
-- ⊗L-1≗ p eq ⊗L⇒L₁ = {!   !}
-- ⊗L-1≗ p eq ⊗L⇒L₂1/\2 = {!   !}
-- ⊗L-1≗ p eq ⊗L⇒L₂2/\1 = {!   !}
-- ⊗L-1≗ p eq ⊗L⇐L₁ = {!   !}
-- ⊗L-1≗ p eq ⊗L⇐L₂1/\2 = {!   !}
-- ⊗L-1≗ p eq ⊗L⇐L₂2/\1 = {!   !}
-- ⊗L-1≗ p eq ⇒L⇒L = {!   !}
-- ⊗L-1≗ p eq ⇒L⇒L₂ = {!   !}
-- ⊗L-1≗ p eq ⇒L⇐L = {!   !}
-- ⊗L-1≗ p eq ⇒L⇐L₂ = {!   !}
-- ⊗L-1≗ p eq ⇐L⇒L = {!   !}
-- ⊗L-1≗ p eq ⇐L⇒L₂ = {!   !}
-- ⊗L-1≗ p eq ⇐L⇐L = {!   !}
-- ⊗L-1≗ p eq ⇐L⇐L₂ = {!   !}

-- ⊗L-1-cut-A : ∀ {T U A B C A'}
--   → (p : Path T)
--   → (f : η A' ⊢ A) (g : U ⊢ C)
--   → (eq : U ≡ sub p (η (A ⊗ B)))
--   → cut (p ++ (∙ ◂ η B)) f (⊗L-1 p g eq) refl ≗
--       ⊗L-1 p (cut p (⊗L ∙ (⊗R f (idA B))) g eq) refl
-- ⊗L-1-cut-A p f (⇒R g) refl = ⇒R (⊗L-1-cut-A _ f g refl)
-- ⊗L-1-cut-A p f (⇐R g) refl = ⇐R (⊗L-1-cut-A _ f g refl)
-- ⊗L-1-cut-A {A = A₁} {B₁} p f (⇒L {U = U} {A} {B} p₁ g g₁) eq with subeq (U ⊛ η (A ⇒ B)) (η (A₁ ⊗ B₁)) p₁ p eq
-- ⊗L-1-cut-A {A = A₁} {B₁} {A' = A'} p f (⇒L {U = U} {A} {B} p₁ g g₁) refl | 2>L1 (gt q refl refl refl)
--   rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η A₁) (q ++ (∙ ◂ η B₁)) |
--           subeq-2>L1 p₁ (η (A ⇒ B)) (η (A' ⊗ B₁)) q = ⇒L (⊗L-1-cut-A q f g refl) refl
-- ... | 2>R1 (gt ∙ eqT () eqp)
-- ⊗L-1-cut-A {A = A₁} {B₁} {A' = A'} p f (⇒L {U = U} {A} {B} p₁ g g₁) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
--   rewrite subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (A' ⊗ B₁)) q₁ q₂ |
--           subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η A₁) q₁ (q₂ ++ (∙ ◂ η B₁)) = ⇒L refl (⊗L-1-cut-A _ f g₁ refl)
-- ⊗L-1-cut-A {A = A₁} {B₁} {A' = A'} p f (⇒L {U = U} {A} {B} p₁ g g₁) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
--   rewrite subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (A' ⊗ B₁)) q₁ q₂ |
--           subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η A₁) (q₁ ++ (∙ ◂ η B₁)) q₂ = ⇒L refl (⊗L-1-cut-A _ f g₁ refl)
-- ⊗L-1-cut-A {A = A₁} {B₁} p f (⇐L {U = U} {A} {B} p₁ g g₁) eq with subeq (η (B ⇐ A) ⊛ U) (η (A₁ ⊗ B₁)) p₁ p eq
-- ... | 2>L1 (gt ∙ eqT () eqp)
-- ⊗L-1-cut-A {A = A₁} {B₁} {A' = A'} p f (⇐L {U = U} {A} {B} p₁ g g₁) refl | 2>R1 (gt q refl refl refl)
--   rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η A₁) (q ++ (∙ ◂ η B₁)) |
--           subeq-2>R1 p₁ (η (B ⇐ A)) (η (A' ⊗ B₁)) q = ⇐L (⊗L-1-cut-A q f g refl) refl
-- ⊗L-1-cut-A {A = A₁} {B₁} {A' = A'} p f (⇐L {U = U} {A} {B} p₁ g g₁) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
--   rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (A' ⊗ B₁)) q₁ q₂ |
--           subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η A₁) q₁ (q₂ ++ (∙ ◂ η B₁)) = ⇐L refl (⊗L-1-cut-A _ f g₁ refl)
-- ⊗L-1-cut-A {A = A₁} {B₁} {A' = A'} p f (⇐L {U = U} {A} {B} p₁ g g₁) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
--   rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (A' ⊗ B₁)) q₁ q₂ |
--           subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η A₁) (q₁ ++ (∙ ◂ η B₁)) q₂ = ⇐L refl (⊗L-1-cut-A _ f g₁ refl)
-- ⊗L-1-cut-A (p ◂ U) f (⊗R g g₁) refl = ⊗R (⊗L-1-cut-A p f g refl) refl
-- ⊗L-1-cut-A (T ▸ p) f (⊗R g g₁) refl = ⊗R refl (⊗L-1-cut-A p f g₁ refl)
-- ⊗L-1-cut-A {A = A₁} {B₁} p f (⊗L {A = A} {B} p₁ g) eq with subeq (η (A ⊗ B)) (η (A₁ ⊗ B₁)) p₁ p eq
-- ⊗L-1-cut-A {A = A₁} {B₁} {A' = A'} p f (⊗L {A = A} {B} p₁ g) refl | 1≡2 (same refl refl refl) 
--   rewrite subeq-1≡2 p (η (A' ⊗ B₁)) = ~ cut-cong2 (p ++ (∙ ◂ _)) f refl (idA-cut-left-unit (p ++ (_ ▸ ∙)) g refl)
-- ⊗L-1-cut-A {A = A₁} {B₁} {A' = A'} p f (⊗L {A = A} {B} p₁ g) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
--   rewrite subeq-1/\2 q (η (A ⊗ B)) (η (A' ⊗ B₁)) q₁ q₂ |
--           subeq-1/\2 q (η (A ⊗ B)) (η A₁) q₁ (q₂ ++ (∙ ◂ η B₁)) = ⊗L (⊗L-1-cut-A  _ f g refl)
-- ⊗L-1-cut-A {A = A₁} {B₁} {A' = A'} p f (⊗L {A = A} {B} p₁ g) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
--   rewrite subeq-2/\1 q (η (A ⊗ B)) (η (A' ⊗ B₁)) q₁ q₂ |
--           subeq-2/\1 q (η (A ⊗ B)) (η A₁) (q₁ ++ (∙ ◂ η B₁)) q₂ = ⊗L (⊗L-1-cut-A  _ f g refl)
-- ⊗L-1-cut-A ∙ f ax ()

-- ⊗L-1-cut-B : ∀ {T U A B C B'}
--   → (p : Path T)
--   → (f : η B' ⊢ B) (g : U ⊢ C)
--   → (eq : U ≡ sub p (η (A ⊗ B)))
--   → cut (p ++ (η A ▸ ∙)) f (⊗L-1 p g eq) refl ≗
--       ⊗L-1 p (cut p (⊗L ∙ (⊗R (idA A) f)) g eq) refl
-- ⊗L-1-cut-B p f (⇒R g) refl = ⇒R (⊗L-1-cut-B _ f g refl)
-- ⊗L-1-cut-B p f (⇐R g) refl = ⇐R (⊗L-1-cut-B _ f g refl)
-- ⊗L-1-cut-B {A = A₁} {B₁} p f (⇒L {U = U} {A} {B} p₁ g g₁) eq with subeq (U ⊛ η (A ⇒ B)) (η (A₁ ⊗ B₁)) p₁ p eq
-- ⊗L-1-cut-B {A = A₁} {B₁} {B' = B'} p f (⇒L {U = U} {A} {B} p₁ g g₁) refl | 2>L1 (gt q refl refl refl)
--   rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η B₁) (q ++ (η A₁ ▸ ∙)) |
--           subeq-2>L1 p₁ (η (A ⇒ B)) (η (A₁ ⊗ B')) q = ⇒L (⊗L-1-cut-B q f g refl) refl
-- ... | 2>R1 (gt ∙ eqT () eqp)
-- ⊗L-1-cut-B {A = A₁} {B₁} {B' = B'} p f (⇒L {U = U} {A} {B} p₁ g g₁) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
--   rewrite subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η (A₁ ⊗ B')) q₁ q₂ |
--           subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η B₁) q₁ (q₂ ++ (η A₁ ▸ ∙)) = ⇒L refl (⊗L-1-cut-B _ f g₁ refl)
-- ⊗L-1-cut-B {A = A₁} {B₁} {B' = B'} p f (⇒L {U = U} {A} {B} p₁ g g₁) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
--   rewrite subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η (A₁ ⊗ B')) q₁ q₂ |
--           subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η B₁) (q₁ ++ (η A₁ ▸ ∙)) q₂ = ⇒L refl (⊗L-1-cut-B _ f g₁ refl)
-- ⊗L-1-cut-B {A = A₁} {B₁} p f (⇐L {U = U} {A} {B} p₁ g g₁) eq with subeq (η (B ⇐ A) ⊛ U) (η (A₁ ⊗ B₁)) p₁ p eq
-- ... | 2>L1 (gt ∙ eqT () eqp)
-- ⊗L-1-cut-B {A = A₁} {B₁} {B' = B'} p f (⇐L {U = U} {A} {B} p₁ g g₁) refl | 2>R1 (gt q refl refl refl)
--   rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η B₁) (q ++ (η A₁ ▸ ∙)) |
--           subeq-2>R1 p₁ (η (B ⇐ A)) (η (A₁ ⊗ B')) q = ⇐L (⊗L-1-cut-B q f g refl) refl
-- ⊗L-1-cut-B {A = A₁} {B₁} {B' = B'} p f (⇐L {U = U} {A} {B} p₁ g g₁) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
--   rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η (A₁ ⊗ B')) q₁ q₂ |
--           subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η B₁) q₁ (q₂ ++ (η A₁ ▸ ∙)) = ⇐L refl (⊗L-1-cut-B _ f g₁ refl)
-- ⊗L-1-cut-B {A = A₁} {B₁} {B' = B'} p f (⇐L {U = U} {A} {B} p₁ g g₁) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
--   rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η (A₁ ⊗ B')) q₁ q₂ |
--           subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η B₁) (q₁ ++ (η A₁ ▸ ∙)) q₂ = ⇐L refl (⊗L-1-cut-B _ f g₁ refl)
-- ⊗L-1-cut-B (p ◂ U) f (⊗R g g₁) refl = ⊗R (⊗L-1-cut-B p f g refl) refl
-- ⊗L-1-cut-B (T ▸ p) f (⊗R g g₁) refl = ⊗R refl (⊗L-1-cut-B p f g₁ refl)
-- ⊗L-1-cut-B {A = A₁} {B₁} p f (⊗L {A = A} {B} p₁ g) eq with subeq (η (A ⊗ B)) (η (A₁ ⊗ B₁)) p₁ p eq
-- ⊗L-1-cut-B {A = A₁} {B₁} {B' = B'} p f (⊗L {A = A} {B} p₁ g) refl | 1≡2 (same refl refl refl) 
--   rewrite subeq-1≡2 p (η (A₁ ⊗ B')) = ~ idA-cut-left-unit (p ++ (∙ ◂ _)) (cut (p ++ (_ ▸ ∙)) f g refl) refl
-- ⊗L-1-cut-B {A = A₁} {B₁} {B' = B'} p f (⊗L {A = A} {B} p₁ g) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
--   rewrite subeq-1/\2 q (η (A ⊗ B)) (η (A₁ ⊗ B')) q₁ q₂ |
--           subeq-1/\2 q (η (A ⊗ B)) (η B₁) q₁ (q₂ ++ (η A₁ ▸ ∙)) = ⊗L (⊗L-1-cut-B  _ f g refl)
-- ⊗L-1-cut-B {A = A₁} {B₁} {B' = B'} p f (⊗L {A = A} {B} p₁ g) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
--   rewrite subeq-2/\1 q (η (A ⊗ B)) (η (A₁ ⊗ B')) q₁ q₂ |
--           subeq-2/\1 q (η (A ⊗ B)) (η B₁) (q₁ ++ (η A₁ ▸ ∙)) q₂ = ⊗L (⊗L-1-cut-B  _ f g refl)
-- ⊗L-1-cut-B ∙ f ax ()


-- ⊗L-1-cut◂ : ∀ {T U W₁ W₂ W₃ A B C A'}
--   → (p₁ : Path W₁) (p₂ : Path W₂) (p₃ : Path W₃)
--   → (f : T ⊢ A') (g : U ⊢ C)
--   → (eq : U ≡ sub p₁ (sub p₂ (η A') ⊛ sub p₃ (η (A ⊗ B))))
--   → ⊗L-1 (p₁ ++ (_ ▸ p₃)) (cut (p₁ ++ (p₂ ◂ _)) f g eq) refl ≗
--       cut (p₁ ++ (p₂ ◂ _)) f (⊗L-1 (p₁ ++ (_ ▸ p₃)) g eq) refl
-- ⊗L-1-cut◂ p₁ p₂ p₃ f (⇒R g) refl = ⇒R (⊗L-1-cut◂ (_ ▸ p₁) p₂ p₃ f g refl)
-- ⊗L-1-cut◂ p₁ p₂ p₃ f (⇐R g) refl = ⇐R (⊗L-1-cut◂ (p₁ ◂ _) p₂ p₃ f g refl)
-- ⊗L-1-cut◂ p₁ p₂ p₃ f (⇒L p g g₁) eq = {!   !}
-- ⊗L-1-cut◂ {A = A₁} {B₁} {A' = A'} p₁ p₂ p₃ f (⇐L {U = U} {A} {B} p g g₁) eq with subeq (η (B ⇐ A) ⊛ U) (sub p₂ (η A') ⊛ sub p₃ (η (A₁ ⊗ B₁))) p p₁ eq
-- ⊗L-1-cut◂ {A = A₁} {B₁} {A' = A'} p₁ ∙ p₃ f (⇐L {U = U} {A} {B} p g g₁) refl | 1≡2 (same refl refl refl) 
--   rewrite subeq-2>L1 p₁ (sub p₃ (η (A₁ ⊗ B₁))) (η (B ⇐ A)) ∙ |
--           subeq-2>R1 p₁ (η (B ⇐ A) ) (η (A₁ ⊗ B₁)) p₃ |
--           subeq-2>L1 p₁ (sub p₃ (η A₁ ⊛ η B₁)) (η (B ⇐ A)) ∙ = {!   !}
-- ... | 2>L1 (gt ∙ eqT () eqp)
-- ⊗L-1-cut◂ {A = A₁} {B₁} {A' = A'} p₁ p₂ p₃ f (⇐L {U = U} {A} {B} p g g₁) refl | 2>R1 (gt q refl refl refl) = {!   !}
-- ... | 1>L2 x = {!   !}
-- ... | 1>R2 x = {!   !}
-- ... | 1/\2 x = {!   !}
-- ... | 2/\1 x = {!   !}
-- ⊗L-1-cut◂ ∙ p₂ p₃ f (⊗R g g₁) refl = refl
-- ⊗L-1-cut◂ (p₁ ◂ U) p₂ p₃ f (⊗R g g₁) refl = ⊗R (⊗L-1-cut◂ p₁ p₂ p₃ f g refl) refl
-- ⊗L-1-cut◂ (T ▸ p₁) p₂ p₃ f (⊗R g g₁) refl = ⊗R refl (⊗L-1-cut◂ p₁ p₂ p₃ f g₁ refl)
-- ⊗L-1-cut◂ {A = A₁} {B₁} {A' = A'} p₁ p₂ p₃ f (⊗L {A = A} {B} p g) eq with subeq (η (A ⊗ B)) (sub p₂ (η A') ⊛ sub p₃ (η (A₁ ⊗ B₁))) p p₁ eq
-- ... | 1>L2 (gt q refl eqU refl) with subeq (η A') (η (A ⊗ B)) p₂ q (⊛eq eqU .proj₁)
-- ⊗L-1-cut◂ {A = A₁} {B₁} {A' = A'} p₁ p₂ p₃ f (⊗L {A = A} {B} .(p₁ ++ (q ◂ _)) g) refl | 1>L2 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
--   rewrite subeq-1/\2 p₁ (η (A ⊗ B)) (η (A₁ ⊗ B₁)) p₂ p₃ |
--           subeq-1≡2 (p₁ ++ (p₂ ◂ sub p₃ (η A₁ ⊛ η B₁))) (η (A ⊗ B)) |
--           subeq-1≡2 (p₁ ++ (p₂ ◂ sub p₃ (η (A₁ ⊗ B₁)))) (η (A ⊗ B)) = {!   !}
-- ... | 1/\2 x = {!   !}
-- ... | 2/\1 x = {!   !}
-- ⊗L-1-cut◂ {A = A₁} {B₁} {A' = A'} p₁ p₂ p₃ f (⊗L {A = A} {B} p g) eq | 1>R2 (gt q refl eqU refl) with subeq (η (A₁ ⊗ B₁)) (η (A ⊗ B)) p₃ q (⊛eq eqU .proj₂)
-- ⊗L-1-cut◂ {T} {A = A₁} {B₁} {A' = A'} p₁ p₂ p₃ f (⊗L {A = A} {B} p g) refl | 1>R2 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
--   rewrite subeq-1≡2 (p₁ ++ (sub p₂ (η A') ▸ p₃)) (η (A₁ ⊗ B₁)) |
--           subeq-2/\1 p₁ (η (A₁ ⊗ B₁)) (η A') p₂ p₃ |
--           subeq-1≡2 (p₁ ++ (sub p₂ T ▸ p₃)) (η (A₁ ⊗ B₁)) = refl
-- ⊗L-1-cut◂ {T} {A = A₁} {B₁} {A' = A'} p₁ p₂ p₃ f (⊗L {A = A} {B} .(p₁ ++ (_ ▸ q)) g) refl | 1>R2 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-2/\1 (p₁ ++ (sub p₂ (η A') ▸ q₁)) (η (A ⊗ B)) (η (A₁ ⊗ B₁)) q₂ q₃ |
--           subeq-2/\1 p₁ (η (A ⊗ B)) (η A') p₂ (q₁ ++ (sub q₂ (η A₁ ⊛ η B₁) ▸ q₃)) |
--           subeq-2/\1 p₁ (η (A ⊗ B)) (η A') p₂ (q₁ ++ (sub q₂ (η (A₁ ⊗ B₁)) ▸ q₃)) |
--           subeq-2/\1 (p₁ ++ (sub p₂ T ▸ q₁)) (η (A ⊗ B)) (η (A₁ ⊗ B₁)) q₂ q₃ = ⊗L (⊗L-1-cut◂ p₁ p₂ (q₁ ++ (q₂ ◂ _)) f g refl)
-- ⊗L-1-cut◂ {T} {A = A₁} {B₁} {A' = A'} p₁ p₂ p₃ f (⊗L {A = A} {B} .(p₁ ++ (_ ▸ q)) g) refl | 1>R2 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-1/\2 (p₁ ++ (sub p₂ (η A') ▸ q₁)) (η (A ⊗ B)) (η (A₁ ⊗ B₁)) q₂ q₃ |
--           subeq-2/\1 p₁ (η (A ⊗ B)) (η A') p₂ (q₁ ++ (q₂ ◂ sub q₃ (η A₁ ⊛ η B₁))) |
--           subeq-2/\1 p₁ (η (A ⊗ B)) (η A') p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (A₁ ⊗ B₁)))) |
--           subeq-1/\2 (p₁ ++ (sub p₂ T ▸ q₁)) (η (A ⊗ B)) (η (A₁ ⊗ B₁)) q₂ q₃ = ⊗L (⊗L-1-cut◂ p₁ p₂ (q₁ ++ (_ ▸ q₃)) f g refl)
-- ⊗L-1-cut◂ {T} {A = A₁} {B₁} {A' = A'} p₁ p₂ p₃ f (⊗L {A = A} {B} p g) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
--   rewrite subeq-1/\2 q (η (A ⊗ B)) (η (A₁ ⊗ B₁)) q₁ (q₂ ++ (sub p₂ (η A') ▸ p₃)) |
--           subeq-1/\2 q (η (A ⊗ B)) (η A') q₁ (q₂ ++ (p₂ ◂ sub p₃ (η A₁ ⊛ η B₁))) |
--           subeq-1/\2 q (η (A ⊗ B)) (η A') q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (A₁ ⊗ B₁)))) |
--           subeq-1/\2 q (η (A ⊗ B)) (η (A₁ ⊗ B₁)) q₁ (q₂ ++ (sub p₂ T ▸ p₃)) = ⊗L (⊗L-1-cut◂ (q ++ (_ ▸ q₂)) p₂ p₃ f g refl)
-- ⊗L-1-cut◂ {T} {A = A₁} {B₁} {A' = A'} p₁ p₂ p₃ f (⊗L {A = A} {B} p g) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
--   rewrite subeq-2/\1 q (η (A ⊗ B)) (η (A₁ ⊗ B₁)) (q₁ ++ (sub p₂ (η A') ▸ p₃)) q₂ |
--           subeq-2/\1 q (η (A ⊗ B)) (η A') (q₁ ++ (p₂ ◂ sub p₃ (η A₁ ⊛ η B₁))) q₂ |
--           subeq-2/\1 q (η (A ⊗ B)) (η A') (q₁ ++ (p₂ ◂ sub p₃ (η (A₁ ⊗ B₁)))) q₂ |
--           subeq-2/\1 q (η (A ⊗ B)) (η (A₁ ⊗ B₁)) (q₁ ++ (sub p₂ T ▸ p₃)) q₂ = ⊗L (⊗L-1-cut◂ (q ++ (q₁ ◂ _)) p₂ p₃ f g refl)
-- ⊗L-1-cut◂ ∙ p₂ p₃ f ax ()

-- ⊗L-1-cut▸ : ∀ {T U W₁ W₂ W₃ A B C A'}
--   → (p₁ : Path W₁) (p₂ : Path W₂) (p₃ : Path W₃)
--   → (f : T ⊢ A') (g : U ⊢ C)
--   → (eq : U ≡ sub p₁ (sub p₂ (η (A ⊗ B)) ⊛ sub p₃ (η A')))
--   → ⊗L-1 (p₁ ++ (p₂ ◂ _)) (cut (p₁ ++ (_ ▸ p₃)) f g eq) refl ≗
--       cut (p₁ ++ (_ ▸ p₃)) f (⊗L-1 (p₁ ++ (p₂ ◂ _)) g eq) refl
-- ⊗L-1-cut▸ p₁ p₂ p₃ f g eq = {!   !}

-- ⊗L-1-cut-C : ∀ {T U V A B C C'}
--   → (p : Path T) (q : Path U)
--   → (f : V ⊢ C') (g : sub p (η (A ⊗ B)) ⊢ C)
--   → (eq : V ≡ sub q (η C))
--   → ⊗L-1 (q ++ p) (cut q g f eq) refl ≗
--       (cut q (⊗L-1 p g refl) f eq)


-- ⊗L-1-cut⇒L : ∀ {T U V W A A' B B' C} (p : Path T) (q : Path U)
--  → (f : V ⊢ A ⇒ B)
--  → (g : W ⊢ A) (h : sub q (η B) ⊢ C)
--  → (eq : V ≡ sub p (η (A' ⊗ B')))
--  → ⊗L-1 (q ++ (W ▸ p)) (cut⇒L q f g h) (cong (λ x → sub q (W ⊛ x)) eq) ≗
--       cut⇒L q (⊗L-1 p f eq) g h
-- ⊗L-1-cut⇒L p q (⇒R f) g h refl = 
--   ⊗L-1≗ (q ++ (_ ▸ p)) refl (~ (≡to≗ (cut-vass (∙ ◂ _) q g f h refl refl))) 
--   ∘ (⊗L-1-cut-C (_ ▸ p) q h (cut (∙ ◂ _) g f refl) refl 
--   ∘ (cut-cong1 q h refl (⊗L-1-cut◂ ∙ ∙ p g f refl) 
--   ∘ ≡to≗ (cut-vass (∙ ◂ _) q g (⊗L-1 (_ ▸ p) f refl) h refl refl)))

-- ⊗L-1-cut⇒L {A' = A'} {B' = B'} p q (⇒L {U = U} {A} {B} p₁ f f₁) g h eq with subeq (U ⊛ η (A ⇒ B)) (η (A' ⊗ B')) p₁ p eq
-- ⊗L-1-cut⇒L {W = W} {A' = A'} {B' = B'} p q (⇒L {U = U} {A} {B} p₁ f f₁) g h refl | 2>L1 (gt q₁ refl refl refl) 
--   rewrite subeq-2>L1 (q ++ (W ▸ p₁)) (η (A ⇒ B)) (η (A' ⊗ B')) q₁ = refl
-- ... | 2>R1 (gt ∙ eqT () eqp)
-- ⊗L-1-cut⇒L {W = W} {A' = A'} {B' = B'} p q (⇒L {U = U} {A} {B} p₁ f f₁) g h refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-1/\2 (q ++ (W ▸ q₁)) (U ⊛ η (A ⇒ B)) (η (A' ⊗ B')) q₂ q₃ = ⇒L refl (⊗L-1-cut⇒L (q₁ ++ (_ ▸ q₃)) q f₁ g h refl)
-- ⊗L-1-cut⇒L {W = W} {A' = A'} {B' = B'} p q (⇒L {U = U} {A} {B} p₁ f f₁) g h refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-2/\1 (q ++ (W ▸ q₁)) (U ⊛ η (A ⇒ B)) (η (A' ⊗ B')) q₂ q₃ = ⇒L refl (⊗L-1-cut⇒L (q₁ ++ (q₂ ◂ _)) q f₁ g h refl)
-- ⊗L-1-cut⇒L {A' = A'} {B' = B'} p q (⇐L {U = U} {A} {B} p₁ f f₁) g h eq with subeq (η (B ⇐ A) ⊛ U) (η (A' ⊗ B')) p₁ p eq
-- ... | 2>L1 (gt ∙ eqT () eqp)
-- ⊗L-1-cut⇒L {W = W} {A' = A'} {B' = B'} p q (⇐L {U = U} {A} {B} p₁ f f₁) g h refl | 2>R1 (gt q₁ refl refl refl) 
--   rewrite subeq-2>R1 (q ++ (W ▸ p₁)) (η (B ⇐ A)) (η (A' ⊗ B')) q₁ = refl
-- ⊗L-1-cut⇒L {W = W} {A' = A'} {B' = B'} p q (⇐L {U = U} {A} {B} p₁ f f₁) g h refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-1/\2 (q ++ (W ▸ q₁)) (η (B ⇐ A) ⊛ U) (η (A' ⊗ B')) q₂ q₃ = ⇐L refl (⊗L-1-cut⇒L (q₁ ++ (_ ▸ q₃)) q f₁ g h refl)
-- ⊗L-1-cut⇒L {W = W} {A' = A'} {B' = B'} p q (⇐L {U = U} {A} {B} p₁ f f₁) g h refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-2/\1 (q ++ (W ▸ q₁)) (η (B ⇐ A) ⊛ U) (η (A' ⊗ B')) q₂ q₃ = ⇐L refl (⊗L-1-cut⇒L (q₁ ++ (q₂ ◂ _)) q f₁ g h refl)
-- ⊗L-1-cut⇒L {A' = A'} {B' = B'} p q (⊗L {A = A} {B} p₁ f) g h eq with subeq (η (A ⊗ B)) (η (A' ⊗ B')) p₁ p eq
-- ⊗L-1-cut⇒L {W = W} {A' = A'} {B' = B'} p q (⊗L {A = A} {B} p₁ f) g h refl | 1≡2 (same refl refl refl) 
--   rewrite subeq-1≡2 (q ++ (W ▸ p)) (η (A' ⊗ B')) = refl
-- ⊗L-1-cut⇒L {W = W} {A' = A'} {B' = B'} p q (⊗L {A = A} {B} p₁ f) g h refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-1/\2 (q ++ (W ▸ q₁)) (η (A ⊗ B)) (η (A' ⊗ B')) q₂ q₃ = ⊗L (⊗L-1-cut⇒L (q₁ ++ (_ ▸ q₃)) q f g h refl)
-- ⊗L-1-cut⇒L {W = W} {A' = A'} {B' = B'} p q (⊗L {A = A} {B} p₁ f) g h refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-2/\1 (q ++ (W ▸ q₁)) (η (A ⊗ B)) (η (A' ⊗ B')) q₂ q₃ = ⊗L (⊗L-1-cut⇒L (q₁ ++ (q₂ ◂ _)) q f g h refl)


-- ⊗L-1-cut⇐L : ∀ {T U V W A A' B B' C} (p : Path T) (q : Path U)
--  → (f : V ⊢ B ⇐ A)
--  → (g : W ⊢ A) (h : sub q (η B) ⊢ C)
--  → (eq : V ≡ sub p (η (A' ⊗ B')))
--  → ⊗L-1 (q ++ (p ◂ W)) (cut⇐L q f g h) (cong (λ x → sub q (x ⊛ W)) eq) ≗
--       cut⇐L q (⊗L-1 p f eq) g h
-- ⊗L-1-cut⇐L p q (⇐R f) g h refl = 
--   ⊗L-1≗ (q ++ (p ◂ _)) refl (~ (≡to≗ (cut-vass (_ ▸ ∙) q g f h refl refl))) 
--   ∘ (⊗L-1-cut-C (p ◂ _) q h (cut (_ ▸ ∙) g f refl) refl 
--   ∘ (cut-cong1 q h refl (⊗L-1-cut▸ ∙ p ∙ g f refl)
--   ∘ ≡to≗ (cut-vass (_ ▸ ∙) q g (⊗L-1 (p ◂ _) f refl) h refl refl)))
-- ⊗L-1-cut⇐L {A' = A'} {B' = B'} p q (⇒L {U = U} {A} {B} p₁ f f₁) g h eq with subeq (U ⊛ η (A ⇒ B)) (η (A' ⊗ B')) p₁ p eq
-- ⊗L-1-cut⇐L {W = W} {A' = A'} {B' = B'} p q (⇒L {U = U} {A} {B} p₁ f f₁) g h refl | 2>L1 (gt q₁ refl refl refl) 
--   rewrite subeq-2>L1 (q ++ (p₁ ◂ W)) (η (A ⇒ B)) (η (A' ⊗ B')) q₁ = refl
-- ... | 2>R1 (gt ∙ eqT () eqp)
-- ⊗L-1-cut⇐L {W = W} {A' = A'} {B' = B'} p q (⇒L {U = U} {A} {B} p₁ f f₁) g h refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-1/\2 (q ++ (q₁ ◂ W)) (U ⊛ η (A ⇒ B)) (η (A' ⊗ B')) q₂ q₃ = ⇒L refl (⊗L-1-cut⇐L (q₁ ++ (_ ▸ q₃)) q f₁ g h refl)
-- ⊗L-1-cut⇐L {W = W} {A' = A'} {B' = B'} p q (⇒L {U = U} {A} {B} p₁ f f₁) g h refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-2/\1 (q ++ (q₁ ◂ W)) (U ⊛ η (A ⇒ B)) (η (A' ⊗ B')) q₂ q₃ = ⇒L refl (⊗L-1-cut⇐L (q₁ ++ (q₂ ◂ _)) q f₁ g h refl)
-- ⊗L-1-cut⇐L {A' = A'} {B' = B'} p q (⇐L {U = U} {A} {B} p₁ f f₁) g h eq with subeq (η (B ⇐ A) ⊛ U) (η (A' ⊗ B')) p₁ p eq
-- ... | 2>L1 (gt ∙ eqT () eqp)
-- ⊗L-1-cut⇐L {W = W} {A' = A'} {B' = B'} p q (⇐L {U = U} {A} {B} p₁ f f₁) g h refl | 2>R1 (gt q₁ refl refl refl) 
--   rewrite subeq-2>R1 (q ++ (p₁ ◂ W)) (η (B ⇐ A)) (η (A' ⊗ B')) q₁ = refl
-- ⊗L-1-cut⇐L {W = W} {A' = A'} {B' = B'} p q (⇐L {U = U} {A} {B} p₁ f f₁) g h refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-1/\2 (q ++ (q₁ ◂ W)) (η (B ⇐ A) ⊛ U) (η (A' ⊗ B')) q₂ q₃ = ⇐L refl (⊗L-1-cut⇐L (q₁ ++ (_ ▸ q₃)) q f₁ g h refl)
-- ⊗L-1-cut⇐L {W = W} {A' = A'} {B' = B'} p q (⇐L {U = U} {A} {B} p₁ f f₁) g h refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-2/\1 (q ++ (q₁ ◂ W)) (η (B ⇐ A) ⊛ U) (η (A' ⊗ B')) q₂ q₃ = ⇐L refl (⊗L-1-cut⇐L (q₁ ++ (q₂ ◂ _)) q f₁ g h refl)
-- ⊗L-1-cut⇐L {A' = A'} {B' = B'} p q (⊗L {A = A} {B} p₁ f) g h eq with subeq (η (A ⊗ B)) (η (A' ⊗ B')) p₁ p eq
-- ⊗L-1-cut⇐L {W = W} {A' = A'} {B' = B'} p q (⊗L {A = A} {B} p₁ f) g h refl | 1≡2 (same refl refl refl) 
--   rewrite subeq-1≡2 (q ++ (p ◂ W)) (η (A' ⊗ B')) = refl
-- ⊗L-1-cut⇐L {W = W} {A' = A'} {B' = B'} p q (⊗L {A = A} {B} p₁ f) g h refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-1/\2 (q ++ (q₁ ◂ W)) (η (A ⊗ B)) (η (A' ⊗ B')) q₂ q₃ = ⊗L (⊗L-1-cut⇐L (q₁ ++ (_ ▸ q₃)) q f g h refl)
-- ⊗L-1-cut⇐L {W = W} {A' = A'} {B' = B'} p q (⊗L {A = A} {B} p₁ f) g h refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-2/\1 (q ++ (q₁ ◂ W)) (η (A ⊗ B)) (η (A' ⊗ B')) q₂ q₃ = ⊗L (⊗L-1-cut⇐L (q₁ ++ (q₂ ◂ _)) q f g h refl)

-- ⊗L-1-cut⊗L : ∀ {T U V A A' B B' C} (p : Path T) (q : Path U)
--  → (f : V ⊢ (A ⊗ B)) (g : sub q (η A ⊛ η B) ⊢ C)
--  → (eq : V ≡ sub p (η (A' ⊗ B')))
--  → ⊗L-1 (q ++ p) (cut⊗L q f g) (cong (λ x → sub q x) eq) ≗ cut⊗L q (⊗L-1 p f eq) g
-- -- ⊗L-1-cut⊗L = {!   !}
-- ⊗L-1-cut⊗L {A' = A'} {B' = B'} p q (⇒L {U = U} {A} {B} p₁ f f₁) g eq with subeq (U ⊛ η (A ⇒ B)) (η (A' ⊗ B')) p₁ p eq
-- ⊗L-1-cut⊗L {A' = A'} {B' = B'} p q (⇒L {U = U} {A} {B} p₁ f f₁) g refl | 2>L1 (gt q₁ refl refl refl) 
--   rewrite  subeq-2>L1 (q ++ p₁) (η (A ⇒ B)) (η (A' ⊗ B')) q₁ = refl
-- ... | 2>R1 (gt ∙ eqT () eqp)
-- ⊗L-1-cut⊗L {A' = A'} {B' = B'} p q (⇒L {U = U} {A} {B} p₁ f f₁) g refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-1/\2 (q ++ q₁) (U ⊛ η (A ⇒ B)) (η (A' ⊗ B')) q₂ q₃ = ⇒L refl (⊗L-1-cut⊗L (q₁ ++ (_ ▸ q₃)) q f₁ g refl)
-- ⊗L-1-cut⊗L {A' = A'} {B' = B'} p q (⇒L {U = U} {A} {B} p₁ f f₁) g refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-2/\1 (q ++ q₁) (U ⊛ η (A ⇒ B)) (η (A' ⊗ B')) q₂ q₃ = ⇒L refl (⊗L-1-cut⊗L (q₁ ++ (q₂ ◂ _)) q f₁ g refl)
-- ⊗L-1-cut⊗L {A' = A'} {B' = B'} p q (⇐L {U = U} {A} {B} p₁ f f₁) g eq with subeq (η (B ⇐ A) ⊛ U) (η (A' ⊗ B')) p₁ p eq
-- ... | 2>L1 (gt ∙ eqT () eqp)
-- ⊗L-1-cut⊗L {A' = A'} {B' = B'} p q (⇐L {U = U} {A} {B} p₁ f f₁) g refl | 2>R1 (gt q₁ refl refl refl) 
--   rewrite  subeq-2>R1 (q ++ p₁) (η (B ⇐ A)) (η (A' ⊗ B')) q₁ = refl
-- ⊗L-1-cut⊗L {A' = A'} {B' = B'} p q (⇐L {U = U} {A} {B} p₁ f f₁) g refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-1/\2 (q ++ q₁) (η (B ⇐ A) ⊛ U) (η (A' ⊗ B')) q₂ q₃ = ⇐L refl (⊗L-1-cut⊗L (q₁ ++ (_ ▸ q₃)) q f₁ g refl)
-- ⊗L-1-cut⊗L {A' = A'} {B' = B'} p q (⇐L {U = U} {A} {B} p₁ f f₁) g refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-2/\1 (q ++ q₁) (η (B ⇐ A) ⊛ U) (η (A' ⊗ B')) q₂ q₃ = ⇐L refl (⊗L-1-cut⊗L (q₁ ++ (q₂ ◂ _)) q f₁ g refl)
-- ⊗L-1-cut⊗L (p ◂ U) q (⊗R f f₁) g refl = ⊗L-1-cut-C p (q ++ (∙ ◂ _)) (cut (q ++ (_ ▸ ∙)) f₁ g refl) f refl
-- ⊗L-1-cut⊗L (T ▸ p) q (⊗R f f₁) g refl = 
--   ⊗L-1≗ (q ++ (T ▸ p)) refl (≡to≗ (cut-hass q ∙ ∙ f f₁ g refl)) 
--   ∘ (⊗L-1-cut-C p (q ++ (_ ▸ ∙)) (cut (q ++ (∙ ◂ _)) f g refl) f₁ refl 
--   ∘ (~ (≡to≗ (cut-hass q ∙ ∙ f (⊗L-1 p f₁ refl) g refl))))
-- ⊗L-1-cut⊗L {A' = A'} {B' = B'} p q (⊗L {A = A} {B} p₁ f) g eq with subeq (η (A ⊗ B)) (η (A' ⊗ B')) p₁ p eq
-- ⊗L-1-cut⊗L {A' = A'} {B' = B'} p q (⊗L {A = A} {B} p₁ f) g refl | 1≡2 (same refl refl refl) 
--   rewrite subeq-1≡2 (q ++ p) (η (A' ⊗ B')) = refl
-- ⊗L-1-cut⊗L {A' = A'} {B' = B'} p q (⊗L {A = A} {B} p₁ f) g refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-1/\2 (q ++ q₁) (η (A ⊗ B)) (η (A' ⊗ B')) q₂ q₃ = ⊗L (⊗L-1-cut⊗L (q₁ ++ (_ ▸ q₃)) q f g refl)
-- ⊗L-1-cut⊗L {A' = A'} {B' = B'} p q (⊗L {A = A} {B} p₁ f) g refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-2/\1 (q ++ q₁) (η (A ⊗ B)) (η (A' ⊗ B')) q₂ q₃ = ⊗L (⊗L-1-cut⊗L (q₁ ++ (q₂ ◂ _)) q f g refl)

-- -- ⊗L-1-cut-C = {!   !}
-- ⊗L-1-cut-C p q (⇒R f) g refl = ⇒R (⊗L-1-cut-C p (_ ▸ q) f g refl)
-- ⊗L-1-cut-C p q (⇐R f) g refl = ⇐R (⊗L-1-cut-C p (q ◂ _) f g refl)
-- ⊗L-1-cut-C {C = C} p q (⇒L {U = U} {A} {B} p₁ f f₁) g eq with subeq (U ⊛ η (A ⇒ B)) (η C) p₁ q eq
-- ⊗L-1-cut-C {A = A₁} {B₁} {C} p q (⇒L {U = U} {A} {B} p₁ f f₁) g refl | 2>L1 (gt q₁ refl refl refl) 
--   rewrite subeq-2>L1 p₁ (η (A ⇒ B))  (η (A₁ ⊗ B₁)) (q₁ ++ p) = ⇒L (⊗L-1-cut-C p q₁ f g refl) refl
-- ⊗L-1-cut-C {C = C} p q (⇒L {U = U} {A} {B} p₁ f f₁) g refl | 2>R1 (gt ∙ refl refl refl) = ⊗L-1-cut⇒L p p₁ g f f₁ refl
-- ⊗L-1-cut-C {A = A₁} {B₁} {C} p q (⇒L {U = U} {A} {B} p₁ f f₁) g refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
--   rewrite  subeq-1/\2 q₁ (U ⊛ η (A ⇒ B)) (η (A₁ ⊗ B₁)) q₂ (q₃ ++ p) = ⇒L refl (⊗L-1-cut-C p (q₁ ++ (_ ▸ q₃)) f₁ g refl)
-- ⊗L-1-cut-C {A = A₁} {B₁} {C} p q (⇒L {U = U} {A} {B} p₁ f f₁) g refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
--   rewrite  subeq-2/\1 q₁ (U ⊛ η (A ⇒ B)) (η (A₁ ⊗ B₁)) (q₂ ++ p) q₃ = ⇒L refl (⊗L-1-cut-C p (q₁ ++ (q₂ ◂ _)) f₁ g refl)

-- ⊗L-1-cut-C {C = C} p q (⇐L {U = U} {A} {B} p₁ f f₁) g eq with subeq (η (B ⇐ A) ⊛ U) (η C) p₁ q eq
-- ⊗L-1-cut-C {C = C} p q (⇐L {U = U} {A} {B} p₁ f f₁) g refl | 2>L1 (gt ∙ refl refl refl) = ⊗L-1-cut⇐L p p₁ g f f₁ refl
-- ⊗L-1-cut-C {A = A₁} {B₁} {C} p q (⇐L {U = U} {A} {B} p₁ f f₁) g refl | 2>R1 (gt q₁ refl refl refl) 
--   rewrite subeq-2>R1 p₁ (η (B ⇐ A))  (η (A₁ ⊗ B₁)) (q₁ ++ p) = ⇐L (⊗L-1-cut-C p q₁ f g refl) refl
-- ⊗L-1-cut-C {A = A₁} {B₁} {C} p q (⇐L {U = U} {A} {B} p₁ f f₁) g refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
--   rewrite  subeq-1/\2 q₁ (η (B ⇐ A) ⊛ U) (η (A₁ ⊗ B₁)) q₂ (q₃ ++ p) = ⇐L refl (⊗L-1-cut-C p (q₁ ++ (_ ▸ q₃)) f₁ g refl)
-- ⊗L-1-cut-C {A = A₁} {B₁} {C} p q (⇐L {U = U} {A} {B} p₁ f f₁) g refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
--   rewrite  subeq-2/\1 q₁ (η (B ⇐ A) ⊛ U) (η (A₁ ⊗ B₁)) (q₂ ++ p) q₃ = ⇐L refl (⊗L-1-cut-C p (q₁ ++ (q₂ ◂ _)) f₁ g refl)
  
-- ⊗L-1-cut-C p (q ◂ U) (⊗R f f₁) g refl = ⊗R (⊗L-1-cut-C p q f g refl) refl
-- ⊗L-1-cut-C p (T ▸ q) (⊗R f f₁) g refl = ⊗R refl (⊗L-1-cut-C p q f₁ g refl)

-- ⊗L-1-cut-C {C = C} p q (⊗L {A = A} {B} p₁ f) g eq with subeq (η (A ⊗ B)) (η C) p₁ q eq
-- ⊗L-1-cut-C {C = C} p q (⊗L {A = A} {B} p₁ f) g refl | 1≡2 (same refl refl refl) = ⊗L-1-cut⊗L p p₁ g f refl
-- ⊗L-1-cut-C {A = A₁} {B₁} {C} p q (⊗L {A = A} {B} p₁ f) g refl | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-1/\2 q₁ (η (A ⊗ B)) (η (A₁ ⊗ B₁)) q₂ (q₃ ++ p) = ⊗L (⊗L-1-cut-C p (q₁ ++ (_ ▸ q₃)) f g refl)
-- ⊗L-1-cut-C {A = A₁} {B₁} {C} p q (⊗L {A = A} {B} p₁ f) g refl | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
--   rewrite subeq-2/\1 q₁ (η (A ⊗ B)) (η (A₁ ⊗ B₁)) (q₂ ++ p) q₃ = ⊗L (⊗L-1-cut-C p (q₁ ++ (q₂ ◂ _)) f g refl)
-- ⊗L-1-cut-C p ∙ ax g refl = refl

-- ⊗L⊗L-1 : ∀ {T U A B C}
--   → (p : Path T)
--   → (f : U ⊢ C)
--   → (eq : U ≡ sub p (η (A ⊗ B)))
--   → ⊗L p (⊗L-1 p f eq) ≗ subst-cxt eq f
-- ⊗L⊗L-1 p (⇒R f) refl = ⊗L⇒R ∘ ⇒R (⊗L⊗L-1 (_ ▸ p) f refl)
-- ⊗L⊗L-1 p (⇐R f) refl = ⊗L⇐R ∘ ⇐R (⊗L⊗L-1 (p ◂ _) f refl)
-- ⊗L⊗L-1 {A = A'} {B'} p (⇒L {U = U} {A} {B} p₁ f g) eq with subeq (U ⊛ η (A ⇒ B)) (η (A' ⊗ B')) p₁ p eq
-- ⊗L⊗L-1 {A = A'} {B'} p (⇒L {U = U} {A} {B} p₁ f g) refl | 2>L1 (gt q refl refl refl) = ⊗L⇒L₁ ∘ ⇒L (⊗L⊗L-1 q f refl) refl
-- ... | 2>R1 (gt ∙ eqT () eqp)
-- ⊗L⊗L-1 {A = A'} {B'} p (⇒L {U = U} {A} {B} p₁ f g) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) = 
--   ⊗L⇒L₂2/\1 {p = q} ∘ ⇒L refl (⊗L⊗L-1 _ g refl)
-- ⊗L⊗L-1 {A = A'} {B'} p (⇒L {U = U} {A} {B} p₁ f g) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 
--   ⊗L⇒L₂1/\2 {p = q} ∘ ⇒L refl (⊗L⊗L-1 _ g refl)
-- ⊗L⊗L-1 {A = A'} {B'} p (⇐L {U = U} {A} {B} p₁ f g) eq with subeq (η (B ⇐ A) ⊛ U) (η (A' ⊗ B')) p₁ p eq
-- ... | 2>L1 (gt ∙ eqT () eqp)
-- ⊗L⊗L-1 {A = A'} {B'} p (⇐L {U = U} {A} {B} p₁ f g) refl | 2>R1 (gt q refl refl refl) = ⊗L⇐L₁ ∘ ⇐L (⊗L⊗L-1 q f refl) refl
-- ⊗L⊗L-1 {A = A'} {B'} p (⇐L {U = U} {A} {B} p₁ f g) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) = 
--   ⊗L⇐L₂2/\1 {p = q} ∘ ⇐L refl (⊗L⊗L-1 _ g refl)
-- ⊗L⊗L-1 {A = A'} {B'} p (⇐L {U = U} {A} {B} p₁ f g) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 
--   ⊗L⇐L₂1/\2 {p = q} ∘ ⇐L refl (⊗L⊗L-1 _ g refl)
-- ⊗L⊗L-1 (p ◂ U) (⊗R f g) refl = ⊗L⊗R₁ ∘ ⊗R (⊗L⊗L-1 p f refl) refl
-- ⊗L⊗L-1 (T ▸ p) (⊗R f g) refl = ⊗L⊗R₂ ∘ ⊗R refl (⊗L⊗L-1 p g refl)
-- ⊗L⊗L-1 {A = A'} {B'} p (⊗L {A = A} {B} p₁ f) eq with subeq (η (A ⊗ B)) (η (A' ⊗ B')) p₁ p eq
-- ⊗L⊗L-1 {A = A'} {B'} p (⊗L {A = A} {B} p₁ f) refl | 1≡2 (same refl refl refl) = refl
-- ⊗L⊗L-1 {A = A'} {B'} p (⊗L {A = A} {B} p₁ f) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) = 
--   ⊗L⊗L {p = q} ∘ ⊗L (⊗L⊗L-1 _ f refl)
-- ⊗L⊗L-1 {A = A'} {B'} p (⊗L {A = A} {B} p₁ f) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 
--   (~ ⊗L⊗L {p = q}) ∘ ⊗L (⊗L⊗L-1 _ f refl)
-- ⊗L⊗L-1 ∙ ax ()