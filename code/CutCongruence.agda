{-# OPTIONS --rewriting #-}

module CutCongruence where

open import Relation.Binary.PropositionalEquality hiding ([_]; _≗_) 
open import Data.Product
open import Data.Empty
open import Fma
open import SeqCalc
open import Cut
open import SubEqProperties
open import CutEqualities
open import CutCirceqEquations

{-
Cut is well-defined wrt. ≗
-}

cut-cong1 : ∀ {T U W C D} (p : Path T)
  → {f f' : U ⊢ D} 
  → (g : W ⊢ C)
  → (eq : W ≡ sub p (η D))
  → (eq' : f ≗ f')
  → cut p f (subst-cxt eq g) refl ≗ cut p f' (subst-cxt eq g) refl

cut-cong2 : ∀ {T U W C D} (p : Path T)
  → (f : U ⊢ D) 
  → {g g' : W ⊢ C}
  → (eq : W ≡ sub p (η D))
  → (eq' : g ≗ g')
  → cut p f (subst-cxt eq g) refl ≗ cut p f (subst-cxt eq g') refl

cut⇒L-cong1 : ∀ {T U V A B C} (p : Path T)
  → {f f' : U ⊢ A ⇒ B}
  → (g : V ⊢ A)
  → (h : sub p (η B) ⊢ C)
  → (eq : f ≗ f')
  → cut⇒L p f g h ≗ cut⇒L p f' g h
cut⇒L-cong1 p g g₁ refl = refl
cut⇒L-cong1 p g g₁ (~ eq') = ~ cut⇒L-cong1 p g g₁ eq'
cut⇒L-cong1 p g g₁ (eq' ∘ eq'') = cut⇒L-cong1 p g g₁ eq' ∘ cut⇒L-cong1 p g g₁ eq''
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ (⇒R eq') 
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ = cut-cong2 (p ++ (∙ ◂ _)) g refl (cut-cong1 p g₁ refl eq')
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ (⇒L eq' eq'') 
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ = ⇒L eq' (cut⇒L-cong1 p g g₁ eq'')
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ (⇐L eq' eq'') 
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ = ⇐L eq' (cut⇒L-cong1 p g g₁ eq'')
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ (⊗L eq')
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ = ⊗L (cut⇒L-cong1 p g g₁ eq')
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ (⇒L⇒R {p = p₂} {f} {h}) 
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ = 
            ≡to≗ (cut⇒L-vass-right p p₂ f g₁ g h) 
            ∘ (~ cut-cong2 (p ++ (∙ ◂ sub p₂ (_ ⊛ η (_ ⇒ _)))) g refl (cut⇒L≗ p (_ ▸ p₂) h g₁ refl))
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ (⇐L⇒R {p = p₂} {f} {h}) 
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ = 
            ≡to≗ (cut⇐L-vass-right p p₂ f g₁ g h) 
            ∘ (~ cut-cong2 (p ++ (∙ ◂ sub p₂ (η (_ ⇐ _) ⊛ _))) g refl (cut⇐L≗ p (_ ▸ p₂) h g₁ refl))
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ (⊗L⇒R {p = p₂} {f}) 
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ =
            ≡to≗ (cut⊗L-vass-right p p₂ g g₁ f) 
            ∘ (~ cut-cong2 (p ++ (∙ ◂ sub p₂ (η (_ ⊗ _)))) g refl (cut⊗L≗ p (_ ▸ p₂) f g₁ refl))
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ (⊗L⊗L {p = p₂})
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ = ⊗L⊗L {p = p ++ (_ ▸ p₂)}
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ ⊗L⇒L₁
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ = ⊗L⇒L₁
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ (⊗L⇒L₂1/\2 {p = p₂})
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ = ⊗L⇒L₂1/\2 {p = p ++ (_ ▸ p₂)}
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ (⊗L⇒L₂2/\1 {p = p₂}) 
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ = ⊗L⇒L₂2/\1 {p = p ++ (_ ▸ p₂)}
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ ⊗L⇐L₁
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ = ⊗L⇐L₁
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ (⊗L⇐L₂1/\2 {p = p₂}) 
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ = ⊗L⇐L₂1/\2 {p = p ++ (_ ▸ p₂)}
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ (⊗L⇐L₂2/\1 {p = p₂})
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ = ⊗L⇐L₂2/\1 {p = p ++ (_ ▸ p₂)}
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ ⇒L⇒L
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ = ⇒L⇒L
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ (⇒L⇒L₂ {p = p₂}) 
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ = ⇒L⇒L₂ {p = p ++ (_ ▸ p₂)}
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ ⇒L⇐L 
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ = ⇒L⇐L
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ (⇒L⇐L₂ {p = p₂}) 
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ = ⇒L⇐L₂ {p = p ++ (_ ▸ p₂)}
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ ⇐L⇒L 
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ = ⇐L⇒L
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ (⇐L⇒L₂ {p = p₂})
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ = ⇐L⇒L₂ {p = p ++ (_ ▸ p₂)}
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ ⇐L⇐L 
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ = ⇐L⇐L
cut⇒L-cong1 {U = U} {A = A} {B} p g g₁ (⇐L⇐L₂ {p = p₂}) 
  rewrite subeq-2>R1 p U (η (A ⇒ B)) ∙ |
          subeq-2>R1 p U (η (A ⇒ B)) ∙ = ⇐L⇐L₂ {p = p ++ (_ ▸ p₂)}

cut⇒L-cong2 : ∀ {T U V A B C} (p : Path T)
  → (f : U ⊢ A ⇒ B)
  → (g g' : V ⊢ A)
  → (h h' : sub p (η B) ⊢ C)
  → (eq : g ≗ g') (eq' : h ≗ h')
  → cut⇒L p f g h ≗ cut⇒L p f g' h'
cut⇒L-cong2 p (⇒R f) g g' h h' eq eq' = 
  cut-cong1 (p ++ (∙ ◂ _)) (cut p f h refl) refl eq ∘ cut-cong2 (p ++ (∙ ◂ _)) g' refl (cut-cong2 p f refl eq')
cut⇒L-cong2 p (⇒L p₁ f f₁) g g' h h' eq eq' = ⇒L refl (cut⇒L-cong2 p f₁ g g' h h' eq eq')
cut⇒L-cong2 p (⇐L p₁ f f₁) g g' h h' eq eq' = ⇐L refl (cut⇒L-cong2 p f₁ g g' h h' eq eq')
cut⇒L-cong2 p (⊗L p₁ f) g g' h h' eq eq' = ⊗L (cut⇒L-cong2 p f g g' h h' eq eq')

cut⇐L-cong1 : ∀ {T U V A B C} (p : Path T)
  → {f f' : U ⊢ B ⇐ A}
  → (g : V ⊢ A)
  → (h : sub p (η B) ⊢ C)
  → (eq : f ≗ f')
  → cut⇐L p f g h ≗ cut⇐L p f' g h
cut⇐L-cong1 p g g₁ refl = refl
cut⇐L-cong1 p g g₁ (~ eq') = ~ cut⇐L-cong1 p g g₁ eq'
cut⇐L-cong1 p g g₁ (eq' ∘ eq'') = cut⇐L-cong1 p g g₁ eq' ∘ cut⇐L-cong1 p g g₁ eq''
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ (⇐R eq') 
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ = cut-cong2 (p ++ (_ ▸ ∙)) g refl (cut-cong1 p g₁ refl eq')
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ (⇒L eq' eq'') 
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ = ⇒L eq' (cut⇐L-cong1 p g g₁ eq'') 
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ (⇐L eq' eq'') 
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ = ⇐L eq' (cut⇐L-cong1 p g g₁ eq'')
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ (⊗L eq')
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ = ⊗L (cut⇐L-cong1 p g g₁ eq')
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ (⇒L⇐R {p = p₂} {f} {h}) 
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ = 
            ≡to≗ (cut⇒L-vass-left p p₂ f g₁ g h) 
            ∘ (~ cut-cong2 (p ++ (sub p₂ (_ ⊛ η (_ ⇒ _)) ▸ ∙)) g refl (cut⇒L≗ p (p₂ ◂ _) h g₁ refl))
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ (⇐L⇐R {p = p₂} {f} {h}) 
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ = 
            ≡to≗ (cut⇐L-vass-left p p₂ f g₁ g h) 
            ∘ (~ cut-cong2 (p ++ (sub p₂ (η (_ ⇐ _) ⊛ _) ▸ ∙)) g refl (cut⇐L≗ p (p₂ ◂ _) h g₁ refl))
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ (⊗L⇐R {p = p₂} {f}) 
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ = 
            ≡to≗ (cut⊗L-vass-left p p₂ g g₁ f) 
            ∘ (~ cut-cong2 (p ++ (sub p₂ (η (_ ⊗ _)) ▸ ∙)) g refl (cut⊗L≗ p (p₂ ◂ _) f g₁ refl))
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ (⊗L⊗L {p = p₂})
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ = ⊗L⊗L {p = p ++ (p₂ ◂ _)}
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ ⊗L⇒L₁
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ = ⊗L⇒L₁
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ (⊗L⇒L₂1/\2 {p = p₂})
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ = ⊗L⇒L₂1/\2 {p = p ++ (p₂ ◂ _)}
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ (⊗L⇒L₂2/\1 {p = p₂}) 
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ = ⊗L⇒L₂2/\1 {p = p ++ (p₂ ◂ _)}
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ ⊗L⇐L₁
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ = ⊗L⇐L₁
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ (⊗L⇐L₂1/\2 {p = p₂}) 
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ = ⊗L⇐L₂1/\2 {p = p ++ (p₂ ◂ _)}
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ (⊗L⇐L₂2/\1 {p = p₂})
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ = ⊗L⇐L₂2/\1 {p = p ++ (p₂ ◂ _)}
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ ⇒L⇒L
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ = ⇒L⇒L
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ (⇒L⇒L₂ {p = p₂}) 
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ = ⇒L⇒L₂ {p = p ++ (p₂ ◂ _)}
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ ⇒L⇐L 
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ = ⇒L⇐L
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ (⇒L⇐L₂ {p = p₂}) 
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ = ⇒L⇐L₂ {p = p ++ (p₂ ◂ _)}
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ ⇐L⇒L 
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ = ⇐L⇒L
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ (⇐L⇒L₂ {p = p₂})
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ = ⇐L⇒L₂ {p = p ++ (p₂ ◂ _)}
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ ⇐L⇐L 
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ = ⇐L⇐L
cut⇐L-cong1 {U = U} {A = A} {B} p g g₁ (⇐L⇐L₂ {p = p₂}) 
  rewrite subeq-2>L1 p U (η (B ⇐ A)) ∙ |
          subeq-2>L1 p U (η (B ⇐ A)) ∙ = ⇐L⇐L₂ {p = p ++ (p₂ ◂ _)}

cut⇐L-cong2 : ∀ {T U V A B C} (p : Path T)
  → (f : U ⊢ B ⇐ A)
  → (g g' : V ⊢ A)
  → (h h' : sub p (η B) ⊢ C)
  → (eq : g ≗ g') (eq' : h ≗ h')
  → cut⇐L p f g h ≗ cut⇐L p f g' h'
cut⇐L-cong2 p (⇐R f) g g' h h' eq eq' = 
  cut-cong1 (p ++ (_ ▸ ∙)) (cut p f h refl) refl eq ∘ cut-cong2 (p ++ (_ ▸ ∙)) g' refl (cut-cong2 p f refl eq')
cut⇐L-cong2 p (⇒L p₁ f f₁) g g' h h' eq eq' = ⇒L refl (cut⇐L-cong2 p f₁ g g' h h' eq eq')
cut⇐L-cong2 p (⇐L p₁ f f₁) g g' h h' eq eq' = ⇐L refl (cut⇐L-cong2 p f₁ g g' h h' eq eq')
cut⇐L-cong2 p (⊗L p₁ f) g g' h h' eq eq' = ⊗L (cut⇐L-cong2 p f g g' h h' eq eq')

cut⊗L-cong1 : ∀ {T U A B C} (p : Path T)
  → {f f' : U ⊢ A ⊗ B}
  → (g : sub p (η A ⊛ η B) ⊢ C )
  → (eq : f ≗ f')
  → cut⊗L p f g ≗ cut⊗L p f' g
cut⊗L-cong1 p g refl = refl
cut⊗L-cong1 p g (~ eq') = ~ cut⊗L-cong1 p g eq'
cut⊗L-cong1 p g (eq' ∘ eq'') = 
  cut⊗L-cong1 p g eq' ∘ cut⊗L-cong1 p g eq''
cut⊗L-cong1 {A = A} {B} p g (⇒L eq' eq'') 
  rewrite subeq-1≡2 p (η (A ⊗ B)) = ⇒L eq' (cut⊗L-cong1 p g eq'')
cut⊗L-cong1 {A = A} {B} p g (⇐L eq' eq'') 
  rewrite subeq-1≡2 p (η (A ⊗ B)) = ⇐L eq' (cut⊗L-cong1 p g eq'')
cut⊗L-cong1 {A = A} {B} p g (⊗R {f' = f'} {g₁} eq' eq'')
  rewrite subeq-1≡2 p (η (A ⊗ B)) = 
    cut-cong1 (p ++ (∙ ◂ _)) (cut (p ++ (η A ▸ ∙)) g₁ g refl) refl eq' 
    ∘ cut-cong2 (p ++ (∙ ◂ _)) f' refl (cut-cong1 (p ++ (η A ▸ ∙)) g refl eq'')
cut⊗L-cong1 {A = A} {B} p g (⊗L eq') 
  rewrite subeq-1≡2 p (η (A ⊗ B)) = ⊗L (cut⊗L-cong1 p g eq')
cut⊗L-cong1 {A = A} {B} p g (⇒L⊗R₁ {A = A'} {B'} {p = p₂} {f = f} {g₁} {h}) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = 
            ~ cut⇒L≗ (p ++ (∙ ◂ _)) p₂ g₁ (cut (p ++ (η A ▸ ∙)) h g refl) refl
cut⊗L-cong1 {A = A} {B} p g (⇒L⊗R₂ {U = U} {A = A'} {B'} {p = p₂} {f = f} {g₁} {h}) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = 
          ≡to≗ (cut⇒L-hass p p₂ f g g₁ h)
          ∘ (~ cut-cong2 (p ++ (∙ ◂ sub p₂ (U ⊛ η (A' ⇒ B')))) g₁ refl (cut⇒L≗ (p ++ (η A ▸ ∙)) p₂ h g refl))
cut⊗L-cong1 {A = A} {B} p g (⇐L⊗R₁ {A = A'} {B'} {p = p₂} {f = f} {g₁} {h}) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = 
            ~ cut⇐L≗ (p ++ (∙ ◂ _)) p₂ g₁ (cut (p ++ (η A ▸ ∙)) h g refl) refl
cut⊗L-cong1 {A = A} {B} p g (⇐L⊗R₂ {U = U} {A = A'} {B'} {p = p₂} {f = f} {g₁} {h}) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = 
            ≡to≗ (cut⇐L-hass p p₂ f g g₁ h)
            ∘ (~ cut-cong2 (p ++ (∙ ◂ sub p₂ (η (B' ⇐ A') ⊛ U))) g₁ refl (cut⇐L≗ (p ++ (η A ▸ ∙)) p₂ h g refl))
cut⊗L-cong1 {A = A} {B} p g (⊗L⊗R₁ {A = A'} {B'} {p = p₂} {f = f} {g₁}) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = 
            ~ cut⊗L≗ (p ++ (∙ ◂ _)) p₂ f (cut (p ++ (η A ▸ ∙)) g₁ g refl) refl
cut⊗L-cong1 {A = A} {B} p g (⊗L⊗R₂ {A = A'} {B'} {p = p₂} {f = f} {g₁}) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = 
            ≡to≗ (cut⊗L-hass p p₂ f g g₁)
            ∘ cut-cong2 (p ++ (∙ ◂ sub p₂ (η (_ ⊗ _)))) f refl (~ cut⊗L≗ (p ++ (η A ▸ ∙)) p₂ g₁ g refl)
cut⊗L-cong1 {A = A} {B} p g (⊗L⊗L {p = p₁}) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = ⊗L⊗L {p = p ++ p₁}
cut⊗L-cong1 {A = A} {B} p g ⊗L⇒L₁ 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = ⊗L⇒L₁
cut⊗L-cong1 {A = A} {B} p g (⊗L⇒L₂1/\2 {p = p₁}) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = ⊗L⇒L₂1/\2 {p = p ++ p₁}
cut⊗L-cong1 {A = A} {B} p g (⊗L⇒L₂2/\1 {p = p₁}) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = ⊗L⇒L₂2/\1 {p = p ++ p₁}
cut⊗L-cong1 {A = A} {B} p g ⊗L⇐L₁ 
  rewrite subeq-1≡2 p (η (A ⊗ B)) | 
          subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = ⊗L⇐L₁
cut⊗L-cong1 {A = A} {B} p g (⊗L⇐L₂1/\2 {p = p₁}) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = ⊗L⇐L₂1/\2 {p = p ++ p₁}
cut⊗L-cong1 {A = A} {B} p g (⊗L⇐L₂2/\1 {p = p₁}) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = ⊗L⇐L₂2/\1 {p = p ++ p₁}
cut⊗L-cong1 {A = A} {B} p g ⇒L⇒L 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = ⇒L⇒L
cut⊗L-cong1 {A = A} {B} p g (⇒L⇒L₂ {p = p₁}) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B))= (⇒L⇒L₂ {p = p ++ p₁})
cut⊗L-cong1 {A = A} {B} p g ⇒L⇐L 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = ⇒L⇐L
cut⊗L-cong1 {A = A} {B} p g (⇒L⇐L₂ {p = p₁}) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B))= (⇒L⇐L₂ {p = p ++ p₁})
cut⊗L-cong1 {A = A} {B} p g ⇐L⇒L 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = ⇐L⇒L
cut⊗L-cong1 {A = A} {B} p g (⇐L⇒L₂ {p = p₁}) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = (⇐L⇒L₂ {p = p ++ p₁})
cut⊗L-cong1 {A = A} {B} p g ⇐L⇐L 
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = ⇐L⇐L
cut⊗L-cong1 {A = A} {B} p g (⇐L⇐L₂ {p = p₁})  
  rewrite subeq-1≡2 p (η (A ⊗ B)) |
          subeq-1≡2 p (η (A ⊗ B)) = ⇐L⇐L₂ {p = p ++ p₁}


cut⊗L-cong2 : ∀ {T U A B C} (p : Path T)
  → (f : U ⊢ A ⊗ B)
  → (g g' : sub p (η A ⊛ η B) ⊢ C )
  → (eq : g ≗ g')
  → cut⊗L p f g ≗ cut⊗L p f g'
cut⊗L-cong2 p (⇒L p₁ f f₁) g g' eq = ⇒L refl (cut⊗L-cong2 p f₁ g g' eq)
cut⊗L-cong2 p (⇐L p₁ f f₁) g g' eq = ⇐L refl (cut⊗L-cong2 p f₁ g g' eq)
cut⊗L-cong2 p (⊗R f f₁) g g' eq = cut-cong2 (p ++ (∙ ◂ _)) f refl (cut-cong2 (p ++ (η _ ▸ ∙)) f₁ refl eq)
cut⊗L-cong2 p (⊗L p₁ f) g g' eq = ⊗L (cut⊗L-cong2 p f g g' eq)

{-
Proof of cut-cong1
-}

cut-cong1 p (⇒R g) refl eq' = ⇒R (cut-cong1 (_ ▸ p) g refl eq')
cut-cong1 p (⇐R g) refl eq' = ⇐R (cut-cong1 (p ◂ _) g refl eq')
cut-cong1 p (⇒L p₁ g g₁) eq eq' with subeq _ _ p₁ p eq
cut-cong1 {D = D} p (⇒L {A = A} {B} p₁ g g₁) refl eq' | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η D) q = ⇒L (cut-cong1 q g refl eq') refl
cut-cong1 p (⇒L {U = U} {A = A} {B} p₁ g g₁) refl eq' | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 p₁ U (η (A ⇒ B)) ∙ = cut⇒L-cong1 p₁ g g₁ eq' 

cut-cong1 {D = D} p (⇒L {U = U} {A = A} {B} p₁ g g₁) refl eq' | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η D) q₁ q₂ = ⇒L refl (cut-cong1 (q ++ (sub q₁ (η B) ▸ q₂)) g₁ refl eq')
cut-cong1 {D = D} p (⇒L {U = U} {A = A} {B} p₁ g g₁) refl eq' | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η D) q₁ q₂ = ⇒L refl (cut-cong1 (q ++ (q₁ ◂ sub q₂ (η B))) g₁ refl eq')
cut-cong1 p (⇐L p₁ g g₁) eq eq' with subeq _ _ p₁ p eq
cut-cong1 p (⇐L {U = U} {A = A} {B} p₁ g g₁) refl eq' | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 p₁ U (η (B ⇐ A)) ∙ = cut⇐L-cong1 p₁ g g₁ eq'

cut-cong1 {D = D} p (⇐L {A = A} {B} p₁ g g₁) refl eq' | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η D) q = ⇐L (cut-cong1 q g refl eq') refl
cut-cong1 {D = D} p (⇐L {U = U} {A = A} {B} p₁ g g₁) refl eq' | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η D) q₁ q₂ = ⇐L refl (cut-cong1 (q ++ (sub q₁ (η B) ▸ q₂)) g₁ refl eq')
cut-cong1 {D = D} p (⇐L {U = U} {A = A} {B} p₁ g g₁) refl eq' | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η D) q₁ q₂ = ⇐L refl (cut-cong1 (q ++ (q₁ ◂ sub q₂ (η B))) g₁ refl eq')
cut-cong1 (p ◂ U) (⊗R g g₁) refl eq' = ⊗R (cut-cong1 p g refl eq') refl
cut-cong1 (T ▸ p) (⊗R g g₁) refl eq' = ⊗R refl (cut-cong1 p g₁ refl eq')
cut-cong1 p (⊗L p₁ g) eq eq' with subeq _ _ p₁ p eq
cut-cong1 p (⊗L {A = A} {B} p₁ g) refl eq' | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) = cut⊗L-cong1 p g eq'
cut-cong1 {D = D} p (⊗L {A = A} {B} p₁ g) refl eq' | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η D) q₁ q₂ = ⊗L (cut-cong1 (q ++ (sub q₁ (η A ⊛ η B) ▸ q₂)) g refl eq')
cut-cong1 {D = D} p (⊗L {A = A} {B} p₁ g) refl eq' | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η D) q₁ q₂ = ⊗L (cut-cong1 (q ++ (q₁ ◂ sub q₂ (η A ⊛ η B))) g refl eq')
cut-cong1 ∙ ax refl eq' = eq' 


{-
Proof of cut-cong2
-}

cut-cong2 {D = D} p f eq (⇒L {U = U} {A} {B} {p = p₁} eq' eq'') with subeq (U ⊛ η (A ⇒ B)) (η D) p₁ p eq
cut-cong2 {D = D} p f refl (⇒L {U = _} {A} {B} {p = p₁} eq' eq'') | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η D) q = ⇒L (cut-cong2 q f refl eq') eq''
cut-cong2 {D = D} p f refl (⇒L {U = U} {A} {B} {p = p₁} eq' eq'') | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 p₁ U (η (A ⇒ B)) ∙ = cut⇒L-cong2 p₁ f _ _ _ _ eq' eq''  
cut-cong2 {D = D} p f refl (⇒L {U = U} {A} {B} eq' eq'') | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η D) q₁ q₂ = ⇒L eq' (cut-cong2 (q ++ (sub q₁ (η B) ▸ q₂)) f refl eq'')
cut-cong2 {D = D} p f refl (⇒L {U = U} {A} {B} eq' eq'') | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η D) q₁ q₂ = ⇒L eq' (cut-cong2 (q ++ (q₁ ◂ sub q₂ (η B))) f refl eq'')

cut-cong2 p f eq (⇐L {p = p₁} eq' eq'') with subeq _ _ p₁ p eq
cut-cong2 {D = D} p f refl (⇐L {U = U} {A} {B} {p = p₁} {g} {h} {k} eq' eq'') | 2>L1 (gt ∙ refl refl refl)
  rewrite subeq-2>L1 p₁ U (η (B ⇐ A)) ∙ = cut⇐L-cong2 p₁ f g h k _ eq' eq''
cut-cong2 {D = D} p f refl (⇐L {U = _} {A} {B} {p = p₁} eq' eq'') | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η D) q = ⇐L (cut-cong2 q f refl eq') eq''
cut-cong2 {D = D} p f refl (⇐L {U = U} {A} {B} eq' eq'') | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η D) q₁ q₂ = ⇐L eq' (cut-cong2 (q ++ (sub q₁ (η B) ▸ q₂)) f refl eq'')
cut-cong2 {D = D} p f refl (⇐L {U = U} {A} {B} eq' eq'') | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η D) q₁ q₂ = ⇐L eq' (cut-cong2 (q ++ (q₁ ◂ sub q₂ (η B))) f refl eq'')

cut-cong2 (p ◂ U) f refl (⊗R eq' eq'') = ⊗R (cut-cong2 p f refl eq') eq''

cut-cong2 (T ▸ p) f refl (⊗R eq' eq'') = ⊗R eq' (cut-cong2 p f refl eq'')

cut-cong2 p f eq (⊗L {p = p₁} eq') with subeq _ _ p₁ p eq
cut-cong2 p f refl (⊗L {A = A} {B} eq') | 1≡2 (same refl refl refl)
  rewrite subeq-1≡2 p (η (A ⊗ B)) = cut⊗L-cong2 p f _ _ eq'
cut-cong2 {D = D} p f refl (⊗L {A = A} {B} eq') | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η D) q₁ q₂ = ⊗L (cut-cong2 (q ++ (sub q₁ (η A ⊛ η B) ▸ q₂)) f refl eq')
cut-cong2 {D = D} p f refl (⊗L {A = A} {B} eq') | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η D) q₁ q₂ = ⊗L (cut-cong2 (q ++ (q₁ ◂ sub q₂ (η A ⊛ η B))) f refl eq')

cut-cong2 p f eq (⇒L⇒R {p = p₁}) with subeq _ _ p₁ p eq
cut-cong2 {D = D} p f refl (⇒L⇒R {A = A} {B} {p = p₁}) | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η D) q = ⇒L⇒R
cut-cong2 p f refl (⇒L⇒R {U = U} {A} {B} {p = p₁}) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 p₁ U (η (A ⇒ B)) ∙ = cut⇒L⇒R p₁ f
cut-cong2 {D = D} p f refl (⇒L⇒R {U = U} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η D) q₁ q₂ = ⇒L⇒R
cut-cong2 {D = D} p f refl (⇒L⇒R {U = U} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η D) q₁ q₂ = ⇒L⇒R

cut-cong2 {D = D} p f eq (⇐L⇒R {U = U} {A} {B} {p = p₁}) with subeq (η (B ⇐ A) ⊛ U) (η D) p₁ p eq
cut-cong2 {D = D} p f refl (⇐L⇒R {U = U} {A} {B} {p = p₁}) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 p₁ U (η (B ⇐ A)) ∙ = cut⇐L⇒R p₁ f
cut-cong2 {D = D} p f refl (⇐L⇒R {A = A} {B} {p = p₁}) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η D) q = ⇐L⇒R
cut-cong2 {D = D} p f refl (⇐L⇒R {U = U} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η D) q₁ q₂ = ⇐L⇒R
cut-cong2 {D = D} p f refl (⇐L⇒R {U = U} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η D) q₁ q₂ = ⇐L⇒R

cut-cong2 p f eq (⊗L⇒R {p = p₁}) with subeq _ _ p₁ p eq
cut-cong2 p f refl (⊗L⇒R {A = A} {B} {p = p₁}) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) = cut⊗L⇒R p f
cut-cong2 {D = D} p f refl (⊗L⇒R {A = A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η D) q₁ q₂ = ⊗L⇒R
cut-cong2 {D = D} p f refl (⊗L⇒R {A = A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η D) q₁ q₂ = ⊗L⇒R

cut-cong2 p f eq (⇒L⇐R {p = p₁}) with subeq _ _ p₁ p eq
cut-cong2 {D = D} p f refl (⇒L⇐R {A = A} {B} {p = p₁}) | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η D) q = ⇒L⇐R
cut-cong2 p f refl (⇒L⇐R {U = U} {A} {B} {p = p₁}) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 p₁ U (η (A ⇒ B)) ∙ = cut⇒L⇐R p₁ f
cut-cong2 {D = D} p f refl (⇒L⇐R {U = U} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η D) q₁ q₂ = ⇒L⇐R
cut-cong2 {D = D} p f refl (⇒L⇐R {U = U} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η D) q₁ q₂ = ⇒L⇐R

cut-cong2 p f eq (⇐L⇐R {p = p₁}) with subeq _ _ p₁ p eq
cut-cong2 {D = D} p f refl (⇐L⇐R {U = U} {A} {B} {p = p₁}) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 p₁ U (η (B ⇐ A)) ∙ = cut⇐L⇐R p₁ f
cut-cong2 {D = D} p f refl (⇐L⇐R {A = A} {B} {p = p₁}) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η D) q = ⇐L⇐R
cut-cong2 {D = D} p f refl (⇐L⇐R {U = U} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η D) q₁ q₂ = ⇐L⇐R
cut-cong2 {D = D} p f refl (⇐L⇐R {U = U} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η D) q₁ q₂ = ⇐L⇐R

cut-cong2 p f eq (⊗L⇐R {p = p₁}) with subeq _ _ p₁ p eq
cut-cong2 p f refl (⊗L⇐R {A = A} {B} {p = p₁}) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) = cut⊗L⇐R p f
cut-cong2 {D = D} p f refl (⊗L⇐R {A = A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η D) q₁ q₂ = ⊗L⇐R
cut-cong2 {D = D} p f refl (⊗L⇐R {A = A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η D) q₁ q₂ = ⊗L⇐R

cut-cong2 (p ◂ U) f eq (⇒L⊗R₁ {p = p₁}) with subeq _ _ p₁ p (⊛eq eq .proj₁)
cut-cong2 {D = D} (p ◂ _) f refl (⇒L⊗R₁ {A = A} {B} {p = p₁}) | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η D) q = ⇒L⊗R₁
cut-cong2 (p ◂ _) f refl (⇒L⊗R₁ {U = U} {A = A} {B} {p = p₁}) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 p₁ U (η (A ⇒ B)) ∙ = cut⇒L⊗R₁ p₁ f
cut-cong2 {D = D} (p ◂ _) f refl (⇒L⊗R₁ {U = U} {A = A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η D) q₁ q₂ = ⇒L⊗R₁
cut-cong2 {D = D} (p ◂ _) f refl (⇒L⊗R₁ {U = U} {A = A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η D) q₁ q₂ = ⇒L⊗R₁

cut-cong2 (T ▸ p) f refl (⇒L⊗R₁ {p = p₁}) = ⇒L⊗R₁

cut-cong2 (p ◂ U) f refl (⇒L⊗R₂ {p = p₁}) = ⇒L⊗R₂

cut-cong2 (T ▸ p) f eq (⇒L⊗R₂ {p = p₁}) with subeq _ _ p₁ p (⊛eq eq .proj₂)
cut-cong2 {D = D} (T ▸ p) f refl (⇒L⊗R₂ {A = A} {B} {p = p₁}) | 2>L1 (gt q refl refl refl) 
  rewrite subeq-2>L1 p₁ (η (A ⇒ B)) (η D) q = ⇒L⊗R₂
cut-cong2 (_ ▸ p) f refl (⇒L⊗R₂ {U = U} {A = A} {B} {p = p₁}) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 p₁ U (η (A ⇒ B)) ∙ = cut⇒L⊗R₂ p₁ f
cut-cong2 {D = D} (_ ▸ p) f refl (⇒L⊗R₂ {U = U} {A = A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η D) q₁ q₂ = ⇒L⊗R₂
cut-cong2 {D = D} (_ ▸ p) f refl (⇒L⊗R₂ {U = U} {A = A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η D) q₁ q₂ = ⇒L⊗R₂

cut-cong2 (p ◂ U) f eq (⇐L⊗R₁ {p = p₁}) with subeq _ _ p₁ p (⊛eq eq .proj₁)
cut-cong2 (p ◂ _) f refl (⇐L⊗R₁ {U = U} {A = A} {B} {p = p₁}) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 p₁ U (η (B ⇐ A)) ∙ = cut⇐L⊗R₁ p₁ f
cut-cong2 {D = D} (p ◂ _) f refl (⇐L⊗R₁ {A = A} {B} {p = p₁}) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η D) q = ⇐L⊗R₁
cut-cong2 {D = D} (p ◂ _) f refl (⇐L⊗R₁ {U = U} {A = A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η D) q₁ q₂ = ⇐L⊗R₁
cut-cong2 {D = D} (p ◂ _) f refl (⇐L⊗R₁ {U = U} {A = A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η D) q₁ q₂ = ⇐L⊗R₁

cut-cong2 (T ▸ p) f refl (⇐L⊗R₁ {p = p₁}) = ⇐L⊗R₁

cut-cong2 (p ◂ U) f refl (⇐L⊗R₂ {p = p₁}) = ⇐L⊗R₂ 

cut-cong2 (T ▸ p) f eq (⇐L⊗R₂ {p = p₁}) with subeq _ _ p₁ p (⊛eq eq .proj₂)
cut-cong2 (_ ▸ p) f refl (⇐L⊗R₂ {U = U} {A = A} {B} {p = p₁}) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 p₁ U (η (B ⇐ A)) ∙ = cut⇐L⊗R₂ p₁ f
cut-cong2 {D = D} (T ▸ p) f refl (⇐L⊗R₂ {A = A} {B} {p = p₁}) | 2>R1 (gt q refl refl refl) 
  rewrite subeq-2>R1 p₁ (η (B ⇐ A)) (η D) q = ⇐L⊗R₂
cut-cong2 {D = D} (_ ▸ p) f refl (⇐L⊗R₂ {U = U} {A = A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η D) q₁ q₂ = ⇐L⊗R₂
cut-cong2 {D = D} (_ ▸ p) f refl (⇐L⊗R₂ {U = U} {A = A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η D) q₁ q₂ = ⇐L⊗R₂

cut-cong2 (p ◂ U) f eq (⊗L⊗R₁ {p = p₁}) with subeq _ _ p₁ p (⊛eq eq .proj₁)
cut-cong2 {D = D} (p ◂ _) f refl (⊗L⊗R₁ {U = U} {A = A} {B}) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) = cut⊗L⊗R₁ p f
cut-cong2 {D = D} (p ◂ _) f refl (⊗L⊗R₁ {U = U} {A = A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η D) q₁ q₂ = ⊗L⊗R₁
cut-cong2 {D = D} (p ◂ _) f refl (⊗L⊗R₁ {U = U} {A = A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η D) q₁ q₂ = ⊗L⊗R₁

cut-cong2 (T ▸ p) f refl (⊗L⊗R₁ {p = p₁}) = ⊗L⊗R₁

cut-cong2 (p ◂ U) f refl (⊗L⊗R₂ {p = p₁}) = ⊗L⊗R₂

cut-cong2 (T ▸ p) f eq (⊗L⊗R₂ {p = p₁}) with subeq _ _ p₁ p (⊛eq eq .proj₂)
cut-cong2 {D = D} (_ ▸ p) f refl (⊗L⊗R₂ {U = U} {A = A} {B}) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p (η (A ⊗ B)) = cut⊗L⊗R₂ p f
cut-cong2 {D = D} (_ ▸ p) f refl (⊗L⊗R₂ {U = U} {A = A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η D) q₁ q₂ = ⊗L⊗R₂
cut-cong2 {D = D} (_ ▸ p) f refl (⊗L⊗R₂ {U = U} {A = A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η D) q₁ q₂ = ⊗L⊗R₂

cut-cong2 p f eq (⊗L⊗L {p = p₁} {p₂} {p₃}) with subeq _ _ p₁ p eq
... | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut-cong2 ._ f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A ⊗ B)) p₂ p₃ |
          subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (η A' ⊛ η B'))) (η (A ⊗ B)) |
          subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (η (A' ⊗ B')))) (η (A ⊗ B)) = ~ cut⊗L⊗L₁ p₁ q p₃ f
cut-cong2 {D = D} ._ f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (A' ⊗ B')) (η D) (q₁ ++ (sub q₂ (η (A ⊗ B)) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (η (A ⊗ B)) (η D) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (η (A ⊗ B)) (η D) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η D) (q₁ ++ (sub q₂ (η A ⊛ η B) ▸ q₃)) p₃ = ⊗L⊗L {p = p₁} 
cut-cong2 {D = D} ._ f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (A' ⊗ B')) (η D) (q₁ ++ (q₂ ◂ sub q₃ (η (A ⊗ B)))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (η (A ⊗ B)) (η D) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (η (A ⊗ B)) (η D) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η D) (q₁ ++ (q₂ ◂ sub q₃ (η A ⊛ η B))) p₃ = ⊗L⊗L {p = p₁} 
cut-cong2 p f eq (⊗L⊗L {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut-cong2 ._ f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1/\2 p₁ (η (A ⊗ B)) (η (A' ⊗ B')) p₂ p₃ |
          subeq-1≡2 (p₁ ++ (sub p₂ (η A ⊛ η B) ▸ q)) (η (A' ⊗ B')) |
          subeq-1≡2 (p₁ ++ (sub p₂ (η (A ⊗ B)) ▸ q)) (η (A' ⊗ B')) = cut⊗L⊗L₂ p₁ p₂ q f
cut-cong2 {D = D} ._ f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 p₁ (η (A ⊗ B)) (η D) p₂ (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η A ⊛ η B) ▸ q₁)) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (sub p₂ (η (A ⊗ B)) ▸ q₁)) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (η (A ⊗ B)) (η D) p₂ (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) = ⊗L⊗L {p = p₁} 
cut-cong2 {D = D} ._ f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 p₁ (η (A ⊗ B)) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η A ⊛ η B) ▸ q₁)) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (sub p₂ (η (A ⊗ B)) ▸ q₁)) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (η (A ⊗ B)) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) = ⊗L⊗L {p = p₁} 
cut-cong2 {D = D} p f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (η (A ⊗ B)) (η D) (q₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η D) (q₁ ++ (sub p₂ (η A ⊛ η B) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η D) (q₁ ++ (sub p₂ (η (A ⊗ B)) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (A ⊗ B)) (η D) (q₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) q₂ = ⊗L⊗L {p = q ++ (q₁ ◂ _)}
cut-cong2 {D = D} p f refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (A ⊗ B)) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η D) q₁ (q₂ ++ (sub p₂ (η A ⊛ η B) ▸ p₃)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η D) q₁ (q₂ ++ (sub p₂ (η (A ⊗ B)) ▸ p₃)) |
          subeq-2/\1 q (η (A ⊗ B)) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) = ⊗L⊗L {p = q ++ (_ ▸ q₂)}

cut-cong2 p f eq (⊗L⇒L₁ {p = p₁} {p'}) with subeq _ _ p' p eq
... | 2>L1 (gt q refl eqU refl) with subeq _ _ p₁ q (⊛eq eqU .proj₁)
cut-cong2 ._ f refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p' = p'}) | 2>L1 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-2>L1 p' (η (A ⇒ B)) (η (A' ⊗ B')) q |
          subeq-1≡2 (p' ++ (q ◂ η (A ⇒ B))) (η (A' ⊗ B')) |
          subeq-1≡2 q (η (A' ⊗ B')) = cut⊗L⇒L-vass₁ p' q f
cut-cong2 {D = D} ._ f refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p' = p'}) | 2>L1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2>L1 p' (η (A ⇒ B)) (η D) (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) |
          subeq-1/\2 q₁ (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-1/\2 (p' ++ (q₁ ◂ η (A ⇒ B))) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-2>L1 p' (η (A ⇒ B)) (η D) (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃))  = ⊗L⇒L₁ {p' = p'}
cut-cong2 {D = D} ._ f refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p' = p'}) | 2>L1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2>L1 p' (η (A ⇒ B)) (η D) (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) |
          subeq-2/\1 q₁ (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-2/\1 (p' ++ (q₁ ◂ η (A ⇒ B))) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-2>L1 p' (η (A ⇒ B)) (η D) (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B')))  = ⊗L⇒L₁ {p' = p'}
cut-cong2 p f refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = p₁} {p'}) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 p' (sub p₁ (η (A' ⊗ B'))) (η (A ⇒ B)) ∙ |
          subeq-1/\2 p' (η (A' ⊗ B')) (η (A ⇒ B)) p₁ ∙ |
          subeq-1/\2 p' (η A' ⊛ η B') (η (A ⇒ B)) p₁ ∙ |
          subeq-2>R1 p' (sub p₁ (η A' ⊛ η B')) (η (A ⇒ B)) ∙ = ~ cut⊗L⇒L-vass₂ p' p₁ f
cut-cong2 {D = D} p f refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = p₁}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (sub p₁ (η (A' ⊗ B')) ⊛ η (A ⇒ B)) (η D) q₁ q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η D) (q₁ ++ (p₁ ◂ η (A ⇒ B))) q₂ |
          subeq-1/\2 q (sub p₁ (η A' ⊛ η B') ⊛ η (A ⇒ B)) (η D) q₁ q₂ = ⊗L⇒L₁ {p' = q ++ (q₁ ◂ _)}
cut-cong2 {D = D} p f refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = p₁}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (sub p₁ (η (A' ⊗ B')) ⊛ η (A ⇒ B)) (η D) q₁ q₂ |
          subeq-2/\1 q (η (A' ⊗ B')) (η D) q₁ (q₂ ++ (p₁ ◂ η (A ⇒ B))) |
          subeq-2/\1 q (sub p₁ (η A' ⊛ η B') ⊛ η (A ⇒ B)) (η D) q₁ q₂ = ⊗L⇒L₁ {p' = q ++ (_ ▸ q₂)}

cut-cong2 p f eq (⊗L⇒L₂1/\2 {p = p₁} {p₂} {p₃}) with subeq _ _ p₁ p eq
cut-cong2 p f eq (⊗L⇒L₂1/\2 {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut-cong2 ._ f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 1≡2 (same refl refl refl)
  rewrite subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η (A' ⊗ B')) q p₃ |
          subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (η B))) (η (A' ⊗ B')) |
          subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (U ⊛ η (A ⇒ B)))) (η (A' ⊗ B')) = cut⊗L⇒L1/\2-hass₂ p₁ q p₃ f
cut-cong2 {D = D} ._ f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η D) (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η B))) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (U ⊛ η (A ⇒ B)))) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η D) (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) p₃ = ⊗L⇒L₂1/\2 {p = p₁}
cut-cong2 {D = D} ._ f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η D) (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η B))) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (U ⊛ η (A ⇒ B)))) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-2/\1 p₁ (U ⊛ η (A ⇒ B)) (η D) (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) p₃ = ⊗L⇒L₂1/\2 {p = p₁}
cut-cong2 p f eq (⊗L⇒L₂1/\2 {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut-cong2 {D = D} ._ f refl (⊗L⇒L₂1/\2 {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2>L1 (gt q₁ refl refl refl)
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) (η (A ⇒ B)) (η D) q₁ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η D) p₂ (p₃ ++ (q₁ ◂ η (A ⇒ B))) |
          subeq-2>L1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) (η (A ⇒ B)) (η D) q₁ = ⊗L⇒L₂1/\2 {p = p₁}
cut-cong2 ._ f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) U (η (A ⇒ B)) ∙ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (A ⇒ B)) p₂ (p₃ ++ (U ▸ ∙)) |
          subeq-2>R1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) U (η (A ⇒ B)) ∙ = ~ cut⊗L⇒L1/\2-hass₁ p₁ p₂ p₃ f
cut-cong2 {D = D} ._ f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q₁)) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η D) p₂ (q₁ ++ (sub q₂ (η B) ▸ q₃)) |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η D) p₂ (q₁ ++ (sub q₂ (U ⊛ η (A ⇒ B)) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q₁)) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ = ⊗L⇒L₂1/\2 {p = p₁}
cut-cong2 {D = D} ._ f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q₁)) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η B))) |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (U ⊛ η (A ⇒ B)))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q₁)) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ = ⊗L⇒L₂1/\2 {p = p₁}
cut-cong2 {D = D} p f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η D) (q₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η D) (q₁ ++ (p₂ ◂ sub p₃ (η B))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η D) (q₁ ++ (p₂ ◂ sub p₃ (U ⊛ η (A ⇒ B)))) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η D) (q₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) q₂ = ⊗L⇒L₂1/\2 {p = q ++ (q₁ ◂ _)} 
cut-cong2 {D = D} p f refl (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η D) q₁ (q₂ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (U ⊛ η (A ⇒ B)))) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η D) q₁ (q₂ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) = ⊗L⇒L₂1/\2 {p = q ++ (_ ▸ q₂)}

cut-cong2 p f eq (⊗L⇒L₂2/\1 {p = p₁} {p₂} {p₃}) with subeq _ _ p₁ p eq
cut-cong2 p f eq (⊗L⇒L₂2/\1  {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut-cong2 {D = D} ._ f refl (⊗L⇒L₂2/\1  {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2>L1 (gt q₁ refl refl refl)
  rewrite subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) (η (A ⇒ B)) (η D) q₁ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η D) (p₂ ++ (q₁ ◂ η (A ⇒ B))) p₃ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) (η (A ⇒ B)) (η D) q₁ = ⊗L⇒L₂2/\1  {p = p₁} 
cut-cong2 ._ f refl (⊗L⇒L₂2/\1  {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) U (η (A ⇒ B)) ∙ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A ⇒ B)) (p₂ ++ (U ▸ ∙)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) U (η (A ⇒ B)) ∙ = ~ cut⊗L⇒L2/\1-hass₁ p₁ p₂ p₃ f
cut-cong2 {D = D} ._ f refl (⊗L⇒L₂2/\1  {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η D) (q₁ ++ (sub q₂ (η B) ▸ q₃)) p₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η D) (q₁ ++ (sub q₂ (U ⊛ η (A ⇒ B)) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ =  ⊗L⇒L₂2/\1  {p = p₁}
cut-cong2 {D = D} ._ f refl (⊗L⇒L₂2/\1  {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η D) (q₁ ++ (q₂ ◂ sub q₃ (η B))) p₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η D) (q₁ ++ (q₂ ◂ sub q₃ (U ⊛ η (A ⇒ B)))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ =  ⊗L⇒L₂2/\1  {p = p₁}
cut-cong2 p f eq (⊗L⇒L₂2/\1  {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut-cong2 ._ f refl (⊗L⇒L₂2/\1  {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 1≡2 (same refl refl refl)
  rewrite subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A' ⊗ B')) p₂ q |
          subeq-1≡2 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (A' ⊗ B')) |
          subeq-1≡2 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q)) (η (A' ⊗ B')) = cut⊗L⇒L2/\1-hass₂ p₁ p₂ p₃ f 
cut-cong2 {D = D} ._ f refl (⊗L⇒L₂2/\1  {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η D) p₂ (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q₁)) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η D) p₂ (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) = ⊗L⇒L₂2/\1  {p = p₁}
cut-cong2 {D = D} ._ f refl (⊗L⇒L₂2/\1  {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q₁)) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) = ⊗L⇒L₂2/\1  {p = p₁}
cut-cong2 {D = D} p f refl (⊗L⇒L₂2/\1  {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η D) (q₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η D) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η D) (q₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η D) (q₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) q₂ = ⊗L⇒L₂2/\1  {p = q ++ (q₁ ◂ _)} 
cut-cong2 {D = D} p f refl (⊗L⇒L₂2/\1  {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η D) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η D) q₁ (q₂ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) =  ⊗L⇒L₂2/\1  {p = q ++ (_ ▸ q₂)}

cut-cong2 p f eq (⊗L⇐L₁ {p = p₁} {p'}) with subeq _ _ p' p eq
cut-cong2 p f refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = p₁} {p'}) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 p' (sub p₁ (η (A' ⊗ B'))) (η (B ⇐ A)) ∙ |
          subeq-2/\1 p' (η (A' ⊗ B')) (η (B ⇐ A)) ∙ p₁ |
          subeq-2/\1 p' (η A' ⊛ η B') (η (B ⇐ A)) ∙ p₁ |
          subeq-2>L1 p' (sub p₁ (η A' ⊛ η B')) (η (B ⇐ A)) ∙ = ~ cut⊗L⇐L-vass₂ p' p₁ f
cut-cong2 p f eq (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = p₁} {p'}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₁ q (⊛eq eqU .proj₂)
cut-cong2 ._ f refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p' = p'}) | 2>R1 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-2>R1 p' (η (B ⇐ A)) (η (A' ⊗ B')) q |
          subeq-1≡2 (p' ++ (η (B ⇐ A) ▸ q)) (η (A' ⊗ B')) |
          subeq-1≡2 q (η (A' ⊗ B')) = cut⊗L⇐L-vass₁ p' q f -- cut⊗L⇒L p' q f
cut-cong2 {D = D} ._ f refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p' = p'}) | 2>R1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2>R1 p' (η (B ⇐ A)) (η D) (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) |
          subeq-1/\2 q₁ (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-1/\2 (p' ++ (η (B ⇐ A) ▸ q₁)) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-2>R1 p' (η (B ⇐ A)) (η D) (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃))  = ⊗L⇐L₁ {p' = p'}
cut-cong2 {D = D} ._ f refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p' = p'}) | 2>R1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2>R1 p' (η (B ⇐ A)) (η D) (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) |
          subeq-2/\1 q₁ (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-2/\1 (p' ++ (η (B ⇐ A) ▸ q₁)) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-2>R1 p' (η (B ⇐ A)) (η D) (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B')))  = ⊗L⇐L₁ {p' = p'}
cut-cong2 {D = D} p f refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = p₁}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ sub p₁ (η (A' ⊗ B'))) (η D) q₁ q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η D) (q₁ ++ (η (B ⇐ A) ▸ p₁)) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ sub p₁ (η A' ⊛ η B')) (η D) q₁ q₂ = ⊗L⇐L₁ {p' = q ++ (q₁ ◂ _)}
cut-cong2 {D = D} p f refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = p₁}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ sub p₁ (η (A' ⊗ B'))) (η D) q₁ q₂ |
          subeq-2/\1 q (η (A' ⊗ B')) (η D) q₁ (q₂ ++ (η (B ⇐ A) ▸ p₁)) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ sub p₁ (η A' ⊛ η B')) (η D) q₁ q₂ = ⊗L⇐L₁ {p' = q ++ (_ ▸ q₂)}


cut-cong2 p f eq (⊗L⇐L₂1/\2 {p = p₁} {p₂} {p₃}) with subeq _ _ p₁ p eq
cut-cong2 p f eq (⊗L⇐L₂1/\2 {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut-cong2 ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 1≡2 (same refl refl refl)
  rewrite subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η (A' ⊗ B')) q p₃ |
          subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (η B))) (η (A' ⊗ B')) |
          subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (η (B ⇐ A) ⊛ U))) (η (A' ⊗ B')) = cut⊗L⇐L1/\2-hass₂ p₁ q p₃ f 
cut-cong2 {D = D} ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η D) (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η B))) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (B ⇐ A) ⊛ U))) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η D) (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) p₃ = ⊗L⇐L₂1/\2 {p = p₁}
cut-cong2 {D = D} ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η D) (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η B))) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (B ⇐ A) ⊛ U))) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U) (η D) (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) p₃ = ⊗L⇐L₂1/\2 {p = p₁}
cut-cong2 p f eq (⊗L⇐L₂1/\2 {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut-cong2  ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2>L1 (gt ∙ refl refl refl)
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) U (η (B ⇐ A)) ∙ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η (B ⇐ A)) p₂ (p₃ ++ (∙ ◂ U)) |
          subeq-2>L1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) U (η (B ⇐ A)) ∙ = ~ cut⊗L⇐L1/\2-hass₁ p₁ p₂ p₃ f
cut-cong2 {D = D} ._ f refl (⊗L⇐L₂1/\2 {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2>R1 (gt q₁ refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) (η (B ⇐ A)) (η D) q₁ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η D) p₂ (p₃ ++ (η (B ⇐ A) ▸ q₁)) |
          subeq-2>R1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) (η (B ⇐ A)) (η D) q₁ = ⊗L⇐L₂1/\2 {p = p₁} 
cut-cong2 {D = D} ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q₁)) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η D) p₂ (q₁ ++ (sub q₂ (η B) ▸ q₃)) |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η D) p₂ (q₁ ++ (sub q₂ (η (B ⇐ A) ⊛ U) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q₁)) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ = ⊗L⇐L₂1/\2 {p = p₁}
cut-cong2 {D = D} ._ f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q₁)) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η B))) |
          subeq-1/\2 p₁ (η (A' ⊗ B')) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (B ⇐ A) ⊛ U))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q₁)) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ = ⊗L⇐L₂1/\2 {p = p₁}
cut-cong2 {D = D} p f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η D) (q₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η D) (q₁ ++ (p₂ ◂ sub p₃ (η B))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η D) (q₁ ++ (p₂ ◂ sub p₃ (η (B ⇐ A) ⊛ U))) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η D) (q₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) q₂ = ⊗L⇐L₂1/\2 {p = q ++ (q₁ ◂ _)} 
cut-cong2 {D = D} p f refl (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η D) q₁ (q₂ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (B ⇐ A) ⊛ U))) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η D) q₁ (q₂ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) = ⊗L⇐L₂1/\2 {p = q ++ (_ ▸ q₂)}

cut-cong2 p f eq (⊗L⇐L₂2/\1 {p = p₁} {p₂} {p₃}) with subeq _ _ p₁ p eq
cut-cong2 p f eq (⊗L⇐L₂2/\1  {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut-cong2 ._ f refl (⊗L⇐L₂2/\1  {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) U (η (B ⇐ A)) ∙ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η (B ⇐ A)) (p₂ ++ (∙ ◂ U)) p₃ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) U (η (B ⇐ A)) ∙ = ~ cut⊗L⇐L2/\1-hass₁ p₁ p₂ p₃ f
cut-cong2 {D = D} ._ f refl (⊗L⇐L₂2/\1  {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2>R1 (gt q₁ refl refl refl)
  rewrite subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) (η (B ⇐ A)) (η D) q₁ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η D) (p₂ ++ (η (B ⇐ A) ▸ q₁)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) (η (B ⇐ A)) (η D) q₁ = ⊗L⇐L₂2/\1  {p = p₁} 
cut-cong2 {D = D} ._ f refl (⊗L⇐L₂2/\1  {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η D) (q₁ ++ (sub q₂ (η B) ▸ q₃)) p₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η D) (q₁ ++ (sub q₂ (η (B ⇐ A) ⊛ U) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ =  ⊗L⇐L₂2/\1  {p = p₁}
cut-cong2 {D = D} ._ f refl (⊗L⇐L₂2/\1  {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η D) (q₁ ++ (q₂ ◂ sub q₃ (η B))) p₃ |
          subeq-2/\1 p₁ (η (A' ⊗ B')) (η D) (q₁ ++ (q₂ ◂ sub q₃ (η (B ⇐ A) ⊛ U))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ = ⊗L⇐L₂2/\1  {p = p₁}
cut-cong2 p f eq (⊗L⇐L₂2/\1  {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut-cong2 ._ f refl (⊗L⇐L₂2/\1  {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 1≡2 (same refl refl refl)
  rewrite subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A' ⊗ B')) p₂ q |
          subeq-1≡2 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (A' ⊗ B')) |
          subeq-1≡2 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q)) (η (A' ⊗ B')) = cut⊗L⇐L2/\1-hass₂ p₁ p₂ p₃ f 
cut-cong2 {D = D} ._ f refl (⊗L⇐L₂2/\1  {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η D) p₂ (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q₁)) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η D) p₂ (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) = ⊗L⇐L₂2/\1  {p = p₁}
cut-cong2 {D = D} ._ f refl (⊗L⇐L₂2/\1  {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q₁)) (η (A' ⊗ B')) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) = ⊗L⇐L₂2/\1  {p = p₁}
cut-cong2 {D = D} p f refl (⊗L⇐L₂2/\1  {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η D) (q₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η D) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (A' ⊗ B')) (η D) (q₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η D) (q₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) q₂ = ⊗L⇐L₂2/\1  {p = q ++ (q₁ ◂ _)} 
cut-cong2 {D = D} p f refl (⊗L⇐L₂2/\1  {U = U} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) |
          subeq-2/\1 q (η (A' ⊗ B')) (η D) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) |
          subeq-2/\1 q (η (A' ⊗ B')) (η D) q₁ (q₂ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) =  ⊗L⇐L₂2/\1  {p = q ++ (_ ▸ q₂)}

cut-cong2 p f eq (⇒L⇒L {q = q} {r})  with subeq _ _ r p eq
cut-cong2 p f eq (⇒L⇒L {q = q} {r}) | 2>L1 (gt q₁ refl eqU refl) with subeq _ _ q q₁ (⊛eq eqU .proj₁)
cut-cong2 {D = D} ._ f refl (⇒L⇒L {A = A} {B} {A'} {B'} {q = q} {r}) | 2>L1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 r (η (A ⇒ B)) (η D) (q ++ (q₁ ◂ η (A' ⇒ B'))) |
          subeq-2>L1 q (η (A' ⇒ B')) (η D) q₁ |
          subeq-2>L1 (r ++ (q ◂ η (A ⇒ B))) (η (A' ⇒ B')) (η D) q₁ = ⇒L⇒L {r = r}
cut-cong2 ._ f refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>L1 (gt q₁ refl refl refl) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 r (η (A ⇒ B)) (T ⊛ η (A' ⇒ B')) (q ++ (T ▸ ∙)) |
          subeq-2>R1 (r ++ (q ◂ η (A ⇒ B))) T (η (A' ⇒ B')) ∙ |
          subeq-2>L1 r (η (A ⇒ B)) (η (A' ⇒ B')) (q ++ (T ▸ ∙)) |
          subeq-2>R1 q T (η (A' ⇒ B')) ∙ = cut⇒L⇒L-vass₁ q r f
cut-cong2 {D = D} ._ f refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2>L1 r (η (A ⇒ B)) (η D) ((q₁ ++ (sub q₂ (T ⊛ η (A' ⇒ B')) ▸ q₃))) |
          subeq-1/\2 q₁ (T ⊛ η (A' ⇒ B')) (η D) q₂ q₃ |
          subeq-1/\2 (r ++ (q₁ ◂ η (A ⇒ B))) (T ⊛ η (A' ⇒ B')) (η D) q₂ q₃ |
          subeq-2>L1 r (η (A ⇒ B)) (η D) ((q₁ ++ (sub q₂ (η B') ▸ q₃))) = ⇒L⇒L {r = r}
cut-cong2 {D = D} ._ f refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2>L1 r (η (A ⇒ B)) (η D) ((q₁ ++ (q₂ ◂ sub q₃ (T ⊛ η (A' ⇒ B'))))) |
          subeq-2/\1 q₁ (T ⊛ η (A' ⇒ B')) (η D) q₂ q₃ |
          subeq-2/\1 (r ++ (q₁ ◂ η (A ⇒ B))) (T ⊛ η (A' ⇒ B')) (η D) q₂ q₃ |
          subeq-2>L1 r (η (A ⇒ B)) (η D) ((q₁ ++ (q₂ ◂ sub q₃ (η B')))) = ⇒L⇒L {r = r}
cut-cong2 p f refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 r (sub q (T ⊛ η (A' ⇒ B'))) (η (A ⇒ B)) ∙ |
          subeq-1/\2 r (T ⊛ η (A' ⇒ B')) (η (A ⇒ B)) q ∙ |
          subeq-2>R1 r (sub q (η B')) (η (A ⇒ B)) ∙ = ~ cut⇒L⇒L-vass₂ q r f
cut-cong2 {D = D} p f refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (sub q (T ⊛ η (A' ⇒ B')) ⊛ η (A ⇒ B)) (η D) q₂ q₃ |
          subeq-1/\2 q₁ (T ⊛ η (A' ⇒ B')) (η D) (q₂ ++ (q ◂ η (A ⇒ B))) q₃ |
          subeq-1/\2 q₁ (sub q (η B') ⊛ η (A ⇒ B)) (η D) q₂ q₃ = ⇒L⇒L {r = q₁ ++ (q₂ ◂ _)}
cut-cong2 {D = D} p f refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (sub q (T ⊛ η (A' ⇒ B')) ⊛ η (A ⇒ B)) (η D) q₂ q₃ |
          subeq-2/\1 q₁ (T ⊛ η (A' ⇒ B')) (η D) q₂ (q₃ ++ (q ◂ η (A ⇒ B))) |
          subeq-2/\1 q₁ (sub q (η B') ⊛ η (A ⇒ B)) (η D) q₂ q₃ = ⇒L⇒L {r = q₁ ++ (_ ▸ q₃)}

cut-cong2 p f eq (⇒L⇒L₂ {p = p₁} {p₂} {p₃}) with subeq _ _ p₁ p eq
cut-cong2 p f eq (⇒L⇒L₂ {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut-cong2 {D = D} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2>L1 (gt q₁ refl refl refl)
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η D) (p₂ ++ (q₁ ◂ η (A ⇒ B))) p₃ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) (η (A ⇒ B)) (η D) q₁ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (η (A ⇒ B)) (η D) q₁ = ⇒L⇒L₂ {p = p₁}
cut-cong2 ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (A ⇒ B)) (p₂ ++ (U ▸ ∙)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) U (η (A ⇒ B)) ∙ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) U (η (A ⇒ B)) ∙  = cut⇒L⇒L-hass₂ p₁ p₂ p₃ f
cut-cong2 {D = D} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η D) (q₁ ++ (sub q₂ (U ⊛ η (A ⇒ B)) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η B'))) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ |
          subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η D) (q₁ ++ (sub q₂ (η B) ▸ q₃)) p₃ = ⇒L⇒L₂ {p = p₁}
cut-cong2 {D = D} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η D) (q₁ ++ (q₂ ◂ sub q₃ (U ⊛ η (A ⇒ B)))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η B'))) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ |
          subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η D) (q₁ ++ (q₂ ◂ sub q₃ (η B))) p₃ = ⇒L⇒L₂ {p = p₁}
cut-cong2 p f eq (⇒L⇒L₂ {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut-cong2 {D = D} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) (η (A' ⇒ B')) (η D) q₁ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η D) p₂ (p₃ ++ (q₁ ◂ η (A' ⇒ B'))) |
          subeq-2>L1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (A' ⇒ B')) (η D) q₁ = ⇒L⇒L₂ {p = p₁}
cut-cong2 ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) V (η (A' ⇒ B')) ∙ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (A' ⇒ B')) p₂ (p₃ ++ (V ▸ ∙)) |
          subeq-2>R1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) V (η (A' ⇒ B')) ∙ = ~ cut⇒L⇒L-hass₁ p₁ p₂ p₃ f
cut-cong2 {D = D} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q₁)) (V ⊛ η (A' ⇒ B')) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η D) p₂ (q₁ ++ (sub q₂ (η B') ▸ q₃)) |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η D) p₂ (q₁ ++ (sub q₂ (V ⊛ η (A' ⇒ B')) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (V ⊛ η (A' ⇒ B')) (η D) q₂ q₃ = ⇒L⇒L₂ {p = p₁}
cut-cong2 {D = D} ._ f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q₁)) (V ⊛ η (A' ⇒ B')) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η B'))) |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (V ⊛ η (A' ⇒ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (V ⊛ η (A' ⇒ B')) (η D) q₂ q₃ = ⇒L⇒L₂ {p = p₁}
cut-cong2 {D = D} p f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (V ⊛ η (A' ⇒ B')) (η D) (q₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η D) (q₁ ++ (p₂ ◂ sub p₃ (η B'))) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η D) (q₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) q₂ |
          subeq-1/\2 q (V ⊛ η (A' ⇒ B')) (η D) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = ⇒L⇒L₂ {p = q ++ (q₁ ◂ _)}
cut-cong2 {D = D} p f refl (⇒L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (V ⊛ η (A' ⇒ B')) (η D) q₁ (q₂ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B'))) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) |
          subeq-2/\1 q (V ⊛ η (A' ⇒ B')) (η D) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = ⇒L⇒L₂ {p = q ++ (_ ▸ q₂)}

cut-cong2 p f eq (⇒L⇐L {q = q} {r}) with subeq _ _ r p eq
cut-cong2 p f refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 r (sub q (T ⊛ η (A' ⇒ B'))) (η (B ⇐ A)) ∙ |
          subeq-2/\1 r (T ⊛ η (A' ⇒ B')) (η (B ⇐ A)) ∙ q  |
          subeq-2>L1 r (sub q (η B')) (η (B ⇐ A)) ∙ = ~ cut⇐L⇒L-vass₂ q r f
cut-cong2 p f eq (⇒L⇐L {q = q} {r}) | 2>R1 (gt q₁ refl eqU refl) with subeq _ _ q q₁ (⊛eq eqU .proj₂)
cut-cong2 {D = D} ._ f refl (⇒L⇐L {A = A} {B} {A'} {B'} {q = q} {r}) | 2>R1 (gt ._ refl refl refl) | 2>L1 (gt q₁ refl refl refl)
  rewrite subeq-2>R1 r (η (B ⇐ A)) (η D) (q ++ (q₁ ◂ η (A' ⇒ B'))) |
          subeq-2>L1 q (η (A' ⇒ B')) (η D) q₁ |
          subeq-2>L1 (r ++ (η (B ⇐ A) ▸ q)) (η (A' ⇒ B')) (η D) q₁ = ⇒L⇐L {r = r}
cut-cong2 ._ f refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>R1 (gt q₁ refl refl refl) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 r (η (B ⇐ A)) (T ⊛ η (A' ⇒ B')) (q ++ (T ▸ ∙)) |
          subeq-2>R1 (r ++ (η (B ⇐ A) ▸ q)) T (η (A' ⇒ B')) ∙ |
          subeq-2>R1 r (η (B ⇐ A)) (η (A' ⇒ B')) (q ++ (T ▸ ∙)) |
          subeq-2>R1 q T (η (A' ⇒ B')) ∙ = cut⇒L⇐L-vass₁ q r f 
cut-cong2 {D = D} ._ f refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2>R1 r (η (B ⇐ A)) (η D) ((q₁ ++ (sub q₂ (T ⊛ η (A' ⇒ B')) ▸ q₃))) |
          subeq-1/\2 q₁ (T ⊛ η (A' ⇒ B')) (η D) q₂ q₃ |
          subeq-1/\2 (r ++ (η (B ⇐ A) ▸ q₁)) (T ⊛ η (A' ⇒ B')) (η D) q₂ q₃ |
          subeq-2>R1 r (η (B ⇐ A)) (η D) ((q₁ ++ (sub q₂ (η B') ▸ q₃))) = ⇒L⇐L {r = r}
cut-cong2 {D = D} ._ f refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2>R1 r (η (B ⇐ A)) (η D) ((q₁ ++ (q₂ ◂ sub q₃ (T ⊛ η (A' ⇒ B'))))) |
          subeq-2/\1 q₁ (T ⊛ η (A' ⇒ B')) (η D) q₂ q₃ |
          subeq-2/\1 (r ++ (η (B ⇐ A) ▸ q₁)) (T ⊛ η (A' ⇒ B')) (η D) q₂ q₃ |
          subeq-2>R1 r (η (B ⇐ A)) (η D) ((q₁ ++ (q₂ ◂ sub q₃ (η B')))) = ⇒L⇐L {r = r}
cut-cong2 {D = D} p f refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (B ⇐ A) ⊛ sub q (T ⊛ η (A' ⇒ B'))) (η D) q₂ q₃ |
          subeq-1/\2 q₁ (T ⊛ η (A' ⇒ B')) (η D) (q₂ ++ (η (B ⇐ A) ▸ q)) q₃ |
          subeq-1/\2 q₁ (η (B ⇐ A) ⊛ sub q (η B')) (η D) q₂ q₃ =  ⇒L⇐L {r = q₁ ++ (q₂ ◂ _)}
cut-cong2 {D = D} p f refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (B ⇐ A) ⊛ sub q (T ⊛ η (A' ⇒ B'))) (η D) q₂ q₃ |
          subeq-2/\1 q₁ (T ⊛ η (A' ⇒ B')) (η D) q₂ (q₃ ++ (η (B ⇐ A) ▸ q)) |
          subeq-2/\1 q₁ (η (B ⇐ A) ⊛ sub q (η B')) (η D) q₂ q₃ = ⇒L⇐L {r = q₁ ++ (_ ▸ q₃)}

cut-cong2 p f eq (⇒L⇐L₂ {p = p₁} {p₂} {p₃}) with subeq _ _ p₁ p eq
cut-cong2 p f eq (⇒L⇐L₂ {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut-cong2 {D = D} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2>L1 (gt q₁ refl refl refl)
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η D) (p₂ ++ (q₁ ◂ η (A ⇒ B))) p₃ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) (η (A ⇒ B)) (η D) q₁ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (η (A ⇒ B)) (η D) q₁ = ⇒L⇐L₂ {p = p₁}
cut-cong2 ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (A ⇒ B)) (p₂ ++ (U ▸ ∙)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) U (η (A ⇒ B)) ∙ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) U (η (A ⇒ B)) ∙  = cut⇒L⇐L-hass₂ p₁ p₂ p₃ f
cut-cong2 {D = D} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η D) (q₁ ++ (sub q₂ (U ⊛ η (A ⇒ B)) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η B'))) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ |
          subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η D) (q₁ ++ (sub q₂ (η B) ▸ q₃)) p₃ = ⇒L⇐L₂ {p = p₁}
cut-cong2 {D = D} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η D) (q₁ ++ (q₂ ◂ sub q₃ (U ⊛ η (A ⇒ B)))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η B'))) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (U ⊛ η (A ⇒ B)) (η D) q₂ q₃ |
          subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η D) (q₁ ++ (q₂ ◂ sub q₃ (η B))) p₃ = ⇒L⇐L₂ {p = p₁}
cut-cong2 p f eq (⇒L⇐L₂ {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut-cong2 ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) V (η (B' ⇐ A')) ∙ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η (B' ⇐ A')) p₂ (p₃ ++ (∙ ◂ V)) |
          subeq-2>L1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) V (η (B' ⇐ A')) ∙ = ~ cut⇐L⇒L-hass₁ p₁ p₂ p₃ f
cut-cong2 {D = D} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2>R1 (gt q₁ refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) (η (B' ⇐ A')) (η D) q₁ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η D) p₂ (p₃ ++ (η (B' ⇐ A') ▸ q₁)) |
          subeq-2>R1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (B' ⇐ A')) (η D) q₁ = ⇒L⇐L₂ {p = p₁}
cut-cong2 {D = D} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q₁)) (η (B' ⇐ A') ⊛ V) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η D) p₂ (q₁ ++ (sub q₂ (η B') ▸ q₃)) |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η D) p₂ (q₁ ++ (sub q₂ (η (B' ⇐ A') ⊛ V) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (B' ⇐ A') ⊛ V) (η D) q₂ q₃ = ⇒L⇐L₂ {p = p₁}
cut-cong2 {D = D} ._ f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ q₁)) (η (B' ⇐ A') ⊛ V) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η B'))) |
          subeq-1/\2 p₁ (U ⊛ η (A ⇒ B)) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (B' ⇐ A') ⊛ V))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (B' ⇐ A') ⊛ V) (η D) q₂ q₃ = ⇒L⇐L₂ {p = p₁}
cut-cong2 {D = D} p f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (η (B' ⇐ A') ⊛ V) (η D) (q₁ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η D) (q₁ ++ (p₂ ◂ sub p₃ (η B'))) q₂ |
          subeq-1/\2 q (U ⊛ η (A ⇒ B)) (η D) (q₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) q₂ |
          subeq-1/\2 q (η (B' ⇐ A') ⊛ V) (η D) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = ⇒L⇐L₂ {p = q ++ (q₁ ◂ _)}
cut-cong2 {D = D} p f refl (⇒L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B' ⇐ A') ⊛ V) (η D) q₁ (q₂ ++ (sub p₂ (U ⊛ η (A ⇒ B)) ▸ p₃)) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B'))) |
          subeq-2/\1 q (U ⊛ η (A ⇒ B)) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) |
          subeq-2/\1 q (η (B' ⇐ A') ⊛ V) (η D) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = ⇒L⇐L₂ {p = q ++ (_ ▸ q₂)}

cut-cong2 p f eq (⇐L⇒L {q = q} {r}) with subeq _ _ r p eq
cut-cong2 p f eq (⇐L⇒L {q = q} {r}) | 2>L1 (gt q₁ refl eqU refl) with subeq _ _ q q₁ (⊛eq eqU .proj₁)
cut-cong2 ._ f refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>L1 (gt q₁ refl refl refl) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 r (η (A ⇒ B)) (η (B' ⇐ A') ⊛ T) (q ++ (∙ ◂ T)) |
          subeq-2>L1 (r ++ (q ◂ η (A ⇒ B))) T (η (B' ⇐ A')) ∙ |
          subeq-2>L1 r (η (A ⇒ B)) (η (B' ⇐ A')) (q ++ (∙ ◂ T)) |
          subeq-2>L1 q T (η (B' ⇐ A')) ∙ = cut⇐L⇒L-vass₁ q r f
cut-cong2 {D = D} ._ f refl (⇐L⇒L {A = A} {B} {A'} {B'} {q = q} {r}) | 2>L1 (gt ._ refl refl refl) | 2>R1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 r (η (A ⇒ B)) (η D) (q ++ (η (B' ⇐ A') ▸ q₁)) |
          subeq-2>R1 q (η (B' ⇐ A')) (η D) q₁ |
          subeq-2>R1 (r ++ (q ◂ η (A ⇒ B))) (η (B' ⇐ A')) (η D) q₁ = ⇐L⇒L {r = r}
cut-cong2 {D = D} ._ f refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>L1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2>L1 r (η (A ⇒ B)) (η D) ((q₁ ++ (sub q₂ (η (B' ⇐ A') ⊛ T) ▸ q₃))) |
          subeq-1/\2 q₁ (η (B' ⇐ A') ⊛ T) (η D) q₂ q₃ |
          subeq-1/\2 (r ++ (q₁ ◂ η (A ⇒ B))) (η (B' ⇐ A') ⊛ T) (η D) q₂ q₃ |
          subeq-2>L1 r (η (A ⇒ B)) (η D) ((q₁ ++ (sub q₂ (η B') ▸ q₃))) = ⇐L⇒L {r = r}
cut-cong2 {D = D} ._ f refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>L1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2>L1 r (η (A ⇒ B)) (η D) ((q₁ ++ (q₂ ◂ sub q₃ (η (B' ⇐ A') ⊛ T)))) |
          subeq-2/\1 q₁ (η (B' ⇐ A') ⊛ T) (η D) q₂ q₃ |
          subeq-2/\1 (r ++ (q₁ ◂ η (A ⇒ B))) (η (B' ⇐ A') ⊛ T) (η D) q₂ q₃ |
          subeq-2>L1 r (η (A ⇒ B)) (η D) ((q₁ ++ (q₂ ◂ sub q₃ (η B')))) = ⇐L⇒L {r = r}
cut-cong2 p f refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 r (sub q (η (B' ⇐ A') ⊛ T)) (η (A ⇒ B)) ∙ |
          subeq-1/\2 r (η (B' ⇐ A') ⊛ T) (η (A ⇒ B)) q ∙ |
          subeq-2>R1 r (sub q (η B')) (η (A ⇒ B)) ∙ = ~ cut⇒L⇐L-vass₂ q r f
cut-cong2 {D = D} p f refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (sub q (η (B' ⇐ A') ⊛ T) ⊛ η (A ⇒ B)) (η D) q₂ q₃ |
          subeq-1/\2 q₁ (η (B' ⇐ A') ⊛ T) (η D) (q₂ ++ (q ◂ η (A ⇒ B))) q₃ |
          subeq-1/\2 q₁ (sub q (η B') ⊛ η (A ⇒ B)) (η D) q₂ q₃ = ⇐L⇒L {r = q₁ ++ (q₂ ◂ _)}
cut-cong2 {D = D} p f refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (sub q (η (B' ⇐ A') ⊛ T) ⊛ η (A ⇒ B)) (η D) q₂ q₃ |
          subeq-2/\1 q₁ (η (B' ⇐ A') ⊛ T) (η D) q₂ (q₃ ++ (q ◂ η (A ⇒ B))) |
          subeq-2/\1 q₁ (sub q (η B') ⊛ η (A ⇒ B)) (η D) q₂ q₃ = ⇐L⇒L {r = q₁ ++ (_ ▸ q₃)}

cut-cong2 p f eq (⇐L⇒L₂ {p = p₁} {p₂} {p₃}) with subeq _ _ p₁ p eq
cut-cong2 p f eq (⇐L⇒L₂ {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut-cong2 ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (B ⇐ A)) (p₂ ++ (∙ ◂ U)) p₃ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) U (η (B ⇐ A)) ∙ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) U (η (B ⇐ A)) ∙  = cut⇐L⇒L-hass₂ p₁ p₂ p₃ f
cut-cong2 {D = D} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2>R1 (gt q₁ refl refl refl)
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η D) (p₂ ++ (η (B ⇐ A) ▸ q₁)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) (η (B ⇐ A)) (η D) q₁ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (η (B ⇐ A)) (η D) q₁ = ⇐L⇒L₂ {p = p₁}
cut-cong2 {D = D} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η D) (q₁ ++ (sub q₂ (η (B ⇐ A) ⊛ U) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η B'))) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ |
          subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η D) (q₁ ++ (sub q₂ (η B) ▸ q₃)) p₃ = ⇐L⇒L₂ {p = p₁}
cut-cong2 {D = D} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η D) (q₁ ++ (q₂ ◂ sub q₃ (η (B ⇐ A) ⊛ U))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η B'))) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ |
          subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η D) (q₁ ++ (q₂ ◂ sub q₃ (η B))) p₃ = ⇐L⇒L₂ {p = p₁}
cut-cong2 p f eq (⇐L⇒L₂ {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut-cong2 {D = D} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2>L1 (gt q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) (η (A' ⇒ B')) (η D) q₁ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η D) p₂ (p₃ ++ (q₁ ◂ η (A' ⇒ B'))) |
          subeq-2>L1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (A' ⇒ B')) (η D) q₁ = ⇐L⇒L₂ {p = p₁}
cut-cong2 ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2>R1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) V (η (A' ⇒ B')) ∙ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (A' ⇒ B')) p₂ (p₃ ++ (V ▸ ∙)) |
          subeq-2>R1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) V (η (A' ⇒ B')) ∙ = ~ cut⇒L⇐L-hass₁ p₁ p₂ p₃ f
cut-cong2 {D = D} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q₁)) (V ⊛ η (A' ⇒ B')) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η D) p₂ (q₁ ++ (sub q₂ (η B') ▸ q₃)) |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η D) p₂ (q₁ ++ (sub q₂ (V ⊛ η (A' ⇒ B')) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (V ⊛ η (A' ⇒ B')) (η D) q₂ q₃ = ⇐L⇒L₂ {p = p₁}
cut-cong2 {D = D} ._ f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q₁)) (V ⊛ η (A' ⇒ B')) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η B'))) |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (V ⊛ η (A' ⇒ B')))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (V ⊛ η (A' ⇒ B')) (η D) q₂ q₃ = ⇐L⇒L₂ {p = p₁}
cut-cong2 {D = D} p f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (V ⊛ η (A' ⇒ B')) (η D) (q₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η D) (q₁ ++ (p₂ ◂ sub p₃ (η B'))) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η D) (q₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) q₂ |
          subeq-1/\2 q (V ⊛ η (A' ⇒ B')) (η D) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = ⇐L⇒L₂ {p = q ++ (q₁ ◂ _)}
cut-cong2 {D = D} p f refl (⇐L⇒L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (V ⊛ η (A' ⇒ B')) (η D) q₁ (q₂ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B'))) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) |
          subeq-2/\1 q (V ⊛ η (A' ⇒ B')) (η D) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = ⇐L⇒L₂ {p = q ++ (_ ▸ q₂)}

cut-cong2 p f eq (⇐L⇐L {q = q} {r}) with subeq _ _ r p eq
cut-cong2 p f refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 r (sub q (η (B' ⇐ A') ⊛ T)) (η (B ⇐ A)) ∙ |
          subeq-2/\1 r (η (B' ⇐ A') ⊛ T) (η (B ⇐ A)) ∙ q |
          subeq-2>L1 r (sub q (η B')) (η (B ⇐ A)) ∙ = ~ cut⇐L⇐L-vass₂ q r f
cut-cong2 p f eq (⇐L⇐L {q = q} {r}) | 2>R1 (gt q₁ refl eqU refl) with subeq _ _ q q₁ (⊛eq eqU .proj₂)
cut-cong2 ._ f refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>R1 (gt q₁ refl refl refl) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>R1 r (η (B ⇐ A)) (η (B' ⇐ A') ⊛ T) (q ++ (∙ ◂ T)) |
          subeq-2>L1 (r ++ (η (B ⇐ A) ▸ q)) T (η (B' ⇐ A')) ∙ |
          subeq-2>R1 r (η (B ⇐ A)) (η (B' ⇐ A')) (q ++ (∙ ◂ T)) |
          subeq-2>L1 q T (η (B' ⇐ A')) ∙ = cut⇐L⇐L-vass₁ q r f
cut-cong2 {D = D} ._ f refl (⇐L⇐L {A = A} {B} {A'} {B'} {q = q} {r}) | 2>R1 (gt ._ refl refl refl) | 2>R1 (gt q₁ refl refl refl) 
  rewrite subeq-2>R1 r (η (B ⇐ A)) (η D) (q ++ (η (B' ⇐ A') ▸ q₁)) |
          subeq-2>R1 q (η (B' ⇐ A')) (η D) q₁ |
          subeq-2>R1 (r ++ (η (B ⇐ A) ▸ q)) (η (B' ⇐ A')) (η D) q₁ = ⇐L⇐L {r = r}
cut-cong2 {D = D} ._ f refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>R1 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2>R1 r (η (B ⇐ A)) (η D) ((q₁ ++ (sub q₂ (η (B' ⇐ A') ⊛ T) ▸ q₃))) |
          subeq-1/\2 q₁ (η (B' ⇐ A') ⊛ T) (η D) q₂ q₃ |
          subeq-1/\2 (r ++ (η (B ⇐ A) ▸ q₁)) (η (B' ⇐ A') ⊛ T) (η D) q₂ q₃ |
          subeq-2>R1 r (η (B ⇐ A)) (η D) ((q₁ ++ (sub q₂ (η B') ▸ q₃))) = ⇐L⇐L {r = r}
cut-cong2 {D = D} ._ f refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 2>R1 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2>R1 r (η (B ⇐ A)) (η D) ((q₁ ++ (q₂ ◂ sub q₃ (η (B' ⇐ A') ⊛ T)))) |
          subeq-2/\1 q₁ (η (B' ⇐ A') ⊛ T) (η D) q₂ q₃ |
          subeq-2/\1 (r ++ (η (B ⇐ A) ▸ q₁)) (η (B' ⇐ A') ⊛ T) (η D) q₂ q₃ |
          subeq-2>R1 r (η (B ⇐ A)) (η D) ((q₁ ++ (q₂ ◂ sub q₃ (η B')))) = ⇐L⇐L {r = r}
cut-cong2 {D = D} p f refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ (η (B ⇐ A) ⊛ sub q (η (B' ⇐ A') ⊛ T)) (η D) q₂ q₃ |
          subeq-1/\2 q₁ (η (B' ⇐ A') ⊛ T) (η D) (q₂ ++ (η (B ⇐ A) ▸ q)) q₃ |
          subeq-1/\2 q₁ (η (B ⇐ A) ⊛ sub q (η B')) (η D) q₂ q₃ = ⇐L⇐L {r = q₁ ++ (q₂ ◂ _)}
cut-cong2 {D = D} p f refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ (η (B ⇐ A) ⊛ sub q (η (B' ⇐ A') ⊛ T)) (η D) q₂ q₃ |
          subeq-2/\1 q₁ (η (B' ⇐ A') ⊛ T) (η D) q₂ (q₃ ++ (η (B ⇐ A) ▸ q)) |
          subeq-2/\1 q₁ (η (B ⇐ A) ⊛ sub q (η B')) (η D) q₂ q₃ =  ⇐L⇐L {r = q₁ ++ (_ ▸ q₃)}

cut-cong2 p f eq (⇐L⇐L₂ {p = p₁} {p₂} {p₃}) with subeq _ _ p₁ p eq
cut-cong2 p f eq (⇐L⇐L₂ {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl eqU refl) with subeq _ _ p₂ q (⊛eq eqU .proj₁)
cut-cong2 ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (B ⇐ A)) (p₂ ++ (∙ ◂ U)) p₃ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) U (η (B ⇐ A)) ∙ |
          subeq-2>L1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) U (η (B ⇐ A)) ∙  = cut⇐L⇐L-hass₂ p₁ p₂ p₃ f
cut-cong2 {D = D} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2>R1 (gt q₁ refl refl refl)
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η D) (p₂ ++ (η (B ⇐ A) ▸ q₁)) p₃ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η B'))) (η (B ⇐ A)) (η D) q₁ |
          subeq-2>R1 (p₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (η (B ⇐ A)) (η D) q₁ = ⇐L⇐L₂ {p = p₁}
cut-cong2 {D = D} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η D) (q₁ ++ (sub q₂ (η (B ⇐ A) ⊛ U) ▸ q₃)) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η B'))) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ |
          subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η D) (q₁ ++ (sub q₂ (η B) ▸ q₃)) p₃ = ⇐L⇐L₂ {p = p₁}
cut-cong2 {D = D} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>L1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η D) (q₁ ++ (q₂ ◂ sub q₃ (η (B ⇐ A) ⊛ U))) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η B'))) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (η (B ⇐ A) ⊛ U) (η D) q₂ q₃ |
          subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η D) (q₁ ++ (q₂ ◂ sub q₃ (η B))) p₃ = ⇐L⇐L₂ {p = p₁}
cut-cong2 p f eq (⇐L⇐L₂ {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl eqU refl) with subeq _ _ p₃ q (⊛eq eqU .proj₂)
cut-cong2 ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2>L1 (gt ∙ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) V (η (B' ⇐ A')) ∙ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η (B' ⇐ A')) p₂ (p₃ ++ (∙ ◂ V)) |
          subeq-2>L1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) V (η (B' ⇐ A')) ∙ = ~ cut⇐L⇐L-hass₁ p₁ p₂ p₃ f
cut-cong2 {D = D} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2>R1 (gt q₁ refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) (η (B' ⇐ A')) (η D) q₁ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η D) p₂ (p₃ ++ (η (B' ⇐ A') ▸ q₁)) |
          subeq-2>R1 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (B' ⇐ A')) (η D) q₁ = ⇐L⇐L₂ {p = p₁}
cut-cong2 {D = D} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q₁)) (η (B' ⇐ A') ⊛ V) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η D) p₂ (q₁ ++ (sub q₂ (η B') ▸ q₃)) |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η D) p₂ (q₁ ++ (sub q₂ (η (B' ⇐ A') ⊛ V) ▸ q₃)) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (B' ⇐ A') ⊛ V) (η D) q₂ q₃ = ⇐L⇐L₂ {p = p₁}
cut-cong2 {D = D} ._ f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2>R1 (gt q refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ q₁)) (η (B' ⇐ A') ⊛ V) (η D) q₂ q₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η B'))) |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U) (η D) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (B' ⇐ A') ⊛ V))) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q₁)) (η (B' ⇐ A') ⊛ V) (η D) q₂ q₃ = ⇐L⇐L₂ {p = p₁}
cut-cong2 {D = D} p f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q (η (B' ⇐ A') ⊛ V) (η D) (q₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η D) (q₁ ++ (p₂ ◂ sub p₃ (η B'))) q₂ |
          subeq-1/\2 q (η (B ⇐ A) ⊛ U) (η D) (q₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) q₂ |
          subeq-1/\2 q (η (B' ⇐ A') ⊛ V) (η D) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = ⇐L⇐L₂ {p = q ++ (q₁ ◂ _)}
cut-cong2 {D = D} p f refl (⇐L⇐L₂ {U = U} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q (η (B' ⇐ A') ⊛ V) (η D) q₁ (q₂ ++ (sub p₂ (η (B ⇐ A) ⊛ U) ▸ p₃)) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B'))) |
          subeq-2/\1 q (η (B ⇐ A) ⊛ U) (η D) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) |
          subeq-2/\1 q (η (B' ⇐ A') ⊛ V) (η D) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = ⇐L⇐L₂ {p = q ++ (_ ▸ q₂)}

cut-cong2 p f refl refl = refl
cut-cong2 p f refl (~ eq') = ~ cut-cong2 p f refl eq'
cut-cong2 p f refl (eq' ∘ eq'') = cut-cong2 p f refl eq' ∘ cut-cong2 p f refl eq''
cut-cong2 p f refl (⇒R eq') = ⇒R (cut-cong2 (η _ ▸ p) f refl eq')
cut-cong2 p f refl (⇐R eq') = ⇐R (cut-cong2 (p ◂ η _) f refl eq')
