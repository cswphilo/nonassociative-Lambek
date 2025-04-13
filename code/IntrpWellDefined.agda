{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefined where

open import Relation.Binary.PropositionalEquality hiding ([_]; _≗_) 
open import Data.Product 
open import Fma
open import SeqCalc
open import Interpolation
open import SubEqProperties

module _ (T : Tree) (p : Path T) (U : Tree) (C : Fma) (m m' : MIP T p U C) where
  open MIP m 
  open MIP m' renaming (D to D'; g to g'; h to h')
  
  record MIP≗ : Set where
    constructor intrp≗
    field
      eqD : D ≡ D'
      eqg : subst-cxt (cong (λ x → sub p (η x)) eqD) g ≗ g'
      eqh : subst-succ eqD h ≗ h'

mip≗ : ∀ {T} (p : Path T) U {V C} {f f' : V ⊢ C}  
  → (eq₁ : V ≡ sub p U) 
  → (eq₂ : f ≗ f')
  → MIP≗ T p U C (mip p U f eq₁) (mip p U f' eq₁)

mip≗ p U {f = f} {f'} eq₁ (_∘_ eq₂ eq₃) with mip p U f eq₁ | mip p U f' eq₁ | mip≗ p U eq₁ eq₂ | mip≗ p U eq₁ eq₃
... | intrp ._ g h | intrp ._ g' h' | intrp≗ refl eqg eqh | intrp≗ refl eqg' eqh' = 
  intrp≗ refl (eqg ∘ eqg') (eqh ∘ eqh')
mip≗ p U refl (⇒R {f = f} {f'} eq₂) with mip (_ ▸ p) U f refl | mip (_ ▸ p) U f' refl | mip≗ (_ ▸ p) U refl eq₂
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = intrp≗ refl (⇒R eqg) eqh
mip≗ p U refl (⇐R {f = f} {f'} eq₂) with mip (p ◂ _) U f refl | mip (p ◂ _) U f' refl | mip≗ (p ◂ _) U refl eq₂
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = intrp≗ refl (⇐R eqg) eqh
mip≗ p U eq₁ (⇒L {U = U₁} {A} {B} {p = p₁}  eq₂ eq₃) with subeq U (U₁ ⊛ η (A ⇒ B)) p p₁ (sym eq₁)
mip≗ p ._ refl (⇒L {g = k} {k'} eq₂ eq₃) | 1≡2 (same refl refl refl) with mip p (η _) k refl | mip p (η _) k' refl | mip≗ p (η _) refl eq₃  
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = 
  intrp≗ refl eqg (⇒L eq₂ eqh)
mip≗ p ._ refl (⇒L {g = k} {k'} eq₂ eq₃) | 2>L1 (gt q refl refl refl) with mip p (sub q (η _) ⊛ _) k refl | mip p (sub q (η _) ⊛ _) k' refl | mip≗ p (sub q (η _) ⊛ _) refl eq₃
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = 
  intrp≗ refl eqg (⇒L eq₂ eqh) 
mip≗ p ._ eq₁ (⇒L {g = k} {k'} eq₂ eq₃) | 2>R1 (gt q refl refl refl) with mip p (_ ⊛ sub q (η _)) k refl | mip p (_ ⊛ sub q (η _)) k' refl | mip≗ p (_ ⊛ sub q (η _)) refl eq₃
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = 
  intrp≗ refl eqg (⇒L eq₂ eqh) 
mip≗ ._ U refl (⇒L {f = k} {k'} eq₂ eq₃) | 1>L2 (gt q refl refl refl) with mip q U k refl | mip q U k' refl | mip≗ q U refl eq₂
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = 
  intrp≗ refl (⇒L eqg eq₃) eqh
mip≗ ._ ._ refl (⇒L {U = U} {p = p} {f} {f'} {k} {k'} eq₂ eq₃) | 1>R2 (gt ∙ refl refl refl) with mip ∙ U f refl | mip ∙ U f' refl | mip p (η _) k refl | mip p (η _) k' refl | mip≗ ∙ U refl eq₂ | mip≗ p (η _) refl eq₃
... | intrp D g h | intrp .D g' h' | intrp E g₁ h₁ | intrp .E g₁' h₁' | intrp≗ refl eqg eqh | intrp≗ refl eqg₁ eqh₁ = intrp≗ refl (⇒L eqh eqg₁) (⇒R (⇒L eqg eqh₁)) -- A ⇒ B is the interpolant formula
mip≗ ._ U refl (⇒L {g = k} {k'} eq₂ eq₃) | 1/\2 (disj q q₁ q₂ refl refl refl refl) with mip (q ++ (q₁ ◂ sub q₂ (η _))) U k refl | mip (q ++ (q₁ ◂ sub q₂ (η _))) U k' refl | mip≗ (q ++ (q₁ ◂ sub q₂ (η _))) U refl eq₃
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = 
  intrp≗ refl (⇒L eq₂ eqg) eqh
mip≗ ._ U refl (⇒L {g = k} {k'} eq₂ eq₃) | 2/\1 (disj q q₁ q₂ refl refl refl refl) with mip (q ++ (sub q₁ (η _) ▸ q₂)) U k refl | mip (q ++ (sub q₁ (η _) ▸ q₂)) U k' refl | mip≗ (q ++ (sub q₁ (η _) ▸ q₂)) U refl eq₃ 
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = 
  intrp≗ refl (⇒L eq₂ eqg) eqh

mip≗ p U eq₁ (⇐L {U = U₁} {A} {B} {p = p₁} eq₂ eq₃) with subeq U (η (B ⇐ A) ⊛ U₁) p p₁ (sym eq₁)
mip≗ p ._ refl (⇐L {g = k} {k'} eq₂ eq₃) | 1≡2 (same refl refl refl) with mip p (η _) k refl | mip p (η _) k' refl | mip≗ p (η _) refl eq₃  
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = 
  intrp≗ refl eqg (⇐L eq₂ eqh)
mip≗ p ._ refl (⇐L {g = k} {k'} eq₂ eq₃) | 2>L1 (gt q refl refl refl) with mip p (sub q (η _) ⊛ _) k refl | mip p (sub q (η _) ⊛ _) k' refl | mip≗ p (sub q (η _) ⊛ _) refl eq₃
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = 
  intrp≗ refl eqg (⇐L eq₂ eqh) 
mip≗ p ._ eq₁ (⇐L {g = k} {k'} eq₂ eq₃) | 2>R1 (gt q refl refl refl) with mip p (_ ⊛ sub q (η _)) k refl | mip p (_ ⊛ sub q (η _)) k' refl | mip≗ p (_ ⊛ sub q (η _)) refl eq₃
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = 
  intrp≗ refl eqg (⇐L eq₂ eqh) 
mip≗ ._ ._ refl (⇐L {U = U} {p = p} {f} {f'} {k} {k'} eq₂ eq₃) | 1>L2 (gt ∙ refl refl refl) with mip ∙ U f refl | mip ∙ U f' refl | mip p (η _) k refl | mip p (η _) k' refl | mip≗ ∙ U refl eq₂ | mip≗ p (η _) refl eq₃
... | intrp D g h | intrp .D g' h' | intrp E g₁ h₁ | intrp .E g₁' h₁' | intrp≗ refl eqg eqh | intrp≗ refl eqg₁ eqh₁ = intrp≗ refl (⇐L eqh eqg₁) (⇐R (⇐L eqg eqh₁)) -- A ⇐ B is the interpolant formula
mip≗ ._ U refl (⇐L {f = k} {k'} eq₂ eq₃) | 1>R2 (gt q refl refl refl) with mip q U k refl | mip q U k' refl | mip≗ q U refl eq₂
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = 
  intrp≗ refl (⇐L eqg eq₃) eqh
mip≗ ._ U refl (⇐L {g = k} {k'} eq₂ eq₃) | 1/\2 (disj q q₁ q₂ refl refl refl refl) with mip (q ++ (q₁ ◂ sub q₂ (η _))) U k refl | mip (q ++ (q₁ ◂ sub q₂ (η _))) U k' refl | mip≗ (q ++ (q₁ ◂ sub q₂ (η _))) U refl eq₃
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = 
  intrp≗ refl (⇐L eq₂ eqg) eqh
mip≗ ._ U refl (⇐L {g = k} {k'} eq₂ eq₃) | 2/\1 (disj q q₁ q₂ refl refl refl refl) with mip (q ++ (sub q₁ (η _) ▸ q₂)) U k refl | mip (q ++ (sub q₁ (η _) ▸ q₂)) U k' refl | mip≗ (q ++ (sub q₁ (η _) ▸ q₂)) U refl eq₃ 
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = 
  intrp≗ refl (⇐L eq₂ eqg) eqh
mip≗ ∙ ._ refl (⊗R {f = f} {f'} {k} {k'} eq₂ eq₃) with mip ∙ _ f refl | mip ∙ _ k refl | mip ∙ _ f' refl | mip ∙ _ k' refl | mip≗ ∙ _ refl eq₂ | mip≗ ∙ _ refl eq₃
... | intrp D g h | intrp E g' h' | intrp .D g'' h'' | intrp .E g''' h''' | intrp≗ refl eqg eqh | intrp≗ refl eqg' eqh' = 
  intrp≗ refl (⊗L (⊗R eqg eqg')) (⊗R eqh eqh') 
mip≗ (p ◂ U₁) U refl (⊗R {f = f} {f'} eq₂ eq₃) with mip p U f refl | mip p U f' refl | mip≗ p _ refl eq₂
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = 
  intrp≗ refl (⊗R eqg eq₃) eqh 
mip≗ (T ▸ p) U refl (⊗R {g = k} {k'} eq₂ eq₃) with mip p U k refl | mip p U k' refl | mip≗ p _ refl eq₃
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = 
  intrp≗ refl (⊗R eq₂ eqg) eqh 
mip≗ p U eq₁ (⊗L {p = p₁} eq) with subeq _ _ p p₁ (sym eq₁)
mip≗ p ._ refl (⊗L  {f = f} {f'} eq) | 1≡2 (same refl refl refl) with mip p _ f refl | mip p _ f' refl | mip≗ p _ refl eq
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = 
  intrp≗ refl eqg (⊗L eqh) 
mip≗ p ._ refl (⊗L {f = f} {f'} eq) | 2>L1 (gt q refl refl refl) with mip p _ f refl | mip p _ f' refl | mip≗ p _ refl eq
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = 
  intrp≗ refl eqg (⊗L eqh)
mip≗ p ._ refl (⊗L {f = f} {f'} eq) | 2>R1 (gt q refl refl refl) with mip p _ f refl | mip p _ f' refl | mip≗ p _ refl eq
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = 
  intrp≗ refl eqg (⊗L eqh)
mip≗ ._ U refl (⊗L {p = p} {f} {f'} eq) | 1/\2 (disj q q₁ q₂ refl refl refl refl) with mip (q ++ (q₁ ◂ sub q₂ (η _ ⊛ η _))) _ f refl | mip (q ++ (q₁ ◂ sub q₂ (η _ ⊛ η _))) _ f' refl | mip≗ (q ++ (q₁ ◂ sub q₂ (η _ ⊛ η _))) _ refl eq
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = 
  intrp≗ refl (⊗L eqg) eqh
mip≗ ._ U refl (⊗L {p = p} {f} {f'} eq) | 2/\1 (disj q q₁ q₂ refl refl refl refl) with mip (q ++ (sub q₁ (η _ ⊛ η _) ▸ q₂)) _ f refl | mip (q ++ (sub q₁ (η _ ⊛ η _) ▸ q₂)) _ f' refl | mip≗ (q ++ (sub q₁ (η _ ⊛ η _) ▸ q₂)) _ refl eq
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = 
  intrp≗ refl (⊗L eqg) eqh
mip≗ p U eq₁ (⇒L⇒R {U = U₁} {A = A} {B} {p = p₁}) with subeq U (U₁ ⊛ η (A ⇒ B)) p p₁ (sym eq₁)
mip≗ p .(_ ⊛ η (_ ⇒ _)) refl (⇒L⇒R {U = U} {A} {B}) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p (U ⊛ η (A ⇒ B)) = 
    intrp≗ refl refl refl
mip≗ p ._ refl (⇒L⇒R {U = U} {A} {B}) | 2>L1 (gt {W₂ = W₂} q refl refl refl) rewrite subeq-2>L1 p W₂ (U ⊛ (η (A ⇒ B))) q = 
  intrp≗ refl refl refl
mip≗ p ._ refl (⇒L⇒R {U = U} {A} {B}) | 2>R1 (gt {W₁} q refl refl refl) 
  rewrite subeq-2>R1 p W₁ (U ⊛ η (A ⇒ B)) q = 
    intrp≗ refl refl refl
mip≗ ._ U refl (⇒L⇒R {A = A} {B} {p = p₁}) | 1>L2 (gt q refl refl refl) rewrite subeq-1>L2 p₁ (η (A ⇒ B)) U q = 
  intrp≗ refl ⇒L⇒R refl
mip≗ ._ ._ refl (⇒L⇒R {U = U} {A} {B} {p = p}) | 1>R2 (gt ∙ refl refl refl) rewrite subeq-1>R2 p U (η (A ⇒ B)) ∙ = 
  intrp≗ refl ⇒L⇒R refl
mip≗ ._ U refl (⇒L⇒R {U = U₁} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) rewrite subeq-1/\2 q U (U₁ ⊛ η (A ⇒ B)) q₁ q₂ = 
  intrp≗ refl ⇒L⇒R refl
mip≗ ._ U refl (⇒L⇒R {U = U₁} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite  subeq-2/\1 q U (U₁ ⊛ η (A ⇒ B)) q₁ q₂ = 
    intrp≗ refl ⇒L⇒R refl
mip≗ p U eq₁ (⇐L⇒R {U = U₁} {A = A} {B} {p = p₁}) with subeq U (η (B ⇐ A) ⊛ U₁) p p₁ (sym eq₁)
mip≗ p ._ refl (⇐L⇒R {U = U} {A} {B}) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p (η (B ⇐ A) ⊛ U) = 
    intrp≗ refl refl refl
mip≗ p ._ refl (⇐L⇒R {U = U} {A} {B}) | 2>L1 (gt {W₂ = W₂} q refl refl refl) rewrite subeq-2>L1 p W₂ (η (B ⇐ A) ⊛ U) q = 
  intrp≗ refl refl refl
mip≗ p ._ refl (⇐L⇒R {U = U} {A} {B}) | 2>R1 (gt {W₁} q refl refl refl) 
  rewrite subeq-2>R1 p W₁ (η (B ⇐ A) ⊛ U) q = 
    intrp≗ refl refl refl
mip≗ ._ ._ refl (⇐L⇒R {U = U} {A} {B} {p = p₁}) | 1>L2 (gt ∙ refl refl refl) rewrite subeq-1>L2 p₁ U (η (B ⇐ A)) ∙ = 
  intrp≗ refl ⇐L⇒R refl
mip≗ ._ U refl (⇐L⇒R {A = A} {B} {p = p}) | 1>R2 (gt q refl refl refl) rewrite subeq-1>R2 p (η (B ⇐ A)) U q =
  intrp≗ refl ⇐L⇒R refl
mip≗ ._ U refl (⇐L⇒R {U = U₁} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) rewrite subeq-1/\2 q U (η (B ⇐ A) ⊛ U₁) q₁ q₂ = 
  intrp≗ refl ⇐L⇒R refl
mip≗ ._ U refl (⇐L⇒R {U = U₁} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite  subeq-2/\1 q U (η (B ⇐ A) ⊛ U₁) q₁ q₂ = 
    intrp≗ refl ⇐L⇒R refl
mip≗ p U eq₁ (⊗L⇒R {A = A} {B} {p = p₁}) with subeq U (η (A ⊗ B)) p p₁ (sym eq₁) -- there are no 1>2 cases since A ⊗ B is just a node!
mip≗ p .(η (_ ⊗ _)) refl (⊗L⇒R {A = A} {B}) | 1≡2 (same refl refl refl) rewrite subeq-1≡2 p (η (A ⊗ B)) = 
  intrp≗ refl refl refl
mip≗ p ._ refl (⊗L⇒R {A = A} {B}) | 2>L1 (gt {W₂ = W₂} q refl refl refl) rewrite subeq-2>L1 p W₂ (η (A ⊗ B)) q = 
  intrp≗ refl refl refl
mip≗ p ._ refl (⊗L⇒R {A = A} {B} ) | 2>R1 (gt {W₁} q refl refl refl) rewrite subeq-2>R1 p W₁ (η (A ⊗ B)) q = 
  intrp≗ refl refl refl
mip≗ ._ U refl (⊗L⇒R {A = A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) rewrite subeq-1/\2 q U (η (A ⊗ B)) q₁ q₂ = 
  intrp≗ refl ⊗L⇒R refl
mip≗ ._ U refl (⊗L⇒R {A = A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) rewrite subeq-2/\1 q U (η (A ⊗ B)) q₁ q₂ = 
  intrp≗ refl ⊗L⇒R refl
mip≗ p U eq₁ (⇒L⇐R {U = U₁} {A = A} {B} {p = p₁}) with subeq U (U₁ ⊛ η (A ⇒ B)) p p₁ (sym eq₁)
mip≗ p .(_ ⊛ η (_ ⇒ _)) refl (⇒L⇐R {U = U} {A} {B}) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p (U ⊛ η (A ⇒ B)) = 
    intrp≗ refl refl refl
mip≗ p ._ refl (⇒L⇐R {U = U} {A} {B}) | 2>L1 (gt {W₂ = W₂} q refl refl refl) rewrite subeq-2>L1 p W₂ (U ⊛ (η (A ⇒ B))) q = 
  intrp≗ refl refl refl
mip≗ p ._ refl (⇒L⇐R {U = U} {A} {B}) | 2>R1 (gt {W₁} q refl refl refl) 
  rewrite subeq-2>R1 p W₁ (U ⊛ η (A ⇒ B)) q = 
    intrp≗ refl refl refl
mip≗ ._ U refl (⇒L⇐R {A = A} {B} {p = p₁}) | 1>L2 (gt q refl refl refl) rewrite subeq-1>L2 p₁ (η (A ⇒ B)) U q = 
  intrp≗ refl ⇒L⇐R refl
mip≗ ._ ._ refl (⇒L⇐R {U = U} {A} {B} {p = p}) | 1>R2 (gt ∙ refl refl refl) rewrite subeq-1>R2 p U (η (A ⇒ B)) ∙ = 
  intrp≗ refl ⇒L⇐R refl
mip≗ ._ U refl (⇒L⇐R {U = U₁} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) rewrite subeq-1/\2 q U (U₁ ⊛ η (A ⇒ B)) q₁ q₂ = 
  intrp≗ refl ⇒L⇐R refl
mip≗ ._ U refl (⇒L⇐R {U = U₁} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite  subeq-2/\1 q U (U₁ ⊛ η (A ⇒ B)) q₁ q₂ = 
    intrp≗ refl ⇒L⇐R refl
mip≗ p U eq₁ (⇐L⇐R {U = U₁} {A = A} {B} {p = p₁}) with subeq U (η (B ⇐ A) ⊛ U₁) p p₁ (sym eq₁)
mip≗ p ._ refl (⇐L⇐R {U = U} {A} {B}) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p (η (B ⇐ A) ⊛ U) = 
    intrp≗ refl refl refl
mip≗ p ._ refl (⇐L⇐R {U = U} {A} {B}) | 2>L1 (gt {W₂ = W₂} q refl refl refl) rewrite subeq-2>L1 p W₂ (η (B ⇐ A) ⊛ U) q = 
  intrp≗ refl refl refl
mip≗ p ._ refl (⇐L⇐R {U = U} {A} {B}) | 2>R1 (gt {W₁} q refl refl refl) 
  rewrite subeq-2>R1 p W₁ (η (B ⇐ A) ⊛ U) q = 
    intrp≗ refl refl refl
mip≗ ._ ._ refl (⇐L⇐R {U = U} {A} {B} {p = p₁}) | 1>L2 (gt ∙ refl refl refl) rewrite subeq-1>L2 p₁ U (η (B ⇐ A)) ∙ = 
  intrp≗ refl ⇐L⇐R refl
mip≗ ._ U refl (⇐L⇐R {A = A} {B} {p = p}) | 1>R2 (gt q refl refl refl) rewrite subeq-1>R2 p (η (B ⇐ A)) U q =
  intrp≗ refl ⇐L⇐R refl
mip≗ ._ U refl (⇐L⇐R {U = U₁} {A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) rewrite subeq-1/\2 q U (η (B ⇐ A) ⊛ U₁) q₁ q₂ = 
  intrp≗ refl ⇐L⇐R refl
mip≗ ._ U refl (⇐L⇐R {U = U₁} {A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite  subeq-2/\1 q U (η (B ⇐ A) ⊛ U₁) q₁ q₂ = 
    intrp≗ refl ⇐L⇐R refl
mip≗ p U eq₁ (⊗L⇐R {A = A} {B} {p = p₁}) with subeq U (η (A ⊗ B)) p p₁ (sym eq₁) -- there are no 1>2 cases since A ⊗ B is just a node!
mip≗ p ._ refl (⊗L⇐R {A = A} {B}) | 1≡2 (same refl refl refl) rewrite subeq-1≡2 p (η (A ⊗ B)) = 
  intrp≗ refl refl refl
mip≗ p ._ refl (⊗L⇐R {A = A} {B}) | 2>L1 (gt {W₂ = W₂} q refl refl refl) rewrite subeq-2>L1 p W₂ (η (A ⊗ B)) q = 
  intrp≗ refl refl refl
mip≗ p ._ refl (⊗L⇐R {A = A} {B} ) | 2>R1 (gt {W₁} q refl refl refl) rewrite subeq-2>R1 p W₁ (η (A ⊗ B)) q = 
  intrp≗ refl refl refl
mip≗ ._ U refl (⊗L⇐R {A = A} {B}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) rewrite subeq-1/\2 q U (η (A ⊗ B)) q₁ q₂ = 
  intrp≗ refl ⊗L⇐R refl
mip≗ ._ U refl (⊗L⇐R {A = A} {B}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) rewrite subeq-2/\1 q U (η (A ⊗ B)) q₁ q₂ = 
  intrp≗ refl ⊗L⇐R refl

mip≗ p U eq₁ (⇒L⊗R₁ {U = U₁} {A = A} {B} {p = p₁}) with subeq U (U₁ ⊛ η (A ⇒ B)) p (p₁ ◂ _) (sym eq₁) 
mip≗ ._ ._ refl (⇒L⊗R₁ {U = U} {A = A} {B} {p = p}) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p (U ⊛ η (A ⇒ B)) = intrp≗ refl refl refl
mip≗ ∙ ._ refl (⇒L⊗R₁) | 2>L1 (gt ∙ refl refl refl) = intrp≗ refl refl ⇒L⊗R₁
mip≗ ∙ ._ refl (⇒L⊗R₁) | 2>L1 (gt (q ◂ U) refl refl refl) = intrp≗ refl refl ⇒L⊗R₁
mip≗ ∙ ._ refl (⇒L⊗R₁) | 2>L1 (gt (T ▸ q) refl refl refl) = intrp≗ refl refl ⇒L⊗R₁
mip≗ (p ◂ U₁) ._ refl (⇒L⊗R₁ {U = U₂} {A = A} {B}) | 2>L1 (gt {W₂ = W₂} q refl refl refl) 
  rewrite subeq-2>L1 p W₂ (U₂ ⊛ η (A ⇒ B)) q = intrp≗ refl refl refl
mip≗ (T ▸ p) ._ eq₁ (⇒L⊗R₁) | 2>L1 (gt q refl refl ())
mip≗ ∙ ._ eq₁ (⇒L⊗R₁) | 2>R1 (gt q refl refl ())
mip≗ (p ◂ U₁) ._ refl (⇒L⊗R₁ {U = U₂} {A = A} {B} {p = p₁}) | 2>R1 (gt {W₁} q refl refl refl) 
  rewrite subeq-2>R1 p W₁ (U₂ ⊛ η (A ⇒ B)) q = intrp≗ refl refl refl
mip≗ (T ▸ p) ._ eq₁ (⇒L⊗R₁) | 2>R1 (gt q refl refl ())
mip≗ ._ U refl (⇒L⊗R₁ {A = A} {B} {p = p}) | 1>L2 (gt q refl refl refl) rewrite subeq-1>L2 p (η (A ⇒ B)) U q = intrp≗ refl ⇒L⊗R₁ refl
mip≗ ._ ._ refl (⇒L⊗R₁ {U = U} {A = A} {B} {p = p}) | 1>R2 (gt ∙ refl refl refl) rewrite subeq-1>R2 p U (η (A ⇒ B)) ∙ = intrp≗ refl ⇒L⊗R₁ refl
... | 1/\2 (disj ∙ q₁ q₂ refl refl refl ())
mip≗ ._ U refl (⇒L⊗R₁ {U = U₂} {A = A} {B}) | 1/\2 (disj (q ◂ U₁) q₁ q₂ refl refl refl refl) rewrite subeq-1/\2 q U (U₂ ⊛ η (A ⇒ B)) q₁ q₂ = 
  intrp≗ refl ⇒L⊗R₁ refl
... | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl refl ())
mip≗ ._ U refl (⇒L⊗R₁ {U = U₂} {A = A} {B}) | 2/\1 (disj ∙ q₁ q₂ refl refl refl refl) = intrp≗ refl ⇒L⊗R₁ refl
mip≗ ._ U refl (⇒L⊗R₁ {U = U₂} {A = A} {B}) | 2/\1 (disj (q ◂ U₁) q₁ q₂ refl refl refl refl) rewrite subeq-2/\1 q U (U₂ ⊛ η (A ⇒ B)) q₁ q₂ =
  intrp≗ refl ⇒L⊗R₁ refl 
... | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl () eqp₂)

mip≗ p U eq₁ (⇒L⊗R₂ {U = U₁}{A = A} {B} {p = p₁}) with subeq U (U₁ ⊛ η (A ⇒ B)) p (_ ▸ p₁) (sym eq₁)
mip≗ ._ ._ refl (⇒L⊗R₂ {U = U₁} {A = A} {B} {p = p₁}) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p₁ (U₁ ⊛ η (A ⇒ B)) = intrp≗ refl refl refl
mip≗ ∙ ._ eq₁ (⇒L⊗R₂) | 2>L1 (gt q refl refl ())
mip≗ (p ◂ U₁) ._ eq₁ (⇒L⊗R₂) | 2>L1 (gt q refl refl ())
mip≗ (T ▸ p) ._ refl (⇒L⊗R₂ {U = U₁} {A = A} {B}) | 2>L1 (gt {W₂ = W₂} q refl refl refl) 
  rewrite subeq-2>L1 p W₂ (U₁ ⊛ η (A ⇒ B)) q = intrp≗ refl refl refl 
mip≗ ∙ ._ refl (⇒L⊗R₂) | 2>R1 (gt ∙ refl refl refl) = intrp≗ refl refl ⇒L⊗R₂
mip≗ ∙ ._ refl (⇒L⊗R₂) | 2>R1 (gt (q ◂ U) refl refl refl) = intrp≗ refl refl ⇒L⊗R₂
mip≗ ∙ ._ refl (⇒L⊗R₂) | 2>R1 (gt (T ▸ q) refl refl refl) = intrp≗ refl refl ⇒L⊗R₂
mip≗ (p ◂ U₁) ._ eq₁ (⇒L⊗R₂) | 2>R1 (gt q refl refl ())
mip≗ (T ▸ p) ._ refl (⇒L⊗R₂ {U = U₁} {A = A} {B}) | 2>R1 (gt {W₁} q refl refl refl) 
  rewrite subeq-2>R1 p W₁ (U₁ ⊛ (η (A ⇒ B))) q = intrp≗ refl refl refl
mip≗ ._ U refl (⇒L⊗R₂ {A = A} {B} {p = p₁}) | 1>L2 (gt q refl refl refl) 
  rewrite subeq-1>L2 p₁ (η (A ⇒ B)) U q = intrp≗ refl ⇒L⊗R₂ refl
mip≗ ._ ._ refl (⇒L⊗R₂ {U = U₁} {A = A} {B} {p = p₁}) | 1>R2 (gt ∙ refl refl refl) 
  rewrite subeq-1>R2 p₁ U₁ (η (A ⇒ B)) ∙ = intrp≗ refl ⇒L⊗R₂ refl
mip≗ ._ U refl (⇒L⊗R₂) | 1/\2 (disj ∙ q₁ q₂ refl refl refl refl) = intrp≗ refl ⇒L⊗R₂ refl
-- The endsequent is T ⊛ (sub p₁ (U₁ ⊛ η (A ⇒ B))) ⊢ A' ⊗ B'.
-- In the disjoint case, if q goes to the left, then U₁ ≡ (sub p₁ (U₁ ⊛ η (A ⇒ B))).
-- However, by the definition of LeftRight, two paths of U and U₁ ⊛ η (A ⇒ B) would diverge afterwards, which is a contradiction.
-- Therefore, only q ≡ ∙ or q going to the right are valid cases.
... | 1/\2 (disj (q ◂ V) q₁ q₂ refl refl refl ())
mip≗ ._ U refl (⇒L⊗R₂ {U = U₁} {A = A} {B}) | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q U (U₁ ⊛ η (A ⇒ B)) q₁ q₂ = intrp≗ refl ⇒L⊗R₂ refl
... | 2/\1 (disj ∙ q₁ q₂ refl refl () eqp₂)
... | 2/\1 (disj (q ◂ U₁) q₁ q₂ refl refl () eqp₂)
mip≗ ._ U refl (⇒L⊗R₂ {U = U₁} {A = A} {B}) | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q U (U₁ ⊛ η (A ⇒ B)) q₁ q₂ = intrp≗ refl ⇒L⊗R₂ refl
  
mip≗ p U eq₁ (⇐L⊗R₁ {U = U₁} {A = A} {B} {p = p₁}) with subeq U (η (B ⇐ A) ⊛ U₁) p (p₁ ◂ _) (sym eq₁)
mip≗ ._ ._ refl (⇐L⊗R₁ {U = U₁} {A = A} {B} {p = p₁}) | 1≡2 (same refl refl refl)
  rewrite subeq-1≡2 p₁ (η (B ⇐ A) ⊛ U₁) = intrp≗ refl refl refl
mip≗ ∙ ._ refl (⇐L⊗R₁) | 2>L1 (gt ∙ refl refl refl) = intrp≗ refl refl ⇐L⊗R₁
mip≗ ∙ ._ refl (⇐L⊗R₁) | 2>L1 (gt (q ◂ U) refl refl refl) = intrp≗ refl refl ⇐L⊗R₁
mip≗ ∙ ._ refl (⇐L⊗R₁) | 2>L1 (gt (T ▸ q) refl refl refl) = intrp≗ refl refl ⇐L⊗R₁
mip≗ (p ◂ U₂) ._ refl (⇐L⊗R₁ {U = U₁} {A = A} {B}) | 2>L1 (gt {W₂ = W₂} q refl refl refl) 
  rewrite subeq-2>L1 p W₂ (η (B ⇐ A) ⊛ U₁) q = intrp≗ refl refl refl
mip≗ (T ▸ p) ._ eq₁ (⇐L⊗R₁) | 2>L1 (gt q refl refl ())
mip≗ ∙ ._ eq₁ (⇐L⊗R₁) | 2>R1 (gt q refl refl ())
mip≗ (p ◂ U₂) ._ refl (⇐L⊗R₁ {U = U₁} {A = A} {B}) | 2>R1 (gt {W₁} q refl refl refl) 
  rewrite subeq-2>R1 p W₁ (η (B ⇐ A) ⊛ U₁) q = intrp≗ refl refl refl
mip≗ (T ▸ p) ._ eq₁ (⇐L⊗R₁) | 2>R1 (gt q refl refl ())
mip≗ ._ ._ refl (⇐L⊗R₁ {U = U₁} {A = A} {B} {p = p₁}) | 1>L2 (gt ∙ refl refl refl) 
  rewrite subeq-1>L2 p₁ U₁ (η (B ⇐ A)) ∙ = intrp≗ refl ⇐L⊗R₁ refl
mip≗ ._ U refl (⇐L⊗R₁ {A = A} {B} {p = p₁}) | 1>R2 (gt q refl refl refl) 
  rewrite subeq-1>R2 p₁ (η (B ⇐ A)) U q  = intrp≗ refl ⇐L⊗R₁ refl
... | 1/\2 (disj ∙ q₁ q₂ refl refl refl ())
mip≗ ._ U refl (⇐L⊗R₁ {U = U₁} {A = A} {B}) | 1/\2 (disj (q ◂ U₂) q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q U (η (B ⇐ A) ⊛ U₁) q₁ q₂ = intrp≗ refl ⇐L⊗R₁ refl
... | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl refl ())
mip≗ ._ U refl (⇐L⊗R₁) | 2/\1 (disj ∙ q₁ q₂ refl refl refl refl) = intrp≗ refl ⇐L⊗R₁ refl
mip≗ ._ U refl (⇐L⊗R₁ {U = U₁} {A = A} {B}) | 2/\1 (disj (q ◂ U₂) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q U (η (B ⇐ A) ⊛ U₁) q₁ q₂ = intrp≗ refl ⇐L⊗R₁ refl
... | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl () eqp₂)

mip≗ p U eq₁ (⇐L⊗R₂ {U = U₁} {A = A} {B} {p = p₁}) with subeq U (η (B ⇐ A) ⊛ U₁) p (_ ▸ p₁) (sym eq₁)
mip≗ ._ ._ refl (⇐L⊗R₂ {U = U₁} {A = A} {B} {p = p₁}) | 1≡2 (same refl refl refl)
  rewrite subeq-1≡2 p₁ (η (B ⇐ A) ⊛ U₁) = intrp≗ refl refl refl
mip≗ ∙ ._ eq₁ (⇐L⊗R₂) | 2>L1 (gt q refl refl ())
mip≗ (p ◂ U₁) ._ eq₁ (⇐L⊗R₂) | 2>L1 (gt q refl refl ())
mip≗ (T ▸ p) ._ refl (⇐L⊗R₂ {U = U₁} {A = A} {B}) | 2>L1 (gt {W₂ = W₂} q refl refl refl) 
  rewrite subeq-2>L1 p W₂ (η (B ⇐ A) ⊛ U₁) q = intrp≗ refl refl refl
mip≗ ∙ ._ refl (⇐L⊗R₂) | 2>R1 (gt ∙ refl refl refl) = intrp≗ refl refl ⇐L⊗R₂
mip≗ ∙ ._ refl (⇐L⊗R₂) | 2>R1 (gt (q ◂ U) refl refl refl) = intrp≗ refl refl ⇐L⊗R₂
mip≗ ∙ ._ refl (⇐L⊗R₂) | 2>R1 (gt (T ▸ q) refl refl refl) = intrp≗ refl refl ⇐L⊗R₂
mip≗ (p ◂ U₁) ._ eq₁ (⇐L⊗R₂) | 2>R1 (gt q refl refl ())
mip≗ (T ▸ p) ._ refl (⇐L⊗R₂ {U = U₁} {A = A} {B}) | 2>R1 (gt {W₁} q refl refl refl) 
  rewrite subeq-2>R1 p W₁ (η (B ⇐ A) ⊛ U₁) q = intrp≗ refl refl refl
mip≗ ._ ._ refl (⇐L⊗R₂ {U = U₁} {A = A} {B} {p = p₁}) | 1>L2 (gt ∙ refl refl refl) 
  rewrite subeq-1>L2 p₁ U₁ (η (B ⇐ A)) ∙ = intrp≗ refl ⇐L⊗R₂ refl
mip≗ ._ U refl (⇐L⊗R₂ {A = A} {B} {p = p₁}) | 1>R2 (gt q refl refl refl) 
  rewrite subeq-1>R2 p₁ (η (B ⇐ A)) U q = intrp≗ refl ⇐L⊗R₂ refl
mip≗ ._ U refl (⇐L⊗R₂) | 1/\2 (disj ∙ q₁ q₂ refl refl refl refl) = intrp≗ refl ⇐L⊗R₂ refl
... | 1/\2 (disj (q ◂ U₁) q₁ q₂ refl refl refl ())
mip≗ ._ U refl (⇐L⊗R₂ {U = U₁} {A = A} {B}) | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q U (η (B ⇐ A) ⊛ U₁) q₁ q₂ = intrp≗ refl ⇐L⊗R₂ refl
... | 2/\1 (disj ∙ q₁ q₂ refl refl () eqp₂)
... | 2/\1 (disj (q ◂ U₁) q₁ q₂ refl refl () eqp₂)
mip≗ ._ U refl (⇐L⊗R₂ {U = U₁} {A = A} {B}) | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q U (η (B ⇐ A) ⊛ U₁) q₁ q₂ = intrp≗ refl ⇐L⊗R₂ refl

mip≗ p U eq₁ (⊗L⊗R₁ {U = U₁} {A} {B} {p = p₁}) with subeq U (η (A ⊗ B)) p (p₁ ◂ U₁) (sym eq₁)
mip≗ ._ ._ refl (⊗L⊗R₁ {A = A} {B} {p = p₁}) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p₁ (η (A ⊗ B)) = intrp≗ refl refl refl
mip≗ ∙ ._ refl (⊗L⊗R₁) | 2>L1 (gt ∙ refl refl refl) = intrp≗ refl refl ⊗L⊗R₁
mip≗ ∙ ._ refl (⊗L⊗R₁) | 2>L1 (gt (q ◂ U) refl refl refl) = intrp≗ refl refl ⊗L⊗R₁
mip≗ ∙ ._ refl (⊗L⊗R₁) | 2>L1 (gt (T ▸ q) refl refl refl) = intrp≗ refl refl ⊗L⊗R₁
mip≗ (p ◂ U₁) ._ refl (⊗L⊗R₁ {A = A} {B}) | 2>L1 (gt {W₂ = W₂} q refl refl refl) 
  rewrite subeq-2>L1 p W₂ (η (A ⊗ B)) q = intrp≗ refl refl refl
mip≗ (T ▸ p) ._ eq₁ (⊗L⊗R₁) | 2>L1 (gt q refl refl ())
mip≗ ∙ ._ eq₁ (⊗L⊗R₁) | 2>R1 (gt q refl refl ())
mip≗ (p ◂ U₁) ._ refl (⊗L⊗R₁ {A = A} {B}) | 2>R1 (gt {W₁} q refl refl refl) 
  rewrite subeq-2>R1 p W₁ (η (A ⊗ B)) q = intrp≗ refl refl refl
mip≗ (T ▸ p) ._ eq₁ (⊗L⊗R₁) | 2>R1 (gt q refl refl ())
mip≗ ._ U eq₁ (⊗L⊗R₁) | 1/\2 (disj ∙ q₁ q₂ refl refl refl ())
mip≗ ._ U refl (⊗L⊗R₁ {A = A} {B}) | 1/\2 (disj (q ◂ U₁) q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q U (η (A ⊗ B)) q₁ q₂ = intrp≗ refl ⊗L⊗R₁ refl
... | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl refl ())
mip≗ ._ U refl (⊗L⊗R₁) | 2/\1 (disj ∙ q₁ q₂ refl refl refl refl) = intrp≗ refl ⊗L⊗R₁ refl
mip≗ ._ U refl (⊗L⊗R₁ {A = A} {B}) | 2/\1 (disj (q ◂ U₁) q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q U (η (A ⊗ B)) q₁ q₂ = intrp≗ refl ⊗L⊗R₁ refl
... | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl () eqp₂)

mip≗ p U eq₁ (⊗L⊗R₂ {U = U₁} {A} {B} {p = p₁}) with subeq U (η (A ⊗ B)) p (U₁ ▸ p₁) (sym eq₁)
mip≗ ._ ._ refl (⊗L⊗R₂ {A = A} {B} {p = p₁}) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 p₁ (η (A ⊗ B)) = intrp≗ refl refl refl
mip≗ ∙ ._ eq₁ (⊗L⊗R₂) | 2>L1 (gt q refl refl ())
mip≗ (p ◂ U₁) ._ eq₁ (⊗L⊗R₂) | 2>L1 (gt q refl refl ())
mip≗ (T ▸ p) ._ refl (⊗L⊗R₂ {A = A} {B}) | 2>L1 (gt {W₂ = W₂} q refl refl refl)
  rewrite subeq-2>L1 p W₂ (η (A ⊗ B)) q = intrp≗ refl refl refl
mip≗ ∙ ._ refl (⊗L⊗R₂) | 2>R1 (gt ∙ refl refl refl) = intrp≗ refl refl ⊗L⊗R₂
mip≗ ∙ ._ refl (⊗L⊗R₂) | 2>R1 (gt (q ◂ U) refl refl refl) = intrp≗ refl refl ⊗L⊗R₂
mip≗ ∙ ._ refl (⊗L⊗R₂) | 2>R1 (gt (T ▸ q) refl refl refl) = intrp≗ refl refl ⊗L⊗R₂
mip≗ (p ◂ U₁) ._ eq₁ (⊗L⊗R₂) | 2>R1 (gt q refl refl ())
mip≗ (T ▸ p) ._ refl (⊗L⊗R₂ {A = A} {B}) | 2>R1 (gt {W₁} q refl refl refl) 
  rewrite subeq-2>R1 p W₁ (η (A ⊗ B)) q = intrp≗ refl refl refl
mip≗ ._ U refl (⊗L⊗R₂) | 1/\2 (disj ∙ q₁ q₂ refl refl refl refl) = intrp≗ refl ⊗L⊗R₂ refl
... | 1/\2 (disj (q ◂ U₁) q₁ q₂ refl refl refl ())
mip≗ ._ U refl (⊗L⊗R₂ {A = A} {B}) | 1/\2 (disj (T ▸ q) q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q U (η (A ⊗ B)) q₁ q₂ = intrp≗ refl ⊗L⊗R₂ refl
... | 2/\1 (disj ∙ q₁ q₂ refl refl () eqp₂)
... | 2/\1 (disj (q ◂ U₁) q₁ q₂ refl refl () eqp₂)
mip≗ ._ U refl (⊗L⊗R₂ {A = A} {B}) | 2/\1 (disj (T ▸ q) q₁ q₂ refl refl refl refl)
  rewrite subeq-2/\1 q U (η (A ⊗ B)) q₁ q₂ = intrp≗ refl ⊗L⊗R₂ refl


mip≗ p U eq₁ (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) with subeq U _ p p₁ (sym eq₁) 
mip≗ p ._ refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1≡2 (same refl refl refl) 
  rewrite subeq-2>L1 p (sub p₃ (η (A' ⊗ B'))) (η (A ⊗ B)) p₂ |
          subeq-2>R1 p (sub p₂ (η A ⊛ η B)) (η (A' ⊗ B')) p₃ |
          subeq-2>R1 p (sub p₂ (η (A ⊗ B))) (η (A' ⊗ B')) p₃ |
          subeq-2>L1 p (sub p₃ (η A' ⊛ η B')) (η (A ⊗ B)) p₂ = intrp≗ refl refl (⊗L⊗L {p = ∙} {p₂} {p₃})

mip≗ p ._ refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2>L1 (gt {W₂ = W₂} q refl refl refl) 
  rewrite subeq-2>L1 p W₂ (η (A ⊗ B)) (q ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) |
          subeq-2>L1 p W₂ (η (A' ⊗ B')) (q ++ (sub p₂ (η A ⊛ η B) ▸ p₃)) |
          subeq-2>L1 p W₂ (η (A' ⊗ B')) (q ++ (sub p₂ (η (A ⊗ B)) ▸ p₃)) |
          subeq-2>L1 p W₂ (η (A ⊗ B)) (q ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) = intrp≗ refl refl (⊗L⊗L {p = q ◂ _} {p₂} {p₃})

mip≗ p ._ refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2>R1 (gt {W₁} q refl refl refl) 
  rewrite subeq-2>R1 p W₁ (η (A ⊗ B)) (q ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) |
          subeq-2>R1 p W₁ (η (A' ⊗ B')) (q ++ (sub p₂ (η A ⊛ η B) ▸ p₃)) |
          subeq-2>R1 p W₁ (η (A' ⊗ B')) (q ++ (sub p₂ (η (A ⊗ B)) ▸ p₃)) |
          subeq-2>R1 p W₁ (η (A ⊗ B)) (q ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) = intrp≗ refl refl (⊗L⊗L {p = _ ▸ q} {p₂} {p₃})

mip≗ p U eq₁ (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt q refl eqU refl) with subeq U _ q p₂ (sym ((⊛eq eqU) .proj₁))
mip≗ ._ ._ refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1/\2 p₁ (η (A ⊗ B)) (η (A' ⊗ B')) q p₃ |
          subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (η (A' ⊗ B')))) (η (A ⊗ B)) |
          subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (η A' ⊛ η B'))) (η (A ⊗ B)) |
          subeq-1/\2 p₁ (η A ⊛ η B) (η (A' ⊗ B')) q p₃ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (q ◂ sub p₃ (η (A' ⊗ B')))) W₂ (η (A ⊗ B)) q₁ |
          subeq-1/\2 p₁ (sub q₁ (η A ⊛ η B) ⊛ W₂) (η (A' ⊗ B')) q p₃ |
          subeq-1/\2 p₁ (sub q₁ (η (A ⊗ B)) ⊛ W₂) (η (A' ⊗ B')) q p₃ |
          subeq-2>L1 (p₁ ++ (q ◂ sub p₃ (η A' ⊛ η B'))) W₂ (η (A ⊗ B)) q₁ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 2>R1 (gt {W₁} q₁ refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (q ◂ sub p₃ (η (A' ⊗ B')))) W₁ (η (A ⊗ B)) q₁ |
          subeq-1/\2 p₁ (W₁ ⊛ sub q₁ (η A ⊛ η B)) (η (A' ⊗ B')) q p₃ |
          subeq-1/\2 p₁ (W₁ ⊛ sub q₁ (η (A ⊗ B))) (η (A' ⊗ B')) q p₃ |
          subeq-2>R1 (p₁ ++ (q ◂ sub p₃ (η A' ⊛ η B'))) W₁ (η (A ⊗ B)) q₁ = intrp≗ refl refl refl

mip≗ ._ U refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) U (η (A ⊗ B)) q₂ q₃ |
          subeq-1/\2 p₁ U (η (A' ⊗ B')) (q₁ ++ (q₂ ◂ sub q₃ (η A ⊛ η B))) p₃ |
          subeq-1/\2 p₁ U (η (A' ⊗ B')) (q₁ ++ (q₂ ◂ sub q₃ (η (A ⊗ B)))) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) U (η (A ⊗ B)) q₂ q₃ = intrp≗ refl (⊗L⊗L {p = p₁} {q₁ ++ (_ ▸ q₃)} {p₃}) refl

mip≗ ._ U refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (A' ⊗ B')))) U (η (A ⊗ B)) q₂ q₃ |
          subeq-1/\2 p₁ U (η (A' ⊗ B')) (q₁ ++ (sub q₂ (η A ⊛ η B) ▸ q₃)) p₃ |
          subeq-1/\2 p₁ U (η (A' ⊗ B')) (q₁ ++ (sub q₂ (η (A ⊗ B)) ▸ q₃)) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η A' ⊛ η B'))) U (η (A ⊗ B)) q₂ q₃ = intrp≗ refl (⊗L⊗L {p = p₁} {q₁ ++ (q₂ ◂ _)} {p₃}) refl

mip≗ p U eq₁ (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt q refl eqU refl) with subeq U _ q p₃ (sym ((⊛eq eqU) .proj₂))
mip≗ ._ ._ refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (A' ⊗ B')) (η (A ⊗ B)) p₂ q |
          subeq-1≡2 (p₁ ++ (sub p₂ (η A ⊛ η B) ▸ q)) (η (A' ⊗ B')) |
          subeq-1≡2 (p₁ ++ (sub p₂ (η (A ⊗ B)) ▸ q)) (η (A' ⊗ B')) |
          subeq-2/\1 p₁ (η A' ⊛ η B') (η (A ⊗ B)) p₂ q = intrp≗ refl refl refl

mip≗ ._ ._ refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl) 
  rewrite subeq-2/\1 p₁ (sub q₁ (η (A' ⊗ B')) ⊛ W₂) (η (A ⊗ B)) p₂ q |
          subeq-2>L1 (p₁ ++ (sub p₂ (η A ⊛ η B) ▸ q)) W₂ (η (A' ⊗ B')) q₁ |
          subeq-2>L1 (p₁ ++ (sub p₂ (η (A ⊗ B)) ▸ q)) W₂ (η (A' ⊗ B')) q₁ |
          subeq-2/\1 p₁ (sub q₁ (η A' ⊛ η B') ⊛ W₂) (η (A ⊗ B)) p₂ q = intrp≗ refl refl refl

mip≗ ._ ._ refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 2>R1 (gt {W₁} q₁ refl refl refl) 
  rewrite subeq-2/\1 p₁ (W₁ ⊛ sub q₁ (η (A' ⊗ B'))) (η (A ⊗ B)) p₂ q |
          subeq-2>R1 (p₁ ++ (sub p₂ (η A ⊛ η B) ▸ q)) W₁ (η (A' ⊗ B')) q₁ |
          subeq-2>R1 (p₁ ++ (sub p₂ (η (A ⊗ B)) ▸ q)) W₁ (η (A' ⊗ B')) q₁ |
          subeq-2/\1 p₁ (W₁ ⊛ sub q₁ (η A' ⊛ η B')) (η (A ⊗ B)) p₂ q = intrp≗ refl refl refl

mip≗ ._ U refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ U (η (A ⊗ B)) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η A ⊛ η B) ▸ q₁)) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (sub p₂ (η (A ⊗ B)) ▸ q₁)) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-2/\1 p₁ U (η (A ⊗ B)) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) = intrp≗ refl (⊗L⊗L {p = p₁} {p₂} {q₁ ++ (_ ▸ q₃)}) refl

mip≗ ._ U refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ U (η (A ⊗ B)) p₂ (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η A ⊛ η B) ▸ q₁)) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (sub p₂ (η (A ⊗ B)) ▸ q₁)) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-2/\1 p₁ U (η (A ⊗ B)) p₂ (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) = intrp≗ refl (⊗L⊗L {p = p₁} {p₂} {q₁ ++ (q₂ ◂ _)}) refl

mip≗ ._ U refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q U (η (A ⊗ B)) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) |
          subeq-1/\2 q U (η (A' ⊗ B')) q₁ (q₂ ++ (sub p₂ (η A ⊛ η B) ▸ p₃)) |
          subeq-1/\2 q U (η (A' ⊗ B')) q₁ (q₂ ++ (sub p₂ (η (A ⊗ B)) ▸ p₃)) |
          subeq-1/\2 q U (η (A ⊗ B)) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) = intrp≗ refl (⊗L⊗L {p = q ++ (_ ▸ q₂)} {p₂} {p₃}) refl

mip≗ ._ U refl (⊗L⊗L {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q U (η (A ⊗ B)) (q₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) q₂ |
          subeq-2/\1 q U (η (A' ⊗ B')) (q₁ ++ (sub p₂ (η A ⊛ η B) ▸ p₃)) q₂ |
          subeq-2/\1 q U (η (A' ⊗ B')) (q₁ ++ (sub p₂ (η (A ⊗ B)) ▸ p₃)) q₂ |
          subeq-2/\1 q U (η (A ⊗ B)) (q₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) q₂ = intrp≗ refl (⊗L⊗L {p = q ++ (q₁ ◂ _)} {p₂} {p₃}) refl

mip≗ p U eq₁ (⊗L⇒L₁ {p = q} {q'}) with subeq U _ p q' (sym eq₁)
mip≗ p ._ refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = q} {q'}) | 1≡2 (same refl refl refl) 
  rewrite subeq-2>L1 p (η (A ⇒ B)) (η (A' ⊗ B')) q |
          subeq-1≡2 p (sub q (η A' ⊛ η B') ⊛ η (A ⇒ B)) = 
          intrp≗ refl refl ⊗L⇒L₁ 
mip≗ p ._ refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = q} {q'}) | 2>L1 (gt {W₂ = W₂} r refl refl refl) 
  rewrite subeq-2>L1 p W₂ (η (A' ⊗ B')) (r ++ (q ◂ η (A ⇒ B))) |
          subeq-2>L1 p W₂ (sub q (η A' ⊛ η B') ⊛ η (A ⇒ B)) r = 
          intrp≗ refl refl ⊗L⇒L₁ 
mip≗ p ._ refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = q} {q'}) | 2>R1 (gt {W₁} r refl refl refl) 
  rewrite subeq-2>R1 p W₁ (η (A' ⊗ B')) (r ++ (q ◂ η (A ⇒ B))) |
          subeq-2>R1 p W₁ (sub q (η A' ⊛ η B') ⊛ η (A ⇒ B)) r = 
          intrp≗ refl refl ⊗L⇒L₁ 
mip≗ ._ U eq₁ (⊗L⇒L₁ {p = q} {_}) | 1>L2 (gt r refl eqU refl) with subeq _ _ r q (sym (⊛eq eqU .proj₁)) 
mip≗ ._ ._ refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = _} {q'}) | 1>L2 (gt r refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 r (η (A' ⊗ B')) |
          subeq-1≡2 (q' ++ (r ◂ η (A ⇒ B))) (η (A' ⊗ B')) |
          subeq-1>L2 q' (η (A ⇒ B)) (η A' ⊛ η B') r = 
          intrp≗ refl refl refl 
mip≗ ._ ._ refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = _} {q'}) | 1>L2 (gt r refl refl refl) | 2>L1 (gt {W₂ = W₂} q refl refl refl) 
  rewrite subeq-2>L1 r W₂ (η (A' ⊗ B')) q |
          subeq-2>L1 (q' ++ (r ◂ η (A ⇒ B))) W₂ (η (A' ⊗ B')) q |
          subeq-1>L2 q' (η (A ⇒ B)) (sub q (η A' ⊛ η B') ⊛ W₂) r = 
          intrp≗ refl refl refl 
mip≗ ._ ._ refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = _} {q'}) | 1>L2 (gt r refl refl refl) | 2>R1 (gt {W₁} q refl refl refl) 
  rewrite subeq-2>R1 r W₁ (η (A' ⊗ B')) q |
          subeq-2>R1 (q' ++ (r ◂ η (A ⇒ B))) W₁ (η (A' ⊗ B')) q |
          subeq-1>L2 q' (η (A ⇒ B)) (W₁ ⊛ sub q (η A' ⊛ η B')) r = 
          intrp≗ refl refl refl
mip≗ ._ U refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = _} {q'}) | 1>L2 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q U (η (A' ⊗ B')) q₁ q₂ |
          subeq-1/\2 (q' ++ (q ◂ η (A ⇒ B))) U (η (A' ⊗ B')) q₁ q₂ |
          subeq-1>L2 q' (η (A ⇒ B)) U (q ++ (q₁ ◂ sub q₂ (η A' ⊛ η B'))) = 
          intrp≗ refl ⊗L⇒L₁ refl
mip≗ ._ U refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = _} {q'}) | 1>L2 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-2/\1 q U (η (A' ⊗ B')) q₁ q₂ |
          subeq-2/\1 (q' ++ (q ◂ η (A ⇒ B))) U (η (A' ⊗ B')) q₁ q₂ |
          subeq-1>L2 q' (η (A ⇒ B)) U (q ++ (sub q₁ (η A' ⊛ η B') ▸ q₂)) = 
          intrp≗ refl ⊗L⇒L₁ refl
-- A ⇒ B is the interpolant tree          
mip≗ ._ ._ refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = ∙} {q'}) | 1>R2 (gt ∙ refl refl refl) 
  rewrite subeq-2/\1 q' (η (A ⇒ B)) (η (A' ⊗ B')) ∙ ∙ |
          subeq-1>R2 q' (η A' ⊛ η B') (η (A ⇒ B)) ∙ = intrp≗ refl ⊗L⇒L₁ (⇒R (⇒L refl refl)) -- this is refl but I write (⇒R (⇒L refl refl))
mip≗ ._ ._ refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = q ◂ U} {q'}) | 1>R2 (gt ∙ refl refl refl)    -- to remind that this is the principal case
  rewrite subeq-2/\1 q' (η (A ⇒ B)) (η (A' ⊗ B')) (q ◂ U) ∙ |
          subeq-1>R2 q' (sub (q ◂ U) (η A' ⊛ η B')) (η (A ⇒ B)) ∙ = intrp≗ refl ⊗L⇒L₁ (⇒R (⇒L refl refl))
mip≗ ._ ._ refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = T ▸ q} {q'}) | 1>R2 (gt ∙ refl refl refl) 
  rewrite subeq-2/\1 q' (η (A ⇒ B)) (η (A' ⊗ B')) (T ▸ q) ∙ |
          subeq-1>R2 q' (sub (T ▸ q) (η A' ⊛ η B')) (η (A ⇒ B)) ∙ = intrp≗ refl ⊗L⇒L₁ (⇒R (⇒L refl refl))
-- A ⇒ B is the interpolant tree          
mip≗ ._ U refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = q}) | 1/\2 (disj r r₁ r₂ refl refl refl refl) 
  rewrite subeq-1/\2 r U (η (A' ⊗ B')) r₁ (r₂ ++ (q ◂ η (A ⇒ B))) |
          subeq-1/\2 r U (sub q (η A' ⊛ η B') ⊛ η (A ⇒ B)) r₁ r₂ = 
          intrp≗ refl ⊗L⇒L₁ refl
mip≗ ._ U refl (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = q}) | 2/\1 (disj r r₁ r₂ refl refl refl refl) 
  rewrite subeq-2/\1 r U (η (A' ⊗ B')) (r₁ ++ (q ◂ η (A ⇒ B))) r₂ |
          subeq-2/\1 r U (sub q (η A' ⊛ η B') ⊛ η (A ⇒ B)) r₁ r₂ = 
          intrp≗ refl ⊗L⇒L₁ refl 

mip≗ p U eq₁ (⊗L⇒L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) with subeq U _ p p₁ (sym eq₁) 
mip≗ p ._ refl (⊗L⇒L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1≡2 (same refl refl refl) 
  rewrite subeq-2>R1 p (sub p₂ (η (A' ⊗ B'))) (U₁ ⊛ η (A ⇒ B)) p₃ |
          subeq-2>L1 p (sub p₃ (η B)) (η (A' ⊗ B')) p₂ |
          subeq-2>L1 p (sub p₃ (U₁ ⊛ η (A ⇒ B))) (η (A' ⊗ B')) p₂ |
          subeq-2>R1 p (sub p₂ (η A' ⊛ η B')) (U₁ ⊛ η (A ⇒ B)) p₃ = intrp≗ refl refl (⊗L⇒L₂1/\2 {p = ∙} {p₂} {p₃})

mip≗ p ._ refl (⊗L⇒L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2>L1 (gt {W₂ = W₂} q refl refl refl) 
  rewrite subeq-2>L1 p W₂ (U₁ ⊛ η (A ⇒ B)) (q ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) |
          subeq-2>L1 p W₂ (η (A' ⊗ B')) (q ++ (p₂ ◂ sub p₃ (η B))) |
          subeq-2>L1 p W₂ (η (A' ⊗ B')) (q ++ (p₂ ◂ sub p₃ (U₁ ⊛ η (A ⇒ B)))) |
          subeq-2>L1 p W₂ (U₁ ⊛ η (A ⇒ B)) (q ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) = intrp≗ refl refl (⊗L⇒L₂1/\2 {p = q ◂ _} {p₂} {p₃})

mip≗ p ._ refl (⊗L⇒L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2>R1 (gt {W₁} q refl refl refl) 
  rewrite subeq-2>R1 p W₁ (U₁ ⊛ η (A ⇒ B)) (q ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) |
          subeq-2>R1 p W₁ (η (A' ⊗ B')) (q ++ (p₂ ◂ sub p₃ (η B))) |
          subeq-2>R1 p W₁ (η (A' ⊗ B')) (q ++ (p₂ ◂ sub p₃ (U₁ ⊛ η (A ⇒ B)))) |
          subeq-2>R1 p W₁ (U₁ ⊛ η (A ⇒ B)) (q ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) = intrp≗ refl refl (⊗L⇒L₂1/\2 {p = _ ▸ q} {p₂} {p₃})

mip≗ p U eq₁ (⊗L⇒L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt q refl eqU refl) with subeq _ _ q p₂ (sym ((⊛eq eqU) .proj₁))
mip≗ ._ ._ refl (⊗L⇒L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃})  | 1>L2 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1/\2 p₁ (η (A' ⊗ B')) (U₁ ⊛ η (A ⇒ B)) q p₃ |
          subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (U₁ ⊛ η (A ⇒ B)))) (η (A' ⊗ B')) |
          subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (η B))) (η (A' ⊗ B')) |
          subeq-1/\2 p₁ (η A' ⊛ η B') (U₁ ⊛ η (A ⇒ B)) q p₃ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⊗L⇒L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl) 
  rewrite subeq-1/\2 p₁ (sub q₁ (η (A' ⊗ B')) ⊛ W₂) (U₁ ⊛ η (A ⇒ B)) q p₃ |
          subeq-2>L1 (p₁ ++ (q ◂ sub p₃ (η B))) W₂ (η (A' ⊗ B')) q₁ |
          subeq-2>L1 (p₁ ++ (q ◂ sub p₃ (U₁ ⊛ η (A ⇒ B)))) W₂ (η (A' ⊗ B')) q₁ |
          subeq-1/\2 p₁ (sub q₁ (η A' ⊛ η B') ⊛ W₂) (U₁ ⊛ η (A ⇒ B)) q p₃ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⊗L⇒L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 2>R1 (gt {W₁} q₁ refl refl refl) 
  rewrite subeq-1/\2 p₁ (W₁ ⊛ sub q₁ (η (A' ⊗ B'))) (U₁ ⊛ η (A ⇒ B)) q p₃ |
          subeq-2>R1 (p₁ ++ (q ◂ sub p₃ (η B))) W₁ (η (A' ⊗ B')) q₁ |
          subeq-2>R1 (p₁ ++ (q ◂ sub p₃ (U₁ ⊛ η (A ⇒ B)))) W₁ (η (A' ⊗ B')) q₁ |
          subeq-1/\2 p₁ (W₁ ⊛ sub q₁ (η A' ⊛ η B')) (U₁ ⊛ η (A ⇒ B)) q p₃ = intrp≗ refl refl refl

mip≗ ._ U refl (⊗L⇒L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 p₁ U (U₁ ⊛ η (A ⇒ B)) (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) p₃  |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η B))) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (U₁ ⊛ η (A ⇒ B)))) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-1/\2 p₁ U (U₁ ⊛ η (A ⇒ B)) (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) p₃ = intrp≗ refl (⊗L⇒L₂1/\2 {p = p₁} {q₁ ++ (_ ▸ q₃)}) refl 

mip≗ ._ U refl (⊗L⇒L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 p₁ U (U₁ ⊛ η (A ⇒ B)) (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η B))) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (U₁ ⊛ η (A ⇒ B)))) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-1/\2 p₁ U (U₁ ⊛ η (A ⇒ B)) (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) p₃ = intrp≗ refl (⊗L⇒L₂1/\2 {p = p₁} {q₁ ++ (q₂ ◂ _)} {p₃}) refl

mip≗ p U eq₁ (⊗L⇒L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt q refl eqU refl) with subeq _ _ q p₃ (sym ((⊛eq eqU) .proj₂))
mip≗ ._ ._ refl (⊗L⇒L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q)) (U₁ ⊛ η (A ⇒ B)) |
          subeq-2/\1 p₁ (η B) (η (A' ⊗ B')) p₂ q |
          subeq-2/\1 p₁ (U₁ ⊛ η (A ⇒ B)) (η (A' ⊗ B')) p₂ q |
          subeq-1≡2 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q)) (U₁ ⊛ η (A ⇒ B)) = intrp≗ refl refl refl
          
mip≗ ._ ._ refl (⊗L⇒L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q)) W₂ (U₁ ⊛ η (A ⇒ B)) q₁ |
          subeq-2/\1 p₁ (sub q₁ (η B) ⊛ W₂) (η (A' ⊗ B')) p₂ q |
          subeq-2/\1 p₁ (sub q₁ (U₁ ⊛ η (A ⇒ B)) ⊛ W₂) (η (A' ⊗ B')) p₂ q |
          subeq-2>L1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q)) W₂ (U₁ ⊛ η (A ⇒ B)) q₁ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⊗L⇒L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 2>R1 (gt {W₁} q₁ refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q)) W₁ (U₁ ⊛ η (A ⇒ B)) q₁ |
          subeq-2/\1 p₁ (W₁ ⊛ sub q₁ (η B)) (η (A' ⊗ B')) p₂ q |
          subeq-2/\1 p₁ (W₁ ⊛ sub q₁ (U₁ ⊛ η (A ⇒ B))) (η (A' ⊗ B')) p₂ q |
          subeq-2>R1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q)) W₁ (U₁ ⊛ η (A ⇒ B)) q₁ = intrp≗ refl refl refl

mip≗ ._ U refl (⊗L⇒L₂1/\2 {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt ._ refl refl refl) | 1>L2 (gt q₁ refl refl refl) 
  rewrite subeq-1>L2 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) (η (A ⇒ B)) U q₁ |
          subeq-2/\1 p₁ U (η (A' ⊗ B')) p₂ (p₃ ++ (q₁ ◂ η (A ⇒ B))) |
          subeq-2/\1 p₁ U (η A' ⊛ η B') p₂ (p₃ ++ (q₁ ◂ η (A ⇒ B))) |
          subeq-1>L2 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) (η (A ⇒ B)) U q₁ = intrp≗ refl (⊗L⇒L₂1/\2 {p = p₁} {p₂} {p₃}) refl

mip≗ ._ ._ refl (⊗L⇒L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt ._ refl refl refl) | 1>R2 (gt ∙ refl refl refl) 
  rewrite subeq-1>R2 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) U₁ (η (A ⇒ B)) ∙ |
          subeq-2/\1 p₁ (η B) (η (A' ⊗ B')) p₂ p₃ |
          subeq-2/\1 p₁ (η (A ⇒ B)) (η (A' ⊗ B')) p₂ (p₃ ++ (U₁ ▸ ∙)) |
          subeq-1>R2 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) U₁ (η (A ⇒ B)) ∙ = intrp≗ refl (⊗L⇒L₂1/\2 {p = p₁} {p₂} {p₃}) refl

mip≗ ._ U refl (⊗L⇒L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ ((sub p₂ (η (A' ⊗ B'))) ▸ q₁)) U (U₁ ⊛ η (A ⇒ B)) q₂ q₃ |
          subeq-2/\1 p₁ U (η (A' ⊗ B')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η B))) |
          subeq-2/\1 p₁ U (η (A' ⊗ B')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (U₁ ⊛ η (A ⇒ B)))) |
          subeq-1/\2 (p₁ ++ ((sub p₂ (η A' ⊛ η B')) ▸ q₁)) U (U₁ ⊛ η (A ⇒ B)) q₂ q₃ = intrp≗ refl (⊗L⇒L₂1/\2 {p = p₁} {p₂} {q₁ ++ (_ ▸ q₃)}) refl

mip≗ ._ U refl (⊗L⇒L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ ((sub p₂ (η (A' ⊗ B'))) ▸ q₁)) U (U₁ ⊛ η (A ⇒ B)) q₂ q₃ |
          subeq-2/\1 p₁ U (η (A' ⊗ B')) p₂ (q₁ ++ (sub q₂ (η B) ▸ q₃)) |
          subeq-2/\1 p₁ U (η (A' ⊗ B')) p₂ (q₁ ++ (sub q₂ (U₁ ⊛ η (A ⇒ B)) ▸ q₃)) |
          subeq-2/\1 (p₁ ++ ((sub p₂ (η A' ⊛ η B')) ▸ q₁)) U (U₁ ⊛ η (A ⇒ B)) q₂ q₃ = intrp≗ refl (⊗L⇒L₂1/\2 {p = p₁} {p₂} {q₁ ++ (q₂ ◂ _)}) refl

mip≗ ._ U refl (⊗L⇒L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q U (U₁ ⊛ η (A ⇒ B)) q₁ (q₂ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) |
          subeq-1/\2 q U (η (A' ⊗ B')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B))) |
          subeq-1/\2 q U (η (A' ⊗ B')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (U₁ ⊛ η (A ⇒ B)))) |
          subeq-1/\2 q U (U₁ ⊛ η (A ⇒ B)) q₁ (q₂ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) = intrp≗ refl (⊗L⇒L₂1/\2 {p = q ++ (_ ▸ q₂)} {p₂} {p₃}) refl

mip≗ ._ U refl (⊗L⇒L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q U (U₁ ⊛ η (A ⇒ B)) (q₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) q₂ |
          subeq-2/\1 q U (η (A' ⊗ B')) (q₁ ++ (p₂ ◂ sub p₃ (η B))) q₂ |
          subeq-2/\1 q U (η (A' ⊗ B')) (q₁ ++ (p₂ ◂ sub p₃ (U₁ ⊛ η (A ⇒ B)))) q₂ |
          subeq-2/\1 q U (U₁ ⊛ η (A ⇒ B)) (q₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) q₂ = intrp≗ refl (⊗L⇒L₂1/\2 {p = q ++ (q₁ ◂ _)} {p₂} {p₃}) refl


mip≗ p U eq₁ (⊗L⇒L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) with subeq U _ p p₁ (sym eq₁) 
mip≗ p ._ refl (⊗L⇒L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1≡2 (same refl refl refl)
  rewrite subeq-2>L1 p (sub p₃ (η (A' ⊗ B'))) (U₁ ⊛ η (A ⇒ B)) p₂ |
          subeq-2>R1 p (sub p₂ (η B)) (η (A' ⊗ B')) p₃ |
          subeq-2>R1 p (sub p₂ (U₁ ⊛ η (A ⇒ B))) (η (A' ⊗ B')) p₃ |
          subeq-2>L1 p (sub p₃ (η A' ⊛ η B')) (U₁ ⊛ η (A ⇒ B)) p₂ = intrp≗ refl refl (⊗L⇒L₂2/\1 {p = ∙} {p₂} {p₃})

mip≗ p ._ refl (⊗L⇒L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2>L1 (gt {W₂ = W₂} q refl refl refl)
  rewrite subeq-2>L1 p W₂ (U₁ ⊛ η (A ⇒ B)) (q ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) |
          subeq-2>L1 p W₂ (η (A' ⊗ B')) (q ++ (sub p₂ (η B) ▸ p₃)) |
          subeq-2>L1 p W₂ (η (A' ⊗ B')) (q ++ (sub p₂ (U₁ ⊛ η (A ⇒ B)) ▸ p₃)) |
          subeq-2>L1 p W₂ (U₁ ⊛ η (A ⇒ B)) (q ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) = intrp≗ refl refl (⊗L⇒L₂2/\1 {p = q ◂ _} {p₂} {p₃})

mip≗ p ._ refl (⊗L⇒L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2>R1 (gt {W₁} q refl refl refl) 
  rewrite subeq-2>R1 p W₁ (U₁ ⊛ η (A ⇒ B)) (q ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) |
          subeq-2>R1 p W₁ (η (A' ⊗ B')) (q ++ (sub p₂ (η B) ▸ p₃)) |
          subeq-2>R1 p W₁ (η (A' ⊗ B')) (q ++ (sub p₂ (U₁ ⊛ η (A ⇒ B)) ▸ p₃)) |
          subeq-2>R1 p W₁ (U₁ ⊛ η (A ⇒ B)) (q ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) = intrp≗ refl refl (⊗L⇒L₂2/\1 {p = _ ▸ q} {p₂} {p₃})

mip≗ p U eq₁ (⊗L⇒L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt q refl eqU refl) with subeq _ _ q p₂ (sym ((⊛eq eqU) .proj₁))
mip≗ ._ ._ refl (⊗L⇒L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (η (A' ⊗ B')))) (U₁ ⊛ η (A ⇒ B)) |
          subeq-1/\2 p₁ (η B) (η (A' ⊗ B')) q p₃ |
          subeq-1/\2 p₁ (U₁ ⊛ η (A ⇒ B)) (η (A' ⊗ B')) q p₃ |
          subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (η A' ⊛ η B'))) (U₁ ⊛ η (A ⇒ B)) = intrp≗ refl refl refl
          
mip≗ ._ ._ refl (⊗L⇒L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl)
  rewrite subeq-2>L1 (p₁ ++ (q ◂ sub p₃ (η (A' ⊗ B')))) W₂ (U₁ ⊛ η (A ⇒ B)) q₁ |
          subeq-1/\2 p₁ (sub q₁ (η B) ⊛ W₂) (η (A' ⊗ B')) q p₃ |
          subeq-1/\2 p₁ (sub q₁ (U₁ ⊛ η (A ⇒ B)) ⊛ W₂) (η (A' ⊗ B')) q p₃ |
          subeq-2>L1 (p₁ ++ (q ◂ sub p₃ (η A' ⊛ η B'))) W₂ (U₁ ⊛ η (A ⇒ B)) q₁ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⊗L⇒L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 2>R1 (gt {W₁} q₁ refl refl refl)
  rewrite subeq-2>R1 (p₁ ++ (q ◂ sub p₃ (η (A' ⊗ B')))) W₁ (U₁ ⊛ η (A ⇒ B)) q₁ |
          subeq-1/\2 p₁ (W₁ ⊛ sub q₁ (η B)) (η (A' ⊗ B')) q p₃ |
          subeq-1/\2 p₁ (W₁ ⊛ sub q₁ (U₁ ⊛ η (A ⇒ B))) (η (A' ⊗ B')) q p₃ |
          subeq-2>R1 (p₁ ++ (q ◂ sub p₃ (η A' ⊛ η B'))) W₁ (U₁ ⊛ η (A ⇒ B)) q₁ = intrp≗ refl refl refl

mip≗ ._ U refl (⊗L⇒L₂2/\1 {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1>L2 (gt q₁ refl refl refl) 
  rewrite subeq-1>L2 (p₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) (η (A ⇒ B)) U q₁ |
          subeq-1/\2 p₁ U (η (A' ⊗ B')) (p₂ ++ (q₁ ◂ η (A ⇒ B))) p₃ |
          subeq-1/\2 p₁ U (η A' ⊛ η B') (p₂ ++ (q₁ ◂ η (A ⇒ B))) p₃ |
          subeq-1>L2 (p₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) (η (A ⇒ B)) U q₁ = intrp≗ refl (⊗L⇒L₂2/\1 {p = p₁} {p₂} {p₃}) refl

mip≗ ._ ._ refl (⊗L⇒L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1>R2 (gt ∙ refl refl refl)
  rewrite subeq-1>R2 (p₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) U₁ (η (A ⇒ B)) ∙ |
          subeq-1/\2 p₁ (η B) (η (A' ⊗ B')) p₂ p₃ |
          subeq-1/\2 p₁ (η (A ⇒ B)) (η (A' ⊗ B')) (p₂ ++ (U₁ ▸ ∙)) p₃ |
          subeq-1>R2 (p₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) U₁ (η (A ⇒ B)) ∙ =  intrp≗ refl (⊗L⇒L₂2/\1 {p = p₁} {p₂} {p₃}) refl

mip≗ ._ U refl (⊗L⇒L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (q₁ ◂ (sub p₃ (η (A' ⊗ B'))))) U (U₁ ⊛ η (A ⇒ B)) q₂ q₃ |
          subeq-1/\2 p₁ U (η (A' ⊗ B')) (q₁ ++ (q₂ ◂ sub q₃ (η B))) p₃ |
          subeq-1/\2 p₁ U (η (A' ⊗ B')) (q₁ ++ (q₂ ◂ sub q₃ (U₁ ⊛ η (A ⇒ B)))) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ (sub p₃ (η A' ⊛ η B')))) U (U₁ ⊛ η (A ⇒ B)) q₂ q₃ = intrp≗ refl (⊗L⇒L₂2/\1 {p = p₁}  {q₁ ++ (_ ▸ q₃)} {p₃}) refl

mip≗ ._ U refl (⊗L⇒L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (q₁ ◂ (sub p₃ (η (A' ⊗ B'))))) U (U₁ ⊛ η (A ⇒ B)) q₂ q₃ |
          subeq-1/\2 p₁ U (η (A' ⊗ B')) (q₁ ++ (sub q₂ (η B) ▸ q₃)) p₃ |
          subeq-1/\2 p₁ U (η (A' ⊗ B')) (q₁ ++ (sub q₂ (U₁ ⊛ η (A ⇒ B)) ▸ q₃)) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ (sub p₃ (η A' ⊛ η B')))) U (U₁ ⊛ η (A ⇒ B)) q₂ q₃ = intrp≗ refl (⊗L⇒L₂2/\1 {p = p₁} {q₁ ++ (q₂ ◂ _)} {p₃}) refl

mip≗ p U eq₁ (⊗L⇒L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt q refl eqU refl) with subeq _ _ q p₃ (sym ((⊛eq eqU) .proj₂))
mip≗ ._ ._ refl (⊗L⇒L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._})  | 1>R2 (gt q refl refl refl) | 1≡2 (same refl refl refl)
  rewrite subeq-2/\1 p₁ (η (A' ⊗ B')) (U₁ ⊛ η (A ⇒ B)) p₂ q |
          subeq-1≡2 (p₁ ++ (sub p₂ (U₁ ⊛ η (A ⇒ B)) ▸ q)) (η (A' ⊗ B')) |
          subeq-1≡2 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (A' ⊗ B')) |
          subeq-2/\1 p₁ (η A' ⊛ η B') (U₁ ⊛ η (A ⇒ B)) p₂ q = intrp≗ refl refl refl

mip≗ ._ ._ refl (⊗L⇒L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl) 
  rewrite subeq-2/\1 p₁ (sub q₁ (η (A' ⊗ B')) ⊛ W₂) (U₁ ⊛ η (A ⇒ B)) p₂ q |
          subeq-2>L1 (p₁ ++ (sub p₂ (η B) ▸ q)) W₂ (η (A' ⊗ B')) q₁ |
          subeq-2>L1 (p₁ ++ (sub p₂ (U₁ ⊛ η (A ⇒ B)) ▸ q)) W₂ (η (A' ⊗ B')) q₁ |
          subeq-2/\1 p₁ (sub q₁ (η A' ⊛ η B') ⊛ W₂) (U₁ ⊛ η (A ⇒ B)) p₂ q = intrp≗ refl refl refl

mip≗ ._ ._ refl (⊗L⇒L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 2>R1 (gt {W₁} q₁ refl refl refl) 
  rewrite subeq-2/\1 p₁ (W₁ ⊛ sub q₁ (η (A' ⊗ B'))) (U₁ ⊛ η (A ⇒ B)) p₂ q |
          subeq-2>R1 (p₁ ++ (sub p₂ (η B) ▸ q)) W₁ (η (A' ⊗ B')) q₁ |
          subeq-2>R1 (p₁ ++ (sub p₂ (U₁ ⊛ η (A ⇒ B)) ▸ q)) W₁ (η (A' ⊗ B')) q₁ |
          subeq-2/\1 p₁ (W₁ ⊛ sub q₁ (η A' ⊛ η B')) (U₁ ⊛ η (A ⇒ B)) p₂ q = intrp≗ refl refl refl

mip≗ ._ U refl (⊗L⇒L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ U (U₁ ⊛ η (A ⇒ B)) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q₁)) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (sub p₂ (U₁ ⊛ η (A ⇒ B)) ▸ q₁)) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-2/\1 p₁ U (U₁ ⊛ η (A ⇒ B)) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) = intrp≗ refl (⊗L⇒L₂2/\1 {p = p₁} {p₂} {q₁ ++ (_ ▸ q₃)}) refl

mip≗ ._ U refl (⊗L⇒L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ U (U₁ ⊛ η (A ⇒ B)) p₂ (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q₁)) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (sub p₂ (U₁ ⊛ η (A ⇒ B)) ▸ q₁)) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-2/\1 p₁ U (U₁ ⊛ η (A ⇒ B)) p₂ (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) = intrp≗ refl (⊗L⇒L₂2/\1 {p = p₁} {p₂} {q₁ ++ (q₂ ◂ _)}) refl

mip≗ ._ U refl (⊗L⇒L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q U (U₁ ⊛ η (A ⇒ B)) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) |
          subeq-1/\2 q U (η (A' ⊗ B')) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃))  |
          subeq-1/\2 q U (η (A' ⊗ B')) q₁ (q₂ ++ (sub p₂ (U₁ ⊛ η (A ⇒ B)) ▸ p₃)) |
          subeq-1/\2 q U (U₁ ⊛ η (A ⇒ B)) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) = intrp≗ refl (⊗L⇒L₂2/\1 {p = q ++ (_ ▸ q₂)} {p₂} {p₃}) refl

mip≗ ._ U refl (⊗L⇒L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q U (U₁ ⊛ η (A ⇒ B)) (q₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) q₂ |
          subeq-2/\1 q U (η (A' ⊗ B')) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ |
          subeq-2/\1 q U (η (A' ⊗ B')) (q₁ ++ (sub p₂ (U₁ ⊛ η (A ⇒ B)) ▸ p₃)) q₂ |
          subeq-2/\1 q U (U₁ ⊛ η (A ⇒ B)) (q₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) q₂ = intrp≗ refl (⊗L⇒L₂2/\1 {p = q ++ (q₁ ◂ _)} {p₂} {p₃}) refl

mip≗ p U eq₁ (⊗L⇐L₁ {p = q} {q'}) with subeq U _ p q' (sym eq₁)
mip≗ p ._ refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = q} {q'}) | 1≡2 (same refl refl refl) 
  rewrite subeq-2>R1 p (η (B ⇐ A)) (η (A' ⊗ B')) q |
          subeq-1≡2 p (η (B ⇐ A) ⊛ sub q (η A' ⊛ η B')) = 
          intrp≗ refl refl ⊗L⇐L₁ 
mip≗ p ._ refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = q} {q'}) | 2>L1 (gt {W₂ = W₂} r refl refl refl) 
  rewrite subeq-2>L1 p W₂ (η (A' ⊗ B')) (r ++ (η (B ⇐ A) ▸ q)) |
          subeq-2>L1 p W₂ (η (B ⇐ A) ⊛ sub q (η A' ⊛ η B')) r =
          intrp≗ refl refl ⊗L⇐L₁ 
mip≗ p ._ refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = q} {q'}) | 2>R1 (gt {W₁} r refl refl refl) 
  rewrite subeq-2>R1 p W₁ (η (A' ⊗ B')) (r ++ (η (B ⇐ A) ▸ q)) |
          subeq-2>R1 p W₁ (η (B ⇐ A) ⊛ sub q (η A' ⊛ η B')) r = 
          intrp≗ refl refl ⊗L⇐L₁ 
-- B ⇐ A is the interpolant tree          
mip≗ ._ ._ refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = ∙} {q'}) | 1>L2 (gt ∙ refl refl refl) 
  rewrite subeq-1/\2 q' (η (B ⇐ A)) (η (A' ⊗ B')) ∙ ∙ |
          subeq-1>L2 q' (η A' ⊛ η B') (η (B ⇐ A)) ∙ = intrp≗ refl ⊗L⇐L₁ (⇐R (⇐L refl refl)) -- this is refl but I write (⇐R (⇐L refl refl))
mip≗ ._ ._ refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = q ◂ U} {q'}) | 1>L2 (gt ∙ refl refl refl)    -- to remind that this is the principal case
  rewrite subeq-1/\2 q' (η (B ⇐ A)) (η (A' ⊗ B')) ∙ (q ◂ U) |
          subeq-1>L2 q' (sub (q ◂ U) (η A' ⊛ η B')) (η (B ⇐ A)) ∙ = 
          intrp≗ refl ⊗L⇐L₁ (⇐R (⇐L refl refl))
mip≗ ._ ._ refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = T ▸ q} {q'}) | 1>L2 (gt ∙ refl refl refl) 
  rewrite subeq-1/\2 q' (η (B ⇐ A)) (η (A' ⊗ B')) ∙ (T ▸ q) |
          subeq-1>L2 q' (sub (T ▸ q) (η A' ⊛ η B')) (η (B ⇐ A)) ∙ = 
          intrp≗ refl ⊗L⇐L₁ (⇐R (⇐L refl refl))
-- B ⇐ A is the interpolant tree          
     
mip≗ ._ _ eq₁ (⊗L⇐L₁ {p = q} {q'}) | 1>R2 (gt r refl eqU refl) with subeq _ _ r q (sym (⊛eq eqU .proj₂))
mip≗ ._ ._ refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = _} {q'}) | 1>R2 (gt r refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 r (η (A' ⊗ B')) |
          subeq-1≡2 (q' ++ (η (B ⇐ A) ▸ r)) (η (A' ⊗ B')) |
          subeq-1>R2 q' (η (B ⇐ A)) (η A' ⊛ η B') r = 
          intrp≗ refl refl refl 
mip≗ ._ ._ refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = _} {q'}) | 1>R2 (gt r refl refl refl) | 2>L1 (gt {W₂ = W₂} q refl refl refl) 
  rewrite subeq-2>L1 r W₂ (η (A' ⊗ B')) q |
          subeq-2>L1 (q' ++ (η (B ⇐ A) ▸ r)) W₂ (η (A' ⊗ B')) q |
          subeq-1>R2 q' (η (B ⇐ A)) (sub q (η A' ⊛ η B') ⊛ W₂) r = 
          intrp≗ refl refl refl   
mip≗ ._ ._ refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = _} {q'}) | 1>R2 (gt r refl refl refl) | 2>R1 (gt {W₁} q refl refl refl) 
  rewrite subeq-2>R1 r W₁ (η (A' ⊗ B')) q |
          subeq-2>R1 (q' ++ (η (B ⇐ A) ▸ r)) W₁ (η (A' ⊗ B')) q |
          subeq-1>R2 q' (η (B ⇐ A)) (W₁ ⊛ sub q (η A' ⊛ η B')) r =
          intrp≗ refl refl refl
mip≗ ._ U refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = _} {q'}) | 1>R2 (gt ._ refl refl refl) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q U (η (A' ⊗ B')) q₁ q₂ |
          subeq-1/\2 (q' ++ (η (B ⇐ A) ▸ q)) U (η (A' ⊗ B')) q₁ q₂ |
          subeq-1>R2 q' (η (B ⇐ A)) U (q ++ (q₁ ◂ sub q₂ (η A' ⊛ η B'))) = 
          intrp≗ refl ⊗L⇐L₁ refl
mip≗ ._ U refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = _} {q'}) | 1>R2 (gt ._ refl refl refl) | 2/\1 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-2/\1 q U (η (A' ⊗ B')) q₁ q₂ |
          subeq-2/\1 (q' ++ (η (B ⇐ A) ▸ q)) U (η (A' ⊗ B')) q₁ q₂ |
          subeq-1>R2 q' (η (B ⇐ A)) U (q ++ (sub q₁ (η A' ⊛ η B') ▸ q₂)) =
          intrp≗ refl ⊗L⇐L₁ refl

mip≗ ._ U refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = q}) | 1/\2 (disj r r₁ r₂ refl refl refl refl) 
  rewrite subeq-1/\2 r U (η (A' ⊗ B')) r₁ (r₂ ++ (η (B ⇐ A) ▸ q)) |
          subeq-1/\2 r U (η (B ⇐ A) ⊛ sub q (η A' ⊛ η B')) r₁ r₂ = 
          intrp≗ refl ⊗L⇐L₁ refl
mip≗ ._ U refl (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = q}) | 2/\1 (disj r r₁ r₂ refl refl refl refl) 
  rewrite subeq-2/\1 r U (η (A' ⊗ B')) (r₁ ++ (η (B ⇐ A) ▸ q)) r₂ |
          subeq-2/\1 r U (η (B ⇐ A) ⊛ sub q (η A' ⊛ η B')) r₁ r₂ = 
          intrp≗ refl ⊗L⇐L₁ refl 

mip≗ p U eq₁ (⊗L⇐L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) with subeq U _ p p₁ (sym eq₁) 
mip≗ p ._ refl (⊗L⇐L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1≡2 (same refl refl refl) 
  rewrite subeq-2>R1 p (sub p₂ (η (A' ⊗ B'))) (η (B ⇐ A) ⊛ U₁) p₃ |
          subeq-2>L1 p (sub p₃ (η B)) (η (A' ⊗ B')) p₂ |
          subeq-2>L1 p (sub p₃ (η (B ⇐ A) ⊛ U₁)) (η (A' ⊗ B')) p₂ |
          subeq-2>R1 p (sub p₂ (η A' ⊛ η B')) (η (B ⇐ A) ⊛ U₁) p₃ = intrp≗ refl refl (⊗L⇐L₂1/\2 {p = ∙} {p₂} {p₃})

mip≗ p ._ refl (⊗L⇐L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2>L1 (gt {W₂ = W₂} q refl refl refl) 
  rewrite subeq-2>L1 p W₂ (η (B ⇐ A) ⊛ U₁) (q ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) |
          subeq-2>L1 p W₂ (η (A' ⊗ B')) (q ++ (p₂ ◂ sub p₃ (η B))) |
          subeq-2>L1 p W₂ (η (A' ⊗ B')) (q ++ (p₂ ◂ sub p₃ (η (B ⇐ A) ⊛ U₁))) |
          subeq-2>L1 p W₂ (η (B ⇐ A) ⊛ U₁) (q ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) = intrp≗ refl refl (⊗L⇐L₂1/\2 {p = q ◂ _} {p₂} {p₃})

mip≗ p ._ refl (⊗L⇐L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2>R1 (gt {W₁} q refl refl refl) 
  rewrite subeq-2>R1 p W₁ (η (B ⇐ A) ⊛ U₁) (q ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) |
          subeq-2>R1 p W₁ (η (A' ⊗ B')) (q ++ (p₂ ◂ sub p₃ (η B))) |
          subeq-2>R1 p W₁ (η (A' ⊗ B')) (q ++ (p₂ ◂ sub p₃ (η (B ⇐ A) ⊛ U₁))) |
          subeq-2>R1 p W₁ (η (B ⇐ A) ⊛ U₁) (q ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) = intrp≗ refl refl (⊗L⇐L₂1/\2 {p = _ ▸ q} {p₂} {p₃})

mip≗ p U eq₁ (⊗L⇐L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt q refl eqU refl) with subeq _ _ q p₂ (sym ((⊛eq eqU) .proj₁))
mip≗ ._ ._ refl (⊗L⇐L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃})  | 1>L2 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1/\2 p₁ (η (A' ⊗ B')) (η (B ⇐ A) ⊛ U₁) q p₃ |
          subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (η (B ⇐ A) ⊛ U₁))) (η (A' ⊗ B')) |
          subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (η B))) (η (A' ⊗ B')) |
          subeq-1/\2 p₁ (η A' ⊛ η B') (η (B ⇐ A) ⊛ U₁) q p₃ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⊗L⇐L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl) 
  rewrite subeq-1/\2 p₁ (sub q₁ (η (A' ⊗ B')) ⊛ W₂) (η (B ⇐ A) ⊛ U₁) q p₃ |
          subeq-2>L1 (p₁ ++ (q ◂ sub p₃ (η B))) W₂ (η (A' ⊗ B')) q₁ |
          subeq-2>L1 (p₁ ++ (q ◂ sub p₃ (η (B ⇐ A) ⊛ U₁))) W₂ (η (A' ⊗ B')) q₁ |
          subeq-1/\2 p₁ (sub q₁ (η A' ⊛ η B') ⊛ W₂) (η (B ⇐ A) ⊛ U₁) q p₃ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⊗L⇐L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 2>R1 (gt {W₁} q₁ refl refl refl) 
  rewrite subeq-1/\2 p₁ (W₁ ⊛ sub q₁ (η (A' ⊗ B'))) (η (B ⇐ A) ⊛ U₁) q p₃ |
          subeq-2>R1 (p₁ ++ (q ◂ sub p₃ (η B))) W₁ (η (A' ⊗ B')) q₁ |
          subeq-2>R1 (p₁ ++ (q ◂ sub p₃ (η (B ⇐ A) ⊛ U₁))) W₁ (η (A' ⊗ B')) q₁ |
          subeq-1/\2 p₁ (W₁ ⊛ sub q₁ (η A' ⊛ η B')) (η (B ⇐ A) ⊛ U₁) q p₃ = intrp≗ refl refl refl

mip≗ ._ U refl (⊗L⇐L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 p₁ U (η (B ⇐ A) ⊛ U₁) (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) p₃  |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η B))) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (B ⇐ A) ⊛ U₁))) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-1/\2 p₁ U (η (B ⇐ A) ⊛ U₁) (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) p₃ = intrp≗ refl (⊗L⇐L₂1/\2 {p = p₁} {q₁ ++ (_ ▸ q₃)}) refl 

mip≗ ._ U refl (⊗L⇐L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 p₁ U (η (B ⇐ A) ⊛ U₁) (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η B))) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (B ⇐ A) ⊛ U₁))) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-1/\2 p₁ U (η (B ⇐ A) ⊛ U₁) (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) p₃ = intrp≗ refl (⊗L⇐L₂1/\2 {p = p₁} {q₁ ++ (q₂ ◂ _)} {p₃}) refl

mip≗ p U eq₁ (⊗L⇐L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt q refl eqU refl) with subeq _ _ q p₃ (sym ((⊛eq eqU) .proj₂))
mip≗ ._ ._ refl (⊗L⇐L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q)) (η (B ⇐ A) ⊛ U₁) |
          subeq-2/\1 p₁ (η B) (η (A' ⊗ B')) p₂ q |
          subeq-2/\1 p₁ (η (B ⇐ A) ⊛ U₁) (η (A' ⊗ B')) p₂ q |
          subeq-1≡2 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q)) (η (B ⇐ A) ⊛ U₁) = intrp≗ refl refl refl
          
mip≗ ._ ._ refl (⊗L⇐L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q)) W₂ (η (B ⇐ A) ⊛ U₁) q₁ |
          subeq-2/\1 p₁ (sub q₁ (η B) ⊛ W₂) (η (A' ⊗ B')) p₂ q |
          subeq-2/\1 p₁ (sub q₁ (η (B ⇐ A) ⊛ U₁) ⊛ W₂) (η (A' ⊗ B')) p₂ q |
          subeq-2>L1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q)) W₂ (η (B ⇐ A) ⊛ U₁) q₁ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⊗L⇐L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 2>R1 (gt {W₁} q₁ refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ q)) W₁ (η (B ⇐ A) ⊛ U₁) q₁ |
          subeq-2/\1 p₁ (W₁ ⊛ sub q₁ (η B)) (η (A' ⊗ B')) p₂ q |
          subeq-2/\1 p₁ (W₁ ⊛ sub q₁ (η (B ⇐ A) ⊛ U₁)) (η (A' ⊗ B')) p₂ q |
          subeq-2>R1 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ q)) W₁ (η (B ⇐ A) ⊛ U₁) q₁ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⊗L⇐L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt ._ refl refl refl) | 1>L2 (gt ∙ refl refl refl) 
  rewrite subeq-1>L2 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) U₁ (η (B ⇐ A)) ∙ |
          subeq-2/\1 p₁ (η B) (η (A' ⊗ B')) p₂ p₃ |
          subeq-2/\1 p₁ (η (B ⇐ A)) (η (A' ⊗ B')) p₂ (p₃ ++ (∙ ◂ U₁)) |
          subeq-1>L2 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) U₁ (η (B ⇐ A)) ∙ =  intrp≗ refl (⊗L⇐L₂1/\2 {p = p₁} {p₂} {p₃}) refl

mip≗ ._ U refl (⊗L⇐L₂1/\2 {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt ._ refl refl refl) | 1>R2 (gt q₁ refl refl refl)
  rewrite subeq-1>R2 (p₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) (η (B ⇐ A)) U q₁ |
          subeq-2/\1 p₁ U (η (A' ⊗ B')) p₂ (p₃ ++ (η (B ⇐ A) ▸ q₁)) |
          subeq-2/\1 p₁ U (η A' ⊛ η B') p₂ (p₃ ++ (η (B ⇐ A) ▸ q₁)) |
          subeq-1>R2 (p₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) (η (B ⇐ A)) U q₁ =  intrp≗ refl (⊗L⇐L₂1/\2 {p = p₁} {p₂} {p₃}) refl
  
mip≗ ._ U refl (⊗L⇐L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ ((sub p₂ (η (A' ⊗ B'))) ▸ q₁)) U (η (B ⇐ A) ⊛ U₁) q₂ q₃ |
          subeq-2/\1 p₁ U (η (A' ⊗ B')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η B))) |
          subeq-2/\1 p₁ U (η (A' ⊗ B')) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (B ⇐ A) ⊛ U₁))) |
          subeq-1/\2 (p₁ ++ ((sub p₂ (η A' ⊛ η B')) ▸ q₁)) U (η (B ⇐ A) ⊛ U₁) q₂ q₃ = intrp≗ refl (⊗L⇐L₂1/\2 {p = p₁} {p₂} {q₁ ++ (_ ▸ q₃)}) refl

mip≗ ._ U refl (⊗L⇐L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ ((sub p₂ (η (A' ⊗ B'))) ▸ q₁)) U (η (B ⇐ A) ⊛ U₁) q₂ q₃ |
          subeq-2/\1 p₁ U (η (A' ⊗ B')) p₂ (q₁ ++ (sub q₂ (η B) ▸ q₃)) |
          subeq-2/\1 p₁ U (η (A' ⊗ B')) p₂ (q₁ ++ (sub q₂ (η (B ⇐ A) ⊛ U₁) ▸ q₃)) |
          subeq-2/\1 (p₁ ++ ((sub p₂ (η A' ⊛ η B')) ▸ q₁)) U (η (B ⇐ A) ⊛ U₁) q₂ q₃ = intrp≗ refl (⊗L⇐L₂1/\2 {p = p₁} {p₂} {q₁ ++ (q₂ ◂ _)}) refl

mip≗ ._ U refl (⊗L⇐L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q U (η (B ⇐ A) ⊛ U₁) q₁ (q₂ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) |
          subeq-1/\2 q U (η (A' ⊗ B')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η B))) |
          subeq-1/\2 q U (η (A' ⊗ B')) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (B ⇐ A) ⊛ U₁))) |
          subeq-1/\2 q U (η (B ⇐ A) ⊛ U₁) q₁ (q₂ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) = intrp≗ refl (⊗L⇐L₂1/\2 {p = q ++ (_ ▸ q₂)} {p₂} {p₃}) refl

mip≗ ._ U refl (⊗L⇐L₂1/\2 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q U (η (B ⇐ A) ⊛ U₁) (q₁ ++ (sub p₂ (η (A' ⊗ B')) ▸ p₃)) q₂ |
          subeq-2/\1 q U (η (A' ⊗ B')) (q₁ ++ (p₂ ◂ sub p₃ (η B))) q₂ |
          subeq-2/\1 q U (η (A' ⊗ B')) (q₁ ++ (p₂ ◂ sub p₃ (η (B ⇐ A) ⊛ U₁))) q₂ |
          subeq-2/\1 q U (η (B ⇐ A) ⊛ U₁) (q₁ ++ (sub p₂ (η A' ⊛ η B') ▸ p₃)) q₂ = intrp≗ refl (⊗L⇐L₂1/\2 {p = q ++ (q₁ ◂ _)} {p₂} {p₃}) refl

mip≗ p U eq₁ (⊗L⇐L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) with subeq U _ p p₁ (sym eq₁) 
mip≗ p ._ refl (⊗L⇐L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1≡2 (same refl refl refl)
  rewrite subeq-2>L1 p (sub p₃ (η (A' ⊗ B'))) (η (B ⇐ A) ⊛ U₁) p₂ |
          subeq-2>R1 p (sub p₂ (η B)) (η (A' ⊗ B')) p₃ |
          subeq-2>R1 p (sub p₂ (η (B ⇐ A) ⊛ U₁)) (η (A' ⊗ B')) p₃ |
          subeq-2>L1 p (sub p₃ (η A' ⊛ η B')) (η (B ⇐ A) ⊛ U₁) p₂ = intrp≗ refl refl (⊗L⇐L₂2/\1 {p = ∙} {p₂} {p₃})

mip≗ p ._ refl (⊗L⇐L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2>L1 (gt {W₂ = W₂} q refl refl refl)
  rewrite subeq-2>L1 p W₂ (η (B ⇐ A) ⊛ U₁) (q ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) |
          subeq-2>L1 p W₂ (η (A' ⊗ B')) (q ++ (sub p₂ (η B) ▸ p₃)) |
          subeq-2>L1 p W₂ (η (A' ⊗ B')) (q ++ (sub p₂ (η (B ⇐ A) ⊛ U₁) ▸ p₃)) |
          subeq-2>L1 p W₂ (η (B ⇐ A) ⊛ U₁) (q ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) = intrp≗ refl refl (⊗L⇐L₂2/\1 {p = q ◂ _} {p₂} {p₃})

mip≗ p ._ refl (⊗L⇐L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2>R1 (gt {W₁} q refl refl refl) 
  rewrite subeq-2>R1 p W₁ (η (B ⇐ A) ⊛ U₁) (q ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) |
          subeq-2>R1 p W₁ (η (A' ⊗ B')) (q ++ (sub p₂ (η B) ▸ p₃)) |
          subeq-2>R1 p W₁ (η (A' ⊗ B')) (q ++ (sub p₂ (η (B ⇐ A) ⊛ U₁) ▸ p₃)) |
          subeq-2>R1 p W₁ (η (B ⇐ A) ⊛ U₁) (q ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) = intrp≗ refl refl (⊗L⇐L₂2/\1 {p = _ ▸ q} {p₂} {p₃})

mip≗ p U eq₁ (⊗L⇐L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt q refl eqU refl) with subeq _ _ q p₂ (sym ((⊛eq eqU) .proj₁))
mip≗ ._ ._ refl (⊗L⇐L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (η (A' ⊗ B')))) (η (B ⇐ A) ⊛ U₁) |
          subeq-1/\2 p₁ (η B) (η (A' ⊗ B')) q p₃ |
          subeq-1/\2 p₁ (η (B ⇐ A) ⊛ U₁) (η (A' ⊗ B')) q p₃ |
          subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (η A' ⊛ η B'))) (η (B ⇐ A) ⊛ U₁) = intrp≗ refl refl refl
          
mip≗ ._ ._ refl (⊗L⇐L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl)
  rewrite subeq-2>L1 (p₁ ++ (q ◂ sub p₃ (η (A' ⊗ B')))) W₂ (η (B ⇐ A) ⊛ U₁) q₁ |
          subeq-1/\2 p₁ (sub q₁ (η B) ⊛ W₂) (η (A' ⊗ B')) q p₃ |
          subeq-1/\2 p₁ (sub q₁ (η (B ⇐ A) ⊛ U₁) ⊛ W₂) (η (A' ⊗ B')) q p₃ |
          subeq-2>L1 (p₁ ++ (q ◂ sub p₃ (η A' ⊛ η B'))) W₂ (η (B ⇐ A) ⊛ U₁) q₁ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⊗L⇐L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 2>R1 (gt {W₁} q₁ refl refl refl)
  rewrite subeq-2>R1 (p₁ ++ (q ◂ sub p₃ (η (A' ⊗ B')))) W₁ (η (B ⇐ A) ⊛ U₁) q₁ |
          subeq-1/\2 p₁ (W₁ ⊛ sub q₁ (η B)) (η (A' ⊗ B')) q p₃ |
          subeq-1/\2 p₁ (W₁ ⊛ sub q₁ (η (B ⇐ A) ⊛ U₁)) (η (A' ⊗ B')) q p₃ |
          subeq-2>R1 (p₁ ++ (q ◂ sub p₃ (η A' ⊛ η B'))) W₁ (η (B ⇐ A) ⊛ U₁) q₁ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⊗L⇐L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1>L2 (gt ∙ refl refl refl) 
  rewrite subeq-1>L2 (p₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) U₁ (η (B ⇐ A)) ∙ |
          subeq-1/\2 p₁ (η B) (η (A' ⊗ B')) p₂ p₃ |
          subeq-1/\2 p₁ (η (B ⇐ A)) (η (A' ⊗ B')) (p₂ ++ (∙ ◂ U₁)) p₃ |
          subeq-1>L2 (p₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) U₁ (η (B ⇐ A)) ∙ =  intrp≗ refl (⊗L⇐L₂2/\1 {p = p₁} {p₂} {p₃}) refl

mip≗ ._ U refl (⊗L⇐L₂2/\1 {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1>R2 (gt q₁ refl refl refl) 
  rewrite subeq-1>R2 (p₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) (η (B ⇐ A)) U q₁ |
          subeq-1/\2 p₁ U (η (A' ⊗ B')) (p₂ ++ (η (B ⇐ A) ▸ q₁)) p₃ |
          subeq-1/\2 p₁ U (η A' ⊛ η B') (p₂ ++ (η (B ⇐ A) ▸ q₁)) p₃ |
          subeq-1>R2 (p₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) (η (B ⇐ A)) U q₁ = intrp≗ refl (⊗L⇐L₂2/\1 {p = p₁} {p₂} {p₃}) refl

mip≗ ._ U refl (⊗L⇐L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (q₁ ◂ (sub p₃ (η (A' ⊗ B'))))) U (η (B ⇐ A) ⊛ U₁) q₂ q₃ |
          subeq-1/\2 p₁ U (η (A' ⊗ B')) (q₁ ++ (q₂ ◂ sub q₃ (η B))) p₃ |
          subeq-1/\2 p₁ U (η (A' ⊗ B')) (q₁ ++ (q₂ ◂ sub q₃ (η (B ⇐ A) ⊛ U₁))) p₃ |
          subeq-1/\2 (p₁ ++ (q₁ ◂ (sub p₃ (η A' ⊛ η B')))) U (η (B ⇐ A) ⊛ U₁) q₂ q₃ = intrp≗ refl (⊗L⇐L₂2/\1 {p = p₁}  {q₁ ++ (_ ▸ q₃)} {p₃}) refl

mip≗ ._ U refl (⊗L⇐L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (q₁ ◂ (sub p₃ (η (A' ⊗ B'))))) U (η (B ⇐ A) ⊛ U₁) q₂ q₃ |
          subeq-1/\2 p₁ U (η (A' ⊗ B')) (q₁ ++ (sub q₂ (η B) ▸ q₃)) p₃ |
          subeq-1/\2 p₁ U (η (A' ⊗ B')) (q₁ ++ (sub q₂ (η (B ⇐ A) ⊛ U₁) ▸ q₃)) p₃ |
          subeq-2/\1 (p₁ ++ (q₁ ◂ (sub p₃ (η A' ⊛ η B')))) U (η (B ⇐ A) ⊛ U₁) q₂ q₃ = intrp≗ refl (⊗L⇐L₂2/\1 {p = p₁} {q₁ ++ (q₂ ◂ _)} {p₃}) refl

mip≗ p U eq₁ (⊗L⇐L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt q refl eqU refl) with subeq _ _ q p₃ (sym ((⊛eq eqU) .proj₂))
mip≗ ._ ._ refl (⊗L⇐L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._})  | 1>R2 (gt q refl refl refl) | 1≡2 (same refl refl refl)
  rewrite subeq-2/\1 p₁ (η (A' ⊗ B')) (η (B ⇐ A) ⊛ U₁) p₂ q |
          subeq-1≡2 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U₁) ▸ q)) (η (A' ⊗ B')) |
          subeq-1≡2 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (A' ⊗ B')) |
          subeq-2/\1 p₁ (η A' ⊛ η B') (η (B ⇐ A) ⊛ U₁) p₂ q = intrp≗ refl refl refl

mip≗ ._ ._ refl (⊗L⇐L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl) 
  rewrite subeq-2/\1 p₁ (sub q₁ (η (A' ⊗ B')) ⊛ W₂) (η (B ⇐ A) ⊛ U₁) p₂ q |
          subeq-2>L1 (p₁ ++ (sub p₂ (η B) ▸ q)) W₂ (η (A' ⊗ B')) q₁ |
          subeq-2>L1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U₁) ▸ q)) W₂ (η (A' ⊗ B')) q₁ |
          subeq-2/\1 p₁ (sub q₁ (η A' ⊛ η B') ⊛ W₂) (η (B ⇐ A) ⊛ U₁) p₂ q = intrp≗ refl refl refl

mip≗ ._ ._ refl (⊗L⇐L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 2>R1 (gt {W₁} q₁ refl refl refl) 
  rewrite subeq-2/\1 p₁ (W₁ ⊛ sub q₁ (η (A' ⊗ B'))) (η (B ⇐ A) ⊛ U₁) p₂ q |
          subeq-2>R1 (p₁ ++ (sub p₂ (η B) ▸ q)) W₁ (η (A' ⊗ B')) q₁ |
          subeq-2>R1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U₁) ▸ q)) W₁ (η (A' ⊗ B')) q₁ |
          subeq-2/\1 p₁ (W₁ ⊛ sub q₁ (η A' ⊛ η B')) (η (B ⇐ A) ⊛ U₁) p₂ q = intrp≗ refl refl refl

mip≗ ._ U refl (⊗L⇐L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ U (η (B ⇐ A) ⊛ U₁) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (A' ⊗ B')))) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q₁)) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-1/\2 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U₁) ▸ q₁)) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-2/\1 p₁ U (η (B ⇐ A) ⊛ U₁) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η A' ⊛ η B'))) = intrp≗ refl (⊗L⇐L₂2/\1 {p = p₁} {p₂} {q₁ ++ (_ ▸ q₃)}) refl

mip≗ ._ U refl (⊗L⇐L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ U (η (B ⇐ A) ⊛ U₁) p₂ (q₁ ++ (sub q₂ (η (A' ⊗ B')) ▸ q₃)) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q₁)) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-2/\1 (p₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U₁) ▸ q₁)) U (η (A' ⊗ B')) q₂ q₃ |
          subeq-2/\1 p₁ U (η (B ⇐ A) ⊛ U₁) p₂ (q₁ ++ (sub q₂ (η A' ⊛ η B') ▸ q₃)) = intrp≗ refl (⊗L⇐L₂2/\1 {p = p₁} {p₂} {q₁ ++ (q₂ ◂ _)}) refl

mip≗ ._ U refl (⊗L⇐L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-1/\2 q U (η (B ⇐ A) ⊛ U₁) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) |
          subeq-1/\2 q U (η (A' ⊗ B')) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃))  |
          subeq-1/\2 q U (η (A' ⊗ B')) q₁ (q₂ ++ (sub p₂ (η (B ⇐ A) ⊛ U₁) ▸ p₃)) |
          subeq-1/\2 q U (η (B ⇐ A) ⊛ U₁) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) = intrp≗ refl (⊗L⇐L₂2/\1 {p = q ++ (_ ▸ q₂)} {p₂} {p₃}) refl

mip≗ ._ U refl (⊗L⇐L₂2/\1 {U = U₁} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q U (η (B ⇐ A) ⊛ U₁) (q₁ ++ (p₂ ◂ sub p₃ (η (A' ⊗ B')))) q₂ |
          subeq-2/\1 q U (η (A' ⊗ B')) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ |
          subeq-2/\1 q U (η (A' ⊗ B')) (q₁ ++ (sub p₂ (η (B ⇐ A) ⊛ U₁) ▸ p₃)) q₂ |
          subeq-2/\1 q U (η (B ⇐ A) ⊛ U₁) (q₁ ++ (p₂ ◂ sub p₃ (η A' ⊛ η B'))) q₂ = intrp≗ refl (⊗L⇐L₂2/\1 {p = q ++ (q₁ ◂ _)} {p₂} {p₃}) refl

mip≗ p U eq₁ (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) with subeq _ _ p r (sym eq₁)
mip≗ p ._ refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1≡2 (same refl refl refl) 
  rewrite subeq-2>L1 p (η (A ⇒ B)) (T ⊛ η (A' ⇒ B')) q |
          subeq-1≡2 p (sub q (η B') ⊛ η (A ⇒ B)) = intrp≗ refl refl ⇒L⇒L

mip≗ p ._ refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl)
  rewrite subeq-2>L1 p W₂ (T ⊛ η (A' ⇒ B')) (q₁ ++ (q ◂ η (A ⇒ B))) |
          subeq-2>L1 p W₂ (sub q (η B') ⊛ η (A ⇒ B)) q₁ = intrp≗ refl refl ⇒L⇒L

mip≗ p ._ refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>R1 (gt {W₁} q₁ refl refl refl) 
  rewrite subeq-2>R1 p W₁ (T ⊛ η (A' ⇒ B')) (q₁ ++ (q ◂ η (A ⇒ B))) |
          subeq-2>R1 p W₁ (sub q (η B') ⊛ η (A ⇒ B)) q₁ = intrp≗ refl refl ⇒L⇒L

mip≗ p U eq₁ (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>L2 (gt q₁ refl eqU refl) with subeq _ _ q₁ q (sym (⊛eq eqU .proj₁))
mip≗ ._._ refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>L2 (gt q₁ refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 q₁ (T ⊛ η (A' ⇒ B')) |
          subeq-1≡2 (r ++ (q₁ ◂ η (A ⇒ B))) (T ⊛ η (A' ⇒ B')) |
          subeq-1>L2 r (η (A ⇒ B)) (η B') q₁ = intrp≗ refl refl refl

mip≗ ._._ refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>L2 (gt q₁ refl refl refl) | 2>L1 (gt {W₂ = W₂} q₂ refl refl refl) 
  rewrite subeq-2>L1 q₁ W₂ (T ⊛ η (A' ⇒ B')) q₂ |
          subeq-2>L1 (r ++ (q₁ ◂ η (A ⇒ B))) W₂ (T ⊛ η (A' ⇒ B')) q₂ |
          subeq-1>L2 r (η (A ⇒ B)) (sub q₂ (η B') ⊛ W₂) q₁ = intrp≗ refl refl refl

mip≗ ._._ refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>L2 (gt q₁ refl refl refl) | 2>R1 (gt {W₁} q₂ refl refl refl) 
  rewrite subeq-2>R1 q₁ W₁ (T ⊛ η (A' ⇒ B')) q₂ |
          subeq-2>R1 (r ++ (q₁ ◂ η (A ⇒ B))) W₁ (T ⊛ η (A' ⇒ B')) q₂ |
          subeq-1>L2 r (η (A ⇒ B)) (W₁ ⊛ sub q₂ (η B')) q₁ = intrp≗ refl refl refl

mip≗ ._ U refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>L2 (gt ._ refl refl refl) | 1>L2 (gt q₁ refl refl refl) 
  rewrite subeq-1>L2 q (η (A' ⇒ B')) U q₁ |
          subeq-1>L2 (r ++ (q ◂ η (A ⇒ B))) (η (A' ⇒ B')) U q₁ = intrp≗ refl ⇒L⇒L refl

mip≗ ._ ._ refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>L2 (gt ._ refl refl refl) | 1>R2 (gt ∙ refl refl refl) 
  rewrite subeq-1>R2 q T (η (A' ⇒ B')) ∙ |
          subeq-1>R2 (r ++ (q ◂ η (A ⇒ B))) T (η (A' ⇒ B')) ∙ |
          subeq-1>L2 r (η (A ⇒ B)) (η B') q = intrp≗ refl ⇒L⇒L refl

mip≗ ._ U refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>L2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ U (T ⊛ η (A' ⇒ B')) q₂ q₃ |
          subeq-1/\2 (r ++ (q₁ ◂ η (A ⇒ B))) U (T ⊛ η (A' ⇒ B')) q₂ q₃ |
          subeq-1>L2 r (η (A ⇒ B)) U (q₁ ++ (q₂ ◂ sub q₃ (η B'))) = intrp≗ refl ⇒L⇒L refl

mip≗ ._ U refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>L2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ U (T ⊛ η (A' ⇒ B')) q₂ q₃ |
          subeq-2/\1 (r ++ (q₁ ◂ η (A ⇒ B))) U (T ⊛ η (A' ⇒ B')) q₂ q₃ |
          subeq-1>L2 r (η (A ⇒ B)) U (q₁ ++ (sub q₂ (η B') ▸ q₃)) = intrp≗ refl ⇒L⇒L refl

mip≗ ._ ._  refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = ∙} {r}) | 1>R2 (gt ∙ refl refl refl)
  rewrite subeq-2/\1 r (η (A ⇒ B)) (T ⊛ η (A' ⇒ B')) ∙ ∙ |
          subeq-1>R2 r (η B') (η (A ⇒ B)) ∙ = intrp≗ refl (⇒L⇒L {q = ∙}) refl

mip≗ ._ ._  refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q ◂ U} {r}) | 1>R2 (gt ∙ refl refl refl) 
  rewrite subeq-2/\1 r (η (A ⇒ B)) (T ⊛ η (A' ⇒ B')) (q ◂ U) ∙ |
          subeq-1>R2 r (sub q (η B') ⊛ U) (η (A ⇒ B)) ∙ = intrp≗ refl ⇒L⇒L refl
          
mip≗ ._ ._  refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = T₁ ▸ q} {r}) | 1>R2 (gt ∙ refl refl refl) 
  rewrite subeq-2/\1 r (η (A ⇒ B)) (T ⊛ η (A' ⇒ B')) (T₁ ▸ q) ∙ |
          subeq-1>R2 r (T₁ ⊛ sub q (η B')) (η (A ⇒ B)) ∙ = intrp≗ refl ⇒L⇒L refl

mip≗ ._ U refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 q₁ U (T ⊛ η (A' ⇒ B')) q₂ (q₃ ++ (q ◂ η (A ⇒ B))) |
          subeq-1/\2 q₁ U (sub q (η B') ⊛ η (A ⇒ B)) q₂ q₃ = intrp≗ refl ⇒L⇒L refl
          
mip≗ ._ U refl (⇒L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ U (T ⊛ η (A' ⇒ B')) (q₂ ++ (q ◂ η (A ⇒ B))) q₃ |
          subeq-2/\1 q₁ U (sub q (η B') ⊛ η (A ⇒ B)) q₂ q₃ = intrp≗ refl ⇒L⇒L refl


mip≗ p U eq₁ (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) with subeq _ _ p p₁ (sym eq₁)
mip≗ p ._ refl (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1≡2 (same refl refl refl) 
  rewrite subeq-2>L1 p (sub p₃ (V ⊛ η (A' ⇒ B'))) (U₁ ⊛ η (A ⇒ B)) p₂ |
          subeq-2>R1 p (sub p₂ (η B)) (V ⊛ η (A' ⇒ B')) p₃ = intrp≗ refl refl (⇒L⇒L₂ {p = ∙} {p₂} {p₃})

mip≗ p ._ refl (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2>L1 (gt {W₂ = W₂} q refl refl refl) 
  rewrite subeq-2>L1 p W₂ (U₁ ⊛ η (A ⇒ B)) (q ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) |
          subeq-2>L1 p W₂ (V ⊛ η (A' ⇒ B')) (q ++ (sub p₂ (η B) ▸ p₃)) =  intrp≗ refl refl (⇒L⇒L₂ {p = q ◂ _} {p₂} {p₃})

mip≗ p ._ refl (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2>R1 (gt {W₁} q refl refl refl) 
  rewrite subeq-2>R1 p W₁ (U₁ ⊛ η (A ⇒ B)) (q ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) |
          subeq-2>R1 p W₁ (V ⊛ η (A' ⇒ B')) (q ++ (sub p₂ (η B) ▸ p₃)) = intrp≗ refl refl (⇒L⇒L₂ {p = _ ▸ q} {p₂} {p₃})

mip≗ p U eq₁ (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt q refl eqU refl) with subeq _ _ q p₂ (sym (⊛eq eqU .proj₁))
mip≗ ._ ._ refl (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (U₁ ⊛ η (A ⇒ B)) |
          subeq-1/\2 p₁ (η B') (U₁ ⊛ η (A ⇒ B)) q p₃ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (q ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) W₂ (U₁ ⊛ η (A ⇒ B)) q₁ |
          subeq-1/\2 p₁ (sub q₁ (η B) ⊛ W₂) (V ⊛ η (A' ⇒ B')) q p₃ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 2>R1 (gt {W₁} q₁ refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (q ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) W₁ (U₁ ⊛ η (A ⇒ B)) q₁ |
          subeq-1/\2 p₁ (W₁ ⊛ sub q₁ (η B)) (V ⊛ η (A' ⇒ B')) q p₃ = intrp≗ refl refl refl

mip≗ ._ U refl (⇒L⇒L₂ {U = ._} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1>L2 (gt q refl refl refl) 
  rewrite subeq-1>L2 (p₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (η (A ⇒ B)) U q  = intrp≗ refl (⇒L⇒L₂ {p = p₁}) refl

mip≗ ._ ._ refl (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1>R2 (gt ∙ refl refl refl) 
  rewrite subeq-1>R2 (p₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) U₁ (η (A ⇒ B)) ∙ |
          subeq-1/\2 p₁ (η B) (V ⊛ η (A' ⇒ B')) p₂ p₃ = intrp≗ refl (⇒L⇒L₂ {p = p₁}) refl

mip≗ ._ U refl (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) U (U₁ ⊛ η (A ⇒ B)) q₂ q₃ |
          subeq-1/\2 p₁ U (V ⊛ η (A' ⇒ B')) (q₁ ++ (q₂ ◂ sub q₃ (η B))) p₃ = intrp≗ refl (⇒L⇒L₂ {p = p₁} {q₁ ++ (_ ▸ q₃)} {p₃}) refl

mip≗ ._ U refl (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) U (U₁ ⊛ η (A ⇒ B)) q₂ q₃ | 
          subeq-1/\2 p₁ U (V ⊛ η (A' ⇒ B')) (q₁ ++ (sub q₂ (η B) ▸ q₃)) p₃ = intrp≗ refl (⇒L⇒L₂ {p = p₁} {q₁ ++ (q₂ ◂ _)} {p₃}) refl

mip≗ p U eq₁ (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt q refl eqU refl) with subeq _ _ q p₃ (sym (⊛eq eqU .proj₂))
mip≗ ._ ._ refl (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (U₁ ⊛ η (A ⇒ B)) p₂ q |
         subeq-1≡2 (p₁ ++ (sub p₂ (η B) ▸ q)) (V ⊛ η (A' ⇒ B')) = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl)
  rewrite subeq-2/\1 p₁ (sub q₁ (V ⊛ η (A' ⇒ B')) ⊛ W₂) (U₁ ⊛ η (A ⇒ B)) p₂ q |
          subeq-2>L1 (p₁ ++ (sub p₂ (η B) ▸ q)) W₂ (V ⊛ η (A' ⇒ B')) q₁ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 2>R1 (gt {W₁} q₁ refl refl refl) 
  rewrite subeq-2/\1 p₁ (W₁ ⊛ sub q₁ (V ⊛ η (A' ⇒ B'))) (U₁ ⊛ η (A ⇒ B)) p₂ q |
          subeq-2>R1 (p₁ ++ (q ◂ sub p₂ (η B))) W₁ (V ⊛ η (A' ⇒ B')) q₁ = intrp≗ refl refl refl
  
mip≗ ._ U refl (⇒L⇒L₂ {U = U₁} {._} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt ._ refl refl refl) | 1>L2 (gt q refl refl refl)
  rewrite subeq-2/\1 p₁ U (U₁ ⊛ η (A ⇒ B)) p₂ (p₃ ++ (q ◂ η (A' ⇒ B'))) |
          subeq-1>L2 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (A' ⇒ B')) U q = intrp≗ refl (⇒L⇒L₂ {p = p₁}) refl

mip≗ ._ ._ refl (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt ._ refl refl refl) | 1>R2 (gt ∙ refl refl refl)
  rewrite subeq-2/\1 p₁ (η (A' ⇒ B')) (U₁ ⊛ η (A ⇒ B)) p₂ (p₃ ++ (V ▸ ∙)) |
          subeq-1>R2 (p₁ ++ (sub p₂ (η B) ▸ p₃)) V (η (A' ⇒ B')) ∙ = intrp≗ refl (⇒L⇒L₂ {p = p₁}) refl

mip≗ ._ U refl (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ U (U₁ ⊛ η (A ⇒ B)) p₂ (q₁ ++ (q₂ ◂ sub q₃ (V ⊛ η (A' ⇒ B')))) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q₁)) U (V ⊛ η (A' ⇒ B')) q₂ q₃ = intrp≗ refl (⇒L⇒L₂ {p = p₁} {p₂} {q₁ ++ (_ ▸ q₃)}) refl

mip≗ ._ U refl (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ U (U₁ ⊛ η (A ⇒ B)) p₂ (q₁ ++ (sub q₂ (V ⊛ η (A' ⇒ B')) ▸ q₃)) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q₁)) U (V ⊛ η (A' ⇒ B')) q₂ q₃ = intrp≗ refl (⇒L⇒L₂ {p = p₁} {p₂} {q₁ ++ (q₂ ◂ _)}) refl 

mip≗ ._ U refl (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q U (U₁ ⊛ η (A ⇒ B)) q₁ (q₂ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) |
          subeq-1/\2 q U (V ⊛ η (A' ⇒ B')) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = intrp≗ refl (⇒L⇒L₂ {p = q ++ (_ ▸ q₂)}) refl
          
mip≗ ._ U refl (⇒L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q U (U₁ ⊛ η (A ⇒ B)) (q₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) q₂ |
          subeq-2/\1 q U (V ⊛ η (A' ⇒ B')) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = intrp≗ refl (⇒L⇒L₂ {p = q ++ (q₁ ◂ _)}) refl

mip≗ p U eq₁ (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) with subeq _ _ p r (sym eq₁)
mip≗ p ._ refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1≡2 (same refl refl refl) 
  rewrite subeq-2>R1 p (η (B ⇐ A)) (T ⊛ η (A' ⇒ B')) q |
          subeq-1≡2 p (η (B ⇐ A) ⊛ sub q (η B') ) = intrp≗ refl refl ⇒L⇐L

mip≗ p ._ refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl) 
  rewrite subeq-2>L1 p W₂ (T ⊛ η (A' ⇒ B')) (q₁ ++ (η (B ⇐ A) ▸ q)) |
          subeq-2>L1 p W₂ (η (B ⇐ A) ⊛ sub q (η B')) q₁ = intrp≗ refl refl ⇒L⇐L

mip≗ p ._ refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>R1 (gt {W₁} q₁ refl refl refl) 
  rewrite subeq-2>R1 p W₁ (T ⊛ η (A' ⇒ B')) (q₁ ++ (η (B ⇐ A) ▸ q)) |
          subeq-2>R1 p W₁ (η (B ⇐ A) ⊛ sub q (η B')) q₁ = intrp≗ refl refl ⇒L⇐L

mip≗ ._ ._  refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = ∙} {r}) | 1>L2 (gt ∙ refl refl refl) 
  rewrite subeq-1/\2 r (η (B ⇐ A)) (T ⊛ η (A' ⇒ B')) ∙ ∙ |
          subeq-1>L2 r (η B') (η (B ⇐ A)) ∙ = intrp≗ refl ⇒L⇐L refl

mip≗ ._ ._  refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q ◂ U} {r}) | 1>L2 (gt ∙ refl refl refl) 
  rewrite subeq-1/\2 r (η (B ⇐ A)) (T ⊛ η (A' ⇒ B')) ∙ (q ◂ U) |
          subeq-1>L2 r (sub q (η B') ⊛ U) (η (B ⇐ A)) ∙ = intrp≗ refl ⇒L⇐L refl
          
mip≗ ._ ._  refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = T₁ ▸ q} {r}) | 1>L2 (gt ∙ refl refl refl)
  rewrite subeq-1/\2 r (η (B ⇐ A)) (T ⊛ η (A' ⇒ B')) ∙ (T₁ ▸ q) |
          subeq-1>L2 r (T₁ ⊛ sub q (η B')) (η (B ⇐ A)) ∙ = intrp≗ refl ⇒L⇐L refl

mip≗ p U eq₁ (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>R2 (gt q₁ refl eqU refl) with subeq _ _ q₁ q (sym (⊛eq eqU .proj₂))
mip≗ ._._ refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>R2 (gt q₁ refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 q₁ (T ⊛ η (A' ⇒ B')) |
          subeq-1≡2 (r ++ (η (B ⇐ A) ▸ q₁)) (T ⊛ η (A' ⇒ B')) |
          subeq-1>R2 r (η (B ⇐ A)) (η B') q₁ = intrp≗ refl refl refl

mip≗ ._._ refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>R2 (gt q₁ refl refl refl) | 2>L1 (gt {W₂ = W₂} q₂ refl refl refl)
  rewrite subeq-2>L1 q₁ W₂ (T ⊛ η (A' ⇒ B')) q₂ |
          subeq-2>L1 (r ++ (η (B ⇐ A) ▸ q₁)) W₂ (T ⊛ η (A' ⇒ B')) q₂ |
          subeq-1>R2 r (η (B ⇐ A)) (sub q₂ (η B') ⊛ W₂) q₁ = intrp≗ refl refl refl

mip≗ ._._ refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>R2 (gt q₁ refl refl refl) | 2>R1 (gt {W₁} q₂ refl refl refl)
  rewrite subeq-2>R1 q₁ W₁ (T ⊛ η (A' ⇒ B')) q₂ |
          subeq-2>R1 (r ++ (η (B ⇐ A) ▸ q₁)) W₁ (T ⊛ η (A' ⇒ B')) q₂ |
          subeq-1>R2 r (η (B ⇐ A)) (W₁ ⊛ sub q₂ (η B')) q₁ = intrp≗ refl refl refl

mip≗ ._ U refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>R2 (gt ._ refl refl refl) | 1>L2 (gt q₁ refl refl refl) 
  rewrite subeq-1>L2 q (η (A' ⇒ B')) U q₁ |
          subeq-1>L2 (r ++ (η (B ⇐ A) ▸ q)) (η (A' ⇒ B')) U q₁ = intrp≗ refl ⇒L⇐L refl

mip≗ ._ ._ refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>R2 (gt ._ refl refl refl) | 1>R2 (gt ∙ refl refl refl) 
  rewrite subeq-1>R2 q T (η (A' ⇒ B')) ∙ |
          subeq-1>R2 (r ++ (η (B ⇐ A) ▸ q)) T (η (A' ⇒ B')) ∙ |
          subeq-1>R2 r (η (B ⇐ A)) (η B') q = intrp≗ refl ⇒L⇐L refl

mip≗ ._ U refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 1>R2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 q₁ U (T ⊛ η (A' ⇒ B')) q₂ q₃ |
          subeq-1/\2 (r ++ (η (B ⇐ A) ▸ q₁)) U (T ⊛ η (A' ⇒ B')) q₂ q₃ |
          subeq-1>R2 r (η (B ⇐ A)) U (q₁ ++ (q₂ ◂ sub q₃ (η B'))) = intrp≗ refl ⇒L⇐L refl

mip≗ ._ U refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 1>R2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q₁ U (T ⊛ η (A' ⇒ B')) q₂ q₃ |
          subeq-2/\1 (r ++ (η (B ⇐ A) ▸ q₁)) U (T ⊛ η (A' ⇒ B')) q₂ q₃ |
          subeq-1>R2 r (η (B ⇐ A)) U (q₁ ++ (sub q₂ (η B') ▸ q₃)) = intrp≗ refl ⇒L⇐L refl

mip≗ ._ U refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 q₁ U (T ⊛ η (A' ⇒ B')) q₂ (q₃ ++ (η (B ⇐ A) ▸ q)) |
          subeq-1/\2 q₁ U (η (B ⇐ A) ⊛ sub q (η B')) q₂ q₃ = intrp≗ refl ⇒L⇐L refl
          
mip≗ ._ U refl (⇒L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 q₁ U (T ⊛ η (A' ⇒ B')) (q₂ ++ (η (B ⇐ A) ▸ q)) q₃ |
          subeq-2/\1 q₁ U (η (B ⇐ A) ⊛ sub q (η B')) q₂ q₃ = intrp≗ refl ⇒L⇐L refl

mip≗ p U eq₁ (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) with subeq _ _ p p₁ (sym eq₁)
mip≗ p ._ refl (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1≡2 (same refl refl refl) 
  rewrite subeq-2>L1 p (sub p₃ (η (B' ⇐ A') ⊛ V)) (U₁ ⊛ η (A ⇒ B)) p₂ |
          subeq-2>R1 p (sub p₂ (η B)) (η (B' ⇐ A') ⊛ V) p₃ = intrp≗ refl refl (⇒L⇐L₂ {p = ∙} {p₂} {p₃})

mip≗ p ._ refl (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2>L1 (gt {W₂ = W₂} q refl refl refl)
  rewrite subeq-2>L1 p W₂ (U₁ ⊛ η (A ⇒ B)) (q ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) |
          subeq-2>L1 p W₂ (η (B' ⇐ A') ⊛ V) (q ++ (sub p₂ (η B) ▸ p₃)) =  intrp≗ refl refl (⇒L⇐L₂ {p = q ◂ _} {p₂} {p₃})

mip≗ p ._ refl (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2>R1 (gt {W₁} q refl refl refl)
  rewrite subeq-2>R1 p W₁ (U₁ ⊛ η (A ⇒ B)) (q ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) |
          subeq-2>R1 p W₁ (η (B' ⇐ A') ⊛ V) (q ++ (sub p₂ (η B) ▸ p₃)) = intrp≗ refl refl (⇒L⇐L₂ {p = _ ▸ q} {p₂} {p₃})

mip≗ p U eq₁ (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt q refl eqU refl) with subeq _ _ q p₂ (sym (⊛eq eqU .proj₁))
mip≗ ._ ._ refl (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 1≡2 (same refl refl refl)
  rewrite subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (U₁ ⊛ η (A ⇒ B)) |
          subeq-1/\2 p₁ (η B') (U₁ ⊛ η (A ⇒ B)) q p₃ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl)
  rewrite subeq-2>L1 (p₁ ++ (q ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) W₂ (U₁ ⊛ η (A ⇒ B)) q₁ |
          subeq-1/\2 p₁ (sub q₁ (η B) ⊛ W₂) (η (B' ⇐ A') ⊛ V) q p₃ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 2>R1 (gt {W₁} q₁ refl refl refl)
  rewrite subeq-2>R1 (p₁ ++ (q ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) W₁ (U₁ ⊛ η (A ⇒ B)) q₁ |
          subeq-1/\2 p₁ (W₁ ⊛ sub q₁ (η B)) (η (B' ⇐ A') ⊛ V) q p₃ = intrp≗ refl refl refl

mip≗ ._ U refl (⇒L⇐L₂ {U = ._} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1>L2 (gt q refl refl refl)
  rewrite subeq-1>L2 (p₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (η (A ⇒ B)) U q  = intrp≗ refl (⇒L⇐L₂ {p = p₁}) refl
-- 
mip≗ ._ ._ refl (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1>R2 (gt ∙ refl refl refl)
  rewrite subeq-1>R2 (p₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) U₁ (η (A ⇒ B)) ∙ |
          subeq-1/\2 p₁ (η B) (η (B' ⇐ A') ⊛ V) p₂ p₃ = intrp≗ refl (⇒L⇐L₂ {p = p₁}) refl

mip≗ ._ U refl (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) U (U₁ ⊛ η (A ⇒ B)) q₂ q₃ |
          subeq-1/\2 p₁ U (η (B' ⇐ A') ⊛ V) (q₁ ++ (q₂ ◂ sub q₃ (η B))) p₃ = intrp≗ refl (⇒L⇐L₂ {p = p₁} {q₁ ++ (_ ▸ q₃)} {p₃}) refl

mip≗ ._ U refl (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) U (U₁ ⊛ η (A ⇒ B)) q₂ q₃ | 
          subeq-1/\2 p₁ U (η (B' ⇐ A') ⊛ V) (q₁ ++ (sub q₂ (η B) ▸ q₃)) p₃ = intrp≗ refl (⇒L⇐L₂ {p = p₁} {q₁ ++ (q₂ ◂ _)} {p₃}) refl

mip≗ p U eq₁ (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt q refl eqU refl) with subeq _ _ q p₃ (sym (⊛eq eqU .proj₂))
mip≗ ._ ._ refl (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 1≡2 (same refl refl refl)
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (U₁ ⊛ η (A ⇒ B)) p₂ q |
         subeq-1≡2 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (B' ⇐ A') ⊛ V) = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl)
  rewrite subeq-2/\1 p₁ (sub q₁ (η (B' ⇐ A') ⊛ V) ⊛ W₂) (U₁ ⊛ η (A ⇒ B)) p₂ q |
          subeq-2>L1 (p₁ ++ (sub p₂ (η B) ▸ q)) W₂ (η (B' ⇐ A') ⊛ V) q₁ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 2>R1 (gt {W₁} q₁ refl refl refl)
  rewrite subeq-2/\1 p₁ (W₁ ⊛ sub q₁ (η (B' ⇐ A') ⊛ V)) (U₁ ⊛ η (A ⇒ B)) p₂ q |
          subeq-2>R1 (p₁ ++ (q ◂ sub p₂ (η B))) W₁ (η (B' ⇐ A') ⊛ V) q₁ = intrp≗ refl refl refl
  
mip≗ ._ ._ refl (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt ._ refl refl refl) | 1>L2 (gt ∙ refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A')) (U₁ ⊛ η (A ⇒ B)) p₂ (p₃ ++ (∙ ◂ V)) |
          subeq-1>L2 (p₁ ++ (sub p₂ (η B) ▸ p₃)) V (η (B' ⇐ A')) ∙ = intrp≗ refl (⇒L⇐L₂ {p = p₁}) refl

mip≗ ._ U refl (⇒L⇐L₂ {U = U₁} {._} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt ._ refl refl refl) | 1>R2 (gt q refl refl refl) 
  rewrite subeq-2/\1 p₁ U (U₁ ⊛ η (A ⇒ B)) p₂ (p₃ ++ (η (B' ⇐ A') ▸ q)) |
          subeq-1>R2 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (B' ⇐ A')) U q = intrp≗ refl (⇒L⇐L₂ {p = p₁}) refl

mip≗ ._ U refl (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ U (U₁ ⊛ η (A ⇒ B)) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (B' ⇐ A') ⊛ V))) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q₁)) U (η (B' ⇐ A') ⊛ V) q₂ q₃ = intrp≗ refl (⇒L⇐L₂ {p = p₁} {p₂} {q₁ ++ (_ ▸ q₃)}) refl

mip≗ ._ U refl (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ U (U₁ ⊛ η (A ⇒ B)) p₂ (q₁ ++ (sub q₂ (η (B' ⇐ A') ⊛ V) ▸ q₃)) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q₁)) U (η (B' ⇐ A') ⊛ V) q₂ q₃ = intrp≗ refl (⇒L⇐L₂ {p = p₁} {p₂} {q₁ ++ (q₂ ◂ _)}) refl 

mip≗ ._ U refl (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q U (U₁ ⊛ η (A ⇒ B)) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) |
          subeq-1/\2 q U (η (B' ⇐ A') ⊛ V) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = intrp≗ refl (⇒L⇐L₂ {p = q ++ (_ ▸ q₂)}) refl
          
mip≗ ._ U refl (⇒L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-2/\1 q U (U₁ ⊛ η (A ⇒ B)) (q₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) q₂ |
          subeq-2/\1 q U (η (B' ⇐ A') ⊛ V) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = intrp≗ refl (⇒L⇐L₂ {p = q ++ (q₁ ◂ _)}) refl

mip≗ p U eq₁ (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) with subeq _ _ p r (sym eq₁)
mip≗ p ._ refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1≡2 (same refl refl refl)
  rewrite subeq-2>L1 p (η (A ⇒ B)) (η (B' ⇐ A') ⊛ T) q |
          subeq-1≡2 p (sub q (η B') ⊛ η (A ⇒ B)) = intrp≗ refl refl ⇐L⇒L

mip≗ p ._ refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl) 
  rewrite subeq-2>L1 p W₂ (η (B' ⇐ A') ⊛ T) (q₁ ++ (q ◂ η (A ⇒ B))) |
          subeq-2>L1 p W₂ (sub q (η B') ⊛ η (A ⇒ B)) q₁ = intrp≗ refl refl ⇐L⇒L

mip≗ p ._ refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>R1 (gt {W₁} q₁ refl refl refl)
  rewrite subeq-2>R1 p W₁ (η (B' ⇐ A') ⊛ T) (q₁ ++ (q ◂ η (A ⇒ B))) |
          subeq-2>R1 p W₁ (sub q (η B') ⊛ η (A ⇒ B)) q₁ = intrp≗ refl refl ⇐L⇒L

mip≗ p U eq₁ (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>L2 (gt q₁ refl eqU refl) with subeq _ _ q₁ q (sym (⊛eq eqU .proj₁))
mip≗ ._._ refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>L2 (gt q₁ refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 q₁ (η (B' ⇐ A') ⊛ T) |
          subeq-1≡2 (r ++ (q₁ ◂ η (A ⇒ B))) (η (B' ⇐ A') ⊛ T) |
          subeq-1>L2 r (η (A ⇒ B)) (η B') q₁ = intrp≗ refl refl refl

mip≗ ._._ refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>L2 (gt q₁ refl refl refl) | 2>L1 (gt {W₂ = W₂} q₂ refl refl refl)
  rewrite subeq-2>L1 q₁ W₂ (η (B' ⇐ A') ⊛ T) q₂ |
          subeq-2>L1 (r ++ (q₁ ◂ η (A ⇒ B))) W₂ (η (B' ⇐ A') ⊛ T) q₂ |
          subeq-1>L2 r (η (A ⇒ B)) (sub q₂ (η B') ⊛ W₂) q₁ = intrp≗ refl refl refl

mip≗ ._._ refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>L2 (gt q₁ refl refl refl) | 2>R1 (gt {W₁} q₂ refl refl refl)
  rewrite subeq-2>R1 q₁ W₁ (η (B' ⇐ A') ⊛ T) q₂ |
          subeq-2>R1 (r ++ (q₁ ◂ η (A ⇒ B))) W₁ (η (B' ⇐ A') ⊛ T) q₂ |
          subeq-1>L2 r (η (A ⇒ B)) (W₁ ⊛ sub q₂ (η B')) q₁ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>L2 (gt q₁ refl refl refl) | 1>L2 (gt ∙ refl refl refl)
  rewrite subeq-1>L2 q T (η (B' ⇐ A')) ∙ |
          subeq-1>L2 (r ++ (q ◂ η (A ⇒ B))) T (η (B' ⇐ A')) ∙ |
          subeq-1>L2 r (η (A ⇒ B)) (η B') q = intrp≗ refl ⇐L⇒L refl

mip≗ ._ U refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>L2 (gt ._ refl refl refl) | 1>R2 (gt q₁ refl refl refl) 
  rewrite subeq-1>R2 q (η (B' ⇐ A')) U q₁ |
          subeq-1>R2 (r ++ (q ◂ η (A ⇒ B))) (η (B' ⇐ A')) U q₁ = intrp≗ refl ⇐L⇒L refl

mip≗ ._ U refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {r = r}) | 1>L2 (gt ._ refl refl refl) | 1/\2 (disj q q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 q U (η (B' ⇐ A') ⊛ T) q₂ q₃ |
          subeq-1/\2 (r ++ (q ◂ η (A ⇒ B))) U (η (B' ⇐ A') ⊛ T) q₂ q₃ |
          subeq-1>L2 r (η (A ⇒ B)) U (q ++ (q₂ ◂ sub q₃ (η B'))) = intrp≗ refl ⇐L⇒L refl

mip≗ ._ U refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {r = r}) | 1>L2 (gt ._ refl refl refl) | 2/\1 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q U (η (B' ⇐ A') ⊛ T) q₂ q₃ |
          subeq-2/\1 (r ++ (q ◂ η (A ⇒ B))) U (η (B' ⇐ A') ⊛ T) q₂ q₃ |
          subeq-1>L2 r (η (A ⇒ B)) U (q ++ (sub q₂ (η B') ▸ q₃)) = intrp≗ refl ⇐L⇒L refl

mip≗ ._ ._ refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = ∙} {r}) | 1>R2 (gt ∙ refl refl refl) 
  rewrite subeq-2/\1 r (η (A ⇒ B)) (η (B' ⇐ A') ⊛ T) ∙ ∙ |
          subeq-1>R2 r (η B') (η (A ⇒ B)) ∙ = intrp≗ refl ⇐L⇒L refl

mip≗ ._ ._ refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q ◂ U} {r}) | 1>R2 (gt ∙ refl refl refl) 
  rewrite subeq-2/\1 r (η (A ⇒ B)) (η (B' ⇐ A') ⊛ T) (q ◂ U) ∙ |
          subeq-1>R2 r (sub q (η B') ⊛ U) (η (A ⇒ B)) ∙ = intrp≗ refl ⇐L⇒L refl

mip≗ ._ ._ refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = T₁ ▸ q} {r}) | 1>R2 (gt ∙ refl refl refl)
  rewrite subeq-2/\1 r (η (A ⇒ B)) (η (B' ⇐ A') ⊛ T) (T₁ ▸ q) ∙ |
          subeq-1>R2 r (T₁ ⊛ sub q (η B')) (η (A ⇒ B)) ∙ = intrp≗ refl ⇐L⇒L refl

mip≗ ._ U refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 q₁ U (η (B' ⇐ A') ⊛ T) q₂ (q₃ ++ (q ◂ η (A ⇒ B))) |
          subeq-1/\2 q₁ U (sub q (η B') ⊛ η (A ⇒ B)) q₂ q₃ = intrp≗ refl ⇐L⇒L refl
          
mip≗ ._ U refl (⇐L⇒L {T} {A = A} {B} {A'} {B'} {q = q}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 q₁ U (η (B' ⇐ A') ⊛ T) (q₂ ++ (q ◂ η (A ⇒ B))) q₃ |
          subeq-2/\1 q₁ U (sub q (η B') ⊛ η (A ⇒ B)) q₂ q₃ = intrp≗ refl ⇐L⇒L refl

mip≗ p U eq₁ (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) with subeq _ _ p p₁ (sym eq₁)
mip≗ p ._ refl (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1≡2 (same refl refl refl) 
  rewrite subeq-2>L1 p (sub p₃ (V ⊛ η (A' ⇒ B'))) (η (B ⇐ A) ⊛ U₁) p₂ |
          subeq-2>R1 p (sub p₂ (η B)) (V ⊛ η (A' ⇒ B')) p₃ = intrp≗ refl refl (⇐L⇒L₂ {p = ∙} {p₂} {p₃})

mip≗ p ._ refl (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2>L1 (gt {W₂ = W₂} q refl refl refl) 
  rewrite subeq-2>L1 p W₂ (η (B ⇐ A) ⊛ U₁) (q ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) |
          subeq-2>L1 p W₂ (V ⊛ η (A' ⇒ B')) (q ++ (sub p₂ (η B) ▸ p₃)) =  intrp≗ refl refl (⇐L⇒L₂ {p = q ◂ _} {p₂} {p₃})

mip≗ p ._ refl (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2>R1 (gt {W₁} q refl refl refl) 
  rewrite subeq-2>R1 p W₁ (η (B ⇐ A) ⊛ U₁) (q ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) |
          subeq-2>R1 p W₁ (V ⊛ η (A' ⇒ B')) (q ++ (sub p₂ (η B) ▸ p₃)) = intrp≗ refl refl (⇐L⇒L₂ {p = _ ▸ q} {p₂} {p₃})

mip≗ p U eq₁ (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt q refl eqU refl) with subeq _ _ q p₂ (sym (⊛eq eqU .proj₁))
mip≗ ._ ._ refl (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (η (B ⇐ A) ⊛ U₁) |
          subeq-1/\2 p₁ (η B') (η (B ⇐ A) ⊛ U₁) q p₃ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl) 
  rewrite subeq-2>L1 (p₁ ++ (q ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) W₂ (η (B ⇐ A) ⊛ U₁) q₁ |
          subeq-1/\2 p₁ (sub q₁ (η B) ⊛ W₂) (V ⊛ η (A' ⇒ B')) q p₃ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 2>R1 (gt {W₁} q₁ refl refl refl) 
  rewrite subeq-2>R1 (p₁ ++ (q ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) W₁ (η (B ⇐ A) ⊛ U₁) q₁ |
          subeq-1/\2 p₁ (W₁ ⊛ sub q₁ (η B)) (V ⊛ η (A' ⇒ B')) q p₃ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1>L2 (gt ∙ refl refl refl)
  rewrite subeq-1>L2 (p₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) U₁ (η (B ⇐ A)) ∙ |
          subeq-1/\2 p₁ (η B) (V ⊛ η (A' ⇒ B')) p₂ p₃ = intrp≗ refl (⇐L⇒L₂ {p = p₁}) refl

mip≗ ._ U refl (⇐L⇒L₂ {U = ._} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1>R2 (gt q refl refl refl)
  rewrite subeq-1>R2 (p₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) (η (B ⇐ A)) U q  = intrp≗ refl (⇐L⇒L₂ {p = p₁}) refl

mip≗ ._ U refl (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) U (η (B ⇐ A) ⊛ U₁) q₂ q₃ |
          subeq-1/\2 p₁ U (V ⊛ η (A' ⇒ B')) (q₁ ++ (q₂ ◂ sub q₃ (η B))) p₃ = intrp≗ refl (⇐L⇒L₂ {p = p₁} {q₁ ++ (_ ▸ q₃)} {p₃}) refl

mip≗ ._ U refl (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) U (η (B ⇐ A) ⊛ U₁) q₂ q₃ | 
          subeq-1/\2 p₁ U (V ⊛ η (A' ⇒ B')) (q₁ ++ (sub q₂ (η B) ▸ q₃)) p₃ = intrp≗ refl (⇐L⇒L₂ {p = p₁} {q₁ ++ (q₂ ◂ _)} {p₃}) refl

mip≗ p U eq₁ (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt q refl eqU refl) with subeq _ _ q p₃ (sym (⊛eq eqU .proj₂))
mip≗ ._ ._ refl (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 1≡2 (same refl refl refl) 
  rewrite subeq-2/\1 p₁ (V ⊛ η (A' ⇒ B')) (η (B ⇐ A) ⊛ U₁) p₂ q |
         subeq-1≡2 (p₁ ++ (sub p₂ (η B) ▸ q)) (V ⊛ η (A' ⇒ B')) = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl)
  rewrite subeq-2/\1 p₁ (sub q₁ (V ⊛ η (A' ⇒ B')) ⊛ W₂) (η (B ⇐ A) ⊛ U₁) p₂ q |
          subeq-2>L1 (p₁ ++ (sub p₂ (η B) ▸ q)) W₂ (V ⊛ η (A' ⇒ B')) q₁ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 2>R1 (gt {W₁} q₁ refl refl refl) 
  rewrite subeq-2/\1 p₁ (W₁ ⊛ sub q₁ (V ⊛ η (A' ⇒ B'))) (η (B ⇐ A) ⊛ U₁) p₂ q |
          subeq-2>R1 (p₁ ++ (q ◂ sub p₂ (η B))) W₁ (V ⊛ η (A' ⇒ B')) q₁ = intrp≗ refl refl refl
  
mip≗ ._ U refl (⇐L⇒L₂ {U = U₁} {._} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt ._ refl refl refl) | 1>L2 (gt q refl refl refl)
  rewrite subeq-2/\1 p₁ U (η (B ⇐ A) ⊛ U₁) p₂ (p₃ ++ (q ◂ η (A' ⇒ B'))) |
          subeq-1>L2 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (A' ⇒ B')) U q = intrp≗ refl (⇐L⇒L₂ {p = p₁}) refl

mip≗ ._ ._ refl (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt ._ refl refl refl) | 1>R2 (gt ∙ refl refl refl)
  rewrite subeq-2/\1 p₁ (η (A' ⇒ B')) (η (B ⇐ A) ⊛ U₁) p₂ (p₃ ++ (V ▸ ∙)) |
          subeq-1>R2 (p₁ ++ (sub p₂ (η B) ▸ p₃)) V (η (A' ⇒ B')) ∙ = intrp≗ refl (⇐L⇒L₂ {p = p₁}) refl

mip≗ ._ U refl (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 p₁ U (η (B ⇐ A) ⊛ U₁) p₂ (q₁ ++ (q₂ ◂ sub q₃ (V ⊛ η (A' ⇒ B')))) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q₁)) U (V ⊛ η (A' ⇒ B')) q₂ q₃ = intrp≗ refl (⇐L⇒L₂ {p = p₁} {p₂} {q₁ ++ (_ ▸ q₃)}) refl

mip≗ ._ U refl (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ U (η (B ⇐ A) ⊛ U₁) p₂ (q₁ ++ (sub q₂ (V ⊛ η (A' ⇒ B')) ▸ q₃)) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q₁)) U (V ⊛ η (A' ⇒ B')) q₂ q₃ = intrp≗ refl (⇐L⇒L₂ {p = p₁} {p₂} {q₁ ++ (q₂ ◂ _)}) refl 

mip≗ ._ U refl (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q U (η (B ⇐ A) ⊛ U₁) q₁ (q₂ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) |
          subeq-1/\2 q U (V ⊛ η (A' ⇒ B')) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = intrp≗ refl (⇐L⇒L₂ {p = q ++ (_ ▸ q₂)}) refl
          
mip≗ ._ U refl (⇐L⇒L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl) 
  rewrite subeq-2/\1 q U (η (B ⇐ A) ⊛ U₁) (q₁ ++ (p₂ ◂ sub p₃ (V ⊛ η (A' ⇒ B')))) q₂ |
          subeq-2/\1 q U (V ⊛ η (A' ⇒ B')) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = intrp≗ refl (⇐L⇒L₂ {p = q ++ (q₁ ◂ _)}) refl

mip≗ p U eq₁ (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) with subeq _ _ p r (sym eq₁)
mip≗ p ._ refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1≡2 (same refl refl refl)
  rewrite subeq-2>R1 p (η (B ⇐ A)) (η (B' ⇐ A') ⊛ T) q |
          subeq-1≡2 p (η (B ⇐ A) ⊛ sub q (η B')) = intrp≗ refl refl ⇐L⇐L

mip≗ p ._ refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl)
  rewrite subeq-2>L1 p W₂ (η (B' ⇐ A') ⊛ T) (q₁ ++ (η (B ⇐ A) ▸ q)) |
          subeq-2>L1 p W₂ (η (B ⇐ A) ⊛ sub q (η B')) q₁ = intrp≗ refl refl ⇐L⇐L

mip≗ p ._ refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 2>R1 (gt {W₁} q₁ refl refl refl) 
  rewrite subeq-2>R1 p W₁ (η (B' ⇐ A') ⊛ T) (q₁ ++ (η (B ⇐ A) ▸ q)) |
          subeq-2>R1 p W₁ (η (B ⇐ A) ⊛ sub q (η B')) q₁ = intrp≗ refl refl ⇐L⇐L

mip≗ ._ ._  refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = ∙} {r}) | 1>L2 (gt ∙ refl refl refl)
  rewrite subeq-1/\2 r (η (B ⇐ A)) (η (B' ⇐ A') ⊛ T) ∙ ∙ |
          subeq-1>L2 r (η B') (η (B ⇐ A)) ∙ = intrp≗ refl ⇐L⇐L refl

mip≗ ._ ._  refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q ◂ U} {r}) | 1>L2 (gt ∙ refl refl refl)
  rewrite subeq-1/\2 r (η (B ⇐ A)) (η (B' ⇐ A') ⊛ T) ∙ (q ◂ U) |
          subeq-1>L2 r (sub q (η B') ⊛ U) (η (B ⇐ A)) ∙ = intrp≗ refl ⇐L⇐L refl
          
mip≗ ._ ._  refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = T₁ ▸ q} {r}) | 1>L2 (gt ∙ refl refl refl)
  rewrite subeq-1/\2 r (η (B ⇐ A)) (η (B' ⇐ A') ⊛ T) ∙ (T₁ ▸ q) |
          subeq-1>L2 r (T₁ ⊛ sub q (η B')) (η (B ⇐ A)) ∙ = intrp≗ refl ⇐L⇐L refl

mip≗ p U eq₁ (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>R2 (gt q₁ refl eqU refl) with subeq _ _ q₁ q (sym (⊛eq eqU .proj₂))
mip≗ ._._ refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>R2 (gt q₁ refl refl refl) | 1≡2 (same refl refl refl)
  rewrite subeq-1≡2 q₁ (η (B' ⇐ A') ⊛ T) |
          subeq-1≡2 (r ++ (η (B ⇐ A) ▸ q₁)) (η (B' ⇐ A') ⊛ T) |
          subeq-1>R2 r (η (B ⇐ A)) (η B') q₁ = intrp≗ refl refl refl

mip≗ ._._ refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>R2 (gt q₁ refl refl refl) | 2>L1 (gt {W₂ = W₂} q₂ refl refl refl)
  rewrite subeq-2>L1 q₁ W₂ (η (B' ⇐ A') ⊛ T) q₂ |
          subeq-2>L1 (r ++ (η (B ⇐ A) ▸ q₁)) W₂ (η (B' ⇐ A') ⊛ T) q₂ |
          subeq-1>R2 r (η (B ⇐ A)) (sub q₂ (η B') ⊛ W₂) q₁ = intrp≗ refl refl refl

mip≗ ._._ refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>R2 (gt q₁ refl refl refl) | 2>R1 (gt {W₁} q₂ refl refl refl)
  rewrite subeq-2>R1 q₁ W₁ (η (B' ⇐ A') ⊛ T) q₂ |
          subeq-2>R1 (r ++ (η (B ⇐ A) ▸ q₁)) W₁ (η (B' ⇐ A') ⊛ T) q₂ |
          subeq-1>R2 r (η (B ⇐ A)) (W₁ ⊛ sub q₂ (η B')) q₁ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>R2 (gt q₁ refl refl refl) | 1>L2 (gt ∙ refl refl refl) 
  rewrite subeq-1>L2 q T (η (B' ⇐ A')) ∙ |
          subeq-1>L2 (r ++ (η (B ⇐ A) ▸ q)) T (η (B' ⇐ A')) ∙ |
          subeq-1>R2 r (η (B ⇐ A)) (η B') q = intrp≗ refl ⇐L⇐L refl

mip≗ ._ U refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q} {r}) | 1>R2 (gt ._ refl refl refl) | 1>R2 (gt q₁ refl refl refl) 
  rewrite subeq-1>R2 q (η (B' ⇐ A')) U q₁ |
          subeq-1>R2 (r ++ (η (B ⇐ A) ▸ q)) (η (B' ⇐ A')) U q₁ = intrp≗ refl ⇐L⇐L refl

mip≗ ._ U refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 1>R2 (gt ._ refl refl refl) | 1/\2 (disj q q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 q U (η (B' ⇐ A') ⊛ T) q₂ q₃ |
          subeq-1/\2 (r ++ (η (B ⇐ A) ▸ q)) U (η (B' ⇐ A') ⊛ T) q₂ q₃ |
          subeq-1>R2 r (η (B ⇐ A)) U (q ++ (q₂ ◂ sub q₃ (η B'))) = intrp≗ refl ⇐L⇐L refl

mip≗ ._ U refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {r = r}) | 1>R2 (gt ._ refl refl refl) | 2/\1 (disj q q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 q U (η (B' ⇐ A') ⊛ T) q₂ q₃ |
          subeq-2/\1 (r ++ (η (B ⇐ A) ▸ q)) U (η (B' ⇐ A') ⊛ T) q₂ q₃ |
          subeq-1>R2 r (η (B ⇐ A)) U (q ++ (sub q₂ (η B') ▸ q₃)) = intrp≗ refl ⇐L⇐L refl

mip≗ ._ U refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q}) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 q₁ U (η (B' ⇐ A') ⊛ T) q₂ (q₃ ++ (η (B ⇐ A) ▸ q)) |
          subeq-1/\2 q₁ U (η (B ⇐ A) ⊛ sub q (η B')) q₂ q₃ = intrp≗ refl ⇐L⇐L refl
          
mip≗ ._ U refl (⇐L⇐L {T} {A = A} {B} {A'} {B'} {q = q}) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 q₁ U (η (B' ⇐ A') ⊛ T) (q₂ ++ (η (B ⇐ A) ▸ q)) q₃ |
          subeq-2/\1 q₁ U (η (B ⇐ A) ⊛ sub q (η B')) q₂ q₃ = intrp≗ refl ⇐L⇐L refl

mip≗ p U eq₁ (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) with subeq _ _ p p₁ (sym eq₁)
mip≗ p ._ refl (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1≡2 (same refl refl refl) 
  rewrite subeq-2>L1 p (sub p₃ (η (B' ⇐ A') ⊛ V)) (η (B ⇐ A) ⊛ U₁) p₂ |
          subeq-2>R1 p (sub p₂ (η B)) (η (B' ⇐ A') ⊛ V) p₃ = intrp≗ refl refl (⇐L⇐L₂ {p = ∙} {p₂} {p₃})

mip≗ p ._ refl (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2>L1 (gt {W₂ = W₂} q refl refl refl)
  rewrite subeq-2>L1 p W₂ (η (B ⇐ A) ⊛ U₁) (q ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) |
          subeq-2>L1 p W₂ (η (B' ⇐ A') ⊛ V) (q ++ (sub p₂ (η B) ▸ p₃)) =  intrp≗ refl refl (⇐L⇐L₂ {p = q ◂ _} {p₂} {p₃})

mip≗ p ._ refl (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2>R1 (gt {W₁} q refl refl refl)
  rewrite subeq-2>R1 p W₁ (η (B ⇐ A) ⊛ U₁) (q ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) |
          subeq-2>R1 p W₁ (η (B' ⇐ A') ⊛ V) (q ++ (sub p₂ (η B) ▸ p₃)) = intrp≗ refl refl (⇐L⇐L₂ {p = _ ▸ q} {p₂} {p₃})

mip≗ p U eq₁ (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt q refl eqU refl) with subeq _ _ q p₂ (sym (⊛eq eqU .proj₁))
mip≗ ._ ._ refl (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 1≡2 (same refl refl refl)
  rewrite subeq-1≡2 (p₁ ++ (q ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (η (B ⇐ A) ⊛ U₁) |
          subeq-1/\2 p₁ (η B') (η (B ⇐ A) ⊛ U₁) q p₃ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl)
  rewrite subeq-2>L1 (p₁ ++ (q ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) W₂ (η (B ⇐ A) ⊛ U₁) q₁ |
          subeq-1/\2 p₁ (sub q₁ (η B) ⊛ W₂) (η (B' ⇐ A') ⊛ V) q p₃ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt q refl refl refl) | 2>R1 (gt {W₁} q₁ refl refl refl)
  rewrite subeq-2>R1 (p₁ ++ (q ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) W₁ (η (B ⇐ A) ⊛ U₁) q₁ |
          subeq-1/\2 p₁ (W₁ ⊛ sub q₁ (η B)) (η (B' ⇐ A') ⊛ V) q p₃ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1>L2 (gt ∙ refl refl refl)
  rewrite subeq-1>L2 (p₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) U₁ (η (B ⇐ A)) ∙ |
          subeq-1/\2 p₁ (η B) (η (B' ⇐ A') ⊛ V) p₂ p₃ = intrp≗ refl (⇐L⇐L₂ {p = p₁}) refl

mip≗ ._ U refl (⇐L⇐L₂ {U = ._} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1>R2 (gt q refl refl refl)
  rewrite subeq-1>R2 (p₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) (η (B ⇐ A)) U q  = intrp≗ refl (⇐L⇐L₂ {p = p₁}) refl

mip≗ ._ U refl (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-1/\2 (p₁ ++ (q₁ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) U (η (B ⇐ A) ⊛ U₁) q₂ q₃ |
          subeq-1/\2 p₁ U (η (B' ⇐ A') ⊛ V) (q₁ ++ (q₂ ◂ sub q₃ (η B))) p₃ = intrp≗ refl (⇐L⇐L₂ {p = p₁} {q₁ ++ (_ ▸ q₃)} {p₃}) refl

mip≗ ._ U refl (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {._} {p₃}) | 1>L2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl) 
  rewrite subeq-2/\1 (p₁ ++ (q₁ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) U (η (B ⇐ A) ⊛ U₁) q₂ q₃ | 
          subeq-1/\2 p₁ U (η (B' ⇐ A') ⊛ V) (q₁ ++ (sub q₂ (η B) ▸ q₃)) p₃ = intrp≗ refl (⇐L⇐L₂ {p = p₁} {q₁ ++ (q₂ ◂ _)} {p₃}) refl

mip≗ p U eq₁ (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt q refl eqU refl) with subeq _ _ q p₃ (sym (⊛eq eqU .proj₂))
mip≗ ._ ._ refl (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 1≡2 (same refl refl refl)
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A') ⊛ V) (η (B ⇐ A) ⊛ U₁) p₂ q |
         subeq-1≡2 (p₁ ++ (sub p₂ (η B) ▸ q)) (η (B' ⇐ A') ⊛ V) = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 2>L1 (gt {W₂ = W₂} q₁ refl refl refl)
  rewrite subeq-2/\1 p₁ (sub q₁ (η (B' ⇐ A') ⊛ V) ⊛ W₂) (η (B ⇐ A) ⊛ U₁) p₂ q |
          subeq-2>L1 (p₁ ++ (sub p₂ (η B) ▸ q)) W₂ (η (B' ⇐ A') ⊛ V) q₁ = intrp≗ refl refl refl

mip≗ ._ ._ refl (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt q refl refl refl) | 2>R1 (gt {W₁} q₁ refl refl refl)
  rewrite subeq-2/\1 p₁ (W₁ ⊛ sub q₁ (η (B' ⇐ A') ⊛ V)) (η (B ⇐ A) ⊛ U₁) p₂ q |
          subeq-2>R1 (p₁ ++ (q ◂ sub p₂ (η B))) W₁ (η (B' ⇐ A') ⊛ V) q₁ = intrp≗ refl refl refl
  
mip≗ ._ ._ refl (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt ._ refl refl refl) | 1>L2 (gt ∙ refl refl refl) 
  rewrite subeq-2/\1 p₁ (η (B' ⇐ A')) (η (B ⇐ A) ⊛ U₁) p₂ (p₃ ++ (∙ ◂ V)) |
          subeq-1>L2 (p₁ ++ (sub p₂ (η B) ▸ p₃)) V (η (B' ⇐ A')) ∙ = intrp≗ refl (⇐L⇐L₂ {p = p₁}) refl

mip≗ ._ U refl (⇐L⇐L₂ {U = U₁} {._} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {p₃}) | 1>R2 (gt ._ refl refl refl) | 1>R2 (gt q refl refl refl) 
  rewrite subeq-2/\1 p₁ U (η (B ⇐ A) ⊛ U₁) p₂ (p₃ ++ (η (B' ⇐ A') ▸ q)) |
          subeq-1>R2 (p₁ ++ (sub p₂ (η B) ▸ p₃)) (η (B' ⇐ A')) U q = intrp≗ refl (⇐L⇐L₂ {p = p₁}) refl

mip≗ ._ U refl (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt ._ refl refl refl) | 1/\2 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ U (η (B ⇐ A) ⊛ U₁) p₂ (q₁ ++ (q₂ ◂ sub q₃ (η (B' ⇐ A') ⊛ V))) |
          subeq-1/\2 (p₁ ++ (sub p₂ (η B) ▸ q₁)) U (η (B' ⇐ A') ⊛ V) q₂ q₃ = intrp≗ refl (⇐L⇐L₂ {p = p₁} {p₂} {q₁ ++ (_ ▸ q₃)}) refl

mip≗ ._ U refl (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = p₁} {p₂} {._}) | 1>R2 (gt ._ refl refl refl) | 2/\1 (disj q₁ q₂ q₃ refl refl refl refl)
  rewrite subeq-2/\1 p₁ U (η (B ⇐ A) ⊛ U₁) p₂ (q₁ ++ (sub q₂ (η (B' ⇐ A') ⊛ V) ▸ q₃)) |
          subeq-2/\1 (p₁ ++ (sub p₂ (η B) ▸ q₁)) U (η (B' ⇐ A') ⊛ V) q₂ q₃ = intrp≗ refl (⇐L⇐L₂ {p = p₁} {p₂} {q₁ ++ (q₂ ◂ _)}) refl 

mip≗ ._ U refl (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 1/\2 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-1/\2 q U (η (B ⇐ A) ⊛ U₁) q₁ (q₂ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) |
          subeq-1/\2 q U (η (B' ⇐ A') ⊛ V) q₁ (q₂ ++ (sub p₂ (η B) ▸ p₃)) = intrp≗ refl (⇐L⇐L₂ {p = q ++ (_ ▸ q₂)}) refl
          
mip≗ ._ U refl (⇐L⇐L₂ {U = U₁} {V} {A = A} {B} {A'} {B'} {p = ._} {p₂} {p₃}) | 2/\1 (disj q q₁ q₂ refl refl refl refl)
  rewrite subeq-2/\1 q U (η (B ⇐ A) ⊛ U₁) (q₁ ++ (p₂ ◂ sub p₃ (η (B' ⇐ A') ⊛ V))) q₂ |
          subeq-2/\1 q U (η (B' ⇐ A') ⊛ V) (q₁ ++ (sub p₂ (η B) ▸ p₃)) q₂ = intrp≗ refl (⇐L⇐L₂ {p = q ++ (q₁ ◂ _)}) refl
      
mip≗ p U refl refl = intrp≗ refl refl refl
mip≗ p U refl (~_ {f = f} {f'} eq₂) with mip p U f refl | mip p U f' refl |  mip≗ p U refl eq₂
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = intrp≗ refl (~ eqg) (~ eqh) 
      
 
       