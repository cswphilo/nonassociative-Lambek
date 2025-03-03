{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefined where

open import Relation.Binary.PropositionalEquality hiding ([_]; _≗_) 
open import Data.Product 
open import Fma
open import SeqCalc
open import Interpolation

sub≡ : ∀ {T U V} (p : Path T) → sub p U ≡ sub p V → U ≡ V
sub≡ ∙ refl = refl
sub≡ (p ◂ U) eq = sub≡ p (⊛eq eq .proj₁)
sub≡ (T ▸ p) eq = sub≡ p (⊛eq eq .proj₂)

subeq∙₁ : ∀ {T} (p : Path T) (U : Tree)
  → subeq (sub p U) U ∙ p refl ≡ {!   !}
subeq∙₁ p U = {!   !}
subeq-1≡2 : ∀ {T} (p : Path T) (U : Tree)
  → subeq U U p p refl ≡ 1≡2 (same refl refl refl)
subeq-1≡2 ∙ U = refl
subeq-1≡2 (p ◂ V) U rewrite subeq-1≡2 p U = refl
subeq-1≡2 (T ▸ p) U rewrite subeq-1≡2 p U = refl

subeq-1/\2 : ∀ {T} (p : Path T) (U V : Tree) 
  → {W₁ W₂ : Tree} (p₁ : Path W₁) (p₂ : Path W₂) 
  → subeq U V (p ++ (p₁ ◂ sub p₂ V)) (p ++ (sub p₁ U ▸ p₂)) refl ≡ 1/\2 (disj p p₁ p₂ refl refl refl refl)
subeq-1/\2 ∙ U V p₁ p₂ = refl
subeq-1/\2 (p ◂ U₁) U V p₁ p₂ rewrite subeq-1/\2 p U V p₁ p₂ = refl
subeq-1/\2 (T ▸ p) U V p₁ p₂ rewrite subeq-1/\2 p U V p₁ p₂ = refl

subeq-2/\1 : ∀ {T} (p : Path T) (U V : Tree) 
  → {W₁ W₂ : Tree} (p₁ : Path W₁) (p₂ : Path W₂) 
  → subeq U V (p ++ (sub p₁ V ▸ p₂)) (p ++ (p₁ ◂ sub p₂ U)) refl ≡ 2/\1 (disj p p₁ p₂ refl refl refl refl)
subeq-2/\1 ∙ U V p₁ p₂ = refl
subeq-2/\1 (p ◂ U₁) U V p₁ p₂ rewrite subeq-2/\1 p U V p₁ p₂ = refl
subeq-2/\1 (T ▸ p) U V p₁ p₂ rewrite subeq-2/\1 p U V p₁ p₂ = refl

subeq-2>R1 : ∀ {T} (p : Path T) (W₁ : Tree) {W₂ : Tree} (U : Tree)
  → (q : Path W₂)
  → subeq (W₁ ⊛ sub q U) U p (p ++ (W₁ ▸ q)) refl ≡ 2>R1 (gt q refl refl refl)
subeq-2>R1 ∙ W₁ U q = refl
subeq-2>R1 (p ◂ U₁) W₁ U q rewrite subeq-2>R1 p W₁ U q = refl
subeq-2>R1 (T ▸ p) W₁ U q rewrite subeq-2>R1 p W₁ U q = refl

subeq-2>L1 : ∀ {T} (p : Path T) {W₁ : Tree} (W₂ : Tree) (U : Tree)
  → (q : Path W₁)
  → subeq (sub q U ⊛ W₂) U p (p ++ (q ◂ W₂)) refl ≡ 2>L1 (gt q refl refl refl)
subeq-2>L1 ∙ W₁ U q = refl
subeq-2>L1 (p ◂ U₁) W₁ U q rewrite subeq-2>L1 p W₁ U q = refl
subeq-2>L1 (T ▸ p) W₁ U q rewrite subeq-2>L1 p W₁ U q = refl

subeq-1>R2 : ∀ {T} (p : Path T) (W₁ : Tree) {W₂ : Tree} (U : Tree)
  → (q : Path W₂)
  → subeq U (W₁ ⊛ sub q U) (p ++ (W₁ ▸ q)) p refl ≡ 1>R2 (gt q refl refl refl)
subeq-1>R2 ∙ W₁ U q = refl
subeq-1>R2 (p ◂ U₁) W₁ U q rewrite subeq-1>R2 p W₁ U q = refl
subeq-1>R2 (T ▸ p) W₁ U q rewrite subeq-1>R2 p W₁ U q = refl

subeq-1>L2 : ∀ {T} (p : Path T) {W₁ : Tree} (W₂ : Tree) (U : Tree)
  → (q : Path W₁)
  → subeq U (sub q U ⊛ W₂) (p ++ (q ◂ W₂)) p refl ≡ 1>L2 (gt q refl refl refl)
subeq-1>L2 ∙ W₁ U q = refl
subeq-1>L2 (p ◂ U₁) W₁ U q rewrite subeq-1>L2 p W₁ U q = refl
subeq-1>L2 (T ▸ p) W₁ U q rewrite subeq-1>L2 p W₁ U q = refl

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
mip≗ p U eq₁ (⇒L {U = U₁} {A} {B} {p = p₁}  eq₂ eq₃) | 2/\1 x = {!   !}
mip≗ p U eq₁ (⇐L eq₂ eq₃) = {!   !}
mip≗ p U eq₁ (⊗R eq₂ eq₃) = {!   !}
mip≗ p U eq₁ (⊗L eq) = {!   !}
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
mip≗ p U eq₁ ⇒L⊗R₁ = {!   !}
mip≗ p U eq₁ ⇒L⊗R₂ = {!   !}
mip≗ p U eq₁ ⇐L⊗R₁ = {!   !}
mip≗ p U eq₁ ⇐L⊗R₂ = {!   !}
mip≗ p U eq₁ ⊗L⊗R₁ = {!   !}
mip≗ p U eq₁ ⊗L⊗R₂ = {!   !}
mip≗ p U eq₁ ⊗L⊗L = {!   !}
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
mip≗ p U eq₁ ⊗L⇒L₂1/\2 = {!   !}
mip≗ p U eq₁ ⊗L⇒L₂2/\1 = {!   !}
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
          
mip≗ p U eq₁ ⊗L⇐L₂1/\2 = {!   !}
mip≗ p U eq₁ ⊗L⇐L₂2/\1 = {!   !}
mip≗ p U eq₁ ⇒L⇒L = {!   !}
mip≗ p U eq₁ ⇒L⇒L₂1/\2 = {!   !}
mip≗ p U eq₁ ⇒L⇒L₂2/\1 = {!   !}
mip≗ p U eq₁ ⇒L⇐L = {!   !}
mip≗ p U eq₁ ⇒L⇐L₂1/\2 = {!   !}
mip≗ p U eq₁ ⇒L⇐L₂2/\1 = {!   !}
mip≗ p U eq₁ ⇐L⇒L = {!   !}
mip≗ p U eq₁ ⇐L⇒L₂1/\2 = {!   !}
mip≗ p U eq₁ ⇐L⇒L₂2/\1 = {!   !}
mip≗ p U eq₁ ⇐L⇐L = {!   !}
mip≗ p U eq₁ ⇐L⇐L₂1/\2 = {!   !}
mip≗ p U eq₁ ⇐L⇐L₂2/\1 = {!   !}
mip≗ p U refl refl = intrp≗ refl refl refl
mip≗ p U refl (~_ {f = f} {f'} eq₂) with mip p U f refl | mip p U f' refl |  mip≗ p U refl eq₂
... | intrp D g h | intrp .D g' h' | intrp≗ refl eqg eqh = intrp≗ refl (~ eqg) (~ eqh) 
  
 
  