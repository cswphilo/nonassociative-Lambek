{-# OPTIONS --rewriting #-}

module Fma where

open import Utilities public

-- ============================================================
-- Formulae and Trees of Non-Associative Lambek Calculus NL
-- ============================================================

postulate At : Set

infix 22 _⇒_ _⇐_ _⊛_ _⊗_

-- Formulae

data Fma : Set where
  at : At → Fma
  _⇒_ _⇐_ : Fma → Fma → Fma
  _⊗_ : Fma → Fma → Fma

-- We use the same type Tree to represent both antecedents and
-- contexts (i.e. trees with holes).

data Tree : Set where
  ∙ : Tree
  η : Fma → Tree
  _⊛_ : Tree → Tree → Tree

⊛eq : ∀ {T₁ T₂ U₁ U₂}
  → T₁ ⊛ U₁ ≡ T₂ ⊛ U₂
  → T₁ ≡ T₂ × U₁ ≡ U₂
⊛eq refl = refl , refl

-- The type of paths in a tree.
-- A path start from the root and end in a hole.

data Path : Tree → Set where
  ∙ : Path ∙
  _◂_ : ∀ {T} (p : Path T) U → Path (T ⊛ U)
  _▸_ : ∀ T {U} (p : Path U) → Path (T ⊛ U)

-- Substitution of a tree in a hole specified by a path.

sub : ∀ {T} → Path T → Tree → Tree
sub ∙ U = U
sub (p ◂ V) U = sub p U ⊛ V
sub (V ▸ p) U = V ⊛ sub p U

-- Concatenation of paths.

_++_ : ∀ {T U} (p : Path T) (q : Path U) → Path (sub p U)
∙ ++ q = q
(p ◂ V) ++ q = (p ++ q) ◂ V
(V ▸ p) ++ q = V ▸ (p ++ q)


-- A substitution in a hole determined by a concatenation of paths can
-- be split in two separate substitutions.

sub++ : ∀ {T U V} (p : Path T) {q : Path U}
  → sub (p ++ q) V ≡ sub p (sub q V)
sub++ ∙ = refl
sub++ (p ◂ U) = cong (_⊛ U) (sub++ p)
sub++ (U ▸ p) = cong (U ⊛_) (sub++ p)

{-# REWRITE sub++ #-}

++assoc : ∀ {T U V} (p : Path T) (q : Path U) (r : Path V)
  → (p ++ q) ++ r ≡ p ++ (q ++ r)
++assoc ∙ q r = refl
++assoc (p ◂ U) q r = cong (_◂ U) (++assoc p q r)
++assoc (U ▸ p) q r = cong (U ▸_) (++assoc p q r)

{-# REWRITE ++assoc #-}

-- When given a proof of an equality sub p₁ U₁ ≡ sub p₂ U₂, we need to
-- check the relative positions of U₁ and U₂: either U₁ is contained
-- in U₂, or U₂ is contained in U₁, or U₁ and U₂ belong to different
-- subtrees (which are two more cases).
-- This is what the function subeq does.

module _ {T₁ T₂ : Tree} (p₁ : Path T₁) (p₂ : Path T₂) where

  record Same (U₁ U₂ : Tree) : Set where   -- read: U₁ ≡ U₂
    constructor same
    field
      eqT : T₁ ≡ T₂
      eqU : U₁ ≡ U₂
      eqp : subst Path eqT p₁ ≡ p₂

  record Contains (U₁ U₂ : Tree) : Set where   -- read: U₁ contains U₂
    constructor gt
    field
      {W} : Tree
      q : Path W
      eqT : T₂ ≡ sub p₁ W
      eqU : U₁ ≡ sub q U₂
      eqp : subst Path eqT p₂ ≡ p₁ ++ q

  record ContainsLeft (U₁ U₂ : Tree) : Set where   -- read: U₁ contains U₂
    constructor gt
    field
      {W₁ W₂} : Tree
      q : Path W₁
      eqT : T₂ ≡ sub p₁ (W₁ ⊛ W₂)
      eqU : U₁ ≡ sub (q ◂ W₂) U₂
      eqp : subst Path eqT p₂ ≡ p₁ ++ (q ◂ _)

  record ContainsRight (U₁ U₂ : Tree) : Set where   -- read: U₁ contains U₂
    constructor gt
    field
      {W₁ W₂} : Tree
      q : Path W₂
      eqT : T₂ ≡ sub p₁ (W₁ ⊛ W₂)
      eqU : U₁ ≡ sub (W₁ ▸ q) U₂
      eqp : subst Path eqT p₂ ≡ p₁ ++ (_ ▸ q)

  record LeftRight (U₁ U₂ : Tree) : Set where   -- read: U₁ on the ◁ of U₂
    constructor disj
    field
      {W W₁ W₂} : Tree
      q : Path W
      q₁ : Path W₁
      q₂ : Path W₂
      eqT₁ : sub q (W₁ ⊛ sub q₂ U₂) ≡ T₁
      eqT₂ : T₂ ≡ sub q (sub q₁ U₁ ⊛ W₂)
      eqp₁ : subst Path eqT₁ (q ++ (q₁ ◂ _)) ≡ p₁
      eqp₂ : subst Path eqT₂ p₂ ≡ q ++ (_ ▸ q₂)

module _ {T₁ T₂ : Tree} (p₁ : Path T₁) (p₂ : Path T₂) where

  data SubEqCases (U₁ U₂ : Tree) : Set where
    1≡2 : Same p₁ p₂ U₁ U₂ → SubEqCases U₁ U₂
    2>L1 : ContainsLeft p₁ p₂ U₁ U₂ → SubEqCases U₁ U₂ -- U₂ inside U₁
    2>R1 : ContainsRight p₁ p₂ U₁ U₂ → SubEqCases U₁ U₂ -- U₂ inside U₁
    1>L2 : ContainsLeft p₂ p₁ U₂ U₁ → SubEqCases U₁ U₂ -- U₁ inside U₂
    1>R2 : ContainsRight p₂ p₁ U₂ U₁ → SubEqCases U₁ U₂ -- U₁ inside U₂
    1/\2 : LeftRight p₁ p₂ U₁ U₂ → SubEqCases U₁ U₂  -- U₁ disjoint from U₂, U₁ on the ◁, U₂ on the ▸
    2/\1 : LeftRight p₂ p₁ U₂ U₁ → SubEqCases U₁ U₂  -- U₁ disjoint from U₂, U₁ on the ◁, U₂ on the ▸


subeq : ∀ {T₁ T₂} U₁ U₂ (p₁ : Path T₁) (p₂ : Path T₂)
  → sub p₁ U₁ ≡ sub p₂ U₂
  → SubEqCases p₁ p₂ U₁ U₂
subeq _ U₂ ∙ ∙ refl = 1≡2 (same refl refl refl)
subeq _ U₂ ∙ (p₂ ◂ _) refl = 2>L1 (gt p₂ refl refl refl)
subeq _ U₂ ∙ (_ ▸ p₂) refl = 2>R1 (gt p₂ refl refl refl)
subeq _ U₂ (p₁ ◂ _) ∙ refl = 1>L2 (gt p₁ refl refl refl)
subeq _ U₂ (p₁ ◂ _) (p₂ ◂ _) eq with subeq _ U₂ p₁ p₂ (⊛eq eq .proj₁) | ⊛eq eq .proj₂
... | 1≡2 (same refl eq refl) | refl = 1≡2 (same refl eq refl)
... | 2>L1 (gt q refl refl refl) | refl = 2>L1 (gt q refl refl refl)
... | 2>R1 (gt q refl refl refl) | refl = 2>R1 (gt q refl refl refl)
... | 1>L2 (gt q refl refl refl) | refl = 1>L2 (gt q refl refl refl)
... | 1>R2 (gt q refl refl refl) | refl = 1>R2 (gt q refl refl refl)
... | 1/\2 (disj q q₁ q₂ refl refl refl refl) | refl = 1/\2 (disj (q ◂ _) q₁ q₂ refl refl refl refl)
... | 2/\1 (disj q q₁ q₂ refl refl refl refl) | refl = 2/\1 (disj (q ◂ _) q₁ q₂ refl refl refl refl)
subeq _ U₂ (p₁ ◂ _) (_ ▸ p₂) refl = 1/\2 (disj ∙ p₁ p₂ refl refl refl refl)
subeq _ U₂ (_ ▸ p₁) ∙ refl = 1>R2 (gt p₁ refl refl refl) 
subeq _ U₂ (_ ▸ p₁) (p₂ ◂ _) refl = 2/\1 (disj ∙ p₂ p₁ refl refl refl refl)
subeq _ U₂ (_ ▸ p₁) (_ ▸ p₂) eq with ⊛eq eq
... | refl , eq' with subeq _ U₂ p₁ p₂ eq'
... | 1≡2 (same refl eq refl) = 1≡2 (same refl eq refl)
... | 2>L1 (gt q refl refl refl) = 2>L1 (gt q refl refl refl)
... | 2>R1 (gt q refl refl refl) = 2>R1 (gt q refl refl refl)
... | 1>L2 (gt q refl refl refl) = 1>L2 (gt q refl refl refl)
... | 1>R2 (gt q refl refl refl) = 1>R2 (gt q refl refl refl)
... | 1/\2 (disj q q₁ q₂ refl refl refl refl) = 1/\2 (disj (_ ▸ q) q₁ q₂ refl refl refl refl)
... | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 2/\1 (disj (_ ▸ q) q₁ q₂ refl refl refl refl)
