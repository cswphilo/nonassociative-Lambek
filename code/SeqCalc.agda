{-# OPTIONS --rewriting #-}

module SeqCalc where

open import Relation.Binary.PropositionalEquality hiding ([_]; _≗_) 
open import Data.Product 
open import Fma

-- =======================================
-- The Non-Associative Lambek Calculus NL
-- =======================================

-- Inference rules of NL

data _⊢_ : Tree → Fma → Set where

  ax : ∀ {X}
    → η (at X) ⊢ at X

  ⇒R : ∀ {T A B}
    → η A ⊛ T ⊢ B
    → T ⊢ A ⇒ B

  ⇐R : ∀ {T A B}
    → T ⊛ η A ⊢ B
    → T ⊢ B ⇐ A

  ⇒L : ∀ {T U A B C}
    → (p : Path T)
    → U ⊢ A → sub p (η B) ⊢ C
    → sub p (U ⊛ η (A ⇒ B)) ⊢ C

  ⇐L : ∀ {T U A B C}
    → (p : Path T)
    → U ⊢ A → sub p (η B) ⊢ C
    → sub p (η (B ⇐ A) ⊛ U) ⊢ C

  ⊗R : ∀ {T U A B}
    → T ⊢ A → U ⊢ B
    → T ⊛ U ⊢ A ⊗ B

  ⊗L : ∀ {T A B C}
    → (p : Path T)
    → sub p (η A ⊛ η B) ⊢ C
    → sub p (η (A ⊗ B))  ⊢ C

subst-cxt : ∀ {T U C} → T ≡ U
  → T ⊢ C → U ⊢ C
subst-cxt refl f = f  

subst-succ : ∀ {T C C'} → C ≡ C'
  → T ⊢ C → T ⊢ C'
subst-succ refl f = f  

data _≗_ : {T : Tree} {A : Fma} → T ⊢ A → T ⊢ A → Set where
-- equivalence relation
  refl : ∀{T A} {f : T ⊢ A} → f ≗ f
  ~_ : ∀{T A} {f g : T ⊢ A} → f ≗ g → g ≗ f
  _∘_ : ∀{T A} {f g h : T ⊢ A} → f ≗ g → g ≗ h → f ≗ h

-- congruence
  ⇒R : ∀{T A B}
    → {f g : η A ⊛ T ⊢ B} 
    → f ≗ g
    → ⇒R f ≗ ⇒R g
  ⇐R : ∀{T A B}
    → {f g : T ⊛ η A ⊢ B} 
    → f ≗ g
    → ⇐R f ≗ ⇐R g
  ⇒L : ∀{T U A B C} {p : Path T}
    → {f f' : U ⊢ A} {g g' : sub p (η B) ⊢ C}
    → f ≗ f' → g ≗ g'
    → ⇒L p f g ≗ ⇒L p f' g'
  ⇐L : ∀{T U A B C} {p : Path T}
    → {f f' : U ⊢ A} {g g' : sub p (η B) ⊢ C}
    → f ≗ f' → g ≗ g'
    → ⇐L p f g ≗ ⇐L p f' g'
  ⊗R : ∀ {T U A B}
    → {f f' : T ⊢ A} {g g' : U ⊢ B}
    → f ≗ f' → g ≗ g'
    → ⊗R f g ≗ ⊗R f' g'
  ⊗L : ∀ {T A B C} {p : Path T}
    → {f g : sub p (η A ⊛ η B) ⊢ C}
    → f ≗ g
    → ⊗L p f ≗ ⊗L p g

-- permutative conversions
  ⇒L⇒R : ∀{T U A B A' B'} → {p : Path T} 
    → {f : U ⊢ A} {g : η A' ⊛ sub p (η B) ⊢ B'}
    → ⇒L p f (⇒R g) ≗ ⇒R (⇒L (_ ▸ p) f g)
  ⇐L⇒R : ∀{T U A B A' B'} → {p : Path T} 
    → {f : U ⊢ A} {g : η A' ⊛ sub p (η B) ⊢ B'}
    → ⇐L p f (⇒R g) ≗ ⇒R (⇐L (_ ▸ p) f g)
  ⊗L⇒R : ∀{T A B A' B'} → {p : Path T} 
    → {f : η A' ⊛ sub p (η A ⊛ η B) ⊢ B'}
    → ⊗L p (⇒R f) ≗ ⇒R (⊗L (_ ▸ p) f)
  ⇒L⇐R : ∀{T U A B A' B'} → {p : Path T} 
    → {f : U ⊢ A} {g : sub p (η B) ⊛ η A'  ⊢ B'}
    → ⇒L p f (⇐R g) ≗ ⇐R (⇒L (p ◂ _) f g)
  ⇐L⇐R : ∀{T U A B A' B'} → {p : Path T} 
    → {f : U ⊢ A} {g : sub p (η B) ⊛ η A'  ⊢ B'}
    → ⇐L p f (⇐R g) ≗ ⇐R (⇐L (p ◂ _) f g)
  ⊗L⇐R : ∀{T A B A' B'} → {p : Path T} 
    → {f : sub p (η A ⊛ η B) ⊛ η A' ⊢ B'}
    → ⊗L p (⇐R f) ≗ ⇐R (⊗L (p ◂ _) f)
  ⇒L⊗R₁ : ∀{T U V A B A' B'} → {p : Path T} 
    → {f : U ⊢ A} {g : sub p (η B) ⊢ A'}
    → {h : V ⊢ B'}
    → ⇒L (p ◂ _) f (⊗R g h) ≗ ⊗R (⇒L p f g) h
  ⇒L⊗R₂ : ∀{T U V A B A' B'} → {p : Path T} 
    → {f : U ⊢ A} {g : V ⊢ A'}
    → {h : sub p (η B) ⊢ B'}
    → ⇒L (_ ▸ p) f (⊗R g h) ≗ ⊗R g (⇒L p f h)
  ⇐L⊗R₁ : ∀{T U V A B A' B'} → {p : Path T} 
    → {f : U ⊢ A} {g : sub p (η B) ⊢ A'}
    → {h : V ⊢ B'}
    → ⇐L (p ◂ _) f (⊗R g h) ≗ ⊗R (⇐L p f g) h
  ⇐L⊗R₂ : ∀{T U V A B A' B'} → {p : Path T} 
    → {f : U ⊢ A} {g : V ⊢ A'}
    → {h : sub p (η B) ⊢ B'}
    → ⇐L (_ ▸ p) f (⊗R g h) ≗ ⊗R g (⇐L p f h)
  ⊗L⊗R₁ : ∀{T U A B A' B'} → {p : Path T} 
    → {f : sub p (η A ⊛ η B) ⊢ A'}
    → {g : U ⊢ B'}
    → ⊗L (p ◂ _) (⊗R f g) ≗ ⊗R (⊗L p f) g
  ⊗L⊗R₂ : ∀{T U A B A' B'} → {p : Path T} 
    → {f : U ⊢ A'}
    → {g : sub p (η A ⊛ η B) ⊢ B'}
    → ⊗L (_ ▸ p) (⊗R f g) ≗ ⊗R f (⊗L p g)
  ⊗L⊗L : ∀ {T W₁ W₂ A B A' B' C} 
    → {p : Path T} {p₁ : Path W₁} {p₂ : Path W₂}
    → {f : sub p (sub p₁ (η A ⊛ η B) ⊛ sub p₂ (η A' ⊛ η B')) ⊢ C}
    → ⊗L (p ++ (_ ▸ p₂)) (⊗L (p ++ (p₁ ◂ _)) f) ≗ ⊗L (p ++ (p₁ ◂ _)) (⊗L (p ++ (_ ▸ p₂)) f)
  ⊗L⇒L₁ : ∀{T U A B A' B' C} → {p : Path T} {p' : Path U}
    → {f : sub p (η A' ⊛ η B') ⊢ A} {g : sub p' (η B) ⊢ C}
    → ⊗L (p' ++ (p ◂ _)) (⇒L p' f g) ≗ ⇒L p' (⊗L p f) g
  ⊗L⇒L₂1/\2 : ∀{T U W₁ W₂ A B A' B' C} 
    → {p : Path T} {p₁ : Path W₁} {p₂ : Path W₂}
    → {f : U ⊢ A} {g : sub p (sub p₁ (η A' ⊛ η B') ⊛ sub p₂ (η B)) ⊢ C}
    → ⊗L (p ++ (p₁ ◂ _)) (⇒L (p ++ (_ ▸ p₂)) f g) ≗ ⇒L (p ++ (_ ▸ p₂)) f (⊗L (p ++ (p₁ ◂ _)) g) 
  ⊗L⇒L₂2/\1 : ∀{T U W₁ W₂ A B A' B' C} 
    → {p : Path T} {p₁ : Path W₁} {p₂ : Path W₂}
    → {f : U ⊢ A} {g : sub p (sub p₁ (η B) ⊛ sub p₂ (η A' ⊛ η B')) ⊢ C}
    → ⊗L (p ++ (_ ▸ p₂)) (⇒L (p ++ (p₁ ◂ _)) f g) ≗ ⇒L (p ++ (p₁ ◂ _)) f (⊗L (p ++ (_ ▸ p₂)) g) 
  ⊗L⇐L₁ : ∀{T U A B A' B' C} → {p : Path T} {p' : Path U}
    → {f : sub p (η A' ⊛ η B') ⊢ A} {g : sub p' (η B) ⊢ C}
    → ⊗L (p' ++ (_ ▸ p)) (⇐L p' f g) ≗ ⇐L p' (⊗L p f) g
  ⊗L⇐L₂1/\2 : ∀{T U W₁ W₂ A B A' B' C} 
    → {p : Path T} {p₁ : Path W₁} {p₂ : Path W₂}
    → {f : U ⊢ A} {g : sub p (sub p₁ (η A' ⊛ η B') ⊛ sub p₂ (η B)) ⊢ C}
    → ⊗L (p ++ (p₁ ◂ _)) (⇐L (p ++ (_ ▸ p₂)) f g) ≗ ⇐L (p ++ (_ ▸ p₂)) f (⊗L (p ++ (p₁ ◂ _)) g) 
  ⊗L⇐L₂2/\1 : ∀{T U W₁ W₂ A B A' B' C} 
    → {p : Path T} {p₁ : Path W₁} {p₂ : Path W₂}
    → {f : U ⊢ A} {g : sub p (sub p₁ (η B) ⊛ sub p₂ (η A' ⊛ η B')) ⊢ C}
    → ⊗L (p ++ (_ ▸ p₂)) (⇐L (p ++ (p₁ ◂ _)) f g) ≗ ⇐L (p ++ (p₁ ◂ _)) f (⊗L (p ++ (_ ▸ p₂)) g)   
  ⇒L⇒L : ∀{T U V W A B A' B' C} → {p : Path T} {q : Path V} {r : Path W}
    → {f : sub p U ⊢ A'}
    → {g : sub q (η B') ⊢ A} {h : sub r (η B) ⊢ C}
    → ⇒L (r ++ (q ◂ _)) f (⇒L r g h) ≗ ⇒L r (⇒L q f g) h
  ⇒L⇒L₂1/\2 : ∀{T U V W₁ W₂ A B A' B' C} 
    → {p : Path T} {p₁ : Path W₁} {p₂ : Path W₂}
    → {f : U ⊢ A} {f' : V ⊢ A'}
    → {g : sub p (sub p₁ (η B') ⊛ sub p₂ (η B)) ⊢ C}
    → ⇒L (p ++ (_ ▸ p₂)) f (⇒L (p ++ (p₁ ◂ _)) f' g) ≗ ⇒L (p ++ (_ ▸ p₂)) f (⇒L (p ++ (p₁ ◂ _)) f' g) 
  ⇒L⇒L₂2/\1 : ∀{T U V W₁ W₂ A B A' B' C} 
    → {p : Path T} {p₁ : Path W₁} {p₂ : Path W₂}
    → {f : U ⊢ A} {f' : V ⊢ A'}
    → {g : sub p (sub p₁ (η B) ⊛ sub p₂ (η B')) ⊢ C}
    → ⇒L (p ++ (p₁ ◂ _)) f (⇒L (p ++ (_ ▸ p₂)) f' g) ≗ ⇒L (p ++ (p₁ ◂ _)) f (⇒L (p ++ (_ ▸ p₂)) f' g)
  ⇒L⇐L : ∀{T U V W A B A' B' C} → {p : Path T} {q : Path V} {r : Path W}
    → {f : sub p U ⊢ A'}
    → {g : sub q (η B') ⊢ A} {h : sub r (η B) ⊢ C}
    → ⇒L (r ++ (_ ▸ q)) f (⇐L r g h) ≗ ⇐L r (⇒L q f g) h
  ⇒L⇐L₂1/\2 : ∀{T U V W₁ W₂ A B A' B' C} 
    → {p : Path T} {p₁ : Path W₁} {p₂ : Path W₂}
    → {f : U ⊢ A} {f' : V ⊢ A'}
    → {g : sub p (sub p₁ (η B') ⊛ sub p₂ (η B)) ⊢ C}
    → ⇒L (p ++ (_ ▸ p₂)) f (⇐L (p ++ (p₁ ◂ _)) f' g) ≗ ⇒L (p ++ (_ ▸ p₂)) f (⇐L (p ++ (p₁ ◂ _)) f' g) 
  ⇒L⇐L₂2/\1 : ∀{T U V W₁ W₂ A B A' B' C} 
    → {p : Path T} {p₁ : Path W₁} {p₂ : Path W₂}
    → {f : U ⊢ A} {f' : V ⊢ A'}
    → {g : sub p (sub p₁ (η B) ⊛ sub p₂ (η B')) ⊢ C}
    → ⇒L (p ++ (p₁ ◂ _)) f (⇐L (p ++ (_ ▸ p₂)) f' g) ≗ ⇒L (p ++ (p₁ ◂ _)) f (⇐L (p ++ (_ ▸ p₂)) f' g)
  ⇐L⇒L : ∀{T U V W A B A' B' C} → {p : Path T} {q : Path V} {r : Path W}
    → {f : sub p U ⊢ A'}
    → {g : sub q (η B') ⊢ A} {h : sub r (η B) ⊢ C}
    → ⇐L (r ++ (q ◂ _)) f (⇒L r g h) ≗ ⇒L r (⇐L q f g) h
  ⇐L⇒L₂1/\2 : ∀{T U V W₁ W₂ A B A' B' C} 
    → {p : Path T} {p₁ : Path W₁} {p₂ : Path W₂}
    → {f : U ⊢ A} {f' : V ⊢ A'}
    → {g : sub p (sub p₁ (η B') ⊛ sub p₂ (η B)) ⊢ C}
    → ⇐L (p ++ (_ ▸ p₂)) f (⇒L (p ++ (p₁ ◂ _)) f' g) ≗ ⇐L (p ++ (_ ▸ p₂)) f (⇒L (p ++ (p₁ ◂ _)) f' g) 
  ⇐L⇒L₂2/\1 : ∀{T U V W₁ W₂ A B A' B' C} 
    → {p : Path T} {p₁ : Path W₁} {p₂ : Path W₂}
    → {f : U ⊢ A} {f' : V ⊢ A'}
    → {g : sub p (sub p₁ (η B) ⊛ sub p₂ (η B')) ⊢ C}
    → ⇐L (p ++ (p₁ ◂ _)) f (⇒L (p ++ (_ ▸ p₂)) f' g) ≗ ⇐L (p ++ (p₁ ◂ _)) f (⇒L (p ++ (_ ▸ p₂)) f' g)
  ⇐L⇐L : ∀{T U V W A B A' B' C} → {p : Path T} {q : Path V} {r : Path W}
    → {f : sub p U ⊢ A'}
    → {g : sub q (η B') ⊢ A} {h : sub r (η B) ⊢ C}
    → ⇐L (r ++ (_ ▸ q)) f (⇐L r g h) ≗ ⇐L r (⇐L q f g) h
  ⇐L⇐L₂1/\2 : ∀{T U V W₁ W₂ A B A' B' C} 
    → {p : Path T} {p₁ : Path W₁} {p₂ : Path W₂}
    → {f : U ⊢ A} {f' : V ⊢ A'}
    → {g : sub p (sub p₁ (η B') ⊛ sub p₂ (η B)) ⊢ C}
    → ⇐L (p ++ (_ ▸ p₂)) f (⇐L (p ++ (p₁ ◂ _)) f' g) ≗ ⇐L (p ++ (_ ▸ p₂)) f (⇐L (p ++ (p₁ ◂ _)) f' g) 
  ⇐L⇐L₂2/\1 : ∀{T U V W₁ W₂ A B A' B' C} 
    → {p : Path T} {p₁ : Path W₁} {p₂ : Path W₂}
    → {f : U ⊢ A} {f' : V ⊢ A'}
    → {g : sub p (sub p₁ (η B) ⊛ sub p₂ (η B')) ⊢ C}
    → ⇐L (p ++ (p₁ ◂ _)) f (⇐L (p ++ (_ ▸ p₂)) f' g) ≗ ⇐L (p ++ (p₁ ◂ _)) f (⇐L (p ++ (_ ▸ p₂)) f' g)

≡to≗ : ∀{T C}
  → {f g : T ⊢ C}
  → f ≡ g
  → f ≗ g
≡to≗ refl = refl

-- -- η-conversions
--   ax⊗ : {A B : Fma} → ax ≗ ⊗L {A = A} {B} leaf (⊗R ax ax)
--   ax⇒ : {A B : Fma} → ax ≗ ⇒R {A = A} {B} (⇒L leaf ax ax)
--   ax⇐ : {A B : Fma} → ax ≗ ⇐R {A = A} {B} (⇐L leaf ax ax)

⇒L' : ∀ {T U V W A B C}
  → (p : Path T)
  → U ⊢ A → W ⊢ C
  → W ≡ sub p (η B)
  → V ≡ sub p (U ⊛ η (A ⇒ B))
  → V ⊢ C
⇒L' p f g refl refl = ⇒L p f g

⇐L' : ∀ {T U V W A B C}
  → (p : Path T)
  → U ⊢ A → W ⊢ C
  → W ≡ sub p (η B)
  → V ≡ sub p (η (B ⇐ A) ⊛ U)
  → V ⊢ C
⇐L' p f g refl refl = ⇐L p f g  

⊗L' : ∀ {T V W A B C}
  → (p : Path T)
  → W ⊢ C
  → W ≡ sub p (η A ⊛ η B)
  → V ≡ sub p (η (A ⊗ B)) 
  → V ⊢ C
⊗L' p f refl refl = ⊗L p f


 