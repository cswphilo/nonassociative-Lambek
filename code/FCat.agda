{-# OPTIONS --rewriting #-}

module FCat where

open import Fma 

infix 15 _⟶_ 
infixl 20 _∘_ 

data _⟶_ : Fma → Fma → Set where
  id : {A : Fma} → A ⟶ A
  _∘_ : {A B C : Fma} → (f : B ⟶ C) → (g : A ⟶ B) → A ⟶ C
  _⊗_ : {A B C D : Fma} → (f : A ⟶ B) → (g : C ⟶ D) → A ⊗ C ⟶ B ⊗ D 
  _⇒_ : {A B C D : Fma} → (f : B ⟶ A) → (g : C ⟶ D) → A ⇒ C ⟶ B ⇒ D
  _⇐_ : {A B C D : Fma} → (f : C ⟶ D) → (g : B ⟶ A) → C ⇐ A ⟶ D ⇐ B
  π⇒ : {A B C : Fma} → (f : A ⊗ B ⟶ C) → B ⟶ A ⇒ C
  π⇒-1 : {A B C : Fma} → (f : B ⟶ A ⇒ C) → A ⊗ B ⟶ C
  π⇐ : {A B C : Fma} → (f : A ⊗ B ⟶ C) → A ⟶ C ⇐ B
  π⇐-1 : {A B C : Fma} → (f : A ⟶ C ⇐ B) → A ⊗ B ⟶ C

subst-ant : ∀ {A B C} → A ≡ B → A ⟶ C → B ⟶ C
subst-ant refl f = f
subst-suc : ∀ {A B C} → B ≡ C → A ⟶ B → A ⟶ C
subst-suc refl f = f
-- infixl 25  _⇐'_
-- _⇐'_ : {A B C D : Fma} → (f : B ⟶ A) → (g : C ⟶ D) → C ⇐ A ⟶ D ⇐ B
-- _⇐'_ f g = π⇐ (g ∘ ε ∘ id ⊗ f) 
-- ⇐ is definable via ε

infix 15 _≐_
infixl 20 _．_
infix 21 ~_

data _≐_ : {A B : Fma} → A ⟶ B → A ⟶ B → Set where
  -- ≐ equivalence and congruence
  refl : {A B : Fma} {f : A ⟶ B} → f ≐ f
  ~_ : {A B : Fma} {f g : A ⟶ B} → f ≐ g → g ≐ f
  _．_ : {A B : Fma} {f g h : A ⟶ B} → f ≐ g → g ≐ h → f ≐ h
  _∘_ : {A B C : Fma} {f g : B ⟶ C} {h k : A ⟶ B} →
                         f ≐ g → h ≐ k → f ∘ h ≐ g ∘ k
  _⊗_ : {A B C D : Fma} {f g : A ⟶ C} {h k : B ⟶ D} →
                         f ≐ g → h ≐ k → f ⊗ h ≐ g ⊗ k
  _⇒_ : {A B C D : Fma} {f g : A ⟶ C} {h k : B ⟶ D} →
                         f ≐ g → h ≐ k → h ⇒ f ≐ k ⇒ g
  _⇐_ : {A B C D : Fma} {f g : A ⟶ C} {h k : B ⟶ D} →
                         f ≐ g → h ≐ k → f ⇐ h ≐ g ⇐ k
  π⇐ : {A B C : Fma} → {f g : A ⊗ B ⟶ C} → f ≐ g → π⇐ f ≐ π⇐ g
  π⇐-1 : {A B C : Fma} → {f g : A ⟶ C ⇐ B} → f ≐ g → π⇐-1 f ≐ π⇐-1 g
  π⇒ : {A B C : Fma} → {f g : A ⊗ B ⟶ C} → f ≐ g → π⇒ f ≐ π⇒ g
  π⇒-1 : {A B C : Fma} → {f g : B ⟶ A ⇒ C} → f ≐ g → π⇒-1 f ≐ π⇒-1 g

  -- id, ∘ category
  lid : {A B : Fma} {f : A ⟶ B} → id ∘ f ≐ f
  rid : {A B : Fma} {f : A ⟶ B} → f ≐ f ∘ id
  ass : {A B C D : Fma} {f : C ⟶ D} {g : B ⟶ C} {h : A ⟶ B}
       → f ∘ g ∘ h ≐ f ∘ (g ∘ h)
       
  -- ⊗ functorial
  f⊗id : {A B : Fma} → id {A} ⊗ id {B} ≐ id
  f⊗∘ : {A B C D E F : Fma} {f : A ⟶ C} {g : B ⟶ D} {h : C ⟶ E} {k : D ⟶ F} →  
                    (h ∘ f) ⊗ (k ∘ g) ≐ h ⊗ k ∘ f ⊗ g

  -- ⇒ functorial
  f⇒id : {A B : Fma} → id {A} ⇒ id {B} ≐ id
  f⇒∘ : {A B C D E F : Fma} {f : A ⟶ C} {g : B ⟶ D} {h : C ⟶ E} {k : D ⟶ F} →  
                    (h ∘ f) ⇒ (k ∘ g) ≐ f ⇒ k ∘ h ⇒ g   

  -- ⇐ functorial
  f⇐id : {A B : Fma} → id {B} ⇐ id {A} ≐ id
  f⇐∘ : {A B C D E F : Fma} {f : A ⟶ C} {g : B ⟶ D} {h : C ⟶ E} {k : D ⟶ F} →  
                    (k ∘ g) ⇐ (h ∘ f) ≐ k ⇐ f ∘ g ⇐ h
  
  -- π­⇒ natural 
  π⇒A : {A B A' : Fma} {f : A' ⟶ A} 
        → π⇒ (f ⊗ (id {B})) ≐ f ⇒ id ∘ π⇒ id
  π⇒B : {A B C B' : Fma} {f : A ⊗ B ⟶ C} {g : B' ⟶ B} 
        → (π⇒ f) ∘ g ≐ π⇒ (f ∘ id ⊗ g) 
  π⇒C : {A B C C' : Fma} {f : C ⟶ C'} {g : A ⊗ B ⟶ C}
        → π⇒ (f ∘ g) ≐ id ⇒ f ∘ π⇒ g

  -- π⇒ iso
  π⇒π⇒-1 : {A B C : Fma} {f : A ⊗ B ⟶ C} → π⇒-1 (π⇒ f) ≐ f
  π⇒-1π⇒ : {A B C : Fma} {f : B ⟶ A ⇒ C} → π⇒ (π⇒-1 f) ≐ f

  -- π⇐ natural 
  π⇐A : {A B C A' : Fma} {f : A ⊗ B ⟶ C} {g : A' ⟶ A} 
        → (π⇐ f) ∘ g ≐ π⇐ (f ∘ g ⊗ id) 
  π⇐B : {A B B' : Fma} {f : B' ⟶ B} 
        → π⇐ ((id {A}) ⊗ f) ≐ id ⇐ f ∘ π⇐ id
  π⇐C : {A B C C' : Fma} {f : C ⟶ C'} {g : A ⊗ B ⟶ C}
        → π⇐ (f ∘ g) ≐ f ⇐ id ∘ π⇐ g 

  -- π⇐ iso
  π⇐π⇐-1 : {A B C : Fma} {f : A ⊗ B ⟶ C} → π⇐-1 (π⇐ f) ≐ f
  π⇐-1π⇐ : {A B C : Fma} {f : A ⟶ C ⇐ B} → π⇐ (π⇐-1 f) ≐ f

refl≐' : {A B : Fma}{f g : A ⟶ B} → f ≡ g → f ≐ g
refl≐' refl = refl

-- equational reasoning sugar for ≐

infix 4 _≐'_
infix 1 proof≐_
infixr 2 _≐⟨_⟩_
infix 3 _qed≐

data _≐'_ {A B : Fma} (f g : A ⟶ B) : Set where
  relto :  f ≐ g → f ≐' g

proof≐_ : {A B : Fma} {f g : A ⟶ B} → f ≐' g → f ≐ g
proof≐ relto p = p

_≐⟨_⟩_ :  {A B : Fma} (f : A ⟶ B) {g h : A ⟶ B} → f ≐ g → g ≐' h → f ≐' h 
_ ≐⟨ p ⟩ relto q = relto (p ． q)

_qed≐  :  {A B : Fma} (f : A ⟶ B) → f ≐' f
_qed≐ _ = relto refl

-- some derivable laws

id⊗swap : {A B C D : Fma}
  → {f : A ⟶ B} {g : C ⟶ D}
  → id ⊗ f ∘ g ⊗ id ≐ g ⊗ id ∘ id ⊗ f
id⊗swap {f = f}{g} =
  proof≐
    id ⊗ f ∘ g ⊗ id
  ≐⟨ ~ f⊗∘ ⟩
    (id ∘ g) ⊗ (f ∘ id)
  ≐⟨ lid ⊗ (~ rid) ⟩
    g ⊗ f
  ≐⟨ rid ⊗ (~ lid) ⟩
    (g ∘ id) ⊗ (id ∘ f)
  ≐⟨ f⊗∘ ⟩
    g ⊗ id ∘ id ⊗ f
  qed≐

id⇒swap : {A B C D : Fma} 
  → {f : A ⟶ B} {g : C ⟶ D}
  → id ⇒ f ∘ g ⇒ id ≐ g ⇒ id ∘ id ⇒ f
id⇒swap = ~ f⇒∘ ． ((~ (lid ． rid)) ⇒ (~ (lid ． rid)) ． f⇒∘)

π⇒ANat : {A B C A' : Fma} {f : A ⊗ B ⟶ C} {g : A' ⟶ A} 
         → π⇒ (f ∘ (g ⊗ id)) ≐ g ⇒ id ∘ π⇒ f
π⇒ANat = 
  π⇒C ． (refl ∘ π⇒A ． (~ ass 
  ． (id⇒swap ∘ refl ． (ass ． (refl ∘ (~ π⇒C) ． (refl ∘ π⇒ (~ rid)))))))

id⇐swap : {A B C D : Fma} 
  → {f : A ⟶ B} {g : C ⟶ D}
  → f ⇐ id ∘ id ⇐ g ≐ id ⇐ g ∘ f ⇐ id
id⇐swap = ~ f⇐∘ ． ((~ (lid ． rid)) ⇐ (~ (lid ． rid)) ． f⇐∘)

π⇐BNat : {A B C B' : Fma} {f : A ⊗ B ⟶ C} {g : B' ⟶ B} 
         → π⇐ (f ∘ (id ⊗ g)) ≐ id ⇐ g ∘ π⇐ f
π⇐BNat = 
  π⇐C ． (refl ∘ π⇐B ． (~ ass 
  ． (id⇐swap ∘ refl ． (ass ． (refl ∘ (~ π⇐C) ． (refl ∘ π⇐ (~ rid)))))))
