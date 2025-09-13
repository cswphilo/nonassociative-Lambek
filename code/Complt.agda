{-# OPTIONS --rewriting #-}

module Complt where 

open import Fma
open import SeqCalc
open import FCat
open import Cut
open import CutAssociativities
open import CutCirceqEquations
open import CutCongruence
open import CutEqualities
open import FormulaeAxiom

complt : ∀ {A B} →  A ⟶ B → η A ⊢ B
complt id = axA
complt (f ∘ g) = cut ∙ (complt g) (complt f) refl
complt (f ⊗ g) = ⊗L ∙ (⊗R (complt f) (complt g))
complt (f ⇒ g) = ⇒R (⇒L ∙ (complt f) (complt g))
complt (g ⇐ f) = ⇐R (⇐L ∙ (complt f) (complt g))
complt (π⇒ f) = ⇒R (cut ∙ (⊗R axA axA) (complt f) refl)
complt (π⇒-1 f) = ⊗L ∙ (cut ∙ (⊗R axA (complt f)) (⊗L ∙ (⇒L ∙ axA axA)) refl) -- ⊗L ∙ (⇒R-1 (complt f))
complt (π⇐ f) = ⇐R (cut ∙ (⊗R axA axA) (complt f) refl)
complt (π⇐-1 f) = ⊗L ∙ (cut ∙ (⊗R (complt f) axA) (⊗L ∙ (⇐L ∙ axA axA)) refl) -- ⊗L ∙ (⇐R-1 (complt f))

⇒Rcut⇒L : ∀ {A B C}
  → (f : A ⊢ B ⇒ C)
  → ⇒R (cut⇒L ∙ f axA axA) ≗ f
⇒Rcut⇒L (⇒R f) = ⇒R (axA-cut-left-unit (∙ ◂ _) (cut ∙ f axA refl) refl ∘ axA-cut-right-unit f)
⇒Rcut⇒L (⇒L p f g) = ~ ⇒L⇒R ∘ ⇒L refl (⇒Rcut⇒L g)
⇒Rcut⇒L (⇐L p f g) = ~ ⇐L⇒R ∘ ⇐L refl (⇒Rcut⇒L g)
⇒Rcut⇒L (⊗L p f) = ~ ⊗L⇒R ∘ ⊗L (⇒Rcut⇒L f)

⇐Rcut⇐L : ∀ {A B C}
  → (f : A ⊢ C ⇐ B)
  → ⇐R (cut⇐L ∙ f axA axA) ≗ f
⇐Rcut⇐L (⇐R f) = ⇐R (axA-cut-left-unit (_ ▸ ∙) (cut ∙ f axA refl) refl ∘ axA-cut-right-unit f)
⇐Rcut⇐L (⇒L p f g) = ~ ⇒L⇐R ∘ ⇒L refl (⇐Rcut⇐L g)
⇐Rcut⇐L (⇐L p f g) = ~ ⇐L⇐R ∘ ⇐L refl (⇐Rcut⇐L g)
⇐Rcut⇐L (⊗L p f) = ~ ⊗L⇐R ∘ ⊗L (⇐Rcut⇐L f)

-- Complt preserves equivalence on derivations.
≐complt≗ : ∀ {A B} 
  → {f g : A ⟶ B}
  → (eq : f ≐ g)
  → complt f ≗ complt g
≐complt≗ refl = refl
≐complt≗ (~ eq) = ~ ≐complt≗ eq
≐complt≗ (eq ． eq₁) = ≐complt≗ eq ∘ ≐complt≗ eq₁
≐complt≗ (_∘_ {f = f} {g} {h} {k} eq eq₁) = 
  cut-cong1 ∙ (complt f) refl (≐complt≗ eq₁) 
  ∘ cut-cong2 ∙ (complt k) refl (≐complt≗ eq)
≐complt≗ (eq ⊗ eq₁) = ⊗L (⊗R (≐complt≗ eq) (≐complt≗ eq₁))
≐complt≗ (eq ⇒ eq₁) = ⇒R (⇒L (≐complt≗ eq₁) (≐complt≗ eq))
≐complt≗ (eq ⇐ eq₁) = ⇐R (⇐L (≐complt≗ eq₁) (≐complt≗ eq))
≐complt≗ (π⇒ eq) = ⇒R (cut-cong2 ∙ _ refl (≐complt≗ eq))
≐complt≗ (π⇒-1 eq) = ⊗L (cut-cong2 (∙ ◂ _) axA refl (cut⇒L-cong1 ∙ axA axA (≐complt≗ eq))) -- ⊗L (⇒R-1≗  (≐complt≗ eq)) -- congruence of ⇒R-1
≐complt≗ (π⇐ eq) = ⇐R (cut-cong2 ∙ _ refl (≐complt≗ eq))
≐complt≗ (π⇐-1 eq) = ⊗L (cut⇐L-cong1 ∙ (cut ∙ axA axA refl) axA (≐complt≗ eq)) -- ⊗L (⇐R-1≗  (≐complt≗ eq)) -- congruence of ⇐R-1
≐complt≗ {g = g} lid = axA-cut-right-unit (complt g) -- axA is also a unit (both left and right) for cut
≐complt≗ {f = f} rid = ~ axA-cut-left-unit _ (complt f) _
≐complt≗ (ass {f = f} {g} {h}) = ~ (≡to≗ (cut-vass ∙ ∙ (complt h) (complt g) (complt f) refl refl))
≐complt≗ f⊗id = refl
≐complt≗ f⊗∘ = refl
≐complt≗ f⇒id = refl
≐complt≗ (f⇒∘ {f = f} {g} {k = k}) = 
  ⇒R (~ (cut-cong2 (∙ ◂ _) (complt f) refl (cut⇒L≗ ∙ ∙ (complt g) (complt k) refl)))
≐complt≗ f⇐id = refl
≐complt≗ (f⇐∘ {f = f} {g} {k = k}) = 
  ⇐R (~ (cut-cong2 (_ ▸ ∙) (complt f) refl (cut⇐L≗ ∙ ∙ (complt g) (complt k) refl)))
≐complt≗ (π⇒A {f = f}) = 
  ⇒R 
  (⊗R (axA-cut-left-unit ∙ (complt f) refl ∘ (((~ axA-cut-right-unit (complt f)) 
          ∘ ~ cut-cong2 ∙ (complt f) refl (axA-cut-right-unit axA)) 
          ∘ ~ cut-cong2 ∙ (complt f) refl (cut-cong1 ∙ axA refl (axA-cut-right-unit axA)))) 
       (~ cut-cong1 ∙ axA refl (axA-cut-left-unit ∙ axA refl)))
≐complt≗ (π⇒B {f = f} {g}) = 
  ⇒R (~ ≡to≗ (cut-vass (_ ▸ ∙) ∙ (complt g) (⊗R axA axA) (complt f) refl refl) 
  ∘ (cut-cong1 ∙ (complt f) refl 
    (⊗R refl (axA-cut-right-unit (complt g))) 
  ∘ (cut-cong1 ∙ (complt f) refl 
  (⊗R (~ axA-cut-right-unit axA) 
       (~ axA-cut-left-unit ∙ (complt g) refl)) 
  ∘ ≡to≗ (cut-vass ∙ ∙ (⊗R axA axA) (⊗L ∙ (⊗R axA (complt g))) (complt f) refl refl))))
≐complt≗ (π⇒C {f = f} {g}) = 
  ⇒R ((~ ≡to≗ (cut-vass ∙ ∙ (⊗R axA axA)  (complt g) (complt f) refl refl)) 
  ∘ ~ axA-cut-left-unit (∙ ◂ _) (cut ∙ (cut ∙ (⊗R axA axA) (complt g) refl) (complt f) refl) refl) 
≐complt≗ (π⇐A {f = f} {g}) = 
  ⇐R ((~ ≡to≗ (cut-vass (∙ ◂ _) ∙ (complt g) (⊗R axA axA) (complt f) refl refl)) 
  ∘ (cut-cong1 ∙ (complt f) refl 
  (⊗R (axA-cut-right-unit (complt g) ∘ (~ axA-cut-left-unit ∙ (complt g) refl)) 
       (~ axA-cut-left-unit ∙ axA refl)) 
  ∘ ≡to≗ (cut-vass ∙ ∙ (⊗R axA axA) (⊗L ∙ (⊗R (complt g) axA)) (complt f) refl refl))) 
≐complt≗ (π⇐B {f = f}) = 
  ⇐R 
  (⊗R (~ cut-cong1 ∙ axA refl (axA-cut-left-unit ∙ axA refl)) 
       (axA-cut-left-unit ∙ (complt f) refl ∘ (((~ axA-cut-right-unit (complt f)) 
          ∘ ~ cut-cong2 ∙ (complt f) refl (axA-cut-right-unit axA)) 
          ∘ ~ cut-cong2 ∙ (complt f) refl (cut-cong1 ∙ axA refl (axA-cut-right-unit axA)))))
≐complt≗ (π⇐C {f = f} {g}) = 
  ⇐R ((~ ≡to≗ (cut-vass ∙ ∙ (⊗R axA axA)  (complt g) (complt f) refl refl)) 
  ∘ ~ axA-cut-left-unit (_ ▸ ∙) (cut ∙ (cut ∙ (⊗R axA axA) (complt g) refl) (complt f) refl) refl)
≐complt≗ {g = g} π⇒π⇒-1 = 
  ⊗L ((axA-cut-left-unit (∙ ◂ _) (cut (∙ ◂ _) axA (cut ∙ (cut ∙ (⊗R axA axA) (complt g) refl) axA refl) refl) refl) 
  ∘ (axA-cut-left-unit (∙ ◂ _) (cut ∙ (cut ∙ (⊗R axA axA) (complt g) refl) axA refl) refl)
  ∘ (axA-cut-right-unit (cut ∙ (⊗R axA axA) (complt g) refl))) 
  ∘ (~ cut⊗L≗ ∙ ∙ (⊗R axA axA) (complt g) refl ∘ axA-cut-left-unit ∙ (complt g) refl)
  -- (~ cut⊗L≗ ∙ ∙ (⊗R axA axA) (complt g) refl) 
  -- ∘ axA-cut-left-unit ∙ (complt g) refl
≐complt≗ {g = g} π⇒-1π⇒ = 
  ⇒R (axA-cut-left-unit (∙ ◂ _) (cut (_ ▸ ∙) axA (cut (∙ ◂ _) axA (cut⇒L ∙ (complt g) axA axA) refl) refl) refl 
  ∘ (axA-cut-left-unit (_ ▸ ∙) (cut (∙ ◂ _) axA (cut⇒L ∙ (complt g) axA axA) refl) refl) 
  ∘ (axA-cut-left-unit (∙ ◂ _) (cut⇒L ∙ (complt g) axA axA) refl)) 
  ∘ ⇒Rcut⇒L (complt g)
  -- ⇒R (cut-cong2 (∙ ◂ _) axA refl (axA-cut-left-unit (_ ▸ ∙) (⇒R-1 (complt g)) refl)) 
  -- ∘ (⇒R (axA-cut-left-unit (∙ ◂ _) (⇒R-1 (complt g)) refl) 
  -- ∘ ⇒R⇒R-1 _) -- ⇒R and ⇒R-1 are inverses  
≐complt≗ {g = g} π⇐π⇐-1 = 
  ⊗L (cut-cong1 (_ ▸ ∙) (cut ∙ (cut ∙ (⊗R axA axA) (complt g) refl) axA refl) refl (axA-cut-right-unit axA) 
  ∘ (axA-cut-left-unit (_ ▸ ∙) (cut ∙ (cut ∙ (⊗R axA axA) (complt g) refl) axA refl) refl)
  ∘ axA-cut-right-unit (cut ∙ (⊗R axA axA) (complt g) refl)) 
  ∘ (~ cut⊗L≗ ∙ ∙ (⊗R axA axA) (complt g) refl ∘ axA-cut-left-unit ∙ (complt g) refl)
  -- (~ cut⊗L≗ ∙ ∙ (⊗R axA axA) (complt g) refl) 
  -- ∘ axA-cut-left-unit ∙ (complt g) refl 
≐complt≗ {g = g} π⇐-1π⇐ = 
  ⇐R (axA-cut-left-unit (∙ ◂ _) (cut (_ ▸ ∙) axA (cut⇐L ∙ (complt g) (cut ∙ axA axA refl) axA) refl) refl
  ∘ axA-cut-left-unit (_ ▸ ∙ ) (cut⇐L ∙ (complt g) (cut ∙ axA axA refl) axA) refl
  ∘ cut⇐L-cong2 ∙ (complt g) (cut ∙ axA axA refl) axA axA axA (axA-cut-right-unit axA) refl) 
  ∘ ⇐Rcut⇐L (complt g)
  -- ⇐R (cut-cong2 (∙ ◂ _) axA refl (axA-cut-left-unit (_ ▸ ∙) (⇐R-1 (complt g)) refl)) 
  -- ∘ (⇐R (axA-cut-left-unit (∙ ◂ _) (⇐R-1 (complt g)) refl) 
  -- ∘ ⇐R⇐R-1 _) -- ⇐R and ⇐R-1 are inverses  