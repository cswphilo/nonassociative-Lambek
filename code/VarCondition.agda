{-# OPTIONS --rewriting #-}

module VarCondition where

open import Fma
open import SeqCalc
open import Interpolation

-- ===============================================
-- The variable condition of Maehara interpolation
-- ===============================================

open MIP

_∈_ : (X : At) → Fma → Set
X ∈ at Y = X ≡ Y
X ∈ (A ⇒ B) = X ∈ A ⊎ X ∈ B
X ∈ (B ⇐ A) = X ∈ A ⊎ X ∈ B
X ∈ (A ⊗ B) = X ∈ A ⊎ X ∈ B
  
data _∈ᵀ_ (X : At) : Tree → Set where
  at : ∀ {A} → X ∈ A → X ∈ᵀ η A
  left : ∀ {T U} → X ∈ᵀ T → X ∈ᵀ T ⊛ U
  right : ∀ {T U} → X ∈ᵀ U → X ∈ᵀ T ⊛ U

sub∈ : ∀ {A T U} (p : Path T) → A ∈ᵀ sub p U → A ∈ᵀ T ⊎ A ∈ᵀ U
sub∈ ∙ (at m) = inj₂ (at m)
sub∈ ∙ (left m) = inj₂ (left m)
sub∈ ∙ (right m) = inj₂ (right m)
sub∈ (p ◂ _) (left m) = elim⊎ (λ n → inj₁ (left n)) inj₂ (sub∈ p m)
sub∈ (p ◂ _) (right m) = inj₁ (right m)
sub∈ (T ▸ p) (left m) = inj₁ (left m)
sub∈ (T ▸ p) (right m) = elim⊎ (λ x → inj₁ (right x)) inj₂ (sub∈ p m)

∈sub₁ : ∀ {A T U} (p : Path T) → A ∈ᵀ T → A ∈ᵀ sub p U
∈sub₁ (p ◂ _) (left m) = left (∈sub₁ p m)
∈sub₁ (p ◂ _) (right m) = right m
∈sub₁ (_ ▸ p) (left m) = left m
∈sub₁ (_ ▸ p) (right m) = right (∈sub₁ p m)

∈sub₂ : ∀ {A T U} (p : Path T) → A ∈ᵀ U → A ∈ᵀ sub p U
∈sub₂ ∙ m = m
∈sub₂ (p ◂ _) m = left (∈sub₂ p m)
∈sub₂ (_ ▸ p) m = right (∈sub₂ p m)

record VarCond (T : Tree) (p : Path T) (U : Tree) (C D : Fma) : Set where
  constructor var
  field
    varg : ∀ {X} → X ∈ D → X ∈ᵀ T ⊎ X ∈ C
    varh : ∀ {X} → X ∈ D → X ∈ᵀ U

varcond : ∀ {T} (p : Path T) U {V C}
  → (f : V ⊢ C) (eq : V ≡ sub p U) 
  → VarCond T p U C (D (mip' p U f eq))
varcond {T = T} p _ (⇒R f) refl with varcond (_ ▸ p) _ f refl
... | var vg vh =
  var
    (λ m → lem (vg m))
    vh
  where
    lem : ∀ {X A B} → (X ∈ᵀ (η A ⊛ T)) ⊎ (X ∈ B) → (X ∈ᵀ T) ⊎ (X ∈ A) ⊎ (X ∈ B)
    lem (inj₁ (left (at x))) = inj₂ (inj₁ x)
    lem (inj₁ (right x)) = inj₁ x
    lem (inj₂ y) = inj₂ (inj₂ y)

varcond {T} p _ (⇐R f) refl with varcond (p ◂ _) _ f refl
... | var vg vh =
  var
    (λ m → lem (vg m))
    vh
  where
    lem : ∀ {X A B} → (X ∈ᵀ (T ⊛ η A)) ⊎ (X ∈ B) → (X ∈ᵀ T) ⊎ (X ∈ A) ⊎ (X ∈ B)
    lem (inj₁ (left x)) = inj₁ x
    lem (inj₁ (right (at x))) = inj₂ (inj₁ x)
    lem (inj₂ y) = inj₂ (inj₂ y)

varcond p U (⇒L p' f f') eq with subeq _ _ p' p eq
varcond p ._ (⇒L {U = U} .(p ++ (q ◂ _)) f f') eq | 1>L2 (gt {W₁ = W₁} {W₂ = W₂} q refl refl refl) with varcond p _ f' refl
... | var vg vh =
  var
    vg
    (λ m → lem (vh m))
  where
    lem' : ∀ {A B X} → (X ∈ᵀ W₁) ⊎ (X ∈ᵀ η B) → X ∈ᵀ sub q (U ⊛ η (A ⇒ B))
    lem' n = elim⊎ (∈sub₁ q) (λ { (at m) → ∈sub₂ q (right (at (inj₂ m)))}) n

    lem : ∀ {A B X} → X ∈ᵀ (sub q (η B) ⊛ W₂) → X ∈ᵀ (sub q (U ⊛ η (A ⇒ B)) ⊛ W₂)
    lem (left n) = left (lem' (sub∈ q n))
    lem (right n) = right n

varcond p ._ (⇒L {U = U} _ f f') eq | 1>R2 (gt {W₁ = W₁} q refl refl refl) with varcond p _ f' refl
... | var vg vh =
  var
    vg
    (λ m → lem (vh m))
  
  where
    lem : ∀ {A B X} → X ∈ᵀ (W₁ ⊛ sub q (η B)) → X ∈ᵀ (W₁ ⊛ sub q (U ⊛ η (A ⇒ B)))
    lem (left n) = left n
    lem (right n) = elim⊎ (λ n → right (∈sub₁ q n)) (λ { (at x) → right (∈sub₂ q (right (at (inj₂ x))))}) (sub∈ q n)
varcond _ U (⇒L ._ f f') eq | 2/\1 (disj q q₁ q₂ refl refl refl refl) with varcond (q ++ (q₁ ◂ _)) U f' refl
... | var vg vh =
  var
    (λ m → elim⊎ (λ n →
                    elim⊎ (λ m → inj₁ (∈sub₁ q m))
                          (λ { (left m) → inj₁ (∈sub₂ q (left m)) ;
                               (right m) → elim⊎ (λ m → inj₁ (∈sub₂ q (right (∈sub₁ q₂ m))))
                                              (λ { (at m) → inj₁ (∈sub₂ q (right (∈sub₂ q₂ (right (at (inj₂ m)))))) })
                                              (sub∈ q₂ m) })
                          (sub∈ q n))
                  inj₂
                  (vg m))
    vh

varcond _ U (⇒L _ f f') eq | 1/\2 (disj q q₁ q₂ refl refl refl refl) with varcond (q ++ (_ ▸ q₂)) _ f' refl
... | var vg vh =
  var
    (λ m → elim⊎ (λ m → elim⊎ (λ m → inj₁ (∈sub₁ q m))
                                (λ { (left m) → elim⊎ (λ m → inj₁ (∈sub₂ q (left (∈sub₁ q₁ m))))
                                                    (λ { (at m) → inj₁ (∈sub₂ q (left (∈sub₂ q₁ (right (at (inj₂ m)))))) } )
                                                    (sub∈ q₁ m) ;
                                     (right m) → inj₁ (∈sub₂ q (right m)) })
                                (sub∈ q m))
                  inj₂
                  (vg m))
    vh

varcond p _ (⇒L {U = U} .p f f') eq | 1≡2 (same refl refl refl) with varcond p _ f' refl
... | var vg vh =
  var
    vg
    (λ m → lem (vh m))

    where
      lem : ∀ {X A B} → X ∈ᵀ η B → X ∈ᵀ (U ⊛ η (A ⇒ B))
      lem (at x) = right (at (inj₂ x))
varcond _ U {C = C} (⇒L p' f f') eq | 2>L1 (gt q refl refl refl) with varcond q _ f refl
... | var vg vh =
  var
    (λ m → elim⊎ (λ m → inj₁ (∈sub₂ p' (left m)))
                  (λ m → inj₁ (∈sub₂ p' (right (at (inj₁ m)))))
                  (vg m))
    vh

varcond _ _ (⇒L p' f f') eq | 2>R1 (gt ∙ refl refl refl) with varcond ∙ _ f refl | varcond p' _ f' refl
... | var vg vh | var vl vk =
  var
    (λ { (inj₁ x) → inj₁ (∈sub₂ p' (left (vh x))) ;
         (inj₂ y) → elim⊎ (λ x → inj₁ (∈sub₁ p' x)) inj₂ (vl y) })
    (λ { (inj₁ x) → at (elim⊎ (λ ()) inj₁ (vg x)) ;
         (inj₂ y) → lem (vk y) })
    where
      lem : ∀ {X A B} → X ∈ᵀ η B → X ∈ᵀ η (A ⇒ B)
      lem (at x) = at (inj₂ x)
varcond p _ (⇐L p' f f') eq with subeq _ _ p' p eq
varcond p _ {C = C} (⇐L {U = U} _ f f') eq | 1>L2 (gt {W₂ = W₂} q refl refl refl) with varcond p _ f' refl
... | var vg vh =
  var
    vg
    (λ m → lem (vh m))

  where
    lem : ∀ {X A B} → X ∈ᵀ (sub q (η B) ⊛ W₂) → X ∈ᵀ (sub q (η (B ⇐ A) ⊛ U) ⊛ W₂)
    lem (left x) = elim⊎ (λ x → left (∈sub₁ q x)) (λ { (at x) → left (∈sub₂ q (left (at (inj₂ x)))) }) (sub∈ q x)
    lem (right x) = right x
varcond p _ (⇐L {U = U} _ f f') eq | 1>R2 (gt {W₁ = W₁} q refl refl refl) with varcond p _ f' refl
... | var vg vh =
  var
    vg
    (λ m → lem (vh m))

  where
    lem : ∀ {X A B} → X ∈ᵀ (W₁ ⊛ sub q (η B)) → X ∈ᵀ (W₁ ⊛ sub q (η (B ⇐ A) ⊛ U))
    lem (left x) = left x
    lem (right x) = elim⊎ (λ x → right (∈sub₁ q x)) (λ { (at x) → right (∈sub₂ q (left (at (inj₂ x)))) }) (sub∈ q x)
varcond p _ (⇐L {U = U} .p f f') eq | 1≡2 (same refl refl refl) with varcond p _ f' refl
... | var vg vh =
  var
    vg
    (λ x → lem (vh x))

    where
      lem : ∀ {X A B} → X ∈ᵀ η B → X ∈ᵀ (η (B ⇐ A) ⊛ U)
      lem (at x) = left (at (inj₂ x))
varcond _ _ (⇐L p' f f') eq | 2>L1 (gt ∙ refl refl refl) with varcond ∙ _ f refl | varcond p' _ f' refl
... | var vg vh | var vl vk =
  var
    (λ { (inj₁ x) → inj₁ (∈sub₂ p' (right (vh x))) ;
         (inj₂ y) → elim⊎ (λ x → inj₁ (∈sub₁ p' x)) inj₂ (vl y)})
    (λ { (inj₁ x) → elim⊎ (λ ()) (λ x → at (inj₁ x)) (vg x) ;
         (inj₂ y) → lem (vk y) })
    where
      lem : ∀ {X A B} → X ∈ᵀ η B → X ∈ᵀ η (B ⇐ A)
      lem (at x) = at (inj₂ x)
varcond _ _ (⇐L p' f f') eq | 2>R1 (gt q refl refl refl) with varcond q _ f refl
... | var vg vh =
  var
    (λ x → elim⊎ (λ x → inj₁ (∈sub₂ p' (right x))) (λ x → inj₁ (∈sub₂ p' (left (at (inj₁ x))))) (vg x))
    vh

varcond _ _ (⇐L _ f f') eq | 2/\1 (disj q q₁ q₂ refl refl refl refl) with varcond (q ++ (q₁ ◂ _)) _ f' refl
... | var vg vh =
  var
    (λ x → elim⊎ (λ x → elim⊎ (λ x → inj₁ (∈sub₁ q x))
                                (λ { (left x) → inj₁ (∈sub₂ q (left x)) ;
                                     (right x) → elim⊎ (λ x → inj₁ (∈sub₂ q (right (∈sub₁ q₂ x))))
                                                    (λ { (at x) → inj₁ (∈sub₂ q (right (∈sub₂ q₂ (left (at (inj₂ x))))))})
                                                    (sub∈ q₂ x) })
                                (sub∈ q x))
                  inj₂
                  (vg x))
    vh

varcond _ _ (⇐L _ f f') eq | 1/\2 (disj q q₁ q₂ refl refl refl refl) with varcond (q ++ (_ ▸ q₂)) _ f' refl
... | var vg vh =
  var
    (λ x → elim⊎ (λ x → elim⊎ (λ x → inj₁ (∈sub₁ q x))
                                (λ { (left x) → elim⊎ (λ x → inj₁ (∈sub₂ q (left (∈sub₁ q₁ x))))
                                                    (λ { (at x) → inj₁ (∈sub₂ q (left (∈sub₂ q₁ (left (at (inj₂ x)))))) })
                                                    (sub∈ q₁ x) ;
                                     (right x) → inj₁ (∈sub₂ q (right x)) })
                                (sub∈ q x))
                  inj₂
                  (vg x))
    vh

varcond p U (⊗L p' f) eq with subeq _ _ p' p eq
varcond p _ (⊗L .p f) eq | 1≡2 (same refl refl refl) with varcond p _ f refl
... | var vg vh =
  var
    vg
    (λ x → lem (vh x))

  where
    lem : ∀ {X A B} → X ∈ᵀ (η A ⊛ η B) → X ∈ᵀ η (A ⊗ B)
    lem (left (at x)) = at (inj₁ x)
    lem (right (at x)) = at (inj₂ x)
varcond p _ (⊗L _ f) eq | 1>L2 (gt {W₂ = W₂} q refl refl refl) with varcond p _ f refl
... | var vg vh =
  var
    vg
    (λ x → lem (vh x))

    where
      lem : ∀ {X A B} → X ∈ᵀ (sub q (η A ⊛ η B) ⊛ W₂) → X ∈ᵀ (sub q (η (A ⊗ B)) ⊛ W₂)
      lem (left m) = elim⊎ (λ m → left (∈sub₁ q m)) (λ { (left (at x)) → left (∈sub₂ q (at (inj₁ x))) ; (right (at x)) → left (∈sub₂ q (at (inj₂ x)))}) (sub∈ q m)
      lem (right m) = right m
varcond p _ (⊗L _ f) eq | 1>R2 (gt {W₁ = W₁} q refl refl refl) with varcond p _ f refl
... | var vg vh =
  var
    vg
    (λ x → lem (vh x))

    where
      lem : ∀ {X A B} → X ∈ᵀ (W₁ ⊛ sub q (η A ⊛ η B)) → X ∈ᵀ (W₁ ⊛ sub q (η (A ⊗ B)))
      lem (left x) = left x
      lem (right x) = right (elim⊎ (∈sub₁ q) (λ { (left (at x)) → ∈sub₂ q (at (inj₁ x)) ; (right (at x)) → ∈sub₂ q (at (inj₂ x))}) (sub∈ q x))
varcond _ U (⊗L _ f) eq | 1/\2 (disj q q₁ q₂ refl refl refl refl) with varcond (q ++ (_ ▸ q₂)) _ f refl
... | var vg vh =
  var
    (λ x → elim⊎ (λ x → inj₁ (elim⊎ (∈sub₁ q)
                                       (λ { (left x) → ∈sub₂ q (left (elim⊎ (∈sub₁ q₁)
                                                                       (λ { (left (at x)) → ∈sub₂ q₁ (at (inj₁ x)) ;
                                                                            (right (at x)) → ∈sub₂ q₁ (at (inj₂ x)) })
                                                                       (sub∈ q₁ x)))
                                          ; (right x) → ∈sub₂ q (right x) })
                                       (sub∈ q x)))
                  inj₂
                  (vg x))
    vh

varcond _ U (⊗L _ f) eq | 2/\1 (disj q q₁ q₂ refl refl refl refl) with varcond (q ++ (q₁ ◂ _)) _ f refl
... | var vg vh =
  var
    (λ x → elim⊎ (λ x → inj₁ (elim⊎ (∈sub₁ q)
                                      (λ { (left x) → ∈sub₂ q (left x) ;
                                           (right x) → ∈sub₂ q (right (elim⊎ (∈sub₁ q₂)
                                                                      (λ { (left (at x)) → ∈sub₂ q₂ (at (inj₁ x)) ;
                                                                           (right (at x)) → ∈sub₂ q₂ (at (inj₂ x)) })
                                                                      (sub∈ q₂ x))) })
                                      (sub∈ q x)))
                 inj₂
                 (vg x))
    vh

varcond ∙ _ (⊗R f f') refl with varcond ∙ _ f refl | varcond ∙ _ f' refl
... | var vg vh | var vl vk =
  var
    (λ { (inj₁ x) → elim⊎ (λ ()) (λ x → inj₂ (inj₁ x)) (vg x) ;
         (inj₂ y) → elim⊎ (λ ()) (λ x → inj₂ (inj₂ x)) (vl y)})
    (λ { (inj₁ x) → left (vh x) ;
         (inj₂ y) → right (vk y)})
varcond (p ◂ _) _ (⊗R f f') refl with varcond p _ f refl
... | var vg vh =
  var
    (λ x → elim⊎ (λ x → inj₁ (left x)) (λ x → inj₂ (inj₁ x)) (vg x))
    vh

varcond (_ ▸ p) _ (⊗R f f') refl with varcond p _ f' refl
... | var vg vh =
  var
    (λ x → elim⊎ (λ x → inj₁ (right x)) (λ x → inj₂ (inj₂ x)) (vg x))
    vh

varcond ∙ (η (at X)) ax refl = var inj₂ (λ m → at m) 




