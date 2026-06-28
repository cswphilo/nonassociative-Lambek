{-# OPTIONS --rewriting #-}

module Categorical.Universal where

open import Fma renaming (η to η')
open import Categorical.Free

-- The category defined in FCat is the free magmatic biclosed category.

-- the type of magmatic biclosed categories.
record MBiCCat : Set₁ where
  field
-- -- objects  
    Obj : Set
    ⊗₀ : Obj → Obj → Obj
    ⇒₀ : Obj → Obj → Obj
    ⇐₀ : Obj → Obj → Obj

-- -- morphisms
    Hom : Obj → Obj → Set
    Id : {B : Obj} → Hom B B
    Comp : {D B C : Obj} → Hom B C → Hom D B → Hom D C
    ⊗₁ : {E B C D : Obj} → Hom E B → Hom C D → Hom (⊗₀ E C) (⊗₀ B D)
    ⇒₁ : {A B C D : Obj} → Hom B A → Hom C D → Hom (⇒₀ A C) (⇒₀ B D)
    ⇐₁ : {A B C D : Obj} → Hom C D → Hom B A → Hom (⇐₀ C A) (⇐₀ D B)
    πR : {A B C : Obj} → Hom (⊗₀ A B) C → Hom B (⇒₀ A C)
    πR-1 : {A B C : Obj} → Hom B (⇒₀ A C) → Hom (⊗₀ A B) C
    -- εR : {A B : Obj} → Hom (⊗₀ A (⇒₀ A B)) B
    πL : {A B C : Obj} → Hom (⊗₀ A B) C → Hom A (⇐₀ C B)
    πL-1 : {A B C : Obj} → Hom A (⇐₀ C B) → Hom (⊗₀ A B) C
    -- εL : {A B : Obj} → Hom (⊗₀ (⇐₀ B A) A) B

-- -- equalities
-- -- the equality on morphisms is an equivalence relation
    Eq : {A B : Obj} → Hom A B → Hom A B → Set
    Refl : {C B : Obj} {f : Hom C B} → Eq f f
    Sym : {C B : Obj} {f g : Hom C B} → Eq f g → Eq g f
    Trans : {C B : Obj} {f g h : Hom C B} → Eq f g → Eq g h → Eq f h
-- -- congruence laws for composition, ⊗, ⇒, ⇐ πR, πL
    CompEq : {D B C : Obj} {f g : Hom B C} {h k : Hom D B} →
                           Eq f g → Eq h k → Eq (Comp f h) (Comp g k)
    ⊗₁Eq : {E B C D : Obj} {f g : Hom E C} {h k : Hom B D} →
                           Eq f g → Eq h k → Eq (⊗₁ f h) (⊗₁ g k)
    ⇒₁Eq : {A B C D : Obj} {f g : Hom A C} {h k : Hom B D} →
                           Eq f g → Eq h k → Eq (⇒₁ h f) (⇒₁ k g)
    ⇐₁Eq : {A B C D : Obj} {f g : Hom A C} {h k : Hom B D} →
                           Eq f g → Eq h k → Eq (⇐₁ f h) (⇐₁ g k)
    πREq : {A B C : Obj} {f g : Hom (⊗₀ A B) C} → Eq f g → Eq (πR f) (πR g)
    πR-1Eq : {A B C : Obj} {f g : Hom B (⇒₀ A C)} → Eq f g → Eq (πR-1 f) (πR-1 g)
    πLEq : {A B C : Obj} {f g : Hom (⊗₀ A B) C} → Eq f g → Eq (πL f) (πL g)
    πL-1Eq : {A B C : Obj} {f g : Hom A (⇐₀ C B)} → Eq f g → Eq (πL-1 f) (πL-1 g)
-- -- identity and associativity of composition
    Lid : {C B : Obj} {f : Hom C B} → Eq (Comp Id f) f
    Rid : {C B : Obj} {f : Hom C B} → Eq f (Comp f Id)
    Ass : {E B C D : Obj} {f : Hom C D} {g : Hom B C} {h : Hom E B}
         → Eq (Comp (Comp f g) h) (Comp f (Comp g h))
-- -- ⊗₁ functorial
    f⊗₁Id : {C B : Obj} → Eq (⊗₁ (Id {C}) (Id {B})) Id
    f⊗₁Comp : {G B C D E F : Obj} {f : Hom G C} {g : Hom B D} {h : Hom C E} {k : Hom D F} →  
                      Eq (⊗₁ (Comp h f) (Comp k g)) (Comp (⊗₁ h k) (⊗₁ f g))
-- -- ⇒₁ functorial 
    f⇒₁Id : {A B : Obj} → Eq (⇒₁ (Id {A}) (Id {B})) Id
    f⇒₁Comp : {A B C D E F : Obj} → {f : Hom A C} {g : Hom B D} {h : Hom C E} {k : Hom D F} → 
                          Eq (⇒₁ (Comp h f) (Comp k g)) (Comp (⇒₁ f k) (⇒₁ h g))
-- -- ⇐₁ functorial 
    f⇐₁Id : {A B : Obj} → Eq (⇐₁ (Id {B}) (Id {A})) Id
    f⇐₁Comp : {A B C D E F : Obj} → {f : Hom A C} {g : Hom B D} {h : Hom C E} {k : Hom D F} → 
                          Eq (⇐₁ (Comp k g) (Comp h f)) (Comp (⇐₁ k f) (⇐₁ g h))

-- -- adjunction
    πR-1πR : {A B C : Obj} {f : Hom (⊗₀ A B) C}
      → Eq (πR-1 (πR f)) f
    πRπR-1 : {A B C : Obj} {f : Hom B (⇒₀ A C)}
      → Eq (πR (πR-1 f)) f

    πL-1πL : {A B C : Obj} {f : Hom (⊗₀ A B) C}
      → Eq (πL-1 (πL f)) f
    πLπL-1 : {A B C : Obj} {f : Hom A (⇐₀ C B)}
      → Eq (πL (πL-1 f)) f
-- -- naturalities
    πRA : {A B A' : Obj} {f : Hom A' A}
      → Eq (πR (⊗₁ f (Id {B}))) (Comp (⇒₁ f Id) (πR Id))
    -- πRA : {A B C A' : Obj} {f : Hom (⊗₀ A B) C} {g : Hom A' A}
    --   → Eq (πR (Comp f (⊗₁ g Id))) (Comp (⇒₁ g Id) (πR f))
    πRB : {A B C B' : Obj} {f : Hom (⊗₀ A B) C} {g : Hom B' B}
      → Eq (Comp (πR f) g) (πR (Comp f (⊗₁ Id g))) 
    πRC : {A B C C' : Obj} {f : Hom C C'} {g : Hom (⊗₀ A B) C}
      → Eq (πR (Comp f g)) (Comp (⇒₁ Id f) (πR g))
    πLA : {A B C A' : Obj} {f : Hom (⊗₀ A B) C} {g : Hom A' A}
      → Eq (Comp (πL f) g) (πL (Comp f (⊗₁ g Id))) 
    πLB : {A B B' : Obj} {f : Hom B' B}
      → Eq (πL (⊗₁ (Id {A}) f)) (Comp (⇐₁ Id f) (πL Id))
    -- πLB : {A B C B' : Obj} {f : Hom (⊗₀ A B) C}{g : Hom B' B}
    --   → Eq (πL (Comp f (⊗₁ Id g))) (Comp (⇐₁ Id g) (πL f))
    πLC : {A B C C' : Obj} {f : Hom C C'} {g : Hom (⊗₀ A B) C}
      → Eq (πL (Comp f g)) (Comp (⇐₁ f Id) (πL g))
  Id⇒swap : {A B C D : Obj} {f : Hom A B} {g : Hom C D}
      → Eq (Comp (⇒₁ Id f) (⇒₁ g Id)) (Comp (⇒₁ g Id) (⇒₁ Id f))
  Id⇒swap = Trans (Sym f⇒₁Comp) (Trans (⇒₁Eq (Sym (Trans Lid Rid)) (Sym (Trans Lid Rid))) f⇒₁Comp)
  πRANat : {A B C A' : Obj} {f : Hom (⊗₀ A B) C} {g : Hom A' A}
      → Eq (πR (Comp f (⊗₁ g Id))) (Comp (⇒₁ g Id) (πR f))
  πRANat = Trans πRC (Trans (CompEq Refl πRA) (Trans (Sym Ass) (Trans (CompEq Id⇒swap Refl) (Trans Ass (Trans (CompEq Refl (Sym πRC)) (CompEq Refl (πREq (Sym Rid))))))))
  Id⇐swap : {A B C D : Obj} {f : Hom A B} {g : Hom C D}
      → Eq (Comp (⇐₁ f Id) (⇐₁ Id g)) (Comp (⇐₁ Id g) (⇐₁ f Id))
  Id⇐swap = Trans (Sym f⇐₁Comp) (Trans (⇐₁Eq (Sym (Trans Lid Rid)) (Sym (Trans Lid Rid))) f⇐₁Comp)
  πLBNat : {A B C B' : Obj} {f : Hom (⊗₀ A B) C}{g : Hom B' B}
      → Eq (πL (Comp f (⊗₁ Id g))) (Comp (⇐₁ Id g) (πL f))
  πLBNat = Trans πLC (Trans (CompEq Refl πLB) (Trans (Sym Ass) (Trans (CompEq Id⇐swap Refl) (Trans Ass (Trans (CompEq Refl (Sym πLC)) (CompEq Refl (πLEq (Sym Rid))))))))
  πR-1A : {A A' B C : Obj} {f : Hom B (⇒₀ A C)} {g : Hom A' A}
      → Eq (πR-1 (Comp (⇒₁ g Id) f)) (Comp (πR-1 f) (⊗₁ g Id))
  πR-1A = Trans (πR-1Eq (Trans (CompEq Refl (Sym πRπR-1)) (Sym πRANat))) πR-1πR   
  πR-1B : {A B B' C : Obj} {f : Hom B (⇒₀ A C)} {g : Hom B' B}
      → Eq (Comp (πR-1 f) (⊗₁ Id g)) (πR-1 (Comp f g))
  πR-1B = Trans (Sym πR-1πR) (πR-1Eq (Trans (Sym πRB) (CompEq πRπR-1 Refl)))
  πR-1C : {A B C C' : Obj} {f : Hom C C'} {g : Hom B (⇒₀ A C)}
      → Eq (Comp f (πR-1 g )) (πR-1 (Comp (⇒₁ Id f) g))
  πR-1C = Trans (Sym πR-1πR) (πR-1Eq (Trans πRC (CompEq Refl πRπR-1)))
  πL-1A : {A A' B C : Obj} {f : Hom A (⇐₀ C B)} {g : Hom A' A}
      → Eq (Comp (πL-1 f) (⊗₁ g Id)) (πL-1 (Comp f g))
  πL-1A = Trans (Sym πL-1πL) (πL-1Eq (Trans (Sym πLA) (CompEq πLπL-1 Refl)))
  πL-1B : {A B B' C : Obj} {f : Hom A (⇐₀ C B)} {g : Hom B' B}
      → Eq (πL-1 (Comp (⇐₁ Id g) f)) (Comp (πL-1 f) (⊗₁ Id g))
  πL-1B = Trans (πL-1Eq (Trans (CompEq Refl (Sym πLπL-1)) (Sym πLBNat))) πL-1πL
  πL-1C : {A B C C' : Obj} {f : Hom C C'} {g : Hom A (⇐₀ C B)}
      → Eq (Comp f (πL-1 g )) (πL-1 (Comp (⇐₁ f Id) g))
  πL-1C = Trans (Sym πL-1πL) (πL-1Eq (Trans πLC (CompEq Refl πLπL-1)))

-- =======================================================================


-- -- the type of (strong) magmatic biclosed functors.

record MBiCFun (ℂ 𝔻 : MBiCCat) : Set₁ where
  open MBiCCat
  field
-- -- action on objects, morphisms and equalities  
    F₀ : Obj ℂ → Obj 𝔻
    F₁ : ∀{B C} → Hom ℂ B C → Hom 𝔻 (F₀ B) (F₀ C)
    FEq : ∀{B C} {f g : Hom ℂ B C} → Eq ℂ f g → Eq 𝔻 (F₁ f) (F₁ g)

-- -- functor laws    
    FId : ∀{B} → Eq 𝔻 (F₁ (Id ℂ {B})) (Id 𝔻)
    FComp : ∀{B C D} {g : Hom ℂ C D} {f : Hom ℂ B C} →
           Eq 𝔻 (F₁ (Comp ℂ g f)) (Comp 𝔻 (F₁ g) (F₁ f))
-- -- biclosed functor data and laws         
    m : ∀{B C} → Hom 𝔻 (⊗₀ 𝔻 (F₀ B) (F₀ C)) (F₀ (⊗₀ ℂ B C))
    m-1 : ∀{B C} → Hom 𝔻 (F₀ (⊗₀ ℂ B C)) (⊗₀ 𝔻 (F₀ B) (F₀ C))
    r : ∀ {B C} → Hom 𝔻 (F₀ (⇒₀ ℂ B C)) (⇒₀ 𝔻 (F₀ B) (F₀ C))
    r-1 : ∀ {B C} → Hom 𝔻 (⇒₀ 𝔻 (F₀ B) (F₀ C)) (F₀ (⇒₀ ℂ B C)) 
    l : ∀ {B C} → Hom 𝔻 (F₀ (⇐₀ ℂ C B)) (⇐₀ 𝔻 (F₀ C) (F₀ B))
    l-1 : ∀ {B C} → Hom 𝔻 (⇐₀ 𝔻 (F₀ C) (F₀ B)) (F₀ (⇐₀ ℂ C B)) 
    nm : ∀ {B C D E} {f : Hom ℂ B D} {g : Hom ℂ C E}
        → Eq 𝔻 (Comp 𝔻 m (⊗₁ 𝔻 (F₁ f) (F₁ g))) (Comp 𝔻 (F₁ (⊗₁ ℂ f g)) m)
    nm-1 : ∀ {B C D E} {f : Hom ℂ B D} {g : Hom ℂ C E}
        → Eq 𝔻 (Comp 𝔻 m-1 (F₁ (⊗₁ ℂ f g))) (Comp 𝔻 (⊗₁ 𝔻  (F₁ f) (F₁ g)) m-1)
    nr : ∀ {B C D E} {f : Hom ℂ B D} {g : Hom ℂ C E}
        → Eq 𝔻 (Comp 𝔻 r (F₁ (⇒₁ ℂ f g))) (Comp 𝔻 (⇒₁ 𝔻 (F₁ f) (F₁ g)) r)
    nr-1 : ∀ {B C D E} {f : Hom ℂ B D} {g : Hom ℂ C E}
        → Eq 𝔻 (Comp 𝔻 (F₁ (⇒₁ ℂ f g)) r-1) (Comp 𝔻 r-1 (⇒₁ 𝔻 (F₁ f) (F₁ g)))
    nl : ∀ {B C D E} {f : Hom ℂ B D} {g : Hom ℂ C E}
        → Eq 𝔻 (Comp 𝔻 l (F₁ (⇐₁ ℂ g f))) (Comp 𝔻 (⇐₁ 𝔻 (F₁ g) (F₁ f)) l)
    nl-1 : ∀ {B C D E} {f : Hom ℂ B D} {g : Hom ℂ C E}
        → Eq 𝔻 (Comp 𝔻 (F₁ (⇐₁ ℂ g f)) l-1) (Comp 𝔻 l-1 (⇐₁ 𝔻 (F₁ g) (F₁ f)))
    miso₁ : ∀{B C} → Eq 𝔻 (Comp 𝔻 m m-1) (Id 𝔻 {F₀ (⊗₀ ℂ B C)})
    miso₂ : ∀{B C} → Eq 𝔻 (Comp 𝔻 m-1 m) (Id 𝔻 {⊗₀ 𝔻 (F₀ B) (F₀ C)})
    r-1iso₁ : ∀ {B C} → Eq 𝔻 (Comp 𝔻 r r-1) (Id 𝔻 {⇒₀ 𝔻 (F₀ B) (F₀ C)})
    r-1iso₂ : ∀ {B C} → Eq 𝔻 (Comp 𝔻 r-1 r) (Id 𝔻 {F₀ (⇒₀ ℂ B C)})
    l-1iso₁ : ∀ {B C} → Eq 𝔻 (Comp 𝔻 l l-1) (Id 𝔻 {⇐₀ 𝔻 (F₀ C) (F₀ B)})
    l-1iso₂ : ∀ {B C} → Eq 𝔻 (Comp 𝔻 l-1 l) (Id 𝔻 {F₀ (⇐₀ ℂ C B)})
-- -- preserving adjunction
    pR : ∀ {A B C} → {f : Hom ℂ (⊗₀ ℂ A B) C}
        → Eq 𝔻 (Comp 𝔻 r (F₁ (πR ℂ f))) (πR 𝔻 (Comp 𝔻 (F₁ f) m))
        -- → Eq 𝔻 (F₁ (πR ℂ f)) (Comp 𝔻 r-1 (πR 𝔻 (Comp 𝔻 (F₁ f) m)))
    pR-1 : ∀ {A B C} → {f : Hom ℂ B (⇒₀ ℂ A C)}
        → Eq 𝔻 (Comp 𝔻 (F₁ (πR-1 ℂ f)) m) (πR-1 𝔻 (Comp 𝔻 r (F₁ f)))
        -- → Eq 𝔻 (F₁ (πR-1 ℂ f)) (Comp 𝔻 (πR-1 𝔻 (Comp 𝔻 r (F₁ f))) m-1)
    pL : ∀ {A B C} → {f : Hom ℂ (⊗₀ ℂ A B) C}
      → Eq 𝔻 (Comp 𝔻 l (F₁ (πL ℂ f))) (πL 𝔻 (Comp 𝔻 (F₁ f) m))
      -- → Eq 𝔻 (F₁ (πL ℂ f)) (Comp 𝔻 l-1 (πL 𝔻 (Comp 𝔻 (F₁ f) m)))
    pL-1 : ∀ {A B C} → {f : Hom ℂ A (⇐₀ ℂ C B)}
        → Eq 𝔻 (Comp 𝔻 (F₁ (πL-1 ℂ f)) m) (πL-1 𝔻 (Comp 𝔻 l (F₁ f)))
        -- → Eq 𝔻 (F₁ (πL-1 ℂ f)) (Comp 𝔻 (πL-1 𝔻 (Comp 𝔻 l (F₁ f))) m-1)

-- -- =======================================================================

-- equality of magmatic biclosed functors.
-- -- two magmatic biclosed functors are "equal" if there exists 
-- -- a monoidal closed natural isomorphism between them.

record MBiCFunEq {ℂ 𝔻 : MBiCCat} (F G : MBiCFun ℂ 𝔻) : Set where
  open MBiCCat
  open MBiCFun
  field
    t : ∀ B → Hom 𝔻 (F₀ G B) (F₀ F B)
    t-1 : ∀ B → Hom 𝔻 (F₀ F B) (F₀ G B)
    nt : ∀{B C} (f : Hom ℂ B C) → Eq 𝔻 (Comp 𝔻 (t C) (F₁ G f)) (Comp 𝔻 (F₁ F f) (t B))
    tiso₁ : ∀{B} → Eq 𝔻 (Comp 𝔻 (t B) (t-1 B)) (Id 𝔻)
    tiso₂ : ∀{B} → Eq 𝔻 (Comp 𝔻 (t-1 B) (t B)) (Id 𝔻)
    -- et : Eq 𝔻 (Comp 𝔻 (t (𝕀 ℂ)) (e G)) (e F)
    mt : ∀{B C} → Eq 𝔻 (Comp 𝔻 (t (⊗₀ ℂ B C)) (m G)) (Comp 𝔻 (m F) (⊗₁ 𝔻 (t B) (t C)))
    rt : ∀{B C} → Eq 𝔻 (Comp 𝔻 (⇒₁ 𝔻 (t-1 B) (t C)) (r G)) (Comp 𝔻 (r F) (t (⇒₀ ℂ B C))) -- see nLab
    r-1t : ∀{B C} → Eq 𝔻 (Comp 𝔻 (r-1 F) (⇒₁ 𝔻 (t-1 B) (t C))) (Comp 𝔻 (t (⇒₀ ℂ B C)) (r-1 G)) -- probably can be removed
    lt : ∀{B C} → Eq 𝔻 (Comp 𝔻 (⇐₁ 𝔻 (t C) (t-1 B)) (l G)) (Comp 𝔻 (l F) (t (⇐₀ ℂ C B)))
    l-1t : ∀{B C} → Eq 𝔻 (Comp 𝔻 (l-1 F) (⇐₁ 𝔻 (t C) (t-1 B))) (Comp 𝔻 (t (⇐₀ ℂ C B)) (l-1 G)) -- probably can be removed

record IsStrict {ℂ 𝔻 : MBiCCat} (F : MBiCFun ℂ 𝔻) : Set where
  open MBiCCat
  open MBiCFun F
  field
    mEq : ∀{B C} → (⊗₀ 𝔻 (F₀ B) (F₀ C)) ≡ (F₀ (⊗₀ ℂ B C))
    mId : ∀ {B C} → Eq 𝔻 m (subst (λ x → Hom 𝔻 (⊗₀ 𝔻 (F₀ B) (F₀ C)) x) mEq (Id 𝔻))
    m-1Id : ∀ {B C} → Eq 𝔻 (subst (λ x → Hom 𝔻 x (⊗₀ 𝔻 (F₀ B) (F₀ C))) mEq (Id 𝔻)) m-1
    -- Eq 𝔻 (subst (λ x → Hom 𝔻 (⊗₀ 𝔻 (F₀ B) (F₀ C)) x) (sym mEq) m) (Id 𝔻)
    rEq : ∀ {B C} → (F₀ (⇒₀ ℂ B C)) ≡ (⇒₀ 𝔻 (F₀ B) (F₀ C))
    rId : ∀ {B C} → Eq 𝔻 r (subst (λ x → Hom 𝔻 x (⇒₀ 𝔻 (F₀ B) (F₀ C))) (sym rEq) (Id 𝔻))
    r-1Id : ∀ {B C} → Eq 𝔻 r-1 (subst (λ x → Hom 𝔻 (⇒₀ 𝔻 (F₀ B) (F₀ C)) x) (sym rEq) (Id 𝔻))
    lEq : ∀ {B C} → (F₀ (⇐₀ ℂ C B)) ≡ (⇐₀ 𝔻 (F₀ C) (F₀ B))
    lId : ∀ {B C} → Eq 𝔻 l (subst (λ x → Hom 𝔻 x (⇐₀ 𝔻 (F₀ C) (F₀ B))) (sym lEq) (Id 𝔻))
    l-1Id : ∀ {B C} → Eq 𝔻 l-1 (subst (λ x → Hom 𝔻 (⇐₀ 𝔻 (F₀ C) (F₀ B)) x) (sym lEq) (Id 𝔻))
record IsStrictEq {ℂ 𝔻 : MBiCCat} {F G : MBiCFun ℂ 𝔻} (FGEq : MBiCFunEq F G) : Set where
  open MBiCCat
  open MBiCFun
  -- open IsStrict
  open MBiCFunEq FGEq
  field
   tEq : ∀ B → F₀ G B ≡ F₀ F B 
   tId : ∀ B → Eq 𝔻 (t B) (subst (λ x → Hom 𝔻 (F₀ G B) x) (tEq B) (Id 𝔻))
    
-- -- =======================================================================

-- -- the predicate expressing the universal property.
-- -- -- a magmatic biclosed category satisfies it iff it is the free magmatic
-- -- -- biclosed category on the set At.

record FreeMBiCCat (ℂ : MBiCCat) : Set₁ where
  open MBiCCat
  open MBiCFun
  field
    η : At → Obj ℂ
    F : ∀ 𝔻 (γ : At → Obj 𝔻) → MBiCFun ℂ 𝔻
    comm : ∀ 𝔻 γ {X : At} → F₀ (F 𝔻 γ) (η X) ≡ γ X
    univ : ∀ 𝔻 γ (G : MBiCFun ℂ 𝔻) →
      ({X : At} → F₀ G (η X) ≡ γ X) → MBiCFunEq G (F 𝔻 γ)

-- -- =======================================================================

-- -- FMBiCC(At) is a magmatic biclosed category.

FMBiCC : MBiCCat
FMBiCC = record
  { Obj = Fma
  ; ⊗₀ = _⊗_
  ; ⇒₀ = _⇒_
  ; ⇐₀ = _⇐_
  ; Hom = _⟶_
  ; Id = id
  ; Comp = _∘_
  ; ⊗₁ = _⊗_
  ; ⇒₁ = _⇒_
  ; ⇐₁ = _⇐_
  ; πR = π⇒
  ; πR-1 = π⇒-1
  ; πL = π⇐
  ; πL-1 = π⇐-1
  ; Eq = _≐_
  ; Refl = refl
  ; Sym = ~_
  ; Trans = _．_
  ; CompEq = _∘_
  ; ⊗₁Eq = _⊗_
  ; ⇒₁Eq = _⇒_
  ; ⇐₁Eq = _⇐_
  ; πREq = π⇒
  ; πR-1Eq = π⇒-1
  ; πLEq = π⇐
  ; πL-1Eq = π⇐-1
  ; Lid = lid
  ; Rid = rid
  ; Ass = ass
  ; f⊗₁Id = f⊗id
  ; f⊗₁Comp = f⊗∘
  ; f⇒₁Id = f⇒id
  ; f⇒₁Comp = f⇒∘
  ; f⇐₁Id = f⇐id
  ; f⇐₁Comp = f⇐∘
  ; πR-1πR = π⇒π⇒-1
  ; πRπR-1 = π⇒-1π⇒
  ; πL-1πL = π⇐π⇐-1
  ; πLπL-1 = π⇐-1π⇐
  ; πRA = π⇒A
  ; πRB = π⇒B
  ; πRC = π⇒C
  -- ; πR-1A = π⇒-1A
  -- ; πR-1B = π⇒-1B
  -- ; πR-1C = π⇒-1C
  ; πLA = π⇐A
  ; πLB = π⇐B
  ; πLC = π⇐C
  -- ; πL-1A = π⇐-1A
  -- ; πL-1B = π⇐-1B
  -- ; πL-1C = π⇐-1C
  }

-- -- =======================================================================

-- -- there exists a monoidal functor between Fsk(At) and any other skew
-- -- monoidal category 𝔻 which comes with a set function γ : At →
-- -- MBiCCat.Obj 𝔻.

module Exists (𝔻 : MBiCCat) (γ : At → MBiCCat.Obj 𝔻) where

  open MBiCCat 𝔻

  𝔽₀ : Fma → Obj
  𝔽₀ (at X) = γ X
  𝔽₀ (B ⊗ C) = ⊗₀ (𝔽₀ B) (𝔽₀ C)
  𝔽₀ (B ⇒ C) = ⇒₀ (𝔽₀ B) (𝔽₀ C)
  𝔽₀ (C ⇐ B) = ⇐₀ (𝔽₀ C) (𝔽₀ B)

  𝔽₁ : {B C : Fma} → B ⟶ C → Hom (𝔽₀ B) (𝔽₀ C)
  𝔽₁ id = Id
  𝔽₁ (f ∘ f₁) = Comp (𝔽₁ f) (𝔽₁ f₁)
  𝔽₁ (f ⊗ f₁) = ⊗₁ (𝔽₁ f) (𝔽₁ f₁)
  𝔽₁ (f ⇒ f₁) = ⇒₁ (𝔽₁ f) (𝔽₁ f₁)
  𝔽₁ (f ⇐ f₁) = ⇐₁ (𝔽₁ f) (𝔽₁ f₁)
  𝔽₁ (π⇒ f) = πR (𝔽₁ f)
  𝔽₁ (π⇒-1 f) = πR-1 (𝔽₁ f)
  𝔽₁ (π⇐ f) = πL (𝔽₁ f)
  𝔽₁ (π⇐-1 f) = πL-1 (𝔽₁ f)

  𝔽Eq : {B C : Fma} {f g : B ⟶ C} →
        f ≐ g → Eq (𝔽₁ f) (𝔽₁ g)
  𝔽Eq refl = Refl
  𝔽Eq (~ eq) = Sym (𝔽Eq eq)
  𝔽Eq (eq ． eq₁) = Trans (𝔽Eq eq) (𝔽Eq eq₁)
  𝔽Eq (eq ∘ eq₁) = CompEq (𝔽Eq eq) (𝔽Eq eq₁)
  𝔽Eq (eq ⊗ eq₁) = ⊗₁Eq (𝔽Eq eq) (𝔽Eq eq₁)
  𝔽Eq (eq ⇒ eq₁) = ⇒₁Eq (𝔽Eq eq) (𝔽Eq eq₁)
  𝔽Eq (eq ⇐ eq₁) = ⇐₁Eq (𝔽Eq eq) (𝔽Eq eq₁)
  𝔽Eq (π⇐ eq) = πLEq (𝔽Eq eq)
  𝔽Eq (π⇐-1 eq) = πL-1Eq (𝔽Eq eq)
  𝔽Eq (π⇒ eq) = πREq (𝔽Eq eq)
  𝔽Eq (π⇒-1 eq) = πR-1Eq (𝔽Eq eq)
  𝔽Eq lid = Lid
  𝔽Eq rid = Rid
  𝔽Eq ass = Ass
  𝔽Eq f⊗id = f⊗₁Id
  𝔽Eq f⊗∘ = f⊗₁Comp
  𝔽Eq f⇒id = f⇒₁Id
  𝔽Eq f⇒∘ = f⇒₁Comp
  𝔽Eq f⇐id = f⇐₁Id
  𝔽Eq f⇐∘ = f⇐₁Comp
  𝔽Eq π⇒A = πRA
  𝔽Eq π⇒B = πRB
  𝔽Eq π⇒C = πRC
  𝔽Eq π⇒π⇒-1 = πR-1πR
  𝔽Eq π⇒-1π⇒ = πRπR-1
  𝔽Eq π⇐A = πLA
  𝔽Eq π⇐B = πLB
  𝔽Eq π⇐C = πLC
  𝔽Eq π⇐π⇐-1 = πL-1πL
  𝔽Eq π⇐-1π⇐ = πLπL-1

  𝔽 : MBiCFun FMBiCC 𝔻
  𝔽 = record
    { F₀ = 𝔽₀
    ; F₁ = 𝔽₁
    ; FEq = 𝔽Eq
    ; FId = Refl
    ; FComp = Refl
    ; m = Id
    ; m-1 = Id
    ; r = Id
    ; r-1 = Id
    ; l = Id
    ; l-1 = Id
    ; nm = Trans Lid Rid
    ; nm-1 = Trans Lid Rid
    ; nr = Trans Lid Rid
    ; nr-1 = Trans (Sym Rid) (Sym Lid)
    ; nl = Trans Lid Rid
    ; nl-1 = Trans (Sym Rid) (Sym Lid)
    ; miso₁ = Trans Lid Refl
    ; miso₂ = Trans Refl Lid
    ; r-1iso₁ = Lid
    ; r-1iso₂ = Lid
    ; l-1iso₁ = Lid
    ; l-1iso₂ = Lid
    ; pR = Trans Lid (πREq Rid) 
    ; pR-1 = Sym (Trans (πR-1Eq Lid) Rid)
    ; pL = Trans Lid (πLEq Rid)
    ; pL-1 = Sym (Trans (πL-1Eq Lid) Rid)
    }
  𝔽IsStrict : IsStrict 𝔽 
  𝔽IsStrict = record
    { mEq = refl
    ; mId = Refl
    ; m-1Id = Refl
    ; rEq = refl
    ; rId = Refl
    ; r-1Id = Refl
    ; lEq = refl
    ; lId = Refl
    ; l-1Id = Refl
    } 
-- -- =======================================================================

-- -- the monoidal functor constructed above is unique among those making
-- -- the formed triangle commmute.

module Unique (𝔻 : MBiCCat)
              (γ : At → MBiCCat.Obj 𝔻)
              (G : MBiCFun FMBiCC 𝔻)
              (p : {X : At} → MBiCFun.F₀ G (at X) ≡ γ X)
              where

  open MBiCCat 𝔻
  open MBiCFun G
  open Exists 𝔻 γ

  𝕥 : (B : Fma) → Hom (𝔽₀ B) (F₀ B)

  𝕥-1 : (B : Fma) → Hom (F₀ B) (𝔽₀ B)

  𝕥 (at X) = subst (Hom _) (sym p) Id
  𝕥 (B ⇒ C) = Comp r-1 (⇒₁ (𝕥-1 B) (𝕥 C))
  𝕥 (C ⇐ B) = Comp l-1 (⇐₁ (𝕥 C) (𝕥-1 B))
  𝕥 (B ⊗ C) = Comp m (⊗₁ (𝕥 B) (𝕥 C))

  𝕥-1 (at X) = subst (Hom _) p Id
  𝕥-1 (B ⇒ C) = Comp (⇒₁ (𝕥 B) (𝕥-1 C)) r
  𝕥-1 (C ⇐ B) = Comp (⇐₁ (𝕥-1 C) (𝕥 B)) l
  𝕥-1 (B ⊗ C) = Comp (⊗₁ (𝕥-1 B) (𝕥-1 C)) m-1

  𝕥iso₁ : {B : Fma} → Eq (Comp (𝕥 B) (𝕥-1 B)) Id
  𝕥iso₁ {at X} = lem p
    where
      lem : ∀{Y Z} (r : Z ≡ Y) → Eq (Comp (subst (Hom Y) (sym r) Id) (subst (Hom Z) r Id)) Id
      lem refl = Lid  
  𝕥iso₁ {B ⇒ C} = Trans Ass (Trans (CompEq Refl (Sym Ass)) (Trans (CompEq Refl (CompEq (Sym f⇒₁Comp) Refl)) (Trans (CompEq Refl (CompEq (⇒₁Eq 𝕥iso₁ 𝕥iso₁) Refl)) (Trans (CompEq Refl (CompEq f⇒₁Id Refl)) (Trans (CompEq Refl Lid) r-1iso₂)))))
  𝕥iso₁ {C ⇐ B} = Trans Ass (Trans (CompEq Refl (Sym Ass)) (Trans (CompEq Refl (CompEq (Sym f⇐₁Comp) Refl)) (Trans (CompEq Refl (CompEq (⇐₁Eq 𝕥iso₁ 𝕥iso₁) Refl)) (Trans (CompEq Refl (CompEq f⇐₁Id Refl)) (Trans (CompEq Refl Lid) l-1iso₂)))))
  𝕥iso₁ {B ⊗ C} = Trans (Trans Ass (CompEq Refl (Trans (Sym Ass) (CompEq (Trans (Sym f⊗₁Comp) (⊗₁Eq 𝕥iso₁ 𝕥iso₁)) Refl))))
   (Trans (CompEq Refl (CompEq f⊗₁Id Refl))
   (Trans (CompEq Refl Lid) miso₁))
  
  𝕥iso₂ : {B : Fma} → Eq (Comp (𝕥-1 B) (𝕥 B)) Id
  𝕥iso₂ {at X} = lem p
    where
      lem : ∀{Y Z} (r : Z ≡ Y) → Eq (Comp (subst (Hom Z) r Id) (subst (Hom Y) (sym r) Id)) Id
      lem refl = Lid 
  𝕥iso₂ {B ⇒ C} = Trans Ass (Trans (CompEq Refl (Trans (Trans (Sym Ass) (CompEq r-1iso₁ Refl)) Lid)) (Trans (Sym f⇒₁Comp) (Trans (⇒₁Eq 𝕥iso₂ 𝕥iso₂) f⇒₁Id)))
  𝕥iso₂ {C ⇐ B} = Trans Ass (Trans (CompEq Refl (Trans (Trans (Sym Ass) (CompEq l-1iso₁ Refl)) Lid)) (Trans (Sym f⇐₁Comp) (Trans (⇐₁Eq 𝕥iso₂ 𝕥iso₂) f⇐₁Id)))
  𝕥iso₂ {B ⊗ C} = Trans (Trans Ass (Trans (CompEq Refl (Trans (Sym Ass) (Trans (CompEq miso₂ Refl) Lid))) (Trans (Sym f⊗₁Comp) (⊗₁Eq 𝕥iso₂ 𝕥iso₂)))) f⊗₁Id

  n𝕥 : {B C : Fma} (f : B ⟶ C) →
         Eq (Comp (𝕥 C) (𝔽₁ f)) (Comp (F₁ f) (𝕥 B))
  n𝕥-1 : {B C : Fma} (f : B ⟶ C) →
         Eq (Comp (𝕥-1 C) (F₁ f)) (Comp (𝔽₁ f) (𝕥-1 B))
  n𝕥 id = Trans (Sym Rid) (Trans (Sym Lid) (CompEq (Sym FId) Refl))

  n𝕥 (f ∘ g) = Trans (Trans (Sym Ass) (CompEq (n𝕥 f) Refl)) (Trans Ass (Trans (Trans (CompEq Refl (n𝕥 g)) (Sym Ass)) (CompEq (Sym FComp) Refl)))

  n𝕥 (f ⊗ g) = 
    Trans Ass 
      (Trans (CompEq Refl (Trans (Sym f⊗₁Comp) ((⊗₁Eq (n𝕥 f) (n𝕥 g))))) 
      (Trans (Trans (Trans (CompEq Refl f⊗₁Comp) (Sym Ass)) (CompEq nm Refl)) Ass))

  n𝕥 (f ⇒ g) = 
    Trans (Trans 
      (Trans Ass 
      (Trans (CompEq Refl (Trans (Sym f⇒₁Comp) (Trans (⇒₁Eq (n𝕥 g) (Sym (n𝕥-1 f))) f⇒₁Comp))) 
             (Sym Ass))) (CompEq (Sym nr-1) Refl)) Ass

  n𝕥 (g ⇐ f) = 
    Trans (Trans 
      (Trans Ass 
      (Trans (CompEq Refl (Trans (Sym f⇐₁Comp) (Trans (⇐₁Eq (n𝕥 g) (Sym (n𝕥-1 f))) f⇐₁Comp))) 
             (Sym Ass))) (CompEq (Sym nl-1) Refl)) Ass

  n𝕥 (π⇒ f) = 
    Trans 
      (Trans Ass 
        (Trans (CompEq Refl (Trans (CompEq (⇒₁Eq (Sym Lid) (Sym Lid)) Refl) (Trans (CompEq f⇒₁Comp Refl) (Trans Ass (Trans (CompEq Refl (Trans (Sym πRC) (πREq (n𝕥 f)))) (Trans (Sym πRANat) (Trans (πREq (Trans Ass (CompEq Refl (Trans Ass (CompEq Refl (Trans (Sym f⊗₁Comp) (⊗₁Eq 𝕥iso₁ (Sym Rid)))))))) (Trans (πREq (Sym Ass)) (Sym πRB))))))))) (Sym Ass))) 
      (CompEq (Sym (Trans (Trans (Trans (Sym Lid) (CompEq (Sym r-1iso₂) Refl)) Ass) (CompEq Refl pR))) Refl)

  n𝕥 (π⇒-1 f) = 
    Trans 
      (Trans (Trans (Trans (Trans (Trans (Trans (Trans (Trans (Trans (Trans πR-1C (πR-1Eq (Trans (CompEq (Trans (⇒₁Eq (Sym Lid) (Sym 𝕥iso₂)) f⇒₁Comp) Refl) Ass))) πR-1A) (CompEq (πR-1Eq (Trans (CompEq (Trans (Sym Lid) (CompEq (Sym r-1iso₁) Refl)) Refl) (Trans (CompEq Ass Refl) Ass))) Refl)) (CompEq (Trans (πR-1Eq (CompEq Refl (n𝕥 f))) (πR-1Eq (Sym Ass))) Refl)) (CompEq (Sym πR-1B) Refl)) Ass) (CompEq Refl (Trans (Sym f⊗₁Comp) (⊗₁Eq Lid (Sym Rid))))) (CompEq Refl (Trans (Sym Lid) (CompEq (Sym miso₂) Refl)))) (CompEq Refl (Ass))) (Sym Ass)) 
    (CompEq (Sym (Trans (Trans Rid (Trans (CompEq Refl (Sym miso₁)) (Sym Ass))) (CompEq pR-1 Refl))) Refl)

  n𝕥 (π⇐ f) = 
    Trans 
      (Trans Ass 
        (Trans (CompEq Refl (Trans (CompEq (⇐₁Eq (Sym Lid) (Sym Lid)) Refl) (Trans (CompEq f⇐₁Comp Refl) (Trans Ass (Trans (CompEq Refl (Trans (Sym πLC) (πLEq (n𝕥 f)))) (Trans (Sym πLBNat) (Trans (πLEq (Trans Ass (CompEq Refl (Trans Ass (CompEq Refl (Trans (Sym f⊗₁Comp) (⊗₁Eq (Sym Rid) 𝕥iso₁))))))) (Trans (πLEq (Sym Ass)) (Sym πLA))))))))) (Sym Ass))) 
      (CompEq (Sym (Trans (Trans (Trans (Sym Lid) (CompEq (Sym l-1iso₂) Refl)) Ass) (CompEq Refl pL))) Refl)

  n𝕥 (π⇐-1 f) = 
    Trans 
      (Trans (Trans (Trans (Trans (Trans (Trans (Trans (Trans (Trans (Trans πL-1C (πL-1Eq (Trans (CompEq (Trans (⇐₁Eq (Sym Lid) (Sym 𝕥iso₂)) f⇐₁Comp) Refl) Ass))) πL-1B) (CompEq (πL-1Eq (Trans (CompEq (Trans (Sym Lid) (CompEq (Sym l-1iso₁) Refl)) Refl) (Trans (CompEq Ass Refl) Ass))) Refl)) (CompEq (Trans (πL-1Eq (CompEq Refl (n𝕥 f))) (πL-1Eq (Sym Ass))) Refl)) (CompEq (Sym πL-1A) Refl)) Ass) (CompEq Refl (Trans (Sym f⊗₁Comp) (⊗₁Eq (Sym Rid) Lid)))) (CompEq Refl (Trans (Sym Lid) (CompEq (Sym miso₂) Refl)))) (CompEq Refl (Ass))) (Sym Ass)) 
    (CompEq (Sym (Trans (Trans Rid (Trans (CompEq Refl (Sym miso₁)) (Sym Ass))) (CompEq pL-1 Refl))) Refl)


  n𝕥-1 id = Trans (Trans (CompEq Refl FId) (Sym Rid)) (Sym Lid)
  n𝕥-1 (f ∘ g) = Trans (Trans (Trans (Trans (Trans (CompEq Refl FComp) (Sym Ass)) (CompEq (n𝕥-1 f) Refl)) Ass) (CompEq Refl (n𝕥-1 g))) (Sym Ass)
  
  n𝕥-1 (f ⊗ g) = Trans (Trans (Trans Ass (Trans (CompEq Refl nm-1) (Trans (Sym Ass) (CompEq (Sym f⊗₁Comp) Refl)))) (CompEq (Trans (⊗₁Eq (n𝕥-1 f) (n𝕥-1 g)) f⊗₁Comp) Refl)) Ass

  n𝕥-1 (f ⇒ g) = Trans (Trans (Trans (Trans Ass (Trans (CompEq Refl nr) (Trans (Sym Ass) (CompEq (Sym f⇒₁Comp) Refl)))) (CompEq (⇒₁Eq (n𝕥-1 g) (Sym (n𝕥 f))) Refl)) (CompEq f⇒₁Comp Refl)) Ass

  n𝕥-1 (g ⇐ f) = Trans (Trans (Trans (Trans Ass (Trans (CompEq Refl nl) (Trans (Sym Ass) (CompEq (Sym f⇐₁Comp) Refl)))) (CompEq (⇐₁Eq (n𝕥-1 g) (Sym (n𝕥 f))) Refl)) (CompEq f⇐₁Comp Refl)) Ass
  
  n𝕥-1 (π⇒ f) = 
    Trans (CompEq Refl (Trans (Trans (Trans (Sym Lid) (CompEq (Sym r-1iso₂) Refl)) Ass) (CompEq Refl pR))) 
          (Trans Ass (Trans (CompEq Refl (Trans (Trans (Trans (Sym Ass) (CompEq r-1iso₁ Refl)) Lid) πRC)) (Trans (Sym Ass) (Trans (CompEq (Trans (Sym f⇒₁Comp) (⇒₁Eq (n𝕥-1 f) Refl)) Refl) (Trans (Trans (CompEq f⇒₁Comp Refl) Ass) (Trans (CompEq Refl (Trans (Sym πRC) (πREq (Trans Ass (Trans (CompEq Refl miso₂) (Sym Rid)))))) (Trans (CompEq (Trans (⇒₁Eq (Sym Lid) (Sym Lid)) f⇒₁Comp) Refl) (Trans Ass (Trans (CompEq Refl (Sym πRC)) (Trans (Sym πRANat) (Trans (πREq (Trans Ass (CompEq Refl (Trans (Sym f⊗₁Comp) (⊗₁Eq 𝕥iso₂ (Sym Rid)))))) (Sym πRB))))))))))))

  n𝕥-1 (π⇒-1 f) = 
    Trans (CompEq Refl (Trans (Trans Rid (Trans (CompEq Refl (Sym miso₁)) (Sym Ass))) (CompEq pR-1 Refl))) 
          (Trans (Sym Ass) 
                 (Trans (CompEq (Trans (Trans (Trans (Trans (Trans πR-1C (πR-1Eq (Trans (CompEq (Trans (⇒₁Eq (Sym Lid) (Sym 𝕥iso₁)) f⇒₁Comp) Refl) (Trans Ass (CompEq Refl(Sym Ass)))))) πR-1A) (CompEq (Trans (πR-1Eq (n𝕥-1 f)) (Sym πR-1B)) Refl)) Ass) (CompEq Refl (Trans (Sym f⊗₁Comp) (⊗₁Eq Lid (Sym Rid))))) Refl) Ass))

  n𝕥-1 (π⇐ f) = 
    Trans (CompEq Refl (Trans (Trans (Trans (Sym Lid) (CompEq (Sym l-1iso₂) Refl)) Ass) (CompEq Refl pL))) 
          (Trans Ass (Trans (CompEq Refl (Trans (Trans (Trans (Sym Ass) (CompEq l-1iso₁ Refl)) Lid) πLC)) (Trans (Sym Ass) (Trans (CompEq (Trans (Sym f⇐₁Comp) (⇐₁Eq (n𝕥-1 f) Refl)) Refl) (Trans (Trans (CompEq f⇐₁Comp Refl) Ass) (Trans (CompEq (Trans (⇐₁Eq (Sym Lid) (Sym Lid)) f⇐₁Comp) (Trans (Sym πLC) (πLEq (Trans (Trans Ass (CompEq Refl miso₂)) (Sym Rid))))) (Trans Ass (Trans (CompEq Refl (Sym πLC)) (Trans (Sym πLBNat) (Trans (πLEq (Trans Ass (CompEq Refl (Trans (Sym f⊗₁Comp) (⊗₁Eq (Sym Rid) 𝕥iso₂))))) (Sym πLA)))))))))))

  n𝕥-1 (π⇐-1 f) = 
    Trans (CompEq Refl (Trans (Trans Rid (Trans (CompEq Refl (Sym miso₁)) (Sym Ass))) (CompEq pL-1 Refl))) 
          (Trans (Sym Ass) 
                  (Trans (CompEq (Trans (Trans (Trans (Trans (Trans πL-1C (πL-1Eq (Trans (Sym Ass) (Trans (CompEq (Trans (CompEq (Trans (⇐₁Eq (Sym Lid) (Sym 𝕥iso₁)) f⇐₁Comp) Refl) Ass) Refl) Ass)))) πL-1B) (CompEq (Trans (πL-1Eq (n𝕥-1 f)) (Sym πL-1A)) Refl)) Ass) (CompEq Refl (Trans (Sym f⊗₁Comp) (⊗₁Eq (Sym Rid) Lid)))) Refl) Ass)) 

  𝔽univ : MBiCFunEq G 𝔽
  𝔽univ = record
    { t = 𝕥
    ; t-1 = 𝕥-1
    ; nt = n𝕥
    ; tiso₁ = 𝕥iso₁
    ; tiso₂ = 𝕥iso₂
    ; mt = Sym Rid
    ; rt = Trans (Sym (Trans Lid Rid)) (Trans (CompEq (Sym r-1iso₁) Refl) Ass)
    ; r-1t = Rid
    ; lt = Trans (Sym (Trans Lid Rid)) (Trans (CompEq (Sym l-1iso₁) Refl) Ass)
    ; l-1t = Rid
    }
    
  module Strict (sG : IsStrict G) where
    open IsStrict sG
    𝔽₀Eq : ∀ B → 𝔽₀ B ≡ F₀ B
    𝔽₀Eq (at x) = sym p
    𝔽₀Eq (B ⇒ C) =  trans (cong₂ ⇒₀ (𝔽₀Eq B) (𝔽₀Eq C)) (sym rEq)
    𝔽₀Eq (C ⇐ B) =  trans (cong₂ ⇐₀  (𝔽₀Eq C) (𝔽₀Eq B)) (sym lEq)
    𝔽₀Eq (B ⊗ C) = trans (cong₂ ⊗₀ (𝔽₀Eq B) (𝔽₀Eq C)) mEq
    
    f⊗₁substId₁ : ∀ {B B' C C'}
      → (eq₁ : B ≡ B') (eq₂ : C ≡ C')
      → Eq (⊗₁ (subst (Hom B) eq₁ Id)
                (subst (Hom C) eq₂ Id)) 
           (subst (Hom (⊗₀ B C)) (cong₂ ⊗₀ eq₁ eq₂) Id)
    f⊗₁substId₁ refl refl = f⊗₁Id
    f⊗₁substId₂ : ∀ {B B' C C'}
      → (eq₁ : B ≡ B') (eq₂ : C ≡ C')
      → Eq (⊗₁ (subst (λ x → Hom x B) eq₁ Id)
                (subst (λ x → Hom x C) eq₂ Id)) 
           (subst (λ x → Hom x (⊗₀ B C)) (cong₂ ⊗₀ eq₁ eq₂) Id)
    f⊗₁substId₂ refl refl = f⊗₁Id
    f⇒₁substId₁ : ∀ {B B' C C'}
      → (eq₁ : B ≡ B') (eq₂ : C ≡ C')
      → Eq (⇒₁ (subst (λ x → Hom x B) eq₁ Id)
                (subst (Hom C) eq₂ Id)) 
           (subst (Hom (⇒₀ B C)) (cong₂ ⇒₀ eq₁ eq₂) Id)
    f⇒₁substId₁ refl refl = f⇒₁Id
    f⇒₁substId₂ : ∀ {B B' C C'}
      → (eq₁ : B ≡ B') (eq₂ : C ≡ C')
      → Eq (⇒₁ (subst (Hom B) eq₁ Id)
                (subst (λ x → Hom x C) eq₂ Id)) 
           (subst (λ x → Hom x (⇒₀ B C)) (cong₂ ⇒₀ eq₁ eq₂) Id)
    f⇒₁substId₂ refl refl = f⇒₁Id
    f⇐₁substId₁ : ∀ {B B' C C'}
      → (eq₁ : B ≡ B') (eq₂ : C ≡ C')
      → Eq (⇐₁ (subst (Hom C) eq₂ Id)
                (subst (λ x → Hom x B) eq₁ Id)) 
           (subst (Hom (⇐₀ C B)) (cong₂ ⇐₀ eq₂ eq₁) Id)
    f⇐₁substId₁ refl refl = f⇐₁Id
    f⇐₁substId₂ : ∀ {B B' C C'}
      → (eq₁ : B ≡ B') (eq₂ : C ≡ C')
      → Eq (⇐₁ (subst (λ x → Hom x C) eq₂ Id)
                (subst (Hom B) eq₁ Id)) 
           (subst (λ x → Hom x (⇐₀ C B)) (cong₂ ⇐₀ eq₂ eq₁) Id)
    f⇐₁substId₂ refl refl = f⇐₁Id
    CompTransId₁ : ∀ {B C D}
      → (eq₁ : B ≡ C) (eq₂ : C ≡ D)
      → Eq (Comp (subst (Hom C) eq₂ Id) (subst (Hom B) eq₁ Id))
           (subst (Hom B) (trans eq₁ eq₂) Id)
    CompTransId₁ refl refl = Lid
    CompTransId₂ : ∀ {B C D}
      → (eq₁ : B ≡ C) (eq₂ : C ≡ D)
      → Eq (Comp (subst (λ x → Hom x B) eq₁ Id) (subst (λ x → Hom x C) eq₂ Id))
           (subst (λ x → Hom x B) (trans eq₁ eq₂) Id)
    CompTransId₂ refl refl = Lid
    
    𝔽₁𝕥Eq : (B : Fma) →
      Eq (𝕥 B) (subst (λ x → Hom (𝔽₀ B) x) (𝔽₀Eq B) Id)
    𝔽₁𝕥-1Eq : (B : Fma) →
      Eq (𝕥-1 B) (subst (λ x → Hom x (𝔽₀ B)) (𝔽₀Eq B) Id)
      
    𝔽₁𝕥Eq (at X) = Refl
    𝔽₁𝕥Eq (B ⇒ C) = Trans (CompEq r-1Id Refl) (Trans (CompEq Refl (Trans (⇒₁Eq (𝔽₁𝕥Eq C) (𝔽₁𝕥-1Eq B)) (f⇒₁substId₁ (𝔽₀Eq B) (𝔽₀Eq C)))) (CompTransId₁ (cong₂ ⇒₀ (𝔽₀Eq B) (𝔽₀Eq C)) (sym rEq)))
    𝔽₁𝕥Eq (C ⇐ B) = Trans (CompEq l-1Id Refl) (Trans (CompEq Refl (Trans (⇐₁Eq (𝔽₁𝕥Eq C) (𝔽₁𝕥-1Eq B)) (f⇐₁substId₁ (𝔽₀Eq B) (𝔽₀Eq C)))) (CompTransId₁ (cong₂ ⇐₀ (𝔽₀Eq C) (𝔽₀Eq B)) (sym lEq)))
    𝔽₁𝕥Eq (B ⊗ C) = Trans (CompEq mId Refl) (Trans (CompEq Refl (Trans (⊗₁Eq (𝔽₁𝕥Eq B) (𝔽₁𝕥Eq C)) (f⊗₁substId₁ (𝔽₀Eq B) (𝔽₀Eq C)))) (CompTransId₁ (cong₂ ⊗₀ (𝔽₀Eq B) (𝔽₀Eq C)) mEq))

    𝔽₁𝕥-1Eq (at X) = lem p
      where
        lem : ∀ {Y Z} → (eq : Y ≡ Z) → Eq (subst (Hom Y) eq Id)
                                           (subst (λ x → Hom x Z) (sym eq) Id) 
        lem refl = Refl
    𝔽₁𝕥-1Eq (B ⇒ C) = Trans (CompEq Refl rId) (Trans (CompEq (Trans (⇒₁Eq (𝔽₁𝕥-1Eq C) (𝔽₁𝕥Eq B)) (f⇒₁substId₂ (𝔽₀Eq B) (𝔽₀Eq C))) Refl) (CompTransId₂ (cong₂ ⇒₀ (𝔽₀Eq B) (𝔽₀Eq C)) (sym rEq)))
    𝔽₁𝕥-1Eq (C ⇐ B) = Trans (CompEq Refl lId) (Trans (CompEq (Trans (⇐₁Eq (𝔽₁𝕥-1Eq C) (𝔽₁𝕥Eq B)) (f⇐₁substId₂ (𝔽₀Eq B) (𝔽₀Eq C))) Refl) (CompTransId₂ (cong₂ ⇐₀ (𝔽₀Eq C) (𝔽₀Eq B)) (sym lEq)))
    𝔽₁𝕥-1Eq (B ⊗ C) = Trans (CompEq Refl (Sym m-1Id)) (Trans (CompEq (Trans (⊗₁Eq (𝔽₁𝕥-1Eq B) (𝔽₁𝕥-1Eq C)) (f⊗₁substId₂ (𝔽₀Eq B) (𝔽₀Eq C))) Refl) (CompTransId₂ (cong₂ ⊗₀ (𝔽₀Eq B) (𝔽₀Eq C)) mEq))

    𝔽univStrict : IsStrictEq 𝔽univ
    𝔽univStrict = record { tEq = λ B → 𝔽₀Eq B ; tId = λ B → 𝔽₁𝕥Eq B }
-- -- =======================================================================

-- putting everything together, FMBiCC(At) is the free magmatic biclosed category
-- on the set At.

FMBiCCFree : FreeMBiCCat FMBiCC
FMBiCCFree = record {
  η = at ;
  F = 𝔽 ;
  comm = λ _ _ → refl ;
  univ = 𝔽univ }
  where open Exists
        open Unique

