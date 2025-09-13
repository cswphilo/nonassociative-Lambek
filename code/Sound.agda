{-# OPTIONS --rewriting #-}

module Sound where 

open import Fma
open import SeqCalc
open import FCat

-- We postulate an atomic formula to which holes map.
postulate Z : At 

-- Interpret trees to formulae.
[_] : (T : Tree) → Fma
[ ∙ ] = at Z
[ η x ] = x
[ T ⊛ T₁ ] = [ T ] ⊗ [ T₁ ]

-- A function lifts morphsims with contexts, i.e.
-- given T[∙], it lifts any morphism A ⟶ B to 
-- T[A] ⟶ T[B].
f2T[f] : {T U V : Tree} (p : Path T)
  → (f : [ U ] ⟶ [ V ]) 
  → [ sub p U ] ⟶ [ sub p V ]
f2T[f] ∙ f = f
f2T[f] (p ◂ U) f = f2T[f] p f ⊗ id
f2T[f] (T ▸ p) f = id ⊗ f2T[f] p f

-- ▼Properties of the lifting fucntion▼
f2T[f]∘ : {T U V W : Tree} (p : Path T)
  → (f : [ U ] ⟶ [ V ]) 
  → (g : [ V ] ⟶ [ W ])
  → f2T[f] {U = V} {W} p g ∘ f2T[f] {U = U} p f ≐ f2T[f] p (g ∘ f)
f2T[f]∘ ∙ f g = refl
f2T[f]∘ (p ◂ U) f g = ~ f⊗∘ ． (f2T[f]∘ p f g ⊗ lid)
f2T[f]∘ (T ▸ p) f g = ~ f⊗∘ ． (lid ⊗ f2T[f]∘ p f g)

f2T[f]++ : {T T' U V : Tree} (p : Path T) (q : Path T')
  → (f : [ U ] ⟶ [ V ]) 
  → f2T[f] {U = U} {V} (p ++ q) f ≐ f2T[f] p (f2T[f] q f)
f2T[f]++ ∙ q f = refl
f2T[f]++ (p ◂ U) q f = f2T[f]++ p q f ⊗ refl
f2T[f]++ (T ▸ p) q f = refl ⊗ f2T[f]++ p q f

f2T[f]◂▸ : {T U U' V V' W₁ W₂ : Tree} (p : Path T) (p₁ : Path W₁) (p₂ : Path W₂)
         → (f : [ U ] ⟶ [ U' ]) (g : [ V ] ⟶ [ V' ])
         → f2T[f] {V = V'} (p ++ (sub p₁ U' ▸ p₂)) g 
            ∘ f2T[f] {U = U} (p ++ (p₁ ◂ sub p₂ V)) f 
              ≐ (f2T[f] (p ++ (p₁ ◂ _)) f 
                  ∘ f2T[f] (p ++ (_ ▸ p₂)) g)
f2T[f]◂▸ ∙ p₁ p₂ f g = id⊗swap
f2T[f]◂▸ (p ◂ U) p₁ p₂ f g = ~ f⊗∘ ． (refl ⊗ lid ． (f2T[f]◂▸ p p₁ p₂ f g ⊗ refl ． refl ⊗ rid ． f⊗∘))
f2T[f]◂▸ (T ▸ p) p₁ p₂ f g = ~ f⊗∘ ． (lid ⊗ refl ． (refl ⊗ f2T[f]◂▸ p p₁ p₂ f g ． rid ⊗ refl ． f⊗∘))

f2T[f]cong : {T U V : Tree} (p : Path T)
  → {f g : [ U ] ⟶ [ V ]}
  → (eq : f ≐ g)
  → f2T[f] {U = U} {V} p f ≐ f2T[f] p g
f2T[f]cong ∙ eq = eq
f2T[f]cong (p ◂ U) eq = f2T[f]cong p eq ⊗ refl
f2T[f]cong (T ▸ p) eq = refl ⊗ f2T[f]cong p eq
-- ▲Properties of the lifting fucntion▲

sound : ∀ {T C}
  → (f : T ⊢ C) 
  → [ T ] ⟶ C
sound ax = id
sound (⇒R f) = π⇒ (sound f)
sound (⇐R f) = π⇐ (sound f)
sound (⇒L p f g) = sound g ∘ f2T[f] p (π⇒-1 id ∘ sound f ⊗ id)
sound (⇐L p f g) = sound g ∘ f2T[f] p (π⇐-1 id ∘ id ⊗ sound f)
sound (⊗R f g) = sound f ⊗ sound g
sound (⊗L p f) = sound f ∘ f2T[f] p id

-- Sound preserves equivalence on derivations.
≗sound≐ : ∀ {T C}
  → {f g : T ⊢ C}
  → (eq : f ≗ g)
  → sound f ≐ sound g
≗sound≐ refl = refl
≗sound≐ (~ eq) = ~ ≗sound≐ eq
≗sound≐ (eq ∘ eq₁) = ≗sound≐ eq ． ≗sound≐ eq₁
≗sound≐ (⇒R eq) = π⇒ (≗sound≐ eq)
≗sound≐ (⇐R eq) = π⇐ (≗sound≐ eq)
≗sound≐ (⇒L {p = p} eq eq₁) = ≗sound≐ eq₁ ∘ f2T[f]cong p (refl ∘ (≗sound≐ eq ⊗ refl))
≗sound≐ (⇐L {p = p} eq eq₁) = ≗sound≐ eq₁ ∘ f2T[f]cong p (refl ∘ (refl ⊗ ≗sound≐ eq))
≗sound≐ (⊗R eq eq₁) = ≗sound≐ eq ⊗ ≗sound≐ eq₁
≗sound≐ (⊗L eq) = ≗sound≐ eq ∘ refl
≗sound≐ ⇒L⇒R = π⇒B
≗sound≐ ⇐L⇒R = π⇒B
≗sound≐ ⊗L⇒R = π⇒B
≗sound≐ ⇒L⇐R = π⇐A
≗sound≐ ⇐L⇐R = π⇐A
≗sound≐ ⊗L⇐R = π⇐A 
≗sound≐ ⇒L⊗R₁ = ~ f⊗∘ ． refl ⊗ (~ rid)
≗sound≐ ⇒L⊗R₂ = ~ f⊗∘ ． (~ rid) ⊗ refl
≗sound≐ ⇐L⊗R₁ = ~ f⊗∘ ． refl ⊗ (~ rid)
≗sound≐ ⇐L⊗R₂ = ~ f⊗∘ ． (~ rid) ⊗ refl
≗sound≐ ⊗L⊗R₁ = ~ f⊗∘ ． refl ⊗ (~ rid)
≗sound≐ ⊗L⊗R₂ = ~ f⊗∘ ． (~ rid) ⊗ refl
≗sound≐ (⊗L⊗L {p = p} {p₁} {p₂}) = ass ． ((refl ∘ (~ f2T[f]◂▸ p p₁ p₂ id id)) ． ~ ass)
≗sound≐ (⊗L⇒L₁ {A = A} {B} {A'} {B'} {p = p} {p'} {f}) = 
  ass ． (refl ∘ (refl ∘ f2T[f]++ p' (p ◂ η (A ⇒ B)) id 
      ． (f2T[f]∘ p' (f2T[f] (p ◂ η (A ⇒ B)) id) (π⇒-1 id ∘ (sound f ⊗ id)) 
      ． f2T[f]cong p' (ass ． (refl ∘ (~ f⊗∘ ． refl ⊗ lid))))))
≗sound≐ (⊗L⇒L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p} {p₁} {p₂} {f}) = 
  ass ． ((refl ∘ (f2T[f]++ p (sub p₁ (η A' ⊛ η B') ▸ p₂) (π⇒-1 id ∘ (sound f ⊗ id)) ∘ refl 
      ． (refl ∘ f2T[f]++ p (p₁ ◂ sub p₂ (U ⊛ η (A ⇒ B))) id 
      ． (f2T[f]∘ p (f2T[f] (p₁ ◂ sub p₂ (U ⊛ η (A ⇒ B))) id) (f2T[f] (sub p₁ (η A' ⊛ η B') ▸ p₂) (π⇒-1 id ∘ (sound f ⊗ id))) 
      ． (f2T[f]cong p (~ f⊗∘ ． ((lid ． rid) ⊗ (~ (lid ． rid)) ． f⊗∘))
      ． ~ f2T[f]∘ p (f2T[f] (sub p₁ (η (A' ⊗ B')) ▸ p₂) (π⇒-1 id ∘ (sound f ⊗ id))) (f2T[f] (p₁ ◂ sub p₂ (η B)) id) 
      ． (refl ∘ ~ f2T[f]++ p (sub p₁ (η (A' ⊗ B')) ▸ p₂) (π⇒-1 id ∘ (sound f ⊗ id))) 
      ． (~ f2T[f]++ p (p₁ ◂ sub p₂ (η B)) id ∘ refl)))))) ． ~ ass)
≗sound≐ (⊗L⇒L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p} {p₁} {p₂} {f}) =
  ass ． ((refl ∘ (f2T[f]++ p (p₁ ◂ sub p₂ (η A' ⊛ η B')) (π⇒-1 id ∘ (sound f ⊗ id)) ∘ refl 
      ． (refl ∘ f2T[f]++ p (sub p₁ (U ⊛ η (A ⇒ B)) ▸ p₂) id 
      ． (f2T[f]∘ p (f2T[f] (sub p₁ (U ⊛ η (A ⇒ B)) ▸ p₂) id) (f2T[f] (p₁ ◂ sub p₂ (η A' ⊛ η B')) (π⇒-1 id ∘ (sound f ⊗ id))) 
      ． (f2T[f]cong p (~ f⊗∘ ． ((~ (lid ． rid)) ⊗ (lid ． rid) ． f⊗∘)) 
      ． (~ f2T[f]∘ p (f2T[f] (p₁ ◂ sub p₂ (η (A' ⊗ B'))) (π⇒-1 id ∘ (sound f ⊗ id))) (f2T[f] (sub p₁ (η B) ▸ p₂) id)) 
      ． (refl ∘ ~ f2T[f]++ p (p₁ ◂ sub p₂ (η (A' ⊗ B'))) (π⇒-1 id ∘ (sound f ⊗ id))) 
      ． (~ f2T[f]++ p (sub p₁ (η B) ▸ p₂) id ∘ refl)))))) ． ~ ass)
≗sound≐ (⊗L⇐L₁ {A = A} {B} {A'} {B'} {p = p} {p'} {f}) = 
  ass ． (refl ∘ (refl ∘ f2T[f]++ p' (η (B ⇐ A) ▸ p) id 
      ． (f2T[f]∘ p' (f2T[f] (η (B ⇐ A) ▸ p) id) (π⇐-1 id ∘ (id ⊗ sound f)) 
      ． f2T[f]cong p' (ass ．  (refl ∘ (~ f⊗∘ ． lid ⊗ refl))))))
≗sound≐ (⊗L⇐L₂1/\2 {U = U} {A = A} {B} {A'} {B'} {p = p} {p₁} {p₂} {f}) =
  ass ． ((refl ∘ (f2T[f]++ p (sub p₁ (η A' ⊛ η B') ▸ p₂) (π⇐-1 id ∘ (id ⊗ sound f)) ∘ refl 
      ． (refl ∘ f2T[f]++ p (p₁ ◂ sub p₂ (η (B ⇐ A) ⊛ U)) id 
      ． (f2T[f]∘ p (f2T[f] (p₁ ◂ sub p₂ (η (B ⇐ A) ⊛ U)) id) (f2T[f] (sub p₁ (η A' ⊛ η B') ▸ p₂) (π⇐-1 id ∘ (id ⊗ sound f))) 
      ． (f2T[f]cong p (~ f⊗∘ ． ((lid ． rid) ⊗ (~ (lid ． rid)) ． f⊗∘))
      ． ~ f2T[f]∘ p (f2T[f] (sub p₁ (η (A' ⊗ B')) ▸ p₂) (π⇐-1 id ∘ (id ⊗ sound f))) (f2T[f] (p₁ ◂ sub p₂ (η B)) id) 
      ． (refl ∘ ~ f2T[f]++ p (sub p₁ (η (A' ⊗ B')) ▸ p₂) (π⇐-1 id ∘ (id ⊗ sound f))) 
      ． (~ f2T[f]++ p (p₁ ◂ sub p₂ (η B)) id ∘ refl)))))) ． ~ ass)
≗sound≐ (⊗L⇐L₂2/\1 {U = U} {A = A} {B} {A'} {B'} {p = p} {p₁} {p₂} {f}) =
  ass ． ((refl ∘ (f2T[f]++ p (p₁ ◂ sub p₂ (η A' ⊛ η B')) (π⇐-1 id ∘ (id ⊗ sound f)) ∘ refl 
      ． (refl ∘ f2T[f]++ p (sub p₁ (η (B ⇐ A) ⊛ U) ▸ p₂) id 
      ． (f2T[f]∘ p (f2T[f] (sub p₁ (η (B ⇐ A) ⊛ U) ▸ p₂) id) (f2T[f] (p₁ ◂ sub p₂ (η A' ⊛ η B')) (π⇐-1 id ∘ (id ⊗ sound f))) 
      ． (f2T[f]cong p (~ f⊗∘ ． ((~ (lid ． rid)) ⊗ (lid ． rid) ． f⊗∘)) 
      ． (~ f2T[f]∘ p (f2T[f] (p₁ ◂ sub p₂ (η (A' ⊗ B'))) (π⇐-1 id ∘ (id ⊗ sound f))) (f2T[f] (sub p₁ (η B) ▸ p₂) id)) 
      ． (refl ∘ ~ f2T[f]++ p (p₁ ◂ sub p₂ (η (A' ⊗ B'))) (π⇐-1 id ∘ (id ⊗ sound f))) 
      ． (~ f2T[f]++ p (sub p₁ (η B) ▸ p₂) id ∘ refl)))))) ． ~ ass)
≗sound≐ (⇒L⇒L {A = A} {B} {q = q} {r} {f} {g}) = 
  ass ． (refl ∘ (refl ∘ f2T[f]++ r (q ◂ _) (π⇒-1 id ∘ (sound f ⊗ id)) 
      ． (f2T[f]∘ r (f2T[f] (q ◂ η (A ⇒ B)) (π⇒-1 id ∘ (sound f ⊗ id))) (π⇒-1 id ∘ (sound g ⊗ id)) 
      ． f2T[f]cong r (ass ． (refl ∘ (~ f⊗∘ ． (refl ⊗ lid)))))))
≗sound≐ (⇒L⇒L₂ {p = p} {p₁} {p₂} {f} {f'}) = 
  ass ． ((refl ∘ f2T[f]◂▸ p p₁ p₂ (π⇒-1 id ∘ (sound f ⊗ id)) (π⇒-1 id ∘ (sound f' ⊗ id))) 
      ． ~ ass)
≗sound≐ (⇒L⇐L {A = A} {B} {q = q} {r} {f} {g}) = 
  ass ． (refl ∘ (refl ∘ f2T[f]++ r (_ ▸ q) (π⇒-1 id ∘ (sound f ⊗ id)) 
      ． (f2T[f]∘ r (f2T[f] (η (B ⇐ A) ▸ q) (π⇒-1 id ∘ (sound f ⊗ id))) (π⇐-1 id ∘ (id ⊗ sound g)) 
      ． f2T[f]cong r (ass ． (refl ∘ (~ f⊗∘ ． lid ⊗ refl))))))
≗sound≐ (⇒L⇐L₂ {p = p} {p₁} {p₂} {f} {f'}) = 
  ass ． ((refl ∘ f2T[f]◂▸ p p₁ p₂ (π⇒-1 id ∘ (sound f ⊗ id)) (π⇐-1 id ∘ (id ⊗ sound f'))) 
      ． ~ ass)
≗sound≐ (⇐L⇒L {A = A} {B} {q = q} {r} {f} {g}) = 
  ass ． (refl ∘ (refl ∘ f2T[f]++ r (q ◂ _) (π⇐-1 id ∘ (id ⊗ sound f)) 
      ． (f2T[f]∘ r (f2T[f] (q ◂ η (A ⇒ B)) (π⇐-1 id ∘ (id ⊗ sound f))) (π⇒-1 id ∘ (sound g ⊗ id)) 
      ． f2T[f]cong r (ass ． (refl ∘ (~ f⊗∘ ． (refl ⊗ lid)))))))
≗sound≐ (⇐L⇒L₂ {p = p} {p₁} {p₂} {f} {f'}) = 
  ass ． ((refl ∘ f2T[f]◂▸ p p₁ p₂ (π⇐-1 id ∘ (id ⊗ sound f)) (π⇒-1 id ∘ (sound f' ⊗ id))) 
      ． ~ ass)
≗sound≐ (⇐L⇐L {A = A} {B} {q = q} {r} {f} {g}) =
  ass ． (refl ∘ (refl ∘ f2T[f]++ r (_ ▸ q) (π⇐-1 id ∘ (id ⊗ sound f))
      ． (f2T[f]∘ r (f2T[f] (η (B ⇐ A) ▸ q) (π⇐-1 id ∘ (id ⊗ sound f))) (π⇐-1 id ∘ (id ⊗ sound g)) 
      ． f2T[f]cong r (ass ． (refl ∘ (~ f⊗∘ ． lid ⊗ refl))))))
≗sound≐ (⇐L⇐L₂ {p = p} {p₁} {p₂} {f} {f'}) =
  ass ． ((refl ∘ (f2T[f]◂▸ p p₁ p₂ (π⇐-1 id ∘ (id ⊗ sound f)) (π⇐-1 id ∘ (id ⊗ sound f')))) 
      ． ~ ass)