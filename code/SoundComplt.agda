{-# OPTIONS --rewriting #-}

module SoundComplt where 

open import Fma
open import SeqCalc
open import FCat
open import Cut
open import FormulaeAxiom
open import Sound
open import Complt

-- Axiom on formulae corresponds to identity in the Hilbert-style calculus.
sound-axA≐id : {A : Fma} → sound (axA {A}) ≐ id
sound-axA≐id {at x} = refl
sound-axA≐id {A ⇒ B} = 
  π⇒ (sound-axA≐id ∘ refl) 
  ． (π⇒ lid ． (π⇒ (refl ∘ sound-axA≐id ⊗ refl) 
  ． (π⇒ (refl ∘ f⊗id) 
  ． (π⇒ (~ rid) ． π⇒-1π⇒))))
sound-axA≐id {A ⇐ B} = 
  π⇐ (sound-axA≐id ∘ refl) 
  ． (π⇐ lid ． (π⇐ (refl ∘ refl ⊗ sound-axA≐id) 
  ． (π⇐ (refl ∘ f⊗id) 
  ． (π⇐ (~ rid) ． π⇐-1π⇐))))
sound-axA≐id {A ⊗ B} = ~ rid ． (sound-axA≐id ⊗ sound-axA≐id ． f⊗id)

π⇒-1B : ∀ {A B B' C}
  → {f : B ⟶ A ⇒ C} {g : B' ⟶ B}
  → π⇒-1 f ∘ id ⊗ g ≐ π⇒-1 (f ∘ g) 
π⇒-1B = ~ π⇒π⇒-1 ． π⇒-1 (~ π⇒B ． (π⇒-1π⇒ ∘ refl))

π⇐-1A : ∀ {A A' B C}
  → {f : A ⟶ C ⇐ B} {g : A' ⟶ A}
  → π⇐-1 f ∘ g ⊗ id ≐ π⇐-1 (f ∘ g)
π⇐-1A = ~ π⇐π⇐-1 ． π⇐-1 (~ π⇐A ． (π⇐-1π⇐ ∘ refl))

-- π⇐-1C : ∀ {A B C C'}
--   → {f : C ⟶ C'} {g : B ⟶ C ⇐ A}
--   → f ∘ π⇐-1 g ≐ π⇐-1 (f ⇐ id ∘ g)
-- π⇐-1C = ~ π⇐π⇐-1 ． π⇐-1 (π⇐C ． (refl ∘ π⇐-1π⇐))

-- cut corresponds to composition in the Hilbert-style calculus.
soundcut : ∀ {T U W C D} (p : Path T)
  → (f : U ⊢ D) (g : W ⊢ C)
  → (eq : W ≡ sub p (η D))
  → sound (cut p f g eq) ≐ (sound g ∘ (subst-ant (cong [_] eq) id ∘ f2T[f] {U = U} {η D} p (sound f)))

soundcut⇒L : ∀ {T U V A B C} (p : Path T)
 → (f : U ⊢ A ⇒ B)
 → (g : V ⊢ A) (h : sub p (η B) ⊢ C)
 → sound (cut⇒L p f g h) 
    ≐ (sound h 
        ∘ (f2T[f] {U = η (A ⊗ (A ⇒ B))} {η B} p (π⇒-1 id) 
          ∘ f2T[f] {U = V ⊛ U} {η (A ⊗ (A ⇒ B))} p (sound (⊗R g f))))
soundcut⇒L {U = U} {V} {A} {B} p (⇒R f) g h = 
  soundcut (p ++ (∙ ◂ _)) g (cut p f h refl) refl 
  ． (soundcut p f h refl ∘ refl ． (ass ． (refl ∘ (lid ∘ lid 
  ． (refl ∘ f2T[f]++ p (∙ ◂ _) (sound g) ． (f2T[f]∘ p (f2T[f] {U = V} {η A} (∙ ◂ U) (sound g)) (sound f) 
  ． (f2T[f]cong p ((~ (π⇒-1 lid ． π⇒π⇒-1) 
  ． ~ π⇒-1B ∘ refl) ． ass 
  ． (refl ∘ (~ f⊗∘ ． lid ⊗ (~ rid))))  -- expand with identities is a critical step
  ． ~ f2T[f]∘ p (sound g ⊗ π⇒ (sound f)) (π⇒-1 id))))))))
soundcut⇒L p (⇒L {U = U} {A} {B} p₁ f f₁) g h = 
  soundcut⇒L p f₁ g h ∘ refl 
  ． (ass ． (refl ∘ (refl ∘ (f2T[f]++ p (_ ▸ p₁) (π⇒-1 id ∘ (sound f ⊗ id))) 
  ． (f2T[f]∘ p (sound g ⊗ sound f₁) (π⇒-1 id) ∘ refl 
  ． (f2T[f]∘ p (id ⊗ f2T[f] {U = U ⊛ η (A ⇒ B)} {η B} p₁ (π⇒-1 id ∘ (sound f ⊗ id))) (π⇒-1 id ∘ (sound g ⊗ sound f₁)) 
  ． (f2T[f]cong p (ass 
  ． (refl ∘ (~ f⊗∘ ． (~ rid) ⊗ refl))) 
  ． ~ f2T[f]∘ p (sound g ⊗ (sound f₁ ∘ f2T[f] {U = U ⊛ η (A ⇒ B)} {η B} p₁ (π⇒-1 id ∘ (sound f ⊗ id)))) (π⇒-1 id)))))))
soundcut⇒L p (⇐L {U = U} {A} {B} p₁ f f₁) g h = 
  soundcut⇒L p f₁ g h ∘ refl 
  ． (ass ． (refl ∘ (refl ∘ (f2T[f]++ p (_ ▸ p₁) (π⇐-1 id ∘ (id ⊗ sound f))) 
  ． (f2T[f]∘ p (sound g ⊗ sound f₁) (π⇒-1 id) ∘ refl 
  ． (f2T[f]∘ p (id ⊗ f2T[f] {U = η (B ⇐ A) ⊛ U} {η B} p₁ (π⇐-1 id ∘ (id ⊗ sound f))) (π⇒-1 id ∘ (sound g ⊗ sound f₁)) 
  ． (f2T[f]cong p (ass 
  ． (refl ∘ (~ f⊗∘ ． (~ rid) ⊗ refl))) 
  ． ~ f2T[f]∘ p (sound g ⊗ (sound f₁ ∘ f2T[f] {U = η (B ⇐ A) ⊛ U} {η B} p₁ (π⇐-1 id ∘ (id ⊗ sound f)))) (π⇒-1 id)))))))
soundcut⇒L p (⊗L {A = A} {B} p₁ f) g h = 
  soundcut⇒L p f g h ∘ refl 
  ． (ass ． (refl ∘ (f2T[f]∘ p ((sound g) ⊗ (sound f)) (π⇒-1 id) ∘ refl 
  ． ((refl ∘ f2T[f]++ p (_ ▸ p₁) id) 
  ． (f2T[f]∘ p (id ⊗ f2T[f] {U = η (A ⊗ B)} {η A ⊛ η B} p₁ id) (π⇒-1 id ∘ (sound g ⊗ sound f))
  ． (f2T[f]cong p (ass ． (refl ∘ (~ f⊗∘ ． (~ rid) ⊗ refl))) 
  ． ~ f2T[f]∘ p (sound g ⊗ (sound f ∘ f2T[f] {U = η (A ⊗ B)} {η A ⊛ η B} p₁ id)) (π⇒-1 id))))))) 

soundcut⇐L : ∀ {T U V A B C} (p : Path T)
 → (f : U ⊢ B ⇐ A)
 → (g : V ⊢ A) (h : sub p (η B) ⊢ C)
 → sound (cut⇐L p f g h) 
    ≐ (sound h 
        ∘ (f2T[f] {U = η ((B ⇐ A) ⊗ A)} {η B} p (π⇐-1 id) 
          ∘ f2T[f] {U = U ⊛ V} {η ((B ⇐ A) ⊗ A)} p (sound (⊗R f g))))
soundcut⇐L {U = U} {V} {A} {B} p (⇐R f) g h = 
  soundcut (p ++ (_ ▸ ∙)) g (cut p f h refl) refl 
  ． (soundcut p f h refl ∘ refl ． (ass ． (refl ∘ (lid ∘ lid 
  ． (refl ∘ f2T[f]++ p (_ ▸ ∙) (sound g) 
  ． (f2T[f]∘ p (f2T[f] {U = V} {η A} (U ▸ ∙) (sound g)) (sound f) 
  ． (f2T[f]cong p ((~ (π⇐-1 lid ． π⇐π⇐-1) 
  ． ~ π⇐-1A ∘ refl) ． ass 
  ． (refl ∘ (~ f⊗∘ ． (~ rid) ⊗ lid))) 
  ． ~ f2T[f]∘ p (π⇐ (sound f) ⊗ sound g) (π⇐-1 id))))))))
soundcut⇐L p (⇒L {U = U} {A} {B} p₁ f f₁) g h = 
  soundcut⇐L p f₁ g h ∘ refl 
  ． (ass ． (refl ∘ (refl ∘ (f2T[f]++ p (p₁ ◂ _) (π⇒-1 id ∘ (sound f ⊗ id))) 
  ． (f2T[f]∘ p (sound f₁ ⊗ sound g) (π⇐-1 id) ∘ refl 
  ． (f2T[f]∘ p (f2T[f] {U = U ⊛ η (A ⇒ B)} {η B} p₁ (π⇒-1 id ∘ (sound f ⊗ id)) ⊗ id) (π⇐-1 id ∘ (sound f₁ ⊗ sound g)) 
  ． ((f2T[f]cong p (ass 
  ． (refl ∘ (~ f⊗∘ ． refl ⊗ (~ rid)))) 
  ． ~ f2T[f]∘ p ((sound f₁ ∘ f2T[f] {U = U ⊛ η (A ⇒ B)} {η B} p₁ (π⇒-1 id ∘ (sound f ⊗ id))) ⊗ sound g) (π⇐-1 id))))))))
soundcut⇐L p (⇐L {U = U} {A} {B} p₁ f f₁) g h = 
  soundcut⇐L p f₁ g h ∘ refl 
  ． (ass ． (refl ∘ (refl ∘ (f2T[f]++ p (p₁ ◂ _) (π⇐-1 id ∘ (id ⊗ sound f))) 
  ． (f2T[f]∘ p (sound f₁ ⊗ sound g) (π⇐-1 id) ∘ refl 
  ． (f2T[f]∘ p (f2T[f] {U = η (B ⇐ A) ⊛ U} {η B} p₁ (π⇐-1 id ∘ (id ⊗ sound f)) ⊗ id) (π⇐-1 id ∘ (sound f₁ ⊗ sound g)) 
  ． ((f2T[f]cong p (ass 
  ． (refl ∘ (~ f⊗∘ ． refl ⊗ (~ rid)))) 
  ． ~ f2T[f]∘ p ((sound f₁ ∘ f2T[f] {U = η (B ⇐ A) ⊛ U} {η B} p₁ (π⇐-1 id ∘ (id ⊗ sound f))) ⊗ sound g) (π⇐-1 id))))))))
soundcut⇐L p (⊗L {A = A} {B} p₁ f) g h = 
  soundcut⇐L p f g h ∘ refl 
  ． (ass ． (refl ∘ (f2T[f]∘ p ((sound f) ⊗ (sound g)) (π⇐-1 id) ∘ refl 
  ． ((refl ∘ f2T[f]++ p (p₁ ◂ _) id) 
  ． ((f2T[f]∘ p (f2T[f] {U = η (A ⊗ B)} {η A ⊛ η B} p₁ id ⊗ id) (π⇐-1 id ∘ (sound f ⊗ sound g))
  ． ((f2T[f]cong p (ass ． (refl ∘ (~ f⊗∘ ． refl ⊗ (~ rid)))) 
  ． (~ f2T[f]∘ p ((sound f ∘ f2T[f] {U = η (A ⊗ B)} {η A ⊛ η B} p₁ id) ⊗ sound g) (π⇐-1 id))))))))))

soundcut⊗L : ∀ {T U A B C} (p : Path T)
 → (f : U ⊢ (A ⊗ B)) (g : sub p (η A ⊛ η B) ⊢ C)
 → sound (cut⊗L p f g)
    ≐ (sound g ∘ f2T[f] {U = η (A ⊗ B)} {η A ⊛ η B} p id 
        ∘ (id ∘ f2T[f] {U = U} {η (A ⊗ B)} p (sound f)))
soundcut⊗L p (⇒L {U = U} {A} {B} p₁ f f₁) g = 
  soundcut⊗L p f₁ g ∘ refl 
  ． ((ass ． (refl ∘ (ass ． (refl ∘ (refl ∘ f2T[f]++ p p₁ (π⇒-1 id ∘ (sound f ⊗ id)))) 
  ． (refl ∘ f2T[f]∘ p (f2T[f] {U = U ⊛ η (A ⇒ B)} {η B} p₁ (π⇒-1 id ∘ (sound f ⊗ id))) (sound f₁))))))
soundcut⊗L p (⇐L {U = U} {A} {B} p₁ f f₁) g = 
  soundcut⊗L p f₁ g ∘ refl 
  ． (ass ． (refl ∘ (ass ． (refl ∘ (refl ∘ f2T[f]++ p p₁ (π⇐-1 id ∘ (id ⊗ sound f)))) 
  ． (refl ∘ f2T[f]∘ p (f2T[f] {U = η (B ⇐ A) ⊛ U} {η B} p₁ (π⇐-1 id ∘ (id ⊗ sound f))) (sound f₁)))))
soundcut⊗L {A = A} {B} p (⊗R {T} {U} f f₁) g = 
  soundcut (p ++ (∙ ◂ U)) f (cut (p ++ (η A ▸ ∙)) f₁ g refl) refl 
  ． (soundcut (p ++ (η A ▸ ∙)) f₁ g refl ∘ refl 
  ． (ass ． ((refl ∘ (lid ∘ lid 
  ． (f2T[f]++ p (η A ▸ ∙) (sound f₁) ∘ f2T[f]++ p (∙ ◂ U) (sound f) 
  ． (f2T[f]∘ p (f2T[f] {U = T} {η A} (∙ ◂ U) (sound f)) (f2T[f] {U = U} {η B} (η A ▸ ∙) (sound f₁)) 
  ． (f2T[f]cong p (~ f⊗∘ ． ((lid ⊗ (~ rid)) ． ~ lid)) 
  ． ~ f2T[f]∘ p (sound (⊗R f f₁)) id) 
  ． (refl ∘ ~ lid))))) 
  ． ~ ass)))
soundcut⊗L p (⊗L {A = A} {B} p₁ f) g = 
  soundcut⊗L p f g ∘ refl 
  ． (ass ． (refl ∘ (refl ∘ f2T[f]++ p p₁ id 
  ． (ass ． (refl ∘ f2T[f]∘ p (f2T[f] {U = η (A ⊗ B)} {η A ⊛ η B} p₁ id) (sound f))))))

soundcut p f (⇒R g) refl = π⇒ (soundcut (_ ▸ p) f g refl ． (refl ∘ (lid ． refl ⊗ (~ lid)))) ． ~ π⇒B
soundcut p f (⇐R g) refl = π⇐ (soundcut (p ◂ _) f g refl ． (refl ∘ (lid ． ((~ lid) ⊗ refl)))) ． ~ π⇐A
soundcut {D = D} p f (⇒L {U = U} {A} {B} p₁ g h) eq with subeq (U ⊛ η (A ⇒ B)) (η D) p₁ p eq
soundcut {U = U₁} {D = D} p f (⇒L {U = U} {A} {B} p₁ g h) refl | 2>L1 (gt q refl refl refl) = 
  (refl ∘ ((~ f2T[f]∘ {V = η (A ⊗ (A ⇒ [ η B ]))} p₁ (sound (cut q f g refl) ⊗ id) (π⇒-1 id)) 
  ． (f2T[f]∘ p₁ (sound (cut q f g refl) ⊗ id) (π⇒-1 id) 
  ． (f2T[f]cong p₁ (refl ∘ soundcut q f g refl ⊗ refl 
  ． ((refl ∘ ((refl ∘ lid) ⊗ rid ． f⊗∘)) ． ~ ass)) 
  ． (~ f2T[f]∘ p₁ (f2T[f] {U = U₁} {η D} (q ◂ η (A ⇒ B)) (sound f)) (π⇒-1 id ∘ (sound g ⊗ id))) 
  ． (~ f2T[f]∘ p₁ (sound g ⊗ id) (π⇒-1 id) ∘ refl)) 
  ． (refl ∘ (~ f2T[f]++ p₁ (q ◂ η (A ⇒ B)) (sound f))) 
  ． (f2T[f]∘ {V = η (A ⊗ (A ⇒ B))} p₁ (sound g ⊗ id) (π⇒-1 id) ∘ refl) ． (refl ∘ (~ lid))))) 
  ． ~ ass
soundcut {U = U₁} {D = D} p f (⇒L {U = U} {A} {B} p₁ g h) refl | 2>R1 (gt ∙ refl refl refl) = 
  soundcut⇒L p₁ f g h 
  ． ((refl ∘ (f2T[f]∘ p₁ (sound (⊗R g f)) (π⇒-1 id) 
  ． (f2T[f]cong p₁ ((refl ∘ ((rid ⊗ (~ lid)) ． f⊗∘)) ． ~ ass) 
  ． ~ f2T[f]∘ p₁ (f2T[f] {U = η [ U₁ ]} {η (A ⇒ B)} (U ▸ ∙) (sound f)) (π⇒-1 id ∘ (sound g ⊗ id))) 
  ． (refl ∘ (~ f2T[f]++  p₁ (_ ▸ ∙) (sound f))) ． (refl ∘ (~ lid)))) 
  ． ~ ass)
soundcut {D = D} p f (⇒L {U = U} {A} {B} p₁ g h) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) = 
  soundcut (q ++ (sub q₁ (η B) ▸ q₂)) f h refl ∘ refl 
  ． (ass ． ((refl ∘ (lid ∘ refl 
  ． (f2T[f]◂▸ q q₁ q₂ (π⇒-1 id ∘ (sound g ⊗ id)) (sound f) 
  ． (refl ∘ ~ lid)))) ． ~ ass))
soundcut {D = D} p f (⇒L {U = U} {A} {B} p₁ g h) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 
  soundcut (q ++ (q₁ ◂ sub q₂ (η B))) f h refl ∘ refl 
  ． (ass ． ((refl ∘ (lid ∘ refl 
  ． ((~ f2T[f]◂▸ q q₁ q₂ (sound f) (π⇒-1 id ∘ (sound g ⊗ id))) 
  ． (refl ∘ ~ lid)))) ． ~ ass))
soundcut {D = D} p f (⇐L {U = U} {A} {B} p₁ g h) eq with subeq (η (B ⇐ A) ⊛ U) (η D) p₁ p eq
soundcut {U = U₁} {D = D} p f (⇐L {U = U} {A} {B} p₁ g h) refl | 2>L1 (gt ∙ refl refl refl) = 
  soundcut⇐L p₁ f g h 
  ． ((refl ∘ (f2T[f]∘ p₁ (sound (⊗R f g)) (π⇐-1 id) 
  ． f2T[f]cong p₁ ((refl ∘ ((~ lid) ⊗ rid ． f⊗∘)) 
  ． ~ ass) 
  ． ~ f2T[f]∘ p₁ (f2T[f] {U = U₁} {η (B ⇐ A)} (∙ ◂ U) (sound f)) (π⇐-1 id ∘ (id ⊗ sound g)) 
  ． (refl ∘ (~ f2T[f]++ p₁ (∙ ◂ U) (sound f) ． ~ lid)))) 
  ． ~ ass)
soundcut {U = U₁} {D = D} p f (⇐L {U = U} {A} {B} p₁ g h) refl | 2>R1 (gt q refl refl refl) = 
  (refl ∘ (f2T[f]cong p₁ ((refl ∘ (rid ⊗ (soundcut q f g refl ． (refl ∘ lid)) 
  ． f⊗∘)) 
  ． ~ ass) 
  ． ~ f2T[f]∘ p₁ (f2T[f] {U = U₁} {η D} (η (B ⇐ A) ▸ q) (sound f)) (π⇐-1 id ∘ (id ⊗ sound g)) 
  ． (refl ∘ (~ f2T[f]++ p₁ (η (B ⇐ A) ▸ q) (sound f))) ． (refl ∘ (~ lid)))) 
  ． ~ ass
soundcut {D = D} p f (⇐L {U = U} {A} {B} p₁ g h) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) = 
  soundcut (q ++ (sub q₁ (η B) ▸ q₂)) f h refl ∘ refl 
  ． (ass ． ((refl ∘ (lid ∘ refl 
  ． (f2T[f]◂▸ q q₁ q₂ (π⇐-1 id ∘ (id ⊗ sound g)) (sound f) 
  ． (refl ∘ ~ lid)))) ． ~ ass))
soundcut {D = D} p f (⇐L {U = U} {A} {B} p₁ g h) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 
  soundcut (q ++ (q₁ ◂ sub q₂ (η B))) f h refl ∘ refl 
  ． ((ass ． (((refl ∘ ((lid ∘ refl 
  ． ((~ f2T[f]◂▸ q q₁ q₂ (sound f) (π⇐-1 id ∘ (id ⊗ sound g))) 
  ． (refl ∘ ~ lid)))))) ． ~ ass)))
soundcut (p ◂ U) f (⊗R g h) refl = soundcut p f g refl ⊗ refl ． ((refl ∘ lid) ⊗ rid ． f⊗∘ ． (refl ∘ (~ lid)))
soundcut (T ▸ p) f (⊗R g h) refl = refl ⊗ soundcut p f h refl ． (rid ⊗ (refl ∘ lid) ． f⊗∘ ． (refl ∘ (~ lid)))
soundcut {D = D} p f (⊗L {A = A} {B} p₁ g) eq with subeq (η (A ⊗ B)) (η D) p₁ p eq
soundcut {D = D} p f (⊗L {A = A} {B} p₁ g) refl | 1≡2 (same refl refl refl) = 
  soundcut⊗L p f g
soundcut {D = D} p f (⊗L {A = A} {B} p₁ g) refl | 1/\2 (disj q q₁ q₂ refl refl refl refl) = 
  soundcut (q ++ (sub q₁ (η A ⊛ η B) ▸ q₂)) f g refl ∘ refl 
  ． (ass ． ((refl ∘ (lid ∘ refl ． (f2T[f]◂▸ q q₁ q₂ id (sound f) 
  ． (refl ∘ ~ lid)))) ． ~ ass))
soundcut {D = D} p f (⊗L {A = A} {B} p₁ g) refl | 2/\1 (disj q q₁ q₂ refl refl refl refl) = 
  soundcut (q ++ (q₁ ◂ sub q₂ (η A ⊛ η B))) f g refl ∘ refl 
  ． (ass ． ((refl ∘ (lid ∘ refl ． ((~ f2T[f]◂▸ q q₁ q₂ (sound f) id) 
  ． (refl ∘ ~ lid)))) ． ~ ass))
soundcut ∙ f ax refl = ~ (lid ． lid)

-- sound is a left inverse of complt.
soundcomplt : ∀ {A B} 
  → (f : A ⟶ B)
  → sound (complt f) ≐ f
soundcomplt (f ∘ g) = soundcut ∙ (complt g) (complt f) refl ． (soundcomplt f ∘ (lid ． soundcomplt g))
soundcomplt (f ⊗ g) = ~ rid ． soundcomplt f ⊗ soundcomplt g
soundcomplt (f ⇒ g) = 
  π⇒ (soundcomplt g ∘ (refl ∘ (soundcomplt f ⊗ refl))) 
  ． (π⇒(~ ass) ． (π⇒ANat ． (refl ∘ π⇒C 
  ． (refl ∘ (refl ∘ π⇒-1π⇒) ． (refl ∘ ~ rid ． (~ f⇒∘ ． lid ⇒ lid))))))
soundcomplt (f ⇐ g) = 
  π⇐ (soundcomplt f ∘ (refl ∘ (refl ⊗ soundcomplt g))) 
  ． (π⇐ (~ ass) ． (π⇐BNat ． (refl ∘ π⇐C 
  ． (refl ∘ (refl ∘ π⇐-1π⇐) ． (refl ∘ ~ rid ． (~ f⇐∘ ． lid ⇐ lid))))))
soundcomplt (π⇒ f) = 
  π⇒ (soundcut ∙ (⊗R axA axA) (complt f) refl 
  ． (soundcomplt f ∘ (lid ． sound-axA≐id ⊗ sound-axA≐id ． f⊗id) 
  ． (~ rid)))
soundcomplt (π⇒-1 f) = 
  ~ rid 
  ． (soundcut (∙ ◂ _)  axA (cut⇒L ∙ (complt f) axA axA) refl 
  ． (soundcut⇒L ∙ (complt f) axA axA ∘ refl 
  ． ((sound-axA≐id ∘ refl) ∘ (lid ． sound-axA≐id ⊗ refl ． f⊗id) 
  ． (~ rid ． lid 
  ． (refl ∘ (sound-axA≐id ⊗ soundcomplt f) 
  ． (π⇒-1B ． π⇒-1 lid))))))
soundcomplt (π⇐ f) = 
  π⇐ (soundcut ∙ (⊗R axA axA) (complt f) refl 
  ． (soundcomplt f ∘ (lid ． sound-axA≐id ⊗ sound-axA≐id ． f⊗id) 
  ． (~ rid)))
soundcomplt (π⇐-1 f) = 
  ~ rid 
  ． (soundcut⇐L ∙ (complt f) (cut ∙ axA axA refl) axA 
  ． (sound-axA≐id ∘ refl ． lid 
  ． (refl ∘ (soundcomplt f ⊗ (≗sound≐ (axA-cut-right-unit axA) ． sound-axA≐id)) 
  ． (π⇐-1A ． π⇐-1 lid))))
soundcomplt id = sound-axA≐id

-- soundcomplt {at x} id = refl
-- soundcomplt {A ⇒ B} id = {!   !}
-- soundcomplt {A ⇐ B} id = {!   !}
-- soundcomplt {A ⊗ B} id = ~ rid ． {!   !}    

-- soundcut⇒R-1 : ∀ {T A B} 
--   → {f : T ⊢ A ⇒ B}
--   → sound (⇒R-1 f) ≐ π⇒-1 (sound f)
-- soundcut⇒R-1 {f = f} = {!   !}

-- soundcut⇐R-1 : ∀ {T A B} 
--   → {f : T ⊢ B ⇐ A}
--   → sound (⇐R-1 f) ≐ π⇐-1 (sound f)
-- soundcut⇐R-1 {f = ⇐R f} = ~ π⇐π⇐-1
-- soundcut⇐R-1 {f = ⇒L p f g} = {!   !}
-- soundcut⇐R-1 {f = ⇐L p f g} = soundcut⇐R-1 {f = g} ∘ refl ． {!   !}
-- soundcut⇐R-1 {f = ⊗L p f} = soundcut⇐R-1 {f = f} ∘ refl ． {! sound f  !}      