module Explicit.Equality where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product renaming (_,_ to _,,_)
open import Data.Nat
open import Relation.Nullary
open import Data.Empty

open import Syntax.Raw
open import Syntax.Typed

infix 4 _∷_⊢_⟶_∶_
data _∷_⊢_⟶_∶_ : Ctxtₗ → Ctxt → Term → Term → Ty → Set where

  ⟶β : ∀{Θ Γ A B t s}
       → Θ ∷ ◇ # A ⊢ t ∶ B → Θ ∷ ◇ ⊢ s ∶ A
       → Θ ∷ Γ ⊢ lam t · s ⟶ t [ s ] ∶ B

  ⟶ξ : ∀{Θ Γ A B t t'}
       → Θ ∷ Γ # A ⊢ t ⟶ t' ∶ B
       → Θ ∷ Γ ⊢ lam t ⟶ lam t' ∶ A => B

  ⟶compApp₁  : ∀{Γ Γ' r r' s A B}
               → Γ ∷ Γ' ⊢ r ⟶ r' ∶ A => B → Γ ∷ Γ' ⊢ s ∶ A
               → Γ ∷ Γ' ⊢ r · s ⟶ r' · s ∶ B

  ⟶compApp₂  : ∀{Γ Γ' r s s' A B}
               → Γ ∷ Γ' ⊢ r ∶ A => B → Γ ∷ Γ' ⊢ s ⟶ s' ∶ A
               → Γ ∷ Γ' ⊢ r · s ⟶ r · s' ∶ B

infix 4 _∷_⊢_∼_∶_
data _∷_⊢_∼_∶_ : Ctxtₗ → Ctxt → Term → Term → Ty → Set where

  ~⟶ : ∀{Γ Γ' t s A} -> Γ ∷ Γ' ⊢ t ⟶ s ∶ A → Γ ∷ Γ' ⊢ t ∼ s ∶ A

  ∼refl  : ∀{Γ Γ' t A} → Γ ∷ Γ' ⊢ t ∶ A → Γ ∷ Γ' ⊢ t ∼ t ∶ A
  ∼symm  : ∀{Γ Γ' t s A} → Γ ∷ Γ' ⊢ t ∼ s ∶ A → Γ ∷ Γ' ⊢ s ∼ t ∶ A
  ∼trans : ∀{Γ Γ' t s w A} → Γ ∷ Γ' ⊢ t ∼ s ∶ A → Γ ∷ Γ' ⊢ s ∼ w ∶ A
         → Γ ∷ Γ' ⊢ t ∼ w ∶ A

--------------------------------------------------------------------------------

⟶lemma : ∀{Θ Γ A t s} → Θ ∷ Γ ⊢ t ⟶ s ∶ A → Θ ∷ Γ ⊢ t ∶ A × Θ ∷ Γ ⊢ s ∶ A
⟶lemma (⟶β x x₁) = wkTerm (lam x ● x₁) ,, wkTerm (⊢sub x (⊢Cons ⊢Id x₁))
⟶lemma (⟶ξ red) = lam (proj₁ (⟶lemma red)) ,, lam (proj₂ (⟶lemma red))
⟶lemma (⟶compApp₁ red x) = proj₁ (⟶lemma red) ● x ,, proj₂ (⟶lemma red) ● x
⟶lemma (⟶compApp₂ x red) = x ● proj₁ (⟶lemma red) ,, x ● proj₂ (⟶lemma red)

∼lemma : ∀{Θ Γ A t s} → Θ ∷ Γ ⊢ t ∼ s ∶ A → Θ ∷ Γ ⊢ t ∶ A × Θ ∷ Γ ⊢ s ∶ A
∼lemma (~⟶ x) = ⟶lemma x
∼lemma (∼refl x) = x ,, x
∼lemma (∼symm eq) = proj₂ (∼lemma eq) ,, proj₁ (∼lemma eq)
∼lemma (∼trans eq eq₁) = proj₁ (∼lemma eq) ,, proj₂ (∼lemma eq₁)

-- Lemmas asserting that reducible/convertible terms have the same "size".
mutual

  sameSz⟶LR : ∀{Θ Γ Δ A t s}
              → Θ ∷ Δ ++ Γ ⊢ t ⟶ s ∶ A → Sz (clen Γ) t → Sz (clen Γ) s
  sameSz⟶LR {_} {Γ} (⟶β x x₁) (tmApp (tmLam tm) tm₁) =
    sub-cover-lemma (clen Γ) 0 tm tm₁
  sameSz⟶LR (⟶ξ eq) (tmLam tm) = tmLam (sameSz⟶LR eq tm)

  sameSz⟶LR (⟶compApp₁ red x) (tmApp tm tm₁) = tmApp (sameSz⟶LR red tm) tm₁
  sameSz⟶LR (⟶compApp₂ x red) (tmApp tm tm₁) = tmApp tm (sameSz⟶LR red tm₁)

  sameSz⟶RL : ∀{Θ Γ Δ A t s}
              → Θ ∷ Δ ++ Γ ⊢ t ⟶ s ∶ A → Sz (clen Γ) s → Sz (clen Γ) t
  sameSz⟶RL (⟶β x x₁) tm = liftSz _ (tmApp (tmLam (tyClosed x)) (tyClosed x₁))
  sameSz⟶RL (⟶ξ eq) (tmLam tm) = tmLam (sameSz⟶RL eq tm)
  sameSz⟶RL (⟶compApp₁ red x) (tmApp tm tm₁) = tmApp (sameSz⟶RL red tm) tm₁
  sameSz⟶RL (⟶compApp₂ x red) (tmApp tm tm₁) = tmApp tm (sameSz⟶RL red tm₁)

  sameSz∼LR : ∀{Θ Γ Δ A t s}
            → Θ ∷ Δ ++ Γ ⊢ t ∼ s ∶ A → Sz (clen Γ) t → Sz (clen Γ) s
  sameSz∼LR (~⟶ x) tm = sameSz⟶LR x tm
  sameSz∼LR (∼refl x) tm = tm
  sameSz∼LR (∼symm eq) tm = sameSz∼RL eq tm
  sameSz∼LR (∼trans eq eq₁) tm = sameSz∼LR eq₁ (sameSz∼LR eq tm)

  sameSz∼RL : ∀{Θ Γ Δ A t s}
            → Θ ∷ Δ ++ Γ ⊢ t ∼ s ∶ A → Sz (clen Γ) s → Sz (clen Γ) t
  sameSz∼RL (~⟶ x) tm = sameSz⟶RL x tm
  sameSz∼RL (∼refl x) tm = tm
  sameSz∼RL (∼symm eq) tm = sameSz∼LR eq tm
  sameSz∼RL (∼trans eq eq₁) tm = sameSz∼RL eq (sameSz∼RL eq₁ tm)

≡to∼R : ∀{Θ Γ A t s s'} → s ≡ s' → Θ ∷ Γ ⊢ t ∼ s ∶ A → Θ ∷ Γ ⊢ t ∼ s' ∶ A
≡to∼R refl eq = eq

≡to∼L : ∀{Θ Γ A t t' s} → t ≡ t' → Θ ∷ Γ ⊢ t ∼ s ∶ A → Θ ∷ Γ ⊢ t' ∼ s ∶ A
≡to∼L refl eq = eq

≡∼ : ∀{Θ Θ' Γ Δ A A' t t' s s'}
   → Θ ∷ Γ ⊢ t ∼ s ∶ A
   → Θ ≡ Θ' → Γ ≡ Δ → A ≡ A' → t ≡ t' → s ≡ s'
   → Θ' ∷ Δ ⊢ t' ∼ s' ∶ A'
≡∼ eq refl refl refl refl refl = eq

≡⟶ : ∀{Θ Θ' Γ Δ A A' t t' s s'}
   → Θ ∷ Γ ⊢ t ⟶ s ∶ A
   → Θ ≡ Θ' → Γ ≡ Δ → A ≡ A' → t ≡ t' → s ≡ s'
   → Θ' ∷ Δ ⊢ t' ⟶ s' ∶ A'
≡⟶ eq refl refl refl refl refl = eq

-- --------------------------------------------------------------------------------
-- -- Meta weakening

-- wkₗ⟶ : ∀{Θ Γ A t s} Δ → Θ ∷ Γ ⊢ t ⟶ s ∶ A → Θ ++ Δ ∷ Γ ⊢ t ⟶ s ∶ A
-- wkₗ⟶ Δ (⟶β td sd) = ⟶β (wkMeta Δ td) (wkMeta Δ sd)
-- wkₗ⟶ Δ (⟶ξ red) = ⟶ξ (wkₗ⟶ Δ red)
-- wkₗ⟶ Δ (⟶compApp₁ red x) = ⟶compApp₁ (wkₗ⟶ Δ red) (wkMeta Δ x)
-- wkₗ⟶ Δ (⟶compApp₂ x red) = ⟶compApp₂ (wkMeta Δ x) (wkₗ⟶ Δ red)

-- wkₗ∼ : ∀{Θ Γ A t s} Δ → Θ ∷ Γ ⊢ t ∼ s ∶ A → Θ ++ Δ ∷ Γ ⊢ t ∼ s ∶ A
-- wkₗ∼ Δ (~⟶ x) = ~⟶ (wkₗ⟶ Δ x)
-- wkₗ∼ Δ (∼refl x) = ∼refl (wkMeta Δ x)
-- wkₗ∼ Δ (∼symm eq) = ∼symm (wkₗ∼ Δ eq)
-- wkₗ∼ Δ (∼trans eq eq₁) = ∼trans (wkₗ∼ Δ eq) (wkₗ∼ Δ eq₁)

--------------------------------------------------------------------------------
-- Weakening

⟶wk : ∀{Θ Γ Δ A t s w} → Δ ⊢ᵣ w ∶ Γ
      → Θ ∷ Γ ⊢ t ⟶ s ∶ A → Θ ∷ Δ ⊢ wk t w ⟶ wk s w ∶ A
⟶wk w (⟶β td sd) = ≡⟶ (⟶β td sd) refl refl refl
  (sym (null-wk (tmApp (tmLam (tyClosed td)) (tyClosed sd))))
  (sym (null-wk (sub-cover-lemma 0 0 (tyClosed td) (tyClosed sd))))
⟶wk w (⟶ξ red) = ⟶ξ (⟶wk (⊢Skip w) red)
⟶wk w (⟶compApp₁ red x) = ⟶compApp₁ (⟶wk w red) (⊢wk x w)
⟶wk w (⟶compApp₂ x red) = ⟶compApp₂ (⊢wk x w) (⟶wk w red)

∼wk : ∀{Θ Γ Δ A t s w} → Δ ⊢ᵣ w ∶ Γ
    → Θ ∷ Γ ⊢ t ∼ s ∶ A → Θ ∷ Δ ⊢ wk t w ∼ wk s w ∶ A
∼wk w (~⟶ x) = ~⟶ (⟶wk w x)
∼wk w (∼refl x) = ∼refl (⊢wk x w)
∼wk w (∼symm eq) = ∼symm (∼wk w eq)
∼wk w (∼trans eq eq₁) = ∼trans (∼wk w eq) (∼wk w eq₁)

wk⟶ : ∀{Θ Γ Δ A t s} → Θ ∷ Γ ⊢ t ⟶ s ∶ A → Θ ∷ Δ ++ Γ ⊢ t ⟶ s ∶ A
wk⟶ (⟶β x x₁) = ⟶β x x₁
wk⟶ (⟶ξ eq) = ⟶ξ (wk⟶ eq)
wk⟶ (⟶compApp₁ red x) = ⟶compApp₁ (wk⟶ red) (wkTerm x)
wk⟶ (⟶compApp₂ x red) = ⟶compApp₂ (wkTerm x) (wk⟶ red)

wk∼ : ∀{Θ Γ Δ A t s} → Θ ∷ Γ ⊢ t ∼ s ∶ A → Θ ∷ Δ ++ Γ ⊢ t ∼ s ∶ A
wk∼ (~⟶ x) = ~⟶ (wk⟶ x)
wk∼ (∼refl x) = ∼refl (wkTerm x)
wk∼ (∼symm eq) = ∼symm (wk∼ eq)
wk∼ (∼trans eq eq₁) = ∼trans (wk∼ eq) (wk∼ eq₁)

--------------------------------------------------------------------------------
-- Derived equalities

-- Computation rules
~β : ∀{Θ Γ A B t s}
   → Θ ∷ ◇ # A ⊢ t ∶ B → Θ ∷ ◇ ⊢ s ∶ A
   → Θ ∷ Γ ⊢ (lam t · s) ∼ sub t (Id , s) ∶ B
~β td sd = ~⟶ (⟶β td sd)

-- Compatibility rules
∼ξ : ∀{Θ Γ A B t t'} → Θ ∷ Γ # A ⊢ t ∼ t' ∶ B → Θ ∷ Γ ⊢ lam t ∼ lam t' ∶ A => B
∼ξ (~⟶ x) = ~⟶ (⟶ξ x)
∼ξ (∼refl x) = ∼refl (lam x)
∼ξ (∼symm eq) = ∼symm (∼ξ eq)
∼ξ (∼trans eq eq₁) = ∼trans (∼ξ eq) (∼ξ eq₁)

∼compApp₁  : ∀{Γ Γ' r r' s A B}
           → Γ ∷ Γ' ⊢ r ∼ r' ∶ A => B → Γ ∷ Γ' ⊢ s ∶ A
           → Γ ∷ Γ' ⊢ r · s ∼ r' · s ∶ B
∼compApp₁ (~⟶ x₁) x = ~⟶ (⟶compApp₁ x₁ x)
∼compApp₁ (∼refl x₁) x = ∼refl (x₁ ● x)
∼compApp₁ (∼symm eq) x = ∼symm (∼compApp₁ eq x)
∼compApp₁ (∼trans eq eq₁) x = ∼trans (∼compApp₁ eq x) (∼compApp₁ eq₁ x)

∼compApp₂  : ∀{Γ Γ' r s s' A B}
           → Γ ∷ Γ' ⊢ r ∶ A => B → Γ ∷ Γ' ⊢ s ∼ s' ∶ A
           → Γ ∷ Γ' ⊢ r · s ∼ r · s' ∶ B
∼compApp₂ x (~⟶ x₁) = ~⟶ (⟶compApp₂ x x₁)
∼compApp₂ x (∼refl x₁) = ∼refl (x ● x₁)
∼compApp₂ x (∼symm eq) = ∼symm (∼compApp₂ x eq)
∼compApp₂ x (∼trans eq eq₁) = ∼trans (∼compApp₂ x eq) (∼compApp₂ x eq₁)

∼compApp : ∀{Γ Γ' r r' s s' A B}
         → Γ ∷ Γ' ⊢ r ∼ r' ∶ A => B → Γ ∷ Γ' ⊢ s ∼ s' ∶ A
         → Γ ∷ Γ' ⊢ r · s ∼ r' · s' ∶ B
∼compApp eq eq' =
  ∼trans (∼compApp₁ eq (proj₁ (∼lemma eq'))) (∼compApp₂ (proj₂ (∼lemma eq)) eq')

⊢lsub : ∀{Θ Γ A B t a b}
      → Θ # A ∷ Γ ⊢ t ∶ B → Θ ∷ ◇ ⊢ a ∼ b ∶ A
      → Θ ∷ Γ ⊢ t ⟨ clen Θ ↦ a ⟩ ∼ t ⟨ clen Θ ↦ b ⟩ ∶ B
⊢lsub {Θ} (free {n = n} x) eq with n ≟ clen Θ
⊢lsub (free x) eq | yes p rewrite p | l-maps-here x = wk∼ eq
⊢lsub {Θ} (free {n = .(clen Θ)} here) eq | no ¬p = ⊥-elim (¬p refl)
⊢lsub {Θ} (free {n = n} (there x)) eq | no ¬p = ∼refl (free x)
⊢lsub (var x) eq = ∼refl (var x)
⊢lsub (lam td) eq = ∼ξ (⊢lsub td eq)
⊢lsub (td ● sd) eq = ∼compApp (⊢lsub td eq) (⊢lsub sd eq)
