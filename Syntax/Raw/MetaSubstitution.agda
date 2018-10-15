module Syntax.Raw.MetaSubstitution where

open import Data.Sum
open import Data.Empty
open import Function
open import Utils
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Syntax.Raw.Context
open import Syntax.Raw.Term
open import Syntax.Raw.Substitution

_⟨_↦_⟩ : Term → ℕ → Term → Term
fvar x ⟨ n ↦ a ⟩ with x ≟ n
fvar x ⟨ n ↦ a ⟩ | yes p = a
fvar x ⟨ n ↦ a ⟩ | no ¬p = fvar x
bvar x ⟨ n ↦ a ⟩ = bvar x
lam t ⟨ n ↦ a ⟩ = lam (t ⟨ n ↦ a ⟩)
(t · s) ⟨ n ↦ a ⟩ = t ⟨ n ↦ a ⟩ · s ⟨ n ↦ a ⟩

sngl-msub : ∀ {s} n → fvar n ⟨ n ↦ s ⟩ ≡ s
sngl-msub n with n ≟ n
sngl-msub n | yes p = refl
sngl-msub n | no ¬p = ⊥-elim (¬p refl)

null-lsub : ∀{n t s} → Szₗ n t → t ⟨ n ↦ s ⟩ ≡ t
null-lsub (tmlFree {n} {x} p) with x ≟ suc n
null-lsub (tmlFree {n} {x} p) | yes p₁ rewrite p₁ =
  ⊥-elim (absurde _ _ p (≤refl _))
null-lsub (tmlFree {n} {x} p) | no ¬p = refl
null-lsub tmlVar = refl
null-lsub (tmlLam tm) = cong lam (null-lsub tm)
null-lsub (tmlApp tm tm₁) = cong₂ _·_ (null-lsub tm) (null-lsub tm₁)
