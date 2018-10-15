module Syntax.Raw.Context where

open import Data.Product
open import Data.Nat
open import Data.Empty
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

data Ty : Set where
  _=>_ : Ty → Ty → Ty
infixr 5 _=>_

data Ctxt : Set where
  ◇ : Ctxt
  _#_ : Ctxt → Ty → Ctxt
infixl 7 _#_

Ctxtₗ = Ctxt

infixl 6 _++_
_++_ : Ctxt → Ctxt → Ctxt
Γ ++ ◇ = Γ
Γ ++ (Γ' # A) = (Γ ++ Γ') # A

clen : Ctxt → ℕ
clen ◇ = 0
clen (Γ # x) = suc (clen Γ)

infix 4 _[_]↦_
data _[_]↦_ : Ctxt → ℕ → Ty → Set where
  here : ∀{Γ A} → Γ # A [ zero ]↦ A
  there : ∀{Γ A B n} → Γ [ n ]↦ A → Γ # B [ suc n ]↦ A

↦lemma : ∀{n Γ A} → Γ [ n ]↦ A → n < clen Γ
↦lemma here = s≤s z≤n
↦lemma (there x) = s≤s (↦lemma x)

open import Utils

infix 4 _[_]ₗ↦_
data _[_]ₗ↦_ : Ctxtₗ → ℕ → Ty → Set where
  here : ∀{Γ A} → Γ # A [ clen Γ ]ₗ↦ A
  there : ∀{Γ A B n} → Γ [ n ]ₗ↦ A → Γ # B [ n ]ₗ↦ A

¬lenLemma : ∀{Γ n A} → Γ [ n ]ₗ↦ A → clen Γ ≤ n → ⊥
¬lenLemma here p = absurde _ _ p (≤refl _)
¬lenLemma (there x) p = ¬lenLemma x (<-to-≤ p)

≡lenLemma : ∀{Γ n A} → Γ [ n ]ₗ↦ A → n ≡ clen Γ → ⊥
≡lenLemma {Γ} x p rewrite p = ¬lenLemma x (≤refl _)

↦ₗlemma : ∀{n Γ A} → Γ [ n ]ₗ↦ A → n ≤ clen Γ
↦ₗlemma here = ≤succ (≤refl _)
↦ₗlemma (there x) = ≤trans (↦ₗlemma x) (≤succ (≤refl _))

++◇ : ∀ Θ → Θ ++ ◇ ≡ Θ
++◇ ◇ = refl
++◇ (Θ # A) rewrite ++◇ Θ = refl

++ₗ-lemma : ∀{Θ n A} Δ → Θ [ n ]ₗ↦ A → Θ ++ Δ [ n ]ₗ↦ A
++ₗ-lemma ◇ x = x
++ₗ-lemma (Δ # x₁) x = there (++ₗ-lemma Δ x)

swap++ : ∀ {A} Γ Δ → Γ # A ++ Δ ≡ Γ ++ (◇ # A ++ Δ)
swap++ Γ ◇ = refl
swap++ Γ (Δ # x) = cong (λ y → y # x) (swap++ Γ Δ)
expand↦ : ∀{Γ A n} → ∀ Γ' → Γ' [ n ]↦ A → (Γ ++ Γ') [ n ]↦ A
expand↦ ◇ ()
expand↦ (Γ' # x₁) here = here
expand↦ (Γ' # x₁) (there x) = there (expand↦ Γ' x)

cut-lemma : ∀{A} → ∀ Γ Δ n → Γ ++ Δ [ n ]↦ A → clen Δ > n → Δ [ n ]↦ A
cut-lemma Γ ◇ n x ()
cut-lemma Γ (Δ # x₁) .0 here p = here
cut-lemma Γ (Δ # x₁) .(suc _) (there x) (s≤s p) = there (cut-lemma Γ Δ _ x p)

l-maps-here : ∀{Θ A B} → Θ # A [ clen Θ ]ₗ↦ B → A ≡ B
l-maps-here here = refl
l-maps-here (there x) = ⊥-elim (≡lenLemma x refl)
