module Syntax.Raw.Equality where

open import Syntax.Raw.Term
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Utils
open import Data.Nat
open import Data.Empty

dec≡ : (t s : Term) → Dec (t ≡ s)
dec≡ (fvar x) (fvar y) with x ≟ y
dec≡ (fvar x) (fvar y) | yes p = yes (cong fvar p)
dec≡ (fvar x) (fvar y) | no ¬p = no (λ { refl → ¬p refl })
dec≡ (fvar x) (bvar y) = no (λ ())
dec≡ (fvar x) (lam s) = no (λ ())
dec≡ (fvar x) (s · s₁) = no (λ ())
dec≡ (bvar x) (fvar x₁) = no (λ ())
dec≡ (bvar x) (bvar y) with x ≟ y
dec≡ (bvar x) (bvar y) | yes p = yes (cong bvar p)
dec≡ (bvar x) (bvar y) | no ¬p = no (λ { refl → ¬p refl })
dec≡ (bvar x) (lam s) = no (λ ())
dec≡ (bvar x) (s · s₁) = no (λ ())
dec≡ (lam t) (fvar x) = no (λ ())
dec≡ (lam t) (bvar x) = no (λ ())
dec≡ (lam t) (lam s) with dec≡ t s
dec≡ (lam t) (lam s) | yes p = yes (cong lam p)
dec≡ (lam t) (lam s) | no ¬p = no (λ { refl → ¬p refl })
dec≡ (lam t) (s · s₁) = no (λ ())
dec≡ (t · t₁) (fvar x) = no (λ ())
dec≡ (t · t₁) (bvar x) = no (λ ())
dec≡ (t · t₁) (lam s) = no (λ ())
dec≡ (t · s) (t' · s') with dec≡ t t' | dec≡ s s'
dec≡ (t · s) (t' · s') | yes p | yes q = yes (cong₂ _·_ p q)
dec≡ (t · s) (t' · s') | yes p | no ¬p = no (λ { refl → ¬p refl })
dec≡ (t · s) (t' · s') | no ¬p | yes p = no (λ { refl → ¬p refl })
dec≡ (t · s) (t' · s') | no ¬p | no ¬q = no (λ { refl → ¬q refl })
