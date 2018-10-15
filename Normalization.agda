module Normalization where

open import Syntax.Raw
open import Syntax.Typed
open import Explicit.Equality
open import Explicit.Semantics
open import Implicit
open import Correspondence
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_)

open ⟦_⟧≃⟦_⟧_∈tm_

-- Normalization for the explicit calculus is an immediate consequence
-- of completeness of NbE (which gives us 'nf td', the first component
-- of the Σ type) and soundness of NbE (which gives us convertibility,
-- i.e. the second component of the Σ type)
normalizationᵉ : ∀{Θ Γ A t}
               → Θ ∷ Γ ⊢ t ∶ A
               → Σ Term λ t' → Θ ∷ Γ ⊢ t ∼ t' ∶ A
normalizationᵉ td = nf td ,, soundness td

-- Normalization for the implicit calculus is an immediate consequence
-- of normalization for the explicit calculus, and its equivalence
-- with the implicit one.
normalizationⁱ : ∀{Γ A t}
               → Γ ⊢ t ∶ A
               → Σ Term λ t' → Γ ⊢ t ∼ t' ∶ A
normalizationⁱ td =
  let (t' ,, p) = normalizationᵉ td in t' ,, std-to-target p
