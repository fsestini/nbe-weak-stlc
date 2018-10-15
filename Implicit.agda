module Implicit where

open import Data.Nat
open import Relation.Nullary
open import Utils

open import Syntax.Raw
open import Syntax.Typed

infix 4 _⊢_∶_
_⊢_∶_ : Ctxt → Term → Ty → Set
Γ ⊢ t ∶ A = Γ ∷ ◇ ⊢ t ∶ A

mutual

  infix 4 _⊢_∼_∶_
  data _⊢_∼_∶_ : Ctxt → Term → Term → Ty → Set where

    ∼refl  : ∀{Γ t A} → Γ ⊢ t ∶ A → Γ ⊢ t ∼ t ∶ A
    ∼symm  : ∀{Γ t s A} → Γ ⊢ t ∼ s ∶ A → Γ ⊢ s ∼ t ∶ A
    ∼trans : ∀{Γ t s w A}
           → Γ ⊢ t ∼ s ∶ A
           → Γ ⊢ s ∼ w ∶ A
           → Γ ⊢ t ∼ w ∶ A

    ∼β : ∀{Γ A B t s}
       → Γ ∷ ◇ # A ⊢ t ∶ B → Γ ⊢ s ∶ A
       → Γ ⊢ lam t · s ∼ t [ s ] ∶ B

    ∼sub   : ∀{Γ A B t a b} → Γ # A ⊢ t ∶ B → Γ ⊢ a ∼ b ∶ A
           → Γ ⊢ t ⟨ clen Γ ↦ a ⟩ ∼ t ⟨ clen Γ ↦ b ⟩ ∶ B
