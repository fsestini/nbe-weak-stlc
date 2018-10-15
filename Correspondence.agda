module Correspondence where

open import Syntax.Raw
open import Syntax.Typed
open import Explicit.Equality
open import Implicit
open import Relation.Binary.PropositionalEquality hiding ([_])

--------------------------------------------------------------------------------

null-lsub' : ∀{Θ Γ A t s} → Θ ∷ Γ ⊢ t ∶ A → t ≡ t ⟨ clen Θ ↦ s ⟩
null-lsub' t = sym (null-lsub (metaTyClosed t))

record Factor (Θ : Ctxtₗ) (Γ : Ctxt) (t s : Term) (A : Ty) : Set where
  field
    {C a b} : Term
    {ty}    : Ty
    cder    : Θ # ty ∷ Γ ⊢ C ∶ A
    teq     : t ≡ C ⟨ clen Θ ↦ a ⟩
    seq     : s ≡ C ⟨ clen Θ ↦ b ⟩
    tyeq    : Θ ⊢ a ∼ b ∶ ty

factor : ∀{Θ Γ A t s} → Θ ∷ Γ ⊢ t ⟶ s ∶ A → Factor Θ Γ t s A
factor {Θ} (⟶β {B = B} {t} {s} td sd) =
  record
    { cder = free here ; teq = sym (sngl-msub (clen Θ))
    ; seq = sym (sngl-msub (clen Θ))
    ; tyeq = ∼β td sd
    }
factor (⟶ξ td) with factor td
factor (⟶ξ td) |
  record { cder = cder ; teq = teq ; seq = seq ; tyeq = tyeq } =
  record
    { cder = lam cder ; teq = cong lam teq ; seq = cong lam seq ; tyeq = tyeq }
factor (⟶compApp₁ rx sd) with factor rx
factor (⟶compApp₁ {s = s} rx sd) |
  record { cder = cder ; teq = teq ; seq = seq ; tyeq = tyeq } =
  record
    { cder = cder ● wkMeta (◇ # _) sd ; tyeq = tyeq
    ; teq = cong₂ _·_ teq (null-lsub' sd) 
    ; seq = cong₂ _·_ seq (null-lsub' sd) }
factor (⟶compApp₂ rd rx) with factor rx
factor (⟶compApp₂ {r = r} rd rx) |
  record { cder = cder ; teq = teq ; seq = seq ; tyeq = tyeq } =
  record
    { cder = wkMeta (◇ # _) rd ● cder ; tyeq = tyeq
    ; teq = cong₂ _·_ (null-lsub' rd) teq ; seq = cong₂ _·_ (null-lsub' rd) seq }

convert∼ : ∀{Θ A t s} → Θ ∷ ◇ ⊢ t ∼ s ∶ A → Θ ⊢ t ∼ s ∶ A
convert∼ (∼refl x) = ∼refl x
convert∼ (∼symm eq) = ∼symm (convert∼ eq)
convert∼ (∼trans eq eq₁) = ∼trans (convert∼ eq) (convert∼ eq₁)
convert∼ (~⟶ x) with factor x
convert∼ (~⟶ x) |
  record { cder = cder ; teq = teq ; seq = seq ; tyeq = tyeq }
  rewrite teq | seq = ∼sub cder tyeq

--------------------------------------------------------------------------------

convert : ∀{Θ A t s} → Θ ⊢ t ∼ s ∶ A → Θ ∷ ◇ ⊢ t ∼ s ∶ A
convert (∼refl x) = ∼refl x
convert (∼symm eq) = ∼symm (convert eq)
convert (∼trans eq eq₁) = ∼trans (convert eq) (convert eq₁)
convert (∼β x x₁) = ~⟶ (⟶β x x₁)
convert (∼sub td ab) = ⊢lsub td (convert ab)

--------------------------------------------------------------------------------

std-to-target : ∀{Θ A t s} → Θ ∷ ◇ ⊢ t ∼ s ∶ A → Θ ⊢ t ∼ s ∶ A
std-to-target eq = convert∼ eq

target-to-std : ∀{Θ A t s} → Θ ⊢ t ∼ s ∶ A → Θ ∷ ◇ ⊢ t ∼ s ∶ A
target-to-std eq = convert eq
