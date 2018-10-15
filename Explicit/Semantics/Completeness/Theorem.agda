module Explicit.Semantics.Completeness.Theorem where

open import Syntax.Raw
open import Syntax.Typed
open import Explicit.Equality
open import Data.Nat
open import Data.Maybe
open import Explicit.Semantics.Domain
open import Explicit.Semantics.Completeness.SemanticType
open import Data.Product renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality

open SemTy
open _∈_
open ⟦_⟧≃⟦_⟧_∈tm_
open import Relation.Nullary
open import Data.Empty
open import Function

models-app : ∀{A B Γ t s} → Γ ⊧ t ∶ A => B → Γ ⊧ s ∶ A → Γ ⊧ t · s ∶ B
models-app {A} {B} ht hs ρ = tmAppLemma {A} {B} (ht ρ) (hs ρ)

models-lam : ∀{A B Γ t} → Γ # A ⊧ t ∶ B → Γ ⊧ lam t ∶ A => B
models-lam {A} {B} ht ρ = tmLamLemma {A} {B} (λ x → ht (cCons (cWk ρ) (wit x)))

models-var : ∀{A Γ n} → Γ [ n ]↦ A → Γ ⊧ bvar n ∶ A
models-var () cId
models-var {A} here (cCons ρ y) = ⟨ in∈ y ∣ aux ∣ aux ⟩
  where aux = nfSelf (isNf ⟦ A ⟧ₜ y)
models-var (there x) (cCons ρ y) with models-var x ρ
models-var (there x) (cCons ρ y) | ⟨ tm ∣ e1 ∣ e2 ⟩ = ⟨ tm ∣ e1 ∣ e2 ⟩
models-var x (cWk ρ) with models-var x ρ
models-var {A} x (cWk {w = w} ρ) | ⟨ tm ∣ e1 ∣ e2 ⟩ = 
  ⟨ liftD {A} {w} tm ∣ wkEval e1 ∣ wkEval e2 ⟩

models : ∀{Θ Γ A t} → Θ ∷ Γ ⊢ t ∶ A → Γ ⊧ t ∶ A
models = model (record
  { _∷_⊧_∶_ = const _⊧_∶_
  ; M-free = λ { {A = A} _ _ → ⟨ in∈ (hasNe ⟦ A ⟧ₜ neFree) ∣ eFree ∣ eFree ⟩ }
  ; M-var = models-var
  ; M-lam = λ { {A = A} {B} → models-lam {A} {B} }
  ; M-● = λ { {A = A} {B} → models-app {A} {B} }
  })

models⟶ : ∀{Θ Γ A t s} → Θ ∷ Γ ⊢ t ⟶ s ∶ A → Γ ⊧ t ≃ s ∶ A
models⟶ (⟶β {A = A} {B = B} t s) ρ =
  tmβLemma {A = A} {B} (models (wkTerm (lam t)) ρ) (models (wkTerm s) ρ)
           (tyClosed t) (tyClosed s)
models⟶ (⟶ξ {A = A} {B = B} eq) ρ =
  tmLamLemma {A} {B} λ x → (models⟶ eq) (cCons (cWk ρ) (wit x))
models⟶ (⟶compApp₁ {A = A} {B} red x) ρ =
  tmAppLemma {A} {B} (models⟶ red ρ) (models x ρ)
models⟶ (⟶compApp₂ {A = A} {B} x red) ρ =
  tmAppLemma {A} {B} (models x ρ) (models⟶ red ρ)

models∼ : ∀{Θ Γ A t s} → Θ ∷ Γ ⊢ t ∼ s ∶ A → Γ ⊧ t ≃ s ∶ A
models∼ (~⟶ x) = models⟶ x
models∼ (∼refl x) ρ = models x ρ
models∼ (∼symm eq) ρ = ⟨ ∈tm ih ∣ ↘tm2 ih ∣ ↘tm1 ih ⟩ where ih = models∼ eq ρ
models∼ (∼trans eq eq') ρ =
  ⟨ ∈tm ih ∣ ↘tm1 ih ∣ ≡Eval refl (Eval-fun (↘tm1 ih') (↘tm2 ih)) (↘tm2 ih') ⟩
  where ih = models∼ eq ρ ; ih' = models∼ eq' ρ

--------------------------------------------------------------------------------
-- Normalization function

std : (Γ : Ctxt) → idsub Γ ∈ₛ ⟦ Γ ⟧ₛ
std ◇ = cId
std (Γ # A) = cCons (cWk (std Γ)) (SemTy.hasNe ⟦ A ⟧ₜ neBound)

nf : ∀{Θ Γ A t} → Θ ∷ Γ ⊢ t ∶ A → Term
nf {Θ} {Γ} td = d aux where aux = models td (std Γ)

completeness : ∀{Θ Γ A t s} → Θ ∷ Γ ⊢ t ∼ s ∶ A
             → (td : Θ ∷ Γ ⊢ t ∶ A) → (sd : Θ ∷ Γ ⊢ s ∶ A)
             → nf td ≡ nf sd
completeness {Θ} {Γ} eq td sd =
  trans (Eval-fun (↘tm1 aux-t) (↘tm1 aux)) (Eval-fun (↘tm2 aux) (↘tm2 aux-s))
  where aux-t = models td (std Γ) ; aux-s = models sd (std Γ)
        aux = models∼ eq (std Γ)
