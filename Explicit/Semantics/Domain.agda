module Explicit.Semantics.Domain where

open import Syntax.Raw
open import Syntax.Typed
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Data.Product renaming (_,_ to _,,_)
open import Data.List

D = Term

Rnf : D → Term
Rnf x = x

-- data Env : Set where
--   em : Env
--   ex : Env → {d : D} → Tm 0 d → Env

-- envLen : Env → ℕ
-- envLen em = zero
-- envLen (ex e x) = suc (envLen e)

-- env-to-sub : Env → Σ MetaSubst λ σ → ClosedMS σ
-- env-to-sub em = ⟨⟩ ,, cmsEmpty
-- env-to-sub (ex ρ {d} x) = _ ,, (cmsCons (proj₂ (env-to-sub ρ)) x)

-- esLen : (e : Env) → envLen e ≡ msLen (proj₁ (env-to-sub e))
-- esLen em = refl
-- esLen (ex e x) = cong suc (esLen e)

-- ⟦_⟧ : Term → Env → D
-- ⟦ t ⟧ δ = msub t (proj₁ (env-to-sub δ))

-- ⟦_⟧_↘_ : Term → Env → D → Set
-- ⟦ t ⟧ δ ↘ d = Eval ⟦ t ⟧ δ ↘ d

-- ⟦⟧fun : ∀{t a b δ} → ⟦ t ⟧ δ ↘ a → ⟦ t ⟧ δ ↘ b → a ≡ b
-- ⟦⟧fun e1 e2 = Eval-fun e1 e2

_[_]↘_ : Term → Subst → Term → Set
t [ σ ]↘ a = Eval sub t σ ↘ a

-- idenv : (Θ : Ctxt) → Env
-- idenv ◇ = em
-- idenv (Θ # A) = ex (idenv Θ) {Free (clen Θ)} tmFree
