module Syntax.Typed where

open import Function
open import Utils
open import Data.Nat
open import Relation.Binary.PropositionalEquality

open import Syntax.Raw

mutual
  infix 4 _∷_⊢_∶_
  data _∷_⊢_∶_ : Ctxtₗ → Ctxt → Term → Ty → Set where
    free : ∀{Θ Γ A n} → Θ [ n ]ₗ↦ A → Θ ∷ Γ ⊢ fvar n ∶ A
    var  : ∀{Γ Γ' A n} → Γ' [ n ]↦ A → Γ ∷ Γ' ⊢ bvar n ∶ A
    lam  : ∀{Θ Γ A B t} → Θ ∷ Γ # A ⊢ t ∶ B → Θ ∷ Γ ⊢ lam t ∶ A => B
    _●_  : ∀{Θ Γ A B t s} → Θ ∷ Γ ⊢ t ∶ A => B → Θ ∷ Γ ⊢ s ∶ A
         → Θ ∷ Γ ⊢ t · s ∶ B
  infixl 5 _●_

record Model : Set₁ where
  field
    _∷_⊧_∶_ : Ctxtₗ → Ctxt → Term → Ty → Set

    M-free : ∀{Θ Γ A n} → Θ [ n ]ₗ↦ A → Θ ∷ Γ ⊧ fvar n ∶ A
    M-var  : ∀{Γ Γ' A n} → Γ' [ n ]↦ A → Γ ∷ Γ' ⊧ bvar n ∶ A
    M-lam  : ∀{Θ Γ A B t} → Θ ∷ Γ # A ⊧ t ∶ B → Θ ∷ Γ ⊧ lam t ∶ (A => B)
    M-●    : ∀{Θ Γ A B t s} → Θ ∷ Γ ⊧ t ∶ (A => B) → Θ ∷ Γ ⊧ s ∶ A
           → Θ ∷ Γ ⊧ t · s ∶ B
  infix 4 _∷_⊧_∶_
open Model

model : ∀{Θ Γ A t} → (M : Model) → Θ ∷ Γ ⊢ t ∶ A → _∷_⊧_∶_ M Θ Γ t A
model M (free x) = M-free M x
model M (var x) = M-var M x
model M (lam td) = M-lam M (model M td)
model M (td ● sd) = M-● M (model M td) (model M sd)

≡tm : ∀{Θ Θ' Γ Γ' t t' A A'}
    → Θ ≡ Θ' → Γ ≡ Γ' → t ≡ t' → A ≡ A'
    → Θ' ∷ Γ' ⊢ t' ∶ A' → Θ ∷ Γ ⊢ t ∶ A
≡tm refl refl refl refl tm = tm

tyClosed : ∀{Θ Γ t A} → Θ ∷ Γ ⊢ t ∶ A → Sz (clen Γ) t
tyClosed = model record
  { _∷_⊧_∶_ = λ Θ Γ t A → Sz (clen Γ) t ; M-free = λ _ → tmFree
  ; M-var = λ { {_} {◇} () ; {_} {_ # _} x → tmVar (inv-≤ (↦lemma x)) }
  ; M-lam = tmLam ; M-● = tmApp }

⊢shrink : ∀{Θ Δ Γ A t} → Θ ∷ Δ ++ Γ ⊢ t ∶ A → Sz (clen Γ) t
        → Θ ∷ Γ ⊢ t ∶ A
⊢shrink (free x) tm = free x
⊢shrink {Γ = ◇} (var x) ()
⊢shrink {Δ = Δ} {Γ # B} (var {A = A} x) (tmVar p) =
  var (cut-lemma {A} Δ (Γ # B) _ x (≤suc> _ _ p))
⊢shrink (lam t) (tmLam tm) = lam (⊢shrink t tm)
⊢shrink (t ● s) (tmApp tm tm₁) = ⊢shrink t tm ● ⊢shrink s tm₁

metaTyClosed : ∀{Θ Γ t A} → Θ ∷ Γ ⊢ t ∶ A → Szₗ (clen Θ) t
metaTyClosed = model record
  { _∷_⊧_∶_ = λ Θ _ t _ → Szₗ (clen Θ) t
  ; M-free = λ { here → tmlFree (≤refl _) ; (there x) → tmlFree (↦ₗlemma x) }
  ; M-var = λ _ → tmlVar ; M-lam = tmlLam ; M-● = tmlApp }

wkMeta : ∀{Θ Γ A t} Δ → Θ ∷ Γ ⊢ t ∶ A → Θ ++ Δ ∷ Γ ⊢ t ∶ A
wkMeta Δ = model record
  { _∷_⊧_∶_ = λ Θ Γ t A → Θ ++ Δ ∷ Γ ⊢ t ∶ A
  ; M-free = free ∘ ++ₗ-lemma Δ ; M-var = var ; M-lam = lam ; M-● = _●_
  }

wkTerm : ∀{Θ Γ Δ A t} → Θ ∷ Γ ⊢ t ∶ A → Θ ∷ Δ ++ Γ ⊢ t ∶ A
wkTerm {Δ = Δ} = model record
  { _∷_⊧_∶_ = λ Θ Γ t A → Θ ∷ Δ ++ Γ ⊢ t ∶ A
  ; M-free = free ; M-var = var ∘ expand↦ _ ; M-lam = lam ; M-● = _●_
  }

--------------------------------------------------------------------------------
-- Typed renamings

infix 4 _⊢ᵣ_∶_
data _⊢ᵣ_∶_ : Ctxt → Wk → Ctxt → Set where
  ⊢Id   : ∀{Γ} → Γ ⊢ᵣ Id ∶ Γ
  ⊢Up   : ∀{Γ Δ A w} → Δ ⊢ᵣ w ∶ Γ → Δ # A ⊢ᵣ Up w ∶ Γ
  ⊢Skip : ∀{Γ Δ A w} → Δ ⊢ᵣ w ∶ Γ → Δ # A ⊢ᵣ Skip w ∶ Γ # A

⊢wk-var : ∀{Γ Δ A n w} → Γ [ n ]↦ A → Δ ⊢ᵣ w ∶ Γ → Δ [ wk-var n w ]↦ A
⊢wk-var x ⊢Id = x
⊢wk-var x (⊢Up w) = there (⊢wk-var x w)
⊢wk-var here (⊢Skip w) = here
⊢wk-var (there x) (⊢Skip w) = there (⊢wk-var x w)

⊢wk : ∀{Θ Γ A t} → Θ ∷ Γ ⊢ t ∶ A → ∀{Δ w} → Δ ⊢ᵣ w ∶ Γ → Θ ∷ Δ ⊢ wk t w ∶ A
⊢wk = model record
  { _∷_⊧_∶_ = λ Θ Γ t A → ∀ {Δ w} → Δ ⊢ᵣ w ∶ Γ → Θ ∷ Δ ⊢ wk t w ∶ A
  ; M-free = λ x → const (free x) ; M-var = λ x w → var (⊢wk-var x w)
  ; M-lam = λ x → lam ∘ x ∘ ⊢Skip ; M-● = λ x y w → x w ● y w
  }

⊢wk-comp : ∀{Γ Δ ∇ w w'} → Δ ⊢ᵣ w ∶ Γ → ∇ ⊢ᵣ w' ∶ Δ → ∇ ⊢ᵣ w ·ʷ w' ∶ Γ
⊢wk-comp w ⊢Id = w
⊢wk-comp w (⊢Up w') = ⊢Up (⊢wk-comp w w')
⊢wk-comp ⊢Id (⊢Skip w') = ⊢Skip w'
⊢wk-comp (⊢Up w) (⊢Skip w') = ⊢Up (⊢wk-comp w w')
⊢wk-comp (⊢Skip w) (⊢Skip w') = ⊢Skip (⊢wk-comp w w')

⊢ups : ∀ Δ → Δ ⊢ᵣ up (clen Δ) Id ∶ ◇
⊢ups ◇ = ⊢Id
⊢ups (Δ # x) = ⊢Up (⊢ups Δ)

--------------------------------------------------------------------------------
-- Typed substitutions

infix 4 _∷_⊢ₛ_∶_
data _∷_⊢ₛ_∶_ : Ctxtₗ → Ctxt → Subst → Ctxt → Set where
  ⊢Id   : ∀{Θ Γ} → Θ ∷ Γ ⊢ₛ Id ∶ Γ
  ⊢Cons : ∀{Θ Γ ∇ A t σ}
        → Θ ∷ Γ ⊢ₛ σ ∶ ∇ → Θ ∷ Γ ⊢ t ∶ A → Θ ∷ Γ ⊢ₛ σ , t ∶ ∇ # A
  ⊢Wk   : ∀{Θ Γ Δ ∇ w σ} → ∇ ⊢ᵣ w ∶ Δ → Θ ∷ Δ ⊢ₛ σ ∶ Γ → Θ ∷ ∇ ⊢ₛ σ · w ∶ Γ

⊢sub-var : ∀{Θ Γ A n} → Γ [ n ]↦ A → ∀{Δ σ} → Θ ∷ Δ ⊢ₛ σ ∶ Γ
         → Θ ∷ Δ ⊢ sub-var n σ ∶ A
⊢sub-var x ⊢Id = var x
⊢sub-var here (⊢Cons σ t) = t
⊢sub-var (there x) (⊢Cons σ t) = ⊢sub-var x σ
⊢sub-var x (⊢Wk w σ) = ⊢wk (⊢sub-var x σ) w

⊢sub : ∀{Θ Γ A t} → Θ ∷ Γ ⊢ t ∶ A → ∀{Δ σ} → Θ ∷ Δ ⊢ₛ σ ∶ Γ → Θ ∷ Δ ⊢ sub t σ ∶ A
⊢sub = model record
  { _∷_⊧_∶_ = λ Θ Γ t A → ∀ {Δ σ} → Θ ∷ Δ ⊢ₛ σ ∶ Γ → Θ ∷ Δ ⊢ sub t σ ∶ A
  ; M-free = λ z → const (free z) ; M-var = ⊢sub-var
  ; M-lam = λ x σ → lam (x (⊢Cons (⊢Wk (⊢Up ⊢Id) σ) (var here)))
  ; M-● = λ x y σ → x σ ● y σ
  }
