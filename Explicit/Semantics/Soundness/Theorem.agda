module Explicit.Semantics.Soundness.Theorem where

open import Data.Nat
open import Data.Maybe
open import Syntax.Raw
open import Syntax.Typed
open import Explicit.Equality
open import Explicit.Semantics.Domain
open import Explicit.Semantics.Completeness hiding (appLemma)
open import Data.Product renaming (_,_ to _,,_)
open import Data.Empty
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Explicit.Semantics.Soundness.LogicalRelation
open import Relation.Nullary

varFundamental : ∀{Θ Γ Δ ∇ A n σ ρ a w}
               → Γ [ n ]↦ A
               → Eval wk (sub-var n ρ) w ↘ a
               → Θ ∷ Δ ⊢ₛ σ ® ρ ∶ Γ
               → ∇ ⊢ᵣ w ∶ Δ
               → Θ ∷ ∇ ⊢ wk (sub-var n σ) w ® a ∶ A
varFundamental () ev (◇® x₁) wp
varFundamental here ev (#® rel relt) wp =
  ≡rel refl (Eval-fun (wkEval (nfSelf (nfRel relt))) ev) (kripke wp relt)
varFundamental (there x) ev (#® rel relt) wp = varFundamental x ev rel wp
varFundamental {n = n} {_} {_} {a} {w} x ev
  (·® {σ = σ} {ρ = ρ} {w = w'} rel wp') wp =
  ≡rel (sym (wk-comp w' w (sub-var n σ))) refl aux
  where
    ev' = ≡Eval (wk-comp w' w (sub-var n ρ)) refl ev
    aux = varFundamental x ev' rel (⊢wk-comp wp' wp)

idrel : ∀{Θ} Γ → Θ ∷ Γ ⊢ₛ idsub Γ ® idsub Γ ∶ Γ
idrel ◇ = ◇® ⊢Id
idrel (Γ # A) = #® (·® (idrel Γ) (⊢Up ⊢Id)) (allNe neBound (∼refl (var here)))

fundamental : ∀{Θ Γ Δ ρ A t σ a}
            → Θ ∷ Γ ⊢ t ∶ A
            → Θ ∷ Δ ⊢ₛ σ ® ρ ∶ Γ
            → t [ ρ ]↘ a
            → Θ ∷ Δ ⊢ sub t σ ® a ∶ A
fundamental (free x) rel eFree = allNe neFree (∼refl (free x))
fundamental (var x) rel ev =
  ≡rel (id-wk 0 _) refl (varFundamental {w = Id} x
    (≡Eval (sym (id-wk 0 _)) refl ev) rel ⊢Id)

fundamental {Θ} {Γ} {Δ} {ρ} {σ = σ} (lam {A = A} {B} {t = t'} td) rel (eLam {t' = d} ev) =
  =>-®-Lam (nfEval ev) conv aux
  where
    conv : Θ ∷ Δ ⊢ lam (sub t' (sh σ)) ∼ lam (sub t' (sh σ)) ∶ A => B
    conv = ∼refl (lam (⊢sub td (⊢Cons (⊢Wk (⊢Up ⊢Id) (derₛ rel)) (var here))))
    aux : ∀{s w ∇ a b} → ∇ ⊢ᵣ w ∶ Δ → Θ ∷ ∇ ⊢ s ® a ∶ A → d [ (Id · w) , a ]↘ b
        → Θ ∷ ∇ ⊢ sub (sub t' (sh σ)) ((Id · w) , s) ® b ∶ B
    aux {s} {w} {∇} {a} {b} wp relsa ev' = ≡rel (sym eqq) refl goal
      where
        eqq : sub (sub t' (sh σ)) ((Id · w) , s) ≡ sub t' ((σ · w) , s)
        eqq = trans (sub-comp t') (eq-sub (consˢ (eq-dot sub-id-L)) t')
        goal : Θ ∷ ∇ ⊢ sub t' ((σ · w) , s) ® b ∶ B
        goal = fundamental td (#® (·® rel wp) relsa)
          (≡Eval (eq-sub (consˢ (eq-dot sub-id-L)) t') refl
            (sub-uncomm {t'} {σ = sh ρ} ev ev'))
fundamental (td ● sd) rel (eApp ev ev₁ x) =
  appLemma (fundamental td rel ev) (fundamental sd rel ev₁) x

soundness : ∀{Θ Γ A t} → (td : Θ ∷ Γ ⊢ t ∶ A) → Θ ∷ Γ ⊢ t ∼ nf td ∶ A
soundness {Θ} {Γ} {A} {t} td =
  ≡∼ (convert-® ft) refl refl refl (id-sub' {clen Γ} t) refl
  where
   open ⟦_⟧≃⟦_⟧_∈tm_
   mt = models td (std Γ)
   ft = fundamental td (idrel Γ) (↘tm1 mt)
