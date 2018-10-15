module Explicit.Semantics.Soundness.LogicalRelation where

open import Data.Maybe
open import Syntax.Raw
open import Syntax.Typed
open import Explicit.Equality
open import Explicit.Semantics.Domain
open import Data.Product renaming (_,_ to _,,_)
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])

LogRel : Set₁
LogRel = Ctxtₗ → Ctxt → Term → D → Set

data FunRel (A B : Ty) (RA RB : LogRel) (Θ : Ctxtₗ) (Γ : Ctxt)
  : Term → D → Set where
  =>-®-Lam : ∀{t t'} {d : D} → Nf d
           → Θ ∷ Γ ⊢ t ∼ lam t' ∶ A => B
           → (∀{Δ s a b w} → Δ ⊢ᵣ w ∶ Γ
             → RA Θ Δ s a
             → d [ Id · w , a ]↘ b
             → RB Θ Δ (sub t' (Id · w , s)) b)
           → FunRel A B RA RB Θ Γ t (lam d)
  =>-®-Ne  : ∀{t e} → Ne e
           → (Θ ∷ Γ ⊢ t ∼ e ∶ A => B)
           → FunRel A B RA RB Θ Γ t e

_∷_⊢_®_∶_ : Ctxtₗ → Ctxt → Term → D → Ty → Set
Θ ∷ Γ ⊢ t ® a ∶ (A => B) =
  FunRel A B (_∷_⊢_®_∶ A) (_∷_⊢_®_∶ B) Θ Γ t a

allNe : ∀{Θ Γ A t e} → Ne e
      → Θ ∷ Γ ⊢ t ∼ e ∶ A → Θ ∷ Γ ⊢ t ® e ∶ A
allNe {A = A => A₁} ne conv = =>-®-Ne ne conv

allBound : ∀{Θ Γ A n} → Γ [ n ]↦ A → Θ ∷ Γ ⊢ bvar n ® bvar n ∶ A
allBound {Θ} {Γ} {A} {n} x = allNe neBound (∼refl (var x))

body-rel : ∀{Θ Γ A B d t'}
       → Nf d
       → (∀{Δ s a b w} → Δ ⊢ᵣ w ∶ Γ
         → Θ ∷ Δ ⊢ s ® a ∶ A
         → d [ Id · w , a ]↘ b
         → Θ ∷ Δ ⊢ sub t' (Id · w , s) ® b ∶ B)
       → Θ ∷ Γ # A ⊢ t' ® d ∶ B
body-rel {Θ} {Γ} {A} {B} nfd h = 
  subst₂ (Θ ∷ Γ # A ⊢_®_∶ B) (id-sub' {1} _) ids x
  where
    ids = id-sub' {1} _
    x = h (⊢Up ⊢Id) (allBound here) (nfSelf (subst Nf (sym ids) nfd))

nfRel : ∀{Θ Γ t a A} → Θ ∷ Γ ⊢ t ® a ∶ A → Nf a
nfRel {A = A => B} (=>-®-Lam nfd x x₁) = nfLam nfd
nfRel {A = A => B} (=>-®-Ne x x₁) = nfNe x

∼preservation : ∀{Θ Γ A t t'} {a : D}
              → Θ ∷ Γ ⊢ t ∼ t' ∶ A
              → Θ ∷ Γ ⊢ t' ® a ∶ A
              → Θ ∷ Γ ⊢ t ® a ∶ A
∼preservation {A = A => B} eq (=>-®-Lam x₁ x₂ x₃) = =>-®-Lam x₁ (∼trans eq x₂) x₃
∼preservation {A = A => B} eq (=>-®-Ne x x₁) = =>-®-Ne x (∼trans eq x₁)

convert-® : ∀{Θ Γ A t} {a : D}
            → Θ ∷ Γ ⊢ t ® a ∶ A
            → Θ ∷ Γ ⊢ t ∼ a ∶ A
convert-® {A = A => B} (=>-®-Lam nfd conv h1) =
  ∼trans conv (∼ξ (convert-® (body-rel nfd h1)))
convert-® {A = A => B} (=>-®-Ne x x₁) = x₁

ww : ∀{Θ Γ A t w} → Θ ∷ Γ ⊢ t ∶ A → Θ ∷ Γ ⊢ wk t (skip (clen Γ) w) ∶ A
ww {t = t} {w} td rewrite null-wk {w = w} (tyClosed td) = td

≡rel : ∀{Θ Γ A t s a b} → t ≡ s → a ≡ b → Θ ∷ Γ ⊢ t ® a ∶ A → Θ ∷ Γ ⊢ s ® b ∶ A
≡rel refl refl rel = rel

kripke : ∀{Θ Γ Δ A t a w}
       → Δ ⊢ᵣ w ∶ Γ
       → Θ ∷ Γ ⊢ t ® a ∶ A → Θ ∷ Δ ⊢ wk t w ® wk a w ∶ A
kripke {Θ} {Γ} {Δ} {A => B} {w = w} wp
  (=>-®-Lam {t' = t'} {d = d} nfd conv h1) =
  =>-®-Lam (nfWkLemma nfd) (∼wk wp conv) aux
  where
    aux : {∇ : Ctxt} {s a b : Term} {w' : Wk}
        → ∇ ⊢ᵣ w' ∶ Δ → Θ ∷ ∇ ⊢ s ® a ∶ A
        → wk d (Skip w) [ (Id · w') , a ]↘ b
        → Θ ∷ ∇ ⊢ sub (wk t' (Skip w)) ((Id · w') , s) ® b ∶ B
    aux {w' = w'} wp' relsa h =
      ≡rel (sym (trans (subst-wk {Skip w} t')
           (eq-sub (consˢ (comp-swk Id w w')) t'))) refl
           (h1 {w = w ·ʷ w'} (⊢wk-comp wp wp') relsa
           (≡Eval (trans (subst-wk {Skip w} d)
                  (eq-sub (consˢ (comp-swk Id w w')) d)) refl h))

kripke {A = A => B} w (=>-®-Ne x x₁) = =>-®-Ne (neWkLemma x) (∼wk w x₁)

der : ∀{Θ Γ A t a} → Θ ∷ Γ ⊢ t ® a ∶ A → Θ ∷ Γ ⊢ t ∶ A
der {A = A => B} (=>-®-Lam x₁ x₂ x₃) = proj₁ (∼lemma x₂)
der {A = A => B} (=>-®-Ne x x₁) = proj₁ (∼lemma x₁)

appLemma : ∀{Θ Γ A B r s f a b}
         → Θ ∷ Γ ⊢ r ® f ∶ (A => B) → Θ ∷ Γ ⊢ s ® a ∶ A
         → f ● a ↘ b → Θ ∷ Γ ⊢ r · s ® b ∶ B
appLemma {Θ} {Γ} {A} {B} (=>-®-Lam {t' = t'} {d = d} nfd conv h1) sa (●β rdx sb) =
  ∼preservation
    (∼trans (∼compApp conv (∼refl (der sa)))
      (≡to∼R (eq-sub (consˢ (symmˢ {Id · Id} {Id} (sub-id-L {Id}))) t')
        (~⟶ (⟶β
          (⊢shrink (der h2) (sameSz∼RL (convert-® h2) (β-Redex-Sz-Lam-t rdx)))
          (⊢shrink (der sa) (sameSz∼RL (convert-® sa) (β-Redex-Sz-s rdx)))))))
    (h1 ⊢Id sa (≡Eval (eq-sub (consˢ (symmˢ {Id · Id} {Id}
      (sub-id-L {Id}))) d) refl sb))
  where h2 = body-rel nfd h1
appLemma (=>-®-Ne () x₁) sa (●β rdx sb)
appLemma rf sa (●Ne x) = allNe x (∼compApp (convert-® rf) (convert-® sa))

--------------------------------------------------------------------------------

infix 4 _∷_⊢ₛ_®_∶_
data _∷_⊢ₛ_®_∶_ (Θ : Ctxtₗ) : Ctxt → Subst → Subst → Ctxt → Set where
  ◇® : ∀{Γ σ ρ} → Θ ∷ Γ ⊢ₛ σ ∶ ◇ → Θ ∷ Γ ⊢ₛ σ ® ρ ∶ ◇
  #® : ∀{Γ Δ A σ ρ t} {a : D}
     → Θ ∷ Γ ⊢ₛ σ ® ρ ∶ Δ
     → Θ ∷ Γ ⊢ t ® a ∶ A
     → Θ ∷ Γ ⊢ₛ σ , t ® ρ , a ∶ Δ # A
  ·® : ∀{Γ ∇ Δ σ ρ w}
     → Θ ∷ Γ ⊢ₛ σ ® ρ ∶ Δ → ∇ ⊢ᵣ w ∶ Γ → Θ ∷ ∇ ⊢ₛ σ · w ® ρ · w ∶ Δ

derₛ : ∀{Θ Γ Δ σ ρ} → Θ ∷ Γ ⊢ₛ σ ® ρ ∶ Δ → Θ ∷ Γ ⊢ₛ σ ∶ Δ
derₛ (◇® x) = x
derₛ (#® rel x) = ⊢Cons (derₛ rel) (der x)
derₛ (·® rel x) = ⊢Wk x (derₛ rel)
