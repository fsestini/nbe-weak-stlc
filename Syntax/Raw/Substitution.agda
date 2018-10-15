module Syntax.Raw.Substitution where

open import Utils
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat
open import Data.Product using (proj₁)

open import Algebra
open import Algebra.Structures

open import Syntax.Raw.Term
open import Syntax.Raw.Renaming public
open import Syntax.Raw.Context

data Subst : Set where
  Id  : Subst
  _·_ : Subst → Wk → Subst
  _,_ : Subst → Term → Subst
infixl 7 _,_

sub-var : ℕ → Subst → Term
sub-var x Id = bvar x
sub-var x (σ · w) = wk (sub-var x σ) w
sub-var zero (σ , t) = t
sub-var (suc x) (σ , t) = sub-var x σ

shift : ℕ → Subst → Subst
shift zero σ = σ
shift (suc n) σ = shift n σ · Up Id , bvar 0

sh : Subst → Subst
sh σ = shift 1 σ

sub : Term → Subst → Term
sub (fvar x) σ = fvar x
sub (bvar x) σ = sub-var x σ
sub (lam t) σ = lam (sub t (sh σ))
sub (t · s) σ = sub t σ · sub s σ

_[_] : Term → Term → Term
t [ s ] = sub t (Id , s)

--------------------------------------------------------------------------------
-- Equality of substitutions

private
  infix 4 _≈_
  _≈_ : Subst → Subst → Set
  σ ≈ τ = (x : ℕ) → sub-var x σ ≡ sub-var x τ

  eq-shift' : ∀{σ τ} → σ ≈ τ → ∀ n → shift n σ ≈ shift n τ
  eq-shift' eq zero x = eq x
  eq-shift' eq (suc n) zero = refl
  eq-shift' eq (suc n) (suc x) = cong (λ x₁ → wk x₁ (Up Id)) (eq-shift' eq n x)

  eq-sub' : ∀{σ τ} → σ ≈ τ → ∀ t → sub t σ ≡ sub t τ
  eq-sub' eq (fvar x) = refl
  eq-sub' eq (bvar x) = eq x
  eq-sub' eq (lam t) = cong lam (eq-sub' (eq-shift' eq 1) t)
  eq-sub' eq (t · s) = cong₂ _·_ (eq-sub' eq t) (eq-sub' eq s)

-- Two substitutions are equal if they are point-wise equal when seen as
-- functions from variables to terms.
infix 4 _≈ˢ_
record _≈ˢ_ (σ τ : Subst) : Set where
  constructor ≈ˢin
  field ≈ˢ-meaning : σ ≈ τ
open _≈ˢ_

reflˢ : ∀{σ} → σ ≈ˢ σ
reflˢ = ≈ˢin (λ x → refl)

symmˢ : ∀{σ τ} → σ ≈ˢ τ → τ ≈ˢ σ
symmˢ (≈ˢin x) = ≈ˢin (λ x₁ → sym (x x₁))

transˢ : ∀{σ τ ρ} → σ ≈ˢ τ → τ ≈ˢ ρ → σ ≈ˢ ρ
transˢ (≈ˢin x) (≈ˢin x₁) = ≈ˢin (λ x₂ → trans (x x₂) (x₁ x₂))

eq-shift : ∀{σ τ} → σ ≈ˢ τ → ∀ n → shift n σ ≈ˢ shift n τ
eq-shift (≈ˢin x) n = ≈ˢin (eq-shift' x n)

consˢ : ∀{σ τ s} → σ ≈ˢ τ → (σ , s) ≈ˢ (τ , s)
consˢ (≈ˢin eq) = ≈ˢin λ { zero → refl ; (suc x) → eq x }

eq-sub : ∀{σ τ} → σ ≈ˢ τ → ∀ t → sub t σ ≡ sub t τ
eq-sub (≈ˢin eq) t = eq-sub' eq t

eq-dot : ∀{σ τ w} → σ ≈ˢ τ → (σ · w) ≈ˢ (τ · w)
eq-dot {w = w} (≈ˢin eq) = ≈ˢin (λ x → cong (flip wk w) (eq x))

eq-dot' : ∀{σ w w'} → w ≈ʷ w' → (σ · w) ≈ˢ (σ · w')
eq-dot' weq = ≈ˢin (λ x → eq-wk weq _)

id-eq-lemma : ∀ n → Id ≈ˢ (shift n Id)
id-eq-lemma = ≈ˢin ∘ id-eq-lemma'
  where id-eq-lemma' : ∀ n → Id ≈ (shift n Id)
        id-eq-lemma' zero x = refl
        id-eq-lemma' (suc n) zero = refl
        id-eq-lemma' (suc n) (suc x) = cong (λ z → wk z (Up Id)) (id-eq-lemma' n x)

id-sub : ∀ t → sub t Id ≡ t
id-sub (fvar x) = refl
id-sub (bvar x) = refl
id-sub (lam t) =
  cong lam (trans (eq-sub (symmˢ {Id} {sh Id} (id-eq-lemma 1)) t) (id-sub t))
id-sub (t · s) = cong₂ _·_ (id-sub t) (id-sub s)

id-sub' : ∀ {n} t → sub t (shift n Id) ≡ t
id-sub' {n} t = sym (trans (sym (id-sub t)) (eq-sub (id-eq-lemma n) t))

sub-id-L : ∀{σ} → σ · Id ≈ˢ σ
sub-id-L {σ} = ≈ˢin sub-id-L'
  where sub-id-L' : σ · Id ≈ σ
        sub-id-L' x = id-wk 0 (sub-var x σ)

open Monoid using (isMonoid)
open IsMonoid using (identity)

sh-skip : ∀{σ w} → sh σ · Skip w ≈ˢ sh (σ · w)
sh-skip {σ} {w} = ≈ˢin (λ { zero → refl
  ; (suc x) → trans (wk-comp (Up Id) (Skip w) (sub-var x σ))
             (trans (eq-wk (eq-up {Id ·ʷ w} {w} (idL w)) (sub-var x σ))
                    (sym (wk-comp w (Up Id) (sub-var x σ)))) })
  where idL = proj₁ (identity (isMonoid wkMonoid))

subst-lift-sw : ∀ {w σ} t → sub t (sh σ · Skip w) ≡ sub t (sh (σ · w))
subst-lift-sw {w} {σ} t = eq-sub sh-skip t

wk-subst : ∀{w σ} t → wk (sub t σ) w ≡ sub t (σ · w)
wk-subst (fvar x) = refl
wk-subst (bvar x) = refl
wk-subst (lam t) = cong lam (trans (wk-subst t) (subst-lift-sw t))
wk-subst (t · s) = cong₂ _·_ (wk-subst t) (wk-subst s)

--------------------------------------------------------------------------------
-- Left composition of a weakening with a substitution
_ʷ·_ : Wk → Subst → Subst
w ʷ· Id = Id · w
w ʷ· (σ · w') = (w ʷ· σ) · w'
Id ʷ· (σ , t) = σ , t
Up w ʷ· (σ , t) = w ʷ· σ
Skip w ʷ· (σ , t) = w ʷ· σ , t

comp-swk : ∀ σ w w' → (σ · w) · w' ≈ˢ σ · (w ·ʷ w')
comp-swk σ w w' = ≈ˢin (λ x → wk-comp w w' (sub-var x σ))

subst-lift-ws : ∀{w σ} t → sub t (Skip w ʷ· sh σ) ≡ sub t (sh (w ʷ· σ))
subst-lift-ws = eq-sub (≈ˢin λ { zero → refl ; (suc x) → refl })

subst-wk-var : ∀ w σ x → sub-var (wk-var x w) σ ≡ sub-var x (w ʷ· σ)
subst-wk-var w Id x = refl
subst-wk-var w (σ · w') x = cong (flip wk w') (subst-wk-var w σ x)
subst-wk-var Id (σ , t) x = refl
subst-wk-var (Up w) (σ , t) x = subst-wk-var w σ x
subst-wk-var (Skip w) (σ , t) zero = refl
subst-wk-var (Skip w) (σ , t) (suc x) = subst-wk-var w σ x

subst-wk : ∀{w σ} t → sub (wk t w) σ ≡ sub t (w ʷ· σ)
subst-wk (fvar x) = refl
subst-wk {w} {σ} (bvar x) = subst-wk-var w σ x
subst-wk {w} {σ} (lam t) =
  cong lam (trans (subst-wk t) (subst-lift-ws {w} {σ} t))
subst-wk {w} {σ} (t · s) = cong₂ _·_ (subst-wk t) (subst-wk s)

--------------------------------------------------------------------------------
-- Composition of substitutions
_·ˢ_ : Subst → Subst → Subst
σ ·ˢ Id = σ
σ ·ˢ (τ · w) = (σ ·ˢ τ) · w
Id ·ˢ (τ , x) = τ , x
(σ · w) ·ˢ (τ , t) = σ ·ˢ (w ʷ· (τ , t))
(σ , t) ·ˢ (τ , s) = (σ ·ˢ (τ , s)) , sub t (τ , s)

id-wk-sub-L : ∀ σ → (Id ʷ· σ) ≈ˢ σ
id-wk-sub-L σ = ≈ˢin (id-wk-sub-L' σ)
  where id-wk-sub-L' : ∀ σ → (Id ʷ· σ) ≈ σ
        id-wk-sub-L' Id x = refl
        id-wk-sub-L' (σ · w) x = cong (flip wk w) (id-wk-sub-L' σ x)
        id-wk-sub-L' (σ , t) x = refl

id-wk-comp : ∀ σ τ → (σ ·ˢ (Id ʷ· τ)) ≈ˢ (σ ·ˢ τ)
id-wk-comp σ τ = ≈ˢin (id-wk-comp' σ τ)
  where id-wk-comp' : ∀ σ τ → (σ ·ˢ (Id ʷ· τ)) ≈ (σ ·ˢ τ)
        id-wk-comp' σ Id x = id-wk 0 (sub-var x σ)
        id-wk-comp' σ (τ · w) x = cong (flip wk w) (id-wk-comp' σ τ x)
        id-wk-comp' σ (τ , t) x = refl

sub-comp-lift : ∀{σ τ} → (sh σ ·ˢ sh τ) ≈ˢ sh (σ ·ˢ τ)
sub-comp-lift {σ} {τ} =
  ≈ˢin (λ { zero → refl
          ; (suc x) → cong (flip wk (Up Id)) (≈ˢ-meaning (id-wk-comp σ τ) x) })

sub-comp-var : ∀ σ τ x → sub (sub-var x σ) τ ≡ sub-var x (σ ·ˢ τ)
sub-comp-var σ Id x = id-sub (sub-var x σ)
sub-comp-var σ (τ · w) x =
  trans (sym (wk-subst (sub-var x σ))) (cong (flip wk w) (sub-comp-var σ τ x))
sub-comp-var Id (τ , t) x = refl
sub-comp-var (σ · w) (τ , t) x =
  trans (subst-wk {w} {τ , t} (sub-var x σ)) (sub-comp-var σ (w ʷ· (τ , t)) x)
sub-comp-var (σ , t) (τ , s) zero = refl
sub-comp-var (σ , t) (τ , s) (suc x) = sub-comp-var σ (τ , s) x

sub-comp : ∀{σ τ} t → sub (sub t σ) τ ≡ sub t (σ ·ˢ τ)
sub-comp (fvar x) = refl
sub-comp {σ} {τ} (bvar x) = sub-comp-var σ τ x
sub-comp {σ} {τ} (lam t) =
  cong lam (trans (sub-comp t) (eq-sub (sub-comp-lift {σ} {τ}) t))
sub-comp {σ} {τ} (t · s) = cong₂ _·_ (sub-comp t) (sub-comp s)

--------------------------------------------------------------------------------
-- Other properties

id-comp-L : ∀ σ → Id ·ˢ σ ≈ˢ σ
id-comp-L σ = ≈ˢin (λ x → sym (sub-comp-var Id σ x))

sub-comp-R : ∀ {t} σ τ → (σ , t) ·ˢ τ ≈ˢ (σ ·ˢ τ , sub t τ)
sub-comp-R {t} σ τ = ≈ˢin (λ {
    zero → sym (sub-comp-var (σ , t) τ 0)
  ; (suc x) → trans (sym (sub-comp-var (σ , t) τ (suc x))) (sub-comp-var σ τ x) })

sgl-comp : ∀{σ s} → sh σ ·ˢ (Id , s) ≈ˢ (σ , s)
sgl-comp {σ} = ≈ˢin (λ { zero → refl ; (suc x) → id-wk 0 (sub-var x σ) })

singleton-comp : ∀ {σ s} t → sub (sub t (sh σ)) (Id , s) ≡ sub t (σ , s)
singleton-comp {σ} {s} t =
  trans (sub-comp {sh σ} {Id , s} t) (eq-sub (consˢ {s = s} (sub-id-L {σ})) t)

sub-var-cover-lemma : ∀{s} n m x
                    → x ≤ m + n → Sz n s
                    → Sz (m + n) (sub-var x (shift m (Id , s)))
sub-var-cover-lemma n zero zero p tm = tm
sub-var-cover-lemma .(suc _) zero (suc x) (s≤s p) tm = tmVar p
sub-var-cover-lemma n (suc m) zero p tm = tmVar z≤n
sub-var-cover-lemma n (suc m) (suc x) (s≤s p) tm =
  tm-wk-lemma (m + n) 0 1 (sub-var-cover-lemma n m x p tm)

sub-cover-lemma : ∀{t s} n m
                → Sz (suc (m + n)) t → Sz n s
                → Sz (m + n) (sub t (shift m (Id , s)))
sub-cover-lemma n m tmFree tms = tmFree
sub-cover-lemma n m (tmVar x₁) tms = sub-var-cover-lemma n m _ x₁ tms
sub-cover-lemma n m (tmLam tmt₁) tms =
  tmLam (sub-cover-lemma n (suc m) tmt₁ tms)
sub-cover-lemma n m (tmApp tmt₁ tmt₂) tms =
  tmApp (sub-cover-lemma n m tmt₁ tms) (sub-cover-lemma n m tmt₂ tms)

null-sub-var : ∀{σ} n x → x ≤ n → sub-var x (shift (suc n) σ) ≡ bvar x
null-sub-var zero .0 z≤n = refl
null-sub-var (suc n) zero p = refl
null-sub-var {σ} (suc n) (suc x) (s≤s p)
  rewrite null-sub-var {σ} n x p = refl

null-sub : ∀{σ t n} → Sz n t → sub t (shift n σ) ≡ t
null-sub tmFree = refl
null-sub (tmVar x) = null-sub-var _ _ x
null-sub (tmLam tm) = cong lam (null-sub tm)
null-sub (tmApp tm tm₁) = cong₂ _·_ (null-sub tm) (null-sub tm₁)

¬Sz-sub-var-lemma : ∀{σ} n m x
                  → ¬Sz (m + n) (wk (sub-var x (shift n σ)) (up m Id))
                  → ¬Sz (m + n) (bvar (x + m))
¬Sz-sub-var-lemma zero m zero tm rewrite plus-0 m = ¬tmVar (≤refl m)
¬Sz-sub-var-lemma zero m (suc x) tm rewrite plus-0 m = ¬tmVar (aux x m)
  where
    aux : ∀ x m → suc (x + m) ≥ m
    aux x zero = z≤n
    aux x (suc m) rewrite plus-succ x m = s≤s (aux x m)
¬Sz-sub-var-lemma (suc n) m zero (¬tmVar x) rewrite wk-var-ups 0 m = ¬tmVar x
¬Sz-sub-var-lemma {σ} (suc n) m (suc x) tm =
  ¬Sz≡ (cong bvar (plus-succ x m)) (sym (plus-succ m n))
    (¬Sz-sub-var-lemma {σ} n (suc m) x (¬Sz≡ aux (plus-succ m n) tm))
  where
    aux = trans (wk-comp (Up Id) (up m Id) (sub-var x (shift n σ)))
                (eq-wk {Up Id ·ʷ up m Id} {up (suc m) Id} (ups-comp 1 m) _)

¬Sz-sub-lemma : ∀{t σ} n → ¬Sz n (sub t (shift n σ)) → ¬Sz n t
¬Sz-sub-lemma {fvar x} n tm = tm
¬Sz-sub-lemma {bvar x} n tm =
  ¬Sz≡ (cong bvar (plus-0 x)) refl
    (¬Sz-sub-var-lemma n 0 x (¬Sz≡ (sym (id-wk 0 _)) refl tm))
¬Sz-sub-lemma {lam t} n (¬tmLam tm) = ¬tmLam (¬Sz-sub-lemma (suc n) tm)
¬Sz-sub-lemma {t · s} n (¬tmApp₁ tm) = ¬tmApp₁ (¬Sz-sub-lemma n tm)
¬Sz-sub-lemma {t · s} n (¬tmApp₂ x tm) = inj-tmApp₂ (¬Sz-sub-lemma n tm)

idsub : (Γ : Ctxt) → Subst
idsub Γ = shift (clen Γ) Id
