module Syntax.Raw.Renaming where

open import Data.Sum
open import Utils
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat
open import Data.Product

open import Relation.Binary
open import Algebra
open import Algebra.FunctionProperties

open import Syntax.Raw.Term

data Wk : Set where
  Id : Wk
  Up : Wk → Wk
  Skip : Wk → Wk

wk-var : ℕ → Wk → ℕ
wk-var x Id = x
wk-var x (Up w) = suc (wk-var x w)
wk-var zero (Skip w) = zero
wk-var (suc x) (Skip w) = suc (wk-var x w)

wk : Term → Wk → Term
wk (fvar x) w = fvar x
wk (bvar x) w = bvar (wk-var x w)
wk (lam t) w = lam (wk t (Skip w))
wk (t · s) w = wk t w · wk s w

up : ℕ → Wk → Wk
up zero w = w
up (suc n) w = Up (up n w)

skip : ℕ → Wk → Wk
skip zero w = w
skip (suc n) w = Skip (skip n w)

null-wk-var : ∀ {w} n x → x ≤ n → wk-var x (skip (suc n) w) ≡ x
null-wk-var zero .0 z≤n = refl
null-wk-var (suc n) zero p = refl
null-wk-var (suc n) (suc x) (s≤s p) = cong suc (null-wk-var n x p)

null-wk : ∀ {n t w} → Sz n t → wk t (skip n w) ≡ t
null-wk tmFree = refl
null-wk (tmVar x) = cong bvar (null-wk-var _ _ x)
null-wk (tmLam tm) = cong lam (null-wk tm)
null-wk (tmApp tm tm₁) = cong₂ _·_ (null-wk tm) (null-wk tm₁)

id-wk-var : ∀ n x → wk-var x (skip n Id) ≡ x
id-wk-var zero x = refl
id-wk-var (suc n) zero = refl
id-wk-var (suc n) (suc x) = cong suc (id-wk-var n x)

id-wk : ∀ n t → wk t (skip n Id) ≡ t
id-wk n (fvar x) = refl
id-wk n (bvar x) = cong bvar (id-wk-var n x)
id-wk n (lam t) = cong lam (id-wk (suc n) t)
id-wk n (t · s) = cong₂ _·_ (id-wk n t) (id-wk n s)

-- composition of weakenings
_·ʷ_ : Wk → Wk → Wk
w ·ʷ Id = w
w ·ʷ Up w' = Up (w ·ʷ w')
Id ·ʷ Skip w' = Skip w'
Up w ·ʷ Skip w' = Up (w ·ʷ w')
Skip w ·ʷ Skip w' = Skip (w ·ʷ w')

wk-var-comp : ∀ w w' x → wk-var (wk-var x w) w' ≡ wk-var x (w ·ʷ w')
wk-var-comp w Id x = refl
wk-var-comp w (Up w') x = cong suc (wk-var-comp w w' x)
wk-var-comp Id (Skip w') x = refl
wk-var-comp (Up w) (Skip w') x = cong suc (wk-var-comp w w' x)
wk-var-comp (Skip w) (Skip w') zero = refl
wk-var-comp (Skip w) (Skip w') (suc x) = cong suc (wk-var-comp w w' x)

wk-comp : ∀ w w' t → wk (wk t w) w' ≡ wk t (w ·ʷ w')
wk-comp w w' (fvar x) = refl
wk-comp w w' (bvar x) = cong bvar (wk-var-comp w w' x)
wk-comp w w' (lam t) = cong lam (wk-comp (Skip w) (Skip w') t)
wk-comp w w' (t · s) = cong₂ _·_ (wk-comp w w' t) (wk-comp w w' s)

--------------------------------------------------------------------------------
-- Equality of weakenings

private
  _≈_ : Wk → Wk → Set
  w ≈ w' = (x : ℕ) → wk-var x w ≡ wk-var x w'

record _≈ʷ_ (w w' : Wk) : Set where
  constructor ≈ʷin
  field ≈ʷ-meaning : w ≈ w'
open _≈ʷ_

-- idw-L : ∀ w → (Id ·ʷ w) ≈ʷ w
-- idw-L w = ≈ʷin (λ x → sym (wk-var-comp Id w x))

-- idw-R : ∀ w → (w ·ʷ Id) ≈ʷ w
-- idw-R w = ≈ʷin λ x → refl


-- reflʷ : ∀{w} → w ≈ʷ w
-- reflʷ = ≈ʷin (λ x → refl)

-- symmʷ : ∀{w w'} → w ≈ʷ w' → w' ≈ʷ w
-- symmʷ (≈ʷin eq) = ≈ʷin (λ x → sym (eq x))

≈ʷ-equiv : IsEquivalence _≈ʷ_
≈ʷ-equiv = record
  { refl = ≈ʷin (λ x → refl) ; sym = λ { (≈ʷin eq) → ≈ʷin (λ x → sym (eq x)) }
  ; trans = λ { (≈ʷin f) (≈ʷin g) → ≈ʷin λ x → trans (f x) (g x) }
  }

eq-skip : ∀{w w'} → w ≈ʷ w' → Skip w ≈ʷ Skip w'
eq-skip (≈ʷin eq) = ≈ʷin λ { zero → refl ; (suc x) → cong suc (eq x) }

wk-assoc : ∀ w w' w'' → ((w ·ʷ w') ·ʷ w'') ≈ʷ  (w ·ʷ (w' ·ʷ w''))
wk-assoc w w' w'' = ≈ʷin (wk-assoc' w w' w'')
  where
    wk-assoc' : ∀ w w' w'' → ((w ·ʷ w') ·ʷ w'') ≈  (w ·ʷ (w' ·ʷ w''))
    wk-assoc' w w' Id x = refl
    wk-assoc' w w' (Up w'') x = cong suc (wk-assoc' w w' w'' x)
    wk-assoc' w Id (Skip w'') x = refl
    wk-assoc' w (Up w') (Skip w'') x = wk-assoc' w w' (Up w'') x
    wk-assoc' Id (Skip w') (Skip w'') x = refl
    wk-assoc' (Up w) (Skip w') (Skip w'') x = wk-assoc' w w' (Up w'') x
    wk-assoc' (Skip w) (Skip w') (Skip w'') x =
      ≈ʷ-meaning (eq-skip (≈ʷin (wk-assoc' w w' w''))) x

wk-cong : _·ʷ_ Preserves₂ _≈ʷ_ ⟶ _≈ʷ_ ⟶ _≈ʷ_
wk-cong {w1} {w2} {w3} {w4} (≈ʷin f) (≈ʷin g) =
  ≈ʷin λ x → trans (sym (wk-var-comp w1 w3 x))
            (trans (cong (flip wk-var w3) (f x))
            (trans (g (wk-var x w2)) (wk-var-comp w2 w4 x)))

wkMagma : IsMagma _≈ʷ_ _·ʷ_
wkMagma = record { isEquivalence = ≈ʷ-equiv ; ∙-cong = wk-cong }

wkSemigroup : IsSemigroup _≈ʷ_ _·ʷ_
wkSemigroup = record { isMagma = wkMagma ; assoc = wk-assoc }

wkMonoid : Monoid _ _
wkMonoid = record
  { Carrier = Wk ; _≈_ = _≈ʷ_ ; _∙_ = _·ʷ_ ; ε = Id
  ; isMonoid = record
      { isSemigroup = wkSemigroup
      ; identity = (λ w → ≈ʷin (λ x → sym (wk-var-comp Id w x))) ,
                   (λ w → (≈ʷin λ x → refl))
      }
  }

eq-up : ∀{w w'} → w ≈ʷ w' → Up w ≈ʷ Up w'
eq-up (≈ʷin eq) = ≈ʷin λ x → cong suc (eq x)

eq-skip2 : ∀{w w'} → w ≈ʷ w' → Skip (Skip w) ≈ʷ Skip (Skip w')
eq-skip2 = eq-skip ∘ eq-skip

-- eq-dotʷ : ∀{w w' w''} → w ≈ʷ w' → (w ·ʷ w'') ≈ʷ (w' ·ʷ w'')

eq-wk : ∀{w w'} → w ≈ʷ w' → ∀ t → wk t w ≡ wk t w'
eq-wk eq (fvar x) = refl
eq-wk eq (bvar x) = cong bvar (≈ʷ-meaning eq _)
eq-wk eq (lam t) = cong lam (eq-wk (eq-skip eq) t)
eq-wk eq (t · s) = cong₂ _·_ (eq-wk eq t) (eq-wk eq s)

ups-comp : ∀ n m → (up n Id ·ʷ up m Id) ≈ʷ up (n + m) Id
ups-comp n m = ≈ʷin (ups-comp' n m)
  where ups-comp' : ∀ n m → (up n Id ·ʷ up m Id) ≈ up (n + m) Id
        ups-comp' n zero x rewrite plus-0 n = refl
        ups-comp' n (suc m) x rewrite plus-succ n m = cong suc (ups-comp' n m x)

wk-var≤ : ∀ k m x n → x ≤ n → wk-var x (skip k (up m Id)) ≤ m + n
wk-var≤ zero zero x n p = p
wk-var≤ zero (suc m) x n p = s≤s (wk-var≤ 0 m x n p)
wk-var≤ (suc k) m zero n p = z≤n
wk-var≤ (suc k) m (suc x) zero ()
wk-var≤ (suc k) m (suc x) (suc n) (s≤s p)
  rewrite plus-succ m n = s≤s (wk-var≤ k m x n p)

tm-wk-lemma : ∀{t} n k m → Sz n t → Sz (m + n) (wk t (skip k (up m Id)))
tm-wk-lemma n k m tmFree = tmFree
tm-wk-lemma .(suc _) k m (tmVar {n = n} x₁) rewrite plus-succ m n =
  tmVar (wk-var≤ k m _ n x₁)
tm-wk-lemma n k m (tmLam tm₁) =
  tmLam (Sz≡ refl (plus-succ m n) (tm-wk-lemma (suc n) (suc k) m tm₁))
tm-wk-lemma n k m (tmApp tm₁ tm₂) =
  tmApp (tm-wk-lemma n k m tm₁) (tm-wk-lemma n k m tm₂)

tm-wk-0 : ∀{t w} → Sz 0 t → Sz 0 (wk t w)
tm-wk-0 {t} {w} tm = subst (Sz 0) (sym (null-wk tm)) tm

wk≤ : ∀ w x → x ≤ wk-var x w
wk≤ Id x = ≤refl x
wk≤ (Up w) x = ≤succ (wk≤ w x)
wk≤ (Skip w) zero = z≤n
wk≤ (Skip w) (suc x) = s≤s (wk≤ w x)

sub¬Sz-lemma : ∀{n w t} → ¬Sz n t → ¬Sz n (wk t w)
sub¬Sz-lemma {w = w} (¬tmVar {x = x} p) = ¬tmVar (≤trans p (wk≤ w x))
sub¬Sz-lemma (¬tmLam tm) = ¬tmLam (sub¬Sz-lemma tm)
sub¬Sz-lemma (¬tmApp₁ tm) = ¬tmApp₁ (sub¬Sz-lemma tm)
sub¬Sz-lemma (¬tmApp₂ x tm) = inj-tmApp₂ (sub¬Sz-lemma tm)

wk-var-ups : ∀ x m → wk-var x (up m Id) ≡ x + m
wk-var-ups x zero = sym (plus-0 x)
wk-var-ups x (suc m) = trans (cong suc (wk-var-ups x m)) (sym (plus-succ x m))
