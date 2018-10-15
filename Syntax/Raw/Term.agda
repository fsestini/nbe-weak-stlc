module Syntax.Raw.Term where

open import Data.Product
open import Data.Nat
open import Data.Empty
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Utils

data Term : Set where
  fvar : ℕ → Term
  bvar : ℕ → Term
  lam : Term → Term
  _·_ : Term → Term → Term
infixl 7 _·_

data Sz : ℕ → Term → Set where
  tmFree : ∀{n x} → Sz n (fvar x)
  tmVar  : ∀{n x} → x ≤ n → Sz (suc n) (bvar x)
  tmLam  : ∀{t n} → Sz (suc n) t → Sz n (lam t)
  tmApp  : ∀{t s n} → Sz n t → Sz n s → Sz n (t · s)

data Szₗ : ℕ → Term → Set where
  tmlFree : ∀{n x} → x ≤ n → Szₗ (suc n) (fvar x)
  tmlVar  : ∀{n x} → Szₗ n (bvar x)
  tmlLam  : ∀{t n} → Szₗ n t → Szₗ n (lam t)
  tmlApp  : ∀{t s n} → Szₗ n t → Szₗ n s → Szₗ n (t · s)

data ¬Sz : ℕ → Term → Set where
  ¬tmVar : ∀{n x} → x ≥ n → ¬Sz n (bvar x)
  ¬tmLam : ∀{t n} → ¬Sz (suc n) t → ¬Sz n (lam t)
  ¬tmApp₁ : ∀{t s n} → ¬Sz n t → ¬Sz n (t · s)
  ¬tmApp₂ : ∀{t s n} → Sz n t → ¬Sz n s → ¬Sz n (t · s)

Sz≡ : ∀{t s n m} → t ≡ s → n ≡ m → Sz n t → Sz m s
Sz≡ refl refl tm = tm

¬Sz≡ : ∀{t s n m} → t ≡ s → n ≡ m → ¬Sz n t → ¬Sz m s
¬Sz≡ refl refl tm = tm

liftSz : ∀{t n} m → Sz n t → Sz (n + m) t
liftSz m tmFree = tmFree
liftSz m (tmVar x) = tmVar (≤+ _ x)
liftSz m (tmLam {n = n} tm) rewrite sym (plus-succ n m) = tmLam (liftSz m tm)
liftSz m (tmApp tm tm') = tmApp (liftSz m tm) (liftSz m tm')

¬Sz-lemma : ∀{n t} → ¬Sz n t → Sz n t → ⊥
¬Sz-lemma (¬tmVar p) (tmVar q) = absurde _ _ p q
¬Sz-lemma (¬tmLam ¬tm) (tmLam tm) = ¬Sz-lemma ¬tm tm
¬Sz-lemma (¬tmApp₁ ¬tm) (tmApp tm _) = ¬Sz-lemma ¬tm tm
¬Sz-lemma (¬tmApp₂ x ¬tm) (tmApp _ tm) = ¬Sz-lemma ¬tm tm

decSz : ∀ n → (t : Term) → Sz n t ⊎ ¬Sz n t
decSz n (fvar x) = inj₁ tmFree
decSz n (bvar x) with suc x ≤? n
decSz .(suc _) (bvar x) | yes (s≤s p) = inj₁ (tmVar p)
decSz n (bvar x) | no ¬p with qwerty _ _ ¬p
decSz n (bvar x) | no ¬p | s≤s w = inj₂ (¬tmVar w)
decSz n (lam t) with decSz (suc n) t
decSz n (lam t) | inj₁ x = inj₁ (tmLam x)
decSz n (lam t) | inj₂ y = inj₂ (¬tmLam y)
decSz n (t · s) with decSz n t | decSz n s
decSz n (t · s) | inj₁ x | inj₁ x₁ = inj₁ (tmApp x x₁)
decSz n (t · s) | inj₁ x | inj₂ y = inj₂ (¬tmApp₂ x y)
decSz n (t · s) | inj₂ y | _ = inj₂ (¬tmApp₁ y)

inj-tmApp₂ : ∀{t n s} → ¬Sz n s → ¬Sz n (t · s)
inj-tmApp₂ {t} {n} tm with decSz n t
inj-tmApp₂ tm | inj₁ x = ¬tmApp₂ x tm
inj-tmApp₂ tm | inj₂ y = ¬tmApp₁ y

¬Sz-lemma' : ∀{n t} → (Sz n t → ⊥) → ¬Sz n t
¬Sz-lemma' {t = fvar x} h = ⊥-elim (h tmFree)
¬Sz-lemma' {n} {bvar x} h with n ≤? x
¬Sz-lemma' {n} {bvar x} h | yes p = ¬tmVar p
¬Sz-lemma' {zero} {bvar x} h | no ¬p = ⊥-elim (¬p z≤n)
¬Sz-lemma' {suc n} {bvar x} h | no ¬p with qwerty _ _ ¬p
¬Sz-lemma' {suc n} {bvar x} h | no ¬p | s≤s w = ⊥-elim (h (tmVar w))
¬Sz-lemma' {n} {lam t} h with decSz (suc n) t
¬Sz-lemma' h | inj₁ x = ⊥-elim (h (tmLam x))
¬Sz-lemma' h | inj₂ y = ¬tmLam y
¬Sz-lemma' {n} {t · s} h with decSz n t | decSz n s
¬Sz-lemma' h | inj₁ x | inj₁ x₁ = ⊥-elim (h (tmApp x x₁))
¬Sz-lemma' h | inj₁ x | inj₂ y = ¬tmApp₂ x y
¬Sz-lemma' h | inj₂ y | _ = ¬tmApp₁ y
