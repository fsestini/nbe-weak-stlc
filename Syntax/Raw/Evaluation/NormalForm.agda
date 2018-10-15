module Syntax.Raw.Evaluation.NormalForm where

open import Syntax.Raw.Term
open import Syntax.Raw.Renaming
open import Data.Empty

mutual
  data Nf : Term → Set where
    nfLam : ∀{t} → Nf t → Nf (lam t)
    nfNe   : ∀{t} → Ne t → Nf t

  data Ne : Term → Set where

    neApp   : ∀{t s} → Ne t → Nf s → Ne (t · s) -- → Sz 0 t → Sz 0 s
    lamApp₁ : ∀{t s} → Nf t → Nf s → ¬Sz 1 t → Ne (lam t · s)
    lamApp₂ : ∀{t s} → Nf t → Nf s → Sz 1 t → ¬Sz 0 s → Ne (lam t · s)

    neFree : ∀{x} → Ne (fvar x)
    neBound : ∀{x} → Ne (bvar x)

open import Data.Sum

-- inj-neApp : ∀{t s} → Ne t → Nf s → Ne (t · s)
-- inj-neApp {t} {s} ne nf with decSz 0 t | decSz 0 s
-- inj-neApp {t} {s} ne nf | inj₁ x | inj₁ x₁ = neApp ne nf x x₁
-- inj-neApp {t} {s} ne nf | inj₁ x | inj₂ y = neApp₂ (nfNe ne) nf x y
-- inj-neApp {t} {s} ne nf | inj₂ y | _ = neApp₁ (nfNe ne) nf y

-- inj-neApp₂ : ∀{t s} → Nf t → Nf s → ¬Sz 0 s → Ne (t · s)
-- inj-neApp₂ {t} {s} nft nfs tm with decSz 0 t
-- inj-neApp₂ nft nfs tm | inj₁ x = neApp₂ nft nfs x tm
-- inj-neApp₂ nft nfs tm | inj₂ y = neApp₁ nft nfs y

open import Data.Nat
open import Relation.Binary.PropositionalEquality

nfLamInv : ∀{t} → Nf (lam t) → Nf t
nfLamInv (nfLam nf) = nf
nfLamInv (nfNe ())

mutual

  neWkLemma : ∀{a w} → Ne a → Ne (wk a w)
  neWkLemma (neApp ne nf) = neApp (neWkLemma ne) (nfWkLemma nf)
  neWkLemma (lamApp₁ x y z) =
    lamApp₁ (nfWkLemma x) (nfWkLemma y) (sub¬Sz-lemma z)
  neWkLemma (lamApp₂ x y z r) =
    lamApp₂ (nfWkLemma x) (nfWkLemma y)
      (subst (Sz 1) (sym (null-wk z)) z) (sub¬Sz-lemma r)
  neWkLemma neFree = neFree
  neWkLemma neBound = neBound

  nfWkLemma : ∀{a w} → Nf a → Nf (wk a w)
  nfWkLemma (nfLam nf) = nfLam (nfWkLemma nf)
  nfWkLemma (nfNe x) = nfNe (neWkLemma x)

-- data NeView : Term → Set where
--   NVApp : ∀{t s} → Nf t → Nf s → NeView (t · s)
--   NVFree : ∀{x} → NeView (fvar x)
--   NVBound : ∀{x} → NeView (bvar x)

-- neView : ∀{t} → Ne t → NeView t
-- neView (neApp ne x x₁ x₂) = NVApp (nfNe ne) x
-- neView (neApp₁ x x₁ x₂) = NVApp x x₁
-- neView (neApp₂ x x₁ x₂ x₃) = NVApp x x₁
-- neView neFree = NVFree
-- neView neBound = NVBound

neBeta : ∀{t s} → Ne (lam t · s) → Sz 1 t → Sz 0 s → ⊥
neBeta (neApp () x) tmt tms
neBeta (lamApp₁ x x₁ x₂) tmt tms = ¬Sz-lemma x₂ tmt
neBeta (lamApp₂ x x₁ x₂ x₃) tmt tms = ¬Sz-lemma x₃ tms
