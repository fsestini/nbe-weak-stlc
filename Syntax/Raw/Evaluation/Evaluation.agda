module Syntax.Raw.Evaluation.Evaluation where

open import Function
open import Syntax.Raw.Term
open import Syntax.Raw.Substitution
open import Syntax.Raw.Evaluation.NormalForm
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_)
open import Data.Sum renaming ([_,_] to [[_,,_]])

data β-Redex : Term → Term → Set where
  βrdx : ∀{t s} → Sz 1 t → Sz 0 s → β-Redex (lam t) s

mutual
  infix 4 _●_↘_
  data _●_↘_ : Term → Term → Term → Set where
    ●β : ∀{t s ts} → β-Redex (lam t) s
       → Eval sub t (Id , s) ↘ ts → lam t ● s ↘ ts
    ●Ne : ∀{t s} → Ne (t · s) → t ● s ↘ t · s

  data Eval_↘_ : Term → Term → Set where
    eBound : ∀{x} → Eval bvar x ↘ bvar x
    eFree  : ∀{x} → Eval fvar x ↘ fvar x
    eLam   : ∀{t t'} → Eval t ↘ t' → Eval lam t ↘ lam t'
    eApp   : ∀{t s t' s' ap}
           → Eval t ↘ t' → Eval s ↘ s' → t' ● s' ↘ ap → Eval t · s ↘ ap

≡App : ∀{t t' s s' a b} → t ≡ t' → s ≡ s' → a ≡ b → t ● s ↘ a → t' ● s' ↘ b
≡App refl refl refl x = x

≡Eval : ∀{t t' a b} → t ≡ t' → a ≡ b → Eval t ↘ a → Eval t' ↘ b
≡Eval refl refl x = x

NeApp¬β : ∀{t s} → Ne (t · s) → β-Redex t s → ⊥
NeApp¬β (neApp () x₂) (βrdx x x₁)
NeApp¬β (lamApp₁ x₂ x₃ x₄) (βrdx x x₁) = ¬Sz-lemma x₄ x
NeApp¬β (lamApp₂ x₂ x₃ x₄ x₅) (βrdx x x₁) = ¬Sz-lemma x₅ x₁

decβ-Redex : ∀{t s} → Nf (lam t) → Nf s
           → β-Redex (lam t) s ⊎ Ne (lam t · s)
decβ-Redex {t} {s} (nfLam nft) nfs with decSz 1 t | decSz 0 s
decβ-Redex (nfLam nft) nfs | inj₁ x | inj₁ x₁ = inj₁ (βrdx x x₁)
decβ-Redex (nfLam nft) nfs | inj₁ x | inj₂ y = inj₂ (lamApp₂ nft nfs x y)
decβ-Redex (nfLam nft) nfs | inj₂ y | _ = inj₂ (lamApp₁ nft nfs y)
decβ-Redex (nfNe x) nfs = inj₂ (neApp x nfs)

NeLamLemma : ∀{t d σ} → Nf t → Eval sub t σ ↘ lam d
           → (Σ Term λ d' → t ≡ lam d') ⊎ (Ne t)
NeLamLemma (nfLam nf) (eLam e) = inj₁ (_ ,, refl)
NeLamLemma (nfNe x) e = inj₂ x

decβ-Redex' : ∀{t s} → Nf t → Nf s
            → (Σ Term λ d → t ≡ lam d) ⊎ (Ne t)
            → (β-Redex t s × (Σ Term λ d → t ≡ lam d)) ⊎ Ne (t · s)
decβ-Redex' et es (inj₁ (_ ,, p)) rewrite p =
  [[ (λ x → inj₁ (x ,, (_ ,, refl))) ,, (λ x → inj₂ x) ]] (decβ-Redex et es)
decβ-Redex' et es (inj₂ y) = inj₂ (neApp y es)

β-Redex-Sz-t : ∀{t s} → β-Redex t s → Sz 0 t
β-Redex-Sz-t (βrdx x _) = tmLam x

β-Redex-Sz-Lam-t : ∀{t s} → β-Redex (lam t) s → Sz 1 t
β-Redex-Sz-Lam-t (βrdx x _) = x

β-Redex-Sz-s : ∀{t s} → β-Redex t s → Sz 0 s
β-Redex-Sz-s (βrdx x x₁) = x₁

Lam-inj : ∀{t t'} → lam t ≡ lam t' → t ≡ t'
Lam-inj refl = refl
