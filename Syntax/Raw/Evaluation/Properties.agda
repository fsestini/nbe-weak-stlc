module Syntax.Raw.Evaluation.Properties where

open import Utils
open import Data.Nat
open import Data.Sum
open import Syntax.Raw.Evaluation.Evaluation
open import Syntax.Raw.Term
open import Syntax.Raw.Substitution
open import Syntax.Raw.Evaluation.NormalForm
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,,_)

mutual
  ●-fun : ∀{t s a b} → t ● s ↘ a → t ● s ↘ b → a ≡ b
  ●-fun (●β x e1) (●β y e2) = Eval-fun e1 e2
  ●-fun (●β x x₁) (●Ne y) = ⊥-elim (NeApp¬β y x)
  ●-fun (●Ne x) (●β y x₂) = ⊥-elim (NeApp¬β x y)
  ●-fun (●Ne x) (●Ne x₁) = refl

  Eval-fun : ∀{t a b} → Eval t ↘ a → Eval t ↘ b → a ≡ b
  Eval-fun eBound eBound = refl
  Eval-fun eFree eFree = refl
  Eval-fun (eLam e1) (eLam e2) = cong lam (Eval-fun e1 e2)
  Eval-fun (eApp e1 e2 x) (eApp e3 e4 x₁)
    with Eval-fun e1 e3 | Eval-fun e2 e4
  Eval-fun (eApp e1 e2 x) (eApp e3 e4 y) | refl | refl = ●-fun x y

Eval-fun' : ∀{t s a b} → Eval t ↘ a → Eval s ↘ b → t ≡ s → a ≡ b
Eval-fun' e1 e2 refl = Eval-fun e1 e2

-- Evaluating normal/neutral terms returns the input.
-- In other words, evaluation (to normal form) is idempotent.
mutual
  neSelf : ∀{t} → Ne t → Eval t ↘ t
  neSelf (neApp ne x) = eApp (neSelf ne) (nfSelf x) (●Ne (neApp ne x))
  neSelf (lamApp₁ x x₁ x₂) =
    eApp (eLam (nfSelf x)) (nfSelf x₁) (●Ne (lamApp₁ x x₁ x₂))
  neSelf (lamApp₂ x x₁ x₂ x₃) =
    eApp (eLam (nfSelf x)) (nfSelf x₁) (●Ne (lamApp₂ x x₁ x₂ x₃))
  neSelf neFree = eFree
  neSelf neBound = eBound

  nfSelf : ∀{t} → Nf t → Eval t ↘ t
  nfSelf (nfLam nf) = eLam (nfSelf nf)
  nfSelf (nfNe x) = neSelf x

mutual
  nfApp : ∀{t s a} → Nf t → Nf s → t ● s ↘ a → Nf a
  nfApp nft nfs (●β x e) = nfEval e
  nfApp nft nfs (●Ne x) = nfNe x

  nfEval : ∀{t a} → Eval t ↘ a → Nf a
  nfEval eBound = nfNe neBound
  nfEval eFree = nfNe neFree
  nfEval (eLam e) = nfLam (nfEval e)
  nfEval (eApp e e₁ x) = nfApp (nfEval e) (nfEval e₁) x

mutual
  ●-Sz : ∀{t s a n} → Sz n t → Sz n s → t ● s ↘ a → Sz n a
  ●-Sz {n = n} tmt tms (●β (βrdx x x₂) x₁) =
    liftSz n (Eval-Sz (sub-cover-lemma 0 0 x x₂) x₁)
  ●-Sz tmt tms (●Ne x) = tmApp tmt tms

  Eval-Sz : ∀{t s n} → Sz n t → Eval t ↘ s → Sz n s
  Eval-Sz tmFree eFree = tmFree
  Eval-Sz (tmVar x₁) eBound = tmVar x₁
  Eval-Sz (tmLam tm) (eLam e) = tmLam (Eval-Sz tm e)
  Eval-Sz (tmApp tm tm₁) (eApp e e₁ x) = ●-Sz (Eval-Sz tm e) (Eval-Sz tm₁ e₁) x

mutual

  ●-¬Sz : ∀{t s a n} → t ● s ↘ a → ¬Sz n (t · s) → ¬Sz n a
  ●-¬Sz (●β (βrdx x x₂) x₁) (¬tmApp₁ tm) =
    ⊥-elim (¬Sz-lemma tm (tmLam (liftSz _ x)))
  ●-¬Sz (●β (βrdx x x₃) x₁) (¬tmApp₂ x₂ tm) =
    ⊥-elim (¬Sz-lemma tm (liftSz _ x₃))
  ●-¬Sz (●Ne x) tm = tm

  Eval-¬Sz : ∀{t a n} → Eval t ↘ a → ¬Sz n t → ¬Sz n a
  Eval-¬Sz eBound tm = tm
  Eval-¬Sz eFree tm = tm
  Eval-¬Sz (eLam e) (¬tmLam tm) = ¬tmLam (Eval-¬Sz e tm)
  Eval-¬Sz (eApp e e₁ x) (¬tmApp₁ tm) = ●-¬Sz x (¬tmApp₁ (Eval-¬Sz e tm))
  Eval-¬Sz (eApp e e₁ x) (¬tmApp₂ x₁ tm) = ●-¬Sz x (inj-tmApp₂ (Eval-¬Sz e₁ tm))

Eval-Sz' : ∀{t n a} → Eval t ↘ a → Sz n a → Sz n t
Eval-Sz' {t} {n} e tm with decSz n t
Eval-Sz' e tm | inj₁ x = x
Eval-Sz' e tm | inj₂ y = ⊥-elim (¬Sz-lemma (Eval-¬Sz e y) tm)

Eval-¬Sz' : ∀{t a n} → Eval t ↘ a → ¬Sz n a → ¬Sz n t
Eval-¬Sz' e ¬tm = ¬Sz-lemma' λ x → ¬Sz-lemma ¬tm (Eval-Sz x e)

mutual

  ●wk : ∀{t s a w} → t ● s ↘ a → wk t w ● wk s w ↘ wk a w
  ●wk {w = w} (●β (βrdx tmt tms) y)
    rewrite null-wk {w = w} tmt | null-wk {w = w} tms
          | null-wk {w = w} (Eval-Sz (sub-cover-lemma 0 0 tmt tms) y) =
    ●β (βrdx tmt tms) y
  ●wk {w = w} (●Ne x) = ●Ne (neWkLemma x)

  wkEval : ∀{t s w} → Eval t ↘ s → Eval wk t w ↘ wk s w
  wkEval eBound = eBound
  wkEval eFree = eFree
  wkEval (eLam e) = eLam (wkEval e)
  wkEval (eApp e₁ e₂ x) = eApp (wkEval e₁) (wkEval e₂) (●wk x)

sub-var-comm2 : ∀{s a b}
              → ∀ w n x
              → Eval wk (sub-var x (shift n (Id , a))) w ↘ b
              → Eval s ↘ a
              → Eval wk (sub-var x (shift n (Id , s))) w ↘ b
sub-var-comm2 w zero zero ex es
  with sym (Eval-fun (wkEval {w = w} (nfSelf (nfEval es))) ex)
sub-var-comm2 w zero zero ex es | refl = wkEval {w = w} es
sub-var-comm2 w zero (suc x) ex es = ex
sub-var-comm2 w (suc n) zero ex es = ex
sub-var-comm2 w (suc n) (suc x) ex es =
  ≡Eval (sym (wk-comp (Up Id) w _)) refl
    (sub-var-comm2 (Up Id ·ʷ w) n x (≡Eval (wk-comp (Up Id) w _) refl ex) es)

sub-comm2 : ∀{t s a b} → ∀ n
          → Eval sub t (shift n (Id , a)) ↘ b → Eval s ↘ a
          → Eval sub t (shift n (Id , s)) ↘ b
sub-comm2 {fvar x} n eFree es = eFree
sub-comm2 {bvar x} n et es =
  ≡Eval (id-wk 0 _) refl (sub-var-comm2 Id n x
    (≡Eval (sym (id-wk 0 _)) refl et) es)
sub-comm2 {lam t} n (eLam et) es = eLam (sub-comm2 {t} (suc n) et es)
sub-comm2 {t · s} n (eApp et et₁ x) es =
  eApp (sub-comm2 {t} n et es) (sub-comm2 {s} n et₁ es) x
