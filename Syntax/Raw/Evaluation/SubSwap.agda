module Syntax.Raw.Evaluation.SubSwap where

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
open import Syntax.Raw.Evaluation.Properties
-- open import Syntax.Raw.Evaluation.NeTransfer

NeTransport : ∀{t σ a b} → Eval sub b σ ↘ a → Eval t ↘ b → Ne a → Ne b
NeTransport x eb ne with nfEval eb
NeTransport (eLam x) eb () | nfLam w
NeTransport _ _ _ | nfNe x = x

NeAppTransferLemma' : ∀{t t' t'' s s' s'' σ}
  → Eval sub (lam t'') σ ↘ lam t' → Eval sub s'' σ ↘ s'
  → Eval t ↘ lam t'' → Eval s ↘ s''
  → Ne (lam t' · s')
  → Ne (lam t'' · s'')
NeAppTransferLemma' (eLam et) es et' es' (neApp () x)
NeAppTransferLemma' {t'' = t''} (eLam et) es et' es' (lamApp₁ x x₁ x₂) with decSz 1 t''
NeAppTransferLemma' (eLam et) es et' es' (lamApp₁ x x₁ x₂) | inj₁ y =
  let aux = ¬Sz-sub-lemma 1 (Eval-¬Sz' et x₂) in ⊥-elim (¬Sz-lemma aux y)
NeAppTransferLemma' (eLam et) es et' es' (lamApp₁ x x₁ x₂) | inj₂ y =
  lamApp₁ (nfLamInv (nfEval et')) (nfEval es') y
NeAppTransferLemma' {t'' = t''} (eLam et) es et' es' (lamApp₂ x x₁ x₂ x₃) with decSz 1 t''
NeAppTransferLemma' (eLam et) es et' es' (lamApp₂ x x₁ x₂ x₃) | inj₁ x₄ =
  lamApp₂ ((nfLamInv (nfEval et'))) (nfEval es') x₄ (¬Sz-sub-lemma 0 (Eval-¬Sz' es x₃))
NeAppTransferLemma' (eLam et) es et' es' (lamApp₂ x x₁ x₂ x₃) | inj₂ y =
  lamApp₁ ((nfLamInv (nfEval et'))) (nfEval es') y

NeAppTransferLemma : ∀{t t' t'' s s' s'' σ}
  → Eval sub t'' σ ↘ t' → Eval sub s'' σ ↘ s'
  → Eval t ↘ t'' → Eval s ↘ s''
  → Ne (t' · s')
  → Ne (t'' · s'')
NeAppTransferLemma et es et' es' (neApp ne x) = 
  neApp (NeTransport et et' ne) (nfEval es')
NeAppTransferLemma et es et' es' (lamApp₁ _ _ _) with NeLamLemma (nfEval et') et
NeAppTransferLemma et es et' es' ne@(lamApp₁ _ _ _) | inj₁ x rewrite proj₂ x =
  NeAppTransferLemma' et es et' es' ne
NeAppTransferLemma et es et' es' (lamApp₁ _ _ _) | inj₂ y = neApp y (nfEval es')
NeAppTransferLemma et es et' es' (lamApp₂ _ _ _ _) with NeLamLemma (nfEval et') et
NeAppTransferLemma et es et' es' ne@(lamApp₂ _ _ _ _) | inj₁ x rewrite proj₂ x =
  NeAppTransferLemma' et es et' es' ne
NeAppTransferLemma et es et' es' (lamApp₂ _ _ _ _) | inj₂ y = neApp y (nfEval es')

record SubComp (t b : Term) (σ : Subst) : Set where
  field
    {tm} : Term
    ev1 : Eval t ↘ tm
    ev2 : Eval sub tm σ ↘ b
open SubComp

●-sub-swap : ∀{t t' s s' b σ}
            → SubComp t t' σ → SubComp s s' σ → t' ● s' ↘ b
            → SubComp (t · s) b σ
●-sub-swap {t} {_} {s} {_} {b} {σ} ih ih' ap@(●β rdx ev) = goal
  where
    rdx? = decβ-Redex' (nfEval (ev1 ih)) (nfEval (ev1 ih'))
      (NeLamLemma (nfEval (ev1 ih)) (ev2 ih))
    goal : SubComp (t · s) b σ
    goal with rdx?
    goal | inj₁ (q ,, tee ,, p) =
      record { ev1 = eApp (ev1 ih) (ev1 ih') (≡App (sym p)
                          refl refl (●β brdx evl)) ; ev2 = evlb }
      where
        e1 = ≡Eval (null-sub (β-Redex-Sz-t q)) refl (ev2 ih)
        e2 = ≡Eval (null-sub (β-Redex-Sz-s q)) refl (ev2 ih')
        lam-eq = trans (sym p) (Eval-fun (nfSelf (nfEval (ev1 ih))) e1)
        ss-eq = Eval-fun (nfSelf (nfEval (ev1 ih'))) e2
        brdx : β-Redex (lam tee) (tm ih')
        brdx rewrite lam-eq | ss-eq = rdx
        evl : Eval sub tee (Id , tm ih') ↘ _
        evl = ≡Eval (cong₂ sub (sym (Lam-inj lam-eq))
          (cong₂ _,_ refl (sym ss-eq))) refl ev
        evlb : Eval sub b σ ↘ b
        evlb = ≡Eval (sym (null-sub (Eval-Sz (sub-cover-lemma 0 0
          (β-Redex-Sz-Lam-t rdx) (β-Redex-Sz-s rdx)) ev)))
            refl (nfSelf (nfEval ev))
    goal | inj₂ y =
      record { ev1 = eApp (ev1 ih) (ev1 ih') (●Ne y)
             ; ev2 = eApp (ev2 ih) (ev2 ih') ap }
●-sub-swap {t} {_} {s} ih ih' (●Ne x) =
  record { ev1 = eApp (ev1 ih) (ev1 ih')
                   (●Ne (NeAppTransferLemma (ev2 ih) (ev2 ih') (ev1 ih) (ev1 ih') x))
         ; ev2 = eApp (ev2 ih) (ev2 ih') (●Ne x) }

sub-swap : ∀{t σ b} → Eval sub t σ ↘ b → SubComp t b σ
sub-swap {fvar x} eFree = record { ev1 = eFree ; ev2 = eFree }
sub-swap {bvar x} e = record { ev1 = eBound ; ev2 = e }
sub-swap {lam t} (eLam e) = record { ev1 = eLam (ev1 ih) ; ev2 = eLam (ev2 ih) }
  where ih = sub-swap {t} e
sub-swap {t · s} (eApp e e₁ x) = ●-sub-swap (sub-swap {t} e) (sub-swap {s} e₁) x

sub-swap' : ∀{t a b σ} → Eval t ↘ a → Eval sub t σ ↘ b → Eval sub a σ ↘ b
sub-swap' {t} e1 e2 with sub-swap {t} e2
sub-swap' e1 e2 | record { tm = tm ; ev1 = ev1 ; ev2 = ev2 } =
  ≡Eval (cong₂ sub (Eval-fun ev1 e1) refl) refl ev2

sub-comm : ∀{t a b σ σ'}
         → Eval sub t σ ↘ b → Eval sub t (σ ·ˢ σ') ↘ a → Eval sub b σ' ↘ a
sub-comm {t} {σ = σ} {σ'} e1 e2
  rewrite sym (sub-comp {σ} {σ'} t) = sub-swap' e1 e2

●-sub-swap' : ∀{t t' s s' b σ}
             → Nf t → Nf s
             → Eval sub t σ ↘ t' → Eval sub s σ ↘ s' → t' ● s' ↘ b
             → Σ Term λ a → t ● s ↘ a × Eval sub a σ ↘ b
●-sub-swap' {t} {_} {s} nft ns et es ap 
  with ●-sub-swap {t = t} {s = s} (sub-swap et) (sub-swap es) ap
●-sub-swap' nft nfs et es ap | record { tm = tm ; ev1 = eApp ev3 ev4 x ; ev2 = ev2 } 
  rewrite Eval-fun (nfSelf nft) ev3 | Eval-fun (nfSelf nfs) ev4 = _ ,, x ,, ev2

sub-unswap : ∀{t a b σ} → Eval t ↘ a → Eval sub a σ ↘ b → Eval sub t σ ↘ b
sub-unswap eBound e2 = e2
sub-unswap eFree e2 = e2
sub-unswap (eLam e1) (eLam e2) = eLam (sub-unswap e1 e2)
sub-unswap e@(eApp e1 e3 ap@(●β (βrdx x x₂) x₁)) e2 =
  ≡Eval (sym (null-sub (tmApp (Eval-Sz' e1 (tmLam x)) (Eval-Sz' e3 x₂))))
    (Eval-fun (≡Eval (sym (null-sub (Eval-Sz
      (sub-cover-lemma 0 0 x x₂) x₁))) refl (nfSelf (nfEval x₁))) e2) e
sub-unswap (eApp e1 e3 (●Ne x)) (eApp e2 e4 x₁) =
  eApp (sub-unswap e1 e2) (sub-unswap e3 e4) x₁

sub-uncomm : ∀{t a b σ σ'}
           → Eval sub t σ ↘ a → Eval sub a σ' ↘ b → Eval sub t (σ ·ˢ σ') ↘ b
sub-uncomm {t} e1 e2 = ≡Eval (sub-comp t) refl (sub-unswap e1 e2)
