module Explicit.Semantics.Completeness.SemanticType where

open import Data.Sum
open import Data.Empty
open import Data.Nat
open import Data.Product renaming (_,_ to _,,_)
open import Data.Maybe hiding (ap)
open import Syntax.Raw
open import Explicit.Semantics.Domain
open import Relation.Binary.PropositionalEquality

_∈ₜ_ : D → (D → Set) → Set
d ∈ₜ T = T d

record SemTy : Set₁ where
  field
    P : D → Set
    isNf  : ∀{a} → P a → Nf a
    hasNe : ∀{e} → Ne e → P e
open SemTy

infix 4 _∈_
record _∈_ (a : D) (A : SemTy) : Set where
  no-eta-equality
  pattern
  constructor in∈
  field
    wit : a ∈ₜ P A
open _∈_

hasFree : ∀{A x} → fvar x ∈ A
hasFree {A} = in∈ (hasNe A neFree)

hasBound : ∀{A x} → bvar x ∈ A
hasBound {A} = in∈ (hasNe A neBound)

infix 4 ⟦_⟧≃⟦_⟧_∈tm_
record ⟦_⟧≃⟦_⟧_∈tm_ (t t' : Term) (ρ : Subst) (T : SemTy) : Set where
  constructor ⟨_∣_∣_⟩
  field
    {d} : D
    ∈tm : d ∈ T
    ↘tm1 : t [ ρ ]↘ d
    ↘tm2 : t' [ ρ ]↘ d

record _●_∈ap_ (f a : D) (B : SemTy) : Set where
  field
    {res} : D
    ∈tm   : res ∈ B
    ↘ap  : f ● a ↘ res
open _●_∈ap_

--------------------------------------------------------------------------------

FunP : SemTy → SemTy → D → Set
FunP A B f = Nf f × (∀{a w} → P A a → wk f w ● a ∈ap B)

infixr 6 _==>_
_==>_ : SemTy → SemTy → SemTy
A ==> B = record { P = FunP A B ; isNf = proj₁ ; hasNe = has-ne }
  where
    has-ne : {e : Term} → Ne e → FunP A B e
    has-ne {e} ne = nfNe ne ,, aux
      where
        aux : ∀{a w} → P A a → wk e w ● a ∈ap B
        aux pa = record { ∈tm = in∈ (hasNe B nee) ; ↘ap = ●Ne nee }
          where nee = neApp (neWkLemma ne) (isNf A pa)

⟦_⟧ₜ : Ty → SemTy
⟦ A => Q ⟧ₜ = ⟦ A ⟧ₜ ==> ⟦ Q ⟧ₜ

liftD : ∀{A w d} → d ∈ ⟦ A ⟧ₜ → wk d w ∈ ⟦ A ⟧ₜ
liftD {A => B} {w} {f} (in∈ (nf ,, h)) = in∈ ((nfWkLemma nf) ,, aux)
  where
    aux : ∀{a w'} → P ⟦ A ⟧ₜ a → wk (wk f w) w' ● a ∈ap ⟦ B ⟧ₜ
    aux {a} {w'} p rewrite wk-comp w w' f = h {a} {w ·ʷ w'} p

_∈ₛ_ : Subst → (Subst → Set) → Set
ρ ∈ₛ S = S ρ

data ⟦_⟧ₛ :  Ctxt → Subst → Set where
  cId   : ∀{ρ} → ⟦ ◇ ⟧ₛ ρ
  cCons : ∀{Γ A ρ d} → ρ ∈ₛ ⟦ Γ ⟧ₛ → d ∈ₜ P ⟦ A ⟧ₜ → ⟦ Γ # A ⟧ₛ (ρ , d)
  cWk   : ∀{Γ w ρ} → ρ ∈ₛ ⟦ Γ ⟧ₛ → ⟦ Γ ⟧ₛ (ρ · w)

infix 4 _⊧_≃_∶_
_⊧_≃_∶_ : Ctxt → Term → Term → Ty → Set
Γ ⊧ t ≃ t' ∶ A = ∀{ρ} → ρ ∈ₛ ⟦ Γ ⟧ₛ → ⟦ t ⟧≃⟦ t' ⟧ ρ ∈tm ⟦ A ⟧ₜ

infix 4 _⊧_∶_
_⊧_∶_ : Ctxt → Term → Ty → Set
Γ ⊧ t ∶ A = Γ ⊧ t ≃ t ∶ A

--------------------------------------------------------------------------------

open SemTy
open _∈_
open ⟦_⟧≃⟦_⟧_∈tm_
open _●_∈ap_

≡ap : ∀{f g a A} → f ≡ g → f ● a ∈ap A → g ● a ∈ap A
≡ap refl x = x

appLemma : ∀{A B} {f a : D} → f ∈ A ==> B → a ∈ A → f ● a ∈ap B
appLemma {A} {f = f} (in∈ (_ ,, h)) (in∈ a) = ≡ap (id-wk 0 f) (h {w = Id} a)

tmAppLemma : ∀{A B t t' s s' ρ}
           → ⟦ t ⟧≃⟦ t' ⟧ ρ ∈tm ⟦ A => B ⟧ₜ
           → ⟦ s ⟧≃⟦ s' ⟧ ρ ∈tm ⟦ A ⟧ₜ
           → ⟦ t · s ⟧≃⟦ t' · s' ⟧ ρ ∈tm ⟦ B ⟧ₜ
tmAppLemma t s =
  ⟨ ∈tm ap ∣ eApp (↘tm1 t) (↘tm1 s) (↘ap ap) ∣ eApp (↘tm2 t) (↘tm2 s) (↘ap ap) ⟩
  where ap = appLemma (∈tm t) (∈tm s)

shLemma : ∀{A B ρ t t'}
         → (∀{a w} → a ∈ ⟦ A ⟧ₜ → ⟦ t ⟧≃⟦ t' ⟧ (ρ · w , a) ∈tm ⟦ B ⟧ₜ)
         → ⟦ t ⟧≃⟦ t' ⟧ sh ρ ∈tm ⟦ B ⟧ₜ
shLemma h = h hasBound

tmLamLemma : ∀{A B ρ t t'}
           → (∀{a w} → a ∈ ⟦ A ⟧ₜ → ⟦ t ⟧≃⟦ t' ⟧ (ρ · w , a) ∈tm ⟦ B ⟧ₜ)
           → ⟦ lam t ⟧≃⟦ lam t' ⟧ ρ ∈tm ⟦ A => B ⟧ₜ
tmLamLemma {A} {B} {ρ} {t} {t'} ht' =
  ⟨ in∈ (nfl ,, goal) ∣ eLam (↘tm1 ht) ∣ eLam (↘tm2 ht) ⟩
  where
    ht = shLemma {A} {B} ht'
    nfl = nfLam (nfEval (↘tm1 ht))
    goal : ∀{a w} → P ⟦ A ⟧ₜ a → lam (wk (d ht) (Skip w)) ● a ∈ap ⟦ B ⟧ₜ
    goal pa with decβ-Redex (nfWkLemma nfl) (isNf ⟦ A ⟧ₜ pa)
    goal {a} {w} pa | inj₁ x = 
      record { ∈tm = ∈tm aux ; ↘ap = ●β x (sub-comm {t} e1 e2) }
      where
        aux = ht' (in∈ pa)
        e1 = ≡Eval (trans (wk-subst t) (eq-sub sh-skip t)) refl (wkEval (↘tm1 ht))
        e2 = ≡Eval (eq-sub (consˢ (symmˢ sub-id-L)) t) refl (↘tm1 aux)
    goal pa | inj₂ y = record { ∈tm = in∈ (hasNe ⟦ B ⟧ₜ y) ; ↘ap = ●Ne y }

Eval0 : ∀{n t d ρ} → Sz n t → Eval sub t (shift n ρ) ↘ d → Sz n d
Eval0 {n} tm e = Eval-Sz (subst (Sz n) (sym (null-sub tm)) tm) e

tmSubLemma : ∀{t ρ t' s s' d}
           → t [ sh ρ ]↘ t' → s [ ρ ]↘ s' → t' [ Id , s' ]↘ d
           → sub t (Id , s) [ ρ ]↘ d
tmSubLemma {t} {ρ} {t'} {s} {s'} {d} e1 e3 sb =
  ≡Eval (trans (sub-comp t) (sym (trans (sub-comp t)
    (eq-sub (transˢ (sub-comp-R {s} Id ρ) (consˢ (transˢ (id-comp-L ρ)
      (symmˢ sub-id-L)))) t)))) refl uhm
  where
    uhm : Eval sub (sub t (sh ρ)) (Id , sub s ρ) ↘ d
    uhm = sub-comm2 {sub t (sh ρ)} 0 (sub-unswap e1 sb) e3

tmβLemma : ∀{A B t s ρ}
         → ⟦ lam t ⟧≃⟦ lam t ⟧ ρ ∈tm ⟦ A => B ⟧ₜ
         → ⟦ s ⟧≃⟦ s ⟧ ρ ∈tm ⟦ A ⟧ₜ
         → Sz 1 t → Sz 0 s
         → ⟦ lam t · s ⟧≃⟦ sub t (Id , s) ⟧ ρ ∈tm ⟦ B ⟧ₜ
tmβLemma {A} {B} l s tmt tms with tmAppLemma {A = A} {B = B} l s
tmβLemma {t = t} l sp tmt tms 
  | ⟨ x ∣ ap@(eApp (eLam e1) e3 (●β _ sb)) ∣ _ ⟩ = 
    ⟨ x ∣ ap ∣ tmSubLemma {t} e1 e3 sb ⟩
tmβLemma _ _ tmt tms | ⟨ x ∣ eApp (eLam e1) e3 (●Ne ne) ∣ _ ⟩ = 
  ⊥-elim (neBeta ne (Eval0 tmt e1) (Eval0 tms e3))
