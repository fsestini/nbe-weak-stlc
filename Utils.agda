module Utils where

open import Data.Product
open import Data.Nat
open import Data.Empty
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

qwerty : ∀ m n → ¬ m ≤ n → m > n
qwerty zero zero p = ⊥-elim (p z≤n)
qwerty zero (suc n) p = ⊥-elim (p z≤n)
qwerty (suc m) zero p = s≤s z≤n
qwerty (suc m) (suc n) p = s≤s (qwerty m n (λ z → p (s≤s z)))

same≤ : ∀{x y} → (p q : x ≤ y) → p ≡ q
same≤ z≤n z≤n = refl
same≤ (s≤s p) (s≤s q) = cong s≤s (same≤ p q)

plus-succ : ∀ x y → x + suc y ≡ suc (x + y)
plus-succ zero y = refl
plus-succ (suc x) y = cong suc (plus-succ x y)

plus-0 : ∀ x → x + 0 ≡ x
plus-0 zero = refl
plus-0 (suc x) = cong suc (plus-0 x)

≤refl : ∀ x → x ≤ x
≤refl zero = z≤n
≤refl (suc x) = s≤s (≤refl x)

≤succ : ∀ {x y} → x ≤ y → x ≤ suc y
≤succ z≤n = z≤n
≤succ (s≤s p) = s≤s (≤succ p)

≤trans : ∀{p q r} → p ≤ q → q ≤ r → p ≤ r
≤trans z≤n z≤n = z≤n
≤trans z≤n (s≤s q) = z≤n
≤trans (s≤s p) (s≤s q) = s≤s (≤trans p q)

≤+ : ∀ {x y} z → x ≤ y → x ≤ (y + z)
≤+ z z≤n = z≤n
≤+ z (s≤s p) = s≤s (≤+ z p)

absurde : ∀ n m → suc n ≤ m → m ≤ n → ⊥
absurde zero zero () q
absurde zero (suc m) p ()
absurde (suc n) zero () q
absurde (suc n) (suc m) (s≤s p) (s≤s q) = absurde n m p q

≤suc> : ∀ x y → x ≤ y → suc y > x
≤suc> .0 y z≤n = s≤s z≤n
≤suc> .(suc _) .(suc _) (s≤s p) = s≤s (≤suc> _ _ p)

<-to-≤ : ∀{x y} → x < y → x ≤ y
<-to-≤ (s≤s p) = ≤trans p (≤succ (≤refl _))

inv-≤ : ∀{x y} → suc x ≤ suc y → x ≤ y
inv-≤ (s≤s p) = p

≤case : ∀{x y} → x ≤ y → x ≡ y ⊎ x < y
≤case {y = zero} z≤n = inj₁ refl
≤case {y = suc y} z≤n = inj₂ (s≤s z≤n)
≤case (s≤s p) with ≤case p
≤case (s≤s p) | inj₁ x = inj₁ (cong suc x)
≤case (s≤s p) | inj₂ y = inj₂ (s≤s y)
