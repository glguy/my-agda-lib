open import Algebra
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open CommutativeSemiring commutativeSemiring using (+-assoc; *-comm; +-comm)

module Data.Nat.Parity where

private
  m+1+n≡1+m+n : ∀ n m → n + suc m ≡ suc (n + m)
  m+1+n≡1+m+n zero    _ = refl
  m+1+n≡1+m+n (suc n) m = cong suc (m+1+n≡1+m+n n m)

data Odd : ℕ → Set
data Even : ℕ → Set

data Even where
  zero : Even 0
  suc : ∀ {n} → Odd n → Even (1 + n)

data Odd where
  suc : ∀ {n} → Even n → Odd (1 + n)

even-or-odd : ∀ n → Even n ⊎ Odd n
even-or-odd zero = inj₁ zero
even-or-odd (suc n) with even-or-odd n
... | inj₁ x = inj₂ (suc x)
... | inj₂ y = inj₁ (suc y)

double-even : ∀ n → Even (n + n)
double-even zero    = zero
double-even (suc n) = suc (subst Odd (sym (m+1+n≡1+m+n n n)) (suc (double-even n)))

even-+-even : ∀ {n m} → Even n → Even m → Even (n + m)
odd-+-even : ∀ {n m} → Odd n → Even m → Odd (n + m)

even-+-even zero    m = m
even-+-even (suc n) m = suc (odd-+-even n m)

odd-+-even (suc n) m = suc (even-+-even n m)

even-+-odd : ∀ {n m} → Even n → Odd m → Odd (n + m)
even-+-odd {n} {m} even-n odd-m = subst Odd (+-comm m n) (odd-+-even odd-m even-n)

even-* : ∀ {n} → Even n → (m : ℕ) → Even (n * m)
even-* zero          _ = zero
even-* (suc (suc n)) m = subst Even (+-assoc m _ _) (even-+-even (double-even m) (even-* n _))

*-even : ∀ {n} m → Even n → Even (m * n)
*-even {n} m even-n = subst Even (*-comm n m) (even-* even-n m)

odd-*-odd : ∀ {n m} → Odd n → Odd m → Odd (n * m)
odd-*-odd (suc n) m = odd-+-even m (even-* n _)

not-even-and-odd : ∀ {n} → Even n → Odd n → ⊥
not-even-and-odd zero        ()
not-even-and-odd (suc odd-n) (suc even-n) = not-even-and-odd even-n odd-n

odd-*-inv : ∀ n m → Odd (n * m) → Odd n × Odd m
odd-*-inv n m odd with even-or-odd n | even-or-odd m
... | inj₁ even-n | _ = ⊥-elim (not-even-and-odd (even-* even-n m) odd)
... | _ | inj₁ even-m = ⊥-elim (not-even-and-odd (*-even n even-m) odd)
... | inj₂ odd-n | inj₂ odd-m = odd-n , odd-m

even-*-inv : ∀ {n m} → Even (n * m) → Even n ⊎ Even m
even-*-inv {n} {m} even with even-or-odd n | even-or-odd m
... | inj₁ even-n | _ = inj₁ even-n
... | _ | inj₁ even-m = inj₂ even-m
... | inj₂ odd-n | inj₂ odd-m = ⊥-elim (not-even-and-odd even (odd-*-odd odd-n odd-m))

sqrt-even : ∀ n → Even (n * n) → Even n
sqrt-even n even-n² with even-*-inv even-n²
... | inj₁ even-n = even-n
... | inj₂ even-n = even-n

sqrt-odd : ∀ n → Odd (n * n) → Odd n
sqrt-odd n odd-n² = proj₁ (odd-*-inv n n odd-n²)

data Div2 : ℕ → Set where
  half : (k : ℕ) → Div2 (k + k)

even-div-2 : ∀ {n} → Even n → Div2 n
even-div-2 zero = half zero
even-div-2 (suc (suc n)) with even-div-2 n
... | half k = subst (Div2 ∘ suc) (m+1+n≡1+m+n k k) (half (suc k))

#-Set : ℕ → Set
#-Set n with even-or-odd n
... | inj₁ _ = Even n
... | inj₂ _ = Odd n

#_ : ∀ n → #-Set n
#_ n with even-or-odd n
... | inj₁ even-n = even-n
... | inj₂ odd-n = odd-n
