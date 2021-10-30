-- 7 Euclidean division.
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)
open import Agda.Builtin.Sigma
open import Relation.Nullary

-- 7.1 Optional: definition.
≤-cases : (n m : ℕ) → (n ≤ m) ∨ (suc m ≤ n)
≤-cases zero m = left z≤n
≤-cases (suc n) zero = right (s≤s z≤n)
≤-cases (suc n) (suc m) with ≤-cases n m 
≤-cases (suc n) (suc m) | left x = left (s≤s x)
≤-cases (suc n) (suc m) | right y = right (s≤s y)

_-_ :(m n : ℕ) → {n≤m : n ≤ m} → ℕ
zero - zero = zero
suc m - zero = suc m
(suc m - suc n) {s≤s e} = (m - n) {e}

test- = (10 - 0) {z≤n}

{-# TERMINATING #-}
quotient : (m n : ℕ) → {e : 1 ≤ n} → ℕ
quotient zero n = zero
quotient m n with ≤-cases n m
quotient m n {e} | left p = suc (quotient ((m - n) {p}) n {e})
quotient m n | right p = zero

test-quotient = quotient 11 3

lemma-1 : (k m n : ℕ) (k≤n : k ≤ n) → m ≤ (n - k) {k≤n} → k + m ≤ n
lemma-1 zero m zero z≤n e = e
lemma-1 zero m (suc n) z≤n e = e 
lemma-1 (suc k) m (suc n) (s≤s k≤n) e = s≤s (lemma-1 k m n k≤n e)

{-# TERMINATING #-}
lemma : (m n : ℕ) {e : 1 ≤ n} → ((quotient m n {e}) * n) ≤ m
lemma zero (suc n) = z≤n
lemma (suc m) (suc n) with ≤-cases (suc n) (suc m)
lemma (suc m) (suc n) {e} | left p = lemma-1 (suc n) (quotient ((suc m - suc n) {p}) (suc n) {e} * (suc n)) (suc m) p (lemma ((suc m - suc n) {p}) (suc n) {e}) 
lemma (suc m) (suc n) | right p = z≤n

{-# TERMINATING #-}
remainder : (m n : ℕ) → {e : 1 ≤ n} → ℕ
remainder m n {e} = (m - ((quotient m n {e}) * n)) {lemma m n {e}}

test-remainder = remainder 11 3

-- 7.2 Optional: correctness.
lemma' : (a b : ℕ) {a≤b : a ≤ b} → (b ≡ a + ((b - a) {a≤b}))
lemma' zero zero {z≤n} = refl
lemma' zero (suc b) {z≤n} = refl
lemma' (suc a) (suc b) {s≤s e} = cong suc (lemma' a b {e})

div : (m n : ℕ) {e : 1 ≤ n} → m ≡ ((quotient m n {e}) * n) + (remainder m n {e})
div m n {e} = lemma' ((quotient m n {e}) * n) m

test-div : 11 ≡ ((quotient 11 3 {s≤s z≤n}) * 3) + (remainder 11 3 {s≤s z≤n})
test-div = div 11 3 {s≤s z≤n}

-- 7.3 Optional: internal approach.
n+z≤m : {n m : ℕ} → n ≤ m → n + zero ≤ m
n+z≤m z≤n = z≤n
n+z≤m (s≤s p) = s≤s (n+z≤m p)

{-# TERMINATING #-}
div' : (m n : ℕ) {e : 1 ≤ n} {p : (n ≤ m) ∨ (suc m ≤ n)} → Σ ℕ (λ q → Σ ℕ (λ r → m ≡ (q * n + r)))
div' zero n = zero , zero , refl
div' (suc m) n {e} {right p} = zero , suc m , refl
div' (suc m) n {e} {left p} with  div' (((suc m) - n) {p}) n {e} {≤-cases n (suc m - n)}
div' (suc m) n {e} {left p} | zero , r , p' = suc zero , (suc m - ((suc zero) * (n))) {n+z≤m p} , lemma' ((suc zero) * n) (suc m)
div' (suc m) n {e} {left p} | suc q , r , p' = suc (suc q) , (suc m - ((suc (suc q)) * (n))) {{!!}} , lemma' ((suc (suc q)) * n) (suc m)
