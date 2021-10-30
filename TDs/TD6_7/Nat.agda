open import Relation.Nullary
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)

-- 3 Natural numbers.
-- 3.1 Definition.
data ℕ : Set where
  zero  : ℕ
  suc   : ℕ → ℕ 

-- 3.2 Addition.
_+_ : ℕ → ℕ → ℕ
zero + m = m
(suc n) + m = suc (n + m)

-- 3.3 Multiplication.
_*_ : ℕ → ℕ → ℕ
zero * m = zero
(suc n) * m = m + (n * m)

-- 3.4 Equality is a congruence for successor.
data _≡_ {A : Set} (x : A) : (y : A) → Set where
  refl : x ≡ x

infix 4 _≡_

suc-≡ : {m n : ℕ} → (m ≡ n) → (suc m ≡ suc n)
suc-≡ refl = refl
-- The case analysis only give e = refl.
-- This is because it is the only possible option
-- and it implies that n = m because refl is of
-- type m ≡ m. And, because n = m, we can replace
-- n in (suc n) by m and so (suc n) = (suc m).
-- Therefore the second refl is of type (suc m) ≡ (suc m)
-- ie (suc m) ≡ (suc n).
-- 3.5 Some properties.
zadd-≡ : {n : ℕ} → ((zero + n) ≡ n)
zadd-≡ = refl

addz-≡ : (n : ℕ) → ((n + zero) ≡ n)
addz-≡ zero = refl
addz-≡ (suc n) = suc-≡ (addz-≡ n)

asso-≡ : (m n p : ℕ) → ((m + n) + p) ≡ (m + (n + p))
asso-≡ zero n p = refl
asso-≡ (suc m) n p = suc-≡ (asso-≡ m n p)

asso-suc-≡ : (m n : ℕ) → (suc (m + n)) ≡ (m + (suc n))
asso-suc-≡ zero n = refl
asso-suc-≡ (suc m) n = suc-≡ (asso-suc-≡ m n)

nonz-≡ : {n : ℕ} →  ¬ (zero ≡ (suc n))
nonz-≡ = λ ()

-- 3.6 The recurrence principle.
rec-principle : (p : ℕ → Set) → p(zero) → ((n : ℕ) → (p(n) → p(suc n))) → ((m : ℕ) → p(m))
rec-principle p p0 rec zero = p0
rec-principle p p0 rec (suc n) = rec n (rec-principle p p0 rec n)

zadd'-≡ : (n : ℕ) → ((zero + n) ≡ n)
zadd'-≡ = rec-principle (λ n → ((zero + n) ≡ n)) refl (λ n e → suc-≡ e)

-- 3.7 More equality.
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl e = e

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

suc'-≡ : {m n : ℕ} → (m ≡ n) → (suc m ≡ suc n)
suc'-≡ = cong suc

-- 3.8 Commutativity of addition.

comm-≡ : (m n : ℕ) → (m + n ≡ n + m)
comm-≡ m zero = addz-≡ m
comm-≡ m (suc n) = trans (sym (asso-suc-≡ m n)) ((suc-≡ (comm-≡ m n)))

-- 3.9 Injectivity of successor.
inj-suc-≡ : {m n : ℕ} → (suc m ≡ suc n) → (m ≡ n)
inj-suc-≡ refl = refl

-- 3.10 Decidability of equality.
deci-≡ : (m n : ℕ) → (m ≡ n) ∨ ¬ (m ≡ n)
deci-≡ zero zero = left refl
deci-≡ zero (suc n) = right (λ())
deci-≡ (suc m) zero = right (λ())
deci-≡ (suc m) (suc n) with deci-≡ m n
deci-≡ (suc m) (suc n) | left e = left (cong suc e)
deci-≡ (suc m) (suc n) | right e' = right (λ e → e' (inj-suc-≡ e))

-- 3.11 Recurrence for equality.
J : (A : Set) → (P : (x : A) → (y : A) → (p : x ≡ y) → Set) → (r : (x : A) → P x x refl) → (x : A) → (y : A) → (e : x ≡ y) → P x y e
J A P r x x refl = r x
-- This means that if we have the proof that x ≡ y then
-- we have the proof of (P x y relf) which is proved by (r x) 

-- 3.12 Properties of multiplication.
multz-≡ : (n : ℕ) → ((n * zero) ≡ zero)
multz-≡ zero = refl
multz-≡ (suc n) = multz-≡ n

mult1-≡ : (n : ℕ) → ((n * (suc zero)) ≡ n)
mult1-≡ zero = refl
mult1-≡ (suc n) = suc-≡ (mult1-≡ n)

dist-≡ : (m n p : ℕ) → ((p * (m + n)) ≡ ((p * m) + (p * n)))
dist-≡ m n zero = refl
dist-≡ m n (suc p) = trans (trans (cong (λ k → (m + n) + k) (dist-≡ m n p)) (asso-≡ m n ((p * m) + (p * n)))) (trans ((cong (λ k → m + k) (sym (asso-≡ n (p * m) (p * n))))) (trans (cong (λ k → m + (k + (p * n))) (comm-≡ n (p * m))) (trans (cong (λ k → m + k) (asso-≡ (p * m) n (p * n))) (sym (asso-≡ m (p * m) (n + (p * n)))))))

comm*-≡ : (m n : ℕ) → (m * n ≡ n * m)
comm*-≡ m zero = multz-≡ m
comm*-≡ m (suc n) = trans (trans ((dist-≡ (suc zero) n m)) (cong (λ k → k + (m * n)) (mult1-≡ m))) ( (cong (λ k → m + k) (comm*-≡ m n)))

assoc*-≡ : (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
assoc*-≡ zero n p = refl
assoc*-≡ (suc m) n p = trans (trans (trans (comm*-≡ (n + (m * n)) p) (dist-≡ n (m * n) p)) (trans (cong (λ k → k + (p * (m * n))) (comm*-≡ p n)) (cong (λ k → (n * p) + k) (comm*-≡ p (m * n))))) (cong (λ k → (n * p) + k) (assoc*-≡ m n p))
