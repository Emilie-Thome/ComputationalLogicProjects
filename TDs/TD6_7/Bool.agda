-- 1 Booleans.
-- 1.1 The type of booleans.
data Bool : Set where
  true  : Bool
  false : Bool

-- 1.2 Negation.
not : Bool → Bool
not true = false
not false = true

-- 1.3 Conjunction.
_∧_ : Bool → Bool → Bool
true ∧ true = true
a ∧ false = false
false ∧ b = false

-- 1.4 Disjunction.
_∨_ : Bool → Bool → Bool
false ∨ false = false
a ∨ true = true
true ∨ b = true

-- 2 Equality.
data _≡_ {A : Set} (x : A) : (y : A) → Set where
  refl : x ≡ x

infix 4 _≡_

-- 2.1 Negation is involutive.
not-inv : (b : Bool) → not (not b) ≡ b
-- We have to give a b = true or a b = false.
not-inv true = refl
not-inv false = refl

-- 2.2 Conjunction and negation.
conj-neg : (b : Bool) → (not b) ∧ b ≡ false
conj-neg true = refl
conj-neg false = refl
