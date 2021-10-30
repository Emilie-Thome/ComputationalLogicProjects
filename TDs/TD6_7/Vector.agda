-- 6 Vectors.
open import Data.List hiding (zip ; length)
open import Data.Nat
open import Data.Product hiding (zip)
open import Relation.Binary.PropositionalEquality

-- 6.1 Warmup.
--head : {A : Set} → List A → A
--head [] = ???????? no head for empty list
--head (h ∷ q) = h

-- 6.2 Definition.
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (1 + n)

-- 6.3 Head and tail.
head-vec : {A : Set} {n : ℕ} → Vec A (1 + n) → A
head-vec (h ∷ q) = h

tail-vec : {A : Set} {n : ℕ} → Vec A (1 + n) → Vec A n
tail-vec (h ∷ q) = q

-- 6.4 Concatenation.
concat-vec : {A : Set} {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
concat-vec [] v = v
concat-vec (h ∷ q) v = h ∷ (concat-vec q v)

-- 6.5 Reversal.
snoc-vec : {A : Set} → {n : ℕ} → A → Vec A n → Vec A (suc n)
snoc-vec x [] = x ∷ []
snoc-vec x (h ∷ q) = h ∷ (snoc-vec x q)

-- The snoc-vec function is very important here to prove that if we add an
-- element at the end of the vector then the vector has a length of suc n.
-- The snoc function for lists was only useful to verify that the length of
-- a reversed list is the same as the length of the list, but as here we
-- need it to prove this directly in the definition of the function rev-vec
-- then the function snoc-rev is extremely important (I say that because I
-- tried many hours to make the function rev-vec works and I think it is an
-- important answer to show that the exercice is understood).

rev-vec : {A : Set} → {n : ℕ} → Vec A n → Vec A n
rev-vec [] = []
rev-vec (h ∷ q) = snoc-vec h (rev-vec q)

-- 6.6 Accessing an element.
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

ith : {A : Set} → {n : ℕ} → Fin n → Vec A n → A
ith zero (h ∷ q) = h
ith (suc i) (h ∷ q) = ith i q

-- 6.7 Zipping.
zip : {A B : Set} {n : ℕ} -> Vec A n → Vec B n → Vec (A × B) n
zip [] [] = []
zip (ha ∷ qa) (hb ∷ qb) = (ha , hb) ∷  (zip qa qb)

-- 6.8 Optional: associativity of concatenation.
--concat-assoc : {A : Set} → {n m k : ℕ} → (u : Vec A n) → (v : Vec A m) → (w : Vec A k) → (concat-vec (concat-vec u v) w) ≡ (concat-vec u (concat-vec v w))
-- The length of the resulted vector is not proved when the function is defined so we can (because it is a part of what we want to prove...) but it is needed in the type inferrence of the vector. 

coe : {A B : Set} → A ≡ B → A → B
coe refl = λ z → z

length : {A : Set} {n : ℕ} → Vec A n → ℕ
length {A} {n} l = n

length-≡ : {A : Set} {n n' : ℕ} → n ≡ n' → Vec A n ≡ Vec A n'
length-≡ refl = refl

cons-≡ : {A : Set} {n n' : ℕ} → (e : n' ≡ n) → (x : A) → (l : Vec A n) → (l' : Vec A n') → l ≡ (coe (length-≡ e) l') → x ∷ l ≡ (coe (length-≡ (cong suc e)) (x ∷ l'))
cons-≡ refl = λ x l l' e → cong (λ l → x ∷ l) e

+-assoc : (m n p : ℕ) → m + (n + p) ≡ (m + n) + p
+-assoc zero n p = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)

concat-assoc : {A : Set} → {n m k : ℕ} → (u : Vec A n) → (v : Vec A m) → (w : Vec A k) → (concat-vec (concat-vec u v) w) ≡ coe (length-≡ (+-assoc n m k)) (concat-vec u (concat-vec v w))
concat-assoc [] v w = refl
concat-assoc (x ∷ u) v w = cons-≡ (+-assoc (length u) (length v) (length w)) x (concat-vec (concat-vec u v) w) (concat-vec u (concat-vec v w)) (concat-assoc u v w)


data _≅_ : {A B : Set} (x : A) (y : B) → Set where
  refl : {A : Set} {x : A} → x ≅ x

cong-≅ : {A B : Set} (f : A → B) {x y : A} → x ≅ y → f x ≅ f y
cong-≅ f refl = refl

cons-≅ : {A : Set} {n n' : ℕ} → (e : n' ≅ n) → (x : A) → (l : Vec A n) → (l' : Vec A n') → l ≅ l' → (concat-vec (x ∷ []) l) ≅ (concat-vec (x ∷ []) l')
cons-≅ refl x l l' refl = refl

+-assoc-≅ : (m n p : ℕ) → (m + (n + p)) ≅ ((m + n) + p)
+-assoc-≅ zero n p = refl
+-assoc-≅ (suc m) n p = cong-≅ suc (+-assoc-≅ m n p)

concat-assoc-≅ : {A : Set} → {n m k : ℕ} → (u : Vec A n) → (v : Vec A m) → (w : Vec A k) → (concat-vec (concat-vec u v) w) ≅ (concat-vec u (concat-vec v w))
concat-assoc-≅ [] v w = refl
concat-assoc-≅ (x ∷ u) v w = cons-≅ (+-assoc-≅ (length u) (length v) (length w)) x (concat-vec (concat-vec u v) w) (concat-vec u (concat-vec v w)) (concat-assoc-≅ u v w)
