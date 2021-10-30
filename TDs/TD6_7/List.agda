open import Data.Nat
open import Relation.Binary.PropositionalEquality

-- 4 Lists.
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

-- 4.1 Length.
length : {A : Set} → List A → ℕ
length [] = 0
length (x ∷ l) = 1 + (length l)

-- 4.2 Concatenation.
concat : {A : Set} → List A → List A → List A
concat [] l = l
concat (h ∷ q) l = h ∷ (concat q l)

-- used in rev-concat (used in rev-fixpoint)
concat-[] : {A : Set} → (l : List A) → l ≡ concat l []
concat-[] [] = refl
concat-[] (h ∷ q) = cong (concat (h ∷ [])) (concat-[] q)

concat-length : {A : Set} → (k l : List A) → length (concat k l) ≡ length k + length l
concat-length [] l = refl
concat-length (x ∷ k) l = cong suc (concat-length k l)

concat-assoc : {A : Set} → (k l m : List A) → concat (concat k l) m ≡ concat k (concat l m)
concat-assoc [] l m = refl
concat-assoc (x ∷ k) l m = cong (concat (x ∷ [])) (concat-assoc k l m)

-- 4.3 List reversal.
snoc : {A : Set} → A → List A → List A 
snoc x l = concat l (x ∷ [])

-- used in rev-length
snoc-length : {A : Set} → (x : A) → (l : List A) → length (snoc x l) ≡ suc (length l)
snoc-length x [] = refl
snoc-length x (h ∷ q) = cong suc (snoc-length x q)

rev : {A : Set} → List A → List A
rev [] = []
rev (x ∷ l) = snoc x (rev l)

rev-length : {A : Set} → (l : List A) → length (rev l) ≡ length l
rev-length [] = refl
rev-length (x ∷ l) = trans (snoc-length x (rev l)) (cong suc (rev-length l))

-- used in rev-fixpoint
rev-concat : {A : Set} → (k l : List A) → rev (concat k l) ≡ concat (rev l) (rev k)
rev-concat [] l = concat-[] (rev l)
rev-concat (h ∷ q) l = trans (cong (snoc h) (rev-concat q l)) ((concat-assoc (rev l) (rev q) (h ∷ [])))

rev-fixpoint : {A : Set} → (l : List A) → rev (rev l) ≡  l
rev-fixpoint [] = refl
rev-fixpoint (x ∷ l) = trans (rev-concat (rev l) (x ∷ [])) (cong (concat (x ∷ [])) (rev-fixpoint l))

-- 4.4 Filtering.
open import Data.Bool

filter : {A : Set} → (p : A → Bool) → List A → List A
filter p [] = []
filter p (h ∷ q) with (p h)
filter p (h ∷ q) | true = h ∷ (filter p q)
filter p (h ∷ q) | false = filter p q

filter-false : {A : Set} → (l : List A) → filter (λ a → false) l ≡ []
filter-false [] = refl
filter-false (x ∷ l) = filter-false l

filter-true : {A : Set} → (l : List A) → filter (λ a → true) l ≡ l
filter-true [] = refl
filter-true (x ∷ l) = cong (concat (x ∷ [])) (filter-true l)

