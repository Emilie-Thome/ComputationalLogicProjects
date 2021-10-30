open import Relation.Binary.PropositionalEquality
open import Data.Unit using (⊤ ; tt)
open import Data.Product renaming (_×_ to _∧_ ; proj₁ to fst ; proj₂ to snd)
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)
open import Data.List hiding (length ; head)

-- 1 Order on natural numbers.
data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ}                 → zero  ≤ n
  s≤s : {m n : ℕ} (m≤n : m ≤ n) → suc m ≤ suc n

-- 1.1 Compatibility with successor.
≤-pred : {m n : ℕ} → (suc m ≤ suc n) → m ≤ n
≤-pred (s≤s e) = e

≤-suc : {m n : ℕ} → m ≤ n → suc m ≤ suc n
≤-suc e = s≤s e

≤s : (n : ℕ) → n ≤ suc n
≤s zero = z≤n
≤s (suc n) = s≤s (≤s n)

-- 1.2 Reflexivity.
≤-refl : (n : ℕ) → n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

-- 1.3 Transitivity.
≤-trans : {m n p : ℕ} → (m ≤ n) → (n ≤ p) → (m ≤ p)
≤-trans z≤n e = z≤n
≤-trans (s≤s e1) (s≤s e2) = s≤s (≤-trans e1 e2)

-- 1.4 Totality.
_≤?_ : (m n : ℕ) → (m ≤ n) ∨ (n ≤ m)
zero ≤? n = left z≤n
m ≤? zero = right z≤n
(suc m) ≤? (suc n) with m ≤? n
(suc m) ≤? (suc n) | left e = left (s≤s e)
(suc m) ≤? (suc n) | right e = right (s≤s e)

-- 2 Insertion sort.
-- 2.1 Insertion.
insert : (x : ℕ) → (l : List ℕ) → List ℕ
insert x [] = x ∷ []
insert x (h ∷ q) with x ≤? h
insert x (h ∷ q) | left e = x ∷ (h ∷ q)
insert x (h ∷ q) | right e = h ∷ (insert x q)

-- 2.2 Sorting.
sort : List ℕ → List ℕ
sort [] = []
sort (h ∷ q) = insert h (sort q)

test-sort : List ℕ
test-sort = sort (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

-- 2.3 The bounded below predicate.
data _≤*_ : (x : ℕ) → (l : List ℕ) → Set where
  n≤*[] : {n : ℕ}                 → n ≤* []
  n≤*∷  : {n h : ℕ} {q : List ℕ} (n≤*q : n ≤* q) (n≤h : n ≤ h) → n ≤* (h ∷ q)
  
-- 2.4 The sorted predicate.
sorted : (l : List ℕ) → Set
sorted [] = zero ≤* [] -- zero is considered as a default number here
sorted (h ∷ q) = (h ≤* q) ∧ (sorted q)

-- 2.5 Insert is sorting.
≤*-trans : {m n : ℕ} {l : List ℕ} → n ≤* l → m ≤ n → m ≤* (l)
≤*-trans n≤*[] e = n≤*[]
≤*-trans (n≤*∷ e1 n≤h) e2 = n≤*∷ (≤*-trans e1 e2) (≤-trans e2 n≤h)

insert-trans : {m n : ℕ} {l : List ℕ} → n ≤* l → n ≤ m → n ≤* (insert m l)
insert-trans n≤*[] e = n≤*∷ n≤*[] e
insert-trans {m} {n} {h ∷ q} (n≤*∷ e1 n≤h) e2 with m ≤? h 
insert-trans {m} {n} {h ∷ q} (n≤*∷ e1 n≤h) e2 | left e = n≤*∷ (n≤*∷ e1 n≤h) e2
insert-trans {m} {n} {h ∷ q} (n≤*∷ e1 n≤h) e2 | right e = n≤*∷ (insert-trans e1 e2) n≤h

insert-sorting : (x : ℕ) → (l : List ℕ) → sorted l → sorted (insert x l)
insert-sorting x [] n≤*[] = n≤*[] , n≤*[]
insert-sorting x (h ∷ q) (p1 , p2) with x ≤? h
insert-sorting x (h ∷ q) (p1 , p2) | left e = n≤*∷ (≤*-trans p1 e) e , p1 , p2
insert-sorting x (h ∷ q) (p1 , p2) | right e = insert-trans p1 e , insert-sorting x q p2

-- 2.6 Sort is sorting.
sort-sorting : (l : List ℕ) → sorted (sort l)
sort-sorting [] = n≤*[]
sort-sorting (h ∷ q) = insert-sorting h (sort q) (sort-sorting q)

-- 2.7 The problem of specification.
f : List ℕ → List ℕ
f l = []

f-sorting : (l : List ℕ) → sorted (f l)
f-sorting l = n≤*[]
-- The sorting proof only proves that the returned list is A sorted list and not THE sorted list.
-- The elements of the argument list and the returned one should be the same.

-- 2.8 Intrinsic approach.
--data Sorted : Set where
--  nil : Sorted
--  cons : (h : ℕ) (q : Sorted) → insertion correct de h dans q...

mutual
  data Sorted : Set where
    nil : Sorted
    cons : (h : ℕ) (q : Sorted) → (e : h ≤ head h q) → Sorted 

  head : ℕ → Sorted → ℕ
  head d nil = d
  head d (cons h q e) = h

mutual
  insert' : (x : ℕ) → Sorted → Sorted
  insert' x nil = cons x nil (≤-refl x)
  insert' x (cons h q e) with x ≤? h
  insert' x (cons h q e) | left e' = cons x (cons h q e) e'
  insert' x (cons h q e) | right e' = cons h (insert' x q) (lemma-insert x h q e' e)
  
  lemma-insert : (m n : ℕ) (l : Sorted) → n ≤ m →  n ≤ head n l → n ≤ head n (insert' m l)
  lemma-insert m n nil e1 e2 = e1
  lemma-insert m n (cons h q e) e1 e2 with m ≤? h
  lemma-insert m n (cons h q e) e1 e2 | left e' = e1
  lemma-insert m n (cons h q e) e1 e2 | right e' = e2

sort' : (l : List ℕ) → Sorted
sort' [] = nil
sort' (h ∷ q) = insert' h (sort' q)

test-sort' = sort' (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

-- 3 Optional: Preservation of elements.
-- 3.1 Permutations.
data _∼_ {A : Set} : List A → List A → Set where
  ∼-nil : [] ∼ []
  ∼-drop : (x : A) {l l' : List A} → l ∼ l' → (x ∷ l) ∼ (x ∷ l')
  ∼-swap : (x y : A) (l : List A) → (x ∷ y ∷ l) ∼ (y ∷ x ∷ l)
  ∼-trans : {l l' l'' : List A} → l ∼ l' → l' ∼ l'' → l ∼ l''

-- 3.2 Properties.
∼-refl : {A : Set} {l : List A} → l ∼ l
∼-refl {A} {[]} = ∼-nil
∼-refl {A} {h ∷ _} = ∼-drop h ∼-refl

∼-sym : {A : Set} {l l' : List A} → l ∼ l' → l' ∼ l
∼-sym {A} {[]} {[]} ∼-nil = ∼-nil
∼-sym {A} {(h ∷ _)} {(h ∷ _)} (∼-drop h e) = ∼-drop h (∼-sym e)
∼-sym {A} {(x ∷ y ∷ q)} {(y ∷ x ∷ q)} (∼-swap x y q) = ∼-swap y x q
∼-sym {A} {l} {l'} (∼-trans e1 e2) = ∼-trans (∼-sym e2) (∼-sym e1)

-- 3.3 Insertion and permutation.
insert-∼ : (x : ℕ) (l : List ℕ) → (x ∷ l) ∼ (insert x l)
insert-∼ x [] = ∼-drop x ∼-nil
insert-∼ x (h ∷ q) with x ≤? h
insert-∼ x (h ∷ q) | left e = ∼-trans (∼-swap x h q) (∼-swap h x q)
insert-∼ x (h ∷ q) | right e = ∼-trans (∼-swap x h q) (∼-drop h (insert-∼ x q))

∼-insert : (x : ℕ) {l l' : List ℕ} → l ∼ l' → insert x l ∼ insert x l'
∼-insert h ∼-nil = ∼-drop h ∼-nil
∼-insert h (∼-drop x e) with h ≤? x
∼-insert h (∼-drop x e) | left e' = ∼-drop h (∼-drop x e)
∼-insert h (∼-drop x e) | right e' = ∼-drop x (∼-insert h e)
∼-insert h (∼-swap x y l) = ∼-trans (∼-trans (∼-sym (insert-∼ h (x ∷ y ∷ l))) (∼-drop h (∼-swap x y l))) (insert-∼ h (y ∷ x ∷ l))
∼-insert h (∼-trans e1 e2) = ∼-trans (∼-insert h e1) (∼-insert h e2)

-- 3.4 Sorting and permutation.
sort-∼ : (l : List ℕ) → l ∼ (sort l)
sort-∼ [] = ∼-nil
sort-∼ (h ∷ q) = ∼-trans (insert-∼ h q) (∼-insert h (sort-∼ q))

-- 4 Merge sort.
-- 4.1 Splitting.
split : {A : Set} → List A → List A × List A
split [] = [] , []
split (x ∷ []) = x ∷ [] , []
split (h1 ∷ (h2 ∷ q)) with split q
split (h1 ∷ (h2 ∷ q)) | l1 , l2 = h1 ∷ l1 , h2 ∷ l2

test-split = split (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

-- 4.2 Merging.
merge : (l m : List ℕ) → List ℕ
merge [] m = m
merge l [] = l
merge (lh ∷ lq) (mh ∷ mq) with lh ≤? mh
merge (lh ∷ lq) (mh ∷ mq) | left e = lh ∷ (merge lq (mh ∷ mq))
merge (lh ∷ lq) (mh ∷ mq) | right e = mh ∷ (merge (lh ∷ lq) mq)

-- 4.3 Sorting.
{-# TERMINATING #-}
mergesort : List ℕ → List ℕ
mergesort [] = []
mergesort (x ∷ []) = x ∷ []
mergesort l with split l
mergesort l | l1 , l2 = merge (mergesort l1) (mergesort l2)

test-mergesort : List ℕ
test-mergesort = mergesort (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

-- 4.4 Splitting is decreasing.
_<_ : (m n : ℕ) → Set
m < n = (suc m) ≤ n

length : {A : Set} (l : List A) → ℕ
length [] = zero
length (x ∷ l) = suc (length l)

<-splitl : (l : List ℕ) → 2 ≤ length l → length (fst (split l)) < length l
<-splitl [] ()
<-splitl (x ∷ []) (s≤s ())
<-splitl (h1 ∷ h2 ∷ []) e = s≤s (s≤s z≤n)
<-splitl (h1 ∷ h2 ∷ x ∷ []) e = s≤s (s≤s (s≤s z≤n))
<-splitl (h1 ∷ h2 ∷ h3 ∷ h4 ∷ q) e = s≤s (s≤s (≤-trans (≤s (length (fst (split (h3 ∷ h4 ∷ q))))) (<-splitl (h3 ∷ h4 ∷ q) (s≤s (s≤s z≤n)))))

<-splitr : (l : List ℕ) → 1 ≤ length l → length (snd (split l)) < length l
<-splitr [] ()
<-splitr (x ∷ []) (s≤s z≤n) = s≤s z≤n
<-splitr (h1 ∷ h2 ∷ []) e = s≤s (s≤s z≤n)
<-splitr (h1 ∷ h2 ∷ x ∷ []) e = s≤s (s≤s (z≤n))
<-splitr (h1 ∷ h2 ∷ h3 ∷ h4 ∷ q) e = s≤s (s≤s (≤-trans (≤s (length (snd (split (h3 ∷ h4 ∷ q))))) (<-splitr (h3 ∷ h4 ∷ q) (s≤s (z≤n)))))

-- 4.5 The fuel definition of merge.
mergesort-fuel : (n : ℕ) → (l : List ℕ) → (length l ≤ n) → List ℕ
mergesort-fuel zero l e = l
mergesort-fuel (suc zero) l e = l
mergesort-fuel (suc n) l e with 2 ≤? length l
mergesort-fuel (suc n) l e | left e' = merge (mergesort-fuel n (fst (split l)) (≤-pred (≤-trans (<-splitl l e') e))) (mergesort-fuel n (snd (split l)) (≤-pred (≤-trans (<-splitr l (≤-trans (s≤s z≤n) e')) e)))
mergesort-fuel (suc n) l e | right e' = l

mergesort' : (l : List ℕ) → List ℕ
mergesort' l = mergesort-fuel (length l) l (≤-refl (length l))

test-mergesort' : List ℕ
test-mergesort' = mergesort' (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

-- 4.6 Merge sort is sorting.
mutual
  merge' : (l m : Sorted) → Sorted
  merge' nil m = m
  merge' l nil = l
  merge' (cons lh lq le) (cons mh mq me) with lh ≤? mh
  merge' (cons lh lq le) (cons mh mq me) | left e = cons lh (merge' lq (cons mh mq me)) (lemma-merge lh mh lq mq le me e)
  merge' (cons lh lq le) (cons mh mq me) | right e = cons mh (merge' mq (cons lh lq le)) (lemma-merge mh lh mq lq me le e)

  lemma-head : (n m : ℕ) (l : Sorted) (e : m ≤ n) → (head m l) ≤ (head n l)
  lemma-head n m nil e = e
  lemma-head n m (cons h q e') e = ≤-refl h

  lemma-merge : (lh mh : ℕ) (lq mq : Sorted) (le : lh ≤ head lh lq) (me : mh ≤ head mh mq) → lh ≤ mh → lh ≤ head lh (merge' lq (cons mh mq me))
  lemma-merge lh mh nil mq le me e = ≤-trans e (≤-refl mh)
  lemma-merge lh mh (cons lh' lq le') mq le me e with lh' ≤? mh
  lemma-merge lh mh (cons lh' lq le') mq le me e | left e' = le
  lemma-merge lh mh (cons lh' lq le') mq le me e | right e' = e

mergesort-fuel' : (n : ℕ) → (l : List ℕ) → (length l ≤ n) → (2 ≤ length l) ∨ (length l ≤ 2) → Sorted
-- false cases
mergesort-fuel' 0 [] e (left ())
mergesort-fuel' 0 (h ∷ q) () (left e')
-- real cases
mergesort-fuel' 0 [] e (right e') = nil
mergesort-fuel' (suc n) l e (left e') = merge' (mergesort-fuel' n (fst (split l)) (≤-pred (≤-trans (<-splitl l e') e)) (2 ≤? length (fst (split l)))) (mergesort-fuel' n (snd (split l)) (≤-pred (≤-trans (<-splitr l (≤-trans (s≤s z≤n) e')) e)) (2 ≤? length (snd (split l))))
mergesort-fuel' (suc n) [] e (right e') = nil
mergesort-fuel' (suc n) (h ∷ []) e (right e') = cons h nil (≤-refl h)
mergesort-fuel' (suc n) (h1 ∷ h2 ∷ []) e (right e') = merge' (cons h1 nil (≤-refl h1)) (cons h2 nil (≤-refl h2))
-- false case
mergesort-fuel' (suc n) (h1 ∷ h2 ∷ h3 ∷ q) e (right (s≤s (s≤s ())))

mergesort-sorting : (l : List ℕ) → Sorted
mergesort-sorting l = mergesort-fuel' (length l) l (≤-refl (length l)) (2 ≤? length l)

test-mergesort-sorting : Sorted
test-mergesort-sorting = mergesort-sorting (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

-- 5 Well-founded definition of merge sort.
-- 5.1 Basic definitions.
Rel : (A : Set) → Set₁
Rel A = A → A → Set

data Acc {A : Set} (_<_ : Rel A) (x : A) : Set where
  acc : ((y : A) → y < x → Acc _<_ y) → Acc _<_ x

WellFounded : {A : Set} → (_<_ : Rel A) → Set
WellFounded {A} _<_ = (x : A) → Acc _<_ x

-- The < relation is well founded on ℕ.
-- postulate wfNat : WellFounded _<_

-- 5.2 Definition of merge sort.
aux-mergesort : (l : List ℕ) → Acc _<_ (length l) → List ℕ
aux-mergesort [] e = []
aux-mergesort (x ∷ []) e = (x ∷ [])
aux-mergesort l e with 2 ≤? length l
aux-mergesort l (acc p) | left e' = merge (aux-mergesort (fst (split l)) (p (length (fst (split l))) (<-splitl l e'))) (aux-mergesort (snd (split l)) (p (length (snd (split l))) (<-splitr l (≤-trans (s≤s z≤n) e'))))
aux-mergesort l (acc p) | right e' = l

-- mergesort-wellfounded is defined after wfNat

-- 5.3 Auxiliary lemmas.
≤-< : {m n : ℕ} → (m ≤ n) → m ≡ n ∨ m < n
≤-< {n = zero} (z≤n {zero}) = left refl
≤-< {n = suc n} (z≤n {suc n}) = right (s≤s z≤n)
≤-< (s≤s e) with ≤-< e
≤-< (s≤s e) | left e' = left (cong suc e')
≤-< (s≤s e) | right e' = right (s≤s e')

<-last : {m n : ℕ} → (m < suc n) → m ≡ n ∨ m < n
<-last (s≤s e) = ≤-< e

-- 5.4 ℕ is well-founded.
wfNat : WellFounded _<_
wfNat n = acc (aux n)
  where
  aux : (x y : ℕ) → y < x → Acc _<_ y
  aux (suc a) b e with <-last e
  aux (suc a) .a e | left refl = wfNat a
  aux (suc a) b e | right e' = aux a b (≤-pred (s≤s e'))

mergesort-wellfounded : (l : List ℕ) → List ℕ
mergesort-wellfounded l = aux-mergesort l (wfNat (length l))
