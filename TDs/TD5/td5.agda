open import Data.Product

-- 2 Our first proof.
×-comm : {A B : Set} → (A × B) → (B × A)
×-comm (a , b) = (b , a)

-- 3 Implication.
id : {A : Set} → A → A
id a = a

-- 3.1 First projection.
K : {A B : Set} → A → B → A
K a = λ _ → a

-- 3.2 Application.
app : {A B : Set} → (A → B) → A → B
app f =  λ a → f a

-- 3.3 Flip.
flip : {A B C : Set} → (A → B → C) → B → A → C
flip f = λ b → λ a → f a b

-- 3.4 Transitivity / composition.
comp : {A B C : Set} → (A → B) → (B → C) → (A → C)
comp f = λ g → λ a → g (f a)

-- 3.5 S.
S : {A B C : Set} → (A → B → C) → (A → B) → A → C
S f = λ g → λ z → f z (g z)

-- 4 Conjunction.
open import Data.Product renaming (_×_ to _∧_)

-- 4.1 Projections.
proj1 : {A B : Set} → (A ∧ B) → A
proj1 (a , b) = a

proj2 : {A B : Set} → (A ∧ B) → B
proj2 (a , b) = b

-- 4.2 Diagonal.
diag : {A : Set} → A → (A ∧ A)
diag a = (a , a)

-- 4.3 Commutativity.
and-comm : {A B : Set} → (A ∧ B) → (B ∧ A)
and-comm (a , b) = (b , a)

-- 4.4 Currying.
curry1 : {A B C : Set} → (A ∧ B → C) → (A → B → C)
curry1 f = λ a → λ b → f (a , b)

curry2 : {A B C : Set} → (A → B → C) → (A ∧ B → C)
curry2 f = λ z → f (proj1 z) (proj2 z)

equiv : (A B : Set) → Set
equiv A B = (A → B) ∧ (B → A)

_↔_ : (A B : Set) → Set
A ↔ B = (A → B) ∧ (B → A)

currying : {A B C : Set} → (A ∧ B → C) ↔ (A → B → C)
currying = ((λ f a b → f (a , b)) , (λ f z → f (proj1 z) (proj2 z)))

-- 4.5 Optional: distributivity.
opt-dist : {A B C : Set} → (A → (B ∧ C)) ↔ ((A → B) ∧ (A → C))
opt-dist = ( (λ f → ( (λ z → proj1 (f z)) , λ z → proj2 (f z) )) , λ z → λ a → (proj1 z a , proj2 z a) )

-- 5 Disjunction.
data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

-- 5.1 Elimination rule.
or-elim : {A B C : Set} → (A ∨ B) → (A → C) → (B → C) → C
or-elim (left a) = λ z _ → z a
or-elim (right b) = λ _ z → z b

-- 5.2 Commutativity.
or-comm : {A B : Set} → (A ∨ B) → (B ∨ A)
or-comm (left a) = right a
or-comm (right b) = left b

-- 5.3 Distributivity.
dist : {A B C : Set} → (A ∧ (B ∨ C)) → (A ∧ B) ∨ (A ∧ C)
dist (a , left b) = left (a , b)
dist (a , right c) = right (a , c)

-- 6 Negation.
-- 6.1 Falsity.
data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

-- 6.2 Negation.
¬ : Set → Set
¬ A = A → ⊥

-- 6.3 Contradiction.
contr : {A B : Set} → (A → B) → (¬ B → ¬ A)
contr f = λ g → λ a → g (f a)

-- 6.4 Non-contradiction.
non-contr : {A : Set} → ¬ (A ∧ ¬ A)
non-contr (a , f) = f a

-- 6.5 Double negation introduction.
nni : {A : Set} → A → ¬ (¬ A)
nni a = λ f → f a

-- 6.6 Double negation elimination on ⊥.
⊥-nne : ¬ (¬ ⊥) → ⊥
⊥-nne f = f (λ b → b)

-- 6.7 Elimination of negation.
¬-elim : {A B : Set} → ¬ A → A → B
¬-elim f = λ a → ⊥-elim (f a)

-- 6.8 Non-falsifiability of the law of excluded middle.
nnlem : {A : Set} → ¬ (¬ (A ∨ (¬ A)))
nnlem f = f (right (λ a → f (left a)))

-- 6.9 Russell’s paradox.
rp : {A : Set} → (A → ¬ A) → (¬ A → A) → ⊥
rp f = λ g → f (g (λ a → f a a)) (g (λ a → f a a))

-- 7 Truth.
-- 7.1 Definition.
data ⊤ : Set where
    true : ⊤

-- 7.2 ⊤-strengthening.
ti : {A : Set} → (⊤ → A) → A
ti f = f true

-- 7.3 De Morgan.
dmnt : ¬ ⊤ → ⊥
dmnt = ti

dmtn : ⊥ → ¬ ⊤
dmtn = ⊥-elim

-- 8 Classical logic.
-- 8.1 Equivalence between excluded middle and double negation elimination.
lem : Set₁
lem = (A : Set) → A ∨ (¬ A)

nne : Set₁
nne = (A : Set) → ¬ (¬ A) → A

nne-lem : nne → lem
nne-lem f = λ A → f (A ∨ (A → ⊥)) (λ g → nnlem g)

lem-nne' : {A : Set} → (A ∨ ¬ A) → ¬ (¬ A) → A
lem-nne' (left a) = λ _ → a
lem-nne' (right f) = (λ g → ⊥-elim (g f))

lem-nne : lem → nne
lem-nne f =  λ A → lem-nne' (f A)

-- 8.2 Pierce law.
pierce : Set₁
pierce = {A B : Set} → ((A → B) → A) → A

pierce-lem : pierce → lem
pierce-lem f = λ A → f (λ b → right (λ a → b (left a)))

lem-pierce' : {A B : Set} → (A ∨ ¬ A) → ((A → B) → A) → A
lem-pierce' (left a) = λ _ → a
lem-pierce' (right f) = λ g → g (λ a → ⊥-elim (f a))

lem-pierce : lem → pierce
lem-pierce f {A} = lem-pierce' (f A)
-- As lem is equivalent to nne and to pierce, nne is equivalent to pierce to.
