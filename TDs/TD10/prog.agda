open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Sigma

-- 1 Definition of the programming language.
-- 1.1 A type for programs.
data Bool : Set where
  true : Bool
  false : Bool

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)

data Prog : Set where
  B   : Bool → Prog
  Nat : ℕ → Prog
  _+'_ : Prog → Prog → Prog
  _<'_ : Prog → Prog → Prog
  if_then_else_ : Prog → Prog → Prog → Prog
  _∧_ : Prog → Prog → Prog

-- 1.2 Deciding inequality of natural numbers.
_<?_ : ∀ (m n : ℕ) → Bool
m <? zero = false
zero <? suc n = true
suc m <? suc n = m <? n

-- 1.3 Reduction.
data _⇒_ : Prog → Prog → Set where
  red-add : {n1 n2 : ℕ} → ((Nat n1) +' (Nat n2)) ⇒ Nat (n1 + n2)
  red-addl : {p1 p2 p1' : Prog} → p1 ⇒ p1' → (p1 +' p2) ⇒ (p1' +' p2)
  red-addr : {p1 p2 p2' : Prog} → p2 ⇒ p2' → (p1 +' p2) ⇒ (p1 +' p2')
  red-< : {n1 n2 : ℕ} → (Nat n1 <' Nat n2) ⇒ B (n1 <? n2)
  red-<l : {p1 p2 p1' : Prog} → p1 ⇒ p1' → (p1 <' p2) ⇒ (p1' <' p2)
  red-<r : {p1 p2 p2' : Prog} → p2 ⇒ p2' → (p1 <' p2) ⇒ (p1 <' p2')
  red-iftrue : {p1 p2 : Prog} → (if B true then p1 else p2) ⇒ p1
  red-iffalse : {p1 p2 : Prog} → (if B false then p1 else p2) ⇒ p2
  red-if : {p1 p2 p p' : Prog} → p ⇒ p' → (if p then p1 else p2) ⇒ (if p' then p1 else p2)
  red-∧l : {p1 p2 p1' : Prog} → p1 ⇒ p1' → (p1 ∧ p2) ⇒ (p1' ∧ p2)
  red-∧r : {p1 p2 p2' : Prog} → p2 ⇒ p2' → (p1 ∧ p2) ⇒ (p1 ∧ p2')

-- 1.4 Types.
data Type : Set₁ where
  Boolean : Type
  Natural : Type
  _×_ : Type → Type → Type

-- 1.5 Typing.
data ⊢_∷_ : Prog → Type → Set where
  true-type : ⊢ B true ∷ Boolean
  false-type : ⊢ B false ∷ Boolean
  N-type : {n : ℕ} → ⊢ Nat n ∷ Natural
  +'-type : {p p' : Prog} → ⊢ p ∷ Natural → ⊢ p' ∷ Natural → ⊢ p +' p' ∷ Natural
  <'-type : {p p' : Prog} → ⊢ p ∷ Natural → ⊢ p' ∷ Natural → ⊢ p <' p' ∷ Boolean
  if-type : {A : Type} {p p1 p2 : Prog}
            → ⊢ p ∷ Boolean
            → ⊢ p1 ∷ A
            → ⊢ p2 ∷ A
            → ⊢ (if p then p1 else p2) ∷ A
  ∧-type : {A B : Type} {p1 p2 : Prog}
            → ⊢ p1 ∷ A
            → ⊢ p2 ∷ B
            → ⊢ (p1 ∧ p2) ∷ (A × B)

-- 2 Properties.
-- 2.1 Subject reduction.
subj-red : {A : Type} (p p' : Prog) →  ⊢ p ∷ A → p ⇒ p' →  ⊢ p' ∷ A

subj-red {Natural} ((Nat n1) +' (Nat n2)) .(Nat (n1 + n2)) type red-add = N-type {n1 + n2}
subj-red {Natural} (p1 +' p2) (p1' +' p2) (+'-type type1 type2) (red-addl red) = +'-type (subj-red p1 p1' type1 red) type2
subj-red {Natural} (p1 +' p2) (p1 +' p2') (+'-type type1 type2) (red-addr red) = +'-type type1 (subj-red p2 p2' type2 red)

subj-red {Boolean} ((Nat n1) <' (Nat n2)) (B true) type red = true-type
subj-red {Boolean} ((Nat n1) <' (Nat n2)) (B false) type red = false-type

subj-red {Boolean} (p1 <' p2) (p1' <' p2) (<'-type type1 type2) (red-<l red) = <'-type (subj-red p1 p1' type1 red) type2
subj-red {Boolean} (p1 <' p2) (p1 <' p2') (<'-type type1 type2) (red-<r red) = <'-type type1 (subj-red p2 p2' type2 red)

subj-red (if B true then p1 else p2) .p1 (if-type type type1 type2) red-iftrue = type1
subj-red (if B false then p1 else p2) .p2 (if-type type type1 type2) red-iffalse = type2

subj-red (if p then p1 else p2) (if p' then .p1 else .p2) (if-type type type1 type2) (red-if red) = if-type (subj-red p p' type red) type1 type2

subj-red {A1 × A2} (p1 ∧ p2) (p1' ∧ p2) (∧-type type1 type2) (red-∧l red) = ∧-type (subj-red p1 p1' type1 red) type2
subj-red {A1 × A2} (p1 ∧ p2) (p1 ∧ p2') (∧-type type1 type2) (red-∧r red) = ∧-type type1 (subj-red p2 p2' type2 red)

-- 2.2 Progress.
progress : {A : Type} (p : Prog) → {t : ⊢ p ∷ A} → (((Σ ℕ (λ n → (p ≡ Nat n))) ∨ (Σ Bool (λ b → (p ≡ B b)))) ∨ (Σ Prog (λ p' → (p ⇒ p'))))
progress (B b) = left (right (b , refl))
progress (Nat x) = left (left (x , refl))
progress {Natural} (p1 +' p2) {+'-type t1 t2} with progress {Natural} p1 {t1} , progress {Natural} p2 {t2}
progress {Natural} (p1 +' p2) {+'-type t1 t2} | left set1 , right (p2' , e) = right (p1 +' p2' , red-addr e)
progress {Natural} (p1 +' p2) {+'-type t1 t2} | right (p1' , e) , set2 = right (p1' +' p2 , red-addl e)
progress {Natural} (Nat n1 +' Nat n2) {+'-type N-type N-type} | left (left (.n1 , refl)) , left (left (.n2 , refl)) = right (Nat (n1 + n2) , red-add)
-- false proof
progress {Natural} (.(Nat _) +' Nat x) {+'-type N-type N-type} | left (right ()) , left (left (.x , refl))
progress {Natural} (.(_ +' _) +' Nat x) {+'-type (+'-type t1 t2) N-type} | left (right ()) , left (left (.x , refl))
progress {Natural} (.(if _ then _ else _) +' Nat x) {+'-type (if-type t1 t2 t3) N-type} | left (right ()) , left (left (.x , refl))
progress {Natural} (p1 +' .(Nat _)) {+'-type t1 N-type} | left fst₁ , left (right ())
progress {Natural} (p1 +' .(_ +' _)) {+'-type t1 (+'-type t2 t3)} | left fst₁ , left (right ())
progress {Natural} (p1 +' .(if _ then _ else _)) {+'-type t1 (if-type t2 t3 t4)} | left fst₁ , left (right ())

progress {Boolean} (p1 <' p2) {<'-type t1 t2} with progress {Natural} p1 {t1} , progress {Natural} p2 {t2}
progress {Boolean} (p1 <' p2) {<'-type t1 t2} | set1 , right (p2' , e) = right (p1 <' p2' , red-<r e)
progress {Boolean} (p1 <' p2) {<'-type t1 t2} | right (p1' , e) , set2 = right (p1' <' p2 , red-<l e)
progress {Boolean} ((Nat n1) <' (Nat n2)) {<'-type N-type N-type} | left (left (.n1 , refl)) , left (left (.n2 , refl)) = right (B (n1 <? n2) , red-<)
-- false proof
progress {Boolean} (.(Nat _) <' Nat x) {<'-type N-type N-type} | left (right ()) , left (left (.x , refl))
progress {Boolean} (.(_ +' _) <' Nat x) {<'-type (+'-type t1 t2) N-type} | left (right ()) , left (left (.x , refl))
progress {Boolean} (.(if _ then _ else _) <' Nat x) {<'-type (if-type t1 t2 t3) N-type} | left (right ()) , left (left (.x , refl))
progress {Boolean} (p1 <' .(Nat _)) {<'-type t1 N-type} | left fst₁ , left (right ())
progress {Boolean} (p1 <' .(_ +' _)) {<'-type t1 (+'-type t2 t3)} | left fst₁ , left (right ())
progress {Boolean} (p1 <' .(if _ then _ else _)) {<'-type t1 (if-type t2 t3 t4)} | left fst₁ , left (right ())

progress (if p then p1 else p2) {if-type t t1 t2} with progress {Boolean} p {t}
progress (if B true then p1 else p2) {if-type t t1 t2} | left (right (true , e)) = right (p1 , red-iftrue)
progress (if B false then p1 else p2) {if-type t t1 t2} | left (right (false , e)) = right (p2 , red-iffalse)
progress (if p then p1 else p2) {if-type t t1 t2} | right (p' , e) = right (if p' then p1 else p2 , red-if e)
-- false proof
progress (if .(B true) then p1 else p2) {if-type true-type t1 t2} | left (left (n , ()))
progress (if .(B false) then p1 else p2) {if-type false-type t1 t2} | left (left (n , ()))
progress (if .(_ <' _) then p1 else p2) {if-type (<'-type t t₁) t1 t2} | left (left (n , ()))
progress (if .(if _ then _ else _) then p1 else p2) {if-type (if-type t t₁ t₂) t1 t2} | left (left (n , ()))

progress (p1 ∧ p2) {∧-type t1 t2} with progress p1 {t1} , progress p2 {t2}
progress (p1 ∧ p2) {∧-type t1 t2} | left set1 , set2 = {!!}
progress (p1 ∧ p2) {∧-type t1 t2} | right y , set2 = {!!}

-- 3 Extensions.
-- 3.1 Products.
-- Il faut que je change l'ennoncé de la preuve précédente et donc que j'adapte tous les résultats.
-- Je me suis donc arrêté là, ce n'est pas grand chose mais ça à a été commencé.
