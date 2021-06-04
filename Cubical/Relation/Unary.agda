{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Unary where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Structures.Carrier
import Cubical.Foundations.Logic as L

open import Cubical.Data.Sigma
open import Cubical.Data.Sum.Base using (_⊎_; rec)
open import Cubical.Foundations.Function

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.Decidable using (IsYes)

private
  variable
    a b c ℓ ℓ₁ ℓ₂ : Level
    A : Type a
    B : Type b
    C : Type c

------------------------------------------------------------------------
-- Definition

-- Unary relations are known as predicates and `Pred A ℓ` can be viewed
-- as some property that elements of type A might satisfy.

-- Consequently `P : Pred A ℓ` can also be seen as a subset of A
-- containing all the elements of A that satisfy property P. This view
-- informs much of the notation used below.

RawPred : Type a → (ℓ : Level) → Type _
RawPred A ℓ = A → Type ℓ

Pred : Type a → (ℓ : Level) → Type _
Pred A ℓ = A → hProp ℓ


isPropValued : RawPred A ℓ → Type _
isPropValued P = ∀ x → isProp (P x)

[_] : Pred A ℓ → RawPred A ℓ
[ R ] x = R x .fst

isProp[_] : (P : Pred A ℓ) → isPropValued [ P ]
isProp[ P ] x = P x .snd

fromRaw : (P : RawPred A ℓ) → isPropValued P → Pred A ℓ
fromRaw P isPropP x .fst = P x
fromRaw P isPropP x .snd = isPropP x


------------------------------------------------------------------------
-- Special sets

-- The empty set.

∅ : Pred A _
∅ _ = L.⊥

-- The singleton set.

｛_｝ : A → Pred A _
｛ x ｝ = L._≡ₚ x

-- The universal set.

U : Pred A _
U _ = L.⊤

------------------------------------------------------------------------
-- Membership

infix 6 _∈_ _∉_

_∈_ : A → Pred A ℓ → Type _
x ∈ P = ⟨ P x ⟩

_∉_ : A → Pred A ℓ → Type _
x ∉ P = ¬ x ∈ P

------------------------------------------------------------------------
-- Subset relations

infix 6 _⊆_ _⊇_ _⊈_ _⊉_ _⊂_ _⊃_ _⊄_ _⊅_

_⊆_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

_⊇_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
P ⊇ Q = Q ⊆ P

_⊈_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
P ⊈ Q = ¬ (P ⊆ Q)

_⊉_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
P ⊉ Q = ¬ (P ⊇ Q)

_⊂_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
P ⊂ Q = P ⊆ Q × Q ⊈ P

_⊃_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
P ⊃ Q = Q ⊂ P

_⊄_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
P ⊄ Q = ¬ (P ⊂ Q)

_⊅_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
P ⊅ Q = ¬ (P ⊃ Q)

------------------------------------------------------------------------
-- Properties of sets

infix 10 Satisfiable Universal IUniversal

-- Emptiness - no element satisfies P.

Empty : Pred A ℓ → Type _
Empty P = ∀ x → x ∉ P

-- Satisfiable - at least one element satisfies P.

Satisfiable : Pred A ℓ → Type _
Satisfiable {A = A} P = ∃[ x ∈ A ] x ∈ P

syntax Satisfiable P = ∃⟨ P ⟩

-- Universality - all elements satisfy P.

Universal : Pred A ℓ → Type _
Universal P = ∀ x → x ∈ P

syntax Universal P = Π[ P ]

-- Implicit universality - all elements satisfy P.

IUniversal : Pred A ℓ → Type _
IUniversal P = ∀ {x} → x ∈ P

syntax IUniversal P = ∀[ P ]

-- Decidability - it is possible to determine if an arbitrary element
-- satisfies P.

Decidable : Pred A ℓ → Type _
Decidable P = ∀ x → Dec (x ∈ P)

------------------------------------------------------------------------
-- Operations on sets

infix 10 ⋃ ⋂
infixr 9 _⊢_
infixr 8 _⇒_
infixr 7 _∩_
infixr 6 _∪_
infix 5 _≬_

-- Complement.

∁ : Pred A ℓ → Pred A ℓ
∁ P = λ x → L.¬ P x

-- Implication.

_⇒_ : Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
P ⇒ Q = λ x → P x L.⇒ Q x

-- Union.

_∪_ : Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
P ∪ Q = λ x → P x L.⊔ Q x

-- Intersection.

_∩_ : Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
P ∩ Q = λ x → P x L.⊓ Q x

-- Infinitary union.

⋃ : ∀ {i} (I : Type i) → (I → Pred A ℓ) → Pred A _
⋃ I P = λ x → L.∃[ i ∶ I ] P i x

syntax ⋃ I (λ i → P) = ⋃[ i ∶ I ] P

-- Infinitary intersection.
⋂ : ∀ {i} (I : Type i) → (I → Pred A ℓ) → Pred A _
⋂ I P = λ x → ((i : I) → x ∈ P i) , isPropΠ λ i → isProp[ P i ] x

syntax ⋂ I (λ i → P) = ⋂[ i ∶ I ] P

-- Positive version of non-disjointness, dual to inclusion.

_≬_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
_≬_ {A = A} P Q = ∃[ x ∈ A ] x ∈ P × x ∈ Q

-- Preimage.

_⊢_ : (A → B) → Pred B ℓ → Pred A ℓ
f ⊢ P = λ x → P (f x)

-- Image.

_⊣_ : (A → B) → Pred A ℓ → Pred B _
f ⊣ P = λ x → L.∥ Σ[ y ∈ _ ] y ∈ P × (f y ≡ x) ∥ₚ


------------------------------------------------------------------------
-- Preservation under operations

_Preserves_⟶_ : (A → B) → Pred A ℓ₁ → Pred B ℓ₂ → Type _
f Preserves P ⟶ Q = P ⊆ f ⊢ Q

_Preserves_ : (A → A) → Pred A ℓ → Type _
f Preserves P = f Preserves P ⟶ P

-- A binary variant of _Preserves_⟶_.

_Preserves₂_⟶_⟶_ : (A → B → C) → Pred A ℓ₁ → Pred B ℓ₂ → Pred C ℓ → Type _
_∙_ Preserves₂ P ⟶ Q ⟶ R = ∀ {x y} → x ∈ P → y ∈ Q → x ∙ y ∈ R

_Preserves₂_ : (A → A → A) → Pred A ℓ → Type _
_∙_ Preserves₂ P = _∙_ Preserves₂ P ⟶ P ⟶ P

------------------------------------------------------------------------
-- Logical equivalence

infix 8 _⇔_ _⇚⇛_

_⇔_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
P ⇔ Q = P ⊆ Q × P ⊇ Q

-- Direct logical equivalence (more useful for proofs)

_⇚⇛_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
P ⇚⇛ Q = ∀ x → x ∈ P ≃ x ∈ Q


module _ (P : Pred A ℓ₁) (Q : Pred A ℓ₂) where

  ⇔-⇚⇛ : P ⇔ Q → P ⇚⇛ Q
  ⇔-⇚⇛ (P⊆Q , Q⊆P) x = isPropEquiv→Equiv (P x .snd) (Q x .snd) P⊆Q Q⊆P

  ⇚⇛-⇔ : P ⇚⇛ Q → P ⇔ Q
  ⇚⇛-⇔ P⇚⇛Q = equivFun (P⇚⇛Q _) , invEq (P⇚⇛Q _)

  equiv≃ : P ⇔ Q ≃ P ⇚⇛ Q
  equiv≃ = isPropEquiv→Equiv (isProp× (isPropImplicitΠ λ _ → isPropΠ λ _ → (Q _ .snd)) (isPropImplicitΠ λ _ → isPropΠ λ _ → (P _ .snd)))
                              (isPropΠ λ _ → isPropΣ (isPropΠ λ _ → Q _ .snd) (λ _ → isPropIsEquiv _)) ⇔-⇚⇛ ⇚⇛-⇔

equiv≡ : _⇔_ ≡ _⇚⇛_ {ℓ₁} {A} {ℓ₂} {ℓ}
equiv≡ = funExt (λ P → funExt (λ Q → ua (equiv≃ P Q)))

------------------------------------------------------------------------
-- Predicate combinators

-- These differ from the set operations above, as the carrier set of the
-- resulting predicates are not the same as the carrier set of the
-- component predicates.

infixr  2 _⟨×⟩_
infixr  2 _⟨⊙⟩_
infixr  1 _⟨⊎⟩_
infixr  0 _⟨→⟩_
infixl  9 _⟨·⟩_
infix  10 _~
infixr  9 _⟨∘⟩_
infixr  2 _//_ _\\_

-- Product.

_⟨×⟩_ : Pred A ℓ₁ → Pred B ℓ₂ → Pred (A × B) _
(P ⟨×⟩ Q) (x , y) = P x L.⊓ Q y

-- Sum over one element.

_⟨⊎⟩_ : Pred A ℓ → Pred B ℓ → Pred (A ⊎ B) _
P ⟨⊎⟩ Q = rec P Q

-- Sum over two elements.

_⟨⊙⟩_ : Pred A ℓ₁ → Pred B ℓ₂ → Pred (A × B) _
(P ⟨⊙⟩ Q) (x , y) = P x L.⊔ Q y

-- Implication.

_⟨→⟩_ : Pred A ℓ₁ → Pred B ℓ₂ → Pred (A → B) _
(P ⟨→⟩ Q) f = L.∀[ x ∶ _ ] P x L.⇒ Q (f x)

-- Product.

_⟨·⟩_ : (P : Pred A ℓ₁) (Q : Pred B ℓ₂) →
        (P ⟨×⟩ (P ⟨→⟩ Q)) ⊆ Q ∘ uncurry (flip _$_)
(P ⟨·⟩ Q) (p , f) = f _ p

-- Converse.

_~ : Pred (A × B) ℓ → Pred (B × A) ℓ
P ~ = P ∘ λ { (x , y) → y , x }

-- Composition.

_⟨∘⟩_ : Pred (A × B) ℓ₁ → Pred (B × C) ℓ₂ → Pred (A × C) _
_⟨∘⟩_ {B = B} P Q (x , z) = L.∃[ y ∶ B ] P (x , y) L.⊓ Q (y , z)

-- Post-division.

_//_ : Pred (A × C) ℓ₁ → Pred (B × C) ℓ₂ → Pred (A × B) _
(P // Q) (x , y) = L.∀[ z ∶ _ ] Q (y , z) L.⇒ P (x , z)

-- Pre-division.

_\\_ : Pred (A × C) ℓ₁ → Pred (A × B) ℓ₂ → Pred (B × C) _
P \\ Q = (P ~ // Q ~) ~
