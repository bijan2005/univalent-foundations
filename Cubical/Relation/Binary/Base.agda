{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Binary.Base where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_on_)
open import Cubical.Foundations.HLevels

private
  variable
    a b ℓ : Level
    A : Type a
    B : Type b

RawREL : Type a → Type b → (ℓ : Level) → Type _
RawREL A B ℓ = A → B → Type ℓ

RawRel : Type a → (ℓ : Level) → Type _
RawRel A ℓ = RawREL A A ℓ


REL : Type a → Type b → (ℓ : Level) → Type _
REL A B ℓ = A → B → hProp ℓ

Rel : Type a → (ℓ : Level) → Type _
Rel A ℓ = REL A A ℓ


isPropValued : RawREL A B ℓ → Type _
isPropValued R = ∀ a b → isProp (R a b)


[_] : REL A B ℓ → RawREL A B ℓ
[ R ] a b = R a b .fst

isProp[_] : (R : REL A B ℓ) → isPropValued [ R ]
isProp[ R ] a b = R a b .snd

fromRaw : (R : RawREL A B ℓ) → isPropValued R → REL A B ℓ
fromRaw R isPropR a b .fst = R a b
fromRaw R isPropR a b .snd = isPropR a b
