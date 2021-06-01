{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Unit.Polymorphic where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary using (yes)
open import Cubical.Relation.Binary.Raw using (Decidable)

import Cubical.Data.Unit.Base as ⊤

⊤ : {ℓ : Level} → Type ℓ
⊤ = Lift ⊤.⊤

pattern tt = lift ⊤.tt

infix 4 _≟_

_≟_ : {ℓ : Level} → Decidable {A = ⊤ {ℓ}} _≡_
_ ≟ _ = yes refl

isContr⊤ : {ℓ : Level} → isContr (⊤ {ℓ})
isContr⊤ = tt , λ {tt → refl}

isProp⊤ : {ℓ : Level} → isProp (⊤ {ℓ})
isProp⊤ _ _ i = tt
