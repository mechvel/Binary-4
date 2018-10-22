{-
This file is a part of the library  Binary-4.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.

Binary-4  is free software: you can redistribute it and/or modify it
under the terms of the GNU General Public License.
See  license.txt.
-}

module BPrelude where

open import Level           using (Level; _⊔_)
open import Function        using (_∘_)
open import Relation.Binary using (Symmetric)
open import Relation.Binary.PropositionalEquality as PE using (_≡_; _≢_; sym)
open import Data.Product       using (_×_; ∃)
open import Data.List          using (List ; []; _∷_)
open import Data.String as Str using (String) renaming (_++_ to _+s+_)



--****************************************************************************
infix 3 _←→_

_←→_ :  ∀ {α β} (A : Set α) → (B : Set β) → Set (α ⊔ β)   -- "if and only if"
_←→_ A B =  (A → B) × (B → A)

≢sym :  ∀ {α} {A : Set α} → Symmetric (_≢_ {A = A})
≢sym x≢y =  x≢y ∘ sym

concatStr : List String → String
concatStr []           = ""
concatStr (str ∷ strs) = str +s+ (concatStr strs)

head :  ∀ {α} {A : Set α} → A → List A → A
head x []      =  x
head _ (y ∷ _) =  y

last :  ∀ {α} {A : Set α} → A → List A → A
last x []       =  x
last _ (x ∷ xs) =  last x xs



--============================================================================
module _ {α β : Level} {A : Set α} {B : Set β}
  where
  Injective : (A → B) → Set _
  Injective f =  {x y : A} → f x ≡ f y → x ≡ y

  Surjective : (A → B) → Set _
  Surjective f =  (y : B) → ∃ (\(x : A) → f x ≡ y)
                                 -- This is a constructive surjection,
                                 -- so that a coimage for  y  is returned.

  Bijective : (A → B) → Set _
  Bijective f =  Injective f × Surjective f



