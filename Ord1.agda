{-
This file is a part of the library  Binary-4.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.

Binary-4  is free software: you can redistribute it and/or modify it
under the terms of the GNU General Public License.
See  license.txt.
-}

module Ord1 where

open import Level    using () renaming (zero to 0ℓ)
open import Function using (case_of_)
open import Relation.Binary using
     (Tri; IsPreorder; IsPartialOrder; IsTotalOrder; IsDecTotalOrder;
      DecTotalOrder; IsStrictTotalOrder; StrictTotalOrder
     )
open import Relation.Binary.PropositionalEquality as PE using 
                                                        (_≡_; isEquivalence)
open import Data.Sum using (inj₁; inj₂)  

-- of application ---
open import Bin0 using (Bin)
open import Ord0 using (_<_; _≤_; _≤?_; <-cmp; <-trans; ≤-reflexive; ≤-trans; 
                                                               ≤-antisym; <⇒≤)




--****************************************************************************
<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
<-isStrictTotalOrder = 
                     record{ isEquivalence =  isEquivalence
                           ; trans         =  \{x y z} → <-trans {x} {y} {z}
                           ; compare       =  <-cmp }

<-strictTotalOrder : StrictTotalOrder _ _ _
<-strictTotalOrder = 
                   record{ Carrier            =  Bin
                         ; _≈_                =  _≡_
                         ; _<_                =  _<_
                         ; isStrictTotalOrder =  <-isStrictTotalOrder }

------------------------------------------------------------------------------
≤-isPreorder :  IsPreorder _≡_ _≤_
≤-isPreorder =  record{ isEquivalence =  isEquivalence
                      ; reflexive     =  ≤-reflexive
                      ; trans         =  \{x y z} → ≤-trans {x} {y} {z} }

≤-isPartialOrder :  IsPartialOrder _≡_ _≤_
≤-isPartialOrder =  record{ isPreorder = ≤-isPreorder;  antisym = ≤-antisym }

open Tri

≤-total :  Relation.Binary.Total _≤_
≤-total x y = 
            case <-cmp x y of \ { (tri< le _  _)  → inj₁ (<⇒≤ {x} {y} le)
                                ; (tri≈ _  eq _)  → inj₁ (≤-reflexive eq)
                                ; (tri> _  _  gt) → inj₂ (<⇒≤ {y} {x} gt) }

≤-isTotalOrder :  IsTotalOrder _≡_ _≤_
≤-isTotalOrder =  
               record{ isPartialOrder = ≤-isPartialOrder;  total = ≤-total }

≤-isDecTotalOrder : IsDecTotalOrder _≡_ _≤_
≤-isDecTotalOrder =
       record{ isTotalOrder = ≤-isTotalOrder;  _≟_ = Bin0._≟_;  _≤?_ = _≤?_ }

≤-decTotalOrder : DecTotalOrder 0ℓ 0ℓ 0ℓ
≤-decTotalOrder =
                record{ Carrier         = Bin
                      ; _≈_             = _≡_ {A = Bin}
                      ; _≤_             = _≤_
                      ; isDecTotalOrder = ≤-isDecTotalOrder }
