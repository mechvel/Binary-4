{-
This file is a part of the library  Binary-4.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.

Binary-4  is free software: you can redistribute it and/or modify it
under the terms of the GNU General Public License.
See  license.txt.
-}

module Bin0 where

open import Level            using () renaming (zero to 0ℓ)
open import Function         using (id; _∘_; case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Rel; Setoid; DecSetoid; IsDecEquivalence) 
                            renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality as PE 
                                     using (_≡_; _≢_; _≗_; refl; sym; trans;
                                            cong; cong₂; isEquivalence)
open PE.≡-Reasoning
open import Algebra using (Semigroup; Monoid; CommutativeMonoid)
open import Algebra.Structures using (IsSemigroup; IsMonoid;
                                                   IsCommutativeMonoid)
open import Algebra.FunctionProperties as FuncProp using (Op₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; ∃) 
open import Data.List    using (List; []; _∷_)
open import Data.Nat using (ℕ) 
            renaming (suc to 1+_; pred to pred'; _+_ to _+'_; 
                      _*_ to _*'_; _∸_ to _∸'_; _≤_ to _≤'_
                     )
     -- Renaming  foo -> foo'  is applied in order to distinguish the 
     -- corresponding operators from their Bin versions.
     -- 
open import Data.Nat.Properties as NatP using (module ≤-Reasoning)
     renaming (+-comm to +'-comm; +-assoc to +'-assoc; 
               *-distribˡ-+ to *'-lDistrib; *-cancelˡ-≡ to *'-lCancel
              )
open ≤-Reasoning using () renaming (begin_ to ≤begin_; _∎ to _≤end;
                                    _≡⟨_⟩_ to _≡≤[_]_; _≤⟨_⟩_ to _≤[_]_)

-- of application ---
open import BPrelude using (≢sym; Injective; Surjective)
open import Nat0     using (k+[m+n]≡m+[k+n])





--****************************************************************************
data Bin : Set where 
               0#    : Bin
               2suc  : Bin → Bin    -- \n→ 2*(1+n)  arbitrary nonzero even
               suc2* : Bin → Bin    -- \n→ 1 + 2n   arbitrary odd
--
-- This representation is unique for each natural number.


-- Decidable equality on Bin -------------------------------------------------

2suc-injective : Injective 2suc 
2suc-injective {0#}      {0#}      _  =  refl
2suc-injective {0#}      {2suc _}  ()
2suc-injective {0#}      {suc2* _} ()
2suc-injective {2suc _}  {0#}      () 
2suc-injective {2suc _}  {2suc _}  refl =  refl 
2suc-injective {2suc _}  {suc2* _} ()
2suc-injective {suc2* _} {0#}      ()
2suc-injective {suc2* _} {2suc _}  ()
2suc-injective {suc2* _} {suc2* _} refl =  refl

suc2*-injective : Injective suc2* 
suc2*-injective {0#}      {0#}      _  =  refl
suc2*-injective {0#}      {2suc _}  ()
suc2*-injective {0#}      {suc2* _} ()
suc2*-injective {2suc _}  {0#}      () 
suc2*-injective {2suc _}  {2suc _}  refl =  refl 
suc2*-injective {2suc _}  {suc2* _} ()
suc2*-injective {suc2* _} {0#}      ()
suc2*-injective {suc2* _} {2suc _}  ()
suc2*-injective {suc2* _} {suc2* _} refl =  refl


_≟_ :  Decidable₂ (_≡_ {A = Bin})
0#        ≟ 0#        =  yes refl
0#        ≟ (2suc _)  =  no λ()
0#        ≟ (suc2* _) =  no λ()
(2suc _)  ≟ 0#        =  no λ()
(2suc x)  ≟ (2suc y)  =  case x ≟ y 
                         of \ 
                         { (yes eq) → yes (cong 2suc eq)
                         ; (no ne)  → no (\x'≡y' → ne (2suc-injective x'≡y'))
                         } 
(2suc _)  ≟ (suc2* _) =  no λ() 
(suc2* _) ≟ 0#        =  no λ() 
(suc2* _) ≟ (2suc _)  =  no λ() 
(suc2* x) ≟ (suc2* y) =  case x ≟ y 
                         of \ 
                         { (yes eq) → yes (cong suc2* eq)
                         ; (no ne)  → no (\x'≡y' → ne (suc2*-injective x'≡y'))
                         } 

2suc≢0 :  {x : Bin} → 2suc x ≢ 0#
2suc≢0 ()

suc2*≢0 :  {x : Bin} → suc2* x ≢ 0#
suc2*≢0 ()

----------------------------------------------------
size : Bin → ℕ       -- (number of constructors) - 1
size 0#        = 0
size (2suc x)  = 1+ (size x)
size (suc2* x) = 1+ (size x)

|x|≡0⇒x≡0 :  {x : Bin} → size x ≡ 0 → x ≡ 0#  
|x|≡0⇒x≡0 {0#}     _ =  refl
|x|≡0⇒x≡0 {2suc _}  () 
|x|≡0⇒x≡0 {suc2* _} () 



--============================================================================
-- Arithmetic operations on Bin and their properties. 

suc : Bin → Bin 
suc 0#        =  suc2* 0#
suc (2suc x)  =  suc2* (suc x)   -- 1 + 2(1+x) 
suc (suc2* x) =  2suc x          -- 1 + 1 + 2x =  2*(1+x)

1# = suc 0#;   2# = suc 1#;   3# = suc 2#;   4# = suc 3#;   5# = suc 4#

---------------------------
suc≢0 :  ∀ {x} → suc x ≢ 0#
suc≢0 {0#}      () 
suc≢0 {2suc _}  () 
suc≢0 {suc2* _} () 

------------
infixl 6 _+_

_+_ : Op₂ Bin
0#        + y         =  y
x         + 0#        =  x
(2suc x)  + (2suc y)  =  2suc (suc (x + y))
                                       -- 2(1+x) + 2(1+y) =  2(1 + 1+x+y)
(2suc x)  + (suc2* y) =  suc (2suc (x + y))
                                       -- 2(1+x) + 1 + 2y =  1 + 2(1+x+y)
(suc2* x) + (2suc y)  =  suc (2suc (x + y))
(suc2* x) + (suc2* y) =  suc (suc2* (x + y))
                              -- 1+2x + 1+2y =  2 + 2(x+y) =  1 + 1 + 2(x+y)
--------------------
sum : List Bin → Bin
sum []       =  0#
sum (x ∷ xs) =  x + (sum xs)

--------------
2* : Bin → Bin
2* 0#        = 0#
2* (2suc x)  = 2suc (suc2* x) 
                            -- 2(1+x) + 2(1+x) = 2(1+x + 1+x) =  2(1 + 1+2x)
2* (suc2* x) = 2suc (2* x)

----------------
pred : Bin → Bin
pred 0#        =  0#
pred (2suc x)  =  suc2* x   -- 2(1+x) - 1 =  1+2x
pred (suc2* x) =  2* x      -- 1 + 2x -1  =  2x


---------------------------
2suc-as∘ :  2suc ≗ 2* ∘ suc 
2suc-as∘ 0#       =  refl
2suc-as∘ (2suc x) =  
                  begin 2suc (2suc x)        ≡⟨ cong 2suc (2suc-as∘ x) ⟩
                        2suc (2* (suc x))    ≡⟨ refl ⟩
                        2* (suc2* (suc x))   ≡⟨ refl ⟩
                        2* (suc (2suc x))   
                  ∎
2suc-as∘ (suc2* x) =  refl 


-- suc2*∘suc≗suc∘2suc :  suc2* ∘ suc ≗ suc ∘ 2suc   -- is by  const refl

suc2*-as∘ :  suc2* ≗ suc ∘ 2*   
suc2*-as∘ 0#        = refl
suc2*-as∘ (2suc x)  = refl
suc2*-as∘ (suc2* x) = 
          begin suc2* (suc2* x)     ≡⟨ cong suc2* (suc2*-as∘ x) ⟩
                suc2* (suc 2x)      ≡⟨ refl ⟩
                suc (2suc 2x)       ≡⟨ cong suc (2suc-as∘ 2x) ⟩
                suc (2* (suc 2x))   ≡⟨ cong (suc ∘ 2*) (sym (suc2*-as∘ x)) ⟩
                suc (2* (suc2* x))                         
          ∎
          where 
          2x = 2* x

---------------------------
pred∘suc :  pred ∘ suc ≗ id
pred∘suc 0#        =  refl 
pred∘suc (2suc x)  =  sym (2suc-as∘ x) 
pred∘suc (suc2* x) =  refl


suc∘pred :  (x : Bin) → x ≢ 0# → suc (pred x) ≡ x

suc∘pred 0#        0≢0 =  contradiction refl 0≢0 
suc∘pred (2suc _)  _   =  refl 
suc∘pred (suc2* x) _   =  begin suc (pred (suc2* x))  ≡⟨ refl ⟩
                                suc (2* x)            ≡⟨ sym (suc2*-as∘ x) ⟩
                                suc2* x
                          ∎

----------------------------
0+ :  (x : Bin) → 0# + x ≡ x
0+ _ = refl

+0 :  (x : Bin) → x + 0# ≡ x
+0 0#        = refl
+0 (2suc _)  = refl 
+0 (suc2* _) = refl

-------------
2^ :  ℕ → Bin 
2^ 0      =  1#
2^ (1+ n) =  2* (2^ n)


------------
infixl 7 _*_

_*_ : Op₂ Bin

0#        * _         =  0#
_         * 0#        =  0#
(2suc x)  * (2suc y)  =  2* (2suc (x + (y + x * y)))
(2suc x)  * (suc2* y) =  2suc (x + y * (2suc x))
                      --
                      -- 2(1+x) * (1+2y) =  2(1 + 2y + x + 2xy) 
                      --                 =  2(1 + x + y*2(1 + x))

(suc2* x) * (2suc y)  =  2suc (y + x * (2suc y))
(suc2* x) * (suc2* y) =  suc2* (x + y * (suc2* x))
            --
            -- (1 + 2x)(1 + 2y) =  1 + (2y + 2x + 4xy)
            --                     1 + 2(x + y * (1 + 2x))

-----------------------------
infixl 8 _^_

_^_ : Bin → ℕ → Bin
_ ^ 0      =  1#
x ^ (1+ n) =  x * (x ^ n)

-----------------------------
0* :  (x : Bin) → 0# * x ≡ 0# 
0* _ =  refl

*0 :  (x : Bin) → x * 0#  ≡ 0# 
*0 0#        =  refl
*0 (2suc _)  =  refl
*0 (suc2* _) =  refl


x*y≡0⇒⊎ :  {x y : Bin} → x * y ≡ 0# → x ≡ 0# ⊎ y ≡ 0#

x*y≡0⇒⊎ {0#}      {_ }       _ =  inj₁ refl
x*y≡0⇒⊎ {_}       {0#}       _ =  inj₂ refl
x*y≡0⇒⊎ {2suc _}  {2suc _}  ()
x*y≡0⇒⊎ {2suc _}  {suc2* _} ()
x*y≡0⇒⊎ {suc2* _} {2suc _}  ()
x*y≡0⇒⊎ {suc2* _} {suc2* _} ()

nz*nz :  {x y : Bin} → x ≢ 0# → y ≢ 0# → x * y ≢ 0#
nz*nz x≢0 y≢0 xy≡0 = 
                   case  x*y≡0⇒⊎ xy≡0  of \ { (inj₁ x≡0) → x≢0 x≡0 
                                            ; (inj₂ y≡0) → y≢0 y≡0 } 

infix 4 _∣_

_∣_ :  Rel Bin 0ℓ
x ∣ y =  ∃ (\q → x * q ≡ y)

2*≢1 :  {x : Bin} → 2* x ≢ 1#
2*≢1 {0#}      () 
2*≢1 {2suc _}  () 
2*≢1 {suc2* _} () 

------------------------------------------------------------------------------
suc≗1+ :  suc ≗ (1# +_)
suc≗1+ 0#        =  refl
suc≗1+ (2suc _)  =  refl
suc≗1+ (suc2* _) =  refl

----------------------------------------------------
suc+assoc :  (x y : Bin) → (suc x) + y ≡ suc (x + y)

suc+assoc 0# y =  begin suc 0# + y     ≡⟨ refl ⟩
                        1# + y         ≡⟨ sym (suc≗1+ y) ⟩
                        suc y          ≡⟨ refl ⟩
                        suc (0# + y)
                  ∎
suc+assoc x 0# =  begin suc x + 0#     ≡⟨ +0 (suc x) ⟩
                        suc x          ≡⟨ cong suc (sym (+0 x)) ⟩
                        suc (x + 0#)
                  ∎

suc+assoc (2suc x) (2suc y) = 
  begin 
    (suc (2suc x)) + (2suc y)     ≡⟨ refl ⟩
    suc2* (suc x) + (2suc y)      ≡⟨ refl ⟩
    suc (2suc (suc x + y))        ≡⟨ cong (suc ∘ 2suc) (suc+assoc x y) ⟩
    suc (2suc (suc (x + y)))      ≡⟨ refl ⟩
    suc ((2suc x) + (2suc y))
  ∎

suc+assoc (2suc x) (suc2* y) =  
  begin 
    (suc (2suc x)) + (suc2* y)     ≡⟨ refl ⟩
    (suc2* (suc x)) + (suc2* y)    ≡⟨ refl ⟩
    suc (suc2* (suc x + y))        ≡⟨ cong (suc ∘ suc2*) (suc+assoc x y) ⟩
    suc (suc2* (suc (x + y)))      ≡⟨ refl ⟩
    suc (suc (2suc (x + y)))       ≡⟨ refl ⟩
    suc ((2suc x) + (suc2* y))
  ∎

suc+assoc (suc2* x) (2suc y)  =  refl
suc+assoc (suc2* x) (suc2* y) =  refl

1+≗suc :  (1# +_) ≗ suc
1+≗suc = suc+assoc 0#

-------------
infixr 7 2*'_

toℕ : Bin → ℕ 
toℕ 0#        =  0
toℕ (2suc x)  =  2 *' (1+ (toℕ x)) 
toℕ (suc2* x) =  1+ (2 *' (toℕ x))

 
2*'_ : ℕ → ℕ
2*'_ = (2 *'_) 

toℕ∘2* :  (x : Bin) → toℕ (2* x) ≡ 2*' (toℕ x) 
toℕ∘2* 0#       = refl
toℕ∘2* (2suc x) = 
       begin 
         toℕ (2* (2suc x))     ≡⟨ refl ⟩
         2*' (2 +' 2m)         ≡⟨ cong (2*'_ ∘ (_+' 2m)) (sym (Nat0.*1 2)) ⟩ 
         2*' (2*' 1 +' 2m)     ≡⟨ cong 2*'_ (sym (*'-lDistrib 2 1 m)) ⟩ 
         2*' (2*' (1+ m))      ≡⟨ refl ⟩
         2*' (toℕ (2suc x))
       ∎
       where
       m = toℕ x;  2m = 2*' m

toℕ∘2* (suc2* x) =  cong (2*'_ ∘ 1+_) (toℕ∘2* x)


-----------------------------------------------
toℕ∘suc :  (x : Bin) → toℕ (suc x) ≡ 1+ (toℕ x)
toℕ∘suc 0#        =  refl
toℕ∘suc (2suc x)  =  cong (1+_ ∘ (2 *'_)) (toℕ∘suc x)
toℕ∘suc (suc2* x) =  *'-lDistrib 2 1 (toℕ x)


toℕ∘pred :  (x : Bin) → toℕ (pred x) ≡ pred' (toℕ x)
toℕ∘pred x 
         with x ≟ 0#
... | yes x≡0 =  begin toℕ (pred x)    ≡⟨ cong (toℕ ∘ pred) x≡0 ⟩
                       0               ≡⟨ sym (cong (pred' ∘ toℕ) x≡0) ⟩
                       pred' (toℕ x)
                 ∎
... | no x≢0 =  
         begin toℕ (pred x)           ≡⟨ cong (toℕ ∘ pred) (sym suc-px≡x) ⟩
               toℕ (pred (suc px))    ≡⟨ cong toℕ (pred∘suc px) ⟩
               toℕ px                 ≡⟨ refl ⟩
               pred' (1+ (toℕ px))    ≡⟨ cong pred' (sym (toℕ∘suc px)) ⟩
               pred' (toℕ (suc px))   ≡⟨ cong (pred' ∘ toℕ) suc-px≡x ⟩
               pred' (toℕ x)
         ∎
         where
         px = pred x;  suc-px≡x = suc∘pred x x≢0


------------------------------------------------------------------------------
toℕ+homo :  (x y : Bin) → toℕ (x + y) ≡ toℕ x +' toℕ y
toℕ+homo 0# _  =  refl 
toℕ+homo x  0# =  begin toℕ (x + 0#)      ≡⟨ cong toℕ (+0 x) ⟩
                        toℕ x             ≡⟨ sym (+'-comm (toℕ x) 0) ⟩
                        toℕ x +' 0        ≡⟨ refl ⟩
                        toℕ x +' toℕ 0#
                  ∎
toℕ+homo (2suc x) (2suc y) =  
  begin
    toℕ ((2suc x) + (2suc y))        ≡⟨ refl ⟩
    toℕ (2suc (suc (x + y)))         ≡⟨ refl ⟩
    2 *' (1+ (toℕ (suc (x + y))))    ≡⟨ cong (2*'_ ∘ 1+_) (toℕ∘suc (x + y)) ⟩
    2 *' (1+ (1+ toℕ (x + y)))       ≡⟨ cong (2*'_ ∘ 1+_ ∘ 1+_)
                                                            (toℕ+homo x y) ⟩
    2 *' ((1+ (1+ (m +' n))))        ≡⟨ cong (2*'_ ∘ 1+_)
                                                   (sym (+'-assoc 1 m n))⟩
    2 *' ((1+ ((1+ m) +' n)))        ≡⟨ cong (2*'_ ∘ 1+_ ∘ (_+' n))
                                                           (+'-comm 1 m) ⟩
    2 *' ((1+ ((m +' 1) +' n)))      ≡⟨ cong (2*'_ ∘ 1+_) (+'-assoc m 1 n) ⟩
    2 *' ((1+ ((m +' (1+ n)))))      ≡⟨ cong 2*'_
                                                (sym (+'-assoc 1 m (1+ n))) ⟩
    2 *' ((1+ m) +' (1+ n))          ≡⟨ *'-lDistrib 2 (1+ m) (1+ n) ⟩
    (2*' (1+ m)) +' (2*' (1+ n))     ≡⟨ refl ⟩
    toℕ (2suc x) +' toℕ (2suc y)
  ∎
  where
  m = toℕ x;  n = toℕ y

toℕ+homo (2suc x) (suc2* y) =  
  begin
    toℕ ((2suc x) + (suc2* y))     ≡⟨ refl ⟩
    toℕ (suc (2suc (x + y)))       ≡⟨ toℕ∘suc (2suc (x + y)) ⟩
    1+ (toℕ (2suc (x + y)))        ≡⟨ refl ⟩
    1+ (2*' (1+ (toℕ (x + y))))    ≡⟨ cong (1+_ ∘ 2*'_ ∘ 1+_) (toℕ+homo x y) ⟩
    1+ (2*' (1+ (m +' n)))         ≡⟨ cong (1+_ ∘ 2*'_) 
                                                     (sym (+'-assoc 1 m n)) ⟩
    1+ (2*' (1+m +' n))            ≡⟨ cong 1+_ (*'-lDistrib 2 1+m n) ⟩
    1+ ((2*' 1+m) +' 2*' n)        ≡⟨ k+[m+n]≡m+[k+n] 1 _ (2*' n) ⟩
    (2*' 1+m) +' (1+ (2*' n))      ≡⟨ refl ⟩
    toℕ (2suc x) +' toℕ (suc2* y)
  ∎
  where
  m = toℕ x;  n = toℕ y;  1+m = 1+ m


toℕ+homo (suc2* x) (2suc y) =  
  begin
    toℕ ((suc2* x) + (2suc y))      ≡⟨ refl ⟩
    toℕ (suc (2suc (x + y)))        ≡⟨ toℕ∘suc (2suc (x + y)) ⟩
    1+ (toℕ (2suc (x + y)))         ≡⟨ refl ⟩
    1+ (2*' (1+ (toℕ (x + y))))     ≡⟨ cong (1+_ ∘ 2*'_ ∘ 1+_) (toℕ+homo x y) 
                                     ⟩
    1+ (2*' (1+ (m +' n)))          ≡⟨ cong (1+_ ∘ 2*'_) 
                                                   (k+[m+n]≡m+[k+n] 1 m n) ⟩
    1+ (2*' (m +' 1+n))             ≡⟨ cong 1+_ (*'-lDistrib 2 m 1+n) ⟩
    1+ (2*' m +' 2*' 1+n)           ≡⟨ sym (+'-assoc 1 (2*' m) (2*' 1+n)) ⟩
    (1+ (2*' m)) +' (2*' (1+ n))    ≡⟨ refl ⟩
    toℕ (suc2* x) +' toℕ (2suc y)
  ∎
  where
  m = toℕ x;  n = toℕ y;  1+n = 1+ n

toℕ+homo (suc2* x) (suc2* y) = 
  begin
    toℕ ((suc2* x) + (suc2* y))    ≡⟨ refl ⟩
    toℕ (suc (suc2* (x + y)))      ≡⟨ toℕ∘suc (suc2* (x + y)) ⟩
    1+ (toℕ (suc2* (x + y)))       ≡⟨ refl ⟩
    1+ (1+ (2*' (toℕ (x + y))))    ≡⟨ cong (1+_ ∘ 1+_ ∘ 2*'_) (toℕ+homo x y) ⟩
    1+ (1+ (2*' (m +' n)))         ≡⟨ cong (1+_ ∘ 1+_) (*'-lDistrib 2 m n) ⟩
    1+ (1+ (2*' m +' 2*' n))       ≡⟨ cong 1+_ (sym (+'-assoc 1 (2*' m) _)) ⟩
    1+ ((1+ (2*' m) +' (2*' n)))   ≡⟨ k+[m+n]≡m+[k+n] 1 (1+ (2*' m)) _ ⟩
    (1+ (2*' m)) +' (1+ (2*' n))   ≡⟨ refl ⟩
    toℕ (suc2* x) +' toℕ (suc2* y)
  ∎
  where 
  m = toℕ x;  n = toℕ y



-------------------------------------
fromℕ :  (n : ℕ) → ∃ (\x → toℕ x ≡ n)    -- Mind:  it costs O(n) 
fromℕ 0      =  (0# , refl)
fromℕ (1+ n) =  aux (fromℕ n)
      where
      aux :  ∃ (\x → toℕ x ≡ n) → ∃ (\y → toℕ y ≡ 1+ n)

      aux (x , toℕ-x≡n) =  (suc x , toℕ-suc-x≡1+n)
                    where
                    toℕ-suc-x≡1+n =  begin toℕ (suc x)  ≡⟨ toℕ∘suc x ⟩    
                                           1+ (toℕ x)   ≡⟨ cong 1+_ toℕ-x≡n ⟩
                                           1+ n
                                     ∎

fromℕ₁ = proj₁ ∘ fromℕ 
     
-- fromℕ₁∘1+ :  fromℕ₁ ∘ 1+_ ≗ suc ∘ fromℕ₁
-- fromℕ₁∘1+ _ = refl

test :  -- fromℕ₁ 1 ≡ suc2* 0#,   2 -> 2suc 0#  ,  3 -> suc2* (suc2* 0#)  
        fromℕ₁ 4 ≡ 2suc (suc2* 0#)
test = refl

-----------------------------------------------------------------
fromℕ₁+homo :  (m n : ℕ ) → fromℕ₁ (m +' n) ≡ fromℕ₁ m + fromℕ₁ n
fromℕ₁+homo 0      _ =  refl
fromℕ₁+homo (1+ m) n = 
            begin
              fromℕ₁ ((1+ m) +' n)         ≡⟨ refl ⟩    
              fromℕ₁ (1+ (m +' n))         ≡⟨ refl ⟩
              suc (fromℕ₁ (m +' n))        ≡⟨ cong suc (fromℕ₁+homo m n) ⟩
              suc (a + b)                  ≡⟨ sym (suc+assoc a b) ⟩
              (suc a) + b                  ≡⟨ refl ⟩
              (fromℕ₁ (1+ m)) + (fromℕ₁ n)
            ∎
            where
            a = fromℕ₁ m;  b = fromℕ₁ n  


-------------------------------
toℕ∘fromℕ₁ :  toℕ ∘ fromℕ₁ ≗ id 

toℕ∘fromℕ₁ 0      =  refl
toℕ∘fromℕ₁ (1+ n) = 
               begin toℕ (fromℕ₁ (1+ n))    ≡⟨ refl ⟩
                     toℕ (suc (fromℕ₁ n))   ≡⟨ toℕ∘suc (fromℕ₁ n) ⟩
                     1+ (toℕ (fromℕ₁ n))    ≡⟨ cong 1+_ (toℕ∘fromℕ₁ n) ⟩
                     1+ n
               ∎

------------------------------
toℕ-injective :  Injective toℕ
toℕ-injective {0#}     {0#}      _  =  refl
toℕ-injective {0#}     {2suc _}  () 
toℕ-injective {0#}     {suc2* _} () 
toℕ-injective {2suc _} {0#}      () 
toℕ-injective {2suc x} {2suc y}  2[1+xN]≡2[1+yN] =  cong 2suc x≡y 
                    where
                    xN        = toℕ x  
                    yN        = toℕ y
                    1+xN≡1+yN = *'-lCancel {1+ xN} {1+ yN} 1 2[1+xN]≡2[1+yN]
                    xN≡yN     = cong pred' 1+xN≡1+yN 
                    x≡y       = toℕ-injective xN≡yN

toℕ-injective {2suc x} {suc2* y} 2[1+xN]≡1+2yN =  
                        contradiction 2[1+xN]≡1+2yN (Nat0.2m≢1+2n 1+xN yN)
                        where
                        1+xN = 1+ (toℕ x);  yN = toℕ y

toℕ-injective {suc2* _} {0#} ()
toℕ-injective {suc2* x} {2suc y} 1+2xN≡2[1+yN] = 
                     contradiction (sym 1+2xN≡2[1+yN]) (Nat0.2m≢1+2n 1+yN xN)
                     where
                     xN = toℕ x;  1+yN = 1+ (toℕ y)

toℕ-injective {suc2* x} {suc2* y} 1+2xN≡1+2yN =  cong suc2* x≡y 
    where
    xN = toℕ x;  yN = toℕ y;  2xN≡2yN = cong pred' 1+2xN≡1+2yN

    xN≡yN = *'-lCancel {xN} {yN} 1 2xN≡2yN;   x≡y = toℕ-injective xN≡yN


-------------------------------
toℕ-surjective : Surjective toℕ

toℕ-surjective 0      =  (0# , refl)
toℕ-surjective (1+ n) =  let (a , toℕ-a≡n) = toℕ-surjective n
                             toℕ-suc-a≡1+n =
                                     begin toℕ (suc a)   ≡⟨ toℕ∘suc a ⟩
                                           1+ (toℕ a)    ≡⟨ cong 1+_ toℕ-a≡n ⟩
                                           1+ n
                                     ∎
                         in  
                         (suc a , toℕ-suc-a≡1+n)

-------------------------------
fromℕ₁∘toℕ :  fromℕ₁ ∘ toℕ ≗ id
fromℕ₁∘toℕ a =
             let (b , toℕ-b≡toℕ-a) = fromℕ (toℕ a)
             in  
             begin fromℕ₁ (toℕ a)   ≡⟨ refl ⟩
                   b                ≡⟨ toℕ-injective toℕ-b≡toℕ-a ⟩
                   a
             ∎

-- Summary:  
-- 1)  toℕ : Bin → ℕ  is an isomorphism by _+_,
-- 2)  fromℕ₁         is a homomorphisms by _+_ mutually inverse with toℕ.


------------------------------------------------------------------------------
-- Commutativity and associativity for _+_ are proved by using the isomorphism
-- to ℕ.

module FP-Bin = FuncProp (_≡_ {A = Bin})

+-comm :  FP-Bin.Commutative _+_
+-comm a b =
    begin a + b                     ≡⟨ sym (fromℕ₁∘toℕ (a + b)) ⟩
          fromℕ₁ (toℕ (a + b))      ≡⟨ cong fromℕ₁ (toℕ+homo a b) ⟩
          fromℕ₁ (toℕ a +' toℕ b)   ≡⟨ cong fromℕ₁ (+'-comm (toℕ a) (toℕ b)) ⟩
          fromℕ₁ (toℕ b +' toℕ a)   ≡⟨ cong fromℕ₁ (sym (toℕ+homo b a)) ⟩
          fromℕ₁ (toℕ (b + a))      ≡⟨ fromℕ₁∘toℕ (b + a) ⟩
          b + a
    ∎

+-assoc :  FP-Bin.Associative _+_
+-assoc a b c =
  begin
    (a + b) + c                   ≡⟨ sym (fromℕ₁∘toℕ ((a + b) + c)) ⟩
    fromℕ₁ (toℕ ((a + b) + c))    ≡⟨ cong fromℕ₁ (toℕ+homo (a + b) c) ⟩
    fromℕ₁ (toℕ (a + b) +' cN)    ≡⟨ cong (fromℕ₁ ∘ (_+' cN)) (toℕ+homo a b) ⟩
    fromℕ₁ ((aN +' bN) +' cN)     ≡⟨ cong fromℕ₁ (+'-assoc aN bN cN) ⟩
    fromℕ₁ (aN +' (bN +' cN))     ≡⟨ cong (fromℕ₁ ∘ (aN +'_))
                                                  (sym (toℕ+homo b c)) ⟩
    fromℕ₁ (aN +' toℕ (b + c))    ≡⟨ cong fromℕ₁ (sym (toℕ+homo a (b + c))) ⟩
    fromℕ₁ (toℕ (a + (b + c)))    ≡⟨ fromℕ₁∘toℕ (a + (b + c)) ⟩
    (a + (b + c))
  ∎
  where
  aN = toℕ a;   bN = toℕ b;   cN = toℕ c


x+[y+z]≡y+[x+z] :  ∀ x y z → x + (y + z) ≡ y + (x + z)
x+[y+z]≡y+[x+z] x y z =
                    begin x + (y + z)   ≡⟨ sym (+-assoc x y z) ⟩
                         (x + y) + z    ≡⟨ cong (_+ z) (+-comm x y) ⟩
                         (y + x) + z    ≡⟨ +-assoc y x z ⟩
                         y + (x + z)
                    ∎
                
[x+y]+z≡y+[x+z] :  ∀ x y z → (x + y) + z ≡ y + (x + z)
[x+y]+z≡y+[x+z] x y z =
                      begin (x + y) + z    ≡⟨ cong (_+ z) (+-comm x y) ⟩
                            (y + x) + z    ≡⟨ +-assoc y x z ⟩
                            y + (x + z)
                      ∎

--------------------------------------------
+-lCancel :  ∀ x y z → x + y ≡ x + z → y ≡ z      -- the proof is via toℕ
+-lCancel x y z x+y≡x+z =
                        begin y           ≡⟨ sym (fromℕ₁∘toℕ y) ⟩
                              fromℕ₁ m    ≡⟨ cong fromℕ₁ m≡n ⟩
                              fromℕ₁ n    ≡⟨ fromℕ₁∘toℕ z ⟩
                              z
                        ∎
         where
         k = toℕ x;  m = toℕ y;  n = toℕ z

         eq = begin k +' m         ≡⟨ sym (toℕ+homo x y) ⟩
                    toℕ (x + y)    ≡⟨ cong toℕ x+y≡x+z ⟩
                    toℕ (x + z)    ≡⟨ toℕ+homo x z ⟩
                    k +' n
              ∎

         m≡n = begin m                ≡⟨ sym (NatP.m+n∸n≡m m k)⟩
                     (m +' k) ∸' k    ≡⟨ cong (_∸' k) (+'-comm m k) ⟩
                     (k +' m) ∸' k    ≡⟨ cong (_∸' k) eq ⟩
                     (k +' n) ∸' k    ≡⟨ cong (_∸' k) (+'-comm k n) ⟩
                     (n +' k) ∸' k    ≡⟨ NatP.m+n∸n≡m n k ⟩
                     n
               ∎


+-rCancel :  ∀ x y z → y + x ≡ z + x → y ≡ z
+-rCancel x y z y+x≡z+x =
                        +-lCancel x y z x+y≡x+z
                        where
                        x+y≡x+z = begin x + y    ≡⟨ +-comm x y ⟩
                                        y + x    ≡⟨ y+x≡z+x ⟩
                                        z + x    ≡⟨ +-comm z x ⟩
                                        x + z
                                  ∎

------------------------------------------------------------------------------
setoid : Setoid 0ℓ 0ℓ 
setoid = PE.setoid Bin

decEquivalence :  IsDecEquivalence (_≡_ {A = Bin})
decEquivalence =  record{ isEquivalence = isEquivalence;  _≟_ = _≟_ }

decSetoid : DecSetoid 0ℓ 0ℓ 
decSetoid = record{ Carrier          =  Bin
                  ; _≈_              =  _≡_
                  ; isDecEquivalence =  decEquivalence }

+-isSemigroup : IsSemigroup _≡_ _+_
+-isSemigroup = record{ isEquivalence = isEquivalence
                      ; assoc         = +-assoc
                      ; ∙-cong        = cong₂ _+_ }

+-semigroup : Semigroup 0ℓ 0ℓ
+-semigroup =
            record{ Carrier = Bin;  _≈_ = _≡_;  _∙_ = _+_;  
                    isSemigroup = +-isSemigroup }

 
+-isMonoid : IsMonoid _≡_ _+_ 0#
+-isMonoid = record{ isSemigroup = +-isSemigroup;  identity = (0+ , +0) }


+-monoid : Monoid 0ℓ 0ℓ
+-monoid = record{ Carrier = Bin;
                   _≈_ = _≡_;  _∙_ = _+_;  ε = 0#;  isMonoid = +-isMonoid }


+-isCommutativeMonoid : IsCommutativeMonoid _≡_ _+_ 0#
+-isCommutativeMonoid =  record{ isSemigroup = +-isSemigroup
                               ; identityˡ   = 0+
                               ; comm        = +-comm }

+-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
+-commutativeMonoid = 
                    record{ Carrier = Bin;  _≈_ = _≡_;   _∙_ = _+_;   ε = 0#;
                            isCommutativeMonoid = +-isCommutativeMonoid }
