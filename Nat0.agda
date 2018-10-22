{-
This file is a part of the library  Binary-4.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.

Binary-4  is free software: you can redistribute it and/or modify it
under the terms of the GNU General Public License.
See  license.txt.
-}

module Nat0 where

open import Level                     using () renaming (zero to 0ℓ)
open import Function                  using (_∘_; case_of_)
open import Relation.Nullary          using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Rel; DecSetoid; Tri; StrictTotalOrder) 
                            renaming (Decidable to Decidable₂) 
open import Relation.Binary.PropositionalEquality as PE 
                               using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open PE.≡-Reasoning
open import Algebra using (CommutativeSemiring)
import Algebra.FunctionProperties as FP 
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ; suc; _+_; _∸_; _*_; _≤_; _<_; _>_; z≤n; s≤s; 
                                                                  _≤?_; _≰_)
open import Data.Nat.Divisibility using (divides) 
                     renaming (_∣_ to Standard-∣; _∣?_ to standard-∣?)
open import Data.Nat.Properties as NProp using 
            (*-identityˡ; *-identityʳ; +-comm; +-assoc; *-comm; *-assoc; <⇒≤;
             <⇒≢; ≤-refl; ≤-reflexive; ≤-trans; ≤-step; m≤m+n; m+n∸m≡n;n∸n≡0; 
             m+n∸n≡m; *-distribˡ-+; *-distribʳ-∸; module ≤-Reasoning
            )
open ≤-Reasoning using () renaming (begin_ to ≤begin_; _∎ to _≤end;
                                          _≡⟨_⟩_ to _≡≤[_]_; _≤⟨_⟩_ to _≤[_]_)




--****************************************************************************
decSetoid : DecSetoid 0ℓ 0ℓ   -- DecSetoid for ℕ
decSetoid = NProp.≡-decSetoid

setoid = DecSetoid.setoid decSetoid
sto    = NProp.strictTotalOrder
open StrictTotalOrder sto public using (compare)

module FP-ℕ =  FP (_≡_ {A = ℕ})

1* = *-identityˡ
*1 = *-identityʳ 

*0 :  ∀ n → n * 0 ≡ 0
*0 n =  *-comm n 0

_<?_ : Decidable₂ _<_
_<?_ m =  _≤?_ (suc m)

_>?_ : Decidable₂ _>_
m >? n =  n <? m

open Tri 

≰⇒> :  ∀ {m n} → m ≰ n → m > n
≰⇒> {m} {n} m≰n =
            case compare m n of \
                 { (tri> _   _    m>n) → m>n
                 ; (tri< m<n _   _   ) → contradiction (<⇒≤ m<n) m≰n 
                 ; (tri≈ _   m=n _   ) → contradiction (≤-reflexive m=n) m≰n 
                 }

n≢1+n : ∀ {n} → n ≢ suc n  
n≢1+n ()

0<1+n : ∀ {n} → 0 < suc n
0<1+n = s≤s z≤n

n<1+n : ∀ {n} → n < suc n
n<1+n = ≤-refl

≤0⇒≡ : ∀ {n} → n ≤ 0 → n ≡ 0
≤0⇒≡ z≤n =  refl

suc≢0 : ∀ {n} → suc n ≢ 0
suc≢0 ()

0≢suc : ∀ {n} → 0 ≢ suc n
0≢suc ()

+≡0⇒both≡0 :  ∀ {m n} → m + n ≡ 0 → m ≡ 0 × n ≡ 0

+≡0⇒both≡0 {0}     {0}     _     = ( refl , refl)
+≡0⇒both≡0 {0}     {suc n} 1+n≡0 =  contradiction 1+n≡0 (suc≢0 {n})
+≡0⇒both≡0 {suc _} {_}     ()

k+[m+n]≡m+[k+n] :  ∀ k m n → k + (m + n) ≡ m + (k + n) 
k+[m+n]≡m+[k+n] k m n =
                    begin k + (m + n)   ≡⟨ sym (+-assoc k m n) ⟩
                         (k + m) + n    ≡⟨ cong (_+ n) (+-comm k m) ⟩
                         (m + k) + n    ≡⟨ +-assoc m k n ⟩
                          m + (k + n) 
                    ∎

[k+m]+n≡m+[k+n] :  ∀ k m n → (k + m) + n ≡ m + (k + n)
[k+m]+n≡m+[k+n] k m n =  
                      begin (k + m) + n    ≡⟨ cong (_+ n) (+-comm k m) ⟩
                            (m + k) + n    ≡⟨ +-assoc m k n ⟩
                            m + (k + n)
                      ∎

k*[m*n]≡m*[k*n] :  ∀ k m n → k * (m * n) ≡ m * (k * n) 
k*[m*n]≡m*[k*n] k m n =
                    begin k * (m * n)    ≡⟨ sym (*-assoc k m n) ⟩
                         (k * m) * n    ≡⟨ cong (_* n) (*-comm k m) ⟩
                      (   m * k) * n    ≡⟨ *-assoc m k n ⟩
                          m * (k * n) 
                    ∎

m+n'≡m'+n :  ∀ m n → m + suc n ≡ suc m + n
m+n'≡m'+n m n =
              sym (k+[m+n]≡m+[k+n] 1 m n)

-----------------------------------------------
*-distribˡ-∸ :  FP-ℕ._DistributesOverˡ_ _*_ _∸_
*-distribˡ-∸ k m n =
               begin k * (m ∸ n)      ≡⟨ *-comm k (m ∸ n) ⟩
                     (m ∸ n) * k      ≡⟨ *-distribʳ-∸ k m n ⟩
                     m * k ∸ n * k    ≡⟨ cong₂ _∸_ (*-comm m k) (*-comm n k) ⟩
                     k * m  ∸ k * n 
               ∎

m*[1+n] :  ∀ m n → m * (suc n) ≡ m + m * n
m*[1+n] m n =  
            begin m * (1 + n)     ≡⟨ *-distribˡ-+ m 1 n ⟩
                  m * 1 + m * n   ≡⟨ cong (_+ (m * n)) (*1 m) ⟩
                  m + m * n
            ∎

-------------------------------------------------
m>1⇒m*n≢1 :  ∀ {m n} → m > 1 → m * n ≢ 1 

m>1⇒m*n≢1 {m} {0}     _   m*0≡1  =  0≢suc 0≡1  where 
                                               0≡1 = trans (sym (*0 m)) m*0≡1
m>1⇒m*n≢1 {m} {suc n} m>1 m*n'≡1 =  <⇒≢ m*n'>1 (sym m*n'≡1)
                      where
                      m*n'>1 = ≤begin 2              ≤[ m>1 ]
                                      m              ≤[ m≤m+n m (m * n) ]
                                      m + m * n     ≡≤[ sym (m*[1+n] m n) ]  
                                      m * (suc n)
                               ≤end                                   

2m≢1+2n :  ∀ m n → 2 * m ≢ suc (2 * n)

2m≢1+2n m n 2m≡1+2n =  m>1⇒m*n≢1 {2} {m ∸ n} n<1+n 2[m-n]≡1
               where
               2n       = 2 * n
               2[m-n]≡1 = begin 2 * (m ∸ n)      ≡⟨ *-distribˡ-∸ 2 m n ⟩
                                2 * m ∸ 2n       ≡⟨ cong (_∸ 2n) 2m≡1+2n ⟩
                               (1 + 2n) ∸ 2n    ≡⟨ m+n∸n≡m 1 2n ⟩
                                1 
                          ∎

------------------------------------------------------------------------------
module FP-Nat = FP (_≡_ {A = ℕ})

*-rDistrib-∸ :  FP-Nat._DistributesOverʳ_ _*_ _∸_
*-rDistrib-∸ =  NProp.*-distribʳ-∸

*-lDistrib-∸ :  FP-Nat._DistributesOverˡ_ _*_ _∸_
*-lDistrib-∸ m n k =
               begin m * (n ∸ k)      ≡⟨ *-comm m (n ∸ k) ⟩
                     (n ∸ k) * m      ≡⟨ *-rDistrib-∸ m n k ⟩
                     n * m ∸ k * m    ≡⟨ cong₂ _∸_ (*-comm n m) (*-comm k m) ⟩
                     m * n ∸ m * k
               ∎