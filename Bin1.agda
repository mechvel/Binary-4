{-
This file is a part of the library  Binary-4.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.

Binary-4  is free software: you can redistribute it and/or modify it
under the terms of the GNU General Public License.
See  license.txt.
-}

module Bin1 where

open import Level    using () renaming (zero to 0ℓ)
open import Function using (id; _∘_; case_of_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality as PE using
                 (_≡_; _≢_; _≗_; refl; sym; trans; cong; cong₂; isEquivalence)
open PE.≡-Reasoning
open import Algebra using (Semigroup; Monoid; CommutativeMonoid; Semiring;
                                                         CommutativeSemiring)
open import Algebra.Structures using 
            (IsSemigroup; IsMonoid; IsCommutativeMonoid; IsSemiring; 
             IsSemiringWithoutAnnihilatingZero; IsCommutativeSemiring
            )
import Algebra.FunctionProperties as FuncProp
open import Data.Sum     using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Nat using (ℕ; s≤s) renaming (suc to 1+_; _+_ to _+'_; 
                                              _*_ to _*'_; _≤_ to _≤'_)
open import Data.Nat.Properties as NatP using (module ≤-Reasoning)
     renaming (+-assoc to +'-assoc; +-comm to +'-comm;
               *-assoc to *'-assoc; *-comm to *'-comm;
               *-distribˡ-+ to *'-lDistrib; *-distribʳ-+ to *'-rDistrib;
               ≤-refl to ≤'-refl; +-monoʳ-≤ to +'-monoʳ-≤
              )
open ≤-Reasoning using () renaming (begin_ to ≤begin_; _∎ to _≤end;
                                    _≡⟨_⟩_ to _≡≤[_]_; _≤⟨_⟩_ to _≤[_]_)

-- of application ---
open import Nat0 using (k+[m+n]≡m+[k+n]; k*[m*n]≡m*[k*n]) 
                 renaming (1* to 1*'; *1 to *'1)
open import Bin0 using 
            (Bin; 1#; 2#; size; suc; 2*; 2*'_; 2^; toℕ; fromℕ₁; _+_; _*_; _∣_;
             +0; *0; 2suc≢0; toℕ∘2*; suc≗1+; x*y≡0⇒⊎; toℕ+homo; toℕ-injective; 
             fromℕ₁∘toℕ; toℕ∘fromℕ₁; +-isCommutativeMonoid)



--****************************************************************************
open Bin

2*'∘2*' =  2*'_ ∘ 2*'_

------------------------------------------------------
toℕ*homo :  (x y : Bin) → toℕ (x * y) ≡ toℕ x *' toℕ y
toℕ*homo x y = 
             aux x y (size x +' size y) ≤'-refl
  where
  aux :  (x y : Bin) → (cnt : ℕ) → (size x +' size y ≤' cnt) →
                                   toℕ (x * y) ≡ toℕ x *' toℕ y
  aux 0# _  _ _ = refl
  aux x  0# _ _ = begin toℕ (x * 0#)       ≡⟨ cong toℕ (*0 x) ⟩
                        0                  ≡⟨ sym (Nat0.*0 (toℕ x)) ⟩
                        toℕ x *' toℕ 0#
                  ∎

      --------
  aux (2suc x) (2suc y) (1+ cnt) (s≤s |x|+1+|y|≤cnt) = 
    begin 
      toℕ (2suc x * 2suc y)                ≡⟨ refl ⟩
      toℕ (2* (2suc (x + (y + xy))))       ≡⟨ toℕ∘2* (2suc (x + (y + xy))) ⟩
      2*' (toℕ (2suc (x + (y + xy))))      ≡⟨ refl ⟩
      2*'∘2*' (1+ (toℕ (x + (y + xy))))    ≡⟨ cong (2*'∘2*' ∘ 1+_) 
                                                      (toℕ+homo x (y + xy)) ⟩
      2*'∘2*' (1+ (m +' (toℕ (y + xy))))   ≡⟨ cong (2*'∘2*' ∘ 1+_ ∘ (m +'_)) 
                                                            (toℕ+homo y xy) ⟩
      2*'∘2*' (1+ (m +' (n +' toℕ xy)))
                                   ≡⟨ cong (2*'∘2*' ∘ 1+_ ∘ (m +'_) ∘ (n +'_))
                                           (aux x y cnt |x|+|y|≤cnt) 
                                    ⟩
      2*'∘2*' (1+ (m +' (n +' mn)))   ≡⟨ cong 2*'∘2*' (sym eq) ⟩  
      2*' (2*' (1+m *' 1+n))          ≡⟨ cong 2*'_ (k*[m*n]≡m*[k*n] 2 1+m 1+n)
                                       ⟩
      2*' (1+m *' (2*' 1+n))          ≡⟨ sym (*'-assoc 2 1+m (2*' 1+n)) ⟩ 
      (2*' 1+m) *' (2*' 1+n)          ≡⟨ refl ⟩
      toℕ (2suc x) *' toℕ (2suc y)
    ∎
    where
    m  = toℕ x;    n  = toℕ y;   1+m = 1+ m;    1+n = 1+ n   
    mn = m *' n;   xy = x * y

    eq = begin 
          (1+m *' (1+ n))            ≡⟨ *'-lDistrib 1+m 1 n ⟩ 
          (1+m *' 1 +' 1+m *' n)     ≡⟨ cong (_+' (1+m *' n)) (Nat0.*1 1+m) ⟩
          1+ (m +' 1+m *' n)         ≡⟨ cong (1+_ ∘ (m +'_)) 
                                                       (*'-rDistrib n 1 m) ⟩ 
          1+ (m +' (1 *' n +' mn))   ≡⟨ cong (1+_ ∘ (m +'_) ∘ (_+' mn))
                                                            (Nat0.1* n) ⟩ 
          1+ (m +' (n +' mn))
         ∎

    |x|+|y|≤cnt = 
           ≤begin size x +' size y          ≤[ +'-monoʳ-≤ (size x) 
                                                       (NatP.n≤1+n (size y)) ]
                  size x +' (1+ (size y))   ≤[ |x|+1+|y|≤cnt ] 
                  cnt 
           ≤end

  aux (2suc x) (suc2* y) (1+ cnt) (s≤s |x|+1+|y|≤cnt) =  
    begin
      toℕ ((2suc x) * (suc2* y))           ≡⟨ refl ⟩
      toℕ (2suc (x + y * (2suc x)))        ≡⟨ refl ⟩
      2*' (1+ (toℕ (x + y * (2suc x))))    ≡⟨ cong (2*'_ ∘ 1+_) (toℕ+homo x _)
                                            ⟩
      2*' (1+ (m +' (toℕ (y * (2suc x)))))  ≡⟨ cong (2*'_ ∘ 1+_ ∘ (m +'_)) 
                                                (aux y _ cnt |y|+1+|x|≤cnt) ⟩
      2*' (1+m +' (n *' (toℕ (2suc x))))    ≡⟨ refl ⟩
      2*' (1+m +' (n *' 2[1+m]))            ≡⟨ *'-lDistrib 2 1+m _ ⟩
      2[1+m] +' (2*' (n *' 2[1+m]))         ≡⟨ cong (2[1+m] +'_)
                                                      (sym (*'-assoc 2 n _)) ⟩ 
      2[1+m] +' (2*' n) *' 2[1+m]           ≡⟨ cong (_+' ((2*' n) *' 2[1+m]))
                                                          (sym (1*' 2[1+m])) ⟩ 
      1 *' 2[1+m] +' 2n *' 2[1+m]           ≡⟨ sym (*'-rDistrib 2[1+m] 1 2n) ⟩
      (1+ 2n) *' 2[1+m]                     ≡⟨ *'-comm (1+ 2n) 2[1+m] ⟩ 
      2[1+m] *' (1+ 2n)                     ≡⟨ refl ⟩
      toℕ (2suc x) *' toℕ (suc2* y) 
    ∎
    where
    m = toℕ x;   n = toℕ y;   1+m = 1+ m;   2[1+m] = 2*' (1+ m);   2n = 2*' n

    |y|+1+|x|≤cnt =  
        ≤begin size y +' (1+ (size x))    ≡≤[ k+[m+n]≡m+[k+n] (size y) 1 _ ] 
               (1+ (size y)) +' size x    ≡≤[ +'-comm (1+ (size y)) (size x) ]
               size x +' (1+ (size y))     ≤[ |x|+1+|y|≤cnt ] 
               cnt 
        ≤end

      ---------
  aux (suc2* x) (2suc y) (1+ cnt) (s≤s |x|+1+|y|≤cnt) = 
    begin
      toℕ ((suc2* x) * (2suc y))             ≡⟨ refl ⟩
      toℕ (2suc (y + x * (2suc y)))          ≡⟨ refl ⟩
      2*' (1+ (toℕ (y + x * (2suc y))))      ≡⟨ cong (2*'_ ∘ 1+_)
                                                (toℕ+homo y (x * (2suc y))) ⟩
      2*' (1+ (n +' (toℕ (x * (2suc y)))))  
                                         ≡⟨ cong (2*'_ ∘ 1+_ ∘ (n +'_))
                                            (aux x (2suc y) cnt |x|+1+|y|≤cnt) 
                                          ⟩
      2*' (1+n +' (m *' toℕ (2suc y)))   ≡⟨ refl ⟩
      2*' (1+n +' (m *' 2[1+n]))         ≡⟨ *'-lDistrib 2 1+n _ ⟩
      2[1+n] +' (2*' (m *' 2[1+n]))      ≡⟨ cong (2[1+n] +'_)
                                                 (sym (*'-assoc 2 m _))
                                          ⟩
      2[1+n] +' 2m *' 2[1+n]             ≡⟨ cong (_+' (2m *' 2[1+n]))
                                                      (sym (Nat0.1* 2[1+n])) ⟩
      1 *' 2[1+n] +' 2m *' 2[1+n]        ≡⟨ sym (*'-rDistrib 2[1+n] 1 2m) ⟩
      (1+ 2m) *' 2[1+n]                  ≡⟨ refl ⟩
      toℕ (suc2* x) *' toℕ (2suc y)
    ∎
    where
    m = toℕ x;   n = toℕ y;   1+n = 1+ n;   2m = 2*' m;   2[1+n] = 2*' (1+ n)


  aux (suc2* x) (suc2* y) (1+ cnt) (s≤s |x|+1+|y|≤cnt) = 
    begin
     toℕ ((suc2* x) * (suc2* y))          ≡⟨ refl ⟩
     toℕ (suc2* (x + y * [1+2x]))         ≡⟨ refl ⟩
     1+ (2*' (toℕ (x + y * [1+2x])))      ≡⟨ cong (1+_ ∘ 2*'_)
                                                 (toℕ+homo x (y * [1+2x])) ⟩
     1+ (2*' (m +' (toℕ (y * [1+2x]))))   ≡⟨ cong (1+_ ∘ 2*'_ ∘ (m +'_))
                                              (aux y [1+2x] cnt |y|+1+|x|≤cnt) 
                                           ⟩
     1+ (2*' (m +' (n *' [1+2x]')))       ≡⟨ cong 1+_ 
                                              (*'-lDistrib 2 m (n *' [1+2x]'))
                                           ⟩
     1+ (2m +' (2*' (n *' [1+2x]')))      ≡⟨ cong (1+_ ∘ (2m +'_))  
                                                      (sym (*'-assoc 2 n _)) ⟩
     (1+ 2m) +' 2n *' [1+2x]'             ≡⟨ refl ⟩
     [1+2x]' +' 2n *' [1+2x]'             ≡⟨ cong (_+' (2n *' [1+2x]')) 
                                                       (sym (Nat0.1* [1+2x]'))
                                           ⟩
     1 *' [1+2x]' +' 2n *' [1+2x]'        ≡⟨ sym (*'-rDistrib [1+2x]' 1 2n) ⟩
     (1+ 2n) *' [1+2x]'                   ≡⟨ *'-comm (1+ 2n) [1+2x]' ⟩
     toℕ (suc2* x) *' toℕ (suc2* y)
    ∎
    where
    m      = toℕ x;     n       = toℕ y;       2m = 2*' m;    2n = 2*' n
    [1+2x] = suc2* x;   [1+2x]' = toℕ [1+2x]

    |y|+1+|x|≤cnt =
        ≤begin size y +' (1+ (size x))    ≡≤[ +'-comm (size y) (1+ (size x)) ]
               (1+ (size x)) +' size y    ≡≤[ k+[m+n]≡m+[k+n] 1 (size x) _ ]
               size x +' (1+ (size y))     ≤[ |x|+1+|y|≤cnt ] 
               cnt 
        ≤end

------------------------------------------------------------
fromℕ₁*homo :  ∀ m n → fromℕ₁ (m *' n) ≡ fromℕ₁ m * fromℕ₁ n
fromℕ₁*homo m n =
       begin
         fromℕ₁ (m *' n)           ≡⟨ cong fromℕ₁ (cong₂ _*'_ m≡aN n≡bN) ⟩
         fromℕ₁ (toℕ a *' toℕ b)   ≡⟨ cong fromℕ₁ (sym (toℕ*homo a b)) ⟩
         fromℕ₁ (toℕ (a * b))      ≡⟨ fromℕ₁∘toℕ (a * b) ⟩
         a * b
       ∎
       where
       a    = fromℕ₁ m;            b    = fromℕ₁ n
       m≡aN = sym (toℕ∘fromℕ₁ m);  n≡bN = sym (toℕ∘fromℕ₁ n)

----------------------
2*≗2#* :  2* ≗ (2# *_)
2*≗2#* x = 
         toℕ-injective eq
         where
         eq =  begin toℕ (2* x)     ≡⟨ toℕ∘2* x ⟩
                     2 *' (toℕ x)   ≡⟨ sym (toℕ*homo 2# x) ⟩
                     toℕ (2# * x)
               ∎

2x≡0⇒x≡0 :  {x : Bin} → 2* x ≡ 0# → x ≡ 0#
2x≡0⇒x≡0 {x} 2x≡0 =
                  let 2#*x≡0 :  2# * x ≡ 0#
                      2#*x≡0 =  trans (sym (2*≗2#* x)) 2x≡0
                  in
                  case  x*y≡0⇒⊎ 2#*x≡0  of \
                                     { (inj₁ 2≡0) → contradiction 2≡0 2suc≢0
                                     ; (inj₂ x≡0) → x≡0 }

x≢0⇒2x≢0 :  {x : Bin} → x ≢ 0# → 2* x ≢ 0#
x≢0⇒2x≢0 x≢0 = 
             x≢0 ∘ 2x≡0⇒x≡0

---------------------------
2^≢0 :  (n : ℕ) → 2^ n ≢ 0#
2^≢0 0      ()
2^≢0 (1+ n) =  2^≢0 n ∘ 2x≡0⇒x≡0


------------------------------------------------------------------------------
-- Commutativity and associativity for _*_, and distributivity of _*_ by _+_,
-- are proved by using the isomorphisms to ℕ implemented and proved earlier.

module FP-Bin = FuncProp (_≡_ {A = Bin})

*-comm :  FP-Bin.Commutative _*_
*-comm a b =
    begin a * b                     ≡⟨ sym (fromℕ₁∘toℕ (a * b)) ⟩
          fromℕ₁ (toℕ (a * b))      ≡⟨ cong fromℕ₁ (toℕ*homo a b) ⟩
          fromℕ₁ (toℕ a *' toℕ b)   ≡⟨ cong fromℕ₁ (*'-comm (toℕ a) (toℕ b)) ⟩
          fromℕ₁ (toℕ b *' toℕ a)   ≡⟨ cong fromℕ₁ (sym (toℕ*homo b a)) ⟩
          fromℕ₁ (toℕ (b * a))      ≡⟨ fromℕ₁∘toℕ (b * a) ⟩
          b * a
    ∎

*-assoc :  FP-Bin.Associative _*_
*-assoc a b c =
  begin
    (a * b) * c                   ≡⟨ sym (fromℕ₁∘toℕ ((a * b) * c)) ⟩
    fromℕ₁ (toℕ ((a * b) * c))    ≡⟨ cong fromℕ₁ (toℕ*homo (a * b) c) ⟩
    fromℕ₁ (toℕ (a * b) *' cN)    ≡⟨ cong (fromℕ₁ ∘ (_*' cN)) (toℕ*homo a b) ⟩
    fromℕ₁ ((aN *' bN) *' cN)     ≡⟨ cong fromℕ₁ (*'-assoc aN bN cN) ⟩
    fromℕ₁ (aN *' (bN *' cN))     ≡⟨ cong (fromℕ₁ ∘ (aN *'_))
                                                    (sym (toℕ*homo b c)) ⟩
    fromℕ₁ (aN *' toℕ (b * c))    ≡⟨ cong fromℕ₁ (sym (toℕ*homo a (b * c))) ⟩
    fromℕ₁ (toℕ (a * (b * c)))    ≡⟨ fromℕ₁∘toℕ (a * (b * c)) ⟩
    (a * (b * c))
  ∎
  where
  aN = toℕ a;   bN = toℕ b;   cN = toℕ c

---------------------------------------------------
2*-*-assoc :  (x y : Bin) → (2* x) * y ≡ 2* (x * y)
2*-*-assoc x y = 
               begin (2* x) * y      ≡⟨ cong (_* y) (2*≗2#* x) ⟩
                     (2# * x) * y    ≡⟨ *-assoc 2# x y ⟩
                     2# * (x * y)    ≡⟨ sym (2*≗2#* (x * y)) ⟩
                     2* (x * y)
               ∎

---------------------------------------------
lDistrib :  FP-Bin._DistributesOverˡ_ _*_ _+_
lDistrib a b c =
  begin
    a * (b + c)                         ≡⟨ sym (fromℕ₁∘toℕ (a * (b + c))) ⟩
    fromℕ₁ (toℕ (a * (b + c)))          ≡⟨ cong fromℕ₁ (toℕ*homo a (b + c)) ⟩
    fromℕ₁ (k *' (toℕ (b + c)))         ≡⟨ cong (fromℕ₁ ∘ (k *'_))
                                                          (toℕ+homo b c) ⟩
    fromℕ₁ (k *' (m +' n))              ≡⟨ cong fromℕ₁ (*'-lDistrib k m n) ⟩
    fromℕ₁ (k *' m +' k *' n)           ≡⟨ cong fromℕ₁
                                           (cong₂ _+'_ (sym (toℕ*homo a b))
                                                       (sym (toℕ*homo a c)))
                                         ⟩
    fromℕ₁ (toℕ (a * b) +' toℕ (a * c))  ≡⟨ cong fromℕ₁
                                              (sym (toℕ+homo (a * b) (a * c)))
                                          ⟩
    fromℕ₁ (toℕ (a * b + a * c))         ≡⟨ fromℕ₁∘toℕ (a * b + a * c) ⟩
    a * b + a * c
  ∎
  where
  k = toℕ a;   m = toℕ b;   n = toℕ c


rDistrib :  FP-Bin._DistributesOverʳ_ _*_ _+_
rDistrib a b c =
             begin (b + c) * a      ≡⟨ *-comm (b + c) a ⟩
                   a * (b + c)      ≡⟨ lDistrib a b c ⟩
                   a * b + a * c    ≡⟨ cong₂ _+_ (*-comm a b) (*-comm a c) ⟩
                   b * a + c * a
             ∎

distrib :  FP-Bin._DistributesOver_ _*_ _+_
distrib =  (lDistrib , rDistrib)

2*-distrib : (x y : Bin) → 2* (x + y) ≡ 2* x + 2* y 
2*-distrib x y = 
               begin 2* (x + y)            ≡⟨ 2*≗2#* (x + y) ⟩
                     2# * (x + y)          ≡⟨ lDistrib 2# x y ⟩
                     (2# * x) + (2# * y)   ≡⟨ cong₂ _+_ eq1 eq2 ⟩
                     2* x + 2* y 
               ∎
               where
               eq1 = sym (2*≗2#* x);   eq2 = sym (2*≗2#* y)

------------------
1* :  (1# *_) ≗ id
1* x = 
     begin 1# * x                  ≡⟨ sym (fromℕ₁∘toℕ (1# * x)) ⟩
           fromℕ₁ (toℕ (1# * x))   ≡⟨ cong fromℕ₁ (toℕ*homo 1# x) ⟩
           fromℕ₁ (1 *' n)         ≡⟨ cong fromℕ₁ (1*' n) ⟩
           fromℕ₁ n                ≡⟨ fromℕ₁∘toℕ x ⟩
           x
     ∎
     where n = toℕ x 

*1 :  (_* 1#) ≗ id
*1 x = 
     begin x * 1#    ≡⟨ *-comm x 1# ⟩
           1# * x    ≡⟨ 1* x ⟩
           x
     ∎

2#*x≡x+x :  (x : Bin) → 2# * x ≡ x + x
2#*x≡x+x x =  
           begin 2# * x            ≡⟨ refl ⟩
                 (1# + 1#) * x     ≡⟨ rDistrib x 1# 1# ⟩
                 1# * x + 1# * x   ≡⟨ cong₂ _+_ (1* x) (1* x) ⟩
                 x + x
           ∎

2x≡x+x :  (x : Bin) → 2* x ≡ x + x
2x≡x+x x = 
         trans (2*≗2#* x) (2#*x≡x+x x)

[1+x]* :  (x y : Bin) → (1# + x) * y ≡ y + x * y
[1+x]* x y = 
            begin (1# + x) * y     ≡⟨ rDistrib y 1# x ⟩
                  1# * y + x * y   ≡⟨ cong (_+ (x * y)) (1* y) ⟩
                  y + x * y
            ∎

*[1+x] :  (x y : Bin) → y * (1# + x) ≡ y + y * x
*[1+x] x y = 
           begin y * (1# + x)     ≡⟨ lDistrib y 1# x ⟩
                 y * 1# + y * x   ≡⟨ cong (_+ (y * x)) (*1 y) ⟩
                 y + y * x
           ∎

suc* :  (x y : Bin) → (suc x) * y ≡ y + x * y
suc* x y = 
         begin (suc x) * y     ≡⟨ cong (_* y) (suc≗1+ x) ⟩
               (1# + x) * y    ≡⟨ [1+x]* x y ⟩
               y + x * y
         ∎

*suc :  (x y : Bin) → x * (suc y) ≡ x + x * y
*suc x y = 
         begin x * (suc y)     ≡⟨ cong (x *_) (suc≗1+ y) ⟩
               x * (1# + y)    ≡⟨ *[1+x] y x ⟩
               x + x * y
         ∎

2^-homo :  (m n : ℕ) → 2^ (m +' n) ≡ 2^ m * 2^ n
2^-homo 0 n =
            begin 2^ (0 +' n)    ≡⟨ refl ⟩
                  2^ n           ≡⟨ sym (1* (2^ n)) ⟩
                  1# * 2^ n      ≡⟨ refl ⟩
                  2^ 0 * 2^ n
            ∎

2^-homo (1+ m) n =   
            begin 2^ ((1+ m) +' n)        ≡⟨ refl ⟩
                  2^ (1+ (m +' n))        ≡⟨ refl ⟩
                  2* (2^ (m +' n))        ≡⟨ cong 2* (2^-homo m n) ⟩
                  2* (2^ m * 2^ n)        ≡⟨ sym (2*-*-assoc (2^ m) (2^ n)) ⟩
                  (2* (2^ m)) * (2^ n)    ≡⟨ refl ⟩
                  (2^ (1+ m)) * (2^ n)   
            ∎

------------------------------------------------------------------------------
-- These are about the division relation.

∣x⇒∣y*x :  {x : Bin} → (y z : Bin) → x ∣ y → x ∣ z * y
∣x⇒∣y*x {x} y z (q , xq≡y) =
                           (z * q , xzq≡zy)
                where
                xzq≡zy :  x * (z * q) ≡ z * y
                xzq≡zy =  begin x * (z * q)   ≡⟨ sym (*-assoc x z q) ⟩
                                (x * z) * q   ≡⟨ cong (_* q) (*-comm x z) ⟩
                                (z * x) * q   ≡⟨ *-assoc z x q ⟩
                                z * (x * q)   ≡⟨ cong (z *_) xq≡y ⟩
                                z * y
                          ∎

∣+ :  ∀ {x} → (y z : Bin) → x ∣ y → x ∣ z → x ∣ (y + z)
∣+ {x} y z (q , xq≡y) (q' , xq'≡z) =
                                   (q + q' , x[q+q']≡y+z)
           where
           x[q+q']≡y+z = begin x * (q + q')     ≡⟨ lDistrib x q q' ⟩
                               x * q + x * q'   ≡⟨ cong₂ _+_ xq≡y xq'≡z ⟩
                               y + z
                         ∎

------------------------------------------------------------------------------
*-isSemigroup : IsSemigroup _≡_ _*_
*-isSemigroup = record{ isEquivalence = isEquivalence
                      ; assoc         = *-assoc
                      ; ∙-cong        = cong₂ _*_ }

*-semigroup : Semigroup 0ℓ 0ℓ
*-semigroup =
            record{ Carrier = Bin;  _≈_ = _≡_;  _∙_ = _*_; 
                    isSemigroup = *-isSemigroup }

*-isMonoid : IsMonoid _≡_ _*_ 1#
*-isMonoid = record{ isSemigroup = *-isSemigroup;  identity = (1* , *1) }

*-monoid : Monoid 0ℓ 0ℓ
*-monoid = record{ Carrier = Bin;
                 _≈_ = _≡_;   _∙_ = _*_;   ε = 1#;   isMonoid = *-isMonoid }


*-isCommutativeMonoid : IsCommutativeMonoid _≡_ _*_ 1#
*-isCommutativeMonoid =  record{ isSemigroup = *-isSemigroup
                               ; identityˡ   = 1*
                               ; comm        = *-comm }

*-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
*-commutativeMonoid =
                    record{ Carrier = Bin;  _≈_ = _≡_;   _∙_ = _*_;   ε = 1#;
                            isCommutativeMonoid = *-isCommutativeMonoid }

isSemiringWithoutAnnihilatingZero :
                           IsSemiringWithoutAnnihilatingZero _≡_ _+_ _*_ 0# 1#
isSemiringWithoutAnnihilatingZero =
                 record{ +-isCommutativeMonoid = +-isCommutativeMonoid
                       ; *-isMonoid            = *-isMonoid
                       ; distrib               = distrib
                       }

isSemiring : IsSemiring _≡_ _+_ _*_ 0# 1#
isSemiring =
  record{ isSemiringWithoutAnnihilatingZero =
                                            isSemiringWithoutAnnihilatingZero
        ; zero = ((\x → refl {x = 0#}) , *0)
        }

semiring : Semiring 0ℓ 0ℓ
semiring = record{ Carrier    = Bin;         _≈_ = _≡_;    _+_ = _+_;
                   _*_        = _*_;         0#  = 0#;     1#  = 1#;
                   isSemiring = isSemiring
                 }


isCommutativeSemiring : IsCommutativeSemiring _≡_ _+_ _*_ 0# 1#
isCommutativeSemiring =
             record{ +-isCommutativeMonoid = +-isCommutativeMonoid
                   ; *-isCommutativeMonoid = *-isCommutativeMonoid
                   ; distribʳ              = rDistrib
                   ; zeroˡ                 = (\x → refl {x = 0#})
                   }

commutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
commutativeSemiring =
           record{ Carrier = Bin;
                   _≈_ = _≡_;  _+_ = _+_;  _*_ = _*_;  0# = 0#;  1# = 1#;
                   isCommutativeSemiring = isCommutativeSemiring
                 }

