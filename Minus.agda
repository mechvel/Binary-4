{-
This file is a part of the library  Binary-4.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.

Binary-4  is free software: you can redistribute it and/or modify it
under the terms of the GNU General Public License.
See  license.txt.
-}

module Minus where

open import Function         using (id; _∘_; _$_; case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Tri; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality as PE using 
                         (_≡_; _≢_; _≗_; refl; sym; trans; cong; cong₂; subst)
open PE.≡-Reasoning renaming (begin_ to begin≡_; _∎ to _end≡)
open import Algebra.FunctionProperties as FuncProp using (Op₂)
open import Data.Empty   using (⊥)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂; ∃)
open import Data.Nat using (s≤s)
                  renaming (suc to 1+_; _+_ to _+'_; _*_ to _*'_; _∸_ to _∸'_; 
                                                     _<_ to _<'_; _≤_ to _≤'_)
open import Data.Nat.Properties as NatP using ()
     renaming (+-assoc to +'-assoc; +-comm to +'-comm; 
               *-distribˡ-+ to *'-lDistrib; ≤-reflexive to ≤'-reflexive;   
               +-monoʳ-≤ to +'-monoʳ-≤; *-monoʳ-< to *'-monoʳ-<; 
               *-monoʳ-≤ to *'-monoʳ-≤; ∸-mono to ∸'-mono
              ) 
open import LtReasoning using (module InequalityReasoning)  -- by U. Norell

-- of application ---
open import BPrelude using (_←→_; Injective)
import Nat0 
open import Bin0 using 
     (Bin; 1#; 2#; 2*; 2*'_; suc; pred; toℕ; fromℕ; fromℕ₁; _+_; _*_; toℕ∘2*; 
      +0; 0+; toℕ+homo; fromℕ₁+homo; 2suc-as∘; suc2*-as∘; suc≗1+; 2suc≢0; 
      suc≢0; pred∘suc; suc∘pred; +-comm; suc+assoc; 2*≢1; +-assoc; +-rCancel; 
      [x+y]+z≡y+[x+z]; fromℕ₁∘toℕ; toℕ∘fromℕ₁; x*y≡0⇒⊎
     )
open import Bin1 using (2*-distrib; toℕ*homo; fromℕ₁*homo; 2*≗2#*; *suc) 
open import Ord0 using 
     (_<_; _>_; _≤_; _≥_; _<?_; <-cmp; <-trans; ≤-refl; ≤-reflexive; ≤-trans; 
      ≤-antisym; <-≤-trans; ≤-<-trans; <-irrefl; 0<2suc; 0<suc2*; ≤⇒≯; <⇒≤; 
      ≡⇒≯; <⇒≱; ≮⇒≥; 0≤; ≮0; x<1+x; x<x+1; x<suc-x; 2suc-mono-<; +-monoʳ-<; 
      +-monoˡ-≤; fromℕ₁-mono-≤; suc2*-mono-<; 2*-mono-<; 2*-mono-≤; 
      suc2*<2suc)




--****************************************************************************
open InequalityReasoning {A = Bin} _<_ _≤_
                                   (\{x y}   → ≤-reflexive {x} {y})
                                   (\{x y z} → <-trans   {x} {y} {z})
                                   (\{x y z} → ≤-trans   {x} {y} {z})
                                   (\{x y z} → <-≤-trans {x} {y} {z})
                                   (\{x y z} → ≤-<-trans {x} {y} {z})
open Bin
open Tri

data Minus : Bin → Bin → Bin → Set
     where
     minuend< :  ∀ {x y d} → x < y → d ≡ 0# → Minus x y d
     minuend≡ :  ∀ {x y d} → x ≡ y → d ≡ 0# → Minus x y d
     minuend> :  ∀ {x y d} → x > y → (x ≡ y + d) → Minus x y d


minus :  (x y : Bin) → ∃ (\d → Minus x y d)

minus 0# 0#        =  (0# , minuend≡ refl refl) 
minus 0# (2suc x)  =  (0# , minuend< (0<2suc {x}) refl) 
minus 0# (suc2* x) =  (0# , minuend< (0<suc2* {x}) refl) 

---------------
minus (2suc x) 0#       =  (2suc x , minuend> (0<2suc {x}) refl) 
minus (2suc x) (2suc y) =  aux (minus x y)
      where
      x' = 2suc x;   y' = 2suc y

      aux :  ∃ (\d → Minus x y d) → ∃ (\d' → Minus x' y' d')

      aux (.0# , minuend< x<y refl) =  
                              (0# , minuend< (2suc-mono-< {x} {y} x<y) refl)
      aux (.0# , minuend≡ x≡y refl)  =  (0# , minuend≡ (cong 2suc x≡y) refl)
      aux (d ,   minuend> x>y x≡y+d) =  (2d , minuend> x'>y' x'≡y'+2d)
          where
          2d = 2* d;  x'>y' = 2suc-mono-< {y} {x} x>y 

          x'≡y'+2d : x' ≡ y' + 2d
          x'≡y'+2d = 
               begin≡ 2suc x             ≡⟨ cong 2suc x≡y+d ⟩
                      2suc (y + d)       ≡⟨ 2suc-as∘ (y + d) ⟩
                      2* (suc (y + d))   ≡⟨ cong 2* (sym (suc+assoc y d)) ⟩
                      2* ((suc y) + d)   ≡⟨ 2*-distrib (suc y) d ⟩
                      2* (suc y) + 2d    ≡⟨ cong (_+ 2d) (sym (2suc-as∘ y)) ⟩
                     (2suc y) + 2d
               end≡

minus (2suc x) (suc2* y) =  aux (minus x y)
  where
  -- 2(1+x) ∸ (1 + 2y) =  2 + 2x - (1 + 2y) =  1 + 2x - 2y

  x'  = 2suc x;  y' = suc2* y 
  xN = toℕ x;  yN = toℕ y;    x'N = toℕ x';   y'N = toℕ y' 

  aux :  ∃ (\d → Minus x y d) → ∃ (\d' → Minus x' y' d')

  aux (.0# , minuend< x<y refl) =  (0# , minuend< x'<y' refl)
                                   where
                                   x'<y' =  s≤s (*'-monoʳ-≤ 2 x<y)

  aux (.0# , minuend≡ x≡y refl) =  (1# , minuend> x'>y' x'≡y'+1)
             where
             x'≡y'+1 =  begin≡ 2suc x          ≡⟨ cong 2suc x≡y  ⟩
                               2suc y          ≡⟨ refl  ⟩
                               suc (suc2* y)   ≡⟨ suc≗1+ y' ⟩
                               1# + y'         ≡⟨ +-comm 1# y' ⟩
                               y' + 1# 
                        end≡

             x'>y' =  subst (y' <_) (sym x'≡y'+1) (x<x+1 y')



  aux (d , minuend> x>y x≡y+d) =  (d' , minuend> x'>y' x'≡y'+d')
      where
      d'       = suc2* d
      x'≡y'+d' =  
             sym $ 
             begin≡ (suc2* y) + (suc2* d)  ≡⟨ refl  ⟩
                    suc (suc2* (y + d))    ≡⟨ cong (suc ∘ suc2*) (sym x≡y+d) ⟩
                    suc (suc2* x)          ≡⟨ refl  ⟩ 
                    2suc x 
             end≡

      x'>y' =  begin y'        ≡[ refl ]
                     suc2* y   <[ suc2*-mono-< {y} {x} x>y ]
                     suc2* x   <[ suc2*<2suc x ]
                     2suc x    ≡[ refl ]
                     x'
               ∎

---------------
minus (suc2* x) 0#        =  (suc2* x , minuend> (0<suc2* {x}) refl) 

minus (suc2* x) (suc2* y) =  aux (minus x y)
      where
      x' = suc2* x;  y' = suc2* y

      aux :  ∃ (\d → Minus x y d) → ∃ (\d' → Minus x' y' d')

      aux (.0# , minuend< x<y refl) =  
                               (0# , minuend< (suc2*-mono-< {x} {y} x<y) refl)
      aux (.0# , minuend≡ x≡y refl) =  (0# , minuend≡ (cong suc2* x≡y) refl)

      aux (d , minuend> x>y x≡y+d) =  (2d , minuend> x'>y' x'≡y'+2d)
          where
          2d = 2* d;  x'>y' = suc2*-mono-< {y} {x} x>y 

          x'≡y'+2d : x' ≡ y' + 2d
          x'≡y'+2d = 
              begin≡ suc2* x            ≡⟨ cong suc2* x≡y+d ⟩
                     suc2* (y + d)      ≡⟨ suc2*-as∘ (y + d) ⟩
                     suc (2* (y + d))   ≡⟨ cong suc (2*-distrib y d) ⟩
                     suc (2* y + 2d)    ≡⟨ sym (suc+assoc (2* y) 2d) ⟩
                     suc (2* y) + 2d    ≡⟨ cong (_+ 2d) (sym (suc2*-as∘ y)) ⟩
                     (suc2* y) + 2d
              end≡

minus (suc2* x) (2suc y) =  aux (minus x y) 
  where
  -- res =  (1 + 2x) ∸ 2(1 + y) =  ...

  x' = suc2* x;   y' = 2suc y;   1+x = suc x;   1+y = suc y
  2x = 2* x;      2y = 2* y


  aux :  ∃ (\d → Minus x y d) → ∃ (\d' → Minus x' y' d')

  aux (.0# , minuend< x<y refl) =  (0# , minuend< x'<y' refl) 
                         where
                         x'<y' = begin suc2* x   <[ suc2*-mono-< {x} {y} x<y ] 
                                       suc2* y   <[ suc2*<2suc y ] 
                                       2suc y
                                 ∎

  aux (.0# , minuend≡ x≡y refl) =  (0# , minuend< x'<y'  refl) 
                                   where
                                   x'<y' = begin suc2* x   ≡[ cong suc2* x≡y ] 
                                                 suc2* y   <[ suc2*<2suc y ] 
                                                 2suc y
                                           ∎ 

  aux (d , minuend> x>y x≡y+d) =  (d' , minuend> x'>y' x'≡y'+d') 
      where
      2d     = 2* d;     pd  = pred d;   suc-2y   = suc 2y   
      suc-pd = suc pd;   2pd = 2* pd;    suc2*-pd = suc 2pd 

      d≢0 :  d ≢ 0# 
      d≢0 d≡0 =  <-irrefl (sym x≡y) x>y  
                 where
                 x≡y = begin≡ x        ≡⟨ x≡y+d ⟩
                              y + d    ≡⟨ cong (y +_) d≡0 ⟩
                              y + 0#   ≡⟨ +0 y ⟩
                              y
                       end≡ 

      d≡suc-pd = sym (suc∘pred d d≢0)
      d'       = suc2* pd   
      0<d'     = 0<suc2* {pd} 

      x'≡y'+d' = 
        begin≡
          suc2* x                      ≡⟨ cong suc2* x≡y+d ⟩
          suc2* (y + d)                ≡⟨ suc2*-as∘ (y + d) ⟩
          suc (2* (y + d))             ≡⟨ cong suc (2*-distrib y d) ⟩
          suc (2y + 2d)                ≡⟨ sym (suc+assoc 2y 2d) ⟩
          suc-2y + 2d                  ≡⟨ cong ((suc-2y +_) ∘ 2*) d≡suc-pd ⟩
          suc-2y + 2* (suc pd)         ≡⟨ cong (suc-2y +_) (2*≗2#* suc-pd) ⟩
          suc-2y + 2# * (suc pd)       ≡⟨ cong (suc-2y +_) (*suc 2# pd) ⟩
          suc-2y + (2# + (2# * pd))    ≡⟨ cong ((suc-2y +_) ∘ (2# +_))
                                                          (sym (2*≗2#* pd)) ⟩
          suc-2y + (2# + 2pd)          ≡⟨ refl ⟩
          suc-2y + ((1# + 1#) + 2pd)   ≡⟨ cong (suc-2y +_) (+-assoc 1# 1# 2pd)
                                        ⟩
          suc-2y + (1# + (1# + 2pd))   ≡⟨ cong ((suc-2y +_) ∘ (1# +_))
                                                          (sym (suc≗1+ 2pd)) ⟩
          suc-2y + (1# + suc2*-pd)     ≡⟨ sym (+-assoc suc-2y 1# suc2*-pd) ⟩
          (suc 2y + 1#) + suc2*-pd     ≡⟨ cong ((_+ suc2*-pd) ∘ (_+ 1#)) 
                                                                (suc≗1+ 2y) ⟩
          ((1# + 2y) + 1#) + suc2*-pd  ≡⟨ cong (_+ suc2*-pd) 
                                               ([x+y]+z≡y+[x+z] 1# 2y 1#) ⟩
          (2y + 2#) + suc2*-pd         ≡⟨ refl ⟩
          (2* y + 2* 1#) + suc2*-pd    ≡⟨ cong (_+ suc2*-pd) 
                                                   (sym (2*-distrib y 1#)) ⟩
          2* (y + 1#) + suc2*-pd       ≡⟨ cong ((_+ suc2*-pd) ∘ 2*)
                                                              (+-comm y 1#) ⟩
          2* (1# + y) + suc2*-pd       ≡⟨ cong ((_+ suc2*-pd) ∘ 2*)
                                                         (sym (suc≗1+ y)) ⟩
          2* (suc y) + suc 2pd         ≡⟨ cong₂ _+_ (sym (2suc-as∘ y))
                                                    (sym (suc2*-as∘ pd)) ⟩
          y' + d'
        end≡

      x'>y' =  begin y'        ≡[ +0 y' ]
                     y' + 0#   <[ +-monoʳ-< y' {0#} {d'} 0<d' ]
                     y' + d'   ≡[ sym x'≡y'+d' ]
                     x' 
               ∎


-------------             
infixl 6 _∸_

_∸_ : Op₂ Bin
_∸_ x =  proj₁ ∘ minus x 
         

-------------------------------------------------
x≤y←→x∸y≡0 :  {x y : Bin} → (x ≤ y ←→ x ∸ y ≡ 0#)
x≤y←→x∸y≡0 {x} {y} =
                   (to , from)
  where
  to :  x ≤ y → x ∸ y ≡ 0#
  to x≤y
     with  minus x y
  ...      | (_ , minuend< _   d≡0) =  d≡0
  ...      | (_ , minuend≡ _   d≡0) =  d≡0
  ...      | (_ , minuend> x>y _  ) =  contradiction x>y (≤⇒≯ {x} {y} x≤y)

  from :  x ∸ y ≡ 0# → x ≤ y
  from x-y≡0 = 
             aux (proj₂ res) 
       where 
       res = minus x y;   d = proj₁ res;  d≡0 = x-y≡0

       aux : Minus x y d → x ≤ y
       aux (minuend< x<y _    ) =  <⇒≤ {x} {y} x<y
       aux (minuend≡ x≡y _    ) =  ≤-reflexive x≡y
       aux (minuend> x>y x≡y+d) =  contradiction x>y (≡⇒≯ x≡y)
                                   where
                                   x≡y = begin≡ x        ≡⟨ x≡y+d ⟩
                                                y + d    ≡⟨ cong (y +_) d≡0 ⟩
                                                y + 0#   ≡⟨ +0 y ⟩
                                                y
                                         end≡

x≤y⇒x∸y≡0 :  ∀ {x y} → x ≤ y → x ∸ y ≡ 0#
x≤y⇒x∸y≡0 {x} {y} x≤y =
                      proj₁ (x≤y←→x∸y≡0 {x} {y}) x≤y

x∸y≡0⇒x≤y :  ∀ {x y} → x ∸ y ≡ 0# → x ≤ y
x∸y≡0⇒x≤y {x} {y} x∸y≡0 =
                        proj₂ (x≤y←→x∸y≡0 {x} {y}) x∸y≡0

x<y⇒0<y∸x :  ∀ {x y} → x < y → 0# < y ∸ x
x<y⇒0<y∸x {x} {y} x<y =
              case <-cmp (y ∸ x) 0#
              of \
              { (tri> _ _     gt) → gt
              ; (tri≈ _ y∸x≡0 _ ) → let y≤x = x∸y≡0⇒x≤y {y} {x} y∸x≡0
                                    in  contradiction y≤x (<⇒≱ {x} {y} x<y)
 
              ; (tri< y∸x<0 _ _ ) → contradiction y∸x<0 (≮0 (y ∸ x))
              }

x∸x :  ∀ x → x ∸ x ≡ 0#
x∸x x =
      x≤y⇒x∸y≡0 {x} {x} (≤-refl {x})

0∸ :  ∀ x → 0# ∸ x ≡ 0#
0∸ x =  x≤y⇒x∸y≡0 {0#} {x} (0≤ x)

------------------------------------------------------------------------------
[x+y]∸y≡x :  ∀ x y → (x + y) ∸ y ≡ x
[x+y]∸y≡x x y
            with  minus (x + y) y

... | (_ , minuend< x+y<0+y _  ) =  
                          contradiction 0+y≤x+y (<⇒≱ {x + y} {0# + y} x+y<0+y)
                          where
                          0+y≤x+y =  +-monoˡ-≤ y {0#} {x} (0≤ x) 

... | (d , minuend≡ x+y≡0+y d≡0) =  trans d≡0 (sym x≡0)
                                    where
                                    x≡0 : x ≡ 0#
                                    x≡0 = +-rCancel y x 0# x+y≡0+y

... | (d , minuend> 0+y<x+y x+y≡0+y+d) =  sym x≡d
                       where
                       x+y≡d+y = begin≡ x + y          ≡⟨ x+y≡0+y+d ⟩
                                        (0# + y) + d   ≡⟨ cong (_+ d) (0+ y) ⟩
                                        y + d          ≡⟨ +-comm y d ⟩
                                        d + y
                                 end≡

                       x≡d =  +-rCancel y x d x+y≡d+y

---------------------------------------
[x+y]∸x≡y :  ∀ x y → (x + y) ∸ x ≡ y
[x+y]∸x≡y x y = 
              begin≡ (x + y) ∸ x   ≡⟨ cong (_∸ x)  (+-comm x y) ⟩
                     (y + x) ∸ x   ≡⟨ [x+y]∸y≡x y x ⟩
                     y
              end≡

------------------
∸0 :  (_∸ 0#) ≗ id
∸0 x =
     begin≡ x ∸ 0#          ≡⟨ cong (_∸ 0#) (sym (+0 x)) ⟩
            (x + 0#) ∸ 0#   ≡⟨ [x+y]∸y≡x x 0# ⟩
            x
     end≡


----------------------------------------------
x+[y∸x]≡y :  ∀ {x y} → x ≤ y → x + (y ∸ x) ≡ y
x+[y∸x]≡y {x} {y} x≤y =
                      aux (minus y x)
  where
  aux :  ∃ (\d → Minus y x d) → x + (y ∸ x) ≡ y

  aux (_ , minuend< y<x _) =  contradiction y<x (≤⇒≯ {x} {y} x≤y)
  aux (_ , minuend≡ y≡x _) = 
                    begin≡ 
                      x + (y ∸ x)   ≡⟨ cong₂ _+_ (sym y≡x) (cong (_∸ x) y≡x) ⟩
                      y + (x ∸ x)   ≡⟨ cong (y +_) (x∸x x) ⟩
                      y + 0#        ≡⟨ +0 y ⟩
                      y
                    end≡

  aux (d , minuend> x<y y≡x+d) =
                    begin≡
                      x + (y ∸ x)        ≡⟨ cong ((x +_) ∘ (_∸ x)) y≡d+x ⟩
                      x + ((d + x) ∸ x)  ≡⟨ cong (x +_) ([x+y]∸y≡x d x) ⟩
                      x + d              ≡⟨ sym y≡x+d ⟩
                      y
                    end≡
                    where
                    y≡d+x = trans y≡x+d (+-comm x d)

----------------------------------------------
[x∸y]+y≡x :  ∀ {x y} → y ≤ x → (x ∸ y) + y ≡ x
[x∸y]+y≡x {x} {y} y≤x =
                      trans (+-comm (x ∸ y) y) (x+[y∸x]≡y {y} {x} y≤x)  

-------------------------
_≟_ = Bin0._≟_

pred≗∸1 :  pred ≗ (_∸ 1#)
pred≗∸1 x =
          aux (x ≟ 0#) 
          where
          px = pred x

          aux : Dec (x ≡ 0#) → pred x ≡ x ∸ 1#
          aux (yes x≡0) = 
                        begin≡ pred x     ≡⟨ cong pred x≡0 ⟩
                               pred 0#    ≡⟨ refl ⟩
                               0#         ≡⟨ refl ⟩
                               0# ∸ 1#    ≡⟨ cong (_∸ 1#) (sym x≡0) ⟩
                               x ∸ 1#
                        end≡

          aux (no x≢0) =  
              begin≡ pred x           ≡⟨ cong pred (sym (suc∘pred x x≢0)) ⟩
                     pred (suc px)    ≡⟨ pred∘suc px ⟩
                     px               ≡⟨ sym ([x+y]∸y≡x px 1#) ⟩
                     (px + 1#) ∸ 1#   ≡⟨ cong (_∸ 1#) (+-comm px 1#) ⟩
                     (1# + px) ∸ 1#   ≡⟨ cong (_∸ 1#) (sym (suc≗1+ px)) ⟩
                     (suc px) ∸ 1#    ≡⟨ cong (_∸ 1#) (suc∘pred x x≢0) ⟩
                     x ∸ 1# 
              end≡  

------------------------------------------------------------------------------
toℕ∸homo :  ∀ x y → toℕ (x ∸ y) ≡ (toℕ x) ∸' (toℕ y)
toℕ∸homo x y
           with <-cmp x y

... | tri< x<y _ _ =
                   begin≡ toℕ (x ∸ y)   ≡⟨ cong toℕ (x≤y⇒x∸y≡0 {x} {y} x≤y) ⟩
                          toℕ 0#        ≡⟨ refl ⟩
                          0             ≡⟨ sym (NatP.m≤n⇒m∸n≡0 x≤y) ⟩
                          m ∸' n
                   end≡
                   where
                   m = toℕ x;   n = toℕ y;   x≤y = <⇒≤ {x} {y} x<y

... | tri≈ _ x≡y _ =
                   begin≡ toℕ (x ∸ y)   ≡⟨ cong toℕ (x≤y⇒x∸y≡0 {x} {y} x≤y) ⟩
                          toℕ 0#        ≡⟨ refl ⟩
                          0             ≡⟨ sym (NatP.m≤n⇒m∸n≡0 x≤y) ⟩
                          m ∸' n
                   end≡
                   where
                   m = toℕ x;   n = toℕ y;   x≤y = ≤-reflexive x≡y

... | tri> _ _ y<x =
      begin≡
        toℕ (x ∸ y)                  ≡⟨ sym (NatP.m+n∸n≡m (toℕ (x ∸ y)) n) ⟩
        ((toℕ (x ∸ y)) +' n) ∸' n    ≡⟨ cong (_∸' n) eq ⟩
        ((m ∸' n) +' n) ∸' n         ≡⟨ NatP.m+n∸n≡m (m ∸' n) n ⟩
        m ∸' n
      end≡
      where
      m = toℕ x;   n = toℕ y;   y≤x = <⇒≤ {y} {x} y<x

      eq = begin≡ toℕ (x ∸ y) +' n     ≡⟨ sym (toℕ+homo (x ∸ y) y) ⟩
                  toℕ ((x ∸ y) + y)    ≡⟨ cong toℕ (+-comm (x ∸ y) y) ⟩
                  toℕ (y + (x ∸ y))    ≡⟨ cong toℕ (x+[y∸x]≡y {y} {x} y≤x) ⟩
                  m                    ≡⟨ sym (NatP.m+n∸m≡n y≤x) ⟩
                  n +' (m ∸' n)        ≡⟨ +'-comm n (m ∸' n) ⟩
                  (m ∸' n) +' n
           end≡

------------------------------------------------------------
fromℕ₁∸homo :  ∀ m n → fromℕ₁ (m ∸' n) ≡ (fromℕ₁ m) ∸ (fromℕ₁ n)
fromℕ₁∸homo m n =
       begin≡ fromℕ₁ (m ∸' n)          ≡⟨ cong fromℕ₁ (cong₂ _∸'_ m≡xN n≡yN) ⟩
              fromℕ₁ (toℕ x ∸' toℕ y)  ≡⟨ cong fromℕ₁ (sym (toℕ∸homo x y)) ⟩
              fromℕ₁ (toℕ (x ∸ y))     ≡⟨ fromℕ₁∘toℕ (x ∸ y) ⟩
              x ∸ y
       end≡
       where
       x    = fromℕ₁ m;            y    = fromℕ₁ n
       m≡xN = sym (toℕ∘fromℕ₁ m);  n≡yN = sym (toℕ∘fromℕ₁ n)

------------------------------------------------------------------------------
module FP-Bin = FuncProp (_≡_ {A = Bin})

*-lDistrib-∸ :  FP-Bin._DistributesOverˡ_ _*_ _∸_
*-lDistrib-∸ x y z =
  begin≡
    x * (y ∸ z)                    ≡⟨ sym (fromℕ₁∘toℕ (x * (y ∸ z))) ⟩
    fromℕ₁ (toℕ (x * (y ∸ z)))     ≡⟨ cong fromℕ₁ (toℕ*homo x (y ∸ z)) ⟩
    fromℕ₁ (k *' (toℕ (y ∸ z)))    ≡⟨ cong (fromℕ₁ ∘ (k *'_)) (toℕ∸homo y z) ⟩
    fromℕ₁ (k *' (m ∸' n))         ≡⟨ cong fromℕ₁ (Nat0.*-lDistrib-∸ k m n)
                                    ⟩
    fromℕ₁ ((k *' m) ∸' (k *' n))     ≡⟨ fromℕ₁∸homo (k *' m) (k *' n) ⟩
    fromℕ₁ (k *' m) ∸ fromℕ₁ (k *' n)
                              ≡⟨ cong₂ _∸_ (fromℕ₁*homo k m) (fromℕ₁*homo k n)
                               ⟩
    (fromℕ₁ k * fromℕ₁ m) ∸ (fromℕ₁ k * fromℕ₁ n)
                      ≡⟨ cong₂ _∸_ (cong₂ _*_ (fromℕ₁∘toℕ x) (fromℕ₁∘toℕ y))
                                   (cong₂ _*_ (fromℕ₁∘toℕ x) (fromℕ₁∘toℕ z)) ⟩
    x * y ∸ x * z
  end≡
  where
  k = toℕ x;  m = toℕ y;  n = toℕ z


2*-distrib-∸ :  (x y : Bin) → 2* (x ∸ y) ≡ 2* x ∸ 2* y
2*-distrib-∸ x y = 
     begin≡ 2* (x ∸ y)        ≡⟨ 2*≗2#* (x ∸ y) ⟩
            2# * (x ∸ y)      ≡⟨ *-lDistrib-∸ 2# x y ⟩
            2# * x ∸ 2# * y   ≡⟨ cong₂ _∸_ (sym (2*≗2#* x)) (sym (2*≗2#* y)) ⟩
            2* x ∸ 2* y
     end≡

-----------------------------------------------------------
+-∸-comm :  ∀ {x} y {o} → o ≤ x → (x + y) ∸ o ≡ (x ∸ o) + y
+-∸-comm {x} y {o} o≤x =
  begin≡
    (x + y) ∸ o                  ≡⟨ sym (fromℕ₁∘toℕ ((x + y) ∸ o)) ⟩
    fromℕ₁ (toℕ ((x + y) ∸ o))   ≡⟨ cong fromℕ₁ (toℕ∸homo (x + y) o) ⟩
    fromℕ₁ (toℕ (x + y) ∸' n)    ≡⟨ cong (fromℕ₁ ∘ (_∸' n)) (toℕ+homo x y) ⟩
    fromℕ₁ ((k +' m) ∸' n)       ≡⟨ cong fromℕ₁ (NatP.+-∸-comm m o≤x) ⟩
    fromℕ₁ ((k ∸' n) +' m)       ≡⟨ fromℕ₁+homo (k ∸' n) m ⟩
    fromℕ₁ (k ∸' n) + fromℕ₁ m   ≡⟨ cong ((fromℕ₁ (k ∸' n)) +_)
                                                            (fromℕ₁∘toℕ y) ⟩
    fromℕ₁ (k ∸' n) + y         ≡⟨ cong (_+ y) (fromℕ₁∸homo k n) ⟩
    (fromℕ₁ k ∸ fromℕ₁ n) + y   ≡⟨ cong (_+ y)
                                   (cong₂ _∸_ (fromℕ₁∘toℕ x) (fromℕ₁∘toℕ o)) ⟩
    (x ∸ o) + y
  end≡
  where
  k = toℕ x;   m = toℕ y;   n = toℕ o


------------------------------------------------
∸-+-assoc :  ∀ x y o → (x ∸ y) ∸ o ≡ x ∸ (y + o)
∸-+-assoc x y o =
  begin≡
    (x ∸ y) ∸ o                    ≡⟨ sym (fromℕ₁∘toℕ ((x ∸ y) ∸ o)) ⟩
    fromℕ₁ (toℕ ((x ∸ y) ∸ o))     ≡⟨ cong fromℕ₁ (toℕ∸homo (x ∸ y) o) ⟩
    fromℕ₁ (toℕ (x ∸ y) ∸' n)      ≡⟨ cong (fromℕ₁ ∘ (_∸' n)) (toℕ∸homo x y) ⟩
    fromℕ₁ ((k ∸' m) ∸' n)         ≡⟨ cong fromℕ₁ (NatP.∸-+-assoc k m n) ⟩
    fromℕ₁ (k ∸' (m +' n))         ≡⟨ fromℕ₁∸homo k (m +' n) ⟩
    fromℕ₁ k ∸ fromℕ₁ (m +' n)     ≡⟨ cong ((fromℕ₁ k) ∸_) (fromℕ₁+homo m n) ⟩
    fromℕ₁ k ∸ (fromℕ₁ m + fromℕ₁ n)
                                   ≡⟨ cong ((fromℕ₁ k) ∸_)
                                      (cong₂ _+_ (fromℕ₁∘toℕ y) (fromℕ₁∘toℕ o))
                                    ⟩
    fromℕ₁ k ∸ (y + o)             ≡⟨ cong (_∸ (y + o)) (fromℕ₁∘toℕ x) ⟩
    x ∸ (y + o)
  end≡
  where
  k = toℕ x;  m = toℕ y;  n = toℕ o

----------------------------------------------------------
+-∸-assoc :  ∀ x {y o} → o ≤ y → (x + y) ∸ o ≡ x + (y ∸ o)
+-∸-assoc x {y} {o} o≤y =
  begin≡
    (x + y) ∸ o                   ≡⟨ sym (fromℕ₁∘toℕ ((x + y) ∸ o)) ⟩
    fromℕ₁ (toℕ ((x + y) ∸ o))    ≡⟨ cong fromℕ₁ (toℕ∸homo (x + y) o) ⟩
    fromℕ₁ (toℕ (x + y) ∸' n)     ≡⟨ cong (fromℕ₁ ∘ (_∸' n)) (toℕ+homo x y) ⟩
    fromℕ₁ ((k +' m) ∸' n)        ≡⟨ cong fromℕ₁ (NatP.+-∸-assoc k o≤y) ⟩
    fromℕ₁ (k +' (m ∸' n))        ≡⟨ fromℕ₁+homo k (m ∸' n) ⟩
    fromℕ₁ k + fromℕ₁ (m ∸' n)    ≡⟨ cong (_+ (fromℕ₁ (m ∸' n)))
                                                            (fromℕ₁∘toℕ x) ⟩
    x + fromℕ₁ (m ∸' n)          ≡⟨ cong (x +_) (fromℕ₁∸homo m n) ⟩
    x + (fromℕ₁ m ∸ fromℕ₁ n)    ≡⟨ cong (x +_)
                                     (cong₂ _∸_ (fromℕ₁∘toℕ y) (fromℕ₁∘toℕ o))
                                  ⟩
    x + (y ∸ o)
  end≡
  where
  k = toℕ x;  m = toℕ y;  n = toℕ o



------------------------------------------
∸-mono-≤ :  _∸_ Preserves₂ _≤_ ⟶ _≥_ ⟶ _≤_
∸-mono-≤ {x} {x'} {y} {y'} x≤x' y'≤y =
    begin
      x ∸ y                     ≡[ sym (fromℕ₁∘toℕ (x ∸ y)) ]
      fromℕ₁ (toℕ (x ∸ y))      ≡[ cong fromℕ₁ (toℕ∸homo x y) ]
      fromℕ₁ (xN ∸' yN)         ≤[ fromℕ₁-mono-≤ (∸'-mono x≤x' y'≤y) ]
      fromℕ₁ (x'N ∸' y'N)       ≡[ fromℕ₁∸homo x'N y'N ]
      fromℕ₁ x'N ∸ fromℕ₁ y'N   ≡[ cong₂ _∸_ (fromℕ₁∘toℕ x') (fromℕ₁∘toℕ y') ]
      x' ∸ y'
    ∎
    where  
    xN = toℕ x;  yN = toℕ y;  x'N = toℕ x';  y'N = toℕ y'


∸-monoˡ-≤ :  (x : Bin) → (_∸ x) Preserves _≤_ ⟶ _≤_
∸-monoˡ-≤ x {y} {z} y≤z =
                        ∸-mono-≤ {y} {z} {x} {x} y≤z (≤-refl {x}) 

--------------------------
x∸y≤x :  ∀ x y → x ∸ y ≤ x
x∸y≤x x y =
          begin x ∸ y    ≤[ ∸-mono-≤ {x} {x} {y} {0#} (≤-refl {x}) (0≤ y) ]
                x ∸ 0#   ≡[ ∸0 x ]
                x
          ∎

------------------------------------------
suc2*-x≢2y :  (x y : Bin) → suc2* x ≢ 2* y     -- "odd is not even"
suc2*-x≢2y x y suc2*x≡2y =
                         aux (x <? y) 
  where
  2x = 2* x;   2y = 2* y;   2y≤suc2*x = ≤-reflexive (sym (suc2*x≡2y))
  suc2*x≤2y = ≤-reflexive suc2*x≡2y

  2x+1≡suc2*-x =  begin≡ 2x + 1#    ≡⟨ +-comm 2x 1# ⟩
                         1# + 2x    ≡⟨ sym (suc≗1+ 2x) ⟩
                         suc 2x     ≡⟨ sym (suc2*-as∘ x) ⟩
                         suc2* x 
                  end≡

  aux : Dec (x < y) → ⊥

  aux (yes x<y) =  2*≢1 2[y∸x]≡1
    where
    2x<2y = 2*-mono-< {x} {y} x<y

    2y∸2x≢0 : 2y ∸ 2x ≢ 0#
    2y∸2x≢0 2y∸2x≡0 =  <⇒≱ {2x} {2y} 2x<2y 2y≤2x 
                       where
                       2y≤2x = x∸y≡0⇒x≤y {2y} {2x} 2y∸2x≡0 
    2[y∸x]≡1 =
      begin≡
        2* (y ∸ x)             ≡⟨ 2*-distrib-∸ y x ⟩          
        2y ∸ 2x                ≡⟨ sym (suc∘pred (2y ∸ 2x) 2y∸2x≢0) ⟩  
        suc (pred (2y ∸ 2x))   ≡⟨ cong suc (pred≗∸1 (2y ∸ 2x)) ⟩  
        suc ((2y ∸ 2x) ∸ 1#)   ≡⟨ cong suc (∸-+-assoc 2y 2x 1#) ⟩  
        suc (2y ∸ (2x + 1#))   ≡⟨ cong (suc ∘ (2y ∸_)) 2x+1≡suc2*-x ⟩
        suc (2y ∸ (suc2* x))   ≡⟨ cong suc 
                                       (x≤y⇒x∸y≡0 {2y} {suc2* x} 2y≤suc2*x) ⟩
        1#
     end≡

  aux (no x≮y) =  suc≢0 $  
                  begin≡  
                    suc (2x ∸ 2y)     ≡⟨ suc≗1+ (2x ∸ 2y) ⟩
                    1# + (2x ∸ 2y)    ≡⟨ sym (+-∸-assoc 1# {2x} {2y} 2y≤2x) ⟩
                   (1# + 2x) ∸ 2y    ≡⟨ cong (_∸ 2y) (sym (suc≗1+ 2x)) ⟩
                   (suc 2x) ∸ 2y     ≡⟨ cong (_∸ 2y) (sym (suc2*-as∘ x)) ⟩
                   (suc2* x) ∸ 2y    ≡⟨ x≤y⇒x∸y≡0 {suc2* x} {2y} suc2*x≤2y ⟩ 
                    0#
                  end≡  
                  where
                  y≤x = ≮⇒≥ {x} {y} x≮y;    2y≤2x = 2*-mono-≤ {y} {x} y≤x

------------------------------------------------------------------------------
*-lCancel :  (x y z : Bin) → x ≢ 0# → x * y ≡ x * z → y ≡ z
*-lCancel x y z x≢0 xy≡xz =
                          ≤-antisym y≤z z≤y
   where
   xy    = x * y;               xz    = x * z  
   xy≤xz = ≤-reflexive xy≡xz;   xz≤xy = ≤-reflexive (sym xy≡xz)

   eq  = begin≡ x * (y ∸ z)   ≡⟨ *-lDistrib-∸ x y z ⟩
                xy ∸ xz       ≡⟨ x≤y⇒x∸y≡0 {xy} {xz} xy≤xz ⟩
                0#
         end≡
   eq' = begin≡ x * (z ∸ y)   ≡⟨ *-lDistrib-∸ x z y ⟩
                xz ∸ xy       ≡⟨ x≤y⇒x∸y≡0 {xz} {xy} xz≤xy ⟩
                0#
         end≡

   y≤z = case  x*y≡0⇒⊎ eq   of \ { (inj₁ x≡0)   → contradiction x≡0 x≢0
                                 ; (inj₂ y∸z≡0) → x∸y≡0⇒x≤y {y} {z} y∸z≡0
                                 }
   z≤y = case  x*y≡0⇒⊎ eq'  of \ { (inj₁ x≡0)   → contradiction x≡0 x≢0
                                 ; (inj₂ z∸y≡0) → x∸y≡0⇒x≤y {z} {y} z∸y≡0
                                 }

----------------------------
2*-injective :  Injective 2* 
2*-injective {x} {y} 2x≡2y =  *-lCancel 2# x y 2suc≢0 2#x≡2#y
                              where
                              2#x≡2#y = begin≡ 2# * x   ≡⟨ sym (2*≗2#* x) ⟩
                                               2* x     ≡⟨ 2x≡2y ⟩
                                               2* y     ≡⟨ 2*≗2#* y ⟩
                                               2# * y
                                        end≡ 

