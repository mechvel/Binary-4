{-
This file is a part of the library  Binary-4.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.

Binary-4  is free software: you can redistribute it and/or modify it
under the terms of the GNU General Public License.
See  license.txt.
-}

module Ord0 where

open import Level    using () renaming (zero to 0ℓ)
open import Function using (id; _∘_; flip; _on_; case_of_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using 
            (Rel; Reflexive; Symmetric; Antisymmetric; Transitive; 
             Irreflexive; Tri; _⇒_; _Preserves_⟶_; _Preserves₂_⟶_⟶_
            )
            renaming (Decidable to Decidable₂)

open import Relation.Binary.PropositionalEquality as PE 
                     using (_≡_; _≢_; _≗_; refl; sym; cong; subst; subst₂
                           )
open PE.≡-Reasoning renaming (begin_ to begin≡_; _∎ to _end≡)
open import Data.Sum        using (_⊎_; inj₁; inj₂)
open import Data.Product    using (_,_)
open import Data.List       using (List; []; _∷_; [_])  
open import Data.Nat as Nat using (ℕ; z≤n; s≤s)
     renaming (suc to 1+_; pred to pred'; _+_ to _+'_; _*_ to _*'_; 
               _∸_ to _∸'_; _<_ to _<'_; _≤_ to _≤'_; _>_ to _>'_
              )
open import Data.Nat.Properties as NatP using (n≤1+n; m≤m+n; m+n∸m≡n; m+n∸n≡m)
     renaming (+-comm to +'-comm; +-assoc to +'-assoc; <-irrefl to <'-irrefl;
               *-distribˡ-+ to *'-lDistrib; <-trans to <'-trans;
               ≤-refl to ≤'-refl ;≤-trans to ≤'-trans; <⇒≤ to <'⇒≤;
               ≤-reflexive to ≤'-reflexive; ≤-antisym to ≤'-antisym; 
               +-monoʳ-< to +'-monoʳ-<; +-monoʳ-≤ to +'-monoʳ-≤; 
               +-mono-≤ to +'-mono-≤;   +-mono-<-≤ to +'-mono-<-≤;
               *-mono-≤ to *'-mono-≤;   *-monoʳ-≤ to *'-monoʳ-≤;
               *-mono-< to *'-mono-<;   *-monoʳ-< to *'-monoʳ-<;
               module ≤-Reasoning to ≤'-Reasoning
              )
open ≤'-Reasoning using () renaming (begin_ to ≤'begin_; _∎ to _≤'end;
                                    _≡⟨_⟩_ to _≡≤'[_]_; _≤⟨_⟩_ to _≤'[_]_)

open import LtReasoning using (module InequalityReasoning)  -- by U. Norell

-- of application ---
open import BPrelude using (≢sym; Injective)
import Nat0 
open import Bin0 using 
     (Bin; _≟_; 1#; 2#; suc; pred; 2*; 2*'_; toℕ; fromℕ₁; fromℕ; _+_; _*_; 2^; 
      suc≢0; toℕ-injective; suc≗1+; toℕ∘suc; suc∘pred; pred∘suc; toℕ∘pred; 
      toℕ+homo; +-comm; +-assoc; 2suc-as∘; suc2*-as∘; 0+
     )
open import Bin1 using (toℕ*homo; lDistrib; rDistrib; 2*≗2#*; *1; 1*; 2^≢0; 
                        2x≡x+x; suc*; *[1+x]; 2*-*-assoc; *-comm; 2^-homo)




--****************************************************************************
open Bin 


-- Order relation ------------------------------------------------------------

infix 4 _<_ _>_ _≤_

_≤_ _≥_ _<_ _>_ _≮_ _≯_ _≰_ _≱_    :  Rel Bin 0ℓ     

_≤_ =  _≤'_ on toℕ   -- _≤_ and _⟨_  are induced from ℕ,  
_<_ =  _<'_ on toℕ   -- and this makes toℕ monotone automatically.  
_>_ = flip _<_
_≥_ = flip _≤_

_≮_ x =  ¬_ ∘ _<_ x
_≯_ x =  ¬_ ∘ _>_ x
_≰_ x =  ¬_ ∘ _≤_ x
_≱_ x =  ¬_ ∘ _≥_ x


≤-refl : Reflexive _≤_ 
≤-refl = ≤'-refl

≤-reflexive : _≡_ ⇒ _≤_ 
≤-reflexive {x} {_} refl =  ≤-refl {x} 

≤-trans : Transitive _≤_ 
≤-trans {x} {y} {z} xN≤yN yN≤zN =  ≤'-trans xN≤yN yN≤zN 

≤-antisym : Antisymmetric _≡_ _≤_ 
≤-antisym xN≤yN yN≤xN = 
                      toℕ-injective xN≡yN
                      where
                      xN≡yN = ≤'-antisym xN≤yN yN≤xN 

<-trans : Transitive _<_ 
<-trans {x} {y} {z} xN<yN yN<zN =  <'-trans xN<yN yN<zN 

<-irrefl :  Irreflexive _≡_ _<_
<-irrefl {x} refl =  
                  <'-irrefl refl 

<⇒≯ : _<_ ⇒ _≯_
<⇒≯ {x} {y} x<y y<x =  <'-irrefl refl (<-trans {x} {y} {x} x<y y<x) 

>⇒≮ : _>_ ⇒ _≮_
>⇒≮ {x} {y} y<x =  <⇒≯ {y} {x} y<x

<⇒≢ : _<_ ⇒ _≢_
<⇒≢ {x} {_} x<y x≡y =  <-irrefl {x} {x} refl x<x 
                       where
                       x<x = subst (x <_) (sym x≡y) x<y

>⇒≢ : _>_ ⇒ _≢_
>⇒≢ {_} {_} y<x =  ≢sym (<⇒≢ y<x) 

≡⇒≮ : _≡_ ⇒ _≮_
≡⇒≮ x≡y x<y =  <⇒≢ x<y x≡y

≡⇒≯ : _≡_ ⇒ _≯_
≡⇒≯ x≡y x>y =  >⇒≢ x>y x≡y

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ = <'⇒≤

≤→≢→< :  {x y : Bin} → x ≤ y → x ≢ y → x < y 
≤→≢→< x≤y x≢y =
              NatP.≤+≢⇒< x≤y xN≢yN
              where
              xN≢yN =  x≢y ∘ toℕ-injective

≮0 :  (x : Bin) → x ≮ 0#
≮0 _ () 

0<2suc :  {x : Bin} → 0# < 2suc x
0<2suc {x} = 
           ≤'begin 1+ 0            ≤'[ s≤s z≤n ]
                   2               ≤'[ m≤m+n 2 (2*' n) ]
                   2 +' (2*' n)   ≡≤'[ sym (*'-lDistrib 2 1 n) ]
                   2 *' (1+ n)
           ≤'end 
           where n = toℕ x

0<suc2* :  {x : Bin} → 0# < suc2* x
0<suc2* {x} =  s≤s z≤n

0≤ :  (x : Bin) → 0# ≤ x
0≤ 0#        =  ≤-refl {0#}
0≤ (2suc x)  =  <⇒≤ {0#} {2suc x}  (0<2suc {x})
0≤ (suc2* x) =  <⇒≤ {0#} {suc2* x} (0<suc2* {x})

≢0⇒> :  {x : Bin} → x ≢ 0# → x > 0#

≢0⇒> {0#}      0≢0 =  contradiction refl 0≢0
≢0⇒> {2suc x}  _   =  0<2suc {x}
≢0⇒> {suc2* x} _   =  0<suc2* {x}

≤0⇒≡ :  {x : Bin} → x ≤ 0# → x ≡ 0#
≤0⇒≡ {x} x≤0 = 
             ≤-antisym x≤0 (0≤ x)

0<suc :  (x : Bin) → 0# < suc x
0<suc x = 
        ≢0⇒> (suc≢0 {x}) 

2suc-mono-< :  {x y : Bin} → x < y → 2suc x < 2suc y
2suc-mono-< =  *'-monoʳ-< 1 ∘ s≤s

suc2*-mono-< :  {x y : Bin} → x < y → suc2* x < suc2* y
suc2*-mono-< =  s≤s ∘ *'-monoʳ-< 1

--------------------------------------------
suc-x≤⇒x< :  {x y : Bin} → suc x ≤ y → x < y
suc-x≤⇒x< {x} {y} suc-x≤y = 
                          ≤'begin 1+ (toℕ x)   ≡≤'[ sym (toℕ∘suc x) ]
                                  toℕ (suc x)   ≤'[ suc-x≤y ]
                                  toℕ y
                          ≤'end

x<⇒suc-x≤ :  {x y : Bin} → x < y → suc x ≤ y
x<⇒suc-x≤ {x} {y} x<y = 
                      ≤'begin toℕ (suc x)   ≡≤'[ toℕ∘suc x ]
                              1+ (toℕ x)     ≤'[ x<y ]
                              toℕ y
                      ≤'end

private
  -- of arithmetic on ℕ
  k≤m→2+2k≤2[1+m] :  {k m l : ℕ} → k ≤' m → l +' l *' k ≤' l *' (1+ m)
  k≤m→2+2k≤2[1+m] {k} {m} {l} k≤m = 
            ≤'begin 
              l +' l *' k       ≡≤'[ cong (_+' (l *' k)) (sym (Nat0.*1 l)) ] 
              l *' 1 +' l *' k  ≡≤'[ sym (*'-lDistrib l 1 k) ] 
              l *' (1+ k)        ≤'[ *'-monoʳ-≤ l (s≤s k≤m) ] 
              l *' (1+ m)
            ≤'end

open Tri

------------------------------------------------------------------------------
<-cmp :  (x y : Bin) → Tri (x < y) (x ≡ y) (x > y)

-- It uses toℕ for proofs. It is fast in computing the proper result but can
-- be very expensive in computing the full structure of proofs.

<-cmp 0# 0#        =  tri≈ (≮0 0#) refl (≮0 0#)
<-cmp 0# (2suc x)  =  tri< lt (<⇒≢ {0#} {x'} lt) (<⇒≯ {0#} {x'} lt)
                      where
                      x' = 2suc x;  lt = 0<2suc {x}

<-cmp 0# (suc2* x) =  tri< lt (<⇒≢ {0#} {x'} lt) (<⇒≯ {0#} {x'} lt)
                      where
                      x' = suc2* x;  lt = 0<suc2* {x}

---------------
<-cmp (2suc x) 0#       =  tri> (<⇒≯ {0#} {x'} lt) (>⇒≢ {x'} {0#} lt) lt
                           where
                           x' = 2suc x;  lt = 0<2suc {x}

<-cmp (2suc x) (2suc y) =  aux (<-cmp x y)
      where
      xN = toℕ x;  yN = toℕ y;   x' = 2suc x;  y' = 2suc y  
  
      aux : Tri (x < y) (x ≡ y) (x > y) → Tri (x' < y') (x' ≡ y') (x' > y')

      aux (tri< x<y _ _) =  tri< x'<y' (<⇒≢ x'<y') (<⇒≯ {x'} {y'} x'<y') 
                            where
                            x'<y' = 2suc-mono-< {x} {y} x<y

      aux (tri≈ _ x≡y _) =  tri≈ (≡⇒≮ x'≡y') x'≡y' (≡⇒≯ x'≡y') 
                            where
                            x'≡y' =  cong 2suc x≡y 

      aux (tri> _ _ x>y) =  tri> (>⇒≮ {x'} {y'} x'>y') (>⇒≢ x'>y') x'>y' 
                            where
                            x'>y' = 2suc-mono-< {y} {x} x>y

<-cmp (2suc x) (suc2* y) =  aux (<-cmp x y)
  where
  xN = toℕ x;  yN = toℕ y;   x' = 2suc x;  y' = suc2* y  

  aux : Tri (x < y) (x ≡ y) (x > y) → Tri (x' < y') (x' ≡ y') (x' > y')

  aux (tri≈ _ x≡y _) =  tri> (>⇒≮ {x'} {y'} gt) (>⇒≢ gt) gt   -- 2(1+x) > 1+2x
                        where
                        yN≤xN = ≤'-reflexive (cong toℕ (sym x≡y))

                        gt :  2*' (1+ xN) >' 1+ (2*' yN)
                        gt =  k≤m→2+2k≤2[1+m] {l = 2} yN≤xN
     
  aux (tri> _ _ x>y) =  tri> (>⇒≮ {x'} {y'} gt) (>⇒≢ gt) gt   -- 2(1+x) > 1+2y
      where
      yN≤xN = <⇒≤ {y} {x} x>y

      gt :  2*' (1+ xN) >' 1+ (2*' yN)
      gt =  ≤'begin 
              1+ (1+ (2*' yN))   ≡≤'[ refl ]
              2 +' (2*' yN)       ≤'[ +'-monoʳ-≤ 2 (*'-monoʳ-≤ 2 yN≤xN) ]
              2 +' (2*' xN)      ≡≤'[ sym (*'-lDistrib 2 1 xN) ]
              2*' (1+ xN)
            ≤'end
        
  aux (tri< x<y _ _) =  tri< lt (<⇒≢ lt) (<⇒≯ {x'} {y'} lt)  -- 2(1+x) < 1+2y 
                        where
                        lt :  2*' (1+ xN) <' 1+ (2*' yN)
                        lt =  s≤s (*'-monoʳ-≤ 2 x<y)

---------------
<-cmp (suc2* x) 0# =  tri> (>⇒≮ {x'} {0#} gt) (>⇒≢ {x'} {0#} gt) gt
                      where
                      x' = suc2* x;  gt = 0<suc2* {x}


<-cmp (suc2* x) (2suc y) =  aux (<-cmp x y)
  where
  xN = toℕ x;  yN = toℕ y;   x' = suc2* x;  y' = 2suc y  

  aux : Tri (x < y) (x ≡ y) (x > y) → Tri (x' < y') (x' ≡ y') (x' > y')

  aux (tri< x<y _ _) =  tri< lt (<⇒≢ lt) (<⇒≯ {x'} {y'} lt)  -- 1+2x < 2(1+y)
                        where
                        x≤y = <⇒≤ {x} {y} x<y

                        lt :  1+ (2*' xN) <' 2*' (1+ yN)
                        lt =  k≤m→2+2k≤2[1+m] {l = 2} x≤y

  aux (tri≈ _ x≡y _) =  tri< lt (<⇒≢ lt) (<⇒≯ {x'} {y'} lt)  -- 1+2x < 2(1+x)
                        where
                        xN≤yN = ≤'-reflexive (cong toℕ x≡y)

                        lt :  1+ (2*' xN) <' 2*' (1+ yN)
                        lt =  k≤m→2+2k≤2[1+m] {l = 2} xN≤yN

  aux (tri> _ x≢y x>y) =  tri> (>⇒≮ {x'} {y'} gt) (>⇒≢ gt) gt  
                          where                               -- 1+2x > 2(1+y)
                          gt :  1+ (2*' xN) >' 2*' (1+ yN)
                          gt =  s≤s (*'-monoʳ-≤ 2 x>y)


<-cmp (suc2* x) (suc2* y) =  aux (<-cmp x y)
  where
  x' = suc2* x;  y' = suc2* y;  xN = toℕ x;  yN = toℕ y
  
  aux : Tri (x < y) (x ≡ y) (x > y) → Tri (x' < y') (x' ≡ y') (x' > y')

  aux (tri< x<y _ _) =  tri< x'<y' (<⇒≢ x'<y') (<⇒≯ {x'} {y'} x'<y') 
                        where
                        x'<y' = suc2*-mono-< {x} {y} x<y 

  aux (tri≈ _ x≡y _) =  tri≈ (≡⇒≮ x'≡y') x'≡y' (≡⇒≯ x'≡y')
                        where
                        x'≡y' = cong suc2* x≡y

  aux (tri> _ _ x>y) =  tri> (>⇒≮ {x'} {y'} x'>y') (>⇒≢ x'>y') x'>y'
                        where
                        x'>y' =  suc2*-mono-< {y} {x} x>y 

------------------------------------------------------------------------------
≤⇒⊎ :  {x y : Bin} → x ≤ y → x < y ⊎ x ≡ y
≤⇒⊎ {x} {y} x≤y 
            with <-cmp x y
... | tri< lt _  _   = inj₁ lt
... | tri≈ _  eq _   = inj₂ eq
... | tri> _  _  y<x = contradiction x≤y (NatP.<⇒≱ y<x) 

<⇒≱ :  _<_ ⇒ _≱_
<⇒≱ {x} {y} x<y x≥y = case  ≤⇒⊎ {y} {x} x≥y  of \ 
                                           { (inj₁ y<x) → <⇒≯ {x} {y} x<y y<x
                                           ; (inj₂ y≡x) → <⇒≢ x<y (sym y≡x) }
≤⇒≯ :  _≤_ ⇒ _≯_
≤⇒≯ {x} {y} x≤y x>y =  <⇒≱ {y} {x} x>y x≤y  

≮⇒≥ :  _≮_ ⇒ _≥_
≮⇒≥ {x} {y} x≮y 
            with <-cmp x y
... | tri< lt _  _   =  contradiction lt x≮y 
... | tri≈ _  eq _   =  ≤-reflexive (sym eq)
... | tri> _  _  y<x =  <⇒≤ {y} {x} y<x 

≰⇒> :  _≰_ ⇒ _>_
≰⇒> {x} {y} x≰y  
            with <-cmp x y
... | tri< lt _  _   =  contradiction (<⇒≤ {x} {y} lt) x≰y 
... | tri≈ _  eq _   =  contradiction (≤-reflexive eq) x≰y 
... | tri> _  _  x>y =  x>y


≤,≢⇒< :  {x y : Bin} → x ≤ y → x ≢ y → x < y
≤,≢⇒< x≤y x≢y = 
              case ≤⇒⊎ x≤y of \ { (inj₁ x<y) → x<y
                                ; (inj₂ x≡y) → contradiction x≡y x≢y
                                }

<-≤-trans :  {x y z : Bin} → x < y → y ≤ z → x < z
<-≤-trans {x} {y} {z} x<y y≤z =  
                              case  ≤⇒⊎ {y} {z} y≤z  
                              of \ 
                              { (inj₁ y<z) → <-trans {x} {y} {z} x<y y<z 
                              ; (inj₂ y≡z) → subst (x <_) y≡z x<y }

≤-<-trans :  {x y z : Bin} → x ≤ y → y < z → x < z
≤-<-trans {x} {y} {z} x≤y y<z = 
                              case  ≤⇒⊎ {x} {y} x≤y  
                              of \ 
                              { (inj₁ x<y) → <-trans {x} {y} {z} x<y y<z 
                              ; (inj₂ x≡y) → subst (_< z) (sym x≡y) y<z }

≡0-by≤ :  {x y : Bin} → x ≤ y → y ≡ 0# → x ≡ 0#
≡0-by≤ {x} {y} x≤y y≡0 = 
                       ≤0⇒≡ x≤0   where
                                  x≤0 = subst (x ≤_) y≡0 x≤y

≢0-by≤ :  {x y : Bin} → x ≤ y → x ≢ 0# → y ≢ 0#
≢0-by≤ x≤y x≢0 =
               x≢0 ∘ ≡0-by≤ x≤y

_<?_ : Decidable₂ _<_
x <? y 
     with <-cmp x y
... | tri< lt  _ _ =  yes lt
... | tri≈ ¬lt _ _ =  no ¬lt
... | tri> ¬lt _ _ =  no ¬lt

_≤?_ : Decidable₂ _≤_
x ≤? y 
     with <-cmp x y
... | tri< lt _  _  =  yes (<⇒≤ {x} {y} lt)
... | tri≈ _  eq _  =  yes (≤-reflexive eq)
... | tri> _  _  gt =  no (<⇒≱ {y} {x} gt)
       


open InequalityReasoning {A = Bin} _<_ _≤_
                                   (\{x y}   → ≤-reflexive {x} {y})
                                   (\{x y z} → <-trans   {x} {y} {z})
                                   (\{x y z} → ≤-trans   {x} {y} {z})
                                   (\{x y z} → <-≤-trans {x} {y} {z})
                                   (\{x y z} → ≤-<-trans {x} {y} {z})


--============================================================================
fromℕ₁-mono-≤ :  fromℕ₁ Preserves _≤'_ ⟶ _≤_
fromℕ₁-mono-≤ {m} {n} m≤n =
                      let (x , toℕ-x≡m) = fromℕ m;   (y , toℕ-y≡n) = fromℕ n
                      in
                      subst₂ _≤'_ (sym toℕ-x≡m) (sym toℕ-y≡n) m≤n

------------------------------------------
+-mono-≤ :  _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_

+-mono-≤ {x} {x'} {y} {y'} x≤x' y≤y' = 
  ≤'begin
    toℕ (x + y)     ≡≤'[ toℕ+homo x y ]
    m +' n           ≤'[ +'-mono-≤ {m} {m'} {n} {n'} x≤x' y≤y' ]
    m' +' n'        ≡≤'[ sym (toℕ+homo x' y') ]
    toℕ (x' + y')
  ≤'end 
  where
  m = toℕ x;  n = toℕ y;  m' = toℕ x';  n' = toℕ y' 

---------------------------------------------------
+-monoˡ-≤ :  (x : Bin) → (_+ x) Preserves _≤_ ⟶ _≤_
+-monoˡ-≤ x {y} {z} y≤z = 
                        +-mono-≤ {y} {z} {x} {x} y≤z (≤-refl {x}) 

+-monoʳ-≤ :  (x : Bin) → (x +_) Preserves _≤_ ⟶ _≤_
+-monoʳ-≤ x {y} {z} y≤z = 
                        +-mono-≤ {x} {x} {y} {z} (≤-refl {x}) y≤z


--------------------------------------------
+-mono-<-≤ :  _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_

+-mono-<-≤ {x} {x'} {y} {y'} x<x' y≤y' =  toℕ[x+y]<toℕ[x'+y']
      where
      m = toℕ x;  n = toℕ y;  m' = toℕ x';  n' = toℕ y' 

      m+n<m'+n' =  +'-mono-<-≤ {m} {m'} {n} {n'} x<x' y≤y'

      toℕ[x+y]≡m+n = toℕ+homo x y;  toℕ[x'+y']≡m'+n' = toℕ+homo x' y'

      toℕ[x+y]<toℕ[x'+y'] = subst₂ _<'_ (sym toℕ[x+y]≡m+n)
                                        (sym toℕ[x'+y']≡m'+n') m+n<m'+n'

--------------------------------------------
+-mono-≤-< :  _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_

+-mono-≤-< {x} {x'} {y} {y'} x≤x' y<y' =
                        subst₂ _<_ (+-comm y x) (+-comm y' x') y+x<y'+x'
                        where
                        y+x<y'+x' =  +-mono-<-≤ {y} {y'} {x} {x'} y<y' x≤x'

+-monoˡ-< :  (x : Bin) → (_+ x) Preserves _<_ ⟶ _<_
+-monoˡ-< x {y} {z} y<z = 
                        +-mono-<-≤ {y} {z} {x} {x} y<z (≤-refl {x}) 

+-monoʳ-< :  (x : Bin) → (x +_) Preserves _<_ ⟶ _<_
+-monoʳ-< x {y} {z} y<z = 
                        +-mono-≤-< {x} {x} {y} {z} (≤-refl {x}) y<z 

suc-mono-≤ :  suc Preserves _≤_ ⟶ _≤_
suc-mono-≤ {x} {y} x≤y =  
                       begin suc x     ≡[ suc≗1+ x ]
                             1# + x    ≤[ +-monoʳ-≤ 1# {x} {y} x≤y ] 
                             1# + y    ≡[ sym (suc≗1+ y) ]
                             suc y
                       ∎

x≤y+x :  (x y : Bin) → x ≤ y + x
x≤y+x x y = 
          begin x        ≡[ sym (0+ x) ]
                0# + x   ≤[ +-monoˡ-≤ x {0#} {y} (0≤ y) ]
                y + x
          ∎         

x≤x+y :  (x y : Bin) → x ≤ x + y
x≤x+y x y = 
          begin x        ≤[ x≤y+x x y ]
                y + x    ≡[ +-comm y x ]
                x + y
          ∎

x<1+x :  (x : Bin) → x < 1# + x
x<1+x x = 
        begin x         ≡[ refl ]
              0# + x    <[ +-monoˡ-< x {0#} {1#} (Nat0.n<1+n {0}) ]  
              1# + x
        ∎

x<suc-x :  (x : Bin) → x < suc x
x<suc-x x = 
          begin x        <[ x<1+x x ] 
                1# + x   ≡[ sym (suc≗1+ x) ] 
                suc x
          ∎

x<x+1 :  (x : Bin) → x < x + 1#
x<x+1 x =
        begin x         <[ x<1+x x ] 
              1# + x    ≡[ +-comm 1# x ] 
              x + 1#
        ∎ 

x≤suc-x :  (x : Bin) → x ≤ suc x
x≤suc-x x = 
          <⇒≤ {x} {suc x} (x<suc-x x)

x≢suc-x :  (x : Bin) → x ≢ suc x
x≢suc-x =  <⇒≢ ∘ x<suc-x

pred-x<x :  {x : Bin} → x ≢ 0# → pred x < x
pred-x<x {x} x≢0 = 
                 begin pred x         <[ x<suc-x (pred x) ]
                       suc (pred x)   ≡[ suc∘pred x x≢0 ]
                       x
                 ∎

suc2*<2suc :  (x : Bin) → suc2* x < 2suc x
suc2*<2suc x =
           begin suc2* x           ≡[ suc2*-as∘ x ] 
                 suc 2x            <[ x<1+x (suc 2x) ] 
                 1# + (suc 2x)     ≡[ cong (1# +_) (suc≗1+ 2x) ] 
                 1# + (1# + 2x)    ≡[ sym (+-assoc 1# 1# 2x) ] 
                 (1# + 1#) + 2x    ≡[ cong (2# +_) (2*≗2#* x) ]
                 2# + 2#x          ≡[ sym (*[1+x] x 2#) ]
                 2# * (1# + x)     ≡[ cong (2# *_) (sym (suc≗1+ x)) ] 
                 2# * (suc x)      ≡[ sym (2*≗2#* (suc x)) ]
                 2* (suc x)        ≡[ sym (2suc-as∘ x) ] 
                 2suc x
           ∎
           where
           2x = 2* x;  2#x = 2# * x




------------------------------------------------------------------------------
*-mono-≤ :  _*_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
*-mono-≤ {x} {x'} {y} {y'} x≤x' y≤y' =  toℕ[x*y]≤toℕ[x'*y']
         where
         m = toℕ x;  n = toℕ y;  m' = toℕ x';  n' = toℕ y' 

         m*n≤m'*n' =  *'-mono-≤ {m} {m'} {n} {n'} x≤x' y≤y'

         toℕ[x*y]≡m+n = toℕ*homo x y;  toℕ[x'*y']≡m'*n' = toℕ*homo x' y'

         toℕ[x*y]≤toℕ[x'*y'] = subst₂ _≤'_ (sym toℕ[x*y]≡m+n)
                                           (sym toℕ[x'*y']≡m'*n') m*n≤m'*n'
 

*-monoʳ-≤ :  (x : Bin) → (x *_) Preserves _≤_ ⟶ _≤_
*-monoʳ-≤ x {y} {y'} y≤y' = 
                          *-mono-≤ {x} {x} {y} {y'} (≤-refl {x}) y≤y'

*-monoˡ-≤ :  (x : Bin) → (_* x) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤ x {y} {y'} y≤y' = 
                          *-mono-≤ {y} {y'} {x} {x} y≤y' (≤-refl {x}) 

*-mono-< :  _*_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
*-mono-< {x} {x'} {y} {y'} x<x' y<y' =  
                                     toℕ[x*y]<toℕ[x'*y']
         where
         m = toℕ x;  n = toℕ y;  m' = toℕ x';  n' = toℕ y' 

         m*n<m'*n' =  *'-mono-< {m} {m'} {n} {n'} x<x' y<y'

         toℕ[x*y]≡m+n = toℕ*homo x y;  toℕ[x'*y']≡m'*n' = toℕ*homo x' y'

         toℕ[x*y]<toℕ[x'*y'] = subst₂ _<'_ (sym toℕ[x*y]≡m+n)
                                           (sym toℕ[x'*y']≡m'*n') m*n<m'*n'


*-monoʳ-< :  (x : Bin) → ((suc x) *_) Preserves _<_ ⟶ _<_
*-monoʳ-< x {y} {z} y<z = 
            begin  
              (suc x) * y      ≡[ suc* x y ] 
              y + xy           <[ +-mono-<-≤  {y} {z} {xy} {xz} y<z xy≤xz ] 
              z + xz           ≡[ sym (suc* x z) ] 
              (suc x) * z 
            ∎
            where
            xy = x * y;   xz = x * z;   xy≤xz = *-monoʳ-≤ x (<⇒≤ {y} {z} y<z)


*-monoˡ-< :  (x : Bin) → (_* (suc x)) Preserves _<_ ⟶ _<_
*-monoˡ-< x {y} {z} y<z = 
                        begin y * (suc x)    ≡[ *-comm y (suc x) ] 
                              (suc x) * y    <[ *-monoʳ-< x {y} {z} y<z ] 
                              (suc x) * z    ≡[ *-comm (suc x) z ] 
                              z * (suc x) 
                        ∎

2*-mono-≤ :  2* Preserves _≤_ ⟶ _≤_
2*-mono-≤ {x} {y} x≤y =
                      begin 2* x      ≡[ 2*≗2#* x ]
                            2# * x    ≤[ *-monoʳ-≤ 2# {x} {y} x≤y ]  
                            2# * y    ≡[ sym (2*≗2#* y) ]
                            2* y
                      ∎      

2*-mono-< :  2* Preserves _<_ ⟶ _<_
2*-mono-< {x} {y} x<y =  
                      begin 2* x      ≡[ 2*≗2#* x ]
                            2# * x    <[ *-monoʳ-< 1# {x} {y} x<y ]  
                            2# * y    ≡[ sym (2*≗2#* y) ]
                            2* y
                      ∎

2*-back-mono-≤ :  {x y : Bin} → 2* x ≤ 2* y → x ≤ y
2*-back-mono-≤ {x} {y} 2x≤2y = 
        case  
            <-cmp x y 
        of \ 
        { (tri< x<y _   _  ) → <⇒≤ {x} {y} x<y
        ; (tri≈ _   x≡y _  ) → ≤-reflexive x≡y
        ; (tri> _   _   x>y) → let 2x>2y = 2*-mono-< {y} {x} x>y 
                               in  
                               contradiction 2x≤2y (<⇒≱ {2* y} {2* x} 2x>2y)
        }

2*-back-mono-< :  {x y : Bin} → 2* x < 2* y → x < y
2*-back-mono-< {x} {y} 2x<2y = 
        case  
            <-cmp x y 
        of \ 
        { (tri< x<y _   _  ) → x<y
        ; (tri≈ _   x≡y _  ) → let 2x≡2y = cong 2* x≡y
                               in  contradiction 2x<2y (<-irrefl 2x≡2y)

        ; (tri> _   _   x>y) → let 2x>2y = 2*-mono-< {y} {x} x>y 
                               in  
                               contradiction 2x>2y (<⇒≯ {2* x} {2* y} 2x<2y)
        }

x<2x :  (x : Bin) → x ≢ 0# → x < 2* x 
x<2x x x≢0 = 
           begin x              ≡[ sym (suc∘pred x x≢0) ]
                 suc px         ≡[ sym (*1 (suc px)) ]
                 suc px * 1#    <[ *-monoʳ-< px (x<1+x 1#) ]
                 suc px * 2#    ≡[ *-comm (suc px) 2# ]
                 2# * suc px    ≡[ sym (2*≗2#* (suc px)) ]
                 2* (suc px)    ≡[ cong 2* (suc∘pred x x≢0) ]
                 2* x 
           ∎
           where
           px = pred x

suc-x≤2x :  (x : Bin) → x ≢ 0# → suc x ≤ 2* x 
suc-x≤2x x = 
           x<⇒suc-x≤ {x} {2* x} ∘ x<2x x 

x≤[suc-y]*x :  (x y : Bin) → x ≤ (suc y) * x 
x≤[suc-y]*x x y =
                begin x            ≤[ x≤x+y x (y * x) ]
                      x + y * x    ≡[ sym (suc* y x) ]
                      (suc y) * x 
                ∎

x≤2x :  (x : Bin) → x ≤ 2* x 
x≤2x x =  
       begin x       ≤[ x≤x+y x x ]
             x + x   ≡[ sym (2x≡x+x x) ]
             2* x
       ∎

x<suc2*-x :   (x : Bin) → x < suc2* x
x<suc2*-x x = 
            begin x           <[ x<suc-x x ] 
                  suc x       ≤[ suc-mono-≤ {x} {2* x} (x≤2x x) ]
                  suc (2* x)  ≡[ sym (suc2*-as∘ x) ]
                  suc2* x
            ∎

x<2suc-x :   (x : Bin) → x < 2suc x
x<2suc-x x = 
           begin x           <[ x<suc-x x ] 
                 suc x       ≤[ x≤2x (suc x) ]
                 2* (suc x)  ≡[ sym (2suc-as∘ x) ]
                 2suc x
           ∎

0<2^ :  (n : ℕ) → 0# < 2^ n 
0<2^ n = 
       ≢0⇒> (2^≢0 n)

1≤2^ :  (n : ℕ) → 1# ≤ 2^ n 
1≤2^ n = 
       suc-x≤⇒x< {0#} {2^ n} (0<2^ n)

2^n<2^[1+n] :  (n : ℕ) → 2^ n < 2^ (1+ n) 
2^n<2^[1+n] n =
              x<2x (2^ n) (2^≢0 n)

------------------------------------
2^-mono-≤ :  2^ Preserves _≤'_ ⟶ _≤_
2^-mono-≤ {m} {n} m≤n =
                      begin 2^m           ≡[ sym (*1 2^m) ]
                            2^m * 1#      ≤[ *-monoʳ-≤ 2^m (0<2^ d) ]
                            2^m * 2^d     ≡[ sym (2^-homo m d) ]
                            2^ (m +' d)   ≡[ cong 2^ m+d≡n ]
                            2^ n
                      ∎
                      where
                      2^m = 2^ m;   d     = n ∸' m   
                      2^d = 2^ d;   m+d≡n = m+n∸m≡n m≤n

------------------------------------
2^-mono-< :  2^ Preserves _<'_ ⟶ _<_

2^-mono-< {m} {n} 1+m≤n =
   begin
     2^m               ≡[ sym (1* 2^m) ]
     1# * 2^m          ≡[ cong (1# *_) (sym (suc∘pred 2^m 2^m≢0)) ]
     1# * (suc p2^m)   <[ *-monoˡ-< p2^m {1#} {2#} (x<1+x 1#) ]
     2# * (suc p2^m)   ≡[ cong (2# *_) (suc∘pred 2^m 2^m≢0) ]
     2# * 2^m          ≡[ sym (2*≗2#* 2^m) ]
     2* 2^m            ≡[ refl ]
     2^ (1+ m)         ≤[ 2^-mono-≤ 1+m≤n ]
     2^ n
   ∎
   where
   2^m = 2^ m;   p2^m = pred 2^m;  2^m≢0 = 2^≢0 m

-------------------------------------------------
^-back-mono-< :  {m n : ℕ} → 2^ m < 2^ n → m <' n 
^-back-mono-< {m} {n} 2^m<2^n = 
      case 
          Nat0.compare m n 
      of \ 
      { (tri< m<n _   _  ) → m<n
      ; (tri≈ _   m≡n _  ) → let 2^m≡2^n = cong 2^ m≡n
                             in  contradiction 2^m<2^n (≡⇒≮ 2^m≡2^n) 

      ; (tri> _   _   m>n) → let 2^m>2^n = 2^-mono-< m>n
                             in 
                             contradiction 2^m<2^n (<⇒≯ {2^ n} {2^ m} 2^m>2^n) 
      }


pred-mono-≤ :  pred Preserves _≤_ ⟶ _≤_
pred-mono-≤ {x} {y} x≤y = 
                        ≤'begin toℕ (pred x)    ≡≤'[ toℕ∘pred x ]
                                pred' (toℕ x)    ≤'[ NatP.pred-mono x≤y ]
                                pred' (toℕ y)   ≡≤'[ sym (toℕ∘pred y) ]
                                toℕ (pred y)
                        ≤'end

--------------------------------------
x<1⇒x≡0 :  {x : Bin} → x < 1# → x ≡ 0#
x<1⇒x≡0 {x} x<1 =
                ≤0⇒≡ x≤0   
            where
            suc-x≤1 = x<⇒suc-x≤ {x} {1#} x<1  
                 
            x≤0 = begin x             ≡[ sym (pred∘suc x) ]
                        pred (suc x)  ≤[ pred-mono-≤ {suc x} {1#} suc-x≤1 ]
                        pred 1#       ≡[ refl ]
                        0#
                  ∎  

x≢0,1⇒1<x :  {x : Bin} → x ≢ 0# → x ≢ 1# → 1# < x
x≢0,1⇒1<x {x} x≢0 x≢1 =
                      case <-cmp 1# x
                      of \
                      { (tri< 1<x _   _  ) → 1<x
                      ; (tri≈ _   1≡x _  ) → contradiction (sym 1≡x) x≢1
                      ; (tri> _   _   1>x) → contradiction (x<1⇒x≡0 1>x) x≢0 
                      }                                

------------------------------------------------------------------------------
import Induction.Nat as NatInd
open import Induction.WellFounded using 
     (WellFounded; module All; module Subrelation; module Inverse-image)

-- The strict order on Bin implies the strict order on ℕ:
--
-- <⇒<ℕ : ∀ {b₁ b₂} → b₁ < b₂ → (Nat._<_ on toℕ) b₁ b₂
-- <⇒<ℕ = id

-- Derive well-foundedness of _<_ on Bin from well-foundedness of _<_ on ℕ:
--
<-wellFounded : WellFounded _<_
<-wellFounded = Subrelation.wellFounded id
                        (Inverse-image.wellFounded toℕ NatInd.<-wellFounded)

open All <-wellFounded using () renaming (wfRec to <-rec)

downFrom :  Bin → List Bin     -- x ∷ x-1 ∷ x-2 ∷ ... ∷ 0# ∷ []
downFrom =  <-rec _ _ df
    where
    df : (x : Bin) → (∀ y → y < x → List Bin) → List Bin
    df x dfRec 
         with x ≟ 0#
    ... | yes _  =   [ 0# ]
    ... | no x≢0 =   x ∷ (dfRec (pred x) (pred-x<x {x} x≢0))