{-
This file is a part of the library  Binary-4.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.

Binary-4  is free software: you can redistribute it and/or modify it
under the terms of the GNU General Public License.
See  license.txt.
-}

module GCD where

open import Function using (flip; _∘_; _$_; case_of_)
open import Algebra.FunctionProperties using (Op₂)
open import Relation.Nullary           using (Dec; yes; no)
open import Relation.Nullary.Negation  using (contradiction)
open import Relation.Binary            using (Rel; Tri; _⇒_)
open import Relation.Binary.PropositionalEquality as PE using 
                             (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open PE.≡-Reasoning renaming (begin_ to begin≡_; _∎ to _end≡)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Induction.WellFounded using (module All)

open import LtReasoning using (module InequalityReasoning)  -- by U. Norell

-- of application ---
import Nat0 
open import Bin0 using (Bin; 1#; 2#; _∣_; 2*; _+_; _*_; toℕ; +0; 0+; *0)
open import Bin1 using (*1; 1*; ∣x⇒∣y*x; ∣+; *-assoc; *-comm; 2*≗2#*; 2x≡x+x)
open import Ord0 using (_<_; _≤_; _<?_; _≤?_; ≤-reflexive; ≤-trans; <-trans; 
                        <-≤-trans; ≤-<-trans; <⇒≤; ≮⇒≥; <⇒≱; ≰⇒>; x<⇒suc-x≤; 
                        x≤y+x; +-mono-≤; +-monoʳ-≤; +-monoʳ-<; *-monoˡ-≤; 
                                                    x≢0,1⇒1<x; <-wellFounded)
open import Minus     using (_∸_; [x+y]∸y≡x; *-lDistrib-∸)
open import OfDivMod  using (DivMod; divMod; result)





--****************************************************************************
record GCD (a b : Bin) : Set
       where
       constructor gcd′

       field  proper   : Bin             -- proper gcd   
              divides₁ : proper ∣ a
              divides₂ : proper ∣ b
              greatest : ∀ {d} → (d ∣ a) → (d ∣ b) → (d ∣ proper)


swapGCD :  {a b : Bin} → GCD a b → GCD b a
swapGCD (gcd′ g g∣a g∣b maxg) =  gcd′ g g∣b g∣a (\{d} → flip (maxg {d}))


------------------------------------------------------------------------------
open Bin
open Tri

open InequalityReasoning {A = Bin} _<_ _≤_
                                   (\{x y}   → ≤-reflexive {x} {y})
                                   (\{x y z} → <-trans   {x} {y} {z})
                                   (\{x y z} → ≤-trans   {x} {y} {z})
                                   (\{x y z} → <-≤-trans {x} {y} {z})
                                   (\{x y z} → ≤-<-trans {x} {y} {z})

_≟_ = Bin0._≟_ 




{- ***************************************************************************
-- Commentary:  the version without termination proof. 

gcd : (x y : Bin) → GCD x y 
gcd x y
      with y ≟ 0#
... | yes y≡0 =  gcd′ x (1# , *1 x) (0# , x*0≡y) (\d∣x _ → d∣x)
                 where
                 x*0≡y = trans (*0 x) (sym y≡0)
... | no y≢0 
         with  divMod x y y≢0
...    | result q r x≡r+qy r<y =  liftGCD (gcd y r)
       where
       liftGCD : GCD y r → GCD x y 
       liftGCD (gcd′ g (q₁ , gq₁≡y) (q₂ , gq₂≡r) maximality) = 
                gcd′ g g∣x          g∣y     (\{d} → maximality' {d})
         --
         -- The proper  gcd  preserves, but proofs are corrected.
         where
         qy  = q * y
         g∣y = (q₁ , gq₁≡y)

         g∣r : g ∣ r
         g∣r = (q₂ , gq₂≡r)

         g∣qy :  g ∣ qy 
         g∣qy =  ∣x⇒∣y*x {g} y q g∣y

         g∣r+qy :  g ∣ (r + qy)
         g∣r+qy =  ∣+ {g} r qy g∣r g∣qy
 
         g∣x :  g ∣ x
         g∣x =  subst (g ∣_) (sym x≡r+qy) g∣r+qy

         x-qy≡r :  x ∸ qy ≡ r 
         x-qy≡r =  begin≡ x ∸ qy           ≡⟨ cong (_∸ qy) x≡r+qy ⟩ 
                          (r + qy) ∸ qy    ≡⟨ [x+y]∸y≡x r qy ⟩ 
                          r                   
                   end≡

         maximality' :  ∀ {d} → d ∣ x → d ∣ y → d ∣ g
         maximality' {d} (s , ds≡x) (t , dt≡y) =  maximality {d} d∣y d∣r  
           where
           d∣y : d ∣ y 
           d∣y = (t , dt≡y) 

           tq = t * q
        
           d[s-tq]≡r :  d * (s ∸ tq) ≡ r
           d[s-tq]≡r = 
              begin≡ 
                d * (s ∸ tq)         ≡⟨ *-lDistrib-∸ d s tq ⟩
                (d * s) ∸ (d * tq)   ≡⟨ cong₂ _∸_ ds≡x (sym (*-assoc d t q)) ⟩
                x ∸ (d * t) * q      ≡⟨ cong ((x ∸_) ∘ (_* q)) dt≡y ⟩
                x ∸ y * q            ≡⟨ cong (x ∸_) (*-comm y q) ⟩
                x ∸ q * y            ≡⟨ x-qy≡r ⟩
                r
              end≡ 

           d∣r :  d ∣ r
           d∣r =  ((s ∸ tq) , d[s-tq]≡r) 
******************************************************************************
-}




--============================================================================
open All <-wellFounded using () renaming (wfRec to <-rec)

P :  Bin → Set
P a =  (b : Bin) → GCD a b

-- <-wellFounded, <-rec and P  are used for termination proof.
-- Actually this means that  gcd x y  is computed via  gcd r x,
-- where  r = rem y x,  r < x.  And as _<_ is WellFounded on Bin, 
-- this proves termination of  gcd  to Agda.

gcd : (a : Bin) → P a
gcd =  <-rec _ P gc
  where
  gc :  (x : Bin) → (∀ x' → x' < x → P x') → P x
  gc x gcRec
       with x ≟ 0#
  ... | yes x≡0 =  (\y → let y*0≡x = trans (*0 y) (sym x≡0)
                         in
                         gcd′ y (0# , y*0≡x) (1# , *1 y)  (\_ d∣y → d∣y)
                   )
                   -- : P x                 
       
  ... | (no x≢0) =  aux
      where
      aux : P x
      aux y  with  divMod y x x≢0

      ... | result q r y≡r+qx r<x =  liftGCD (gcRec r r<x x)
         where
         liftGCD : GCD r x → GCD x y
         liftGCD (gcd′ g (q₁ , gq₁≡r) (q₂ , gq₂≡x) maximality) = 
                  gcd′ g g∣x          g∣y          (\{d} → maximality' {d})
           --
           -- The proper  gcd  values preserves, but proofs are corrected.
           where
           qx = q * x

           g∣r : g ∣ r
           g∣r = (q₁ , gq₁≡r)

           g∣x = (q₂ , gq₂≡x)

           g∣qx :  g ∣ qx 
           g∣qx =  ∣x⇒∣y*x {g} x q g∣x

           g∣r+qx :  g ∣ (r + qx)
           g∣r+qx =  ∣+ {g} r qx g∣r g∣qx
 
           g∣y :  g ∣ y
           g∣y =  subst (g ∣_) (sym y≡r+qx) g∣r+qx

           y-qx≡r :  y ∸ qx ≡ r 
           y-qx≡r =  begin≡ y ∸ qx           ≡⟨ cong (_∸ qx) y≡r+qx ⟩ 
                           (r + qx) ∸ qx    ≡⟨ [x+y]∸y≡x r qx ⟩ 
                            r                   
                     end≡

           maximality' :  ∀ {d} → d ∣ x → d ∣ y → d ∣ g
           maximality' {d} (s , ds≡x) (t , dt≡y) =  maximality {d} d∣r d∣x  
             where
             d∣x : d ∣ x 
             d∣x = (s , ds≡x) 

             sq = s * q
        
             d[t-sq]≡r :  d * (t ∸ sq) ≡ r
             d[t-sq]≡r = 
               begin≡ 
                 d * (t ∸ sq)        ≡⟨ *-lDistrib-∸ d t sq ⟩
                 (d * t) ∸ (d * sq)  ≡⟨ cong₂ _∸_ dt≡y (sym (*-assoc d s q)) ⟩
                 y ∸ (d * s) * q     ≡⟨ cong ((y ∸_) ∘ (_* q)) ds≡x ⟩
                 y ∸ x * q           ≡⟨ cong (y ∸_) (*-comm x q) ⟩
                 y ∸ q * x           ≡⟨ y-qx≡r ⟩
                 r
               end≡ 

             d∣r :  d ∣ r
             d∣r =  ((t ∸ sq) , d[t-sq]≡r) 


----------------------------
gcd! : Op₂ Bin
gcd! x =  GCD.proper ∘ gcd x
