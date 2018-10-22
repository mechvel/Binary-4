{-
This file is a part of the library  Binary-4.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.

Binary-4  is free software: you can redistribute it and/or modify it
under the terms of the GNU General Public License.
See  license.txt.
-}

module OfDivMod where

open import Function         using (id; _∘_; _on_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary  using (Tri)
open import Relation.Binary.PropositionalEquality as PE using 
                                                  (_≡_; _≢_; refl; sym; cong)
open PE.≡-Reasoning renaming (begin_ to begin≡_; _∎ to _end≡)

open import Induction.WellFounded using (module All) -- new attempt

open import LtReasoning using (module InequalityReasoning)  -- by U. Norell

-- of application ---
import Nat0 
open import Bin0 using (Bin; suc; 1#; _+_; _*_; 2*; toℕ; suc≢0; 2suc-as∘; 
                        suc2*-as∘; 0+; +0; suc≗1+; suc+assoc; +-assoc
                       )
open import Bin1 using (2*-distrib; 2*-*-assoc; 2x≡x+x; suc*)
open import Ord0 using 
     (_<_; _>_; _≤_; _≥_; <⇒≤; <⇒≱; <-cmp; ≤-refl; x≤2x; ≤-reflexive; ≤-trans;
      <-trans; <-≤-trans; ≤-<-trans; ≢0⇒>; +-monoˡ-≤; +-monoʳ-<; 2*-mono-<; 
      suc-x≤⇒x<; x<⇒suc-x≤; x<1+x; x≤suc-x; 0<suc; x<suc2*-x; <-wellFounded 
     )   
open import Minus using (_∸_; [x+y]∸y≡x; [x+y]∸x≡y; [x∸y]+y≡x; +-∸-assoc; 
                                                               ∸-monoˡ-≤)


 

--****************************************************************************
open Bin
open Tri
_≟_ = Bin0._≟_

open InequalityReasoning {A = Bin} _<_ _≤_
                                   (\{x y}   → ≤-reflexive {x} {y})
                                   (\{x y z} → <-trans   {x} {y} {z})
                                   (\{x y z} → ≤-trans   {x} {y} {z})
                                   (\{x y z} → <-≤-trans {x} {y} {z})
                                   (\{x y z} → ≤-<-trans {x} {y} {z})

record DivMod (dividend divisor : Bin) : Set where
       constructor result
       field
         quotient    :  Bin
         remainder   :  Bin
         equality    :  dividend ≡ remainder + quotient * divisor
         rem<divisor :  remainder < divisor
--
-- Note that  divisor ≢ 0#  in  DivMod _ divisor.


------------------------------------------------------------------------------
open All <-wellFounded using () renaming (wfRec to <-rec)



--============================================================================
divMod :  (a b : Bin) → b ≢ 0# → DivMod a b

{- ---------------------------------
divMod 2a b  for b≢0  is as follows.

Let   a = qb + r,   r < b.
Then
      2a = 2qb + 2r,   r ≤ 2r < 2b,
                       r < b  < 2b.

If  2r < b  then  (2q , 2r)
else              (2q+1, 2r - b).

Prove   2r - b < b.   It is equivalent to  2r < 2b  ~  r < b. 
-------------------------------------
-}

-- <-wellFounded and <-rec  are used to prove termination.
-- Because  divMod a b  is computed via certain  divMod a₀ b,
-- where  a₀ < a.

divMod a b b≢0 =  dmBy-b a 
  where
  dmBy-b :  (a : Bin) → DivMod a b
  dmBy-b =  <-rec _ _ dm
    where
    -- For a ≠ 0,  divMod a b  is reduced to  divMod a' b,   where a' < a.
    -- So that this recursion terminates.

    dm :  (a : Bin) → (∀ x → x < a → DivMod x b) → DivMod a b

    dm 0#       _     =  result 0# 0# refl (≢0⇒> b≢0)

    -------------------
    dm (2suc a) dmRec =  correct (dmRec (suc a) suc-a<2suc-a)
      where
      a' = 2suc a;  2b = 2* b;  1+a = suc a

      -- dmRec :  ∀ x → x < 2suc a → DivMod x b

      suc-a<2suc-a :  suc a < 2suc a
      suc-a<2suc-a =  begin suc a           ≡[ sym (+0 (suc a)) ]
                            suc a + 0#      <[ +-monoʳ-< (suc a) (0<suc a) ]
                            suc a + suc a   ≡[ sym (2x≡x+x (suc a)) ]
                            2* (suc a)      ≡[ sym (2suc-as∘ a) ]
                            2suc a          
                      ∎

      correct :  DivMod 1+a b → DivMod a' b
      correct (result q r 1+a≡r+qb r<b) =  aux (<-cmp 2r b)
        where
        2r  = 2* r;    2q   = 2* q;    qb = q * b;    2r-b = 2r ∸ b
        2qb = 2* qb;   2q*b = 2q * b

        aux :  Tri (2r < b) (2r ≡ b) (2r > b) → DivMod a' b
        aux (tri< 2r<b _ _) =  result 2q 2r a'≡2r+2qb 2r<b
           where
           a'≡2r+2qb =
                begin≡ 2suc a         ≡⟨ 2suc-as∘ a ⟩
                       2* 1+a         ≡⟨ cong 2* 1+a≡r+qb ⟩
                       2* (r + qb)    ≡⟨ 2*-distrib r qb ⟩
                       2r + 2* qb     ≡⟨ cong (2r +_) (sym (2*-*-assoc q b)) ⟩
                       2r + (2q * b)
                end≡

        aux (tri≈ _ 2r≡b _) =  result suc2q 0# a'≡0+[suc2q]*b (≢0⇒> b≢0)
           where
           suc2q          = suc2* q
           a'≡0+[suc2q]*b =
                begin≡
                  2suc a               ≡⟨ 2suc-as∘ a ⟩
                  2* 1+a               ≡⟨ cong 2* 1+a≡r+qb ⟩
                  2* (r + qb)          ≡⟨ 2*-distrib r qb ⟩
                  2r + (2* qb)         ≡⟨ cong (_+ (2* qb)) 2r≡b ⟩
                  b + (2* qb)          ≡⟨ cong (b +_) (sym (2*-*-assoc q b)) ⟩
                  b + 2q * b           ≡⟨ sym (suc* 2q b) ⟩
                  (suc 2q) * b         ≡⟨ cong (_* b) (sym (suc2*-as∘ q)) ⟩
                  (suc2* q) * b        ≡⟨ sym (0+ ((suc2* q) * b)) ⟩
                  0# + (suc2* q) * b
                end≡

        aux (tri> _ _ 2r>b) =  result suc2q 2r-b a'≡[2r-b]+[suc2q]*b 2r-b<b
          where
          -- Given:  r<b,  2r>b

          suc2q = suc2* q;                b≤2r = <⇒≤ {b} {2r} 2r>b
          2r<2b = 2*-mono-< {r} {b} r<b

          suc[2r-b]≤b =
            begin suc (2r ∸ b)    ≡[ suc≗1+ 2r-b ]
                  1# + (2r ∸ b)   ≡[ sym (+-∸-assoc 1# {2r} {b} b≤2r) ]
                  (1# + 2r) ∸ b   ≡[ cong (_∸ b) (sym (suc≗1+ 2r)) ]
                  (suc 2r) ∸ b    ≤[ ∸-monoˡ-≤ b {suc 2r} {2b}
                                                 (x<⇒suc-x≤ {2r} {2b} 2r<2b) ]
                  2b ∸ b          ≡[ cong (_∸ b) (2x≡x+x b) ]
                  (b + b) ∸ b     ≡[ [x+y]∸y≡x b b ]
                  b
            ∎

          2r-b<b =  suc-x≤⇒x< {2r ∸ b} {b} suc[2r-b]≤b

          a'≡[2r-b]+[suc2q]*b =
            begin≡
              2suc a                 ≡⟨ 2suc-as∘ a ⟩
              2* (suc a)             ≡⟨ cong 2* 1+a≡r+qb ⟩
              2* (r + qb)            ≡⟨ 2*-distrib r qb ⟩
              2r + 2qb               ≡⟨ cong (2r +_) (sym (2*-*-assoc q b)) ⟩
              2r + 2q*b              ≡⟨ cong (_+ 2q*b)
                                             (sym ([x∸y]+y≡x {2r} {b} b≤2r)) ⟩
              (2r-b + b) + 2q*b      ≡⟨ +-assoc 2r-b b 2q*b ⟩
              2r-b + (b + 2q*b)      ≡⟨ cong (2r-b +_) (sym (suc* 2q b)) ⟩
              2r-b + (suc 2q) * b    ≡⟨ cong ((2r-b +_) ∘ (_* b))
                                                         (sym (suc2*-as∘ q)) ⟩
             (2r ∸ b) + (suc2* q) * b
            end≡

    --------------------
    dm (suc2* a) dmRec =  correct (dmRec a a<suc2*-a)
      where
      a' = suc2* a;   2a = 2* a  
 
      {- Given:  a = r + qb;   r<b.
         1+2a = 1+2r + 2qb
  
         (q', r') =  if  1+2r<b  then (2q , 1 + 2r)   
                     else             -- b≤1+2r
                                      (1+2q , 1 + 2r - b)
      -}

      a<suc2*-a =  x<suc2*-x a

      correct :  DivMod a b → DivMod a' b
      correct (result q r a≡r+qb r<b) =  aux (<-cmp suc[2r] b)
        where
        2r = 2* r;    suc[2r] = suc 2r;    2q   = 2* q
        qb = q * b;   2*qb    = 2* qb;     2q*b = 2q * b     

        a'≡suc[2r]+2q*b = 
            begin≡
              suc2* a            ≡⟨ suc2*-as∘ a ⟩
              suc (2* a)         ≡⟨ cong (suc ∘ 2*) a≡r+qb ⟩
              suc (2* (r + qb))  ≡⟨ cong suc (2*-distrib r qb) ⟩
              suc (2r + 2*qb)    ≡⟨ sym (suc+assoc 2r 2*qb) ⟩
              suc[2r] + 2*qb     ≡⟨ cong (suc[2r] +_) (sym (2*-*-assoc q b)) ⟩
              suc[2r] + 2q*b
            end≡


        aux :  Tri (suc[2r] < b) (suc[2r] ≡ b) (suc[2r] > b) → DivMod a' b  

        aux (tri< suc[2r]<b _ _) = result 2q suc[2r] a'≡suc[2r]+2q*b suc[2r]<b
        aux (tri≈ _ suc[2r]≡b _) = result q' 0# a'≡0+q'b (≢0⇒> b≢0)
           where
           q' = suc 2q;  q'b = q' * b 

           a'≡0+q'b =  begin≡ a'               ≡⟨ a'≡suc[2r]+2q*b ⟩
                              suc[2r] + 2q*b   ≡⟨ cong (_+ 2q*b) suc[2r]≡b ⟩
                              b + 2q*b         ≡⟨ sym (suc* 2q b) ⟩
                              q' * b           ≡⟨ sym (0+ q'b) ⟩
                              0# + q'b 
                       end≡

        aux (tri> _ _ suc[2r]>b) = result q' r' a'≡r'+q'b r'<b 
          where
          q' = suc 2q;   r' = suc[2r] ∸ b;    q'b = q' * b 

          b≤suc[2r]    =  <⇒≤ {b} {suc[2r]} suc[2r]>b
          suc[r]+r≤b+r =  +-monoˡ-≤ r {suc r} {b} (x<⇒suc-x≤ {r} {b} r<b) 

          a'≡r'+q'b =
            begin≡ 
              a'                ≡⟨ a'≡suc[2r]+2q*b ⟩
              suc[2r] + 2q*b    ≡⟨ cong (_+ 2q*b)
                                     (sym ([x∸y]+y≡x {suc[2r]} {b} b≤suc[2r]))
                                 ⟩
              ((suc[2r] ∸ b) + b) + 2q*b   ≡⟨ +-assoc r' b 2q*b ⟩
              r' + (b + 2q*b)              ≡⟨ cong (r' +_) (sym (suc* 2q b)) ⟩
              r' + (suc 2q) * b            ≡⟨ refl ⟩
              r' + q'b 
            end≡ 

          r'<b = 
              begin suc[2r] ∸ b        ≡[ cong ((_∸ b) ∘ suc) (2x≡x+x r) ] 
                    suc (r + r) ∸ b    ≡[ cong (_∸ b) (sym (suc+assoc r r)) ] 
                    (suc r + r) ∸ b    ≤[ ∸-monoˡ-≤ b {suc r + r} {b + r} 
                                                               suc[r]+r≤b+r  ]
                    (b + r) ∸ b        ≡[ [x+y]∸x≡y b r ]
                    r                  <[ r<b ]
                    b
              ∎

------------------------------------------------------------------------------
quot :  (a b : Bin) → b ≢ 0# → Bin
quot a b =  
         DivMod.quotient ∘ divMod a b  

rem :  (a b : Bin) → b ≢ 0# → Bin
rem a b =  
        DivMod.remainder ∘ divMod a b  
