{-
This file is a part of the library  Binary-4.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.

Binary-4  is free software: you can redistribute it and/or modify it
under the terms of the GNU General Public License.
See  license.txt.
-}

module Logarithm where

open import Function                  using (_∘_; _$_; case_of_)
open import Relation.Nullary          using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary           using (Tri; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality as PE using
                                     (_≡_; _≢_; refl; sym; trans; cong; subst)
open PE.≡-Reasoning renaming (begin_ to begin≡_; _∎ to _end≡)
open import Data.Nat using (ℕ; z≤n; s≤s) 
                     renaming (suc to 1+_; _+_ to _+'_; _≤_ to _≤'_
                             )
open import Data.Nat.Properties as NatP using ()
            renaming (≤-refl to ≤'-refl;module ≤-Reasoning to ≤'-Reasoning
                     )
open ≤'-Reasoning using () renaming (begin_ to ≤'begin_; _∎ to _≤'end;
                                    _≡⟨_⟩_ to _≡≤'[_]_; _≤⟨_⟩_ to _≤'[_]_)

open import LtReasoning using (module InequalityReasoning)  -- by U. Norell

-- of application ---
import Nat0
open import Bin0 using (Bin; suc; 1#; 2#; 3#; 4#; _+_; 2*; 2^; 2suc≢0; 
                        suc2*≢0; 2suc-as∘; suc2*-as∘; suc≗1+; +-assoc;
                                                                  suc+assoc)
open import Bin1 using (2^≢0; x≢0⇒2x≢0; 2x≡x+x; *1; 2*-distrib) 
open import Ord0 using 
     (_≤_; _<_; _>_; ≤-refl; ≤-reflexive; <-trans; ≤-trans; <-≤-trans; 
      ≤-<-trans; <-irrefl; ≤⇒≯; <⇒≤; <⇒≱; ≤,≢⇒<; x<1+x; x<2x; x<⇒suc-x≤; 
      x≤suc-x; x≢suc-x; ≢0⇒>; +-mono-≤-<; 2*-mono-≤; 2*-mono-<; 1≤2^; 
      2*-back-mono-<; 2*-back-mono-≤; ^-back-mono-<; 2^-mono-≤; suc2*<2suc
     )
open import Minus using (suc2*-x≢2y; 2*-injective)




--****************************************************************************
open Bin
open Tri
open InequalityReasoning {A = Bin} _<_ _≤_
                                   (\{x y}   → ≤-reflexive {x} {y})
                                   (\{x y z} → <-trans   {x} {y} {z})
                                   (\{x y z} → ≤-trans   {x} {y} {z})
                                   (\{x y z} → <-≤-trans {x} {y} {z})
                                   (\{x y z} → ≤-<-trans {x} {y} {z})


------------------------------------------------------------------------------
private 
  2≤2*2^e :  ∀ {e} → 2# ≤ 2* (2^ e) 
  2≤2*2^e {e} = 
              begin  2#          ≡[ refl ]
                     2* 1#       ≤[ 2*-mono-≤ {1#} {2^ e} (1≤2^ e) ] 
                     2* (2^ e) 
              ∎


record Log₂ (x : Bin) : Set where
       constructor log₂′ 

       field e      : ℕ 
             pow    : Bin
             2pow   : Bin
             powEq  : pow ≡ 2^ e
             2powEq : 2pow ≡ 2* pow

             le     : pow ≤ x  
             gt     : 2pow > x
             sucEq? : Dec (suc x ≡ 2pow)

       2pow≡2^[1+e] :  2pow ≡ 2^ (1+ e)
       2pow≡2^[1+e] =  trans 2powEq (cong 2* powEq) 

       2^e≤x = subst (_≤ x) powEq le

       x<2*pow : x < 2* pow 
       x<2*pow = subst (x <_) 2powEq gt

       x<2^[1+e] :  x < 2^ (1+ e)
       x<2^[1+e] =  subst (x <_) 2pow≡2^[1+e] gt

       2pow≤2x : 2pow ≤ 2* x
       2pow≤2x = 
               begin 2pow      ≡[ 2powEq ]
                     2* pow    ≤[ 2*-mono-≤ {pow} {x} le ]
                     2* x
               ∎ 

--------------
_≟_ = Bin0._≟_




------------------------------------------------------------------------------
log₂ :  (x : Bin) → x ≢ 0# → Log₂ x

-- Integer part of (log₂ x).

log₂ 0#       0≢0 =  contradiction refl 0≢0
log₂ (2suc x) _   =  aux (x ≟ 0#)
  where
  x' = 2suc x;   1+x = suc x

  aux :  Dec (x ≡ 0#) → Log₂ x' 

  aux (yes x≡0) =  log₂′ 1 2# 4# refl refl  2≤x' le (no 1+x'≢4) 
                   where
                   x'≡2 = cong 2suc x≡0;   2≤x' = ≤-reflexive (sym x'≡2)

                   le = begin (2suc x)     ≡[ cong 2suc x≡0 ]
                              (2suc 0#)    ≡[ 2suc-as∘ 0# ]
                              2* 1#        <[ x<2x (2* 1#) 2suc≢0 ]
                              2* (2* 1#)   ≡[ refl ]
                              2^ 2
                        ∎

                   1+x'≡3 =  cong suc x'≡2   
                   1+x'≢4 =  subst (_≢ 4#) (sym 1+x'≡3) (x≢suc-x 3#)  
  
  aux (no x≢0) =  aux0 (log₂ x x≢0)
    where
    aux0 : Log₂ x → Log₂ x'

    aux0 res@(log₂′ e pow 2pow pow≡2^e 2pow≡2*pow 
                    pow≤x x<2pow (yes 1+x≡2pow)) =
                                                             
              log₂′ 2+e 2*2pow 2*2*2pow 2*2pow≡2^[2+e] refl
                    2*2pow≤x' x'<2*2*2pow (no 1+x'≢2*2*2pow) 
       where
       -- here  x' ≡ 2^(2+e)

       open Log₂ res using (2pow≡2^[1+e])

       2+e = 2 +' e;   2*2pow = 2* 2pow;   2*2*2pow = 2* 2*2pow

       2*2pow≡2^[2+e] = cong 2* 2pow≡2^[1+e]

       x'≡2*2pow =  begin≡ 2suc x       ≡⟨ 2suc-as∘ x ⟩
                           2* (suc x)   ≡⟨ cong 2* 1+x≡2pow ⟩
                           2* 2pow
                    end≡

       2*2pow≤x' =  ≤-reflexive (sym x'≡2*2pow)

       2*2pow≢0 :  2*2pow ≢ 0# 
       2*2pow≢0 2*2pow≡0 =  
                      2^≢0 2+e $
                      begin≡ 2^ 2+e          ≡⟨ refl ⟩
                             2* (2* (2^ e))  ≡⟨ cong 2* (sym 2pow≡2^[1+e]) ⟩
                             2* 2pow         ≡⟨ 2*2pow≡0 ⟩
                             0#
                      end≡

       x'<2*2*2pow =  begin x'          ≡[ x'≡2*2pow ]
                            2*2pow      <[ x<2x 2*2pow 2*2pow≢0 ]
                            2*2*2pow
                      ∎

       -- suc x'  is odd, therefore it is not a power of 2.

       1+x'≢2*2*2pow :  suc x' ≢ 2*2*2pow 

       1+x'≢2*2*2pow suc-x'≡2*2*2pow =  suc2*-x≢2y (suc x) 2*2pow eq
            where
            eq = begin≡ suc2* (suc x)       ≡⟨ suc2*-as∘ (suc x) ⟩
                        suc (2* (suc x))    ≡⟨ cong suc (sym (2suc-as∘ x)) ⟩
                        suc (2suc x)        ≡⟨ refl ⟩
                        suc x'              ≡⟨ suc-x'≡2*2*2pow ⟩
                        2*2*2pow         
                 end≡

    aux0 res@(log₂′ e pow 2pow pow≡2^e 2pow≡2*pow  
                    pow≤x x<2pow (no 1+x≢2pow)) =

              log₂′ 1+e 2pow 2*2pow 2pow≡2^[1+e] refl
                    2pow≤x' x'<2*2pow (no 1+x'≢2*2pow)
      where
      1+e = 1+ e;  2*2pow = 2* 2pow

      -- It holds  2^e ≤  x <  1+x ≤  2*2^e.

      open Log₂ res using (2pow≡2^[1+e]; 2pow≤2x)

      1+x≤2pow =  x<⇒suc-x≤ {x} {2pow} x<2pow
      1+x<2pow =  ≤,≢⇒< 1+x≤2pow 1+x≢2pow

      2pow≤x' = begin 2pow         ≤[ 2pow≤2x ]
                      2* x         ≤[ 2*-mono-≤ {x} {suc x} (x≤suc-x x) ]
                      2* (suc x)   ≡[ sym (2suc-as∘ x) ]
                      2suc x
                ∎

      x'<2*2pow =  begin 2suc x       ≡[ 2suc-as∘ x ]
                         2* (suc x)   <[ 2*-mono-< {suc x} {2pow} 1+x<2pow ]
                         2* 2pow
                   ∎

      1+x'≢2*2pow : suc x' ≢ 2*2pow
      1+x'≢2*2pow 1+x'≡2*2pow =  
                              suc2*-x≢2y (suc x) 2pow eq
             where
             eq = begin≡ suc2* (suc x)       ≡⟨ suc2*-as∘ (suc x) ⟩
                         suc (2* (suc x))    ≡⟨ cong suc (sym (2suc-as∘ x)) ⟩
                         suc (2suc x)        ≡⟨ refl ⟩
                         suc x'              ≡⟨ 1+x'≡2*2pow ⟩    
                         2*2pow
                  end≡ 

--------------
log₂ (suc2* x) _ =  aux (x ≟ 0#)
  where
  x' = suc2* x;   1+x = suc x;   2x = 2* x

  aux :  Dec (x ≡ 0#) → Log₂ x' 
  aux (yes x≡0) =  log₂′ 0 1# 2# refl refl 1≤x' x'<2 (yes 1+x'≡2)  -- x' ≡ 1#
                   where
                   x'≡1   = cong suc2* x≡0
                   1≤x'   = ≤-reflexive (sym x'≡1)
                   1<2    = suc2*<2suc 0#
                   x'<2   = subst (_< 2#) (sym x'≡1) 1<2
                   1+x'≡2 = cong (suc ∘ suc2*) x≡0

  aux (no x≢0) =  
    case  log₂ x x≢0
    of \ 
    { res@(log₂′ e pow 2pow pow≡2^e 2pow≡2*pow pow≤x x<2pow (yes 1+x≡2pow)) → 
         let 
           2*2pow = 2* 2pow

           open Log₂ res using (2pow≡2^[1+e]; 2pow≤2x) 

           suc-x≤2pow =  x<⇒suc-x≤ {x} {2pow} x<2pow

           2pow≤x' = begin 2pow         ≤[ 2pow≤2x ] 
                           2* x         ≤[ x≤suc-x (2* x) ] 
                           suc (2* x)   ≡[ sym (suc2*-as∘ x) ] 
                           suc2* x
                     ∎
           x'<2*2pow = 
              begin 
                suc2* x          ≡[ suc2*-as∘ x ] 
                suc (2* x)       ≡[ cong suc (2x≡x+x x) ]
                suc (x + x)      ≡[ sym (suc+assoc x x) ]
                (suc x) + x      <[ +-mono-≤-< {suc x} {2pow} {x} {2pow}
                                                       suc-x≤2pow x<2pow ]
                2pow + 2pow      ≡[ sym (2x≡x+x 2pow) ]
                2*2pow
              ∎

           -- x' = suc2*x,  1+x ≡ 2*2^e  ==>  x' ≡ 2*2*2^e.

           1+x'≡2*2pow : suc x' ≡ 2*2pow
           1+x'≡2*2pow =
                       begin≡ suc x'          ≡⟨ refl ⟩   
                              suc (suc2* x)   ≡⟨ cong suc (suc2*-as∘ x) ⟩   
                              suc (suc 2x)    ≡⟨ cong suc (suc≗1+ 2x) ⟩   
                              suc (1# + 2x)   ≡⟨ sym (suc+assoc 1# 2x) ⟩   
                              2# + 2x         ≡⟨ cong (_+ 2x) (sym (*1 2#)) ⟩
                              2* 1# + 2x      ≡⟨ sym (2*-distrib 1# x) ⟩   
                              2* (1# + x)     ≡⟨ cong 2* (sym (suc≗1+ x)) ⟩   
                              2* (suc x)      ≡⟨ cong 2* 1+x≡2pow ⟩
                              2* 2pow
                       end≡
         in
         log₂′ (1+ e) 2pow 2*2pow 2pow≡2^[1+e] refl 
               2pow≤x' x'<2*2pow (yes 1+x'≡2*2pow) 


    ; res@(log₂′ e pow 2pow pow≡2^e 2pow≡2*pow pow≤x x<2pow (no 1+x≢2pow)) →
         let 
           2*2pow = 2* 2pow

           open Log₂ res using (2pow≡2^[1+e]; 2pow≤2x)

           suc-x≤2pow =  x<⇒suc-x≤ {x} {2pow} x<2pow

           2pow≤x' = begin 2pow         ≤[ 2pow≤2x ] 
                           2* x         ≤[ x≤suc-x (2* x) ] 
                           suc (2* x)   ≡[ sym (suc2*-as∘ x) ] 
                           suc2* x
                     ∎
           x'<2*2pow = 
                begin suc2* x        ≡[ suc2*-as∘ x ] 
                      suc (2* x)     ≡[ cong suc (2x≡x+x x) ]
                      suc (x + x)    ≡[ sym (suc+assoc x x) ]
                      (suc x) + x    <[ +-mono-≤-< {suc x} {2pow} {x} {2pow}
                                                           suc-x≤2pow x<2pow ]
                      2pow + 2pow    ≡[ sym (2x≡x+x 2pow) ]
                      2* 2pow 
                ∎

           1+x'≢2*2pow : suc x' ≢ 2* 2pow
           1+x'≢2*2pow =
             (\ 1+x'≡2*2pow →
                 let
                   2[1+x]≡2*2pow =
                      begin≡ 
                        2* (suc x)       ≡⟨ cong 2* (suc≗1+ x) ⟩   
                        2* (1# + x)      ≡⟨ 2*-distrib 1# x ⟩   
                        (1# + 1#) + 2x   ≡⟨ +-assoc 1# 1# 2x ⟩   
                        1# + (1# + 2x)   ≡⟨ cong (1# +_) (sym (suc≗1+ 2x)) ⟩   
                        1# + (suc 2x)    ≡⟨ cong (1# +_) (sym (suc2*-as∘ x)) ⟩ 
                        1# + x'          ≡⟨ sym (suc≗1+ x') ⟩   
                        suc x'           ≡⟨ 1+x'≡2*2pow ⟩
                        2* 2pow
                      end≡

                   1+x≡2pow =  2*-injective 2[1+x]≡2*2pow
                 in
                 1+x≢2pow 1+x≡2pow
             )
         in
         log₂′ (1+ e) 2pow 2*2pow 2pow≡2^[1+e] refl
               2pow≤x' x'<2*2pow (no 1+x'≢2*2pow)  
    }



------------------------------------------------------------------------------
log₂! :  (x : Bin) → x ≢ 0# → ℕ 
log₂! x =  Log₂.e ∘ log₂ x 


------------------------------------------------------------------------------
log₂-irrel :  (x : Bin) → (nz nz' : x ≢ 0#) → log₂! x nz ≡ log₂! x nz'

-- irrelevance to the witness
log₂-irrel x nz nz' =  
  let 
    res@(log₂′ e  pow  2pow  pow≡2^e   2pow≡2*pow   pow≤x   x<2pow  _) = 
                                                                     log₂ x nz
    res'@(log₂′ e' pow' 2pow' pow'≡2^e' 2pow'≡2*pow' pow'≤x  x<2pow' _) = 
                                                                    log₂ x nz'
    x≡x = refl {A = Bin} {x = x}
    open Log₂ res  using (x<2^[1+e]; 2^e≤x)
    open Log₂ res' using () 
                   renaming (2^e≤x to 2^e'≤x; x<2^[1+e] to x<2^[1+e'])
  in
  case Nat0.compare e e' 
  of \ 
  { (tri≈ _    e≡e' _) → e≡e'      
  ; (tri< e<e' _    _) → let x<x = begin x           <[ x<2^[1+e] ]
                                         2* (2^ e)   ≤[ 2^-mono-≤ e<e' ]
                                         2^ e'       ≤[ 2^e'≤x ]
                                         x
                                   ∎   
                         in  contradiction x<x (<-irrefl x≡x)

  ; (tri> _ _ e>e') → let x<x = begin x           <[ x<2^[1+e'] ]
                                      2* (2^ e')  ≤[ 2^-mono-≤ e>e' ]
                                      2^ e        ≤[ 2^e≤x ]
                                      x
                                ∎   
                      in  contradiction x<x (<-irrefl x≡x)
  }


------------------------------------------------------------------------------
log₂!-mono-≤ : {x y : Bin} → (x≤y : x ≤ y) → (x≢0 : x ≢ 0#) → (y≢0 : y ≢ 0#) →
                                                    log₂! x x≢0 ≤' log₂! y y≢0

log₂!-mono-≤ {x} {y} x≤y x≢0 y≢0 = 
  let 
    res@(log₂′ e  pow  _     pow≡2^e   _            pow≤x  x<2pow  _) = 
                                                                    log₂ x x≢0
    res'@(log₂′ e' pow' 2pow' pow'≡2^e' 2pow'≡2*pow' pow'≤y y<2pow' _) = 
                                                                    log₂ y y≢0
    open Log₂ res  using (2^e≤x)
    open Log₂ res' using () renaming (x<2^[1+e] to y<2^[1+e'])
  in
  case Nat0.compare e e' 
  of \ 
  { (tri< e<e' _    _   ) → NatP.<⇒≤ e<e' 
  ; (tri≈ _    e≡e' _   ) → NatP.≤-reflexive e≡e' 
  ; (tri> _    _    e>e') → let y<x = begin y           <[ y<2^[1+e'] ]
                                            2^ (1+ e')  ≤[ 2^-mono-≤ e>e' ]
                                            2^ e        ≤[ 2^e≤x ]
                                            x
                                      ∎
                            in  contradiction x≤y (<⇒≱ {y} {x} y<x)
  }


------------------------------------------------------------------------------
log₂!∘2* :  (x : Bin) → (x≢0 : x ≢ 0#) → (2x≢0 : 2* x ≢ 0#) → 
                                       log₂! (2* x) 2x≢0  ≡  1+ (log₂! x x≢0)
-- log₂ 2x = 1+ (log₂ x)

log₂!∘2* x x≢0 2x≢0 = 
  let 
    2x = 2* x

    res@(log₂′ e  pow  2pow  pow≡2^e   2pow≡2*pow   pow≤x    x<2pow   _) = 
                                                                   log₂ x x≢0
    res'@(log₂′ e' pow' 2pow' pow'≡2^e' 2pow'≡2*pow' pow'≤2x  2x<2pow' _) = 
                                                                 log₂ 2x 2x≢0
    open Log₂ res  using (2^e≤x; 2pow≡2^[1+e])
    open Log₂ res' using () renaming (2^e≤x to 2^e'≤2x)

    2*pow'    =  2* pow'
    2x<2*pow' =  subst (2x <_) 2pow'≡2*pow' 2x<2pow'
    x<pow'    =  2*-back-mono-< {x} {pow'} 2x<2*pow'

    2^e<2^e' =  begin 2^ e      ≤[ 2^e≤x ] 
                      x         <[ x<pow' ]
                      pow'      ≡[ pow'≡2^e' ] 
                      2^ e'
                ∎
    e<e' =  ^-back-mono-< 2^e<2^e'
  in
  case  Nat0.compare (1+ e) e'
  of \ 
  { (tri≈ _      1+e≡e' _     ) → sym 1+e≡e'
  ; (tri> _      _      1+e>e') → contradiction e<e' (NatP.<⇒≱ 1+e>e')
  ; (tri< 1+e<e' _      _     ) → 
                 let 2*2pow≤2x = begin 2* 2pow       ≡[ cong 2* 2pow≡2^[1+e] ]
                                       2^ (2 +' e)   ≤[ 2^-mono-≤ 1+e<e' ]
                                       2^ e'         ≤[ 2^e'≤2x ] 
                                       2* x
                                 ∎
                     2pow≤x =  2*-back-mono-≤ {2pow} {x} 2*2pow≤2x
                 in
                 contradiction x<2pow (≤⇒≯ {2pow} {x} 2pow≤x)
  }




--============================================================================
-- A certain extension of  log₂  to zero argument.
-- For nonzero  x,  (ord x)  is  1+ (binary order of x)  

ord : Bin → ℕ
ord 0#        =  0
ord (2suc x)  =  1+ (log₂! (2suc x)  2suc≢0)
ord (suc2* x) =  1+ (log₂! (suc2* x) suc2*≢0)

ord-x≡0⇒x≡0 :  {x : Bin} → ord x ≡ 0 → x ≡ 0#
ord-x≡0⇒x≡0 {0#}      _ = refl
ord-x≡0⇒x≡0 {2suc _}  ()
ord-x≡0⇒x≡0 {suc2* _} ()

ord-x≤0⇒x≡0 :  {x : Bin} → ord x ≤' 0 → x ≡ 0#
ord-x≤0⇒x≡0 =
            ord-x≡0⇒x≡0 ∘ Nat0.≤0⇒≡

---------------------------------------------------------------------
ord-forNonzero :  {x : Bin} → (nz : x ≢ 0#) → ord x ≡ 1+ (log₂! x nz)

ord-forNonzero {0#}     0≢0 =  contradiction refl 0≢0
ord-forNonzero {2suc x} nz  =
  begin≡
    ord (2suc x)                ≡⟨ refl ⟩
    1+ (log₂! (2suc x) 2suc≢0)  ≡⟨ cong 1+_ (log₂-irrel (2suc x) 2suc≢0 nz) ⟩
    1+ (log₂! (2suc x) nz)
  end≡

ord-forNonzero {suc2* x} nz =
    begin≡
      ord (suc2* x)                  ≡⟨ refl ⟩
      1+ (log₂! (suc2* x) suc2*≢0)   ≡⟨ cong 1+_
                                          (log₂-irrel (suc2* x) suc2*≢0 nz) ⟩
      1+ (log₂! (suc2* x) nz)
    end≡

------------------------------------------------------
ord∘2* :  (x : Bin) → x ≢ 0# → ord (2* x) ≡ 1+ (ord x)
ord∘2* x x≢0 =
    begin≡ ord (2* x)                ≡⟨ ord-forNonzero 2x≢0 ⟩
           1+ (log₂! (2* x) 2x≢0)    ≡⟨ cong 1+_ (log₂!∘2* x x≢0 2x≢0) ⟩
           1+ (1+ (log₂! x x≢0))     ≡⟨ cong 1+_ (sym (ord-forNonzero x≢0)) ⟩
           1+ (ord x)
    end≡
    where
    2x≢0 = x≢0⇒2x≢0 x≢0

--------------------------------------
ord-mono-≤ :  ord Preserves _≤_ ⟶ _≤'_

ord-mono-≤ {x} {y} x≤y =  aux (x ≟ 0#) (y ≟ 0#)
  where
  aux :  Dec (x ≡ 0#) → Dec (y ≡ 0#) → ord x ≤' ord y
  aux (yes x≡0) _ =
                  ≤'begin ord x    ≡≤'[ cong ord x≡0 ]
                          0         ≤'[ z≤n ]
                          ord y
                  ≤'end
                  where
                  ord-x≡0 = cong ord x≡0

  aux (no x≢0) (yes y≡0) =  contradiction x≤y (<⇒≱ {y} {x} y<x)
                            where
                            y<x = begin y    ≡[ y≡0 ]
                                        0#   <[ ≢0⇒> x≢0 ]
                                        x
                                  ∎
  aux (no x≢0) (no y≢0) =
      ≤'begin
        ord x              ≡≤'[ ord-forNonzero x≢0 ]
        1+ (log₂! x x≢0)    ≤'[ s≤s (log₂!-mono-≤ x≤y x≢0 y≢0) ]
        1+ (log₂! y y≢0)   ≡≤'[ sym (ord-forNonzero y≢0) ]
        ord y
      ≤'end
