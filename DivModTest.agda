{-
This file is a part of the library  Binary-4.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.

Binary-4  is free software: you can redistribute it and/or modify it
under the terms of the GNU General Public License.
See  license.txt.
-}

module DivModTest where

open import Foreign.Haskell
open import IO.Primitive
open import Data.String using (String; toCostring) renaming (_++_ to _++s_)

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.List using (List; []; _∷_; [_]; map; take; length)
open import Data.Nat        using (ℕ) renaming (suc to 1+_)
open import Data.Nat.Show   using ()  renaming (show to showN)
open import Data.Nat.DivMod using ()
                        renaming (DivMod to DivModN; _divMod_ to _divModN_)
import Data.Fin as Fin

-- of application ---
open import BPrelude using (head; last; concatStr)
open import Bin0     using (Bin; suc; pred; _+_; sum; 2^; toℕ; fromℕ₁)
open import Ord0     using (downFrom)
open import OfDivMod using (DivMod; divMod)
open import Bits     using (showBin; stringToBin)



--****************************************************************************
open Bin

showBins : List Bin → String 
showBins = concatStr ∘ map (\x → "," ++s (showBin x))

showNats : List ℕ → String 
showNats = concatStr ∘ map (\x → "," ++s (showN x))


testN : ℕ → (dr : ℕ) → List String
testN dd dr =
            let (DivModN.result q rF _) =  dd divModN (1+ dr)
                r = Fin.toℕ rF
            in
            "dd = "  ∷ showN dd  ∷ "   dr = " ∷ showN (1+ dr) ∷
            "\nq = " ∷ showN q   ∷ "   r = "  ∷ showN r       ∷ []


rem : Bin → (y : Bin) → y ≢ 0# → Bin
rem x y =
        DivMod.remainder ∘ (divMod x y)

b : Bin 
b = fromℕ₁ 5

b≢0 : b ≢ 0#
b≢0 ()

n = 1000  -- Edit it.  It is the number of calls of  rem.

testB :  ℕ → List String
testB e =
        -- Print  sum [rem x b | x <- [a .. (a - n)]]  where a = 2^e.

        "e : ℕ = "             ∷ showN e ∷  
        "\na = 2^"             ∷ showN e ∷ " : Bin" ∷  
        "\nb : Bin = "         ∷ showBin b ∷
        "\nn : ℕ = "           ∷ showN n ∷
        "\nlength : ℕ = "      ∷ showN (length [a--a-n]) ∷
        -- "\nrems =\n"      ∷ showBins rems ∷
        "\nsum rems : Bin = "  ∷ showBin (sum rems) ∷
        "\nheadRem = "         ∷ showBin rHead ∷
        "    lastRem = "       ∷ showBin rLast ∷ 
        []
        where
        a        = 2^ e
        [a--a-n] = take n (downFrom a)
        rems     = map (\x → rem x b b≢0) [a--a-n]
        rHead    = head 0# rems
        rLast    = last 0# rems

main = (readFiniteFile "data.txt") >>= putStrLn ∘ toCostring ∘ g
       where
       g : String -> String
       g str = concatStr (testB e)
                         -- test ddN drN
               where
               e = toℕ (stringToBin str)


{- Readme ----------------------------------------------------------------

testB  shows the order of the evaluation cost for  divMod a' b relatively 
       to the  bit length |a'|  of  a'  where  a'  is near  a
       (the test takes the values  a' = a, a-1, ..., a-n).

Appending  0  to the string in data.txt makes |a| twice as much. 
The time growth of computing `main' shows the order of the evaluation cost 
of  divMod a b  relatively to |a|.
(Other operations in the loop cost O(|a|).

Timing for  Agda 2.5.4, ghc-7.10.2, Debian Linux, 3 GHz machine: 

  e    | time [sec]
------------------
   256 |   0.03
   512 |   0.06
  1024 |   0.12
       |
  4096 |   0.6
       |
 16384 |   3.0 
 32768 |   6.5
 65536 |  12,8
131072 |  25.2
-------------------------------------------------------------------------
 
It shows that  (divMod a 5)  costs O( |a| ).

Theorem.   n > 1 →  rem (2^(2^n)) 5 =  1.  
~
∀ n (5 | (2^(4*2^n) - 1)).   
-}

