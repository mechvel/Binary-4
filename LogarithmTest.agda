{-
This file is a part of the library  Binary-4.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.

Binary-4  is free software: you can redistribute it and/or modify it
under the terms of the GNU General Public License.
See  license.txt.
-}

module LogarithmTest where

open import Foreign.Haskell
open import IO.Primitive
open import Data.String using (String; toCostring)
                        renaming (_++_ to _++s_)
open import Function  using (_∘_)
open import Data.List using (List; []; _∷_; [_]; length; take; map)
open import Data.Nat  using (ℕ) renaming (suc to 1+_; _+_ to _+'_)
open import Data.Nat.Show using () renaming (show to showN)

-- of application ---
open import BPrelude  using (head; last; concatStr)
open import Bin0      using (Bin; pred; 2^; _+_; toℕ; fromℕ₁)
open import Ord0      using (downFrom)
open import Bits      using (showBin; stringToBin)
open import Logarithm using (ord)



--****************************************************************************
open Bin

sum : List ℕ → ℕ 
sum []       =  0
sum (x ∷ xs) =  x +' (sum xs)

showNats : List ℕ → String
showNats =  concatStr ∘ map (\n → "," ++s (showN n))

n = 1000

test :  ℕ → List String
test e =
       -- Print  sum [ord a .. ord a-n]  where a = 2^e.

       "e = "             ∷ showN e ∷
       "\na = 2^"         ∷ showN e ∷
       "\nn = "           ∷ showN n ∷
       "    length = "    ∷ showN (length [a--a-n]) ∷
       -- "\naHead = "       ∷ showBin aHead ∷
       "    oHead = "     ∷ showN oHead ∷
       -- "\naLast = "       ∷ showBin aLast ∷
       "    oLast = "     ∷ showN oLast ∷
       -- "\nords = \n"      ∷ showNats ords ∷
       "\ns = sum [ord a .. ord a-n] =  "   ∷ showN s ∷
       []
       where
       a        = 2^ e
       [a--a-n] = take n (downFrom a)

       ords = map ord [a--a-n]
       s    = sum ords 

       aHead = head 0# [a--a-n]
       aLast = last 0# [a--a-n]
       oHead = head 0 ords
       oLast = last 0 ords


main = (readFiniteFile "data.txt") >>= putStrLn ∘ toCostring ∘ g
       where
       g : String -> String
       g str = concatStr (test e)
               where
               e = toℕ (stringToBin str)


{- Readme -----------------------------------------------------------------

Appending  0  to the string in  data.txt  makes |a| twice as much.
The time growth of computing `main' shows the order of the evaluation cost
of  (log₂ x)   relatively to |x| = bitLenth x.
(Other operations in the loop cost O(|a|).

Timing for  Agda 2.5.4, ghc-7.10.2, Debian Linux, 3 GHz machine:

  e    |  time [sec]
---------------------
  2048 |   0.12
  4096 |   0.3
  8192 |   1.0
 16384 |   4.1
 32768 |   9.8
 65536 |  23.5
131072 |  49.8

This shows that the cost of  ord x  is  close to linear in (bitLength x). 
-------------------------------------------------------------------------
-}