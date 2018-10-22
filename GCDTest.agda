module GCDTest where

open import Foreign.Haskell
open import IO.Primitive
open import Data.String using (String; toCostring)

open import Function  using (_∘_)
open import Data.List using (List; []; _∷_; [_]; length; reverse; take; 
                                                         zipWith; filter)
open import Data.Nat      using (ℕ) 
open import Data.Nat.Show using () renaming (show to showN)

-- of application ---
open import BPrelude using (concatStr; head; last) 
open import Bin0     using (Bin; 1#; pred; _+_; sum; 2^; toℕ) 
open import Ord0     using (downFrom) 
open import GCD      using (gcd!) 
open import Bits     using (showBin; stringToBin) 



--****************************************************************************
open Bin

n : ℕ
n = 2000

testBin : ℕ → List String    -- for  gcd  on Bin
testBin e =

  -- Print  sum [gcd! x y | (x , y) <- zip [a-n .. a] [a .. a-n]]
  --        where a = 2^e.
  --
  -- The the number of  gcd!  calls is a constant  n;
  -- the bit length of the arguments for  gcd!  is proportional to  e.

  "e   : ℕ    = "                  ∷ showN e ∷  
  "\na : Bin  = "                  ∷ showBin a ∷  
  "\nnumber of results  : ℕ  = "   ∷ showN (length gcds) ∷ 
  "\nnumber of unit gcd  : ℕ  = "  ∷ showN (length units) ∷ 
  "    gSum: ℕ  = "                ∷ showBin (sum gcds) ∷
  "\ngHead = "                     ∷ showBin gHead ∷
  "    gLast = "                   ∷ showBin gLast ∷ 
  []
  where
  a : Bin
  a = 2^ e

  [a--a-n] = take n (downFrom a)
  gcds     = zipWith gcd! (reverse [a--a-n]) [a--a-n]
  gHead    = head 0# gcds 
  gLast    = last 0# gcds
  units    = filter (Bin0._≟_ 1#) gcds 

main = (readFiniteFile "data.txt") >>= putStrLn ∘ toCostring ∘ g
       where
       g : String -> String
       g str = concatStr (testBin e)
               where
               e = toℕ (stringToBin str)


{- Readme --------------------------------------------------------------------

Example:   putting   1001  to  data.txt  means that  

* e = 9,  a = (2# ^ 9)  : Bin

* testBin  finds and prints out the value
  sum [gcd! x y | (x, y) = (a-n, a), (a-n+1, a-1), (a-n+2, a-2) ... (a, a-n)]. 

Appending 0 to the string for  e  in data.txt increases  e  twice,
and increases twice the bit length of the arguments for  gcd!.

Timing for  Agda 2.5.4, ghc-7.10.2, Debian Linux, 3 GHz machine:

  e  | time [sec]
------------------
 32  |  0.2
 64  |  0.5
128  |  2.0
256  |  8.1
512  | 34
------------------------------------------------------------------------------

The  gcd  version with the counter for termination proof is about 10 %
faster. 
-}