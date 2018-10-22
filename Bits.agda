{-
This file is a part of the library  Binary-4.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.

Binary-4  is free software: you can redistribute it and/or modify it
under the terms of the GNU General Public License.
See  license.txt.
-}

module Bits where

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List          using (List; []; _∷_; map; reverse)
open import Data.String as Str using (String)
open import Data.Char          using (Char)
open import Data.Digit         using (Bit)
open import Data.Fin as Fin    using (Fin; zero) renaming (suc to 1+_)
open import Data.Nat           using (ℕ)

-- of application --- 
open import Bin0 using (Bin; 2*; fromℕ₁)



--****************************************************************************
pattern 0b = zero
pattern 1b = 1+ zero
pattern ⊥b = 1+ 1+ ()

open Bin

-- The second Bin representation is  List Bit,  where less significant bits 
-- are set ahead.
-- It is used only for printing and for interface with Bin of Standard 
-- library. 

fromBits : List Bit → Bin
fromBits []        = 0#
fromBits (0b ∷ bs) = 2* (fromBits bs)
fromBits (1b ∷ bs) = suc2* (fromBits bs)
fromBits (⊥b ∷ _) 

add1 : List Bit → List Bit
add1 []        =  1b ∷ []
add1 (0b ∷ bs) =  1b ∷ bs
add1 (1b ∷ bs) =  0b ∷ (add1 bs)
add1 (⊥b ∷ _)

toBits : Bin → List Bit
toBits 0#        =  []
toBits (2suc x)  =  0b ∷ add1 (toBits x)
toBits (suc2* x) =  1b ∷ (toBits x)

toBitsR = reverse ∘ toBits

------------------------------------------------------------------------------
bitToChar : Bit → Char 
bitToChar 0b = '0'
bitToChar 1b = '1'
bitToChar ⊥b 

showBits : List Bit → String
showBits =  
         Str.fromList ∘ map bitToChar

showBitsR : List Bit → String
showBitsR =  
          Str.fromList ∘ map bitToChar ∘ reverse

showBin : Bin → String
showBin = showBits ∘ toBitsR


test0 : -- showBin (fromℕ₁ 0) ≡ ""
        -- showBin (fromℕ₁ 1) ≡ "1"
        -- showBin (fromℕ₁ 2) ≡ "10"
        -- showBin (fromℕ₁ 3) ≡ "11"
        -- showBin (fromℕ₁ 4) ≡ "100"
        showBin (fromℕ₁ 5) ≡ "101"
test0 = refl


------------------------------------------------------------------------------
-- Reading a string to Bin. 

charsToBits : List Char → List Bit    -- it also fiters out non-digits
charsToBits []         =  []
charsToBits ('0' ∷ cs) =  0b ∷ (charsToBits cs)
charsToBits ('1' ∷ cs) =  1b ∷ (charsToBits cs)
charsToBits (_   ∷ cs) =  charsToBits cs


stringToBin : String → Bin
stringToBin = fromBits ∘ charsToBits ∘ reverse ∘ Str.toList

test1 : -- showBin (stringToBin "") ≡ ""
        -- showBin (stringToBin "1") ≡ "1"
        -- showBin (stringToBin "10") ≡ "10"
        -- showBin (stringToBin "11") ≡ "11"
        -- showBin (stringToBin "100") ≡ "100"
        showBin (stringToBin "101") ≡ "101"

test1 = refl
