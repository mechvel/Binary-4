Announcement
============

  Binary-4 -- a Pure Binary Natural Number Arithmetic library for Agda

is available here on GitHub, 
and on 

     http://www.botik.ru/pub/local/Mechveliani/binNat/,


Binary-4  is a pure, regular-performance, complete, and certified 
          binary arithmetic for natural numbers written in Agda.

It has been tested under  Agda 2.5.4, MAlonzo, ghc-7.10.2.

It is also suggested as a replacement for the Bin part in
Standard library lib-0.16
(the modules Data.Bin.agda, Data.Bin.Properties.agda).


About other works on binary natural arithmetic 
==============================================

1. The library of 2013 by Arseniy Alekseyev:

      https://github.com/Rotsor/BinDivMod

It seems to have all the needed functionality and proofs. Only the code.
It uses different representation, different algorithms.

2. The library by Martin Escardo of 2016:

   http://www.cs.bham.ac.uk/~mhe/agda-new/BinaryNaturals.html

(only I do not see there divMod and gcd operations).



Thanks.  I am grateful to Arseniy Alekseyev for his notes and help.
=======



Changes in Binary-4 with respect to Binary-3.2
==============================================

* It has simpler proofs and simpler algorithms,
* It has a faster divMod operation in the case of small divisor values
  (this matter has been pointed out by Arseniy Alekseyev).

* It is used a different representation for Bin:

  data Bin : Set where

       0#    : Bin

       2suc  : Bin -> Bin    -- \n-> 2*(1+n)  arbitrary nonzero even

       suc2* : Bin -> Bin    -- \n-> 1 + 2n   arbitrary odd

* _<_ on Bin is defined defined by mapping to Nat 
  (similar as in Standard library).

* It is used a WellFounded recursion on Bin for termination proof for the 
  functiond  divMod and gcd.


Comments
========

`Pure'  
means that Binary-4 never uses a built-in arithmetic (on Nat) to 
essentially change performance.
The performance order is supposed to remain with replacing the Nat 
arithmetic with the naive unary arithmetic.

`Regular performance' 
means that the arithmetic on Bin of Binary-4 has a 
regular performance cost order -- the one expected for the corresponding 
known naive operations with bit lists.
At least this holds for  <-cmp, _+_, _-._, _*_, divMod, gcd.
Examples:
*  The comparison  <-cmp x y  on Bin costs  O(|x| + |y|),  
                                            where  |z| = bitLength z.

*  Division with remainder  divMod x y y/=0  on Bin costs  O( |x|^2 ).

`Complete'  
means that all the items are implemented that are usually required for 
standard arithmetic. There are provided the following items.

*  _<_ and _<=_ are defined by mapping to Nat,
*  DecTotalOrder instance for _<=_ on Bin,
*  StrictTotalOrder instance for  _<_ on Bin,
*  The bijection property for the map pair  toNat, fromNat. 
*  Subtraction _-._ on Bin,  with the main properties proved.
*  The proofs for isomorphism for _+_, _*_, _-._  for toNat, fromNat.
*  The monotonicity proofs for  toNat, fromNat  for _<=_ and Nat._<=_.
   A similar monotonicity for _<_ and Nat._<=_ are proved.
*  Various kinds of monotonicity for  _+_, _*_, _-._   for _<=_ and _<_  
   are proved.
*  The  CommutativeSemiring  instance  for Bin.
*  Binary logarithm for Bin, with its main properties proved. 
*  Division with remainder  and  GCD   for Bin.
*  The demonstration/test programs for  divMod and gcd.


`Certified'  means that everything is proved in Agda which is regularly 
             required of the above operations.


Usage of Standard library:  Bin  of Standard is _not used_.
--------------------------



Software base 
=============

Binary-4  has been tested under  Agda 2.5.4, MAlozo, ghc-7.10.2.

It also includes the module  LtReasoning.agda  -- a support for inequality 
reasoning by Ulf Norell.

Installation: 

              agda -c $agdaLibOpt GCDTest.agda

Performance tests:  

  LogarithmTest.agda, DivModTest.agda, GCDTest.agda
  ("readme"-s are included). 

Comments and improvements are welcome.

---------------------
Sergei D. Meshveliani
mechvel@botik.ru

