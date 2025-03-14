Deep Verification 
==================================================

Let's now use Liquid Haskell to prove theorems about Haskell functions! 
To do so, we need to activate two flags: `--reflection` and `--ple`.

\begin{code}
module TheoremProving where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ infix ++ @-}
import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (take, drop, (++), map, sum, length)
\end{code}

Equational Proofs 
--------------------------------------------------

The `--reflection` flag allows us to 
reflect Haskell functions into logic, that is we can then use them in refinements. 

\begin{code}
{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)
\end{code}


Now that `++` is reflected, we can use it in the refinements 
and prove theorems about append! 

Let's prove right identity: 

\begin{code}
{-@ rightId :: xs:[a] -> {v:() | xs ++ [] == xs } @-}
rightId :: [a] -> () 
rightId = undefined 
\end{code}

The theorem is a unit type (i.e., has no computational content)
but it is refined to curry the proof statement. 
We can simplify the statement by removing the unit type 
and the value `v`, when they are not required. 

The proof is an inhabitant of the theorem and 
is implemented using functions from the 
[proof combinators](https://hackage.haskell.org/package/liquidhaskell-0.8.0.5/docs/src/Language-Haskell-Liquid-ProofCombinators.html) 
library. 

Most of the equational steps can be simplified by 
PLE ([Proof by Logical Evaluation](https://dl.acm.org/doi/10.1145/3158141))!


Let's now prove the take-drop reconstruction property 
(`take` and `drop` are defined as before, but now reflected!)


\begin{code}
{-@ appendTakeDrop :: i:Nat -> xs:{[a] | i <= len xs} ->
     {xs == (take i xs) ++ (drop i xs) }  @-}
appendTakeDrop :: Int -> [a] -> () 
appendTakeDrop = undefined

\end{code}


MapReduce Definition 
--------------------------------------------------

As a bigger example, let's look into the `mapReduce` function.

The goal is to apply a function `f` to a list of elements. 
But instead of applying it directly, we first chunk the list into smaller lists of size `n`, 
then apply `f` to each chunk, and finally reduce the results using an operator `op`.

\begin{code}
{-@ reflect mapReduce @-}
mapReduce :: Int -> ([a] -> b) -> (b -> b -> b) -> [a] -> b 
mapReduce n f op is = reduce op (f []) (map f (chunk n is))

{-@ reflect reduce @-}
reduce :: (a -> a -> a) -> a -> [a] -> a 
reduce op b []     = b 
reduce op b (x:xs) = op x (reduce op b xs) 

{-@ reflect map @-}
map :: (a -> b) -> [a] -> [b]
map _  []    = []
map f (x:xs) = f x:map f xs 

{-@ reflect chunk @-}
chunk :: Int -> [a] -> [[a]]
\end{code}



Map Reduce Example Client: 
--------------------------------------------------

As an example, we can use `mapReduce` to define a function `psum` 
that "in parallel" computes the sum of a list of integers.

\begin{code}    
{-@ reflect sum @-}
sum  :: [Int] -> Int 
sum []        = 0 
sum (x:xs) = x `plus` sum xs

{-@ reflect plus @-}
plus :: Int -> Int -> Int 
plus x y = x + y 

{-@ reflect psum @-}
psum :: Int -> [Int] -> Int 
psum n is = mapReduce n sum plus is 
\end{code}


 > Question: Is `psum` equivalent to `sum`?




Proving Code Equivalence: `sum` and `psum`
------------------------------------------

The equivalence proof is an instance of the higher order theorem `mRTheorem`: 

\begin{code}
{-@ sumEq :: n:Int -> is:[Int] -> { sum is == psum n is } @-}
sumEq :: Int -> [Int] -> ()
sumEq n is = mRTheorem   n           -- chunk size
                         sum         -- function to map-reduce
                         plus        -- reduction operator
                         plusRightId -- plus has "right-identity"
                         sumDistr    -- sum is "distributive"
                         is          -- input list
\end{code}



where `plusRightId` and `sumDistr` are 
the right-identity and distributive properties of `plus` and `sum` respectively
and are proved by induction.

\begin{code}
{-@ plusRightId :: xs:[Int] 
                -> { plus (sum xs) (sum []) == sum xs } @-}
plusRightId :: [Int] -> ()
plusRightId []     = ()
plusRightId (x:xs) = plusRightId xs

{-@ sumDistr :: xs:[Int] -> ys:[Int] 
             -> { sum (xs ++ ys) == plus (sum xs) (sum ys) } @-}
sumDistr :: [Int] -> [Int] -> ()
sumDistr []     _  = ()
sumDistr (x:xs) ys = sumDistr xs ys
\end{code}




Higher Order Map Reduce Theorem 
--------------------------------------------------

The higher order mapReduce theorem is also proved by 
induction calling the take-drop reconstruction property in the inductive case: 

\begin{code}
{-@ mRTheorem :: n:Int -> f:([a] -> b) -> op:(b -> b -> b)
     -> rightId:(xs:[a] -> {op (f xs) (f []) == f xs } ) 
     -> distrib:(xs:[a] -> ys:[a] 
                        -> {f (xs ++ ys) == op (f xs) (f ys)} )
     -> is:[a]
     -> { mapReduce n f op is == f is }
     / [len is]
  @-}
mRTheorem :: Int -> ([a] -> b) -> (b -> b -> b) -> ([a] -> ()) -> ([a] -> [a] -> ()) -> [a] -> ()
mRTheorem n f op rightId _ []
  = rightId []

mRTheorem n f op rightId _ is@(_:_)
  | n <= 1 || length is <= n 
  = rightId is

mRTheorem n f op rightId distrib is 
  = mRTheorem n f op rightId distrib (drop n is)
  ? distrib (take n is) (drop n is)
  ? appendTakeDrop n is 
\end{code}



Summary
--------------------------------------------------

Liquid Haskell can be used to prove theorems about Haskell functions.
The theorems are expressed as refinements of the unit type and
the proofs are Haskell functions that inhabit the theorems.
Even though the proofs are not automatic, 
they can be simplified using PLE and the proof combinators library.




Missing Code
--------------------------------------------------

\begin{code}
{-@ chunk :: i:Int -> xs:[a] 
          -> [[a]] 
           / [len xs] @-}
chunk i xs 
  | i <= 1 || length xs <= i 
  = [xs] 
  | otherwise
  = take i xs:chunk i (drop i xs)


{-@ reflect length @-}
{-@ length :: xs:[a] -> {v:Nat | v == len xs} @-}
length :: [a] -> Int 
length []     = 0
length (_:xs) = 1 + length xs

{-@ reflect drop @-}
{-@ drop :: i:Nat -> xs:{[a] | i <= len xs } -> {v:[a] | len v == len xs - i } @-}
drop :: Int -> [a] -> [a]
drop i [] = []
drop i (x:xs)
  | i == 0 
  = x:xs  
  | otherwise 
  = drop (i-1) xs 

{-@ reflect take @-}
{-@ take :: i:Nat -> xs:{[a] | i <= len xs } -> {v:[a] | len v == i} @-} 
take :: Int -> [a] -> [a]
take i [] = []
take i (x:xs)
  | i == 0 
  = []
  | otherwise 
  = x:take (i-1) xs
\end{code}
