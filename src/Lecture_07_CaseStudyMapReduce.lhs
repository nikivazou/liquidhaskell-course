Case Study: Map Reduce 
============


\begin{code}
{- OPTIONS_GHC -fplugin=LiquidHaskell #-}
module Lecture_07_CaseStudyMapReduce where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ infix ++ @-}
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (map, take, drop, sum, (++), length)
\end{code}



Map Reduce Explained
--------------------

[MapReduce](https://en.wikipedia.org/wiki/MapReduce) is a programming model 
for processing and generating big data sets with a parallel, distributed algorithm on a cluster. 
Let's explain it here as a way to parallelize sandwich making.

Map reduce is a function that

1. chunks the input,
2. maps a function over the chunks in parallel, and
3. reduces the results to a single value.

<div class="marginfigure"
     id="fig:avl"
     height="300px"
     file="img/map-reduce.jpg"
     caption="MapReduce to make sandwich.">
</div>


Map Reduce "Library" Functions:
-----------------------------

The Haskell definitions of `mapReduce` functions, reflected: 


\begin{code}
{-@ reflect mapReduce @-}
mapReduce :: Int -> ([a] -> b) -> (b -> b -> b) -> [a] -> b
mapReduce n f op is = reduce op (f []) (map f (chunk n is))

{-@ reflect reduce @-}
reduce :: (a -> a -> a) -> a -> [a] -> a
reduce op b []     = b
reduce op b (x:xs) = op x (reduce op b xs)

{-@ reflect map @-}
{-@ map :: (a -> b) -> xs:[a] -> {v:[b] | len v == len xs } @-}
map :: (a -> b) -> [a] -> [b]
map _  []    = [] 
map f (x:xs) = f x : map f xs

-- chunk :: Int -> [a] -> [[a]]
\end{code}

Of course, for `mapReduce` to be efficient the `map` function should be parallelized, 
e.g., using [`parMap`](https://hackage.haskell.org/package/parallel-3.2.2.0/docs/Control-Parallel-Strategies.html).





Map Reduce "Client" Functions: Summing a List 
-------------------------------------------

Let's assume that `sum` is the standard list summing 
and `psum` is the mapReduce parallel summing. 

\begin{code}
-- Standard List Sum
{-@ reflect sum @-}
sum :: [Int] -> Int
sum []     = 0
sum (x:xs) = x + sum xs

-- Parallel Sum
{-@ reflect psum @-}
psum :: Int -> [Int] -> Int
psum n is = mapReduce n sum plus is 

-- Reduction Operator
{-@ reflect plus @-}
plus :: Int -> Int -> Int
plus x y = x + y
\end{code}

Can we prove that `sum` and `psum` are equivalent?



Proving Code Equivalence: `sum` and `psum`
------------------------------------------

The equivalence proof is an instance of the higher order theorem `mRTheorem`: 

\begin{code}
{-@ sumEq :: n:Int -> is:[Int] -> { sum is == psum n is } @-}
sumEq n is = mRTheorem   n           -- chunk size
                         sum         -- function to map-reduce
                         plus        -- reduction operator
                         plusRightId -- plus has "right-identity"
                         sumDistr    -- sum is "distributive"
                         is          -- input list
\end{code}





Chunk Definition: 
-----------------

First, let's define the `chunk` function that splits a list into chunks of size `n`.

**Question:** Define the `take` and `drop` functions below that satisfy 
the following specifications:

\begin{code}
{-@ reflect drop @-}
{-@ drop :: i:Nat -> xs:{[a] | i <= len xs } 
         -> {v:[a] | len v == len xs - i } @-}
drop :: Int -> [a] -> [a]
drop i x = x 
\end{code}

\begin{code}
{-@ reflect take @-}
{-@ take :: i:Nat -> xs:{[a] | i <= len xs } 
         -> {v:[a] | len v == i} @-}
take :: Int -> [a] -> [a]
take i x = x  
\end{code}


**Question:** Define the `chunk` function below that splits a list into chunks of size `n`.

\begin{code}
{-@ reflect chunk @-}
chunk :: Int -> [a] -> [[a]]
chunk i x = [x] 
\end{code}


<details>

<summary>**Solution**</summary>

<p> _The functions `take`, `drop`, and `chunk` can be defined as follows:_</p>

~~~~~{.spec}
drop :: Int -> [a] -> [a]
drop 0 x = x 
drop i (x:xs) = drop (i-1) xs 

take 0 _ = []
take i (x:xs) = x : take (i-1) xs

{-@ chunk :: Int -> x:[a] -> [[a]] / [len x] @-}
chunk :: Int -> [a] -> [[a]]
chunk i x 
  | i <= 0 || length x <= i = [x]
  | otherwise = take i x : chunk i (drop i x)
~~~~~

</details>









Higher Order Theorem: `mRTheorem`
------------------------------------------




The higher order theorem `mRTheorem` states that: 

 > If `f` is right identity and `op` is distributive, then `mapReduce` is equivalent to sequential.

\begin{code}
{-@ mRTheorem :: n:Int -> f:([a] -> b) -> op:(b -> b -> b)
     -> rightId:(xs:[a] -> {op (f xs) (f []) == f xs } )
     -> distrib:(xs:[a] -> ys:[a] -> {f (xs ++ ys) == op (f xs) (f ys)} )
     -> is:[a]
     -> { mapReduce n f op is == f is }
     / [len is]
  @-}
mRTheorem :: Int -> ([a] -> b) -> (b -> b -> b) -> ([a] -> Proof) -> ([a] -> [a] -> Proof) -> [a] -> Proof
mRTheorem n f op rightId distrib is = undefined 
\end{code}

**Question:** What is the proof of `mRTheorem`?


<details>

<summary>**Solution**</summary>

<p> _The function `mRTheorem` can be defined as follows:_</p>

~~~~~{.spec}
mRTheorem n f op rightId distrib is 
  | n <= 0 || length is <= n 
  =   mapReduce n f op is 
  === reduce op (f []) (map f (chunk n is))
  === reduce op (f []) [f is]
  ? rightId is
  === f is 
  *** QED 

mRTheorem n f op rightId distrib is  
  =   mapReduce n f op is 
  === reduce op (f []) (map f (chunk n is))
  === reduce op (f []) (map f (take n is : chunk n (drop n is)))
  === reduce op (f []) (f (take n is) : map f (chunk n (drop n is)))
  ===  op (f (take n is)) (reduce op (f []) (map f (chunk n (drop n is))))
  ? mRTheorem n f op rightId distrib (drop n is)
  === op (f (take n is)) (f (drop n is))
  ? distrib (take n is) (drop n is)
  === f (take n is ++ drop n is)
   ? takeDrop n is
  === f is   
  *** QED  

takeDrop :: Int -> [a] -> Proof
{-@ takeDrop :: i:Nat -> xs:{[a] | i <= len xs }
             -> {take i xs ++ drop i xs == xs} @-}
takeDrop 0 xs     = ()
takeDrop n (_:xs) = takeDrop (n-1) xs
~~~~~

</details>





Lemmata for `mRTheorem` on plus 
------------------------------------------



\begin{code}
plusRightId :: [Int] -> Proof
{-@ plusRightId :: xs:[Int] 
                -> {plus (sum xs) (sum []) == sum xs} @-}
plusRightId = undefined 
\end{code}

**Question:** What is the proof of `plusRightId`?

<details>

<summary>**Solution**</summary>

<p> _The function `plusRightId` can be defined as follows:_</p>

~~~~~{.spec}
plusRightId []     = ()
plusRightId (x:xs) = plusRightId xs 
~~~~~

</details>




\begin{code}
sumDistr :: [Int] -> [Int] -> Proof
{-@ sumDistr :: xs:[Int] -> ys:[Int] 
             -> {sum (xs ++ ys) == plus (sum xs) (sum ys)} @-}
sumDistr xs = undefined 
\end{code}

**Question:** What is the proof of `sumDistr`?


<details>

<summary>**Solution**</summary>

<p> _The function `sumDistr` can be defined as follows:_</p>

~~~~~{.spec}
sumDistr [] ys = ()
sumDistr (x:xs) ys = sumDistr xs ys  
~~~~~

</details>


Summary 
--------

We saw a case study in which map reduce is used to parallelize the sum of a list.
Using Liquid Haskell, we can prove that the parallel sum is equivalent to the sequential sum.









Appendix: List Manipulation Functions
---------------------------

We define the list manipulation functions `++` and `length` below.
\begin{code}
{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)

{-@ reflect length @-}
{-@ length :: xs:[a] -> {v:Nat | v == len xs } @-}
length :: [a] -> Int
length []     = 0
length (_:xs) = 1 + length xs
\end{code}