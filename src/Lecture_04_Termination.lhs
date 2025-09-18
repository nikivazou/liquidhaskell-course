Termination 
============


\begin{code}
{- OPTIONS_GHC -fplugin=LiquidHaskell #-}
module Lecture_04_Termination where

import Prelude hiding (map, gcd, mod)

main :: IO ()
main = return ()
\end{code}


By default Liquid Haskell checks that every function terminates.
This is required for two reasons:

1. Termination is the _expected behavior_ for most functions. 
So, many times potential non-termination is a bug.
2. Termination is _required_ for the [soundness](https://dl.acm.org/doi/10.1145/2628136.2628161) of the type system.

Up to now, we were deactivating the termination checker with the `--no-termination` flag 
or with the `lazy` annotation. 
Now, we will see how to prove termination in cases where Liquid Haskell cannot do it automatically.


Termination Requires Refinements! 
----------------------------------

We start with the known fibonacci function.

\begin{code}
{-@ fib :: i:Int -> Int  @-}
fib :: Int -> Int
fib i | i == 0    = 0 
      | i == 1    = 1 
      | otherwise = fib (i-1) + fib (i-2)
\end{code}

Liquid Haskell will create an error in the above definition, even though 
it does not violate any refinement type specification. 

*This is a termination error* and it will disappear if we 
turn off termination checking (either with `--no-termination` pragma or with `{-@ lazy fib@-}` annotation).

**Question:** Does `fib` terminate?

<details>

<summary>**Solution**</summary>

<p> _Yes, but only when the input is a natural number.
This would also require the result of `fib` to be a natural number. 
Thus, to ensure termination you need the following specification of `fib`:_</p>

~~~~~{.spec}
{-@ fib :: i:Nat -> Nat  @-}
~~~~~

</details>

To ensure `fib` terminates we need to restrict the input to be non-negative.
This is actually implied by the error message that requires 
the recursive argument to be `0 <= v` and `v < i`. 

This error was generated because Liquid Haskell was trying to prove termination of the function 
`fib` by applying its termination heuristic.

*Termination Heuristic:* 
The first argument that can be "sized", i.e., turned into `Nat`, 
should be decreasing in recursive calls and non negative.

`Int` is by default "size" while later we will see how to make other types "sized".


Termination Metrics 
--------------------

The heuristic fails in many cases. 
For example, consider the function `range` that generates a list of integers from `lo` to `hi`.

\begin{code}
{-@ range :: lo:Int -> hi:Int -> [Int] @-} 
range :: Int -> Int -> [Int]
range lo hi
 | lo < hi = lo : range (lo+1) hi
 | otherwise = []
\end{code}

**Question:** Does `range` terminate?

<details>

<summary>**Solution**</summary>

<p> _Yes, because the difference `hi - lo` is decreasing in recursive calls.
Thus, to ensure termination you need the following specification of `range`:_</p>

~~~~~{.spec}
{-@ range :: lo:Int -> hi:Int -> [Int] / [hi - lo] @-} 
~~~~~

</details>



The termination heuristic fails because the first argument is not decreasing in recursive calls.
To specify that the value `hi - lo` is decreasing we need to introduce a termination metric:

~~~.{spec}
{-@ range :: lo:Int -> hi:Int -> [Int] / [hi - lo]@-} 
~~~

Termination metrics are integer expressions that can depend on the function arguments 
and once provided, Liquid Haskell will use them to check termination. 
Concretely, at each recursive call it will check that the termination metric 
is both decreasing and non-negative.


Lexicographic Termination
--------------------------

Many times a single natural number is not enough to specify termination.
For example, consider the ackermann function:

\begin{code}
{-@ ack :: m:Int -> n:Int -> Int  @-} 
ack :: Int -> Int -> Int
ack m n
  | m == 0 = n + 1
  | n == 0 = ack (m-1) 1
  | otherwise = ack (m-1) (ack m (n-1))
\end{code}

**Question:** Does `ack` terminate?

<details>

<summary>**Solution**</summary>

<p> _Yes, because either `m` is decreasing, 
or `m` is the same and `n` is decreasing.
This is a lexicographic termination metric and can be encoded as `[m,n]`. 
But, we need to ensure that `m` and `n` are non-negative, 
which in turn requires the result of `ack` to be non-negative.
Thus, to ensure termination you need the following specification of `ack`:_</p>

~~~~~{.spec}
{-@ ack :: m:Nat -> n:Nat -> Nat  / [m, n] @-} 
~~~~~

</details>

To show that `ack` terminates we need to provide a lexicographic termination metric.
Now at each recursive call, Liquid Haskell will check that the first component of the metric is decreasing
and if it is equal, it will check the second component, etc.


The GCD Example
----------------

The Greater Common Divisor (gcd) function is an interesting example, 
because it might or not require lexicographic termination. 

The gcd of two numbers (which is not both zero) is the largest positive integer
that divides both numbers. 
For example, the gcd of 8 and 12 is 4.


- **GCD with Lexicographic Termination:**

The [Euclidean algorithm](https://en.wikipedia.org/wiki/Euclidean_algorithm)
for computing the gcd of two numbers 
is based on the principle that the greatest common divisor 
of two numbers does not change if the larger number is replaced 
by its difference with the smaller number:


\begin{code}
{-@ gcd :: a:Int -> b:Int -> Int @-}
gcd :: Int -> Int -> Int
gcd 0 b = 0 
gcd a 0 = a 
gcd a b | a == b = a
        | a >  b = gcd (a - b) b 
        | a <  b = gcd a (b - a) 
\end{code}

For example, 
`gcd 8 12 = gcd 8 4 = gcd 4 4 = 4`.

**Question:** Provide the proper lexicographic termination metric for the below `gcd` function.
<details>

<summary>**Solution**</summary>

<p> _The metric is `[a,b]`. 
Either `a` is decreasing or it remains the same and `b` is decreasing. 
Thus, to ensure termination you need the following specification of `gcd`:_</p>

~~~~~{.spec}
{-@ gcd :: a:Nat -> b:Nat -> Nat / [a, b]@-}
~~~~~

</details>


- **GCD with Semantic Termination:**

An alternative definition of `gcd` is using 
the modulo operator.
Instead of directly use the difference of the two numbers, 
`ghc a b` is using the `mod` to remove from `a` 
as many `b`s as possible: 


\begin{code}
{-@ gcdMod :: a:Nat -> b:Nat -> Int @-}
gcdMod :: Int -> Int -> Int
gcdMod a 0 = a
gcdMod a b = gcdMod b (a `mod` b)


{-@ mod :: a:Nat -> b:Nat -> Nat @-}
mod :: Int -> Int -> Int
mod a b
  | a < b = a
  | otherwise = mod (a - b) b
\end{code}

For example, 
`gcdMod 12 8 = gcdMod 8 4 = gcdMod 4 0 = 4`, 
because `mod 12 8 = 4` and `mod 8 4 = 0`.

Interestingly, termination does not require any explicit metrics, 
but follows from the semantics of the functions. 
That means, that if you properly refine the functions,
termination will be guaranteed.


**Question:** Refine properly the `gcd` and `mod` functions to ensure termination.
<details>

<summary>**Solution**</summary>

<p> _Termination is ensured by the following specifications:_</p>

~~~~~{.spec}
{-@ gcdMod :: a:Nat -> b:{Nat | b < a} -> Nat @-}
{-@ mod :: a:Nat -> b:{Nat | b /= 0} -> {v:Nat | v < b} @-}
~~~~~

</details>


Data Types 
------------
When recursive functions are defined on data types, 
Liquid Haskell will first look for _structural termination_, 
meaning that the recursive calls are on a structural subpart of the input.
For example, the `map` definition below terminates because 
`xs` is a subpart of `x:xs`.

\begin{code}
{-@ map :: (a -> b) -> xs:[a] -> [b]  @-}
map :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (x:xs) = f x : map f xs 
\end{code}


Of course, not all recursive functions on data types 
are structurally terminating. 
As an example consider the `merge` function below, that is usually part of 
[merge sort](https://en.wikipedia.org/wiki/Merge_sort) algorithm. 

\begin{code}
{-@ merge :: xs:[a] -> ys:[a] -> [a] @-}
merge :: Ord a => [a] -> [a] -> [a]
merge xs []   = xs
merge [] ys   = ys
merge (x:xs) (y:ys) 
  | x < y     = x:(merge xs (y:ys))
  | otherwise = y:(merge ys (x:xs))
\end{code}

**Question:** Let's prove `merge` terminating using a termination metric.

<details>

<summary>**Solution**</summary>

<p> _Termination is ensured by the following specifications:_</p>

~~~~~{.spec}
{-@ merge :: xs:[a] -> ys:[a] -> [a] / [len xs + len ys]@-}
~~~~~

</details>


**Question:** Let's also show that `merge` propagates sortedness, 
by refining the inputs and output to be IList: 

\begin{code}
{-@ type IList a = [a]<{\h t -> h <= t}>  @-}
\end{code}

<details>

<summary>**Solution**</summary>

<p> _Sortedness is ensured by the following specifications:_</p>

~~~~~{.spec}
{-@ merge :: xs:IList a -> ys:IList a -> IList a / [len xs + len ys]@-}
~~~~~

</details>





User Defined Data Types 
------------------------

In user defined data types, Liquid Haskell tries to prove structural termination. 
For example, mapping over a list defined as a user defined data type 
will not require a termination metric.


\begin{code}
data List  a = Nil | Cons a (List a) 

lmap :: (a -> b) -> List a -> List b
lmap _ Nil         = Nil
lmap f (Cons x xs) = Cons (f x) (lmap f xs)
\end{code}

The user can provide a _size_ for each user defined data type. 
Here, for example, we define the size of a `List` to be the length of the list.

\begin{code}
{-@ data List [llen]  @-}

{-@ measure llen @-}
{-@ llen :: List a -> Nat @-}
llen :: List a -> Int 
llen Nil = 0 
llen (Cons _ xs) = 1 + llen xs 
\end{code}

Now, when structural termination fails, 
Liquid Haskell will use the size of the data type to check termination.
For example, note the termination error provided in the `lmerge` function below.

\begin{code}
lmerge :: Ord a => List a -> List a -> List a 
lmerge xs Nil = xs
lmerge Nil ys = ys 
lmerge (Cons x xs) (Cons y ys) 
  | x < y     = Cons x (lmerge xs (Cons y ys))
  | otherwise = Cons y (lmerge (Cons x xs) ys)
\end{code}

Like with the Haskell's lists, to ensure termination we need to provide a termination metric.
In this case, the termination metric is the size of the `List` data type: 

~~~~~{.spec}
{-@ lmerge :: xs:List a -> ys:List a -> List a / [llen xs + llen ys] @-}
~~~~~



Mutual Recursion
----------------

Two functions are mutually recursive if they call each other.
In such cases, Liquid Haskell will not attempt to prove termination automatically.
Instead, the user needs to provide termination metrics.
For example, consider the `isEven` and `isOdd` functions below.

\begin{code}
{-@ isEven :: n:Nat -> Bool @-}
{-@ isOdd  :: m:Nat -> Bool @-}

isEven :: Int -> Bool
isEven 0 = True
isEven n = isOdd (n-1)

isOdd :: Int -> Bool
isOdd m = not $ isEven m
\end{code}

**Question:** Provide the proper termination metrics for the `isEven` and `isOdd` functions.
<details>

<summary>**Solution**</summary>

<p> _The termination metrics can be the following:_</p>

~~~~~{.spec}
{-@ isEven :: n:Nat -> Bool / [n, 0]@-}
{-@ isOdd  :: m:Nat -> Bool / [m, 1]@-}
~~~~~

</details>

Note that at the definition of `isOdd m`, the recursive argument 
remains the same. Thus, _something_ should decrease! 
We define the termination metric `[m, 1]` for `isOdd` to ensure that the 
second component is decreasing. In the definition of `isEven n`, 
the recursive argument decreases, so the second component of the termination metric 
is irrelevant. 



This pattern of providing numeric values for lexicographic termination metrics
appears very often in mutually recursive functions. 
For example, the below code is a simplification of a real world example
and follows the same pattern.

**Question:** Provide the proper termination metrics for the `eval` and `evalAnd` functions? 

\begin{code}

data BExpr = Const Bool | And BExpr BExpr

{-@ measure size @-}
size :: BExpr -> Int
{-@ size :: BExpr -> Nat @-}
size (Const _)   = 0
size (And e1 e2) = 1 + size e1 + size e2

{-@ eval :: e:BExpr -> Bool @-}
eval :: BExpr ->  Bool
eval (Const b)   = b
eval (And b1 b2) = evalAnd b2 (eval b1)

{-@ evalAnd :: e:BExpr -> Bool -> Bool  @-}
evalAnd :: BExpr -> Bool -> Bool
evalAnd b2 x1 = if x1 then (eval b2) else False 

\end{code}


<details>

<summary>**Solution**</summary>

<p> _The termination metrics can be the following:_</p>

~~~~~{.spec}
{-@ eval :: e:BExpr -> Bool / [size e, 0] @-}
{-@ evalAnd :: e:BExpr -> Bool -> Bool / [size e, 1] @-}
~~~~~

</details>




Summary
--------

Liquid Haskell, by default, checks that every function terminates.
It has three mechanisms to prove termination:

1. _Structural Termination_: for recursive functions on data types, 
    Liquid Haskell will check that the recursive calls are on a subpart of the input.
    If this check fails, either because the function is not defined on a data type or because
    the recursive calls are not on a subpart of the input, then there are two more mechanisms.
2. _Termination Heuristic_: the first argument that can be "sized" should be decreasing 
    and non negative in recursive calls.
3. _Termination Metrics_: user provided, integer expressions that can depend on the function arguments
    and are used to check termination.

The `--no-termination` flag or the `{-@ lazy @-}` annotation can be used to deactivate the termination checker, 
either because the user is not willing to prove termination or because the functions 
are intentionally non-terminating.