Structural Induction 
============


\begin{code}
{- OPTIONS_GHC -fplugin=LiquidHaskell #-}
module Lecture_06_StructuralInduction where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (map, id, length, return, (++), reverse)
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ infixr ++ @-}
\end{code}

We already saw how to prove properties on integers using induction on natural numbers. 
Next, we will see how to prove properties on algebraic data types using structural induction.

As expected, we will prove properties of functions that manipulate the 
most common algebraic data type, lists. 


Structural Induction on Lists
-----------------------------

Next, we define and reflect two functions, `map` and `id`, 
that we will use to illustrate structural induction on lists.

\begin{code}
{-@ reflect map @-}
map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x:map f xs

{-@ reflect id @-}
id :: a -> a
id x = x
\end{code}

The first property we will prove is that 
mapping the identity function over a list is the same as the identity over the list.

This property can be used as an optimization pass, in the right hand side, 
the list is not traversed by map! 

\begin{code}
{-@ idMap :: xs:[a] -> {map id xs == id xs} @-}
idMap :: [a] -> Proof
idMap []
  =  map id []
  === []
  === id []
  *** QED 
idMap (x:xs) 
  =   map id (x:xs)
  === id x:map id xs ? idMap xs
  === x:id xs
  === x:xs   
  === id (x:xs)
  *** QED
\end{code}

The proof goes by _structural induction_ on the list the list `xs`.

- The _base case_ is when `xs` is `[]`, which goes by rewriting.
- The _inductive case_ is when `xs` is `x:xs`, which goes by rewriting and the induction hypothesis.

Note that Liquid Haskell checks both that both cases are defined (by totality) 
and that the inductive call is well-founded (by termination).

As before, `ple` can be used to automate the proof. 
We essentially need to keep the case splitting and the induction hypothesis.


Map Fusion 
-----------

Next, we will prove that mapping two functions over a list is the same as 
mapping the composition of the functions over the list.

For this we define the composition of two functions.

\begin{code}
{-@ reflect comp @-}
comp :: (b -> c) -> (a -> b) -> a -> c
comp f g x = f (g x)
\end{code}

**Question:** Let's prove map fusion.

\begin{code}
{-@ mapFusion :: f:(b -> c) -> g:(a -> b) -> xs:[a] 
              -> {map (comp f g) xs == (map f) (map g xs)} @-}
mapFusion :: (b -> c) -> (a -> b) -> [a] -> Proof
mapFusion f g xs = undefined 
\end{code}

Monoid Laws for Lists 
----------------------

Lists form a monoid structure, in that they have an associative binary operation (list append)
and a neutral element (empty list):

\begin{code}
{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys 
(x:xs) ++ ys = x:(xs++ys)

{-@ reflect empty @-}
empty :: [a]
empty = []
\end{code}

Monoid structures have three laws: associativity, left identity and right identity.
So, let's prove these laws for lists.

- Left Identity: `empty` is the left identity for `append`.

\begin{code}
emptyLeftIdentity :: [a] -> Proof 
{-@ emptyLeftIdentity :: xs:[a] -> {[] ++ xs == xs} @-}
emptyLeftIdentity xs = undefined
\end{code}

- Right Identity: `empty` is the right identity for `append`.

\begin{code}
emptyRightIdentity :: [a] -> Proof 
{-@ emptyRightIdentity :: xs:[a] -> {xs ++ [] == xs} @-}
emptyRightIdentity xs = undefined
\end{code}

- Associativity: `append` is associative.

\begin{code}
appendAssoc :: [a] -> [a] -> [a] -> Proof 
{-@ appendAssoc :: xs:[a] -> ys:[a]-> zs:[a] 
                 -> {xs ++ (ys ++ zs) == (xs ++ ys) ++ zs} @-}
appendAssoc xs ys zs = undefined
\end{code}


Using Proved Lemma
-------------------

As a final example, let's define list reversing 
and prove that reverse distributes over append.

\begin{code}
{-@ reflect reverse @-}
reverse :: [a] -> [a]
reverse []     = []
reverse (x:xs) = reverse xs ++ [x]
\end{code}



**Question:** Let's prove distributivity. 
Hint, you can use the proved lemmas `emptyRightIdentity` and `appendAssoc`.

\begin{code}
distributivity :: [a] -> [a] -> () 
{-@ distributivity :: xs:[a] -> ys:[a] 
                   -> { reverse (xs ++ ys) == reverse ys ++ reverse xs }  @-}
distributivity = undefined 
\end{code}

Liquid Haskell has a (beta) tactic that allows the proof to get automated 
using existing equations proved in lemmas. 
Thus the proof can be automated as follows:

~~~.{spec}
{-@ rewriteWith distributivity [appendAssoc, emptyRightIdentity] @-}
~~~


Summary
-------

We saw how to use Liquid Haskell to encode proofs of structural induction on lists.
We proved the functor and monoid laws for lists and distributivity of reverse over append, 
using the two Liquid Haskell tactics of `ple` and `rewriteWith`.





