Refinement Types 
==================================================

Add "dependent types" to _existing programming languages_! 


Typed languages can say 

 > 42 is an Int

 > "Madrid" is a String

Refinement typed languages can say

  > 42 is an Non Zero Int, 42 : {v:Int | v != 0}

  > "Madrid" is a Non Empty String, "Madrid" : {v:String | len v > 0}


Refimenet Types exist in many languages, e.g.,

- [Flux](https://github.com/flux-rs/flux) for Rust 
- [Stainless](https://epfl-lara.github.io/stainless/) for Scala 
- [Liquid Java](https://catarinagamboa.github.io/liquidjava.html) for Java
- [Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell/) for Haskell


Liquid Haskell
----------------

Liquid Haskell is a refinement type checker for Haskell! 

You can run it 

- in the browser (e.g., using this link), 
- in the command line (after installation from [Hackage](https://hackage.haskell.org/package/liquidhaskell)
or [github](https://github.com/ucsd-progsys/liquidhaskell)), or
- as a GHC plugin (`-fplugin=LiquidHaskell`).

You can use it in two modes:  

- to _automatically_ prove light program properties (e.g., no division by zero) or 
- to _manually_ prove deep program properties (e.g., correctness of `mapReduce`). 

Let's how it works!

This is a Haskell module that you can run in your browser:

\begin{code}
module HaskellMeetup where

import Prelude hiding (take, drop)
\end{code}


Basic Types 
----------------

Liquid Haskell comes with refinement types for various built in Haskell functions. 
For example, division by zero is not allowed:

~~~{.spec}
{-@ div :: Integral a => x:a -> {v:a | v != 0} -> a @-}
~~~

Refinement Types, like `{v:a | v != 0}`, are here, 
Haskell types refined with _logical predicates_ 
(over booleans, linear arithmetic, uninterpreted functions, etc.).

_Notation:_ We use the `{-@ ... @-}` special comments 
for _refinement type annotations_. (These comments are parsed by Liquid Haskell.)

Each call to `div` will check that the second argument is not zero.

\begin{code}

test0 :: Int -> Int 
test0 x = 42 `div` 0

\end{code}

Note, the check is _automatically_ performed by an external 
SMT solver (Z3 by default). 

Concretely, refinement types are using the SMT to check subtyping. 
For the `0` case, the subtyping check is:

~~~{.spec}
        forall v. v = 0 => v != 0
    --------------------------------
  {v:Int | v = 0 } <: {v:Int | v != 0}    0:{v:Int | v = 0 }
 -------------------------------------------------------------
                0 :: {v:Int | v != 0} 
~~~

The SMT rejects the implication, thus type checking fails! 

For the `2` case, the subtyping succeeds:

~~~{.spec}
        forall v. v = 2 => v != 0
    --------------------------------
  {v:Int | v = 2 } <: {v:Int | v != 0}    0:{v:Int | v = 2 }
 -------------------------------------------------------------
                2 :: {v:Int | v != 0} 
~~~


Pre- and Post-Conditions
------------------------

Refinement types are used to specify function's 
requirements, i.e., _preconditions_ and 
guarantees, i.e.,  _postconditions_.

For example, we can give `take` a type that says that

- if the index `i` is in bounds, 
- then the result is a list of length `i`.

~~~{.spec}
{-@ take :: i:Nat -> xs:{[a] | i < len xs} -> {v:[a] | len v = i} @-}
~~~

Now let's use `take`:

\begin{code}

test1 :: [Int] -> Int -> [Int]
test1 xs i = take i xs

\end{code}

The type error here is telling us what is wrong. 
Let's first use a runtime check to fix it! 
Next, let's replace the runtime check with a Liquid Haskell refinement type.
Finally, let's strengthen the refinement type to allow us to divide `42` with 
all the elements we took. 


This example revealed many unique features of verification with Liquid Haskell. 
It is:

1. _path sensitive_, i.e., runtime checks can be used to guide the verification, 
2. _type based_, i.e., we can specify behaviors of collection of data, and 
3. _SMT automated_, i.e., there is no need for user explicit proofs.  



Recursive Functions
--------------------

Let's now define the `take` function.

\begin{code}
{-@ take :: i:Nat -> xs:{[a] | i < len xs}
         -> {v:[a] | len v = i} @-}
take :: Int -> [a] -> [a]
take = undefined 
\end{code}

When defining a function, 
Liquid Haskell requires both the refined and unrefined types.
(GHC does not see the refinement types, which are provided as comments.)
But, for each function Liquid Haskell checks that is 
_total_ (i.e., all cases are covered) 
and _terminating_ (i.e., recursive call is on a smaller input)
 (which can be deactivated with the 
 `--no-totality` and  `--no-termination` flags respectively).  


Dually, let's define the `drop` function.

\begin{code}
{-@ drop :: i:Nat -> xs:{[a] | i < len xs} -> [a] @-}
drop :: Int -> [a] -> [a]
drop = undefined 
\end{code}


Using `take` and `drop` we can now define the `chunk` function that splits a list into chunks of size `i`.

\begin{code}

chunk :: Int -> [a] -> [[a]]
chunk i xs | length xs <= i || i <= 1 
  = [xs]
chunk i xs 
  = take i xs : chunk i (drop i xs)
\end{code}

Liquid Haskell gives a termination error! 
Does `chunk` terminate? 


To show termination we need to 
1. define a _termination metric_ and
2. refine the postcondition of `drop`! 


Summary
-------
We saw how to use Liquid Haskell to _automatically_
prove light program properties, i.e., division by zero and safe indexing. 
Such verification is _path sensitive_, _type based_, and _SMT automated_.
For more information, check out the Liquid Haskell 
[documentation](https://ucsd-progsys.github.io/liquidhaskell/),
[tutorial](https://ucsd-progsys.github.io/liquidhaskell-tutorial/), and 
[github](https://github.com/ucsd-progsys/liquidhaskell). 

Next, we will see how Liquid Haskell can be used to manually prove properties about 
Haskell functions.
For example, can we now prove that `take` and `drop` reconstruct the original list?

~~~{.spec}
forall i. xs.  xs == take i xs ++ drop i xs 
~~~

Yes, using [deep verification](https://nikivazou.github.io/utrecht/TheoremProving.html)! 
