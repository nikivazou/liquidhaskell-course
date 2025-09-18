Programs are Proofs
============


\begin{code}
{- OPTIONS_GHC -fplugin=LiquidHaskell #-}
module Lecture_05_ProofsPrograms where

import Language.Haskell.Liquid.ProofCombinators
\end{code}

Each time you write a program, you are actually writing a proof.

What are the programs prooving? 
The [Curry-Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence), 
independently developed by Curry (1934) and Howard (1969), 
tells us that programs are proofs of theorems.

In this and the next lectures we will explore this correspondence in more detail 
and see how to use it to both write correct programs and prove theorems.


Each Program Proves its type
----------------------------

For example, an identity function on integers, `idInt`, 
is a proof that for all integers `x`, `idInt x` is also an integer.

\begin{code}
idInt :: Int -> Int
idInt x = x
\end{code}

The standard identity polymorphic function, `id`, is a proof that for all types `a`, `id x` is also of type `a`.

\begin{code}
id :: a -> a
id x = x
\end{code}

Polymorphism is very commonly used in _implicitely_ proving theorems 
about the programs, as described in [theorems for free](https://people.mpi-sws.org/~dreyer/tor/papers/wadler.pdf). 

Let's now try to to define a function that states that for each integer, 
there exists an `a`: 

\begin{code}
intToA :: Int -> a
intToA x = error "Define me!"
\end{code}

**Question:** Can you define the function above?

<details>

<summary>**Solution**</summary>

<p> _You can only define it using divergence (which is actually how Haskell's undefined is defined). 
But then you need a `lazy` annotation to deactivate the termination checker!_</p>

~~~~~{.spec}
intToA :: Int -> a
intToA x = intToA x

{-@ lazy intToA @-}
~~~~~

</details>




The only way to define the above function is via divergence. 
Thus, note that when a polymorphic type appears only in the result of your function,
then most probably your function is not terminating... 
The property that it is "proving" does not hold. 

Programs as proofs when they are _well formed_ meaning, 
they are terminating and total.

Propositions as Refinement Types
--------------------------------

In Liquid Haskell, we can write propositions as refinement types.
Concretely, we use refinement types to express theorems 
and define their Haskell functions as proofs of these theorems.

For example, below we prove that `1 + 1 = 2` by defining a function `onePlusOne`:

\begin{code}
{-@ onePlusOne :: () -> {v:() | 1 + 1 = 2 } @-}
onePlusOne :: () -> ()
onePlusOne _ = () 
\end{code}


The result of the function `onePlusOne` is just a unit. 
Thus the function has _no computational content_.
But, its result type is define to state a theorem. 
The proof of the theorem is  performed _just_ by the SMT solver 
that knows linear arithmetic.

Liquid Haskell come with the [proof combinators](https://hackage.haskell.org/package/liquidhaskell-0.8.0.5/docs/src/Language-Haskell-Liquid-ProofCombinators.html) 
library that allows to make the proofs more readable. 


As a first simplification step, Liquid Haskell allows to abbreviate the type 
`{v:T | p }` into just `{p}`, when `v` is not used in the type. 


\begin{code}
{-@ onePlusOne1 :: () -> { 1 + 1 = 2 } @-}
onePlusOne1 :: () -> ()
onePlusOne1 _ = () 
\end{code}


As a second simplification, the proof combinators library 
defines various functions that allow to make the proofs more readable.
For example, it define the following proof combinators:

~~~.{spec}
-- Defined at Language.Haskell.Liquid.ProofCombinators

type Proof = () -- Proof is just a unit

trivial :: Proof
trivial = ()

data QED = QED

(***) :: a -> QED -> Proof
_ *** _ = ()
~~~

With these, we can put the famous 

 > `QED`: quod erat demonstrandum (which was to be demonstrated) 

at the end of the proof.


\begin{code}
{-@ onePlusOne2 :: () -> { 1 + 1 = 2 } @-}
onePlusOne2 :: () -> Proof 
onePlusOne2 _ = trivial *** QED 
\end{code}


Thus, using the Proof Combinator library, in Liquid Haskell, 
we can prove, _for free_ theorems that the SMT knows how to prove.


**Question:** Can you name another trivial theorem that you can prove using Liquid Haskell?

\begin{code}
{-@ trivialThm :: () -> { true } @-}
trivialThm :: () -> Proof 
trivialThm _ = trivial *** QED 
\end{code}


<details>

<summary>**Solution**</summary>

<p> _Anothing that the SMT knows, for example boolean or linear logic:_</p>

~~~~~{.spec}
{-@ trivialThm :: () -> { false => false } @-}
~~~~~

</details>




Quantified Theorems
--------------------

Quantified theorems (e.g., $\forall x . \dots$) can also be expressed in Liquid Haskell, 
by using functional arguments as the universal quantifiers.

For example, we can prove that addition is commutative:

\begin{code}
{-@ propPlusAccum :: x:Int -> y:Int -> { x + y = y + x } @-}
propPlusAccum :: Int -> Int -> Proof
propPlusAccum x y = trivial *** QED
\end{code}

Note, function arguments work as universal quantifiers, 
and also, due to [currying](https://en.wikipedia.org/wiki/Currying), we use function abstraction to express existential quantifiers.


Theorems about Haskell Functions
--------------------------------

Next, we will see how we can use Liquid Haskell to prove theorems about Haskell functions.

To do so, first, we need to turn on the `reflection` flag of Liquid Haskell. 

\begin{code}
{-@ LIQUID "--reflection" @-}
\end{code}

This flag let us `reflect` Haskell functions into the predicate logic of Liquid Haskell.
For example, we can reflect the `fibonacci` function as follows:

\begin{code}
{-@ reflect fib @-}
{-@ fib :: Nat -> Nat @-}
fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n-1) + fib (n-2)
\end{code}

The `reflect` annotation: 

1. Generates a logical uninterpreted function `fib` that can be used in the predicates of Liquid Haskell.
2. Gives a singleton refinement type for `fib` that exactly captures the function definition. 

~~~.{spec}

{-@ fib :: n:Nat -> {v:Nat | v = fib n && 
  v = if n == 0 then 0 
      else if n == 1 then 1
      else fib (n-1) + fib (n-2) } @-}
~~~

Thus, now we can prove properties about the `fib` function.


\begin{code}
{-@ fibTwo :: () -> { fib 2 = 1 } @-}
fibTwo :: () -> Proof
fibTwo _ =   fib 2 
         === fib 1 + fib 0
         *** QED
\end{code}

where `===` is a proof combinator function used for equational reasoning 
(in the style of [Dafny's calculations](https://link.springer.com/chapter/10.1007/978-3-642-54108-7_9)).
It's type first checks that the first two arguments are equal 
and then returns the second, to keep working on the proof. 

~~~.{spec}
(===) :: x:a -> y:{a| x = y}   -> {v:a | v = y }
(=<=) :: x:a -> y:{a | x <= y} -> {v:a | v == y} 
(=>=) :: x:a -> y:{a | x >= y} -> {v:a | v == y}
~~~
Similarly, the `=<=` and `=>=` proof combinators are used for inequalities.


Reusing Proofs, the "because" combinator
----------------------------------------

Let's now prove that `fib 3 = 2`:

\begin{code}
{-@ fibThree :: () -> { fib 3 = 2 } @-}
fibThree :: () -> Proof
fibThree _ = undefined 
\end{code}

**Question:** Can you complete the proof above?

<details>

<summary>**Solution**</summary>

<p> _Using the because operator, the proof goes as follows:_</p>

~~~~~{.spec}
{-@ fibThree :: () -> { fib 3 = 2 } @-}
fibThree :: () -> Proof
fibThree _ =   fib 3 
           === fib 2 + fib 1 
           === fib 1 + fib 0 + 1
           === 1             + 1    
           === 2 
           *** QED 
~~~~~

</details>


If you have completed the proof you might have duplicated the proof of `fibTwo`.
In Liquid Haskell, we can reuse proofs by using the `because` combinator.
The proof combinators library defines the `because` combinator as follows:

~~~.{spec}
(?) :: a -> b -> a
x ? _ = x 
~~~

Thus, essentially introducing the it's second argument as a _fact_ in the proof.

**Question:** Let's now complete the proof of `fibThree` using the `because` combinator.


<details>

<summary>**Solution**</summary>

<p> _Using the because operator, the proof goes as follows:_</p>

~~~~~{.spec}
{-@ fibThree :: () -> { fib 3 = 2 } @-}
fibThree :: () -> Proof
fibThree _ =   fib 3 
           === fib 2 + fib 1 
             ? fibTwo () 
           === 1     + 1    
           === 2 
           *** QED 
~~~~~

</details>



Quantified Proofs
-----------------

Now that we have introduced all the vocabulary of the proof combinators library,
let's prove a more interesting theorem about the `fib` function.
Let's prove that `fib` is increasing. 

\begin{code}
{-@ fibUp :: n:Nat -> { fib n <= fib (n+1) } @-}
fibUp :: Int -> Proof
fibUp 0 =   fib 0 
        =<= fib 1
        *** QED
fibUp 1 =   fib 1 
        =<= fib 1 + fib 0
        =<= fib 2
        *** QED
fibUp n =   fib n 
        === fib (n-1) + fib (n-2)
        =<= fib n + fib (n-2) ? fibUp (n-1)
        =<= fib n + fib (n-2) 
        -- Complete the missing steps here
        =<= fib (n+1)
        *** QED
\end{code}

**Question:** Can you complete the proof above?


<details>

<summary>**Solution**</summary>

<p> _The missing steps are the following:_</p>

~~~~~{.spec}
        ? fibUp (n-2)
        =<= fib n + fib (n-1)
~~~~~

</details>



To simplify proofs, Liquid Haskell has a tactic, called 
`ple` (Proof by Logical Equivalence) that automates most 
equational reasoning steps, but still requires the case splitting and the 
lemma invocations. 

Thus, turning on the `ple` flag, we can simplify the proof of `fibUp`.
\begin{code}
{- LIQUID "--ple" @-}
\end{code}



Monotonicity of the Fibonacci Function
------------------------------------

Let's now prove that the Fibonacci function is monotonic: 

\begin{code}
{-@ fibMonotonic :: x:Nat -> y:{Nat | x < y } 
                 -> {fib x <= fib y} @-}
fibMonotonic :: Int -> Int -> Proof
fibMonotonic x y
  | y == x + 1
  =   fib x     ? () {- Call to the fibUp lemma goes here   -}
  =<= fib (x+1) 
  =<= fib y
  *** QED
  | x < y - 1
  =   fib x     ? () {- Inductive Hypothesis call goes here -}
  =<= fib (y-1) ? () {- Call to the fibUp lemma goes here   -}
  =<= fib y     
  *** QED
\end{code}


**Question:** Can you complete the proof above? 
Concretely, complete the missing calls to the `fibUp` lemma and the inductive hypothesis and the termination 
metric of the proof. 


<details>

<summary>**Solution**</summary>

<p> _The completed proof is the following. 
Note, that it requires a termination metric, since induction is on the second argument `y`:_</p>

~~~~~{.spec}
{-@ fibMonotonic :: x:Nat -> y:{Nat | x < y } 
                 -> {fib x <= fib y} / [y]@-}
fibMonotonic :: Int -> Int -> Proof
fibMonotonic x y
  | y == x + 1
  =   fib x     ? (fibUp x)            {- Call to the fibUp lemma goes here   -}
  =<= fib (x+1) 
  =<= fib y
  *** QED
  | x < y - 1
  =   fib x     ? fibMonotonic x (y-1) {- Inductive Hypothesis call goes here -}
  =<= fib (y-1) ? (fibUp (y-1))        {- Call to the fibUp lemma goes here   -}
  =<= fib y     
  *** QED
~~~~~

</details>





Generalizing the Monotonicity Proof
------------------------------------


Looking for closely at the monotonicity proof of the Fibonacci function,
we can see that the proof is not actually using the definition of the Fibonacci function, 
but only the fact that it is increasing.
Thus, we can turn the proof into a generic proof of the monotonicity of any function `f` that is increasing.

\begin{code}
{-@ fMonotonic :: f:(Nat -> Int) 
               -> fUp:(z:Nat -> {f z <= f (z+1)})
               -> x:Nat -> y:{Nat | x < y } -> {f x <= f y} / [y] @-}
fMonotonic :: (Int -> Int) -> (Int -> ()) -> Int -> Int -> Proof
fMonotonic f fUp x y
  | y == x + 1
  =   fib x     ? fibUp x
  =<= fib (x+1) 
  =<= fib y
  *** QED
  | x < y - 1
  =   fib x     ? fMonotonic f fUp x (y-1)
  =<= fib (y-1) ? fibUp (y-1)
  =<= fib y     
  *** QED
\end{code}

**Question:** Can you complete the proof above?

<details>

<summary>**Solution**</summary>

<p> _To complete, or better generalize, the proof you need to 
1) replace `fib` with `f` and `fibUp` with `fUp`, 
leading to the following proof:_</p>

~~~~~{.spec}
{-@ fMonotonic :: f:(Nat -> Int) 
               -> fUp:(z:Nat -> {f z <= f (z+1)})
               -> x:Nat -> y:{Nat | x < y } -> {f x <= f y} / [y] @-}
fMonotonic :: (Int -> Int) -> (Int -> ()) -> Int -> Int -> Proof
fMonotonic f fUp x y
  | y == x + 1
  =   f x     ? fUp x
  =<= f (x+1) 
  =<= f y
  *** QED
  | x < y - 1
  =   f x     ? fMonotonic f fUp x (y-1)
  =<= f (y-1) ? fUp (y-1)
  =<= f y     
  *** QED
~~~~~

</details>


Once we have the general (a.k.a. higher-order) proof
that increasing functions are monotonic, we can use it to prove the monotonicity of the Fibonacci function.

\begin{code}
{-@ fibMono  :: x:Nat -> y:{Nat | x < y } -> {fib x <= fib y} @-}
fibMono :: Int -> Int -> Proof
fibMono = fMonotonic fib fibUp
\end{code}


Proofs By Natural Induction
---------------------------

The proofs we did so far are essentially proofs by natural induction.


[Natural induction](https://en.wikipedia.org/wiki/Mathematical_induction)
is a proof technique that is used to prove theorems about natural numbers.
Concretely, it is used to prove that a property `P(n)` holds for all natural numbers `n`.
The proof consists of two steps:

1. **Base case**: Prove that `P(0)`  holds.
2. **Inductive step**: Prove that if `P(k)` holds for some `k`, then `P(k+1)` also holds.
3. **Conclusion**: Conclude that `P(n)` holds for all `n`.

For example, we can prove  the textbook theorem that the sum of the first `n` natural numbers is `n*(n+1)/2`. 

$$ P(n) = 1 + .... + n = n*(n+1)/2 $$

Let's prove it using Liquid Haskell.

For that, we first define the `sumTo` function that computes the sum of the first `n` natural numbers.

\begin{code}
{-@ reflect sumTo @-}
{-@ sumTo :: lo:Nat -> hi:{Nat | lo <= hi} -> Nat / [hi]@-}
sumTo :: Int -> Int -> Int 
sumTo lo hi = if lo == hi then 0 else hi + sumTo lo (hi-1) 
\end{code}

Next, we prove that the `sumTo` function is computing the sum of the first `n` natural numbers.

\begin{code}
{-@ sumToN :: n:Nat -> { sumTo 0 n = n * (n + 1) / 2 } @-}
sumToN :: Int -> Proof
sumToN = undefined 
\end{code}

**Question:** Can you complete the proof above? 
Hint, the Haskell function `div` is the integer division. 


<details>

<summary>**Solution**</summary>

<p> _The proof goes by induction and equational reasoning, 
where the logical `/` is `div`:_</p>

~~~~~{.spec}
{-@ sumToN :: n:Nat -> { sumTo 0 n = n * (n + 1) / 2 } @-}
sumToN :: Int -> Proof
sumToN 0 = sumTo 0 0 === 0 *** QED 
sumToN n = 
      sumTo 0 n 
  === n + sumTo 0 (n-1)
    ? sumToN (n-1)
  === n + (n-1) * n `div` 2 
  === n * (n + 1) `div` 2
  *** QED 
~~~~~

</details>




**Question:** Can you _embed_ this theorem in the type of the `sumTo` function?


<details>

<summary>**Solution**</summary>

<p> _Yes! This theorem can be part of the specification of `sumTo` if 
we refine its type signature to:_</p>

~~~~~{.spec}
{-@ sumTo :: lo:Nat -> hi:{Nat | lo <= hi} 
          -> {v:Nat | lo = 0 => v = hi * (hi+1) / 2 } / [hi]@-}
~~~~~

</details>



**Intrinsic vs Extrinsic Theorems:**
Instrinsic theorems are the thereoms that are part of the type signature of the function.
These theorems do not require explicit proofs, since the _definition_ 
of the function is already a proof of the theorem.
Extrinsic theorems are theorems that are not part of the type signature of the function, 
like the `fibMonotonic` theorem.
These theorems require explicit proof terms but they are more expressive, 
since they can encode properties that cannot be encoded or proved by the definition of the function.
Concretely, extrinsic theorems: 

- can relate different functions or different calls to the same function and 
- can encode theorems that require different proof techniques 
  (e.g., induction, case analysis, etc.).



Next, we will see how the concept of natural induction can be generalized to prove 
properties of data types as structural induction.



Summary
-------

In this lecture we have seen how to use Liquid Haskell to prove theorems about Haskell functions.
We have seen how to use the proof combinators library to make the proofs more readable, 
by expressing equational reasoning steps and the because operator. 
We saw that using the `reflection` flag we can turn Haskell functions into predicates of Liquid Haskell
and the `ple` flag we can simplify proofs.
Finally, we saw that proofs are higher-order functions that can be reused to prove other theorems.