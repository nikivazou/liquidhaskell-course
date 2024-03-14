Refinement Types 
============

Refinement types are types refined with logical predicates
that enforce a variety of invariants at compile time. 
In this course, we will learn the refinement type system 
of Liquid Haskell. 


If you follow this course via a brouser, 
you can just click the check button that exists on the code spinnets 
to run Liquid Haskell on your file. 
If you follow it on an editor, then compile the code using the Haskell compiler 
and turn on the `Liquid Haskell plugin``, but uncommenting the following line:

\begin{code}

{- OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--no-termination" @-}
module Lecture_01_RefinementTypes where

main :: IO ()
main = return ()
\end{code}

Either way, you can now use the `Liquid Haskell` type checker,
for example to check that division by zero is not possible.

\begin{code}
test :: Int -> Int
test x = 42 `div` 2
\end{code}

If we call `div` with zero, directly or even indirectly via the `x` argument, 
then at runtime we will get a division by zero error.

~~~~~{.ghci}
ghci> test 0
*** Exception: divide by zero
~~~~~

Liquid Haskell comes with a refined type for the division operator 
that specified that the second argument must be non-zero.

~~~~~{.spec}
div :: Int -> {v:Int | v /= 0} -> Int
~~~~~

The above type specifies that the second argument must be non-zero
and is automatically checked at compile time, using an SMT solver.
Today, we will learn how these checks are performed, and how to
write and use refined types in Haskell.


Installation 
---------------

Liquid Haskell exists on [hackage](https://hackage.haskell.org/package/liquidhaskell),
which is the Haskell package repository, so you can install it using 
`cabal`, `stack`, or instal it from source: 

- [`cabal install liquidhaskell`](https://ucsd-progsys.github.io/liquidhaskell/install/)
will install the Liquid Haskell plugin that you can use in your Haskell projects.
- [Source installation](https://github.com/ucsd-progsys/liquidhaskell?tab=readme-ov-file#running-the-pluging-on-individual-files)
will let you clone Liquid Haskell from github and install it. 


The source code of these class notes can also be downloaded and executed 
from [github](https://github.com/nikivazou/liquidhaskell-course)^[
  These notes are adjusted from the [Liquid Haskell Tutorial](https://ucsd-progsys.github.io/liquidhaskell-tutorial/).
]  


**Note:** This is the first time I am giving these lectures, 
so I would appreciate any feedback you might have, via the virtual classroom, 
pull requests, or email at `niki.vazou@imdea.org`.


Basic Refinement Types
----------------------

Did you note that `2` is a good argument for the division operator? 

But, what is the type of `2`?



In Haskell `2:Int`, but the same value can have many different refinement types. 
A basic refinement type has the form 

$$ \{ v:b \mid p \} $$
where $b$ is the base type (e.g., `Int`, `Bool`, etc.) and $p$ is a logical predicate.

For example, the logical predicate that refines the type of `2` can have many different forms: 

\begin{code}

{-@ type Two      = {v:Int | v == 2}  @-}
{-@ type FortyTwo = {v:Int | v == 42} @-}
{-@ type NZero    = {v:Int | v /= 0}  @-}
{-@ type Pos      = {v:Int | v >  0}  @-}
{-@ type Neg      = {v:Int | v <  0}  @-}
{-@ type Nat      = {v:Int | 0 <= v}  @-}


two :: Int
two = 2 
\end{code}

**Question:** What are good types for `two`? 

**Question:** Can you find more types for `two`?



Subtyping 
----------
So, what is the type of `2`? 
In Liquid Haskell, integers and other constants, e.g., booleans, characters, etc.,
are given a _singleton type_, meaning a type that has only one value.
So, the typing rule for integers is:


$$ 
\inferrule{\texttt{T-Int}}{}{\Gamma \vdash i : \{ \texttt{Int} \mid v = i \}}
$$

In an unrefined system this would be _the only_ type for `2`. 
But refinement types have the notion of _subtyping_, which can give an expression 
many different types. 

The rule for subtyping is the following:

$$
\inferrule
  {\texttt{T-Sub}}
  {
  \Gamma \vdash e : \tau_1 \quad 
  \Gamma \vdash \tau_1 \preceq \tau_2
  }{
  \Gamma \vdash e : \tau_2
  }
$$

This rule states that in an expression, like $2$, that has type $\tau_1$
and $\tau_1$ is a subtype of $\tau_2$, then $2$ can also have type $\tau_2$.

So, $2 : \{ \texttt{Int} \mid 0 \leq v \}$, 
because $\{ \texttt{Int} \mid v = 2  \} \preceq \{ \texttt{Int} \mid 0 \leq v \}$. 
But, let's see how subtyping is decided. 



From Subtyping to Verification Conditions 
-----------------------------------------

The subtyping rule for base types, e.g., integers, booleans, etc.,
is the following:

$$
\inferrule
  {\texttt{Sub-Base}}
  {
   \Gamma \vdash \forall v:b. p_1 \Rightarrow p_2
  }{
  \Gamma \vdash \{ v:\texttt{b} \mid p_1 \} \preceq \{ v:\texttt{b} \mid p_2 \}
  }
$$

Meaning that $\{ v:\texttt{b} \mid p_1 \} \preceq \{ v:\texttt{b} \mid p_2 \}$,
if $p_1$ "implies" $p_2$ for all values $v$ of type $\texttt{b}$.
To check implications, we use the below two implication rules 
that are based on the SMT solver^[
  SMT stands for Satisfiability Modulo Theories and are automated tools that 
  check the satisfiability of logical formulas. 
  Known SMT solvers are Z3, CVC5, etc. 
].


$$
\inferrule
  {\texttt{I-Emp}}
  {
    \texttt{SmtValid}(c)
  }{
    \emptyset \vdash c 
  }
\qquad 
\inferrule
  {\texttt{I-Ext}}
  {
    \Gamma \vdash \forall x.  p \Rightarrow c 
  }{
    \Gamma, x:\{ x:\texttt{b} \mid p \} \vdash c 
  }
$$




**Example:**
When we check that $2$ is indeed a natural number, the following 
derivation takes place 

$$
\inferrule
  {\texttt{T-Sub}}
  {
    \inferrule
    {\texttt{T-Int}}
    {}
    {\emptyset \vdash 2 : \{v: \texttt{Int} \mid 2 = v \}}
    \quad
    \inferrule
    {\texttt{Sub-Base}}
    { 
      \inferrule
      {\texttt{I-Emp}}
      {\texttt{SmtValid} (\forall v:\texttt{Int}. 2 = v \Rightarrow 0 \leq v)}
      {
      \emptyset \vdash \forall v:\texttt{Int}. 2 = v \Rightarrow 0 \leq v
      }
    }
    {\emptyset \vdash \{v: \texttt{Int} \mid 2 = v \} \preceq \{v: \texttt{Int} \mid 0 \leq v \}}
  }
  {\emptyset \vdash 2 : \{v: \texttt{Int} \mid 0 \leq v \}}
$$

So, the type derivation succeeds, because the SMT can indeed decide 
that the implication $2 = v \Rightarrow 0 \leq v$ is valid.

In general, we call such implications _verification conditions_
and the main task of a refinement type checker is to 
reduce the type checking problem to validity of verification conditions.


Verification Conditions
-----------------------
Liquid Haskell takes great care to ensure that type checking is decidable and efficient. 
To achieve this, it has to be careful to generate verification conditions that are
decidable and efficiently checkable by the SMT solver. 
The rules $\texttt{Sub-Base}$ and $\texttt{I-Ext}$, presented above, 
are the main rules that generate verification conditions from the predicates 
found in the refinement types.
Below is the syntax of the predicates and verification conditions: 

$$
\begin{array}{r r c l l}
\textbf{Predicates} & p & ::=  & x, y, z & \textit{variables} \\
                             &   & \mid & \text{true}, \text{false} & \textit{booleans} \\
                             &   & \mid & 0, -1, 1, \dots           & \textit{numbers} \\
                             &   & \mid & \lnot p, p_1 \land p_2, p_1 \lor p_2 & \textit{boolean operators} \\
                             &   & \mid & p_1 = p_2      & \textit{equality} \\
                             &   & \mid & p_1 + p_2, p_1 - p_2, \dots & \textit{linear arithmetic} \\
                             &   & \mid & f (p_1, \dots, p_n)            & \textit{uninterp. functions} \\
                             &   &      & & \\ 
\textbf{Verification Conditions} & c & ::= & p  & \textit{predicates} \\
                             &   & \mid & c_1 \land c_2 & \textit{conjunction} \\
                              &   & \mid & \forall x:b. p \Rightarrow c & \textit{implication} \\
\end{array}
$$

_Verification Conditions_ can be predicates, as a base case, conjunction, so that many verification conditions 
can be gathered together, and implications, as generated by the $\texttt{I-Ext}$ rule.
Most of the syntax of predicates should be familiar to you. 

**Question:** Do we need more boolean operators? Or maybe less? 

_Uninterpreted functions_ are essentially logical functions that always return the same value for the same input.

$$
\forall x\ y. x = y \Rightarrow f(x) = f(y)
$$

They are essential for program verification because 
1. they can be used to encode program functions in the logic and 
2. they can be used to capture ideas not directly implemented. 

For example, in Liquid Haskell, we use the `measure` keyword to define uninterpreted functions.

\begin{code}
{-@ measure isPrime :: Int -> Bool @-}
\end{code}

Given the property of being a function, Liquid Haskell, via SMT, can prove than on same input, `isPrime` returns the same output. 

\begin{code}

{-@ uninteprCheck :: x:Int -> y:Int 
                  -> {v:() | x = y => isPrime x = isPrime y } @-}

uninteprCheck :: Int -> Int -> () 
uninteprCheck _ _ = () 


\end{code}



Primitive Operations
---------------------
Up to now, we have seen how type checking (of base types) is reduced to checking of verification conditions.
We also saw that constants, like integers and booleans, are given singleton types. 
But, what about other operations, like addition, subtraction, etc.?
Remember that the type of `div` was refined to ensure that the second argument is non-zero.
The same happens for other "primitive" operations, like addition, subtraction, etc.
They all come with refined types that essentially map their operations to the SMT primitives. 

So, in Liquid Haskell we have the following refined types for the basic operations:

~~~~{.spec}

(+)  :: Num a => x:a -> y:a -> {v:a | v = x + y}
(-)  :: Num a => x:a -> y:a -> {v:a | v = x - y}
(&&) :: x:Bool -> y:Bool -> {v:Bool | v = x && y }
(||) :: x:Bool -> y:Bool -> {v:Bool | v = x || y }
(==) :: Eq a => x:a -> y:a -> {v:Bool | v = (x = y)}

~~~~

Such specifications of primitive operators come are _trusted_ assumptions, 
required to connect the primitives of the programming language to the SMT solver.
Thus, the refinement rule for such constants is: 

$$
\inferrule{\texttt{T-Const}}
  {}
  {\Gamma \vdash c : \text{tyConst}(c)}
$$



**Question:** What is the verification condition of the problem below? 

\begin{code}

{-@ threePlusSix :: {v:Int | 0 <= v} @-}
threePlusSix :: Int 
threePlusSix = 3 + 6 

\end{code}

**Question:** What is the verification condition of the problem below? 

\begin{code}

{-@ plusSix :: x:Int -> {v:Int | x <= v} @-}
plusSix :: Int -> Int 
plusSix x = x + 6 

\end{code}

**Question:** Can you make the above code return only natural numbers? 



Function Types 
--------------

Refinements on function arguments define _preconditions_, i.e., assumptions about the arguments 
of the function, while refinements on the return type define _postconditions_, i.e., guarantees
about the return value of the function.

For example, addition of two odd numbers is guaranteed to be even: 

\begin{code}
{-@ type Odd  = {v:Int | v mod 2 = 1} @-}
{-@ type Even = {v:Int | v mod 2 = 0} @-}

{-@ addOdds :: x:Odd -> y:Odd -> Even @-}
addOdds :: Int -> Int -> Int
addOdds x y = x + y

\end{code}

Increasing a positive number is guaranteed to be positive:

\begin{code}

{-@ incrPos :: x:Pos -> Pos @-}
incrPos :: Int -> Int 
incrPos x = x + 1

\end{code}

**Question:** What is the verification condition of the problem below?


So, the verification condition generated when checking the output, 
puts into the typing context the input and then checks the postcondition:

$$
\inferrule
  {\text{T-Fun}}
  {\Gamma; x:\tau_x \vdash e : \tau}
  {\Gamma \vdash \lambda x. e : x:\tau_x \rightarrow \tau}
$$

When type checking function applications, 
the subtyping rule is used to _weaken_ the type of the argument into the 
correct type (e.g., make $2$ a natural number).

$$
\inferrule
  {\text{T-App}}
  { \Gamma \vdash e: (x:\tau_x \rightarrow \tau) \quad 
    \Gamma \vdash y : \tau_x}
  {\Gamma \vdash e\ y : x:\tau_x \rightarrow \tau [x / y] }
$$

**Note:** 
The type of the result can contain the input variable which is substitute. 
For example, what is a precise type for `incr2`?


\begin{code}

incr :: Int -> Int 
{-@ incr :: x:Int -> {v:Int | v = x + 1} @-}
incr x = x + 1 


incr2 :: Int -> Int 
incr2 x = incr (incr x)

\end{code}


**Note:** Refinement types assume that application only happens with variables as 
arguments. This is not a limitation because internally we can always use a let binding
to bind the argument to a variable. E.g., the above definition of `incr2` is equivalent to:

~~~{.spec}
incr2 x = let y = incr x in incr y
~~~

This transformation is called ANF (administrative normal form). 
Can you think why it is required? 



_Subtyping_ exists also on function types and it gets interesting... 

**Question:** Which of the following functions 
can be applied to `higher`? 


\begin{code}

fII, fIP, fIN, fPI, fPP, fPN, fNI, fNP, fNN :: Int -> Int 
higher :: (Int -> Int) -> Int 
fII = undefined 
fIP = undefined
fIN = undefined
fPI = undefined
fPP = undefined
fPN = undefined
fNI = undefined
fNP = undefined
fNN = undefined
higher = undefined 


{-@ fII :: Int -> Int @-}
{-@ fIP :: Int -> Pos @-}
{-@ fIN :: Int -> Nat @-}
{-@ fPI :: Pos -> Int @-}
{-@ fPP :: Pos -> Pos @-}
{-@ fPN :: Pos -> Nat @-}
{-@ fNI :: Nat -> Int @-}
{-@ fNP :: Nat -> Pos @-}
{-@ fNN :: Nat -> Nat @-}


{-@ higher :: (Nat -> Nat) -> Nat @-}

testhigher = higher fNN
\end{code}


As we should have figured out, the rule says that 
the result type should be a subtype but the argument a subpertype. 


$$
\inferrule
  {\texttt{Sub-Fun}}
  {
    \Gamma \vdash \tau_{x2} \preceq \tau_{x1} \quad
    \Gamma; x_2:\tau_{x2} \vdash \tau_1[x_1/x_2] \preceq \tau_2
  }{
    \Gamma \vdash x_1:\tau_{x1} \rightarrow \tau_1 \preceq x_2:\tau_{x2} \rightarrow \tau_2
  }
$$

We call the above rule on the argument _contravariant_ and on the result _covariant_.
Also, note that the result is checked under a context that contains the strongest argument! 



Branching and Recursion  
-----------------------

Let's compute the absolute value of a number. 

\begin{code}

abs :: Int -> Int 
abs x = if x > 0 then x else -x 
\end{code}

**Question:** What is the type of `abs`?

**Question:** What is the verification condition generated?

Refinement types are _branch sensitive_, meaning that the type of the result of a branch
depends on the condition of the branch.

The typing rule for branches takes this sensitivity into account:

$$
\inferrule
  {\texttt{T-If}}
  {
    \Gamma \vdash x : \{v:\texttt{bool} \mid p \} \quad 
    \Gamma; y:\{y:\texttt{bool} \mid  x  \} \vdash e_1 : \tau \quad 
    \Gamma; y:\{y:\texttt{bool} \mid  \lnot x  \}  \vdash e_2 : \tau
  }{
    \Gamma \vdash \text{if } x \text{ then } e_1 \text{ else } e_2 : \tau
  }
$$

Note that the branch is also in ANF, so that it can get into the refinements. 
The typing uses a fresh variable $y$ to capture the condition of the branch.


Of course, branching makes more sense when accompanied with recursive functions. 
Let's confirm that the sum of the first $n$ natural numbers is greater then $n$: 

\begin{code}
sumN :: Int -> Int 
sumN n = if n == 0 then 0 else n + sumN (n - 1)
\end{code}

**Question:** What is the type of `sumN`?

**Question:** What is the verification condition generated?

Type checking of recursive functions is itself a recursive process.
Meaning, to check the type of `sumN`, we need to assume that `sumN` has the correct type! 

$$
\inferrule
  {\texttt{T-Rec}}
  {
    \Gamma; f:\tau_f \vdash e_f : \tau_f \quad 
    \Gamma; f:\tau_f \vdash e : \tau 
  }{
    \Gamma \vdash \text{let rec } f = e_f \text{ in } e : \tau
  }
 $$ 


Refined Polymorphism 
------------
The truth is polymorphism is a difficult topic in the area of programming languages. 
But, as a first step let's only see its great points and for refinement types, 
the great benefit of polymorphism is that any polymorphic function can be instantiated 
to refined values. 
For example, the identity function can be instantiated to propagate natural numbers: 

\begin{code}

myid :: a -> a 
myid x = x 

testPoly :: Int 
{-@ testPoly :: Nat @-}
testPoly = higher myid
\end{code}

This is extremely powerful because it allows us to write generic code to propagate
any application specific refinements! Next, we will see how this takes effect when 
using generic structures (e.g., arrays or in general data types).
But now, for completeness, lets see the rules for polymorphism.

To get a polymorphic system, we need the ability to abstract and instantiate over type variables: 

$$
\inferrule
  {\texttt{T-TAbs}}
  {
    \Gamma; \alpha \vdash e : \tau
  } {
    \Gamma \vdash \Lambda \alpha. e : \forall \alpha. \tau
  }
\qquad
\inferrule
  {\texttt{T-TInst}}
  {
    \Gamma \vdash e : \forall \alpha. \tau 
  }{
    \Gamma \vdash e[\tau_\alpha] : \tau[\tau_\alpha/\alpha]
  }
$$

Since we allow subtyping, we also need to allow subtyping on polymorphic types. 
For simplicity, we assume that the type variable is renamed to be the same: 

$$
\inferrule
  {\texttt{Sub-Abs}}
  {
    \Gamma; \alpha \vdash \tau_1 \preceq \tau_2
  }{
    \Gamma \vdash \forall \alpha. \tau_1 \preceq \forall \alpha. \tau_2
  }
$$

Putting it all together: Safe Indexing
---------------------------------------


The major application of refinement types is to ensure indexing is safe.
So, let's generate structures of arrays and safely index them. 
Meaning `ArrayN a n` is an array of `n` elements of type `a` and
accessing them with an index less than 0 or greater than `n` is an
out of bounds error.

\begin{code}
type Array a = Int -> a 
{-@ type ArrayN a N = {i:Nat | i < N} -> a @-}

new :: Int -> a -> Array a 
{-@ new :: n:Nat -> a -> ArrayN a n @-}
new n x = \i -> if 0 <= i && i < n then x else error "Out of Bounds"

set :: Int -> Int -> a -> Array a  -> Array a 
{-@ set :: n:Nat -> i:{Nat | i < n} -> a -> ArrayN a n -> ArrayN a n @-}
set n i x a = \j -> if i == j then x else a j

get :: Int -> Int -> Array a -> a 
{-@ get :: n:Nat -> i:{Nat | i < n} -> ArrayN a n -> a @-}
get n i a = a i 

\end{code}


Let's create an array with 42 elements: 
\begin{code}

{-@ arr42 :: ArrayN Int 42 @-}
arr42 :: Array Int
arr42 = new 42 0

getElem :: Int 
{-@ getElem :: Int @-}
getElem = get 42 10 arr42
\end{code}

**Question:** What are good indices of `arr42`?


To put now _all_ the features we learnt together, let's assume a function 
that checks for primality and use it to generate the next prime number.

\begin{code}
{-@ type Prime = {v:Int | isPrime v } @-}

isPrime :: Int -> Bool 
{-@ isPrime :: i:Int -> {v:Bool | v <=> isPrime i } @-}
isPrime = undefined 

nextPrime :: Int -> Int 
{-@ nextPrime :: Nat -> Prime  @-}
nextPrime x = if isPrime x then x else nextPrime (x + 1)
\end{code}

**Question:** Given `nextPrime` can you generate an array that contains only prime numbers?

\begin{code}
{-@ primes :: n:Nat -> ArrayN Prime n @-}
primes :: Int -> Array Int
primes = undefined 

\end{code}



Summary
-------
To sum up the most important features of a refinement type system are: 

- _implicit subtyping:_ the type of $2$ turn into a non zero without any user casts! 
- _branch sensitivity:_ the type of the result of a branch depends on the condition of the branch! 
- _polymorphism:_ the type of a function can depend on the type of its arguments!


We saw the most important rule of a refinement type system! 
Next, we will look at the data types (so that we can implement more structured arrays)
and we will go into more examples on how to use refinement types. 
But, for completeness, let's put here the definition 
of the language that we have seen and the typing and subtyping rules.


- Syntax of the language:

$$
\begin{array}{r r c l l}
\textbf{Basic Types} & \texttt{b} & ::=  & \texttt{Int} \mid \texttt{Bool}, \dots  &  \\
                             &   &      & & \\ 
\textbf{Types} & \tau & ::=  & \{ v:\texttt{b} \mid p \} & \textit{base} \\
                             &   & \mid &x:\tau_{x} \rightarrow \tau & \textit{function} \\
                             &   & \mid & \forall \alpha. \tau          & \textit{polymorphic} \\
                             &   &      & & \\ 
\textbf{Expressions} & e & ::= & x  & \textit{variables} \\
                             &   & \mid & c & \textit{constants} \\
                             &   & \mid & \lambda x . e  & \textit{function} \\
                             &   & \mid & e\ x  & \textit{application} \\
                             &   & \mid & \text{if } x \text{ then } e \text{ else } e  & \textit{if} \\
                             &   & \mid & \text{let  } x = e \text{ in } e  & \textit{let} \\
                             &   & \mid & \text{let rec } f = e \text{ in } e  & \textit{recursion} \\
                             &   & \mid & \Lambda \alpha. e  & \textit{type abs.} \\
                             &   & \mid & e[\tau]  & \textit{type appl.} \\
\end{array}
$$


- Typing rules collected: 
$$
\inferrule
  {\texttt{T-Sub}}
  {
  \Gamma \vdash e : \tau_1 \quad 
  \Gamma \vdash \tau_1 \preceq \tau_2
  }{
  \Gamma \vdash e : \tau_2
  }
$$

$$
\inferrule{\texttt{T-Const}}
  {}
  {\Gamma \vdash c : \text{tyConst}(c)}
\quad 
\inferrule{\texttt{T-Var}}
  {}
  {\Gamma \vdash x : \Gamma(x)}
$$
$$
\inferrule
  {\text{T-Fun}}
  {\Gamma; x:\tau_x \vdash e : \tau}
  {\Gamma \vdash \lambda x. e : x:\tau_x \rightarrow \tau}
\quad
\inferrule
  {\text{T-App}}
  { \Gamma \vdash e: (x:\tau_x \rightarrow \tau) \quad 
    \Gamma \vdash y : \tau_x}
  {\Gamma \vdash e\ y : x:\tau_x \rightarrow \tau [x / y] }
$$
$$
\inferrule
  {\texttt{T-If}}
  {
    \Gamma \vdash x : \{v:\texttt{bool} \mid p \} \quad 
    \Gamma; y:\{y:\texttt{bool} \mid  x  \} \vdash e_1 : \tau \quad 
    \Gamma; y:\{y:\texttt{bool} \mid  \lnot x  \}  \vdash e_2 : \tau
  }{
    \Gamma \vdash \text{if } x \text{ then } e_1 \text{ else } e_2 : \tau
  }
$$
$$
\inferrule
  {\texttt{T-Let}}
  {
    \Gamma; \vdash e_x : \tau_x \quad 
    \Gamma; x:\tau_x \vdash e : \tau 
  }{
    \Gamma \vdash \text{let } x = e_x \text{ in } e : \tau
  }
 $$ 

$$
\inferrule
  {\texttt{T-Rec}}
  {
    \Gamma; f:\tau_f \vdash e_f : \tau_f \quad 
    \Gamma; f:\tau_f \vdash e : \tau 
  }{
    \Gamma \vdash \text{let rec } f = e_f \text{ in } e : \tau
  }
 $$ 
$$
\inferrule
  {\texttt{T-TAbs}}
  {
    \Gamma; \alpha \vdash e : \tau
  } {
    \Gamma \vdash \Lambda \alpha. e : \forall \alpha. \tau
  }
\qquad
\inferrule
  {\texttt{T-TInst}}
  {
    \Gamma \vdash e : \forall \alpha. \tau 
  }{
    \Gamma \vdash e[\tau_\alpha] : \tau[\tau_\alpha/\alpha]
  }
$$




- Subtyping rules collected:

$$
\inferrule
  {\texttt{Sub-Base}}
  {
   \Gamma \vdash \forall v:b. p_1 \Rightarrow p_2
  }{
  \Gamma \vdash \{ v:\texttt{b} \mid p_1 \} \preceq \{ v:\texttt{b} \mid p_2 \}
  }
$$
$$
\inferrule
  {\texttt{Sub-Fun}}
  {
    \Gamma \vdash \tau_{x2} \preceq \tau_{x1} \quad
    \Gamma; x_2:\tau_{x2} \vdash \tau_1[x_1/x_2] \preceq \tau_2
  }{
    \Gamma \vdash x_1:\tau_{x1} \rightarrow \tau_1 \preceq x_2:\tau_{x2} \rightarrow \tau_2
  }
$$


$$
\inferrule
  {\texttt{Sub-Abs}}
  {
    \Gamma; \alpha \vdash \tau_1 \preceq \tau_2
  }{
    \Gamma \vdash \forall \alpha. \tau_1 \preceq \forall \alpha. \tau_2
  }
$$


**Note:** The definitions of the rules are syntactic. 
One subtyping rule exists for each type and one typing rule exists for each expression.
The subtyping rule applies to all expressions and _in general_ make the system 
not algorithmic (meaning, when does this rule apply?)
To solve this problem and make the system algorithmic Liquid Haskell uses 
a _bidirectional_ type checking algorithm.
In general, the above rules are simplified in various ways (e.g., well formedness is not discussed). 



Further Reading
----------------
These lectures notes are based on the [Liquid Haskell Tutorial](https://ucsd-progsys.github.io/liquidhaskell-tutorial/).
For further reading on how to develop a refinement type checker for your own language,
you can read the [Refinement Types: A Tutorial](https://arxiv.org/abs/2010.07763) 
and for the theoretical foundations of LiquidHaskell, the publication [Mechanizing Refinement Types](https://dl.acm.org/doi/pdf/10.1145/3632912). 


Cheatsheet
----------------

Here is the definition of the primes array.

~~~{.spec}
primes :: Int -> Array Int
primes n = go  1 0  (new n (nextPrime 1))
  where 
    go i j a 
      | i < n     = go (i + 1) (j + 1) (set n j (nextPrime j) a)
      | otherwise = a
~~~
