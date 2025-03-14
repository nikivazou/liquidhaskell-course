Natural Deduction 
============


\begin{code}
{- OPTIONS_GHC -fplugin=LiquidHaskell #-}
module Lecture_08_NaturalDeduction where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ infix ++ @-}
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding ((++))
\end{code}

In a previous lecture we saw tha programs are proofs and we 
proved a higher order property, 
i.e., a property over functions, 
that all increasing functions are monotonic.

In this lecture, we see that any higher order property can be encoded 
in Liquid Haskell, because refinement types can encode higher order logic 
and type checking can encode the natural deduction proof system.

Logical Properties 
------------------

Like a programming language, logic has 

- **syntax** ($e$, $\land$, $\lor$, $\lnot$, $\Rightarrow$ $\forall$, $\exists$)
- **meaning** (if $\phi$ is true and $\psi$ is true, then $\phi \land \psi$ is true), and 
- **"evaluation"** (decision procedues). 

**Natural Deduction** is a decision procedure for logic.
The Curry-Howard correspondence says that 
propositions are types and proofs are programs.
In this lecture, we will see that natural deduction is encoded by type checking rules. 

Concretely, we will see the encoding by filling in the following table:



|               | **Logical Formula**    | **Refinement Type**     |
| ---:          |    :----:              |  :---:                  |
| Native Terms  | $e$                    |                         |
| Conjunction   | $\phi_1 \land \phi_2$  |                         |
| Disjunction   | $\phi_1 \lor \phi_2$   |                         |
| Implication   | $\phi_1 \Rightarrow \phi_2$ |                     |
| Negation      | $\lnot \phi$           |                         |
| Forall        | $\forall x. \phi$      |                         |
| Exists        | $\exists x. \phi$      |                         |


Native Terms
------------

We start with the simplest case, native terms.
We have already seen that native terms are encoded by refinements on unit types: 

\begin{code}
{-@ fact1 :: {v:() | 2 == 1 + 1 } @-}
fact1 :: ()
fact1 = ()

{-@ fact2 :: {v:() | 2 /= 3 } @-}
fact2 :: ()
fact2 = ()
\end{code}


So native terms are encoded by unit types with refinements:

|               | **Logical Formula**    | **Refinement Type**     |
| ---:          |    :----:              |  :---:                  |
| Native Terms  | $e$                    |   $\{e\}$               |
| Conjunction   | $\phi_1 \land \phi_2$  |                         |
| Disjunction   | $\phi_1 \lor \phi_2$   |                         |
| Implication   | $\phi_1 \Rightarrow \phi_2$ |                     |
| Negation      | $\lnot \phi$           |                         |
| Forall        | $\forall x. \phi$      |                         |
| Exists        | $\exists x. \phi$      |                         |


Conjunction
-----------

Conjunction is encoded by the pair type.
If you know that $\phi_1$ is true and $\phi_2$ is true, 
then $(\phi_1, \phi_2)$ is a term that shows that $\phi_1 \land \phi_2$ is true.

\begin{code}
{-@ conj :: ϕ1:{Bool | ϕ1 } -> ϕ2:{Bool | ϕ2 } 
         -> {v:(Bool, Bool) | ϕ1 && ϕ2} @-}
conj :: Bool -> Bool -> (Bool, Bool)
conj ϕ1 ϕ2 = (ϕ1,ϕ2)
\end{code}


Given that logical conjunction can be encoded as pairs, 
we can see how type checking can encode the natural deduction proof system.
When typing pairs, there are three rules: 
left and right _elimination_ and _introduction_.

$$
\inferrule
  {\land\text{-L-E}}
  {
    \Gamma \vdash e : (\phi_1, \phi_2)
  }{
    \Gamma \vdash \text{case } e \text{ of } (x_1, x_2) \rightarrow x_1 : \phi_1
  }
$$

$$
\inferrule
  {\land\text{-R-E}}
  {
    \Gamma \vdash e : (\phi_1, \phi_2)
  }{
    \Gamma \vdash \text{case } e \text{ of } (x_1, x_2) \rightarrow x_2 : \phi_2
  }
$$

$$
\inferrule
  {\land\text{-I}}
  {
    \Gamma \vdash \text{case } e \text{ of } (x_1, x_2) \rightarrow x_1 : \phi_1 \\
    \Gamma \vdash \text{case } e \text{ of } (x_1, x_2) \rightarrow x_2 : \phi_2
  }{
    \Gamma \vdash e : (\phi_1, \phi_2)
  }
$$

If we ignore the expressions above we take exactly the conjuction rules 
of natural deduction.

** You can generate Haskell terms that provide evidence for the 
natural deduction rules!**


As an example, consider the natural deduction devation below 

$$
\inferrule
  {\land\text{-I}}
  {
    \phi_1,\phi_2\land\phi_3 \vdash  \phi_1  \qquad
    \inferrule{\land\text{-R-E}}
    {
      \phi_1,\phi_2\land\phi_3 \vdash  \phi_2\land\phi_3
    }{
      \phi_1,\phi_2\land\phi_3 \vdash  \phi_3
    }
  }{
    \phi_1, \phi_2\land\phi_3 \vdash  \phi_1\land \phi_3
  }
$$

Filling in the terms (and applying the correspondence of propositions and types) we get:

$$
\inferrule
  {\land\text{-I}}
  {
    x_1:\phi_1,x_{23}:\phi_2\land\phi_3 \vdash  x_1:\phi_1  \qquad
    \inferrule{\land\text{-R-E}}
    {
      x_1:\phi_1,x_{23}:\phi_2\land\phi_3 \vdash x_{23}: \phi_2\land\phi_3
    }{
      x_1:\phi_1,x_{23}:\phi_2\land\phi_3 \vdash \text{case } x_{23} \text{ of } (x_2, x_3) \rightarrow x_3: \phi_3
    }
  }{
    x_1:\phi_1,x_{23}: \phi_2\land\phi_3 \vdash (x_1, \text{case } x_{23} \text{ of } (x_2, x_3) \rightarrow x_3): \phi_1\land \phi_3
  }
$$

Let's encode this proof in Liquid Haskell! 

\begin{code}
{-@ ex1 :: φ1:Bool -> φ2:Bool -> φ3:Bool 
    -> {v:() | φ1}
    -> ({v:() | φ2}, {v:() | φ3})
    -> ({v:() | φ1}, {v:() | φ3}) @-}
ex1 :: Bool -> Bool -> Bool -> () -> ((), ()) -> ((), ())
ex1 _ _ _ x1 x23 = 
  (x1, case x23 of (x2,x3) -> x3)
\end{code}

So, conjuction is encoded by the pair type.

|               | **Logical Formula**    | **Refinement Type**     |
| ---:          |    :----:              |  :---:                  |
| Native Terms  | $e$                    |   {e}                 |
| Conjunction   | $\phi_1 \land \phi_2$  | ($\phi_1$, $\phi_2$)    |
| Disjunction   | $\phi_1 \lor \phi_2$   |                         |
| Implication   | $\phi_1 \Rightarrow \phi_2$ |                    |
| Negation      | $\lnot \phi$           |                         |
| Forall        | $\forall x. \phi$      |                         |
| Exists        | $\exists x. \phi$      |                         |


Disjunction
-----------

Disjunction is encoded by the `Either` type, 
which is a sum type that can be either `Left` or `Right`.
`data Either a b = Left a | Right b`.

\begin{code}
{-@ disj :: ϕ1:Bool -> ϕ2:Bool -> {v:() | ϕ1 || ϕ2 }
         -> {v:Either () () | ϕ1 || ϕ2 } @-}
disj :: Bool -> Bool -> () -> Either () ()
disj ϕ1 ϕ2 p = if ϕ1 then Left p else Right p
\end{code}

If you know that $\phi_1$ is true or $\phi_2$ is true, 
then `Left ()` is a term that shows that $\phi_1 \lor \phi_2$ is true
and `Right ()` is a term that shows that $\phi_1 \lor \phi_2$ is true.

Dually to conjunction, disjunction has three rules:
left and right _introduction_ and _elimination_.

$$
\inferrule
  {\lor\text{-L-I}}
  {
    \Gamma \vdash e : \phi_1
  }{
    \Gamma \vdash \text{Left } e : \text{Either } \phi_1 \ \phi_2
  }
$$

$$
\inferrule
  {\lor\text{-R-I}}
  {
    \Gamma \vdash e : \phi_2
  }{
    \Gamma \vdash \text{Right } e : \text{Either } \phi_1 \ \phi_2
  }
$$

$$
\inferrule
  {\lor\text{-E}}
  {
    \Gamma \vdash e : \text{Either } \phi_1\ \phi_2 \\
    \Gamma, x_1 : \phi_1 \vdash e_1 : \phi \quad
    \Gamma, x_2 : \phi_2 \vdash e_2 : \phi
  }{
    \Gamma \vdash \text{case } e \text{ of } \{\text{Left } x_1 \rightarrow x_1 ;  
                                             \text{Right } x_2 \rightarrow x_2 \} : \phi
  }
$$

So, disjunction is encoded by the either type.

|               | **Logical Formula**    | **Refinement Type**     |
| ---:          |    :----:              |  :---:                  |
| Native Terms  | $e$                    |   {e}                 |
| Conjunction   | $\phi_1 \land \phi_2$  | ($\phi_1$, $\phi_2$)    |
| Disjunction   | $\phi_1 \lor \phi_2$   |   \text{Either } $\phi_1$\ $\phi_2$                   |
| Implication   | $\phi_1 \Rightarrow \phi_2$ |                    |
| Negation      | $\lnot \phi$           |                         |
| Forall        | $\forall x. \phi$      |                         |
| Exists        | $\exists x. \phi$      |                         |


Implication
-----------

Implication is encoded by the function type. 
It has two rules: _introduction_ and _elimination_:

$$
\inferrule
  {\Rightarrow\text{-I}}
  {
    \Gamma, x : \phi_x \vdash e : \phi
  }{
    \Gamma \vdash \lambda x. e : \phi_x \rightarrow \phi
  }
$$

$$
\inferrule
  {\Rightarrow\text{-E}}
  {
    \Gamma \vdash e : \phi_x \rightarrow \phi \quad
    \Gamma \vdash e_x : \phi_x
  }{
    \Gamma \vdash e\ e_x : \phi
  }
$$

The Implication Elimination Rule for natural deduction 
is also known as the _modus ponens_ rule.

|               | **Logical Formula**    | **Refinement Type**     |
| ---:          |    :----:              |  :---:                  |
| Native Terms  | $e$                    |   {e}                 |
| Conjunction   | $\phi_1 \land \phi_2$  | ($\phi_1$, $\phi_2$)    |
| Disjunction   | $\phi_1 \lor \phi_2$   |   \text{Either } $\phi_1$\ $\phi_2$                   |
| Implication   | $\phi_1 \Rightarrow \phi_2$ | $\phi_1 \rightarrow \phi_2$                   |
| Negation      | $\lnot \phi$           |                         |
| Forall        | $\forall x. \phi$      |                         |
| Exists        | $\exists x. \phi$      |                         |



Negation
--------

Negation is just implication to `False`.

\begin{code}
{-@ neg :: ϕ:Bool -> {v:() | not ϕ} 
        -> ({v:() | ϕ} -> {v:() | false}) @-}
neg :: Bool -> () -> (() -> ())
neg _ _ = \_ -> ()
\end{code}


|               | **Logical Formula**    | **Refinement Type**     |
| ---:          |    :----:              |  :---:                  |
| Native Terms  | $e$                    |   $\{e\}$                 |
| Conjunction   | $\phi_1 \land \phi_2$  | ($\phi_1$, $\phi_2$)    |
| Disjunction   | $\phi_1 \lor \phi_2$   |   \text{Either } $\phi_1$\ $\phi_2$                   |
| Implication   | $\phi_1 \Rightarrow \phi_2$ | $\phi_1 \rightarrow \phi_2$                   |
| Negation      | $\lnot \phi$           | $\phi \rightarrow \{\text{false}\}$                   |
| Forall        | $\forall x. \phi$      |                         |
| Exists        | $\exists x. \phi$      |                         |


Forall
------

Forall is encoded by the quantified function type.
It has two rules: _introduction_ and _elimination_:

$$
\inferrule
  {\forall\text{-I}}
  {
    \Gamma, x:\tau \vdash e : \phi
  }{
    \Gamma \vdash \lambda x. e : x:\tau \rightarrow \phi
  }
$$

$$
\inferrule
  {\forall\text{-E}}
  {
    \Gamma \vdash e : (x:\tau \rightarrow \phi) \quad
    \Gamma \vdash e_x : \tau
  }{
    \Gamma \vdash e\ e_x : \phi [x / e_x]
  }
$$

|               | **Logical Formula**    | **Refinement Type**     |
| ---:          |    :----:              |  :---:                  |
| Native Terms  | $e$                    |   $\{e\}$                 |
| Conjunction   | $\phi_1 \land \phi_2$  | ($\phi_1$, $\phi_2$)    |
| Disjunction   | $\phi_1 \lor \phi_2$   |   \text{Either } $\phi_1$\ $\phi_2$  |
| Implication   | $\phi_1 \Rightarrow \phi_2$ | $\phi_1 \rightarrow \phi_2$     |
| Negation      | $\lnot \phi$           | $\phi \rightarrow \{\text{false}\}$  |
| Forall        | $\forall x. \phi$      |  $x:\tau \rightarrow \phi$           |
| Exists        | $\exists x. \phi$      |                         |

Exists
------

Exists is encoded by the dependent pair. 
It has two rules: _introduction_ and _elimination_:

$$
\inferrule
  {\exists\text{-I}}
  {
    \Gamma \vdash \text{fst } e : \tau \quad
    \Gamma, x:\tau \vdash \text{snd }  e : \phi
  }{
    \Gamma \vdash e : (x:\tau, \phi[x / \text{fst } e])
  }
$$

$$
\inferrule
  {\exists\text{-E}}
  {
    \Gamma \vdash e : (x:\tau, \phi_x) \quad
    \Gamma, x:\tau, y:\phi_x \vdash e' : \phi
  }{
    \Gamma \vdash \text{case } e \text{ of } (x, y) \rightarrow e' : \phi
  }
$$

|               | **Logical Formula**    | **Refinement Type**     |
| ---:          |    :----:              |  :---:                  |
| Native Terms  | $e$                    |   $\{e\}$                 |
| Conjunction   | $\phi_1 \land \phi_2$  | ($\phi_1$, $\phi_2$)    |
| Disjunction   | $\phi_1 \lor \phi_2$   |   \text{Either } $\phi_1$\ $\phi_2$  |
| Implication   | $\phi_1 \Rightarrow \phi_2$ | $\phi_1 \rightarrow \phi_2$     |
| Negation      | $\lnot \phi$           | $\phi \rightarrow \{\text{false}\}$  |
| Forall        | $\forall x. \phi$      |  $x:\tau \rightarrow \phi$           |
| Exists        | $\exists x. \phi$      |  $(x:\tau, \phi)$           |


That concludes the encoding! 
Let's now see some examples that use it! 

Example 1: existsAll
--------------------

The first example is a proof that if there exists an $x$ 
that satisfies a property forall $y$, 
then forall $y$ there exists an $x$ that satisfies the property.

$$ \phi = \exists x. \forall y. p\ x \ y  \Rightarrow \forall y. \exists x. p \ x \ y $$

Let's prove this propery in Liquid Haskell!

\begin{code}
{-@ exAll :: p:(a -> a -> Bool)
          -> (x::a, y:a -> {v:() | p x y}) 
          -> y:a 
          -> (x::a, {v:() | p x y}) @-}
exAll :: (a -> a -> Bool) -> (a, a -> ()) -> a -> (a, ())
exAll p = undefined
\end{code}

**Question**: Can you prove this property in Liquid Haskell?


The natural deduction proof is shown below:

<div class="marginfigure"
     id="fig:avl"
     height="300px"
     file="img/exAll.png"
     caption="Natural Deduction Proof for exAll">
</div>


Example 2: Distributing Qualifiers
----------------------------------

First, let's distribute the exists quantifier over disjunction.

$$ \phi_\exists = (\exists x. p\ x \lor q\ x) \rightarrow ((\exists x. p\ x) \lor (\exists x. q\ x)) $$

Let's prove this propery in Liquid Haskell!

\begin{code}
exDistOr = undefined 
\end{code}

**Question**: Can you prove this property in Liquid Haskell?


Now, let's distribute the forall quantifier over conjunction.

$$ \phi_\forall = (\forall x. p\ x \land q\ x) \rightarrow ((\forall x. p\ x) \land (\forall x. q\ x))$$

Let's prove this propery in Liquid Haskell!

\begin{code}
allDistAnd = undefined
\end{code}


**Question**: Can you prove this property in Liquid Haskell?

Example 3: List Properties 
---------------------------

Next, let's prove that for all lists that are constructed by appending a list to itself,
there exists an integer that is half the length of the list.

$$ \phi = \forall xs. (\exists ys. xs = ys \text{ ++ } ys) \rightarrow (\exists n. \text{length } xs = n + n )$$

Let's prove this propery in Liquid Haskell!

\begin{code}
evenLen = undefined
\end{code}

**Question**: Can you prove the above property in Liquid Haskell?
_Hint:_ You can use the property `lenAppend`:

\begin{code}
{-@ lenAppend :: xs:[a] -> ys:[a] -> {v:() | len (xs ++ ys) == len xs + len ys} @-}
lenAppend :: [a] -> [a] -> ()
lenAppend [] _      = ()
lenAppend (_:xs) ys = lenAppend xs ys

{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)
\end{code}



Example 4: Natural Induction 
----------------------------

Finally, let's prove that for all natural numbers,

$$ \phi = (p \ 0 \land (\forall n. p \ (n-1) \rightarrow p \ n))) \rightarrow \forall n. p \ n$$

Let's prove this propery in Liquid Haskell!

\begin{code}
natInd = undefined
\end{code}

Summary 
-------

In this lecture, we saw that natural deduction can be encoded in Liquid Haskell.
We saw that the rules of natural deduction can be encoded by the type checking rules of Liquid Haskell.
We saw that the Curry-Howard correspondence can be extended to higher order logic.
We saw that we can prove higher order properties in Liquid Haskell.

