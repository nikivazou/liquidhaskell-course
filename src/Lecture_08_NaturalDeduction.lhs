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

In this lecture, we see that _any_ higher order property can be encoded 
in Liquid Haskell, because refinement types can encode higher order logic 
and type checking can encode the natural deduction proof system.

Logical Properties 
------------------

Like a programming language, logic has 

- **syntax** ($e$, $\land$, $\lor$, $\lnot$, $\Rightarrow$ $\forall$, $\exists$)
- **meaning** (if $\phi$ is true and $\psi$ is true, then $\phi \land \psi$ is true), and 
- **"evaluation"** (decision procedues). 

[**Natural Deduction**](https://en.wikipedia.org/wiki/Natural_deduction) is a decision procedure for logic.
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
| Native Terms  | $e$                    |   $\{v:() | e\}$        |
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


**Deduction Rules:**
The rules of natural deduction are the rules that we can use to prove a formula.
For conjuctions, there are three rules: 

- left and right _elimination_, eliminates the conjunction and 
- _introduction_, introduces the conjunction. 

These rules are part of the natural deduction proof system 
and can also be encoded as refinement type checking rules.





| Rule | **Natural Deduction**    | **Type Checking**     |
| ---:          |    :----:              |  :---:                  |
| Left Elimination  | $\inferrule{}
  {
    \Gamma \vdash \phi_1 \land \phi_2
  }{
    \Gamma \vdash  \phi_1
  }$                    |   $\inferrule{}
  {
    \Gamma \vdash e : (\phi_1, \phi_2)
  }{
    \Gamma \vdash \text{case } e \text{ of } (x_1, x_2) \rightarrow x_1 : \phi_1
  }$                |
| Right Elimination  | $\inferrule{}
  {
    \Gamma \vdash \phi_1 \land \phi_2
  }{
    \Gamma \vdash  \phi_2
  }$                    |   $\inferrule{}
  {
    \Gamma \vdash e : (\phi_1, \phi_2)
  }{
    \Gamma \vdash \text{case } e \text{ of } (x_1, x_2) \rightarrow x_2 : \phi_2
  }$                |
| Introduction  | $\inferrule{}
  {
    \Gamma \vdash \phi_1
    \\
    \Gamma \vdash \phi_2
  }{
    \Gamma \vdash  \phi_1 \land \phi_2
  }$                    |   $\inferrule{}
  {
    \Gamma \vdash \text{case } e \text{ of } (x_1, x_2) \rightarrow x_1 : \phi_1
    \\
    \Gamma \vdash \text{case } e \text{ of } (x_1, x_2) \rightarrow x_2 : \phi_2
  }{
    \Gamma \vdash e : (\phi_1, \phi_2)
  }$                |



The type checking rules are not part of the core rules (that we saw in the first lecture), 
but they can be derived from the core rules.

If we ignore the expressions in the type checking rules, we take exactly the conjuction rules 
of natural deduction.

**You can generate Haskell terms that provide evidence for the 
natural deduction rules!**



**As an example,** consider the logical formula:

$$ \textit{If } \phi_1 \textit{ and } \phi_2\land\phi_3, \text{ then }  \phi_1\land \phi_3 .$$

The natural deduction devation tree is shown below:


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

Filling in the terms (and applying the correspondence of propositions and types) we get
the type checking derivation tree:

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


- **Example 1: Conjunction**

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
| Native Terms  | $e$                    |   $\{v:() | e\}$        |
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

~~~~~{.spec}
data Either a b = Left a | Right b -- defined in Prelude
~~~~~

\begin{code}
{-@ disj :: ϕ1:Bool -> ϕ2:Bool -> {v:() | ϕ1 || ϕ2 }
         -> Either {v:() | ϕ1} {v:() | ϕ2} @-}
disj :: Bool -> Bool -> () -> Either () ()
disj ϕ1 ϕ2 p = if ϕ1 then Left p else Right p
\end{code}

If you know that $\phi_1$ is true or $\phi_2$ is true, 
then `Left ()` is a term that shows that $\phi_1 \lor \phi_2$ is true
and `Right ()` is a term that shows that $\phi_1 \lor \phi_2$ is true.


**Deduction Rules:**
Dually to conjunction, disjunction has three rules:
left and right _introduction_ and _elimination_.


| Rule | **Natural Deduction**    | **Type Checking**     |
| ---:          |    :----:              |  :---:                  |
| Left Introduction  | $\inferrule{}{ \Gamma \vdash \phi_1}{\Gamma \vdash \phi_1 \lor \phi_2}$ | $\inferrule{}
  {
    \Gamma \vdash e : \phi_1
  }{
    \Gamma \vdash \text{Left } e : \text{Either } \phi_1 \ \phi_2
  }$ |
| Right Introduction  | $\inferrule{}{ \Gamma \vdash \phi_2}{\Gamma \vdash \phi_1 \lor \phi_2}$ | $\inferrule{}
  {
    \Gamma \vdash e : \phi_2
  }{
    \Gamma \vdash \text{Right } e : \text{Either } \phi_1 \ \phi_2
  }$ | 
| Elimination | $\inferrule{}
  {
    \Gamma \vdash \phi_1 \lor \phi_2
    \\
    \Gamma, \phi_1 \vdash  \phi
    \\
    \Gamma, \phi_2 \vdash  \phi
  }{
    \Gamma \vdash \phi 
  }$ | $\inferrule{}
  {
    \Gamma \vdash e : \text{Either } \phi_1\ \phi_2 \\
    \Gamma, x_1 : \phi_1 \vdash e_1 : \phi \\
    \Gamma, x_2 : \phi_2 \vdash e_2 : \phi
  }{
    \Gamma \vdash \text{case } e \text{ of } \{\text{Left } x_1 \rightarrow x_1 ;  
                                             \text{Right } x_2 \rightarrow x_2 \} : \phi
  }$ |

So, disjunction is encoded by the either type.

- **Example 2: Disjunction**

Consider the valid logical formula:
$$ \textit{If } \phi \lor \text{ false,} \textit{ then }  \phi .$$

In Liquid Haskell, it is encoded usint the below type specification:

\begin{code}
{-@ exOr :: ϕ:Bool -> Either {v:() | ϕ} {v:() | false }
         -> {v:() | ϕ}  @-}
exOr :: Bool -> Either () () -> ()
exOr φ p = undefined 
\end{code}

**Question**: Can you prove this property in Liquid Haskell?

<details>
<summary>**Solution**</summary>

<p> _The function `exOr` can be defined as follows:_</p>
~~~~~{.spec}
exOr ϕ (Left p)  = p
exOr ϕ (Right p) = error "impossible"
~~~~~
</details>


So, disjunction is encoded by the either type:


|               | **Logical Formula**    | **Refinement Type**     |
| ---:          |    :----:              |  :---:                  |
| Native Terms  | $e$                    |   $\{v:() | e\}$        |
| Conjunction   | $\phi_1 \land \phi_2$  | ($\phi_1$, $\phi_2$)    |
| Disjunction   | $\phi_1 \lor \phi_2$   |   Either $\phi_1$\ $\phi_2$                   |
| Implication   | $\phi_1 \Rightarrow \phi_2$ |                    |
| Negation      | $\lnot \phi$           |                         |
| Forall        | $\forall x. \phi$      |                         |
| Exists        | $\exists x. \phi$      |                         |


Implication & Negation
-----------------------

**Implication** is encoded by the function type. 
It has two rules: _introduction_ and _elimination_:


| Rule | **Natural Deduction**    | **Type Checking**     |
| ---:          |    :----:              |  :---:                  |
| Introduction  | $\inferrule{}{ \Gamma, \phi_x \vdash \phi}{\Gamma \vdash \phi_x \Rightarrow \phi}$ | $\inferrule{}
  {
    \Gamma, x : \phi_x \vdash e : \phi
  }{
    \Gamma \vdash \lambda x. e : \phi_x \rightarrow \phi
  }$ | 
| Elimination | $\inferrule{}
  {
    \Gamma \vdash \phi_x
    \\
    \Gamma \vdash \phi_x \Rightarrow \phi
  }{
    \Gamma \vdash \phi
  }$ | $\inferrule{}
  {
    \Gamma \vdash e_x : \phi_x
    \\
    \Gamma \vdash e : (\phi_x \rightarrow \phi) 
  }{
    \Gamma \vdash e\ e_x : \phi
  }$ |


The Implication Elimination Rule for natural deduction 
is also known as the _modus ponens_ rule.


**Negation** is just implication to `False`.

\begin{code}
{-@ neg :: ϕ:Bool -> {v:() | not ϕ} 
        -> ({v:() | ϕ} -> {v:() | false}) @-}
neg :: Bool -> () -> (() -> ())
neg _ _ = \_ -> ()
\end{code}


|               | **Logical Formula**    | **Refinement Type**     |
| ---:          |    :----:              |  :---:                  |
| Native Terms  | $e$                    |   $\{v:() | e\}$        |
| Conjunction   | $\phi_1 \land \phi_2$  | ($\phi_1$, $\phi_2$)    |
| Disjunction   | $\phi_1 \lor \phi_2$   |   Either  $\phi_1$\ $\phi_2$                   |
| Implication   | $\phi_1 \Rightarrow \phi_2$ | $\phi_1 \rightarrow \phi_2$                   |
| Negation      | $\lnot \phi$           | $\phi \rightarrow \{\text{false}\}$                   |
| Forall        | $\forall x. \phi$      |                         |
| Exists        | $\exists x. \phi$      |                         |



- **Example 3: Contradictions**

Consider the valid logical formula:
$$ \phi_C \doteq  \lnot \phi \land \phi \Rightarrow \text{false}$$


In Liquid Haskell, it is encoded usint the below type specification:
\begin{code}
{-@ exC :: φ:Bool 
        -> (({v:() | φ} -> {v:() | false}), {v:() | φ}) 
        -> {v:() | false} @-}
exC :: Bool ->  (() -> () , ()) -> ()
exC ϕ p = undefined 
\end{code}

**Question**: Can you prove this property in Liquid Haskell?

<details>

<summary>**Solution**</summary>

<p> _The function `exC` can be defined as follows:_</p>

~~~~~{.spec}
exC ϕ (f, p) = f p 
~~~~~
</details>

- **Example 4: Double Negation**

Consider the valid logical formula:

$$ \phi_{DN} \doteq  \lnot \lnot \phi \Rightarrow \phi$$

In Liquid Haskell, it is encoded usint the below type specification:
\begin{code}
{-@ exDN :: φ:Bool 
         -> (({v:() | φ} -> {v:() | false}) -> {v:() | false}) 
         -> {v:() | φ}  @-}
exDN :: Bool -> ((()-> ()) -> ()) -> () 
exDN ϕ nnp = undefined 
\end{code}

**Question**: Can you prove this property in Liquid Haskell?

<details>
<summary>**Solution**</summary>
<p> _The function `exDN` can be defined as follows:_</p>   

~~~~~{.spec}
exDN ϕ nnp | not ϕ = nnp f 
  where 
    {-@ f :: {v:() | not ϕ && ϕ} -> {v:() | false} @-} 
    f :: () -> () 
    f _ = () 
exDN ϕ nnp = ()
~~~~~

</details>





Forall and Exists
----------------

**Universal quantification** is encoded by the function type.
It has two rules: _introduction_ and _elimination_:


| Rule | **Natural Deduction**    | **Type Checking**     |
| ---:          |    :----:              |  :---:                  |
| Introduction  | $\inferrule{}{ \Gamma \vdash \phi_x}{\Gamma \vdash \forall x. \phi_x}$ | $\inferrule{}
  {
    \Gamma, x:\tau \vdash e : \phi_x
  }{
    \Gamma \vdash \lambda x. e : x:\tau \rightarrow \phi_x
  }$ |
| Elimination | $\inferrule{}
  {
    \Gamma \vdash \forall x. \phi_x
  }{
    \Gamma \vdash \phi_x [x / e_x]
  }$ | $\inferrule{}
  {
    \Gamma \vdash e : (x:\tau \rightarrow \phi_x) \quad 
    \Gamma \vdash e_x : \tau
  }{
    \Gamma \vdash e\ e_x : \phi_x [x / e_x]
  }$ | 

**Existsential quantification** is encoded by the dependent pair type.
It has two rules: _introduction_ and _elimination_:

| Rule | **Natural Deduction**    | **Type Checking**     |
| ---:          |    :----:              |  :---:                  |
| Introduction  | $\inferrule{}{ \Gamma \vdash \phi_x[x / e_x]}{\Gamma \vdash \exists x. \phi_x}$ | $\inferrule{}
  {
    \Gamma \vdash \text{fst } e : \tau \quad
    \Gamma, x:\tau \vdash \text{snd }  e : \phi_x
  }{
    \Gamma \vdash e : (x:\tau, \phi_x[x / \text{fst } e])
  }$ |
| Elimination | $\inferrule{}
  {
    \Gamma \vdash \exists x. \phi_x
    \\
    \Gamma, \phi_x[x / e_x] \vdash \phi
  }{
    \Gamma \vdash  : \phi
  }$ | $\inferrule{}
  {
    \Gamma \vdash e : (x:\tau, \phi_x) \\
    \Gamma, x:\tau, y:\phi_x \vdash e' : \phi
  }{
    \Gamma \vdash \text{case } e \text{ of } (x, y) \rightarrow e' : \phi
  }$ |

These concludes the encoding of the rules of natural deduction in refinement types:

|               | **Logical Formula**    | **Refinement Type**     |
| ---:          |    :----:              |  :---:                  |
| Native Terms  | $e$                    |   $\{v:() | e\}$        |
| Conjunction   | $\phi_1 \land \phi_2$  | ($\phi_1$, $\phi_2$)    |
| Disjunction   | $\phi_1 \lor \phi_2$   |   Either  $\phi_1$\ $\phi_2$  |
| Implication   | $\phi_1 \Rightarrow \phi_2$ | $\phi_1 \rightarrow \phi_2$     |
| Negation      | $\lnot \phi$           | $\phi \rightarrow \{\text{false}\}$  |
| Forall        | $\forall x. \phi$      |  $x:\tau \rightarrow \phi$           |
| Exists        | $\exists x. \phi$      |  $(x:\tau, \phi)$           |


Let's now see some examples that use it! 

Examples
-----------

- **Example  4: ExistsAll**


This example encodes a proof that if there exists an $x$ 
that satisfies a property forall $y$, 
then forall $y$ there exists an $x$ that satisfies the property.

$$ \phi \doteq \exists x. \forall y. p\ x \ y  \Rightarrow \forall y. \exists x. p \ x \ y $$

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

<details>
<summary>**Solution**</summary>
<p> _The function `exAll` can be defined as follows:_</p>
~~~~~{.spec}
exAll p (x, f) y = (x, f y)
~~~~~
</details>


The natural deduction proof is shown below:

<div class="marginfigure"
     id="fig:avl"
     height="300px"
     file="img/exAll.png"
     caption="Natural Deduction Proof for exAll">
</div>


- **Example 5: Distributing Qualifiers** 

First, let's distribute the exists quantifier over disjunction.

$$ \phi_\exists = (\exists x. p\ x \lor q\ x) \rightarrow ((\exists x. p\ x) \lor (\exists x. q\ x)) $$

Let's prove this propery in Liquid Haskell!

\begin{code}
exDistOr = undefined 
\end{code}

**Question**: Can you prove this property in Liquid Haskell?

<details>
<summary>**Solution**</summary>
<p> _The function `exDistOr` can be defined as follows:_</p>
~~~~~{.spec}
{-@ exDistOr :: p:(a -> Bool) -> q:(a -> Bool)
             -> (x::a, Either {v:() | p x} {v:() | q x})
             -> Either (x::a, {v:() | p x}) (x::a, {v:() | q x}) @-}
exDistOr :: (a -> Bool) -> (a -> Bool)
         -> (a, Either () ())
         -> Either (a,()) (a,())
exDistOr p q (x, Left f) = Left (x, f )
exDistOr p q (x, Right g) = Right (x, g )
~~~~~
</details>


Now, let's distribute the forall quantifier over conjunction.

$$ \phi_\forall = (\forall x. p\ x \land q\ x) \rightarrow ((\forall x. p\ x) \land (\forall x. q\ x))$$

Let's prove this propery in Liquid Haskell!

\begin{code}
allDistAnd = undefined
\end{code}


**Question**: Can you prove this property in Liquid Haskell?

<details>
<summary>**Solution**</summary>
<p> _The function `allDistAnd` can be defined as follows:_</p>
~~~~~{.spec}
{-@ allDistAnd :: p:(a -> Bool) -> q:(a -> Bool)
               -> (x:a -> ({v:() | p x}, {v:() | q x}))
               -> (x:a -> {v:() | p x}, x:a -> {v:() | q x}) @-}
allDistAnd :: (a -> Bool) -> (a -> Bool)
          -> (a -> ((), ()))
          -> (a -> (), a -> ())

allDistAnd p q xpq = (\x -> case xpq x of (p,_) -> p, 
                      \x -> case xpq x of (_,q) -> q)
~~~~~
</details>


- **Example 6: List Properties**

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


<details>
<summary>**Solution**</summary>
<p> _The function `evenLen` can be defined as follows:_</p>
~~~~~{.spec}
{-@ evenLen :: xs:[a] -> (ys::[a], {v:() | xs == ys ++ ys})
            -> (n::{v:Int | 0 <= v}, {v:() | len xs == n + n}) @-}
evenLen :: [a] -> ([a], ()) -> (Int, ())
evenLen xs (ys, ()) = (length ys, lenAppend ys ys)
~~~~~
</details>


- **Example 7: Natural Induction**


Finally, let's prove that for all natural numbers,

$$ \phi = (p \ 0 \land (\forall n. p \ (n-1) \rightarrow p \ n))) \rightarrow \forall n. p \ n$$

Let's prove this propery in Liquid Haskell!

\begin{code}
natInd = undefined
\end{code}


<details>
<summary>**Solution**</summary>
<p> _The function `natInd` can be defined as follows:_</p>
~~~~~{.spec}
{-@ natInd :: p:({v:Int | 0 <= v} -> Bool)
           -> ({v:() | p 0}, n:{v:Int | 0 <= v} -> {v:() | p (n-1)} -> {v:() | p n})
           -> n:{v:Int | 0 <= v} -> {v:() | p n} / [n] @-}
natInd :: (Int -> Bool) -> ((), Int -> () -> ()) -> Int -> () 
natInd p (p0, pn) n 
  = if n == 0 then p0 else pn n (natInd p (p0, pn) (n-1))
~~~~~
</details>


Summary 
-------

In this lecture, we saw that natural deduction can be encoded with refinement types, 
and specifically in Liquid Haskell.
We saw that the rules of natural deduction can be encoded by the type checking rules of Liquid Haskell, 
where the expressions provide evidence for the rules.
We saw that the Curry-Howard correspondence can be extended to higher order logic.
We saw that we can prove higher order properties in Liquid Haskell.

