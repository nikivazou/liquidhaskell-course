Data Propositions 
============


\begin{code}
{- OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-# LANGUAGE GADTs                    #-}

module Lecture_09_DataPropositions where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
import Language.Haskell.Liquid.ProofCombinators
import Data.Set 

\end{code}


We saw that using the refinement types of Liquid Haskell, 
we can encode any predicate in higher order logic 
(using functions and dependent pairs, respectively for universal 
and existential quantification).
Further using reflection we saw that we can encode in the refinement logic 
any terminating Haskell function. 

Thus, the only thing that remains to encode is no terminating functions. 

In this lecture, we will see how to encode such functions, 
using data propositions. 


Even Numbers
------------

Data propositions essentially axiomatize the behavior of 
predicates in the data type definitions, without actually giving 
a Haskell definition.

They are very similar to Coq's 
[inductive predicates](http://adam.chlipala.net/cpdt/html/Predicates.html).
Thus, let's look at the using the textbook example of even numbers.

First, we define the data type of natural numbers.

\begin{code}
data N = Z | S N 
\end{code}

Then, we _axiomatize_ the proposition that a number is even.

\begin{code}
data EVEN where 
    E0 :: EVEN 
    E2 :: N -> EVEN -> EVEN

data Eveness = EVEN N 

{-@ data EVEN where 
     E0 :: Prop (EVEN Z)
   | E2 :: n:N -> Prop (EVEN n) -> Prop (EVEN (S (S n))) @-}
\end{code}

The two constructors `E0` and `E2` axiomatize the evenness of numbers.
`E0` states that `Z` is even, and `E2` states that if `n` is even, 
then `S (S n)` is also even.

The definition is using the `Prop` type, 
defined in the `Language.Haskell.Liquid.ProofCombinators` module,
that converts expressions into proof objects.
Further, it requires the unrefined `Even` Haskell definition 
as well as an `EVEN` data constructor.


There are two important points in this construction. 

- First, there is no function that computes evens, thus 
there is _no termination check_, meaning, that using data propositions 
one can encode non-terminating computations. 

- Second, the data proposition `EVEN` is a proof object,
thus an `Even` value, gives us information how the proof was constructed.



Construction of Even Numbers
----------------------------

Let's construct some even numbers using the `EVEN` data proposition.

\begin{code}
even0, even2, even4 :: EVEN
{-@ even0 :: Prop (EVEN Z) @-}
even0 = undefined 

{-@ even2 :: Prop (EVEN (S (S Z))) @-}
even2 = undefined

{-@ even4 :: Prop (EVEN (S (S (S (S Z))))) @-}
even4 = undefined
\end{code}

**Question:** Fill in the above definitions to construct the even numbers `0`, `2`, and `4`.

Since `EVEN` is a proof object one can inspect it, 
to, for example, show contradictions. 

\begin{code}
even1_false :: EVEN -> () 
{-@ even1_false :: Prop (EVEN (S Z)) -> {v:() | false} @-}
even1_false _ = undefined
\end{code}

**Question:** Show that `S Z` is not even, by inspection. 

Functions on Even Numbers
-------------------------

Let's now show that each even number,
other than `0`, can be written as `2 + n`, for some `n`.

\begin{code}
even_plus_2 :: N -> EVEN -> (N,()) 
{-@ even_plus_2 :: n:{N | n /= Z} 
                -> Prop (EVEN n) 
                -> (m::N, {v:() | n == S (S m)}) @-}
even_plus_2 _ _ = undefined 
\end{code}

As a final exercise, 
let's show that the sum of two even numbers is also even.

To do so, we first define the `plus` function:

\begin{code}
{-@ reflect plus @-}
plus :: N -> N -> N
plus Z     m = m
plus (S n) m = S (plus n m)
\end{code}

**Question:** Fill in the definition of the `even_plus` function.

\begin{code}
even_plus :: N -> N -> EVEN -> EVEN -> EVEN 
{-@ even_plus :: n:N -> m:N 
              -> Prop (EVEN n) -> Prop (EVEN m) 
              -> Prop (EVEN (plus n m)) @-}
even_plus _ _ _ _ = undefined 
\end{code}


Metatheory of Programming Languages
-----------------------------------

In the theory of programming languages, we often use 
theorem provers, like Liquid Haskell or Coq, to mechanize the proof 
of properties of programs.

Such proofs usually talk about _program evaluation_.  

Due to the [halting problem](https://en.wikipedia.org/wiki/Halting_problem)
we cannot prove, in general that program evaluation terminates, 
thus such concepts are encoded as data propositions (or inductive predicates).



As a simplification, let's consider the simply typed lambda calculus, 
with integers and functions.

\begin{code}
data Expr = EApp  Expr Expr 
          | ELam  Type Expr 
          | EBVar BVar | EFVar Var 
          | EInt  Int 

data Type =  TInt | TFun Type Type 
  deriving Eq 
\end{code}


Evaluation of Expressions 
-------------------------

We use data proposition to axiomatize the step relation 
of the language. 
That is, `Step e e'` defines the relation `e -> e'`.

\begin{code}
{-@ 
data Step where 
    SAppPL :: e1:Expr -> e1':Expr -> e2:Expr 
           -> Prop (Step e1 e1')          
           -> Prop (Step (EApp e1 e2) (EApp e1' e2)) 
  | SAppPR :: e1:Expr -> e2:Expr -> e2':Expr 
           -> Prop (Step e2 e2')
           -> Prop (Step (EApp e1 e2) (EApp e1 e2')) 
  | SAppE  :: e:Expr -> ex:Expr -> tx:Type 
           -> Prop (Step (EApp (ELam tx e) ex) (subst e ex)) 
  @-}
\end{code}


Evaluation of an expression is defined as the transitive closure of the step relation.
That is `Evals e e'` defines the relation `e ->* e'`, which, in general is not terminating. 

\begin{code}
{-@ 
data Evals where 
    ERefl :: e:Expr -> Prop {Evals e e}
  | EStep :: e1:{Expr | lc e1 } -> e2:{Expr | lc e2} -> e3:Expr
          -> Prop (Step  e1 e2)
          -> Prop (Evals e2 e3) 
          -> Prop (Evals e1 e3)  
  @-}
\end{code}


Typing of Expressions
---------------------

We use data propositions to axiomatize the typing relation of the language.
That is, `HasType g e t` defines the relation $\Gamma \vdash e : \tau$, 
where $\Gamma$ is the typing environment, $e$ is the expression and $\tau$ is the type.

\begin{code}
{-@ data HasType where 
       TApp :: g:Env -> e:Expr -> ex:Expr -> t:Type -> tx:Type 
            -> Prop (HasType g e (TFun tx t)) 
            -> Prop (HasType g ex tx)
            -> Prop (HasType g (EApp e ex) t) 
     | TLam :: g:Env -> e:Expr -> tx:Type -> t:Type 
            -> x:{Var | not (member x (dom g)) && not (member x (freeVars e))} 
            -> Prop (HasType (EBind x tx g) (subst e (EFVar x)) t) 
            -> Prop (HasType g (ELam tx e) (TFun tx t)) 
     | TVar :: g:Env -> x:{Var | member x (dom g)} 
            -> Prop (HasType g (EFVar x) (lookupEnv g x))
     | TTInt :: g:Env -> i:Int
            -> Prop (HasType g (EInt i) TInt)
 @-}
\end{code}

Soundness = Progress + Preservation
-----------------------------------

Having defined both the typing and evaluation relations,
we can connect them to show that our type system is sound.
To show soundness, following the 
[tradition of programming languages](https://www.cis.upenn.edu/~bcpierce/tapl/index.html), 
we prove the progress and preservation properties.


**Progress** states that a well-typed expression is either a value or can take a step: 

\begin{code}
{-@ progress :: e:Expr -> t:Type -> ht:Prop (HasType EEmp e t) 
                 -> Either {v:() | isValue e} (Expr, Step)<{\e' p -> prop p = Step e e'}> 
                 / [hasTypeSize ht] @-}
\end{code}


**Preservation** states that if an expression takes a step, 
then the resulting expression is also well-typed:

\begin{code}
{-@ preservation :: e:{Expr | lc e} -> t:Type -> hs:Prop (HasType EEmp e t) 
                 -> e':Expr -> Prop (Step e e') 
                 -> Prop (HasType EEmp e' t) 
                 /  [hasTypeSize hs] @-}
\end{code}

Soundness combines progress and preservation to inductively show that
a well-typed expression evaluates to some expression 
that is either a value or can take a step.

\begin{code}
soundness :: Expr -> Type -> Expr -> HasType -> Evals -> Either () (Expr, Step) 
{-@ soundness :: eo:{Expr | lc eo } -> t:Type -> e:Expr
              -> Prop (HasType EEmp eo t) 
              -> Prop (Evals eo e)
              -> Either {v:() | isValue e} (Expr, Step)<{\e' p -> prop p = Step e e'}> @-}
soundness eo t e eo_has_t eo_evals_e = case eo_evals_e of 
    ERefl _ -> progress eo t eo_has_t 
    EStep _eo e1 _e eo_step_e1 e1_eval_e -> 
        soundness e1 t e (preservation eo t eo_has_t e1 eo_step_e1) e1_eval_e
\end{code}



Summary
-------

In this lecture, we saw data propositions, which are used to axiomatize
the behavior of predicates in the data type definitions. 
Data propositions have two major uses. 
First, they are used to encode non-terminating functions,
like the evaluation function of a programming language.
Second, they construct proof objects, whose inspection can facilitate 
proof developments. 
These two features allow the mechanization of sophisticated proofs, 
like metatheory of programming languages, in theorem provers like Liquid Haskell.




Appendix: The rest of the Code 
-----------------------


\begin{code}
preservation :: Expr -> Type -> HasType -> Expr -> Step -> HasType 
preservation _ _ _ _ _ = undefined
progress :: Expr -> Type -> HasType -> Either () (Expr, Step)  
progress _ _ _ = undefined

{-@ data Env = EEmp 
             | EBind { eVar  :: Var
                     , eType :: Type
                     , eTail :: {g:Env | not (member eVar (dom g)) } 
                     } @-}

{-@ measure dom @-}
dom :: Env -> Set Var 
dom (EBind x _ g) = singleton x `union` dom g 
dom EEmp          = empty 


{-@ reflect lookupEnv @-}
lookupEnv :: Env -> Var -> Type 
{-@ lookupEnv :: g:Env -> {x:Var | member x (dom g)} -> Type  @-} 
lookupEnv (EBind x t g) y
  | x == y    = t 
  | otherwise = lookupEnv g y 


{-@ reflect eAppend @-}
{-@ eAppend :: g1:Env -> g2:{Env | disjoined (dom g1) (dom g2) } 
            -> {g:Env | dom g == union (dom g1) (dom g2) } @-}
eAppend :: Env -> Env -> Env 
eAppend EEmp            g2 = g2 
eAppend (EBind x tx g1) g2 = EBind x tx (eAppend g1 g2)


{-@ inline disjoined @-}
disjoined :: Ord a => Set a -> Set a -> Bool 
disjoined g1 g2 = intersection g1 g2 == empty

-- Define Proposition as the predicates you want to reason about.  

data Proposition 
  = HasType Env  Expr Type -- g |- e :: t 
  | Step    Expr Expr      -- e ->  e'
  | Evals   Expr Expr      -- e ->* e'



-- | Hastype Axiomatization (typing rules). 
-- | Prop (HasType g e t) defines g |- e : t




-- Proof Debugging 

{-@ assertProp :: p:Proposition  -> Prop p -> Prop p @-}
assertProp :: Proposition -> a -> a 
assertProp _ x = x 


-- | Measure for termination proofs 

hasTypeSize :: HasType -> Int  
{-@ hasTypeSize :: HasType -> {v:Int | 0 < v } @-}
{-@ measure hasTypeSize @-}
hasTypeSize (TTInt _ _)              = 1 
hasTypeSize (TVar _ _)               = 1 
hasTypeSize (TLam _ _ _ _ _ ht)      = hasTypeSize ht  + 1 
hasTypeSize (TApp _ _ _ _ _ ht1 ht2) = hasTypeSize ht1 + hasTypeSize ht2 + 1 


-- Haskell Definitions 

data Step where 
  SAppPL :: Expr  -> Expr -> Expr -> Step -> Step 
  SAppPR :: Expr  -> Expr -> Expr -> Step -> Step 
  SAppE  :: Expr  -> Expr -> Type -> Step 
  
  


data HasType where 
     TApp  :: Env -> Expr -> Expr -> Type -> Type -> HasType -> HasType -> HasType
     TLam  :: Env -> Expr -> Type -> Type -> Var -> HasType -> HasType
     TVar  :: Env -> Var ->  HasType
     TTInt :: Env -> Int -> HasType 







data Evals where 
  ERefl :: Expr -> Evals 
  EStep :: Expr -> Expr -> Expr -> Step -> Evals -> Evals  
\end{code}


\begin{code}

{-@ measure isValue @-}
isValue :: Expr -> Bool 
isValue (EApp _ _) = False 
isValue (ELam _ _) = True 
isValue (EBVar _)  = False 
isValue (EFVar _)  = False 
isValue (EInt  _)  = True 


{-@ measure freeVars @-}
freeVars :: Expr -> Set Var  
freeVars (EApp e1 e2) = freeVars e1 `union` freeVars e2 
freeVars (ELam _ e)   = freeVars e
freeVars (EFVar x)    = singleton x 
freeVars (EBVar x)    = empty
freeVars (EInt  _)    = empty


{-@ measure boundVars @-}
boundVars :: Expr -> Set Var 
boundVars (EApp e1 e2) = boundVars e1 `union` boundVars e2
boundVars (ELam _ e)   = boundVars e 
boundVars (EBVar x)    = singleton x 
boundVars (EFVar _)    = empty 
boundVars (EInt  _)    = empty
 

{-@ reflect subst @-}
{-@ subst :: e:Expr -> ex:Expr 
         -> {s:Expr | freeVars s = freeVars e || freeVars s = union (freeVars e) (freeVars ex) } @-} 
subst :: Expr -> Expr -> Expr 
subst e u = substBound e 0 u 

{-@ reflect substBound @-}
{-@ substBound :: e:Expr -> BVar -> ex:Expr 
               -> {s:Expr | freeVars s = freeVars e || freeVars s = union (freeVars e) (freeVars ex)} @-} 
substBound :: Expr -> BVar -> Expr -> Expr 
substBound (EApp e1 e2) x ex 
  = EApp (substBound e1 x ex) (substBound e2 x ex)
substBound (ELam t e) x ex 
  = ELam t (substBound e (x+1) ex)
substBound (EFVar y) _ _   
  =  EFVar y   
substBound (EInt i) _ _   
  =  EInt i    
substBound (EBVar y) x ex 
  | x == y    = ex 
  | otherwise = EBVar y  


{-@ reflect lc @-}
lc :: Expr -> Bool
lc e = lc_at 0 e 

{-@ reflect lc_at @-}
lc_at :: BVar -> Expr -> Bool 
lc_at k (EBVar i)    = i < k 
lc_at k (EFVar _)    = True 
lc_at k (EInt  _)    = True 
lc_at k (EApp e1 e2) = lc_at k e1 && lc_at k e2 
lc_at k (ELam _ e)   = lc_at (k+1) e 



type  Var = Int 
type BVar = Int 

{-@ type BVar = {i:Int | 0 <= i} @-} 
  

{-@ measure isTFun @-}
isTFun :: Type -> Bool 
isTFun (TFun _ _) = True 
isTFun _          = False 

{-@ typeSize :: Type -> Nat @-}
{-@ measure typeSize @-}
typeSize :: Type -> Int 
typeSize TInt        = 1
typeSize (TFun tx t) = 1 + typeSize tx + typeSize t 

data Env = EEmp | EBind Var Type Env
  deriving Eq

\end{code}

