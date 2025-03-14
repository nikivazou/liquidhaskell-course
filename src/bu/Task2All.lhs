Task 2: Proving Theorems 
=========================

\begin{code}

module Task2 where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ infix : @-}
import Prelude  hiding (foldr, map)
import Language.Haskell.Liquid.ProofCombinators

{-@ type TRUE = {v:Bool | v} @-}

{- 

1. Fusions 
------------

1.1 **Map Fusion:** 
Map fusion states that for any two functions `f` and `g`, and any list `xs`, 
instead of applying `f` and `g` to `xs` separately, 
we can apply the composition of `f` and `g` to `xs` once.
It is an optimization property since it allows traversing the list `xs` only once! 

Let's first define and reflect the `map` and `compose` functions.

-}

{-@ reflect map @-}
map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x : map f xs

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) ->  a -> c
compose f g x = f (g x)


{- 

And now, using the equational reasoning operators
`===`, `***`, `QED`, and `?`, prove the map fusion property.

-}

{-@ mapFusion :: f:(b -> c) -> g:(a -> b) -> xs:[a] 
              -> {map (compose f g) xs == (map f) (map g xs)} @-}
mapFusion :: (b -> c) -> (a -> b) -> [a] -> Proof
mapFusion f g xs = undefined 

{- 

1.2 **PLE Automation:**
Now, using the `PLE` tactic, which is already activated in this module, 
write a shorter version of your proof. 

-}


{-@ mapFusionShorter :: f:(b -> c) -> g:(a -> b) -> xs:[a] 
              -> {map (compose f g) xs == (map f) (map g xs)} @-}
mapFusionShorter :: (b -> c) -> (a -> b) -> [a] -> Proof
mapFusionShorter f g xs = undefined 


{- 
1.3 **Fold Fusion:**

Folds also have a fusion property.

Let's first define and reflect the `foldr` function.

-}

{-@ reflect foldr @-}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f b (x:xs) = f x (foldr f b xs)
foldr f b []      = b

{- 
The fusion property for `foldr`
states that the composition of a function `h` with the fold `foldr f e`
is equivalent to folding a different function `g` over the list `xs`.
Prove the fold fusion property: 
-}


{-@ foldrFusion :: h:(b -> c) -> f:(a -> b -> b) -> g:(a -> c -> c) -> e:b -> ys:[a]
                -> fuse:(x:a -> y:b -> {h (f x y) == g x (h y)})
                -> { (compose h (foldr f e)) (ys) == foldr g (h e) ys }
  @-}
foldrFusion :: (b -> c) -> (a -> b -> b) -> (a -> c -> c) -> b -> [a]
             -> (a -> b -> Proof)
             -> Proof
foldrFusion h f g e _  fuse = undefined



{- 
2. Higher Order Properties
---------------------------

2.1 **Universal Fold Property:**
Fold has a (universal property)[https://www.cs.nott.ac.uk/~pszgmh/fold.pdf]
that states that folding a function `f` over a list is equivalent 
to applying a function `h` to the list, 
as long as the two functions satisfy two conditions, encoded as `base` and `step`, below. 
Prove the universal fold property. 
-}

{-@ foldrUniversal
      :: f:(a -> b -> b)
      -> h:([a] -> b)
      -> e:b
      -> ys:[a]
      -> base:{h [] == e }
      -> step: (x:a -> xs:[a] -> {h (x:xs) == f x (h xs)})
      -> { h ys == foldr f e ys }
  @-}
foldrUniversal :: (a -> b -> b) -> ([a] -> b) -> b
               -> [a] -> () -> (a -> [a] -> ()) -> ()
foldrUniversal f h e _ base step = undefined


{- 
2.2 **Fusion via Universality:**
The universal property provides a powerful way to prove fusion properties.

Prove, again the `foldrFusion` property, but this time using the `foldrUniversal` property.
That is, the proof should  call `foldrUniversal` with the appropriate arguments. 
As the `base` and `step` conditions, you can use the provided helper functions 
`fuse_base` and `fuse_step`, given in task `2.3`.
-}

{-@ foldrFusionUniv :: h:(b -> c) -> f:(a -> b -> b) -> g:(a -> c -> c) -> e:b -> ys:[a]
            -> fuse:(x:a -> y:b -> {h (f x y) == g x (h y)})
            -> { (compose h (foldr f e)) (ys) == foldr g (h e) ys }
  @-}
foldrFusionUniv :: (b -> c) -> (a -> b -> b) -> (a -> c -> c) -> b -> [a]
                -> (a -> b -> ())
                -> ()
foldrFusionUniv h f g e ys fuse
  = undefined 

{- 
2.3 **Completing the Proof:**

To complete the proof, we need to provide the helper functions `fuse_base` and `fuse_step`.
_Hint:_ The step goes by case splitting on the list while the base case is trivial.
-}

fuse_step :: (b -> c) -> (a -> b -> b) -> b -> (a -> c -> c)
         -> (a -> b -> ())
         -> a -> [a] -> ()
{-@ fuse_step :: h:(b -> c) -> f:(a -> b -> b) -> e:b -> g:(a -> c -> c)
         -> thm:(x:a -> y:b -> { h (f x y) == g x (h y)})
         -> x:a -> xs:[a]
         -> {(compose h (foldr f e)) (x:xs) == g x ((compose h (foldr f e)) (xs))}
  @-}
fuse_step h f e g thm x _ = undefined 



fuse_base :: (b -> c) -> (a -> b -> b) -> b -> ()
{-@ fuse_base :: h:(b -> c) -> f:(a -> b -> b) -> e:b
              -> { compose h (foldr f e) [] == h e } @-}
fuse_base h f e = undefined



{- 
3. Encoding of Logical Properties
----------------------------------

The following three logical properties are encoded as 
refinement types, using the encoding presented in the 
[class](https://nikivazou.github.io/lh-course/Lecture_08_NaturalDeduction.html). 

Prove these properties, by defining the Haskell function definitions 
for `lp1`, `lp2`, and `lp3`:
-}

{- 
3.1 **Distributivity of `And` over `Or`:**
$$ lp_1  \doteq (p \land (q \lor r)) \Rightarrow ((p \land q) \lor (p \land r)) $$
-}

{-@ lp1 :: p:Bool -> q:Bool -> r:Bool 
       -> ({v:() | p}, Either {v:() | q} {v:() | r})
       -> Either ({v:() | p}, {v:() | q}) ({v:() | p}, {v:() | r})
   @-}
lp1 :: Bool -> Bool -> Bool -> (() , Either () ()) 
    -> Either (() , ()) (() , ())
lp1 _ _ _ _ = undefined


{- 
3.2 **Contraposition:**

$$ lp_2 \doteq (p \Rightarrow q) \Rightarrow \neg q \Rightarrow \neg p $$
-}

{-@ lp2 :: p:Bool -> q:Bool 
        -> ({v:() | p} -> {v:() | q})
        -> ({v:() | q} -> {v:() | false})
        -> ({v:() | p} -> {v:() | false}) @-}
lp2 :: Bool -> Bool -> (() -> ()) -> (() -> ()) -> (() -> ())
lp2 _ _ _ _ _ = undefined


{- 
3.3 **Existential Introduction:**

$$ lp_3 \doteq ((\forall x. p\ x \Rightarrow q) \land \exists x.  p\ x) \Rightarrow q $$
-}

{-@ lp3 :: p:(a -> Bool) -> q:Bool 
       -> ((x:a -> {v:() | p x} -> {v:() | q}), (x::a, {v:() | p x}))
       -> {v:() | q} @-}
lp3 :: (a -> Bool) -> Bool -> (a -> () -> (), (a, ())) -> ()
lp3 _ _ _ = undefined
\end{code}