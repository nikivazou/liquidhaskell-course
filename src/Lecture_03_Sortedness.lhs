Sortedness  & Abstract Refinements 
============


\begin{code}
{- OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--no-termination" @-}
module Lecture_03_Sortedness where

main :: IO ()
main = return ()
\end{code}





Ordered Lists 
--------------

Last time we saw that we can use refinement types on 
the data type definitions to specify _invariants_ about the data types. 
Today we will use this invariant to specify _sortedness_ of lists.
 
Here's a type for sequences that mimics the classical list:


\begin{code}
data IncList a =
    Emp
  | (:<) { hd :: a, tl :: IncList a }

infixr 9 :<
\end{code}

\noindent
The Haskell type above does not state that the elements
are in order of course, but we can specify that requirement
by refining *every* element in `tl` to be *greater than* `hd`:

\begin{code}
{-@ data IncList a =
        Emp
      | (:<) { hd :: a, tl :: IncList {v:a | hd <= v}}  @-}
\end{code}

\newthought{Refined Data Constructors} Once again,
the refined data definition is internally converted
into a "smart" refined data constructor

~~~~~{.spec}
-- Generated Internal representation
data IncList a where
  Emp  :: IncList a
  (:<) :: hd:a -> tl:IncList {v:a | hd <= v} -> IncList a
~~~~~


\noindent which ensures that we can only create legal ordered lists.

\begin{code}
okList :: IncList Int
okList  = 1 :< 2 :< 3 :< Emp      -- accepted by LH

badList :: IncList Int
badList = 2 :< 1 :< 3 :< Emp      -- rejected by LH
\end{code}

\noindent
It's all very well to *specify* ordered lists.
Next, let's see how it's equally easy to *establish*
these invariants by implementing several textbook
sorting routines.

\newthought{Insertion Sort}
First, let's implement [insertion sort](https://en.wikipedia.org/wiki/Insertion_sort#/media/File:Insertion-sort-example-300px.gif), which converts an ordinary
list `[a]` into an ordered list `IncList a`.

\begin{code}
insertSort        :: (Ord a) => [a] -> IncList a
insertSort []     = Emp
insertSort (x:xs) = iinsert x (insertSort xs)
\end{code}

The hard work is done by `insert` which places an element into
the correct position of a sorted list. LiquidHaskell infers that
if you give `insert` an element and a sorted list, it returns a
sorted list.

\begin{code}
iinsert             :: (Ord a) => a -> IncList a -> IncList a
iinsert y Emp       = y :< Emp
iinsert y (x :< xs) = undefined 
\end{code}

**Question:** What should be the definition of `iinsert`?

<details>

<summary>**Solution**</summary>

<p> _The function `iinsert` can be defined as follows: _</p>

~~~~~{.spec}
iinsert             :: (Ord a) => a -> IncList a -> IncList a
iinsert y Emp       = y :< Emp
iinsert y (x :< xs) | y <= x    = y :< x :< xs 
                    | otherwise = x :< iinsert y xs 
~~~~~

</details>

**Question:** Can you update the definition of `insertSort` to use `foldr`?

<details>

<summary>**Solution**</summary>

<p> _The updated definition of `insertSort` using `foldr` is as follows: _</p>

~~~~~{.spec}
insertSort    :: (Ord a) => [a] -> IncList a
insertSort xs = foldr iinsert Emp xs
~~~~~

</details>


**Question:** What do you need to do to define insertion of decreasing lists?

<details>

<summary>**Solution**</summary>

<p> _First you need to define a data type for decreasing lists.
Next, adjust the definition of the sorting function to construct the new type._</p>

</details>



Abstraction over Sortedness
----------------------------

Ideally, we would like to write a verified sorted function 
that works for various sortedness properties and even over Haskell's lists. 
Of course, we cannot constraint all lists to be sorted. 
But, we can abstract the notion of sortedness over the data declaration. 


Thus, instead of explicitly stating that the head should be 
less that the element of the tail: 

~~~.{spec}
{-@ data IncList a = 
         Emp
      | (:<) { hd :: a, tl :: IncList {v:a | hd <= v}}  @-}
~~~

We say that there exists a predicate `p` that relates the head and all elements of the tail:

\begin{code}
data PList a = Nil | Cons a (PList a)

{-@ data PList a < p :: a -> a -> Bool> = 
        Nil
      | Cons { phd :: a, ptl :: PList < p >  a < p phd > }  @-}
\end{code}


**Refined Data Constructors** The internal data constructors are refined to be parametric 
with respect to the predicate `p`:

~~~~~{.spec}
-- Generated Internal representation
data PncList a where
  Nil  :: IncList a
  Cons :: forall a, p. hd:a -> tl:PList <p> {v:a | p hd} -> PList <p> a
~~~~~


Now this abstract predicate can be instantiated with different properties: 

\begin{code}
{-@ type IPList a = PList <{\hd v -> hd <= v}> a  @-}
{-@ type DPList a = PList <{\hd v -> hd >= v}> a  @-}
{-@ type EPList a = PList <{\hd v -> hd == v}> a  @-}

pl1, pl2, pl3, pl4 :: PList Int 

pl1 = Cons 1 (Cons 2 (Cons 3 Nil))
pl2 = Cons 3 (Cons 2 (Cons 1 Nil))
pl3 = Cons 1 (Cons 1 (Cons 1 Nil))
pl4 = Nil
\end{code}

**Question:** Give refinement types to the above four lists.

<details>

<summary>**Solution**</summary>

<p> _The list `pl1` is increasing, `pl2` is decreasing, `pl3` is equal and `pl4` is empty, 
which means that it could have any property._ </p>

~~~~~{.spec}
{-@ pl1 :: IPList Int @-}
{-@ pl2 :: DPList Int @-}
{-@ pl3 :: EPList Int @-}
{-@ pl4 :: IPList Int @-}
~~~~~

</details>





So, now the same Haskell lists can be refined to be either decreasing, increasing or equal. 
For example, the code below inserts into an increasing list:

\begin{code}
{-@ pinsert         :: (Ord a) => a -> IPList a -> IPList a @-}
pinsert             :: (Ord a) => a -> PList a -> PList a
pinsert y Nil       = y `Cons` Nil
pinsert y (x `Cons` xs) 
  | y <= x         = y `Cons` (x `Cons` xs)
  | otherwise      = x `Cons` pinsert y xs
\end{code}

**Question:** Can you adjust it to `insert` for decreasing lists?

<details>

<summary>**Solution**</summary>

<p> _You need to 1) change the type and 2) change the guard condition:_</p>

~~~~~{.spec}
{-@ pinsert         :: (Ord a) => a -> DPList a -> DPList a @-}
pinsert             :: (Ord a) => a -> PList a -> PList a
pinsert y Nil       = y `Cons` Nil
pinsert y (x `Cons` xs) 
  | y >= x         = y `Cons` (x `Cons` xs)
  | otherwise      = x `Cons` pinsert y xs
~~~~~

</details>



Haskell's Lists 
----------------

Liquid Haskell comes by default with parametrized lists. 
So we can instantiate the refinements over Haskell's lists directly.

\begin{code}
{-@ type IList a = [a]<{\hd v -> (v >= hd)}>  @-}
{-@ type DList a = [a]<{\hd v -> (v <= hd)}>  @-}
{-@ type EList a = [a]<{\hd v -> (v == hd)}>  @-}

ilist, dlist, elist :: [Int] 

{-@ ilist :: IList Int @-}
ilist = [1, 2, 3]
    
{-@ dlist :: DList Int @-}
dlist = [3, 2, 1]

{-@ elist :: EList Int @-}
elist = [1, 1, 1]
\end{code}

With these definitions, we can verify insertion of elements into Haskell's lists:

\begin{code}
{-@ insert         :: (Ord a) => a -> IList a -> IList a @-}
insert             :: (Ord a) => a -> [a] -> [a]
insert y []        = [y]
insert y (x:xs) 
  | y <= x         = y:x:xs
  | otherwise      = x:insert y xs

{-@ isort :: (Ord a) => IList a -> IList a @-}
isort :: (Ord a) => [a] -> [a]
isort []     = []
isort (x:xs) = insert x (isort xs)
\end{code}

**Question:** Let's also check if `isort` preserves the `len` of the list.
(Where `len` is the buildin measure for Haskell's lists.)

<details>

<summary>**Solution**</summary>

<p> _The updated types that ensure the length preservation are the following:_</p>

~~~~~{.spec}
{-@ insert :: (Ord a) => a -> x:IList a -> {v:IList a | len v = len x + 1 } @-}
{-@ isort  :: (Ord a) => x:IList a -> {v:IList a | len x = len v} @-}
~~~~~

</details>




This abstraction, called [Abstract Refinements][vazou13]
is very powerful since it allows lists to turn from increasing to decreasing. 
Because of this flexibility, Liquid Haskell can automatically verify 
the below code, used as the official [sorting function](https://hackage.haskell.org/package/base-4.21.0.0/docs/Data-List.html#v:sortBy) in Haskell, 
that very smartly sorts lists by collecting 
increasing and decreasing subsequences and merging them back together.

~~~{.spec}
{-@  sort :: (Ord a) => [a] -> IList a  @-}
sort :: (Ord a) => [a] -> [a]
sort xs = mergeAll (sequences xs)
  where
    sequences :: Ord a => [a] -> [[a]]
    sequences (a:b:xs)
      | a `compare` b == GT = descending b [a]  xs
      | otherwise           = ascending  b (a:) xs
    sequences [x] = [[x]]
    sequences []  = [[]]

    descending :: Ord a => a -> [a] -> [a] -> [[a]]
    descending a as (b:bs)
      | a `compare` b == GT = descending b (a:as) bs
    descending a as bs    = (a:as): sequences bs

    ascending :: Ord a => a -> ([a] -> [a]) -> [a] -> [[a]]
    ascending a as (b:bs) 
      | a `compare` b /= GT = ascending b (\ys -> as (a:ys)) bs
    ascending a as bs      = as [a]: sequences bs

    mergeAll []  = [] 
    mergeAll [x] = x
    mergeAll xs  = mergeAll (mergePairs xs)

    mergePairs :: Ord a => [[a]] -> [[a]]
    mergePairs (a:b:xs) = merge1 a b: mergePairs xs
    mergePairs [x]      = [x]
    mergePairs []       = []

    merge1 :: Ord a => [a] -> [a] -> [a]
    merge1 (a:as') (b:bs')
      | a `compare` b == GT = b:merge1 (a:as')  bs'
      | otherwise           = a:merge1 as' (b:bs')
    merge1 [] bs            = bs
    merge1 as []            = as
~~~


Dependent Pairs
----------------

Liquid Haskell has one more build in abstraction for pairs. 
So, internally the pairs are representing using abstract refinements as :

~~~{.spec}
data Pair a b < p :: a -> b> = P {fst :: a, snd :: b < p fst> }
~~~

The generated type is also parametric: 

~~~{.spec}
-- Generated Internal representation
(,) :: forall a b <p :: a -> b>. x:a -> b <p x> -> Pair a b <p>
~~~


This allows us to specify dependent pairs, where the second element depends on the first:

\begin{code}
{-@ pair1 :: (Int, Int) < {\f s -> f <= s} > @-}
pair1 :: (Int, Int)
pair1 = (2, 4)
\end{code}


So, now we can use the syntax of dependent type theory pairs to write interesting properties: 

\begin{code}
exGt :: Int -> (Int, ())
{-@ exGt :: x:Nat -> (Nat, ()) < {\f s -> f > x} > @-}
exGt x = (x+1, ())
\end{code}

The above code says that for each natural number `x`, there exists one `y` that is greater than `x`, 
taking us to a theorem proving territory, that we will return soon. 

**Question:** Is this property true for less than too? 

<details>

<summary>**Solution**</summary>

<p> _No, because it would encode that for every natural number, 
there exists a smaller natural number, which is not true.
But, it is true for integers:_</p>

~~~~~{.spec}
exLt :: Int -> (Int, ())
{-@ exLt :: x:Int -> (Int, ()) < {\f s -> f < x} > @-}
exLt x = (x-1, ())
~~~~~

</details>



Summary
-------

We saw three ways to specify sortedness of lists:

1. By refining the data type definition, 
2. By abstracting the sortedness property, and
3. By refining the list type directly.

The notion of abstract refinements is very powerful. 
In Liquid Haskell it is also used to encode dependent pairs 
and can be used in user defined data structures to specify various abstract dependencies.

