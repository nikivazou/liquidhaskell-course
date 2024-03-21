Task 1: Program Verification  
-------------

\begin{code}

{- OPTIONS_GHC -fplugin=LiquidHaskell #-}
module Task1 where

import Data.Set hiding (insert, elems, take, drop)
import Prelude  hiding (take, drop)


{-@ type TRUE = {v:Bool | v} @-}
\end{code}


1. Lists 
---------

**1.1 Length Preservation:** 
The function `append` below takes two lists and 
returns a new list that is the concatenation of the two input lists.
Complete the type specification of `append` below, so that the property `prop_append_1`
is accepted by LiquidHaskell.

\begin{code}
{-@ append :: xs:[a] -> ys:[a] -> [a] @-}
append :: [a] -> [a] -> [a]
append [] ys     = ys
append (x:xs) ys = x : append xs ys


{-@ prop_append_1 :: (Ord a) => [a] -> [a] -> TRUE @-}
prop_append_1 :: (Ord a) => [a] -> [a] -> Bool
prop_append_1 xs ys = length (append xs ys) == length xs + length ys
\end{code}


**1.2 Element Preservation:** 
Append also preserves the elements of the input lists.
We encode the elements of the list using the measure `elems` below.

\begin{code}
{-@ measure elems @-}
elems        :: (Ord a) => [a] -> Set a
elems []     = empty
elems (x:xs) = singleton x `union` elems xs
\end{code}

Edit the type specification of `append` above, 
so that the properties `prop_append_2` and `prop_append_3` are accepted by LiquidHaskell.

\begin{code}
{-@ prop_append_2 :: (Ord a) => [a] -> [a] -> TRUE @-}
prop_append_2 :: (Ord a) => [a] -> [a] -> Bool
prop_append_2 xs ys = isSubsetOf (elems xs) (elems (append xs ys))

{-@ prop_append_3 :: (Ord a) => [a] -> [a] -> TRUE @-}
prop_append_3 :: (Ord a) => [a] -> [a] -> Bool
prop_append_3 xs ys = isSubsetOf (elems xs) (elems (append xs ys))
\end{code}

**1.3 Halve:** 
The function `halve` below behaves the opposite of append. 
It takes a list and returns a pair of lists such that the elements of the input list are the union of the elements of the two output lists.
Complete the definition of `halve` below, so that the type signature is accepted by LiquidHaskell.

\begin{code}
{-@ halve :: xs:[a] 
          -> {v:([a],[a]) | len (fst v) + len (snd v) = len xs && elems xs = union (elems (fst v)) (elems (snd v)) } @-}
halve :: [a] -> ([a],[a])
halve []         = undefined 
halve [x]        = undefined 
halve (x1:x2:xs) = undefined 
\end{code}



2. Insertion Sort 
-----------------

In the class we saw that refinements of data type definitions can be used 
to encode increasing lists and use them to define insertion sort:

\begin{code}
data IncList a = Emp | (:<) a (IncList a)
{-@ data IncList a =
        Emp
      | (:<) { hd :: a, tl :: IncList {v:a | hd <= v}}  @-}

infixr 9 :<

{-@ insert :: (Ord a) => x:a -> xs:IncList a -> IncList a @-}
insert :: (Ord a) => a -> IncList a -> IncList a
insert y Emp       = y :< Emp
insert y (x :< xs)
  | y <= x         = y :< xs
  | otherwise      = x :< insert y xs

isort :: (Ord a) => [a] -> IncList a
isort []     = Emp
isort (x:xs) = insert x (isort xs)
\end{code}


**2.1 Length Preservation:**
Measures can be defined for `IncList`s too. For example, the measure `ilen` below defines 
the length of an `IncList`.

\begin{code}
ilen :: IncList a -> Int
{-@ ilen :: IncList a -> Nat @-}
{-@ measure ilen @-}
ilen Emp = 0
ilen (_ :< xs) = 1 + ilen xs
\end{code}

Give the proper type specification for `insert` so that `isort` satisfies the below type: 

~~~.{spec}
{-@ isort :: (Ord a) => xs:[a] -> {v:IncList a | ilen v = len xs } @-}
~~~

_Note:_ You should have discovered a bug in the code above. Fix it!

**2.2 Element Preservation:**
We can also measure the elements of an `IncList` using the measure `ielems` below.

\begin{code}
ielems :: Ord a => IncList a -> Set a 
{-@ ielems :: Ord a => IncList a -> Set a @-}
{-@ measure ielems @-}
ielems Emp = empty 
ielems (x :< xs) = singleton x `union` ielems xs
\end{code}

Give the proper type specification for `insert` so that `isort` satisfies the below type: 

~~~.{spec}
{-@ isort :: (Ord a) => xs:[a] -> {v:IncList a | ilen v = len xs && ielems v = elems xs } @-}
~~~


3. Merge Sort 
-------------
The code below defines merge sort using lists refined to be increasing.

\begin{code}
{-@ type IList a = [a]<{\x y -> x <= y}>@-}

{-@ merge :: Ord a => xs:IList a -> ys:IList a 
          -> {v:IList a | len v = len xs + len ys && elems v = union (elems xs) (elems ys) } @-}
merge :: Ord a => [a] -> [a] -> [a]
merge [] ys         = ys
merge xs []         = xs
merge (x:xs) (y:ys) = undefined 

{-@ msort :: Ord a => xs:[a] -> {v:IList a | len v = len xs && elems v = elems xs} @-}
msort :: Ord a => [a] -> [a]
msort []  = []
msort [x] = [x]
msort  xs = merge (msort left) (msort right)
            where (left,right) = halve xs
\end{code}

**3.1 Merge** 
Complete the definition of `merge` above so that the type signature is accepted by LiquidHaskell.

**3.2 Termination of Merge** 
Termination of `merge` is not trivially shown. Provide a termination metric for `merge` 
so that you remove the `lazy` annotation below.

\begin{code}
{-@ lazy merge @-}
\end{code}


**3.3 Termination of Msort**
Termination of `msort` is also not trivial. 
Can you remove the `lazy` annotation below by providing a termination metric for `msort`?

\begin{code}
{-@ lazy msort @-}
\end{code}

_Hint:_ You have to refine the result of `halve` to ensure that 
when the input list has more than 2 elements, then each of the two output lists is smaller than the input list.