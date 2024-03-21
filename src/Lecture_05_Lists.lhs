Lists 
============


\begin{code}
{- OPTIONS_GHC -fplugin=LiquidHaskell #-}
module Lecture_5_Lists where

import Data.List    (foldl')
import Prelude hiding (head, tail, (!!), map, zipWith, zip, take, drop, reverse)
import Data.Maybe   (fromJust)

main :: IO ()
main = return ()
\end{code}


Haskell comes with the list type `[a]` and a rich set of functions. 
LiquidHaskell comes with the `len` measure that
is used to reason about the length of lists.
Here, we show and prove various properties of lists.


\newthought{A ListN} is a list with exactly `N` elements, and a
`ListX` is a list whose size is the same as another list `X`.  Note
that when defining refinement type aliases, we use uppercase variables
like `N` and `X` to distinguish *value* parameters from the lowercase
*type* parameters like `a`.

\begin{code}
{-@ type ListN a N = {v:[a] | len v = N} @-}
{-@ type ListX a X = ListN a {len X}     @-}
\end{code}


Lists: Size Preserving API
--------------------------

With the types and aliases firmly in our pockets, let us
write dimension-aware variants of the usual list functions.
The implementations are the same as in the standard library
i.e. [`Data.List`][data-list], but the specifications are
enriched with dimension information.

<div class="hwex" id="Map">
\newthought{map} yields a list with the same length as the input.
Fix the specification of `map` so that the `prop_map` is verified.
</div>

\begin{code}
{-@ map      :: (a -> b) -> xs:[a] -> [b] @-}
map :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (x:xs) = f x : map f xs

{-@ type TRUE = {v:Bool | v } @-}
{- prop_map :: [a] -> TRUE @-}
prop_map xs = length ys == length xs
  where
    ys      = map id xs
\end{code}

<div class="hwex" id="Reverse"> \singlestar
We can `reverse` the elements of a list as shown below, using the
tail recursive function `go`. Fix the signature for `go`
so that LiquidHaskell can prove the specification for `reverse`.
</div>

\hint How big is the list returned by `go`?

\begin{code}
{-@ ignore reverse @-}
{-@ reverse       :: xs:[a] -> ListX a xs @-}
reverse :: [a] -> [a]
reverse xs        = go [] xs
  where
    go acc []     = acc
    go acc (x:xs) = go (x:acc) xs
\end{code}


\newthought{zipWith} requires both lists to have the *same* size,
and produces a list with that same size. ^[As made explicit by
the call to `error`, the input type *rules out* the case where one
list is empty and the other is not, as in that case the former's
length is zero while the latter's is not, and hence, different.]

\begin{code}
{-@ zipWith :: (a -> b -> c) -> xs:[a]
                             -> ListX b xs
                             -> ListX c xs
  @-}
zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith f (a:as) (b:bs) = f a b : zipWith f as bs
zipWith _ [] []         = []
zipWith _ _  _          = error "no other cases"
\end{code}

\newthought{unsafeZip} The signature for `zipWith` is quite severe -- it
rules out the case where the zipping occurs only up to the shorter input.
Here's a function that actually allows for that case, where the output
type is the *shorter* of the two inputs:

\begin{code}
{-@ zip :: as:[a] -> bs:[b] -> {v:[(a,b)] | Tinier v as bs} @-}
zip :: [a] -> [b] -> [(a, b)]
zip (a:as) (b:bs) = (a, b) : zip as bs
zip [] _          = []
zip _  []         = []
\end{code}

\noindent The output type uses the predicate `Tinier Xs Ys Zs`
which defines the length of `Xs` to be the smaller of that of
`Ys` and `Zs`.^[In logic, `if p then q else r` is the same as
`p => q && not p => r`.]

\begin{code}
{-@ predicate Tinier X Y Z = Min (len X) (len Y) (len Z) @-}
{-@ predicate Min X Y Z = (if Y < Z then X = Y else X = Z)  @-}
\end{code}




<div class="hwex" id="Zip Unless Empty"> \doublestar
In my experience, `zip` as shown above is far too
permissive and lets all sorts of bugs into my code. As middle
ground, consider `zipOrNull` below. Write a specification
for `zipOrNull` such that the code below is verified by
LiquidHaskell.
</div>

\begin{code}
{-@ ignore zipOrNull @-}
zipOrNull       :: [a] -> [b] -> [(a, b)]
zipOrNull [] _  = []
zipOrNull _ []  = []
zipOrNull xs ys = zipWith (,) xs ys

{- test1 :: {v: _ | len v = 2} @-}
test1     = zipOrNull [0, 1] [True, False]

{- test2 :: {v: _ | len v = 0} @-}
test2     = zipOrNull [] [True, False]

{- test3 :: {v: _ | len v = 0} @-}
test3     = zipOrNull ["cat", "dog"] []
\end{code}

\hint Yes, the type is rather gross; it uses a bunch of
      disjunctions `||` , conjunctions `&&` and implications `=>`.

Lists: Size Reducing API 
------------------------

Next, let's look at some functions that truncate lists, in one way or another.

\newthought{Take} lets us grab the first `k` elements from a list:

\begin{code}
{-@ take'     :: n:Nat -> ListGE a n -> ListN a n @-}
take' :: Int -> [a] -> [a]
take' 0 _      = []
take' n (x:xs) = x : take' (n-1) xs
take' _ _      = error "won't  happen"
\end{code}

\noindent The alias `ListGE a n` denotes lists whose
length is at least `n`:

\begin{code}
{-@ type ListGE a N = {v:[a] | N <= len v} @-}
\end{code}

<div class="hwex" id="Drop">
`Drop` is the yang to `take`'s yin: it returns the remainder after extracting
the first `k` elements. Write a suitable specification for it so that the below
typechecks.
</div>

\begin{code}
{-@ ignore drop @-}
drop :: Int -> [a] -> [a]
drop 0 xs     = xs
drop n (_:xs) = drop (n-1) xs
drop _ _      = error "won't happen"

{- test4 :: ListN String 2 @-}
test4 = drop 1 ["cat", "dog", "mouse"]
\end{code}

<div class="hwex" id="Take it easy">
The version `take'` above is too restrictive;
it insists that the list actually have at least `n` elements.
Modify the signature for the *real* `take` function so that
the code below is accepted by LiquidHaskell.
</div>

\begin{code}
take :: Int -> [a] -> [a]
take 0 _       = []
take _ []      = []
take n (x:xs)  = x : take (n-1) xs

{-@ ignore test5 @-}
{- test5 :: [ListN String 2] @-}
test5 = [ take 2  ["cat", "dog", "mouse"]
        , take 20 ["cow", "goat"]        ]
\end{code}

\newthought{The Partition} function breaks a list into two
sub-lists of elements that either satisfy or fail a user
supplied predicate.

\begin{code}
partition          :: (a -> Bool) -> [a] -> ([a], [a])
partition _ []     = ([], [])
partition f (x:xs)
  | f x            = (x:ys, zs)
  | otherwise      = (ys, x:zs)
  where
    (ys, zs)       = partition f xs
\end{code}

We would like to specify that the *sum* of the output tuple's
dimensions equal the input list's dimension. Lets write measures
to access the elements of the output:

~~~~~{.spec}
{-@ measure fst @-}
fst  (x, _) = x

{-@ measure snd @-}
snd (_, y) = y
~~~~~

\noindent We can now refine the type of `partition` as:

\begin{code}
{-@ partition :: _ -> xs:_ -> {v:_ | Sum2 v (len xs)} @-}
\end{code}

\noindent where `Sum2 V N` holds for a pair of lists dimensions add to `N`:

\begin{code}
{-@ predicate Sum2 X N = len (fst X) + len (snd X) = N @-}
\end{code}

<div class="hwex" id="QuickSort">
Use `partition` to implement `quickSort`.
</div>

\begin{code}
-- >> quickSort [1,4,3,2]
-- [1,2,3,4]

{-@ quickSort    :: (Ord a) => xs:[a] -> ListX a xs @-}
quickSort :: (Ord a) => [a] -> [a]
quickSort []     = []
quickSort (x:xs) = undefined

{- test10 :: ListN String 2 @-}
test10 :: [String]
test10 = quickSort (drop 1 ["cat", "dog", "mouse"])
\end{code}