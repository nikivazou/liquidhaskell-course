Data Types
============


\begin{code}
{- OPTIONS_GHC -fplugin=LiquidHaskell #-}
{- LIQUID "--no-termination" @-}
module Lecture_02_DataTypes where

import Data.List    (foldl')
import Prelude hiding (head, tail, (!!), map, zipWith, zip, take, drop, reverse)
import Data.Maybe   (fromJust)

main :: IO ()
main = return ()
\end{code}



In last lecture, we saw refinement types on primitive values and functions 
and the language of the predicates that includes arithmetic, boolean, and
uninterpreted functions. 
Today, we will see how to use refinement types on data types.
Concretely, 

1. We will define new and use new logical functions on user defined data types. 
2. We use refinements on definitions of data types to specify invariants.
3. We will see how to use LiquidHaskell to reason about Haskell's lists.



Measures 
------

We will start with the most famous data type, the list
and see how we can use refinement types for safe indexing in lists, 
e.g., to 

1. _define_ the length of a list, 
2. _compute_ the length of a list, and 
3. _restrict_ the indexing of lists to valid indices.


Here is the standard list data type in Haskell:

\begin{code}
data List a = Nil | Cons a (List a)
\end{code}

We use the *measure* definition to define the length of a list.

\begin{code}
{-@ measure llen @-}
{-@ llen :: List a -> Nat @-}
llen :: List a -> Int
llen Nil        = 0
llen (Cons x l) = 1 + llen l
\end{code}


_Note:_ The `measure` keyword has two uses in LiquidHaskell.

1. Last time we saw that the `measure` keyword is used to define an uninterpreted SMT function. 
2. Used without a type signature with the same name as a Haskell function, 
the `measure` keyword is used to lift the Haskell function to the refinement logic.


Concretely, a "measure" is a function that has *one* argument
which is a Algebraic Data Type (ADT), like a list. 
The one argument restriction is very important because it allows LiquidHaskell
to automate the verification.^[
    In a next lecture we will see how one can use reflection to lift in the logic 
    functions with more than one argument, but then verification is no more automated.
]
The measure definition "lifts" the Haskell function to the refinement logic,
by refining the types of the data constructors with the exact definition of the function. 

For example, the `llen` measure definition refines the type of the lists constructor to be:

~~~~~{.spec}
Nil  :: {v:List a | llen v = 0}
Cons :: x:a -> l:List a -> {v:List a | llen v = 1 + llen l}
~~~~~


With these refinements, verification can reason about the length of lists: 

\begin{code}

{-@ twoElems :: {v:List Int | llen v == 2} @-}
twoElems :: List Int 
twoElems = Cons 4 (Cons 2 Nil)

\end{code}


Type checking `twoElems`, using ANF, looks like this: 

~~~~~{.spec}

let l0 = Nil        :: {v:List a | llen v = 0}
    l1 = Cons 2 l0  :: {v:List a | llen v = 1 + llen l0}
in Cons 4 l1        :: {v:List a | llen v = 1 + llen l1}
~~~~~


Multiple Measures
------------------

We can define multiple measures for the same data type, 
in which case, the refinements are _conjoined_ together.

For example, we can define a measure that checks empiness of a list. 

\begin{code}
{-@ measure isempty @-}
isempty :: List a -> Bool
isempty Nil = True
isempty _   = False
\end{code}


With these two measure definitions, the types of the list constructors are refined to:

~~~~~{.spec}
Nil  :: {v:List a | llen v = 0 && isempty v}
Cons :: x:a -> l:List a -> {v:List a | llen v = 1 + llen l && not (isempty v)}
~~~~~


**Question:** Let's define the `head` and `tail` functions for lists.

\begin{code}

head :: List a -> a
head = undefined 

\end{code}

\begin{code}

tail :: List a -> List a
tail = undefined 

\end{code}


**Question:** Can you give a strong engouth type for tail 
to verify length of result? 


\begin{code}

{- oneElem :: {v:List Int | llen v == 1} @-}
oneElem :: List Int 
oneElem = tail twoElems

\end{code}



**Question:** Let's now define a safe indexing function for lists.


\begin{code}

{-@ (!!) :: xs:List a -> {i:Int | 0 <= i && i < llen xs } -> a @-}
(!!) :: List a -> Int -> a
(!!) = undefined

\end{code}

**Question:** Let's now define a safe lookup function for lists,
using the case sensitivity of refinement types. 

\begin{code}
safeLookup :: List a -> Int -> Maybe a
safeLookup = undefined
\end{code}


Recursive Functions 
----------------------

Let's write a recursive function that adds up the values of an integer list. 

\begin{code}
listSum :: List Int -> Int
listSum xs = go 0 0 
  where 
    go acc i  
      | i < llen xs = go (acc + (xs !! i)) (i+1)
      | otherwise   = acc
\end{code}

**Question:** What happens if you _replace_ the guard with `i <= llen xs`?

**Question:** Write a variant of the above function that 
computes the `absuluteSum` of the list, i.e., the sum of the absolute values of the elements.

\begin{code}
{-@ absSum :: List Int -> Int @-}
absSum :: List Int -> Int
absSum = undefined 
\end{code}

LiquidHaskell verifies `listSum`, or to be precise the safety of list indexing. 
The verification works because Liquid Haskell is able to _automatically infer_

~~~~~{.spec}
go :: Int -> {v:Int | 0 <= v && v <= llen xs} -> Int
~~~~~

which states that the second parameter `i` is between 0 and the length of the list (inclusive).
LiquidHaskell uses this and the test that `i < llen xs` to verify that the indexing is safe.

_Note:_ LiquidHaskell automatically tests the termination of recursive functions. 
The default termination metric for the above functions fail. Later, we will see how to fix this.
But for now, we can disable termination checking, but declaring functions as `lazy`.

\begin{code}
{-@ lazy listSum @-}
{-@ lazy absSum @-}
\end{code}

**Question:** Why does the type of `go` has `v <= llen xs` and not `v < llen xs`?


Higher-Order Functions
-----------------------
We already used the `go` structure twice, so let's generalize the common pattern! 
Let's refactor the above low-level recursive function
into a generic higher-order `loop`.

\begin{code}
{-@ lazy loop @-}
loop :: Int -> Int -> a -> (Int -> a -> a) -> a
loop lo hi base f =  go base lo
  where
    go acc i
      | i < hi    = go (f i acc) (i + 1)
      | otherwise = acc
\end{code}

We can now use `loop` to implement `listSum`:

\begin{code}
{-@ lazy listSum' @-}
listSum'      :: List Int -> Int
listSum' xs  = loop 0 n 0 body
  where
    body i acc  = acc + (xs !! i)
    n           = llen xs
\end{code}

\newthought{Inference} is a convenient option. LiquidHaskell finds:

\begin{code}
{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}
{-@ loop :: lo:Nat -> hi:{Nat|lo <= hi} -> a 
         -> (Btwn lo hi -> a -> a) -> a @-}
\end{code}

\noindent In English, the above type states that

- `lo` the loop *lower* bound is a non-negative integer
- `hi` the loop *upper* bound is a greater then or equal to `lo`,
- `f`  the loop *body* is only called with integers between `lo` and `hi`.

\noindent
It can be tedious to have to keep typing things like the above.
If we wanted to make `loop` a public or exported function, we
could use the inferred type to generate an explicit signature.

At the call `loop 0 n 0 body` the parameters `lo` and `hi` are
instantiated with `0` and `n` respectively, which, by the way
is where the inference engine deduces non-negativity.
Thus LiquidHaskell concludes that `body` is only called with
values of `i` that are *between* `0` and `(llen xs)`, which
verifies the safety of the call `xs !! i`.

**Question:**
Complete the implementation of `absoluteSum'` below.
When you are done, what is the type that is inferred for `body`?

\begin{code}
{-@ absoluteSum' :: List Int -> Nat @-}
absoluteSum' :: List Int -> Int
absoluteSum' xs = loop 0 n 0 body
  where
    body i acc   = undefined
    n            = llen xs
\end{code}


**Question:**
The following uses `loop` to compute
`dotProduct`s. Why does LiquidHaskell flag an error?
Fix the code or specification so that LiquidHaskell
accepts it. 

\begin{code}
{-@ ignore dotProduct @-}
-- >>> dotProduct ([1,2,3]) ( [4,5,6])
-- 32
{-@ dotProduct :: x:List Int -> y:List Int  -> Int @-}
dotProduct :: List Int -> List Int -> Int
dotProduct x y = loop 0 sz 0 body
  where
    body i acc = acc + (x !! i)  *  (y !! i)
    sz         = llen x
\end{code}



Folding (Indexed Lists)
----------------------------------------


Let's now use lists to represent sparse vectors, 
meaning vectors with many zeros. 

\begin{code}
{-@ type SparseN a N = [(Btwn 0 N, a)] @-}
\end{code}

\noindent Implicitly, all indices *other* than those in the list
have the value `0` (or the equivalent value for the type `a`).

\newthought{The Alias} `SparseN` is just a
shorthand for the (longer) type on the right, it does not
*define* a new type. If you are familiar with the *index-style*
length encoding e.g. as found in [DML][dml] or [Agda][agdavec],
then note that despite  appearances, our `Sparse` definition
is *not* indexed.

\newthought{Sparse Products}
Let's write a function to compute a sparse product

\begin{code}
{-@ sparseProduct  :: x:List Int -> SparseN Int (llen x) -> Int @-}
sparseProduct :: List Int -> [(Int, Int)] -> Int
sparseProduct x y   = go 0 y
  where
    go n []         = n
    go n ((i,v):y') = go (n + (x!!i) * v) y'
\end{code}

LiquidHaskell verifies the above by using the specification
to conclude that for each tuple `(i, v)` in the list `y`, the
value of `i` is within the bounds of the list `x`, thereby
proving `x !! i` safe.

\newthought{Folds}
The sharp reader will have undoubtedly noticed that the sparse product
can be more cleanly expressed as a [fold][foldl]:

~~~~~{.spec}
foldl' :: (a -> b -> a) -> a -> [b] -> a
~~~~~

\noindent We can simply fold over the sparse vector, accumulating the `sum`
as we go along

\begin{code}
{-@ sparseProduct'  :: x:List Int -> SparseN Int (llen x) -> Int @-}
sparseProduct' :: List Int -> [(Int, Int)] -> Int
sparseProduct' x y  = foldl' body 0 y
  where
    body sum (i, v) = sum + (x !! i) * v
\end{code}

\noindent
LiquidHaskell digests this without difficulty.
The main trick is in how the polymorphism of
`foldl'` is instantiated.

1. GHC infers that at this site, the type variable `b` from the
   signature of `foldl'` is instantiated to the Haskell type `(Int, a)`.

2. Correspondingly, LiquidHaskell infers that in fact `b`
   can be instantiated to the *refined* `(Btwn 0 (vlen x), a)`.

Thus, the inference mechanism saves us a fair bit of typing and
allows us to reuse existing polymorphic functions over containers
and such without ceremony.



Data Invariants: Sparse Vectors 
-------------------------------------

Liquid Haskell allows to write invariants on data types. 
As an example, let's revisit the sparse vector representation that we saw earlier.
The `SparseN` type alias we used got the job done, 
but is not pleasant to work with because we have no way of determining 
the *dimension* of the sparse vector.
Instead, let's create a new
datatype to represent such vectors:

\begin{code}
data Sparse a = SP { spDim   :: Int
                   , spElems :: [(Int, a)] }
\end{code}

\noindent
Thus, a sparse vector is a pair of a dimension and a list of
index-value tuples. Implicitly, all indices *other* than those
in the list have the value `0` or the equivalent value type `a`.

\newthought{Legal}
`Sparse` vectors satisfy two crucial properties.
First, the dimension stored in `spDim` is non-negative.
Second, every index in `spElems` must be valid, i.e.
between `0` and the dimension. Unfortunately, Haskell's
type system does not make it easy to ensure that
*illegal vectors are not representable*.^[The standard
approach is to use abstract types and
[smart constructors][smart-ctr-wiki] but even
then there is only the informal guarantee that the
smart constructor establishes the right invariants.]

\newthought{Data Invariants} LiquidHaskell lets us enforce
these invariants with a refined data definition:

\begin{code}
{-@ data Sparse a = SP { spDim   :: Nat
                       , spElems :: [(Btwn 0 spDim, a)]} @-}
\end{code}

\newthought{Refined Data Constructors} The refined data
definition is internally converted into refined types
for the data constructor `SP`:

~~~~~{.spec}
-- Generated Internal representation
data Sparse a where
  SP :: spDim:Nat
     -> spElems:[(Btwn 0 spDim, a)]
     -> Sparse a
~~~~~

\noindent In other words, by using refined input types for `SP`
we have automatically converted it into a *smart* constructor that
ensures that *every* instance of a `Sparse` is legal.
Consequently, LiquidHaskell verifies:

\begin{code}
okSP :: Sparse String
okSP = SP 5 [ (0, "cat")
            , (3, "dog") ]
\end{code}

\noindent but rejects, due to the invalid index:

\begin{code}
{-@ ignore badSP @-}
badSP :: Sparse String
badSP = SP 5 [ (0, "cat")
             , (6, "dog") ]
\end{code}

\newthought{Field Measures} It is convenient to write an alias
for sparse vectors of a given size `N`. We can use the field name
`spDim` as a *measure*, like `llen`. That is, we can use `spDim`
inside refinements^[Note that *inside* a refined `data` definition,
a field name like `spDim` refers to the value of the field, but *outside*
it refers to the field selector measure or function.]

\begin{code}
{-@ type SparseIN a N = {v:Sparse a | spDim v == N} @-}
\end{code}

\newthought{Sparse Products}
Let's write a function to compute a sparse product

\begin{code}
{-@ dotProd :: x:List Int -> SparseIN Int (llen x) -> Int @-}
dotProd :: List Int -> Sparse Int -> Int
dotProd x (SP _ y) = go 0 y
  where
    go sum ((i, v) : y') = go (sum + (x !! i) * v) y'
    go sum []            = sum
\end{code}

\noindent
LiquidHaskell verifies the above by using the specification
to conclude that for each tuple `(i, v)` in the list `y`, the
value of `i` is within the bounds of the list `x`, thereby
proving `x !! i` safe.

\newthought{Folded Product} We can port the `fold`-based product
to our new representation:

\begin{code}
{-@ dotProd' :: x:List Int -> SparseIN Int (llen x) -> Int @-}
dotProd' :: List Int -> Sparse Int -> Int
dotProd' x (SP _ y) = foldl' body 0 y
  where
    body sum (i, v) = sum + (x !! i)  * v
\end{code}

\noindent As before, LiquidHaskell checks the above by
[automatically instantiating refinements](#sparsetype)
for the type parameters of `foldl'`, saving us a fair
bit of typing and enabling the use of the elegant
polymorphic, higher-order combinators we know and love.

<div class="hwex" id="Sanitization"> \singlestar
Invariants are all well and good for data computed
*inside* our programs. The only way to ensure the
legality of data coming from *outside*, i.e. from
the "real world", is to write a sanitizer that will
check the appropriate invariants before constructing
a `Sparse` list. Write the specification and
implementation of a sanitizer `fromList`, so that
the following typechecks:
</div>

\hint You need to check that *all* the indices in
`elts` are less than `dim`; the easiest way is to
compute a new `Maybe [(Int, a)]` which is `Just`
the original pairs if they are valid, and `Nothing`
otherwise.

\begin{code}
fromList          :: Int   -> [(Int, a)] -> Maybe (Sparse a)
fromList dim elts = undefined

{- test :: SparseIN String 3 @-}
test     :: Maybe (Sparse String)
test     = fromList 3 [(0, "cat"), (2, "mouse")]
\end{code}

<div class="hwex" id="Addition">
Write the specification and implementation
of a function `plus` that performs the addition of two `Sparse`
vectors of the *same* dimension, yielding an output of that dimension.
When you are done, the following code should typecheck:
</div>

\begin{code}
plus     :: (Num a) => Sparse a -> Sparse a -> Sparse a
plus x y = undefined

{- testPlus :: SparseIN Int 3 @-}
testPlus :: Sparse Int
testPlus    = plus vec1 vec2
  where
    vec1 = SP 3 [(0, 12), (2, 9)]
    vec2 = SP 3 [(0, 8),  (1, 100)]
\end{code}


Ordered Lists {#orderedlists}
--------------

As a second example of refined data types, let's consider a
different problem: representing *ordered* sequences. Here's
a type for sequences that mimics the classical list:


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

{-@ ignore badList @-}
badList :: IncList Int
badList = 2 :< 1 :< 3 :< Emp      -- rejected by LH
\end{code}

\noindent
It's all very well to *specify* ordered lists.
Next, let's see how it's equally easy to *establish*
these invariants by implementing several textbook
sorting routines.

\newthought{Insertion Sort}
First, let's implement insertion sort, which converts an ordinary
list `[a]` into an ordered list `IncList a`.

\begin{code}
insertSort        :: (Ord a) => [a] -> IncList a
insertSort []     = Emp
insertSort (x:xs) = insert x (insertSort xs)
\end{code}

The hard work is done by `insert` which places an element into
the correct position of a sorted list. LiquidHaskell infers that
if you give `insert` an element and a sorted list, it returns a
sorted list.

\begin{code}
insert             :: (Ord a) => a -> IncList a -> IncList a
insert y Emp       = y :< Emp
insert y (x :< xs)
  | y <= x         = y :< x :< xs
  | otherwise      = x :< insert y xs
\end{code}

<div class="hwex" id="Insertion Sort">
Complete the implementation of the function below to
use `foldr` to eliminate the explicit recursion in `insertSort`.
</div>

\begin{code}
insertSort'     :: (Ord a) => [a] -> IncList a
insertSort' xs  = foldr f b xs
  where
     f          = undefined    -- Fill this in
     b          = undefined    -- Fill this in
\end{code}


We will come back to the concept of increasing lists 
and see how one can provide such a specification for Haskell's 
lists. But for now, let's study easier properties of lists.




The List API 
------------
Haskell comes with the list type `[a]` and a rich set of functions. 
LiquidHaskell comes with the `len` measure that, silimar to `llen` that we define, 
is used to reason about the length of lists.

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

Lists: Size Reducing API {#listreducing}
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

Summary 
------
Today we saw how refinement interact with data types. 
Concretely we saw how to define _measures_ to specify properties of user defined 
data and how to refine the definitions of data types to specify invariants.
Finally, we saw how all these features interact with existing Haskell libraries, 
and concretely how to use LiquidHaskell to reason about Haskell's lists. 