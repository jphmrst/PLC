---
title     : "NatData: Data structures with natural numbers"
layout    : page
prev      : /Naturals/
permalink : /NatData/
next      : /Poly/
---

```
module plc.fp.NatData where
open import Data.Bool
open import Data.Nat

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
```

## Pairs of numbers

In a `data` definition, each constructor can take any number of
arguments — none (as with `true`, `false` and `zero`), one (as with
`suc`), or more than one:

```
data NatProd : Set where
  pair : ℕ → ℕ → NatProd
```

This declaration can be read: "The one and only way to construct a
pair of numbers is by applying the constructor `pair` to two arguments
of type ℕ."

#### Exercise `trynatpair` (starting) {#trynatpair}

Write an expression for forming a `NatProd` from the natural numbers
`3` and `5`.  Use the `C-c C-n` key sequence as in Exercise
`try-nat-defs` to check your expression.

#### Exercise `sort2` (starting) {#sort2}

Write a function `sort2` which accepts two numbers, and then creates a
pair with the smaller of the arguments as the first pair element, and
the larger as the second pair element.

    sort2 : ℕ → ℕ → NatProd
    -- Your definition here

    _ : sort2 3 5 ≡ pair 3 5
    _ = refl

    _ : sort2 5 3 ≡ pair 3 5
    _ = refl

    _ : sort2 4 4 ≡ pair 4 4
    _ = refl

### Extracting the elements of a pair

Here are simple functions for extracting the first and second
components of a pair:

```
fst : NatProd → ℕ
fst (pair x y) = x

snd : NatProd → ℕ
snd (pair x y) = y
```

And here is a function for swapping the two elements of a pair:

```
swapPair : NatProd → NatProd
swapPair (pair x y) = pair y x
```

## Lists of numbers

Pairs have only one possible form.  But to represent singly-linked
lists, we must account for two possible forms in the same way that
natural numbers have two possible forms.  A list of natural numbers is
either the empty list, or else a pair of a number and another list.

```
infixr 5 _∷_

data NatList : Set where
  [] : NatList
  _∷_ : ℕ → NatList → NatList
```

We are using symbols here rather than a name written with letters as
with pairs — but Agda has very few "special" characters, so these are
valid names just as `pair` is a valid name.  The name `[]`, often
pronounced _nil_, represents the empty list.  It is a constructor, but
needs no arguments to construct the value.  The constructor `∷` is
often pronounced _cons_.  The first argument to a `∷` constructor is
what we call the _head_ or a list, and the second argument is what we
call the _tail_.

The underscores `_` _are_ special characters, and are not part of the
name.  As with operators like `≡` and `+` which we have seen before,
the underscore shows how `∷` shows be written with its first argument
before it, and its second argument after it.

The `infixr` declaration tells Agda that we want `∷` to be
_right-associative_.  That is, if we write `x ∷ y ∷ z` for some
expressions `x`, `y` and `z`, then we want Agda to understand that
expressions to be the same as `x ∷ (y ∷ z)`, and **not** `(x ∷ y)
∷ z`.  The number `5` tells Agda that most other operations should be
grouped before applying `∷`.  So for example, `x ∷ y + 2 ∷ z` will
mean `x ∷ (y + 2) ∷ z`, and not `(x ∷ y) + (2 ∷ z)`.  This value
is called the _precedence_ of the `∷` operator.

For example, here is a three-element list:

```
mylist : NatList
mylist = 10 ∷ 20 ∷ 30 ∷ []
```

#### Exercise `trynatlist` (starting) {#trynatlist}

Write an expression for the list containing the numbers 10, 9, 8, 7
and 6 (in that order).

### Functions on lists

Next let's look at several functions for constructing and manipulating
lists.  First, the `repeat` function takes a number `n` and a `count`
and returns a list of length `count` in which every element is `n`.

```
repeat : ℕ -> ℕ -> NatList
repeat n zero = []
repeat n (suc count') = n ∷ repeat n count'
```

The `length` function calculates the length of a list.

```
length : NatList -> ℕ
length [] = 0
length (x ∷ xs) = 1 + length xs
```

The `++` function (pronounced "append") concatenates two lists.

```
infixr 5 _++_

_++_ : NatList → NatList → NatList
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys
```

A list appended to a non-empty list yields a list with the head the
same as the head of the non-empty list, and a tail the same as the
other list appended to tail of the non-empty list.

#### Exercise `tryrepeat` (starting) {#tryrepeat}

Does the expression `repeat 3 5` produce a list of length 3 containing
the number 5, or a list of length 5 containing the number 3?  Work out
your answer from the definition before using a call to Agda to check
your idea.  What happens if either the first or last argument is an
empty list?  Both?

#### Exercise `nonzeros` (practice) {#nonzeros}

Complete the definition of `nonzeros`.  The assertion after the
definition template shows (to both you and to Agda) what the function
should do.  The exercises will often include these statements, which
serve as tests for your code: if Agda cannot transform the expression
`nonzeros (0 ∷ 1 ∷ 0 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ [])` into the expression
`1 ∷ 2 ∷ 3 ∷ []` using your definition of `nonzeros`, then loading
the file will raise an error.

But as in earlier examples, you must move this code to the left
margin, and enclose it withing three backticks `` ` `` so that Agda
actually does load your code and the test.  Having this file load
successfully because Agda ignores your code for this exercise is not a
form of success on the exercise!

    nonzeros : NatList → NatList
    nonzeros [] = []
    -- Add your cases here

    _ : nonzeros (0 ∷ 1 ∷ 0 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
    _ = refl

#### Exercise `oddmembers` (practice) {#oddmembers}

Complete the definition of `oddmembers`. Have a look at the test to
understand what it should do, and use the function `odd` from the
[Naturals]({{ site.baseurl }}/Naturals/) section.

    oddmembers : NatList -> NatList
    -- Add your cases here

    _ : oddmembers (0 ∷ 1 ∷ 2 ∷ 3 ∷ 3 ∷ 0 ∷ []) ≡ (1 ∷ 3 ∷ 3 ∷ [])
    _ = refl

#### Exercise `countOddMembers` (practice) {#countOddMembers}

Complete the definition of `countOddMembers`, using the tests
to understand what these functions should do.

    countOddMembers : NatList -> ℕ
    -- Your definition goes here
    
    _ : countOddMembers (0 ∷ 1 ∷ 2 ∷ 3 ∷ 3 ∷ 0 ∷ []) ≡ 3
    _ = refl
    
    _ : countOddMembers (0 ∷ 2 ∷ 0 ∷ []) ≡ 0
    _ = refl
    
    _ : countOddMembers [] ≡ 0
    _ = refl

#### Exercise `reverse` (practice) {#reverse}

Write a function `reverse`, which takes a `NatList`, and returns
another list with the same elements in the reverse order.

    reverse : NatList → NatList
    -- Your definition goes here
    
    _ : reverse (0 ∷ 1 ∷ 2 ∷ 3 ∷ 3 ∷ 0 ∷ []) ≡ (0 ∷ 3 ∷ 3 ∷ 2 ∷ 1 ∷ 0 ∷ [])
    _ = refl
    
    _ : reverse (0 ∷ 2 ∷ 0 ∷ []) ≡ (0 ∷ 2 ∷ 0 ∷ [])
    _ = refl

    _ : reverse [] = []
    _ = refl

#### Exercise `removeOddMembers` (practice) {#removeOddMembers}

Complete the definition of `removeOddMembers`.

    removeOddMembers : NatList -> NatList
    -- Your definition goes here
    
    _ : removeOddMembers (0 ∷ 1 ∷ 2 ∷ 3 ∷ 3 ∷ 0 ∷ []) ≡ 1 ∷ 3 ∷ 3 ∷ []
    _ = refl
    
    _ : removeOddMembers (0 ∷ 2 ∷ 0 ∷ []) ≡ 0 ∷ 2 ∷ 0 ∷ []
    _ = refl
    
    _ : removeOddMembers [] ≡ []
    _ = refl

#### Exercise `doubleAll` (practice) {#doubleAll}

Write a function `doubleAll` which takes a list of numbers, and
returns a list of the same length with double the value of each
respective element.

    doubleAll : NatList → NatList
    -- Your definition here

    _ : doubleAll [] ≡ []
    _ = refl

    _ : doubleAll (2 ∷ []) ≡ (4 ∷ [])
    _ = refl

    _ : doubleAll (1 ∷ 3 ∷ 4 ∷ []) ≡ (2 ∷ 6 ∷ 8 ∷ [])
    _ = refl

#### Exercise `alternate` (practice) {#alternate}

Complete the following definition of `alternate`, which interleaves
two lists into one, alternating between elements taken from the first
list and elements from the second.  See the tests below for more
specific examples.

Hint: one natural and elegant way of writing `alternate` will fail to
satisfy Coq's requirement that all function definitions be "obviously
terminating."  If you find yourself in this rut, look for a slightly
more verbose solution that considers elements of both lists at the
same time.  One possible solution involves defining a new kind of
pairs, but this is not the only way.

    alternate : NatList → NatList → NatList
    -- Your solution goes here

    _ : alternate (1 ∷ 2 ∷ 3 ∷ []) (4 ∷ 5 ∷ 6 ∷ [])
                   ≡ (1 ∷ 4 ∷ 2 ∷ 5 ∷ 3 ∷ 6 ∷ [])
    _ = refl

    _ : alternate (1 ∷ 2 ∷ 3 ∷ []) (4 ∷ []) ≡ (1 ∷ 4 ∷ 2 ∷ 3 ∷ [])
    _ = refl

#### Exercise `isPalendrome` (practice) {#isPalendrome}

Write a function `isPalendrome` which checks if a `NatList` is the
same backwards as forwards.

    isPalendrome : NatList → Bool
    -- Your definition goes here

    _ : isPalendrome (1 ∷ 2 ∷ 3 ∷ 2 ∷ 1 ∷ []) ≡ true
    _ = refl

    _ : isPalendrome (1 ∷ 2 ∷ 3 ∷ 3 ∷ 2 ∷ 1 ∷ []) ≡ true
    _ = refl

    _ : isPalendrome (1 ∷ 2 ∷ 3 ∷ 2 ∷ 4 ∷ []) ≡ false
    _ = refl

    _ : isPalendrome [] ≡ true
    _ = refl

#### Exercise `noNeighborDups` (practice) {#noNeighborDups}

Write a function `noNeighborDups` which returns a `NatList` which is
the same as its argument, except that consecutive instances of the
same value are removed.

    noNeighborDups : NatList → NatList
    -- Your definition goes here

    _ : noNeighborDups (1 ∷ 2 ∷ 3 ∷ 1 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ 1 ∷ []
    _ = refl

    _ : noNeighborDups (1 ∷ 2 ∷ 2 ∷ 2 ∷ 3 ∷ 3 ∷ 1 ∷ 1 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ 1 ∷ []
    _ = refl

    _ : noNeighborDups [] ≡ []
    _ = refl

#### Exercise `value21` (practice) {#value21}

How would you define a data type to represent the different cards of a
deck of poker cards? How would you represent a hand of cards?

Define a function `value21` which, given a hand of cards calculates
its values according to the rules of 21 (Blackjack): that is, all the
cards from 2 to 10 are worth their face value. Jack, Queen, King count
as 10. The Ace card is worth 11, but if this would mean the overall
value of the hand exceeds 21, then an ace is valued at 1.

#### Exercise `stringlists` (practice) {#stringlists}

```
open import Data.String
```

Define a data type `StringList`, which is a linked list like a
`NatList` but which holds strings (use `[]ₛ` and `∷ₛ` as its
constructors).  Write the functions `concList`, which takes a
`StringList` and concatenates its elements down to a single `String`.

    concList : StringList → String
    -- Your definition goes here

    _ : concList ("H" ∷ₛ "e" ∷ₛ "ll" ∷ₛ "o" ∷ₛ []ₛ) ≡ "Hello"
    _ = refl

## Bags via lists

A _bag_ (or _multiset_) is like a set, except that each element can
appear multiple times rather than just once.  One possible
representation for a bag of numbers is as a list.

```
Bag : Set
Bag = NatList
```

#### Exercise `bagcount` (practice) {#bagcount}

Complete the following definition of `count` which returns the number
of times a particular value occurs in a bag.

    count : ℕ → Bag → ℕ
    -- Your definition goes here

    _ : count 1 (1 ∷ 2 ∷ 3 ∷ 1 ∷ 4 ∷ 1 ∷ []) = 3
    _ = refl

    _ : count 6 (1 ∷ 2 ∷ 3 ∷ 1 ∷ 4 ∷ 1 ∷ []) = 0
    _ = refl

#### Exercise `bagsum` (practice) {#bagsum}

Multiset `sum` is similar to set `union`: `sum a b` contains all the
elements of `a` and of `b`.  (Mathematicians usually define `union` on
multisets a little bit differently — using `max` instead of `sum` —
which is why we don't call this operation `union`.)  Try to define
`sum` in a single clause, in terms of other functions which you have
already defined, instead of explicitly setting up a recursive
definition.

    sum : Bag -> Bag -> Bag
    sum b1 b2 = ?

    _ : count 1 (sum (1 ∷ 2 ∷ 3 ∷ []) (1 ∷ 4 ∷ 1 ∷ [])) ≡ 3.
    _ = refl

#### Exercise `bagadd` (practice) {#bagadd}

The `add` function on bags takes one number, plus a bag, and returns a
new bag which includes all of the elements of the old bag, plus the
given number.

    add : ℕ → Bag → Bag
    add n b = ?
    
    _ : count 1 (add 1 (1 ∷ 4 ∷ 1 ∷ [])) ≡ 3
    _ = refl

#### Exercise `bagmember` (practice) {#bagmember}

The `member` function returns true exactly when its bag argument
contains its number argument at least once.

    member ∷ ℕ → Bag → Bool
    member n b = ?

    _ : member 1 (1 ∷ 4 ∷ 1 ∷ []) ≡ True
    _ = member 2 (1 ∷ 4 ∷ 1 ∷ []) ≡ False

#### Exercise `bagremoveone` (practice) {#bagremoveone}

When `removeOne` is applied to a bag without the number to remove, it
should return the same bag unchanged.

    removeOne : ℕ → Bag → Bag
    removeOne n b = ?

    _ : count 5 (remove_one 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 1 ∷ [])) ≡ 0
    _ = refl
    
    _ : count 5 (remove_one 5 (2 ∷ 1 ∷ 4 ∷ 1 ∷ [])) ≡ 0
    _ = refl
    
    _ : count 4 (remove_one 5 (2 ∷ 1 ∷ 4 ∷ 5 ∷ 1 ∷ 4 ∷ [])) ≡ 2
    _ = refl
    
    _ : count 5 (remove_one 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 5 ∷ 1 ∷ 4 ∷ [])) ≡ 1
    _ = refl

#### Exercise `bagremoveall` (practice) {#bagremoveall}

    removeAll : ℕ → Bag → Bag
    removeAll n b = ?
    
    _ : count 5 (remove_all 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 1 ∷ [])) ≡ 0
    _ = refl
    
    _ : count 5 (remove_all 5 (2 ∷ 1 ∷ 4 ∷ 1 ∷ [])) ≡ 0
    _ = refl
    
    _ : count 4 (remove_all 5 (2 ∷ 1 ∷ 4 ∷ 5 ∷ 1 ∷ 4 ∷ [])) ≡ 2
    _ = refl
    
    _ : count 5
          (remove_all 5
            (2 ∷ 1 ∷ 5 ∷ 4 ∷ 5 ∷ 1 ∷ 4 ∷ 5 ∷ 1 ∷ 4 ∷ [])) ≡ 0
    _ = refl

#### Exercise `bagsubset` (practice) {#bagsubset}

One bag is a subset of another if the former contains no more
occurences of any element than the latter.

    subset : Bag → Bag → Bool
    subset b1 b2 = ?
    
    _ : subset (1 ∷ 2 ∷ []) (2 ∷ 1 ∷ 4 ∷ 1 ∷ []) ≡ True
    _ = refl

    _ : subset (1 ∷ 2 ∷ 2 ∷ []) (2 ∷ 1 ∷ 4 ∷ 1 ∷ []) = False
    _ = refl
    
## Options

Suppose we want to write a function that returns the `n`th element of
some list.  If we give it type `ℕ → NatList → ℕ`, then we'll have to
choose some number to return when the list is too short.

```
nthBad : NatList -> ℕ -> ℕ
nthBad [] _ = 42
nthBad (x ∷ _) 0 = x
nthBad (_ ∷ xs) (suc n) = nthBad xs n
```

This solution is not so good: If `nth_bad` returns `42`, we can't tell
whether that value actually appears on the input without further
processing. A better alternative is to change the return type of
`nthBad` to include an error value as a possible outcome. We call
this type `NatMaybe`.

```
data NatMaybe : Set where
  nothing : NatMaybe
  just : ℕ → NatMaybe
```

We can then change the above definition of `nthBad` to return `nothing`
when the list is too short and `just a` when the list has enough
members and `a` appears at position `n`. We call this new function
`nthError` to indicate that it may result in an error.

```
nthError : NatList → ℕ → NatMaybe
nthError [] _ = nothing
nthError (x ∷ _) 0 = just x
nthError (_ ∷ xs) (suc n) = nthError xs n

_ : nthError (4 ∷ 5 ∷ 6 ∷ 7 ∷ []) 0 ≡ just 4
_ = refl

_ : nthError (4 ∷ 5 ∷ 6 ∷ 7 ∷ []) 3 ≡ just 7
_ = refl

_ : nthError (4 ∷ 5 ∷ 6 ∷ 7 ∷ []) 9 ≡ nothing
_ = refl
```

We could also write this function with an `if_then_else_` expression
and equality testing:

```
nthError' : NatList → ℕ → NatMaybe
nthError' [] _ = nothing
nthError' (x ∷ xs) n = if (n ≡ᵇ 0) then (just x) else nthError' xs (n ∸ 1)

_ : nthError' (4 ∷ 5 ∷ 6 ∷ 7 ∷ []) 0 ≡ just 4
_ = refl

_ : nthError' (4 ∷ 5 ∷ 6 ∷ 7 ∷ []) 3 ≡ just 7
_ = refl

_ : nthError' (4 ∷ 5 ∷ 6 ∷ 7 ∷ []) 9 ≡ nothing
_ = refl
```

The function below pulls the `ℕ` out of a `NatMaybe`, returning a
supplied default in the `nothing` case.

```
optionElim : ℕ → NatMaybe → ℕ
optionElim d nothing = d
optionElim d (just n) = n
```

#### Exercise `hderror` (practice) {#hderror}

    hdError : NatList → NatMaybe
    hdError [] = nothing
    hderror (x ∷ _) = just x

    _ : hdError [] ≡ nothing
    _ = refl
    
    _ : hdError (1 ∷ []) ≡ just 1
    _ = refl
    
    _ : hdError (5 ∷ 6 ∷ []) ≡ just 5
    _ = refl
    
## Partial Maps {#partialMaps}

As a final illustration of how data structures can be defined in Agda
here is a simple *partial map* data type, analogous to the map or
dictionary data structures found in most programming languages.

First, we define a new inductive datatype `id` to serve as the "keys"
of our partial maps.

```
data Id : Set where
  id : ℕ → Id
```

Internally, an `id` is just a number.  Introducing a separate type by
wrapping each ℕ with the tag `id` makes definitions more readable and
gives us more flexibility to change the type behind `Id`.

We'll also need an equality test for `Id` values.

``` 
_≡idᵇ_ : Id → Id → Bool
(id n) ≡idᵇ (id m) = n ≡ᵇ m
```

Now we can define the type of partial maps:

```
data PartialMap : Set where
  empty : PartialMap
  entry : Id → ℕ → PartialMap → PartialMap
```

This declaration can be read: "There are two ways to construct a
`PartialMap`: either using the constructor `empty` to represent an
empty partial map, or applying the constructor `entry` to a key, a
value, and an existing `PartialMap` to construct a `PartialMap` with
an additional key-to-value mapping."

The `update` function overrides the entry for a given key in a partial
map by shadowing it with a new one (or simply adds a new entry if the
given key is not already present).

```
update : PartialMap → Id → ℕ → PartialMap
update pm key value = entry key value pm
```

Last, the `find` function searches a `PartialMap` for a given key.  It
returns `nothing` if the key was not found and `just val` if the key
was associated with `val`.  If the same key is mapped to multiple
values, `find` will return the first one it encounters.

```
find : Id → PartialMap → NatMaybe
find _ empty = nothing
find key (entry k v pm) with key ≡idᵇ k
...                        | true = just v
...                        | false = find key pm
```

This function uses a new control structure introduced by `with`.
After `with` is an expression, and the subsequent `...  |` lines
should give patterns which cover every case of the values which may be
the result of the expression.  In this example, there are only two
possible values `true` and `false`, so we have two different cases.

## Unicode

This section uses the following Unicode symbols:

    →  U+2192  RIGHTWARDS ARROW (\to, \r, \->)
    ∷  U+2237  PROPORTION  (\::)

---

*This page is derived from Pierce et al., with some short exceprts
from Wadler et al., and by Maraist.  Exercise sort2 is derived from
Keller and Chakravarty.  For more information see the [sources and
authorship]({{ site.baseurl }}/Sources/) page.*
