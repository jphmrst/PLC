---
title     : "Functional: Higher-order functions"
layout    : page
prev      : /Poly/
permalink : /Functional/
next      : /Maps/
---

```
module plc.fp.Functional where
open import Data.Bool
open import Data.Nat
open import plc.fp.Poly

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
```

Like most modern programming languages — especially other "functional"
languages, including OCaml, Haskell, Racket, Scala, Clojure, etc. —
Agda treats functions as first-class citizens, allowing them to be
passed as arguments to other functions, returned as results, stored in
data structures, etc.

## Higher-order functions

Functions that manipulate other functions are often called
_higher-order_ functions.  Here's a simple one:

```
doIt3Times : ∀ {X : Set} → (X → X) → X → X
doIt3Times f n = f (f (f n))
```

The argument `f` here is itself a function (from `X` to `X`); the body
of `doit3times` applies `f` three times to some value `n`.

```
minusTwo : ℕ → ℕ
minusTwo x = x ∸ 2

_ : doIt3Times minusTwo 9 ≡ 3
_ = refl

_ : doIt3Times not true ≡ false
_ = refl

```

#### Exercise `typesFunctional` (practice) {typesFunctional}

Write Agda definitions which have the following types:

 - `ℕ → (ℕ → ℕ) → ℕ`
 - `(ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ)`

   Hint: which of the three pairs of parentheses are unnecessary?

#### Exercise `isPalendromePoly` (practice) {#isPalendromePoly}

Generalizing
[the `isPalendrome` function]({{ site.baseurl }}/NatData/#isPalendrome)
requires an extra parameter: in our monomorphic version we were
comparing only natural numbers, but to make the function polymorhic we
receive an additional parameter which tells us how to check the list
elements for equality.

    isPalendrome : ∀ {X : Set} → (X → X → Bool) → List X → Bool
    -- Your definition goes here

Adapt the tests of monomorphic `isPalendrome` to the new functions,
and extend them for lists of other types, finding appropriate
comparison functions in the standard libraries.

#### Exercise `noNeighborDupsPoly` (practice) {#noNeighborDupsPoly}

Generalize
[the `noNeighborDups` function]({{ site.baseurl }}/NatData/#noNeighborDups)
by adding an extra parameter in the same way as for `isPalendrome`.

    noNeighborDups : ∀ {X : Set} → (X → X → Bool) → List X → List X
    -- Your definition goes here

Adapt the tests of monomorphic `noNeighborDups` to the new functions,
and extend them for lists of other types, finding appropriate
comparison functions in the standard libraries.

### Filter

Here is a more useful higher-order function, taking a list of `X`s and
a _predicate_ on `X` (a function from `X` to `bool`) and "filtering"
the list, returning a new list containing just those elements for
which the predicate returns `true`.

```
filter : ∀ {X : Set} → (X → Bool) → List X → List X
filter _ [] = []
filter f (x ∷ xs) with f x
...                   | true = x ∷ filter f xs
...                   | false = filter f xs
```

For example, if we apply `filter` to the predicate `even` and a list
of numbers, it returns a list containing just the even members of that
list.

```
even : ℕ → Bool
even 0 = true
even 1 = false
even (suc (suc n)) = even n

_ : filter even (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ (2 ∷ 4 ∷ [])
_ = refl
```

We use `filter` on lists of arbitrarily complex element types, such as
selecting all of the elements of a list of lists whose length is 1.

```
lengthIs1 : ∀ {X : Set} → List X → Bool
lengthIs1 (_ ∷ []) = true
lengthIs1 _ = false

_ : filter lengthIs1 ((1 ∷ 2 ∷ []) ∷ (3 ∷ []) ∷ (4 ∷ [])
                       ∷ (5 ∷ 6 ∷ 7 ∷ []) ∷ [] ∷ (8 ∷ []) ∷ [])
      ≡ ((3 ∷ []) ∷ (4 ∷ []) ∷ (8 ∷ []) ∷ [])
_ = refl
```

We can use `filter` to give a concise version of
[the `countOddMembers` function]({{ site.baseurl }}/NatData/#countOddMembers).

```
length : ∀ {X : Set} → List X → ℕ
length [] = 0
length (_ ∷ xs) = suc (length xs)

odd : ℕ → Bool
odd 0 = false
odd 1 = true
odd (suc (suc n)) = odd n

countOddMembers : List ℕ -> ℕ
countOddMembers l = length (filter odd l)

_ : countOddMembers (1 ∷ 0 ∷ 3 ∷ 1 ∷ 4 ∷ 5 ∷ []) ≡ 4
_ = refl

_ : countOddMembers (0 ∷ 2 ∷ 4 ∷ []) ≡ 0
_ = refl

_ : countOddMembers [] ≡ 0
_ = refl
```

## Anonymous functions

It is arguably a little sad, in the example just above, to be forced
to define the function `lengthIs1` and give it a name just to be able
to pass it as an argument to `filter`.  We will probably never use a
function like `lengthIs1` again.  Moreover, this is not an isolated
example: when using higher-order functions, we often want to pass as
arguments "one-off" functions that we will never use again.  Having to
give each of these functions a name would be tedious.

Fortunately, there is a better way.  We can construct a function "on
the fly" without declaring it at the top level or giving it a name.
These functions are called *anonymous* functions, and we use a *lambda
abstraction* to write them down.

```
_ : doIt3Times (λ { n → n * n }) 2 ≡ 256
_ = refl
```

The expression `λ { n → n * n }` can be read as "the function that,
given a number `n`, yields `n * n`.

Here is the `filter` example, rewritten to use an anonymous function.

```
_ : filter (λ l → (length l) ≡ᵇ 1)
           ((1 ∷ 2 ∷ []) ∷ (3 ∷ []) ∷ (4 ∷ [])
              ∷ (5 ∷ 6 ∷ 7 ∷ []) ∷ [] ∷ (8 ∷ []) ∷ [])
      ≡ ((3 ∷ []) ∷ (4 ∷ []) ∷ (8 ∷ []) ∷ [])
_ = refl
```

We can give multiple before the arrow as a shorthand for multiple
nested λs.  For example, instead of

    λ { x → λ { y → (2 * x) + y }}

we could write

    λ { x y → (2 * x) + y }

The two both have type `ℕ → ℕ → ℕ`, and return the same result for any
two argments.

We can also write multiple patterns inside a lambda expression, just
as we can with multiple function clauses.  The general form of a
lambda expressions is

    λ{ P₁ → N₁; ⋯ ; Pₙ → Nₙ }

This expression is equivalent to a function `f` defined by the equations

    f P₁ = N₁
    ⋯
    f Pₙ = Nₙ

where the `Pₙ` are patterns (left-hand sides of an equation) and the
`Nₙ` are expressions (right-hand side of an equation).

In the case that there is one equation and the pattern is a variable,
we may also use the syntax

    λ x → N

or

    λ (x : A) → N

both of which are equivalent to `λ{x → N}`. The latter allows one to
specify the domain of the function.

Often using an anonymous lambda expression is more convenient than
using a named function: it avoids a lengthy type declaration; and the
definition appears exactly where the function is used, so there is no
need for the writer to remember to declare it in advance, or for the
reader to search for the definition in the code.


#### Exercise `filterEvenGt7` (starting) {#filterEvenGt7}

Use `filter` to write a function `filterEvenGt7` that takes a list
of natural numbers as input and returns a list of just those that are
even and greater than 7.

    filterEvenGt7a : List ℕ → List ℕ
    -- FILL IN: filterEvenGt7a l = filter ? l

    _ : filterEvenGt7a (1 ∷ 2 ∷ 6 ∷ 9 ∷ 10 ∷ 3 ∷ 12 ∷ 8 ∷ [])
          ≡ (10 ∷ 12 ∷ 8 ∷ [])
    _ = refl

    _ : filterEvenGt7a (5 ∷ 2 ∷ 6 ∷ 19 ∷ 129 ∷ []) ≡ []
    _ = refl

#### Exercise `filterPartition` (practice) {#filterPartition}

Use `filter` to write a function `partition`,

    partition : ∀ (X : Set) → (X → Bool) → List X → Prod (List X) (List X)

Given a set `X`, a predicate of type `X → Bool` and a `List` of values
of type `X`, `partition` should return a pair of lists.  The first
member of the pair is the sublist of the original list containing the
elements that satisfy the test, and the second is the sublist
containing those that fail the test.  The order of elements in the two
sublists should be the same as their order in the original list.

    _ : partition oddb (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
          ≡ pair (1 ∷ 3 ∷ 5 ∷ []) (2 ∷ 4 ∷ [])
    _ = refl
    
    _ : partition (λ { x → false }) (5 ∷ 9 ∷ 0 ∷ [])
          ≡ ([], (5 ∷ 9 ∷ 0 ∷ [])).
    _ = refl


## Function composition

A common operation on functions is _composition_:

```
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)
```

So `g ∘ f` is the function that first applies `f` and
then applies `g`.  An equivalent definition, exploiting lambda
expressions, is as follows:

```
_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f  =  λ x → g (f x)
```


## Map

Another useful higher-order function is called `map`.

```
map : ∀ {X Y : Set} → (X → Y) → List X → List Y
map _ [] = []
map f (x ∷ xs) = f x ∷ map f xs
```

It takes a function `f` and a list `l = (n1 ∷ n2 ∷ n3 ∷ ...)` and
returns the list `(f n1 ∷ f n2 ∷ f n3 ∷ ...)`, where `f` has been
applied to each element of `l` in turn.  For example:

```
_ : map (λ { x → 3 + x}) (2 ∷ 0 ∷ 2 ∷ []) ≡ (5 ∷ 3 ∷ 5 ∷ [])
_ = refl
```

The element types of the input and output lists need not be the same,
since `map` takes _two_ type arguments `X` and `Y`.  If some function
argument `f1` maps numbers to booleans, then `map` with first argument
`f1` would require its second argument to be a list of numbers, and
would return a list of boolean values:

```
_ : map odd (2 ∷ 1 ∷ 2 ∷ 5 ∷ []) ≡ (false ∷ true ∷ false ∷ true ∷ [])
_ = refl
```

It can even be applied to a list of numbers and a function from
numbers to _lists_ of booleans to yield a _list of lists_ of booleans:

```
_ : map (λ { n → (even n ∷ odd n ∷ []) }) (2 ∷ 1 ∷ 2 ∷ 5 ∷ [])
      ≡ ( (true ∷ false ∷ []) ∷ (false ∷ true ∷ [])
           ∷ (true ∷ false ∷ []) ∷ (false ∷ true ∷ []) ∷ [])
_ = refl
```

#### Exercise `flatMap` (practice) {#flatMap}

The function `map` maps a `List X` to a `List Y` using a function of
type `X → Y`.  Write a similar function `flatMap`, which maps a
`List X` to a `List Y` using a function `f` of type `X → List Y`.
Your definition should work by "flattening" the results of `f`,
concatenating the several list results into a single list.

    flatMap : ∀ {X Y : Set} → (X → List Y) → List X → List Y
    -- Your clauses go here

    _ : flatMap (λ { n → (n ∷ n ∷ n ∷ []) }) (1 ∷ 5 ∷ 4 ∷ [])
          ≡ (1 ∷ 1 ∷ 1 ∷ 5 ∷ 5 ∷ 5 ∷ 4 ∷ 4 ∷ 4 ∷ [])
    _ = refl

### `map` and `Maybe`

Lists are not the only inductive type for which `map` makes sense.
Here is a `map` for the `Maybe` type:

```
optionMap : ∀ {X Y : Set} → (X → Y) → Maybe X → Maybe Y
optionMap _ nothing = nothing
optionMap f (just x) = just (f x)
```

#### Exercise `explicitFilterMap` (practice) {#explicitFilterMap}

The definitions and uses of `filter` and `map` use implicit arguments
in many places.  Replace the curly braces around the implicit
arguments with parentheses, fill in explicit type parameters where
necessary, and use Agda to check that example calls to the revised
functions still work.  (This exercise is easiest to do on a _copy_ of
this file that you can throw away afterwards.)

## Fold

An even more powerful higher-order function is called `foldr`.  This
function is the inspiration for the `reduce` operation that lies at
the heart of Google's map/reduce distributed programming framework.

```
foldr : ∀ {X Y : Set} → (X → Y → Y) → Y → List X → Y
foldr _ z [] = z
foldr f z (x ∷ xs) = f x (foldr f z xs)
```

Intuitively, the behavior of the `foldr` operation is to insert a
given binary operator `f` between every pair of elements in a given
list.  For example, `fold _+_ (1 ∷ 2 ∷ 3 ∷4 ∷ [])` intuitively
means `1+2+3+4`.  To make this precise, we also need a "starting
element" that serves as the second input to `f` in the base case.  So,
for example,

```
_ : foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 1 + (2 + (3 + (4 + 0)))
_ = refl

_ : foldr _*_ 1 (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 24
_ = refl

_ : foldr _∧_ true (true ∷ true ∷ false ∷ true ∷ []) ≡ false
_ = refl
```

{::comment}
_ : foldr _++_ [] ((1 ∷ []) ∷ [] ∷ (2 ∷ 3 ∷ []) ∷ (4 ∷ []) ∷ [])
      ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
_ = refl
{:/comment}

The first of the examples above illustrates what the `r` in `foldr`
represents: *right*, as in right-associative.  When we write out the
elements of a list, we already know the `∷` operator is
right-associative.  That is, we already know that

```
_ : (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ (1 ∷ (2 ∷ (3 ∷ (4 ∷ []))))
_ = refl
```

and not

    (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ ((((1 ∷ 2) ∷ 3) ∷ 4) ∷ [])

(which is not even well-typed!).  The `r` in `foldr` means that we
preserve this associativity when we replace `∷` with the operator
argument.  There is also a function `foldl` which applies the operator
*left-associatively* to the list elements:

```
foldl : ∀ {X Y : Set} → (X → Y → X) → X → List Y → X
foldl f z []       = z
foldl f z (x ∷ xs) = foldl f (f z x) xs
```

Note that the role of `z` is not exactly the same in `foldr` as
in`foldl`.  Our intuition for `foldr` was to replace each `∷` with
`f`, and the final `[]` with `z`.  But we use the `z` argument in
`foldl` at the very *beginning* of the expression, with the first
argument:

    foldl _OP_ z (x1 ∷ x2 ∷ x3 ∷ ... ∷ xN)
      ≡ (((((z _OP_ x1) _OP_ x2) _OP_ x3) _OP_ ...) _OP_ xN)

For adding numbers with the default element 0, the choice of `foldl`
or `foldr` makes no difference because addition is associative:

```
_ : foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ foldl _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
_ = refl
```

However subtraction is not associative, and the choice of `foldl` or
`foldr` does make a difference.

```
_ : foldr _∸_ 0 (8 ∷ 4 ∷ 2 ∷ 1 ∷ []) ≡ (8 ∸ (4 ∸ (2 ∸ (1 ∸ 0))))
_ = refl

_ : foldl _∸_ 8 (4 ∷ 2 ∷ 1 ∷ 0 ∷ []) ≡ ((((8 ∸ 4) ∸ 2) ∸ 1) ∸ 0)
_ = begin
       foldl _∸_ 8 (4 ∷ 2 ∷ 1 ∷ 0 ∷ [])
    ≡⟨⟩ foldl _∸_ (8 ∸ 4) (2 ∷ 1 ∷ 0 ∷ [])
    ≡⟨⟩ foldl _∸_ ((8 ∸ 4) ∸ 2) (1 ∷ 0 ∷ [])
    ≡⟨⟩ foldl _∸_ (((8 ∸ 4) ∸ 2) ∸ 1) (0 ∷ [])
    ≡⟨⟩ foldl _∸_ ((((8 ∸ 4) ∸ 2) ∸ 1) ∸ 0) []
    ≡⟨⟩ (((8 ∸ 4) ∸ 2) ∸ 1) ∸ 0
    ∎
```

#### Exercise `foldTypesDifferent` (starting) {#foldTypesDifferent}

Observe that the type of the fold functions is parameterized by _two_
type variables, `X` and `Y`, and the parameter `f` is a binary
operator that takes an `X` and a `Y` and returns a `Y`.  Can you think
of a situation where it would be useful for `X` and `Y` to be
different?

## Functions that construct functions

Most of the higher-order functions we have talked about so far take
functions as arguments.  Let's look at some examples that involve
_returning_ functions as the results of other functions.  To begin,
here is a function that takes a value `x` (drawn from some type `x`)
and returns a function from `ℕ` to `x` that yields `x` whenever it is
called, ignoring its `ℕ` argument.

```
constfun : ∀ {X : Set} → X → (ℕ → X)
constfun x = λ { k → x }

ftrue : ℕ → Bool
ftrue = constfun true

_ : ftrue 0 ≡ true
_ = refl

```

In fact, the multiple-argument functions we have already seen are also
examples of passing functions as data.  To see why, recall the type of
`_+_`.

    _+_ : ℕ → ℕ → ℕ

Each `→` in this expression is actually a binary operator on types.
This operator is _right-associative_, so the type of `_+_` is really a
shorthand for `ℕ → (ℕ → ℕ)` — that is, it can be read as saying that
"`_+_` is a one-argument function that takes a `ℕ` and returns a
one-argument function that takes another `ℕ` and returns a `ℕ`."  We
represent a function of two arguments in terms of a function of the
first argument that returns a function of the second argument.  This
trick goes by the name _currying_.  Agda, like other functional
languages such as Haskell and ML, is designed to make currying easy to
use.  Just as function arrows associate to the right, application
associates to the left:

 - `ℕ → ℕ → ℕ` stands for `ℕ → (ℕ → ℕ)`, and
 - `_+_ 2 3` stands for `(_+_ 2) 3`.

In our earlier uses of `_+_` we always applied `_+_` to both of its
arguments at once, but if we like we can supply just the first.  This
use of a curried function with some of its arguments is called
_partial application_.  The term `_+_ 2` by itself stands for the
function that adds two to its argument, hence applying it to three
yields five.

```
plus3 : ℕ → ℕ
plus3 = _+_ 3

_ : plus3 4 ≡ 7
_ = refl

_ : doIt3Times plus3 0 ≡ 9
_ = refl

_ : doIt3Times plus3 0 ≡ 9
_ = refl
```

Currying is named for Haskell Curry, after whom the programming
language Haskell is also named.  Curry's work dates to the 1930's.
When I first learned about currying, I was told it was misattributed,
since the same idea was previously proposed by Moses Schönfinkel in
the 1920's.  I was told a joke: "It should be called schönfinkeling,
but currying is tastier". Only later did I learn that the explanation
of the misattribution was itself a misattribution.  The idea actually
appears in the _Begriffsschrift_ of Gottlob Frege, published in 1879.

## Additional exercises

#### Exercise `functionToType` (practice) {#functionToType}

What is the most general types you can give to these functions?  Try
to work them out on your own before checking your answers.

 - double x = x * 2

 - twice f x = f (f x)

 - seq3 f g h x = h (g (f x))

#### Exercise `foldLength` (practice) {#foldLength}

Many common functions on lists can be implemented in terms of the fold
functions.  Give an alternative definition of `length` with a single
clause, and which makes a call to one of the fold functions.

    foldLength : ∀ {X : Set} → List X → ℕ
    foldLength xs = -- Your expression here

    _ : foldLength (4 ∷ 7 ∷ 0 ∷ []) ≡ 3
    _ = refl

#### Exercise `foldMap` (practice) {#foldMap}

We can also define `map` in terms of `foldr`.

    foldMap : ∀ {X Y : Set} → (X → Y) → List X → List Y
    foldMap f xs = -- Your expression here

    _ : foldMap (λ { x → 3 + x}) (2 ∷ 0 ∷ 2 ∷ []) ≡ (5 ∷ 3 ∷ 5 ∷ [])
    _ = refl

    _ : foldMap odd (2 ∷ 1 ∷ 2 ∷ 5 ∷ [])
          ≡ (false ∷ true ∷ false ∷ true ∷ [])
    _ = refl

#### Extended exercise: Church numerals

The following exercises explore an alternative way of defining natural
numbers, using the so-called _Church numerals_, named after
mathematician Alonzo Church.  We can represent a natural number `n` as
a function that takes a function `f` as a parameter and returns `f`
iterated `n` times.

```
module Church where
  cnat : Set1
  cnat = ∀ (X : Set) → (X → X) → (X → X)
```

Let's see how to write some numbers with this notation.  Iterating a
function once should be the same as just applying it.  Thus:

```
  one : cnat
  one = λ { X f x → f x }
```

Similarly, `two` should apply `f` twice to its argument:

```
  two : cnat
  two = λ { X f x → f (f x) }
```

Defining `zero` is somewhat trickier: how can we "apply a function
zero times"?  The answer is actually simple: just return the argument
untouched.

```
  zeroC : cnat
  zeroC = λ { X f x → x }
```

More generally, a number `n` can be written as

    fun X f x => f (f ... (f x) ...)

with `n` occurrences of `f`.  Notice in particular how the
`doIt3Times` function we've defined previously is actually just the
Church representation of `3`.

```
  three : cnat
  three = λ { X f n → f (f (f n)) }
```

Complete the definitions of the following functions. 

##### Exercise `churchSucc` (practice) {#churchSucc}

Successor of a natural number: given a Church numeral `n`, the
successor [succ n] is a function that iterates its argument once more
than `n`.

    succ : cnat → cnat
    -- succ n = λ { X f x →  -- Complete this lambda expression
  
    _ : succ zeroC ≡ one
    _ = refl
  
    _ : succ one ≡ two
    _ = refl
  
    _ : succ two ≡ three
    _ = refl

##### Exercise `churchPlus` (practice) {#churchPlus}

Define the addition of two Church numbers:

    plus : cnat → cnat → cnat
    plus n m = λ {X f x →  -- Complete this lambda expression

    _ : plus zero one ≡ one
    _ = refl

    _ : plus one zero ≡ one
    _ = refl

    _ : plus two one ≡ three
    _ = refl

    _ : plus (plus two two) three ≡ plus one (plus three three)
    _ = refl

##### Exercise `churchMult` (practice) {#churchMult}

Continue with a definition of multiplication:

    mult : cnat → cnat → cnat
    mult n m = λ {X f x →  -- Complete this lambda expression

    _ : mult zero one ≡ zero
    _ = refl

    _ : mult zero three ≡ zero
    _ = refl

    _ : mult one one ≡ one
    _ = refl

    _ : mult two one ≡ two
    _ = refl

    _ : mult two two ≡ plus one three
    _ = refl

##### Exercise `churchExp` (practice) {#churchExp}

    exp : cnat → cnat → cnat
    exp n m = λ {X f x →  -- Complete this lambda expression

    _ : exp zero one ≡ zero
    _ = refl

    _ : exp zero three ≡ zero
    _ = refl

    _ : exp one zero ≡ one
    _ = refl

    _ : exp three zero ≡ one
    _ = refl

    _ : exp one one ≡ one
    _ = refl

    _ : exp two two ≡ plus one three
    _ = refl

## Unicode

This section uses the following Unicode symbols:

    λ   U+03BB  GREEK SMALL LETTER LAMDA  (\Gl, \lambda)
    →  U+2192  RIGHTWARDS ARROW (\to, \r, \->)
    ∀  U+2200  FOR ALL  (\all)
    ∘  U+2218  RING OPERATOR (\o, \circ, \comp)
    ∷  U+2237  PROPORTION  (\::)

---

*This page is derived from Pierce et al., except for the section on
 currying which includes text from Wadler et al.  For more information
 see the [sources and authorship]({{ site.baseurl }}/Sources/) page.*
 
