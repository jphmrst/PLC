---
title     : "Depend: Dependent Types"
layout    : page
prev      : /Functional/
permalink : /Depend/
next      : /
---

```
module plc.fp.Depend where
open import Data.Bool
open import Data.Nat

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
```

## The relationship between types and expressions

Over your experience with programming, you have seen different ways in
which types and value expressions (or _terms_) can be related.

 - **Terms can depend on terms**.  When we write a function in Agda
   (or a method in Java, or a function in C, or a subroutine in
   assembler), we are describing a way in which one value can be
   derived from one or more other values.  With this mechanism, we
   have set up a way for the evaluation of one term to depend on the
   evaluation of other terms.

 - **Types can depend on types**.  When we define a polymorphic
   datatype in Agda (or a generic class in Java, or a template class
   in C++), we are describing a way in which one type can be derived
   from one or more other types.

 - **Terms can depend on types**.  When we define a polymorphic
   function in Agda (or a generic method in Java), we are describing a
   way in which a term can be derived from one or more types.

These arrangements are very common in programming languages.  However
there is a fourth, less commonly found, posibility.  In Agda,
**types** can depend on **terms**.  We will use this idea extensively
in the next chapter, but we begin with a simple example in this
section.

Recall our definition of a list of natural numbers:

    data NatList : Set where
      [] : NatList
      _∷_ : ℕ → NatList → NatList

Lists of any length all have the same type.  `[]`, `1 ∷ []` and
`1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []` all have type `NatList`.  
*Vectors* are a linked linear data structure where the length of
the vector *is* distinguished by the type.

```
module NatVector where
    infixr 5 _∷_
    
    data NatVec : ℕ → Set where
      []  : NatVec 0
      _∷_ : ∀ {n : ℕ} → (x : ℕ) → (xs : NatVec n) → NatVec (suc n)
```

Instead of quantifying over another type, as we did with polymorphic
`List`, here we are quantifying over a natural number.  `NatVec 2`
and `NatVec 5` are not the same type, since `2` and `5` are not the
same number.

Here are some instances of `NatVec`:

```
    nv1 : NatVec 0
    nv1 = []

    nv3 : NatVec 3
    nv3 = 10 ∷ 20 ∷ 30 ∷ []

    nv5 : NatVec 5
    nv5 = 50 ∷ 40 ∷ nv3
```

### Functions on `NatVec`

Let us revisit the functions we wrote on lists for `NatVec`.  To give
a type for functions on `NatVec`, we will often need to use the values
passed as parameters in the types of the results.  Recall the `repeat`
function on `NatList`s:

    repeat : ℕ → ℕ → NatList
    repeat n zero = []
    repeat n (suc count') = n ∷ repeat n count'

If we are building a `NatVec` instead of a `NatList`, the length of
the resulting list will be the same as the value of the second
argument.  So we need to include that value in the signature of our
`repeat` for `NatVec`:

    repeat : ℕ → ℕ → NatVec ?

How do we fill in that blank with length of the vector?  The function
signature must standalone, and define the function type without using
the clauses which might follow.  For this reason Agda allows us to
give names to the arguments in the signature, not just in the defining
clauses,

    repeat : ℕ → (len : ℕ) → NatVec ?

We can then use that name as the argument to `NatVec`.

```
    repeat : ℕ → (len : ℕ) → NatVec len
```

Then the rest of the function definition is just the same as for
`NatList`:

```
    repeat n zero = []
    repeat n (suc count') = n ∷ repeat n count'
```

We can use the quantified arguments when we write the clauses of the
function implementation.  As usual, if the argument in implicit, we
must wrap it in curly braces to access it.  This makes the `length`
function must easier to calculate:

```
    length : ∀ {len : ℕ} → NatVec len → ℕ
    length {len} _ = len
```

The length of the vector is present in the type, and we can return it
directly.

When we use natural numbers in a type, we have access to functions
over natural numbers as well.  Consider the append function `_++_`:
the length of its result should be the sum of the lengths of its
arguments.  We see this idea in the signature of `_++_` for `NatVec`,

```
    _++_ : ∀ {m n : ℕ} → NatVec m → NatVec n → NatVec (m + n)
    [] ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
```

#### Exercise `tryNatVec` (starting) {#tryNatVec}

Check the type of these `NatVec` expressions both on paper using
the rules defined for `NatVec`, and interactively in Agda.

    1 ∷ 2 ∷ 10 ∷ []
    1 ∷ 2 ∷ 10 ∷ 10 ∷ 20 ∷ 100 ∷ []

What happens if we assign a `NatVec` to a variable with the wrong
length?

    badVec : NatVec 3
    badVec = 5 ∷ 6 ∷ []

#### Exercise `tryNatVecFns` (starting) {#tryNatVecFns}

What type do these expressions have?  Again, check their types both on
paper using the rules defined for `NatVec`, and interactively in Agda.

    repeat 10 4
    [] ++ []
    (10 ∷ []) ++ []
    (1 ∷ 2 ∷ 10 ∷ []) ++ (1 ∷ 2 ∷ 10 ∷ 10 ∷ 20 ∷ 100 ∷ [])

#### Exercise `doubleAllVec` (practice) {#doubleAllVec}

Adapt the [`doubleAll`]({{ site.baseurl }}/NatData/#doubleAll)
function and tests from `NatList`s to `NatVec`s.

#### Exercise `alternateVecFails` (practice) {#alternateVecFails}

Why is it difficult to adapt the
[`alternate`]({{ site.baseurl }}/NatData/#alternate)
function from `NatList`s to `NatVec`s?

#### Exercise `stringVecs` (practice) {#stringVecs}

Develop a `StringVec` type like the `StringList` type from the
[NatData section]({{ site.baseurl }}/NatData/#stringLists)

```
-- End of module NatVector
```

### Abstracting over both terms and types

We have now written types which depend on other types, and we have
written types which depend on terms.  Both cases use a similar
mechanism: we use a universal quantifier `∀` to name a type or term
which we may then use in the rest of the type.  Of course in the same
way we can also create types which depend *both* on other types *and*
on terms.

So we can define a polymorphic vector which can hold any type, and be
of any length.

```
data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)
```

Note that in the first line of the definition we write
`Vec (A : Set) : ℕ → Set` rather than `Vec : ∀ (A : Set) → ℕ → Set`.
When we want to refer to one of the arguments of a data type
constructor in the various data constructor lines, we must write it
*before* the colon `:` which follows the type name.  The scope of `A`
in `∀ (A : Set) →` is limited to the rest of the type expression, but
the scope of `A` in `data Vec (A : Set)` is the entire `data`
declaration.

The constructors for the empty list and the cons cell follow the same
pattern as when we moved from monomorphic lists to polymorphic lists.
The type of the values contained in the vector is given with the same
name as in the first line.

The `repeat`, `length` and append functions do not depend on the types
of their elements, so we can adapt them

    repeat : ℕ → ℕ → NatList
    repeat n zero = []
    repeat n (suc count') = n ∷ repeat n count'

If we are building a `NatVec` instead of a `NatList`, the length of
the resulting list will be the same as the value of the second
argument.  So we need to include that value in the signature of our
`repeat` for `NatVec`:

    repeat : ℕ → ℕ → NatVec ?

How do we fill in that blank with length of the vector?  The function
signature must standalone, and define the function type without using
the clauses which might follow.  For this reason Agda allows us to
give names to the arguments in the signature, not just in the defining
clauses,

    repeat : ℕ → (len : ℕ) → NatVec ?

We can then use that name as the argument to `NatVec`.

```
    repeat : ℕ → (len : ℕ) → NatVec len
```

Then the rest of the function definition is just the same as for
`NatList`:

```
    repeat n zero = []
    repeat n (suc count') = n ∷ repeat n count'
```

We can use the quantified arguments when we write the clauses of the
function implementation.  As usual, if the argument in implicit, we
must wrap it in curly braces to access it.  This makes the `length`
function must easier to calculate:

```
    length : ∀ {len : ℕ} → NatVec len → ℕ
    length {len} _ = len
```

The length of the vector is present in the type, and we can return it
directly.

When we use natural numbers in a type, we have access to functions
over natural numbers as well.  Consider the append function `_++_`:
the length of its result should be the sum of the lengths of its
arguments.  We see this idea in the signature of `_++_` for `NatVec`,

```
    _++_ : ∀ {m n : ℕ} → NatVec m → NatVec n → NatVec (m + n)
    [] ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
```

TODO exercises --- all functions

TODO Longer exercise on names in maps?

## Unicode

This section uses the following unicode:

    ℕ  U+2115  DOUBLE-STRUCK CAPITAL N (\bN)
    →  U+2192  RIGHTWARDS ARROW (\to, \r, \->)
    ∀  U+2200  FOR ALL  (\all)
    ∷  U+2237  PROPORTION  (\::)
    ≡  U+2261  IDENTICAL TO (\==)

---

*This page is by Maraist.
For more information see the [sources and authorship]({{ site.baseurl
}}/Sources/) page.*
