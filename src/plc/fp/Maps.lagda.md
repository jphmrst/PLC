---
title     : "Maps: Total and partial maps"
layout    : page
prev      : /Functional/
permalink : /Maps/
next      : /Depend/
---

```
module plc.fp.Maps where
open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.String

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
```

_Maps_ (or _dictionaries_) are ubiquitous data structures, both in
commercial programming projects, and in the studies we will make in
the coming chapters.  They make a nice larger case study of building
data structures out of higher-order functions, and we will be able to
extend this case study when we move later to *verified* functional
programming.

We'll define two flavors of maps: _total_ maps, which include a
"default" element to be returned when a key being looked up does not
exist, and _partial_ maps, which use `Maybe` types to indicate
success or failure.  The latter is defined in terms of the former,
using `nothing` as the default element. 

First, we need a type for the keys that we use to index into our maps.
When we looked at [monomorphic maps over natural numbers]({{
site.baseurl }}/NatData/#partial-maps) we introduced a fresh type `Id`
for this purpose.  Here (and for our uses of maps later in the course)
we will use the `String` type from Agda's standard library as the key
type, along with its boolean equality operator `==`.

## Total maps

Our maps in this chapter will be similar in behavior to the one we saw
earlier.  This time around, though, we're going to use higher-order
functions, rather than lists of key-value pairs, to build the maps.
The advantage of this representation is that it offers a more
_extensional_ view of maps, where two maps that respond to queries in
the same way will be represented as literally the same thing (the very
same function), rather than just "equivalent" data structures.  This
will simply some of the reasoning we will do about maps later on.

```
TotalMap : Set -> Set
TotalMap A = String → A
```

Intuitively, a total map over an element type `A` is just a function
that can be used to look up `String`s, yielding values of type `A`.
The function `↦↦` yields an empty total map, given a default element;
this map always returns the default element when applied to any
string.

```
↪ : ∀ {A : Set} → A → TotalMap A
↪ v = λ { x → v }
```

More interesting is the update function, which we will write as a
three-argument operator `_↦_,_`.  As before, `m ↦ x , v` is a new map
that takes `x` to `v`, and for every other key returns whatever `m`
returns.

```
_↦_,_ : ∀ {A : Set} → String → A → TotalMap A → TotalMap A
x ↦ v , m = λ { x' → if x == x' then v else m x' }
infixr 4 _↦_,_
```

This definition is a nice example of higher-order programming: taking
a function `m` and yielding a new function whose behavior is derived
from (but is not exactly the same as) `m`.

For example, we can build a map taking `String`s to `Bool`s, where
`"foo"` and `"bar"` are mapped to `true` and every other key is mapped
to `false`, like this:

```
fooBarExample : TotalMap Bool
fooBarExample = "foo" ↦ true , "bar" ↦ true , ↪ false

_ : fooBarExample "foo" ≡ true
_ = refl

_ : fooBarExample "bar" ≡ true
_ = refl

_ : fooBarExample "baz" ≡ false
_ = refl
```

This completes the definition of total maps.  Note that we don't need
to define a `find` operation because it is just function application!

## Partial maps

We define _partial maps_ on top of total maps.  A partial map with
elements of type `A` is simply a total map with elements of type
`Maybe A` and default element `nothing`.

```
PartialMap : Set → Set
PartialMap A = TotalMap (Maybe A)

∅ : ∀ { A : Set } → PartialMap A
∅ = ↪ nothing

_↦ₚ_,_ : ∀ {A : Set} → String → A → PartialMap A → PartialMap A
x ↦ₚ v , m = x ↦ just v , m
infixr 4 _↦ₚ_,_

```

We can also hide the last case when it is empty.

```
_↦ₚ_ : ∀ {A : Set} → String → A → PartialMap A
x ↦ₚ v = x ↦ just v , ∅
infixr 4 _↦ₚ_

churchTuring : PartialMap Bool
churchTuring = "Church" ↦ₚ true , "Turing" ↦ₚ false

_ : churchTuring "Church" ≡ just true
_ = refl

_ : churchTuring "Turing" ≡ just false
_ = refl

_ : churchTuring "Smith" ≡ nothing
_ = refl
```

## Unicode

This chapter uses the following unicode:

    ↦ (\mapsto)
    ↪ (\hookrightarrow)
    ∅ (\emptyset)
    ∷  U+2237  PROPORTION  (\::)

---

*This page is derived from Pierce et al.  For more information see the
[sources and authorship]({{ site.baseurl }}/Sources/) page.*
