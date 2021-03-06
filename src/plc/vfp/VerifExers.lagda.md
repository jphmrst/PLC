---
title     : "VerifExers: Further applications and exercises"
layout    : page
prev      : /Logic/
permalink : /VerifExers/
next      : /ImpExprs/
---

```
module plc.vfp.VerifExers where
```

This section contains additional applications and exercises on the
verification techniques we have seen in this chapter.  We revisit the
vector, partial map, and total map types we defined earlier.

Some of the exercises in this section are written a little differently
than the exercises in earlier sections.  We use `postulate` keyword.
It allows us to use these lemmas in later sections, even if you are
not able to complete all of the exercises, or if you complete them in
a different file.  When you work the exercises, be sure to remove the
`postulate` keyword when you add your proof.

## Imports

```
open import Data.Bool
open import Data.Nat
```

## Revisiting size-indexed vectors

```
module MoreDepend where
  open import plc.fp.Depend
  open import Data.Product using (∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
```

In the [previous section]({{ site.baseurl }}/Logic/) we discussed the
existential quantifier as something we would use to wrap a logical
formula.  But we can also use it to describe some property of an
ordinary data structure.

In [Section Depend]({{ site.baseurl }}/Depend/) we built a library of
vectors which were like ordinary polymorphic linked lists, but where
the type of each vector contained its length.  However, there was one
conspicuous absence from the functions in the exercises for that
section: a vector version of the `filter` function.  In general, we
cannot predict how many elements in a list will satisfy an arbitrary
function `f`.  So it is tricky to declare what the size will be of the
result of a call to `filter`:

      filter : ∀ {A : Set} {n : ℕ} → (A → Bool) → Vec A n → Vec A ?

Although we cannot declare the size with precision for all cases, we
can be sure that such a size will exist.  So it is natural to use the
existential quantifier to describe it.

```
  filter : ∀ {A : Set} {n : ℕ} → (A → Bool) → (Vec A n) → ∃[ n′ ] (Vec A n′)
```

What does it mean to have a value whose type is `∃[ n′ ] (Vec A n′)`?
Just as with evidence for a formula, the value is a pair: a witness,
plus a value of the type for the particular witness.  Here, the
witness is a value for `n′`, the length of the vector.  So if the
argument is the empty vector, then the result witness will be zero —
we will not find any elements to satisfy `f` in the empty vector.  The
value result of type `Vec A zero` will be the empty vector.

```
  filter f [] = ⟨ 0 , [] ⟩
```

When the argument is not empty, we need to consider two additional
values.

 1. As with the list version of `filter`, we must check whether the
    first element of the vector satisfies `f`.

 2. We must also make a recursive call to `filter` with the rest of
    the vector.  Of course we also made such a recursive call in the
    list version of `filter`!  But there is a key difference: in the
    list version of `filter`, the result is a list.  Here, we get not
    only a vector, but _also the witness_ because the result has the
    type of an existential quantification.

We evaluate both of these expressions to determine which clause of
`filter` should apply.

```
  filter f (x ∷ xs) with (f x) | filter f xs
```

If the filtering function returns `true` for the first element of the
argument vector, then we must include that element is the resulting
vector.  But we must also give the resulting vector a type where the
length is one greater that the vector of the recursive call.  So if
the witness value for the recursive call to `filter` is some number
`m`, then the witness for the vector including `x` will be the
successor of `m`:

```
  ...                  | true  | ⟨ m , xs' ⟩ = ⟨ suc m , x ∷ xs' ⟩
```

If the filtering function rejects the first element of the vector,
then the witness and vector result for this list would be the same as
the witness and vector result for the recursive call, because we do
not include that element in the result.

```
  ...                  | false | v'          = v'
```


```
  -- End of module MoreDepend
```

## Properties of total maps

```
module MapProps where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong)
  open Eq.≡-Reasoning
  open import Data.String
  open import Data.Maybe
  open import plc.fp.Maps
  import plc.vfp.Logic as LL
  open LL
  open LL.String
  import plc.vfp.DataProp as DP
  open DP.Inspect
```

Recall that we used _functions_, rather than lists of key-value pairs,
to build maps.

    TotalMap : Set → Set
    TotalMap A = String → A

We will see some payoff from that choice in this section, since this
design simplifies some of the proofs we will construct.
To discuss the idea that two functions are equal, we will need the
notion of extensionality for most of these exercises.

#### Exercise `tApplyEmpty` (recommended)

Show that the empty map returns its default element for all keys:

```
  postulate tApplyEmpty : ∀ {A : Set} (x : String) (v : A) → (↪ v) x ≡ v
  -- Remove the keyword postulate, and fill in your proof here
```
    
#### Exercise `tUpdateEq` (recommended)

Show that if we update a map `m` at a key `x` with a new value `v` and
then look up `x` in the map resulting from the `update`, we get back
`v`.

```
  postulate  tUpdateEq : ∀ {A : Set} (m : TotalMap A) x (v : A)
                           → (x ↦ v , m) x ≡ v
  -- Remove the keyword postulate, and fill in your proof here
```
    
#### Exercise `tUpdateNeq` (recommended)

On the other hand, show that if we update a map `m` at a key `x1` and
then look up a _different_ key `x2` in the resulting map, we get the
same result that `m` would have given.

```
  postulate tUpdateNeq : ∀ {A : Set} (m : TotalMap A) x1 x2 v
                           → (x1 ≢ x2)
                             → (x1 ↦ v , m) x2 ≡ m x2
  -- Remove the keyword postulate, and fill in your proof here
```

#### Exercise `tUpdateShadow` (recommended)

Show that if we update a map `m` at a key `x` with a value `v1`, and
then update again with the same key `x` and another value `v2`, the
resulting map behaves the same (gives the same result when applied to
any key) as the simpler map obtained by performing just the *second*
`update` on `m`.

```
  postulate tUpdateShadow : ∀ {A : Set} (m : TotalMap A) x v1 v2
                              → (x ↦ v2 , x ↦ v1 , m) ≡ (x ↦ v2 , m)
  -- Remove the keyword postulate, and fill in your proof here
```

You will need to use both [functional extensionality]({{ site.baseurl
}}/Logic/#extensionality) and the [inspection idiom]({{ site.baseurl
}}/DataProp/#inspect) for Exercise `tUpdateShadow`.  The top-level of
your solution should look something like

    tUpdateShadow m x v1 v2 = extensionality point
      where point : (y : String) → (x ↦ v2 , x ↦ v1 , m) y ≡ (x ↦ v2 , m) y

The conclusion of the lemma `(x ↦ v2 , x ↦ v1 , m) ≡ (x ↦ v2 , m)`
relates two _functions_ — remember again that `TotalMap` is just an
abbreviation for a particular function type.  Starting your solution
like the two lines above introduces a helping result `point` which
demonstrates the desired relationship at a particular name to which
the two maps can be applied.  Then since there are no restrictions on
what names may be passed to `point`, extensionality allows that helper
result to be lifted to the whole of the functions themselves.

Inside of point, your reasoning will vary according to whether `x` and
`y` are the same string, or more specifically, whether `x == y` is
`true` or `false`.  The most natural way to divide up these cases is
by using a `with` clause.  A first approach would extend the two lines
above with something like this:

    point y with x == y

and then two cases, one for each of the possible outcomes.  However,
starting in this way you would quickly see that simply knowing the
value of `x == y` is not enough: you will also need to use _evidence_
that `(x == y) ≡ true` or `(x == y) ≡ false` (you are encouraged to
try the proof with this first `with` clause, to see how the evidence
is insufficient).  Filling this gap is what the inspection idiom
provides.  We can refine the `with` clause as

    point y with inspect (x == y)

to have both the value result, and the evidence of the relationship
between the value result and `x == y`.

You will need to set up a similar structure for some — but not all —
of the exercises below.  Take the time to think about what makes these
techniques necessary here, so that you can recognize those signs
later.

#### Exercise `tUpdateSame` (recommended)

Show that if we update a map to assign key `x` the same value as it
already has in `m`, then the result is equal to `m`:

```
  postulate tUpdateSame : ∀ {A : Set} (m : TotalMap A) x → (x ↦ m x , m) ≡ m
  -- Remove the keyword postulate, and fill in your proof here
```

#### Exercise `tUpdatePermute` (recommended)

Show that if we update a map `m` at two distinct keys, it doesn't
matter in which order we do the updates.

```
  postulate tUpdatePermute : ∀ {A : Set} (m : TotalMap A) v1 v2 x1 x2
                               → x1 ≢ x2
                                 → (x1 ↦ v1 , x2 ↦ v2 , m)
                                   ≡ (x2 ↦ v2 , x1 ↦ v1 , m)
  -- Remove the keyword postulate, and fill in your proof here
```

#### Exercise `tUpdateSinglePointUpdates` (recommended)

Show that if we update a map `m` at one point in two
possibly-different ways, then the resulting maps are the same if the
two update values are the same.

```
  postulate tSinglePointUpdates : ∀ {A : Set} (m : TotalMap A) x v1 v2
                                    → (v1 ≡ v2)
                                      → (x ↦ v1 , m) ≡ (x ↦ v2 , m)
  -- Remove the keyword postulate, and fill in your proof here
```

#### Exercise `tUpdateSinglePoint≡Updates` (recommended)

Show that if we update a map `m` at one point in two
possibly-different ways, then the resulting maps are the same if the
two update values are the same.

```
  postulate tSinglePoint≡Updates : ∀ {A : Set} (m1 m2 : TotalMap A) x v1 v2
                                     → (m1 ≡ m2) → (v1 ≡ v2)
                                       → (x ↦ v1 , m1) ≡ (x ↦ v2 , m2)
  -- Remove the keyword postulate, and fill in your proof here
```

## Properties of partial maps

We can straightforwardly lift all of the basic lemmas about total maps
to partial maps.

#### Exercise `applyEmpty` (recommended)

```
  postulate applyEmpty : ∀ {A : Set} (x : String) → ∅ {A} x ≡ nothing
  -- Remove the keyword postulate, and fill in your proof here
```

#### Exercise `updateEq` (recommended)

```
  postulate updateEq : ∀ {A : Set} (m : PartialMap A) x v
                         → (x ↦ₚ v , m) x ≡ just v
  -- Remove the keyword postulate, and fill in your proof here
```

#### Exercise `updateNeq` (recommended)

```
  postulate updateNeq : ∀ {A : Set} (m : PartialMap A) x1 x2 v
                          → x1 ≢ x2
                            → (x2 ↦ₚ v , m) x1 ≡ m x1
  -- Remove the keyword postulate, and fill in your proof here
```

#### Exercise `updateShadow` (recommended)

```
  postulate updateShadow : ∀ {A : Set} (m : PartialMap A) x v1 v2
                             → (x ↦ₚ v2 , x ↦ₚ v1 , m) ≡ (x ↦ₚ v2 , m)
  -- Remove the keyword postulate, and fill in your proof here
```

#### Exercise `updateSame` (recommended)

```
  postulate updateSame : ∀ {A : Set} (m : PartialMap A) x v
                           → m x ≡ just v
                             → (x ↦ₚ v , m) ≡ m
  -- Remove the keyword postulate, and fill in your proof here
```

#### Exercise `updatePermute` (recommended)

```
  postulate updatePermute : ∀ {A : Set} (m : PartialMap A) x1 x2 v1 v2
                              → x1 ≢ x2
                                → (x1 ↦ₚ v1 , x2 ↦ₚ v2 , m)
                                    ≡ (x2 ↦ₚ v2 , x1 ↦ₚ v1 , m)
  -- Remove the keyword postulate, and fill in your proof here
```

```
  -- End of module MapProps
```

---

*The vectors section is by Maraist, and the sections on total and
partial maps are derived from Pierce et al.  For more information see
the [sources and authorship]({{ site.baseurl }}/Sources/) page.*
