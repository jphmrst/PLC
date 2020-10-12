---
title     : "MapProps: Properties of total and partial maps"
layout    : page
prev      : /DataProp/
permalink : /MapProps/
next      : /Relations/
---

```
module plc.vfp.MapProps where
```

This section is mostly exercises.  We revisit the partial and total
map types we defined earlier, and use the techniques of the previous
sections to establish their properties.

Most of the exercises in this section are written a little differently
than the exercises in earlier sections.  We use `postulate` keyword,
which we saw earlier in the [Equality]({{ site.baseurl }}/Equality/)
section.  Here, the `postulate` keyword allows us to use these lemmas
in later sections, even if you are not able to complete all of the
exercises, or complete them in a different file.  When you work the
exercises, be sure to remove the `postulate` keyword when you add your
proof.

## Imports

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Bool
open import Data.Maybe
open import Data.String
open import plc.fp.Maps
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
```

## Properties of total maps

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
                         → T (not (x1 == x2))
                           → (x1 ↦ v , m) x2 ≡ m x2
-- Remove the keyword postulate, and fill in your proof here
```

#### Exercise `tUpdateShadow` (recommended)

Show that if we update a map `m` at a key `x` with a value `v1`, and
then update again with the same key `x` and another value `v2`, the
resulting map behaves the same (gives the same result when applied to
any key) as the simpler map obtained by performing just the *second*
`update` on `m`:

```
postulate tUpdateShadow : ∀ {A : Set} (m : TotalMap A) x v1 v2
                            → (x ↦ v2 , x ↦ v1 , m) ≡ (x ↦ v2 , m)
-- Remove the keyword postulate, and fill in your proof here
```


{::comment}
-- #### Exercise `tUpdateShadow` (recommended)

-- For this and the next lemma, it is convenient to use the reflection
-- idioms introduced in chapter \CHAP{IndProp}.  We begin by proving a
-- fundamental _reflection lemma_ relating the equality proposition on
-- strings with the boolean function `eqb_string`.

-- postulate eqbStringP : ∀ (x y : String) → x ≡ y ⇔ x == y
-- -- Remove the keyword postulate, and fill in your proof here
-- 
-- Now, given `string`s `x1` and `x2`, we can use the tactic
--     `destruct (eqb_stringP x1 x2)` to simultaneously perform case
--     analysis on the result of `eqb_string x1 x2` and generate
--     hypotheses about the equality (in the sense of `=`) of `x1`
--     and `x2`. *)
{:/comment}

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
                             → T (not (x2 == x1))
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
                        → T (not (x2 == x1))
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
                            → T (not (x2 == x1))
                              → (x1 ↦ₚ v1 , x2 ↦ₚ v2 , m)
                                  ≡ (x2 ↦ₚ v2 , x1 ↦ₚ v1 , m)
-- Remove the keyword postulate, and fill in your proof here
```

---

*This page is derived from Pierce et al.; for more information see the
[sources and authorship]({{ site.baseurl }}/Sources/) page.*
