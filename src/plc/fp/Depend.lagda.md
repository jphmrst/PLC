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
there is a fourth posibility, which is less common found.  In Agda,
**types** can depend on **terms**.  We will use this idea extensively
in the next chapter, but we begin with a simple example in this
section.

Recall our definition of a list of natural numbers:

    data NatList : Set where
      [] : NatList
      _∷_ : ℕ → NatList → NatList

Lists of any length all have the same type.  `[]`, `1 :: []` and
`1 :: 2 :: 3 :: 4 :: 5 :: []` all have type `NatList`.  
*Vectors* are a linked linear data structure where the length of
the vector *is* distinguished by the type.

```
module NatVactor where
    data NatVec : ℕ → Set where
      []  : NatVec zero
      _∷_ : ∀ {n : ℕ} (x : ℕ) (xs : NatVec n) → NatVec (suc n)
```

Instead of quantifying over another type, as we did with polymorphic
`List`, here we are quantifying over a natural number.  `NatVec 2`
and `NatVec 5` are not the same type, since `2` and `5` are not the
same number.
