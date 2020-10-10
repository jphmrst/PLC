---
title     : "Negation: Negation, with intuitionistic and classical logic"
layout    : page
prev      : /Connectives/
permalink : /Negation/
next      : /Quantifiers/
---

```
module plc.lc.Negation where
```

This section introduces negation, and discusses intuitionistic
and classical logic.

## Imports

```
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import plc.vfp.Relations using (_≃_)
open import plc.lc.Isomorphism using (extensionality)
```


## Standard Prelude

Definitions similar to those in this section can be found in the standard library:
```
import Relation.Nullary using (¬_)
import Relation.Nullary.Negation using (contraposition)
```

## Unicode

This section uses the following Unicode symbols:

    ¬  U+00AC  NOT SIGN (\neg)
    ≢  U+2262  NOT IDENTICAL TO (\==n)

---

*This page is derived from Wadler et al.; for more information see the [sources and authorship]({{ site.baseurl }}/Sources/) page.*
