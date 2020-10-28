---
title     : "Relations: Inductive definition of relations"
layout    : page
prev      : /DataProp/
permalink : /Relations/
next      : /DataRel/
---

```
module plc.vfp.Relations where
```

So far we have used and proven statements about equality.  The
premises and conclusions of the lemmas and statements have been of the
form `A ≣ B`.  The proposition of equality is built into Agda's
library: since the first section we have imported it from module `Eq`.
But there is nothing unique or special about the equality relation.
We can define other relations in the same way that the standard
library defines equality.  We will continue our pattern of looking
first at relations involving natural numbers, and in the next section
exploring relations on data structures such as linked lists.

## Imports

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.String hiding (_<_)
open import Data.Char hiding (_<_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Function using (_∘_)
```


## Defining relations

The relation _less than or equal_ has an infinite number of
instances.  Here are a few of them:

    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
```
data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n
```
Here `z≤n` and `s≤s` (with no spaces) are constructor names, while
`zero ≤ n`, and `m ≤ n` and `suc m ≤ suc n` (with spaces) are types.
In the same way as `_≡_`, `_≤_` is an _indexed_ datatype,
where the type `m ≤ n` is indexed by two natural numbers,
`m` and `n`.  In Agda any line beginning
with two or more dashes is a comment, and here we have exploited that
convention to write our Agda code in a form that resembles the
corresponding proof tree inference rules,
a trick we will use often from now on.

Both definitions above tell us the same two things:

* _Base case_: for all naturals `n`, the proposition `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

* _Base case_: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

For example, here in inference rule notation is the proof that
`2 ≤ 4`:

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof:
```
_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)
```

When we prove a formula built with the `_≤_` relation, the evidence we
supply will _always_ be constructed with either the `z≤n` or the `s≤s`
constructor.  Our definition for `_≤_` includes only these
constructors.  This is the same sort of observation as the idea that
all natural numbers are built using either the `zero` or `suc`
constructors.  There is no other way to construct a number, and there
is no other way to construct evidence for `_≤_`.  When we use a
function call to return a natural number, we may be hiding away the
part of the program that uses one of the `ℕ` constructors, but the
result is nonetheless based one one of the `ℕ` constructors.  The same
is true for the evidence of `_≤_` formulas: even when we use some
other proof function to produce evidence for a `_≤_` formula, that
evidence value can always be associated with one of the two
constructors `z≤n` or `s≤s`.

We declare the precedence for comparison as follows:

```
infix 4 _≤_
```
We set the precedence of `_≤_` at level 4, so it binds less tightly
than `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.


## Inversion on evidence

{::comment}

TODO FUTURE --- If we do the "Logic" section first, then we can use
Pierce's example `ev n → (n = 0) ∨ (∃ n', n = S (S n') ∧ ev n')`.
Maybe more exercises available as well?

{:/comment}

Suppose we are proving some fact involving a number `n`, and we are
given `n ≤ n₁` as a hypothesis.  We already know how to perform case
analysis on `n`, generating separate subgoals for the case where `n`
is `zero` and the case where `n = suc n'` for some `n'`.  But for some
proofs we may instead want to analyze the _evidence_ that `n ≤ n₁`
directly.  When this evidence is a premise, we can apply pattern
matching to base our reasoning on the form of evidence we have.  We
can also rely on Agda to rule our clauses which are absurd.

There is only one way to prove that `suc m ≤ suc n`, for any `m`
and `n`.  Let's say that we want to prove this formula:

```
inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n
```

This lemma is the opposite of the constructor: the constructor maps
evidence that `m ≤ n` to evidence that `suc m ≤ suc n`.  This lemma
goes the opposite way.  So we can begin with

    inv-s≤s m≤n = ?

Here `m≤n` (a single three-character identifier, with no spaces) is a
variable name while `m ≤ n` (three one-character identifiers,
separated by spaces) is a type, and the latter is the type of the
former.  It is a common convention in Agda to derive a variable name
by removing spaces from its type.

We can ask Agda to split the `m≤n` parameter into cases, and there is
in fact only one relevant case:

    inv-s≤s (s≤s m≤n₀) = {  }0

The type of the premise is `suc m ≤ suc n`, which is inconsistent with
the type resulting from the constructor `z≤n`, so therefore there is
no clause with the `z≤n` constructor.  Now we have available evidence
that `m ≤ n`, bound to the name `m≤n₀`:

```
inv-s≤s (s≤s m≤n₀) = m≤n₀
```

In our definitions, we go from smaller things to larger things.  For
instance, from `m ≤ n` we can conclude `suc m ≤ suc n`, where `suc m`
is bigger than `m` (that is, the former contains the latter), and
`suc n` is bigger than `n`. Inversion on evidence allows us to go
from bigger things to smaller things.

Not every rule is invertible; indeed, the rule for `z≤n` has
no non-implicit hypotheses, so there is nothing to invert.
But often inversions of this kind hold.

Another example of inversion is showing that there is
only one way a number can be less than or equal to zero.
```
inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
    --------
  → m ≡ zero
inv-z≤n z≤n = refl
```

## Properties of ordering relations

Relations pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Reflexive_. For all `n`, the relation `n ≤ n` holds.
* _Transitive_. For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
* _Anti-symmetric_. For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
* _Total_. For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

* _Preorder_. Any relation that is reflexive and transitive.
* _Partial order_. Any preorder that is also anti-symmetric.
* _Total order_. Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it is a preorder, partial order, or total order.  A
careful author will often call out these properties — or their lack —
for instance by saying that a newly introduced relation is a partial
order but not a total order.


#### Exercise `orderings` (practice) {#orderings}

Give an example of a preorder that is not a partial order.

```
-- Your code goes here
```

Give an example of a partial order that is not a total order.

```
-- Your code goes here
```

## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflexivity:
```
≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl
```
The proof is a straightforward induction on the implicit argument `n`.
In the base case, `zero ≤ zero` holds by `z≤n`.  In the inductive
case, the inductive hypothesis `≤-refl {n}` gives us a proof of `n ≤
n`, and applying `s≤s` to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p`
hold, then `m ≤ p` holds.  Again, `m`, `n`, and `p` are implicit:
```
≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n       _          =  z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)
```
Here the proof is by induction on the _evidence_ that `m ≤ n`.  In the
base case, the first inequality holds by `z≤n` and must show `zero ≤ p`,
which follows immediately by `z≤n`.  In this case, the fact that
`n ≤ p` is irrelevant, and we write `_` as the pattern to indicate
that the corresponding evidence is unused.

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.

The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that such a
case cannot arise, and does not require (or permit) it to be listed.

Alternatively, we could make the implicit parameters explicit:
```
≤-trans′ : ∀ (m n p : ℕ)
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans′ zero    _       _       z≤n       _          =  z≤n
≤-trans′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans′ m n p m≤n n≤p)
```
One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.

The technique of induction on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on
values of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Anti-symmetry

The third property to prove about comparison is that it is
antisymmetric: for all naturals `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds:
```
≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)
```
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold.

In the base case, both inequalities hold by `z≤n`.  So we are given
`zero ≤ zero` and `zero ≤ zero`, and we must show `zero ≡ zero`, which
follows by reflexivity.  (Reflexivity of equality, that is, not
reflexivity of inequality.)

In the inductive case, the first inequality holds by `s≤s m≤n` and the
second inequality holds by `s≤s n≤m`, and so we are given `suc m ≤ suc n`
and `suc n ≤ suc m` and must show `suc m ≡ suc n`.  The inductive
hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`, and our goal
follows by congruence.

#### Exercise `≤-antisym-cases` (practice) {#leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?

```
-- Your code goes here
```


## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total:
```
data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n
```
Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

(For those familiar with logic, the above definition
could also be written as a disjunction. Disjunctions will
be introduced in the [Logic]({{ site.baseurl }}/Logic/) section.)

This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype:
```
data Total′ : ℕ → ℕ → Set where

  forward′ : ∀ {m n : ℕ}
    → m ≤ n
      ----------
    → Total′ m n

  flipped′ : ∀ {m n : ℕ}
    → n ≤ m
      ----------
    → Total′ m n
```
Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality:
```
≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)
```
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

* _First base case_: If the first argument is `zero` and the
  second argument is `n` then the forward case holds,
  with `z≤n` as evidence that `zero ≤ n`.

* _Second base case_: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

* _Inductive case_: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  + The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  + The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following:
```
≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)
```
This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound on the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case:
```
≤-total″ : ∀ (m n : ℕ) → Total m n
≤-total″ m       zero                      =  flipped z≤n
≤-total″ zero    (suc n)                   =  forward z≤n
≤-total″ (suc m) (suc n) with ≤-total″ m n
...                        | forward m≤n   =  forward (s≤s m≤n)
...                        | flipped n≤m   =  flipped (s≤s n≤m)
```
It differs from the original code in that it pattern
matches on the second argument before the first argument.


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is _monotonic_ with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning:

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right:
```
+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)
```
The proof is by induction on the first argument.

* _Base case_: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

* _Inductive case_: The first argument is `suc n`, in which case
  `suc n + p ≤ suc n + q` simplifies to `suc (n + p) ≤ suc (n + q)`.
  The inductive hypothesis `+-monoʳ-≤ n p q p≤q` establishes that
  `n + p ≤ n + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition:
```
+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n
```
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results:
```
+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)
```
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

```
-- Your code goes here
```


## Strict inequality {#strict-inequality}

We can define strict inequality similarly to inequality:
```
infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n
```
The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.

Clearly, strict inequality is not reflexive. However it is
_irreflexive_ in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
_trichotomy_: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly when `n < m`).
It is also monotonic with regards to addition and multiplication.

Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred to
the [Negation]({{ site.baseurl }}/Negation/) section.

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by
exploiting the corresponding properties of inequality.

#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

```
-- Your code goes here
```

#### Exercise `trichotomy` (practice) {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`.

Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation]({{ site.baseurl }}/Negation/).)

```
-- Your code goes here
```

#### Exercise `+-mono-<` (practice) {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

```
-- Your code goes here
```

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

```
-- Your code goes here
```

#### Exercise `<-trans-revisited` (practice) {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relation between strict inequality and inequality and
the fact that inequality is transitive.

```
-- Your code goes here
```


## Even and odd

As a further example, let's specify even and odd numbers.  In the
previous chapter, we defined `even` and `odd` as functions each
mapping a natural number to a boolean value.  In the same way that we
can have both a comparison function and a comparison relation.
Inequality and strict inequality are _binary relations_, while even
and odd are _unary relations_, sometimes called _predicates_:

```
data even : ℕ → Set
data odd : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc   : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
```

A number is even either if it is zero, or if it is the successor of an
odd number.  A number is odd if it is the successor of an even number.

This is our first use of _mutually recursive_ declarations.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).

This is also our first use of _overloaded_ constructors,
that is, using the same name for constructors of different types.
Here `suc` means one of three constructors:

    suc : ℕ → ℕ

    suc : ∀ {n : ℕ}
      → odd n
        ------------
      → even (suc n)

    suc : ∀ {n : ℕ}
      → even n
        -----------
      → odd (suc n)

Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.

We can show that the sum of two even numbers is even:

```
e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)
```

Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.

This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.

To show that the sum of two even numbers is even, consider the
evidence that the first number is even. If it is because it is zero,
then the sum is even because the second number is even.  If it is
because it is the successor of an odd number, then the result is even
because it is the successor of the sum of an odd and an even number,
which is odd.

To show that the sum of an odd and even number is odd, consider the
evidence that the first number is odd. If it is because it is the
successor of an even number, then the result is odd because it is the
successor of the sum of two even numbers, which is even.

#### Exercise `double-even` (practice) {#double-even}

Recall the function `double`,

```
double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))
```

Prove that the `double` of any number is even:

    even-double : ∀ n → even (double n)
    -- Your clauses here

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

```
-- Your code goes here
```

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that
Exercise [Bin]({{ site.baseurl }}/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:

    ⟨⟩ I O I I
    ⟨⟩ O O I O I I

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings:

    Can b
    ------------
    Can (inc b)

Show that converting a natural to a bitstring always yields a
canonical bitstring:

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity:

    Can b
    ---------------
    to (from b) ≡ b

(Hint: For each of these, you may first need to prove related
properties of `One`. Also, you may need to prove that
if `One b` then `1` is less or equal to the result of `from b`.)

```
-- Your code goes here
```

## Regular expressions

The `even` and `odd` properties provide a simple example for
illustrating inductive definitions and the basic techniques for
reasoning about them, but it is not terribly exciting — it is hard to
see much difference between those inductive relations and the
corresponding recursive functions.

To give a better sense of the power of inductive relations, we now
show how to use them to model a classic concept in computer science:
_regular expressions_ (REs).  REs are a notation for describing a set
of strings which match a particular pattern.  The application of an RE
is determining whether a particular string _matches_ that RE.

There are several forms of RE, and each form has different rules which
match various strings.

```
data RegEx : Set where
  ∅ : RegEx
  ε : RegEx
  [_] : Char → RegEx
  _>>_ : RegEx → RegEx → RegEx
  _||_ : RegEx → RegEx → RegEx
  _* : RegEx → RegEx
```

 - The RE `∅` does not match any strings.

 - The RE `ε` matches the empty string `""`.

 - The literal RE for any character `c`, `[ c ]` matches the
   one-character string containing `c`.

 - If `re₁` matches `s₁`, and `re₂` matches `s₂`, then the PR `re1 >> re2`
   matches the concatentation `s₁ ++ s₂`.

 - If at least one of `re₁` and `re₂` matches `s`, then `re₁ || re₂`
   also matches `s`.

 - Finally, if we can write some string `s` as the concatenation of a
   sequence of strings `s ≡ s₁ ++ ... ++ sₖ`, and the RE `re` matches
   each one of the strings `sᵢ`, then `re *` matches `s`.

   In particular, the sequence of strings may be empty, so `re *`
   always matches the empty string `""` no matter what `re` is.

   This notation is called the _Kleene star_, named after the
   scientist who first used it to specify repetition in syntax.

Here are some examples of regular expressions:


```
re1 : RegEx
re1 = [ 'e' ]
re2 : RegEx
re2 = [ 'c' ] >> [ 'd' ]
re3 : RegEx
re3 = re1 || re2
re4 : RegEx
re4 = (re3 *) >> [ 'z' ]
```

 - The regular expression `re1` for the literal character `e` matches
   only one string `"e"`.
   
 - The concatenation RE `re2` matches first the literal character `c`,
   and then the literal character `d`.  So `re2` also matches exactly
   one string `"cd"`.
   
 - `re3` places `re1` and `re2` in alternation, and matches both `"e"`
   and `"cd"`.
   
 - Finally `re4` adds the Kleene star, and matches strings like
   `"eecdz"`, `"cdecdez"` and `"eeeecdcdecdecdeeecdcdcdz"`.  It also
   matches `"z"`, since there could be zero repetitions matching
   `re3`.

Now we can translate the informal descriptions of how each form of RE
matches strings into a formal Agda definition.  We use the operator
`_=~_` to associate a regular expression and a string which the RE
matches.

```
data _=~_ : RegEx → String → Set where
```

We define forms of evidence which explain how each form of RE matches
its strings.  The `ε` RE can match only the empty string:

```
  ε=~Empty : ε =~ ""
```

For any character, the literal RE `[ c ]` matches exactly one string.
The `fromChar` function converts a character to the length-one string
containing that character.

```
  =~char : ∀ {c : Char} → [ c ] =~ fromChar c
```

The `=~>>` constructor builds evidence for the concatenation of two
REs, given evidence of how the two component REs match two substrings.

```
  =~>> : ∀ {r₁ r₂ : RegEx} {s₁ s₂ : String}
           → r₁ =~ s₁ → r₂ =~ s₂
             → (r₁ >> r₂) =~ (s₁ ++ s₂)
```

We have two ways of forming evidence for what a RE built with `_||_`
matches.  One rule applies when the left sub-RE matches the string;
the other rule, when the right sub-RE matches.

```
  =~||₁ : ∀ {r₁ r₂ : RegEx} {s₁ : String} → r₁ =~ s₁ → (r₁ || r₂) =~ s₁
  =~||₂ : ∀ {r₁ r₂ : RegEx} {s₂ : String} → r₂ =~ s₂ → (r₁ || r₂) =~ s₂
```

There are two rules for the Kleene star.  The Kleene star can match
zero uses of the underlying RE, which means that it must match the
empty string.

```
  =~*Empty : ∀ {r : RegEx} → (r *) =~ ""
```

The other rule for the Kleene star uses recursion to describe the
first of several uses of the underlying RE `r`.  We identify two
substrings `s₁` and `s₂`: the `=~*One` rule requires evidence first
that `r` matches `s₁`, and then that all further applications of `r`
match `s₂`.

```
  =~*One : ∀ {r : RegEx} {s₁ s₂ : String}
             → r =~ s₁ → (r *) =~ s₂
               → (r *) =~ (s₁ ++ s₂)
```

To prove a formula using the `_=~_` connective, we use combinations of
the contructors for `_=~_`.  This is consistent with the proofs we
have written so far.  The constructor for the `_≡_` relation is
`refl`, so if we want to prove a formula built with `_≡_` then our
evidence is based on `refl`.  The constructors for the `even` relation
are `zero` and `suc`, and when we wrote proofs for formulas built with
`even` we built evidence with one of those constructors.  And here,
when we wish to prove a `_=~_` relation, we use its constructors.

When a regular expression forms is not recursive, the proofs of
matching for those REs are very simple:

```
_ : ε =~ ""
_ = ε=~Empty

_ : [ 'e' ] =~ "e"
_ = =~char
```

Here are two ways of writing the proof that the RE of two literals
`[ 'e' ] >> [ 'f' ]` matches the string `"ef"`.  We could begin
with the proofs that each of the REs `[ 'e' ]` and `[ 'f' ]` match
the length-one strings `"e"` and `"f"`:

    e : [ 'e' ] =~ "e"
    e = =~char

    f : [ 'f' ] =~ "f"
    f = =~char

Then we can combine these proofs with the `=~>>` constructor for the
overall RE,

```
_ : ([ 'e' ] >> [ 'f' ]) =~ "ef"
_ = =~>> e f
    where e : [ 'e' ] =~ "e"
          e = =~char

          f : [ 'f' ] =~ "f"
          f = =~char
```

Alternatively, we could simply write the subproofs directly as
arguments of the `=~>>` constructor,

```
_ : ([ 'e' ] >> [ 'f' ]) =~ "ef"
_ = =~>> =~char =~char
```

#### Exercise `match-simple-alt` (recommended)

Show that the regular expression `[ 'c' ] || [ 'd' ]` matches the
string `"d"`.

#### Exercise `match-simple-star` (recommended)

Show that the regular expression `([ 'c' ] || [ 'd' ]) *` matches the
string `"cdc"`.

#### Exercise `match4-z` (recommended)

Show that the regular expression `re4` above matches the string
`"z"`.

#### Exercise `match3-cd` (practice)

Show that the regular expression `re3` above matches the string
`"cd"`.

#### Exercise `match-cdecdz` (practice)

Show that the regular expression `re4` above matches the string
`"cdecdz"`.

## Records

One common case of using relations has a single constructor, and
multiple premises.

    data SomeRelation (T1 T2 ... Tn : Set) : Set where
      oneConstructor : ∀ (x1 : ...) (x2 : ...) ... (xM : ...)
                         → SomeRelation ...

We will often find ourselves writing accompanying helper functions to
extract the `x1`, `x2` and so forth for a particular instance of the
relation,

    x1 (oneConstructor v1 v2 ... vM) = v1

This use case is common enough that Agda offers a shorthand `record`
notation.  Agda's records are similar to the instance variables of
Java's objects or to C's `structs`, although of course wothout the
mutability of those languages.  We will use Agda's records to describe
relations when we need to name subrelations for later access.

In this section we make frequent use of the composition operator
discussed in the [Functional section]({{ site.baseurl
}}/Functional/#fnComposition), which here we import from the
`Function` module.  Note that Agda defines `∘` using a lambda
expression,

    f ∘ g = λ x → f (g x)

And note also that like most characters in Agda, `∘` can be used to
build identifier names.  So while `f ∘ g` is the composition of the
two functions `f` and `g`, `f∘g` is a three-character name.

### Isomorphism

Two sets are isomorphic if their elements can be put in exact
correspondence.  Isomorphism is another name for the idea of a
_bijection_, or for two sets which are both _one-to-one_ and _onto_.
Here is a formal definition of isomorphism:

```
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_
```

Let's unpack the definition. An isomorphism between sets `A` and `B` consists
of four things:

 - A function `to` from `A` to `B`,

 - A function `from` from `B` back to `A`,
 
 - Evidence `from∘to` asserting that `from` is a *left-inverse* for
   `to`,
 
 - Evidence `to∘from` asserting that `from` is a *right-inverse* for
   `to`.

In particular, the third asserts that `from ∘ to` is the identity, and
the fourth that `to ∘ from` is the identity, hence the names.  The
declaration `open _≃_` makes available the names `to`, `from`,
`from∘to`, and `to∘from`, otherwise we would need to write `_≃_.to`
and so on.

The above is our first use of records. A record declaration is equivalent
to a corresponding inductive data declaration:
```
data _≃′_ (A B : Set): Set where
  mk-≃′ : ∀ (to : A → B) →
          ∀ (from : B → A) →
          ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
          ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
          A ≃′ B

to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f

from′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘to′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (x : A) → from′ A≃B (to′ A≃B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f

to∘from′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (y : B) → to′ A≃B (from′ A≃B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g
```

We construct values of the record type with the syntax

    record
      { to    = f
      ; from  = g
      ; from∘to = g∘f
      ; to∘from = f∘g
      }

which corresponds to using the constructor of the corresponding
inductive type

    mk-≃′ f g g∘f f∘g

where `f`, `g`, `g∘f`, and `f∘g` are values of suitable types.


### Isomorphism is an equivalence

Isomorphism is an equivalence, meaning that it is reflexive, symmetric,
and transitive.  To show isomorphism is reflexive, we take both `to`
and `from` to be the identity function:
```
≃-refl : ∀ {A : Set}
    -----
  → A ≃ A
≃-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    ; to∘from = λ{y → refl}
    }
```
In the above, `to` and `from` are both bound to identity functions,
and `from∘to` and `to∘from` are both bound to functions that discard
their argument and return `refl`.  In this case, `refl` alone is an
adequate proof since for the left inverse, `from (to x)`
simplifies to `x`, and similarly for the right inverse.

To show isomorphism is symmetric, we simply swap the roles of `to`
and `from`, and `from∘to` and `to∘from`:
```
≃-sym : ∀ {A B : Set}
  → A ≃ B
    -----
  → B ≃ A
≃-sym A≃B =
  record
    { to      = from A≃B
    ; from    = to   A≃B
    ; from∘to = to∘from A≃B
    ; to∘from = from∘to A≃B
    }
```

To show isomorphism is transitive, we compose the `to` and `from`
functions, and use equational reasoning to combine the inverses:
```
≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
≃-trans A≃B B≃C =
  record
    { to       = to   B≃C ∘ to   A≃B
    ; from     = from A≃B ∘ from B≃C
    ; from∘to  = λ{x →
        begin
          (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x)
        ≡⟨⟩
          from A≃B (from B≃C (to B≃C (to A≃B x)))
        ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
          from A≃B (to A≃B x)
        ≡⟨ from∘to A≃B x ⟩
          x
        ∎}
    ; to∘from = λ{y →
        begin
          (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y)
        ≡⟨⟩
          to B≃C (to A≃B (from A≃B (from B≃C y)))
        ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
          to B≃C (from B≃C y)
        ≡⟨ to∘from B≃C y ⟩
          y
        ∎}
     }
```

#### Exercise `_⇔_` (practice) {#iff}

We define the equivalence of propositions (also known as "if and only
if") as follows:

```
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
infix 3 _⇔_
```

Show that equivalence is reflexive, symmetric, and transitive.

```
-- Your code goes here
```

## Standard library

Definitions similar to those in this section can be found in the standard library:
```
import Data.Nat using (_≤_; z≤n; s≤s)
import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total;
                                  +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
```
In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in
the [Logic]({{ site.baseurl }}/Logic/) section),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here,
and more arguments are implicit.


## Unicode

This section uses the following Unicode symbols:

    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ∘  U+2218  RING OPERATOR (\o, \circ, \comp)
    ≃  U+2243  ASYMPTOTICALLY EQUAL TO (\~- or \simeq)
    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.

---

*This page is derived primarily from Wadler et al., with additional
material by Maraist.  The introduction to inversion on evidence, and
the regular expressions example, are adapted from Pierce et al.  For
more information see the [sources and authorship]({{ site.baseurl
}}/Sources/) page.*
