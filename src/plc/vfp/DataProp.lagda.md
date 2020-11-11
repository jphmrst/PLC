---
title     : "DataProp: Properties of data structures"
layout    : page
prev      : /Induction/
permalink : /DataProp/
next      : /Relations/
---

```
module plc.vfp.DataProp where
```

In the same way that we can state and prove properties about natural
numbers, we can state and prove properties about other structures.  In
this section we revisit the `Pair` and `List` data types to study
their properties.

## Imports

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Function using (_∘_)
open import Data.Bool
open import Data.Nat
open import Data.List using (List; _∷_; []; _++_; map)
open import Data.String using (String)
open import plc.fp.Poly using (Prod; pair; fst; snd; swapPair;
                               Maybe; nothing; just)
```

## Reasoning about pairs

Pairs are simple structures, and the statements we make about them are
not especially deep.  We rely especially on pattern matching to
extract the structure of pairs when they are the subject of a
statement.

```
surjectivePairing : ∀ {A B : Set} (p : Prod A B) → p ≡ pair (fst p) (snd p)
surjectivePairing (pair a b) = refl
```

The result is immediate, since is easy to see how

    pair (fst (pair a b)) (snd (pair a b))

rewrites to (pair a b).  But if we had left the pair not matched to an
explicit pattern,

    surjectivePairing p = ...

Agda would not be able to find the result.

#### Exercise `snd-fst-is-swapPair` (recommended)

Prove that:

    snd-fst-is-swapPair :  ∀ (A B : Set) (p : Prod A B) →
                             pair (snd p) (fst p) ≡ swapPair p
    -- Your code goes here

#### Exercise `fst-swapPair-is-snd` (recommended)

Prove that:

    fst-swapPair-is-snd : ∀ (A B : Set) (p : Prod A B) →
                            fst (swapPair p) ≡ snd p
    -- Your code goes here

## Reasoning about append

We can reason about lists in much the same way that we reason
about numbers.  Here is the proof that append is associative:
```
++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎
```
The proof is by induction on the first argument. The base case instantiates
to `[]`, and follows by straightforward computation.
The inductive case instantiates to `x ∷ xs`,
and follows by straightforward computation combined with the
inductive hypothesis.  As usual, the inductive hypothesis is indicated by a recursive
invocation of the proof, in this case `++-assoc xs ys zs`.

Recall that Agda supports [sections]({{ site.baseurl }}/Induction/#sections).
Applying `cong (x ∷_)` promotes the inductive hypothesis:

    (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)

to the equality:

    x ∷ ((xs ++ ys) ++ zs) ≡ x ∷ (xs ++ (ys ++ zs))

which is needed in the proof.

It is also easy to show that `[]` is a left and right identity for `_++_`.
That it is a left identity is immediate from the definition:
```
++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎
```
That it is a right identity follows by simple induction:
```
++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎
```
As we will see later,
these three properties establish that `_++_` and `[]` form
a _monoid_ over lists.

## Reasoning about length

```
length : ∀ {A : Set} → List A → ℕ
length []        =  zero
length (x ∷ xs)  =  suc (length xs)
```

The length of one list appended to another is the
sum of the lengths of the lists:
```
length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys =
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎
```
The proof is by induction on the first argument. The base case
instantiates to `[]`, and follows by straightforward computation.  As
before, Agda cannot infer the implicit type parameter to `length`, and
it must be given explicitly.  The inductive case instantiates to
`x ∷ xs`, and follows by straightforward computation combined with the
inductive hypothesis.  As usual, the inductive hypothesis is indicated
by a recursive invocation of the proof, in this case `length-++ xs ys`,
and it is promoted by the congruence `cong suc`.


## Reverse

Using append, it was easy to formulate a function to reverse a list:

```
reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ (x ∷ [])
```

The reverse of the empty list is the empty list.
The reverse of a non-empty list
is the reverse of its tail appended to a unit list
containing its head.

Here is an example showing how to reverse a list:
```
_ : reverse (0 ∷ 1 ∷ 2 ∷ []) ≡ (2 ∷ 1 ∷ 0 ∷ [])
_ =
  begin
    reverse (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    reverse (1 ∷ 2 ∷ []) ++ (0 ∷ [])
  ≡⟨⟩
    (reverse (2 ∷ []) ++ (1 ∷ [])) ++ (0 ∷ [])
  ≡⟨⟩
    ((reverse [] ++ (2 ∷ [])) ++ (1 ∷ [])) ++ (0 ∷ [])
  ≡⟨⟩
    (([] ++ (2 ∷ [])) ++ (1 ∷ [])) ++ (0 ∷ [])
  ≡⟨⟩
    (([] ++ 2 ∷ []) ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ [] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ ([] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ (1 ∷ [] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ ([] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ∎
```
Reversing a list in this way takes time _quadratic_ in the length of
the list. This is because reverse ends up appending lists of lengths
`1`, `2`, up to `n - 1`, where `n` is the length of the list being
reversed, append takes time linear in the length of the first
list, and the sum of the numbers up to `n - 1` is `n * (n - 1) / 2`.
(We will validate that last fact in an exercise later in this section.)

#### Exercise `reverse-++-distrib` (recommended)

Show that the reverse of one list appended to another is the
reverse of the second appended to the reverse of the first:

    reverse (xs ++ ys) ≡ reverse ys ++ reverse xs


#### Exercise `reverse-involutive` (recommended)

A function is an _involution_ if when applied twice it acts
as the identity function.  Show that reverse is an involution:

    reverse (reverse xs) ≡ xs


## Faster reverse

The definition above, while easy to reason about, is less efficient than
one might expect since it takes time quadratic in the length of the list.
The idea is that we generalise reverse to take an additional argument:
```
shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)
```
The definition is by recursion on the first argument. The second argument
actually becomes _larger_, but this is not a problem because the argument
on which we recurse becomes _smaller_.

Shunt is related to reverse as follows:
```
shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys =
  begin
    shunt [] ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ((x ∷ []) ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) (x ∷ []) ys) ⟩
    (reverse xs ++ (x ∷ [])) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎
```
The proof is by induction on the first argument.
The base case instantiates to `[]`, and follows by straightforward computation.
The inductive case instantiates to `x ∷ xs` and follows by the inductive
hypothesis and associativity of append.  When we invoke the inductive hypothesis,
the second argument actually becomes *larger*, but this is not a problem because
the argument on which we induct becomes *smaller*.

Generalising on an auxiliary argument, which becomes larger as the argument on
which we recurse or induct becomes smaller, is a common trick. It belongs in
your quiver of arrows, ready to slay the right problem.

Having defined shunt be generalisation, it is now easy to respecialise to
give a more efficient definition of reverse:
```
reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []
```

Given our previous lemma, it is straightforward to show
the two definitions equivalent:
```
reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎
```

Here is an example showing fast reverse of the list `[ 0 , 1 , 2 ]`:
```
_ : reverse′ (0 ∷ 1 ∷ 2 ∷ []) ≡ 2 ∷ 1 ∷ 0 ∷ []
_ =
  begin
    reverse′ (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    shunt (0 ∷ 1 ∷ 2 ∷ []) []
  ≡⟨⟩
    shunt (1 ∷ 2 ∷ []) (0 ∷ [])
  ≡⟨⟩
    shunt (2 ∷ []) (1 ∷ 0 ∷ [])
  ≡⟨⟩
    shunt [] (2 ∷ 1 ∷ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ∎
```
Now the time to reverse a list is linear in the length of the list.

## Map {#Map}

Map applies a function to every element of a list to generate a
corresponding list.  Map is an example of a _higher-order function_,
one which takes a function as an argument or returns a function as a
result:

    map : ∀ {A B : Set} → (A → B) → List A → List B
    map f []        =  []
    map f (x ∷ xs)  =  f x ∷ map f xs

Map of the empty list is the empty list.
Map of a non-empty list yields a list
with head the same as the function applied to the head of the given list,
and tail the same as map of the function applied to the tail of the given list.

Here is an example showing how to use map to increment every element of a list:
```
_ : map suc (0 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
_ =
  begin
    map suc (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ map suc (1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ map suc (2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ map suc []
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ []
  ≡⟨⟩
    1 ∷ 2 ∷ 3 ∷ []
  ∎
```
Map requires time linear in the length of the list.

It is often convenient to exploit currying by applying
map to a function to yield a new function, and at a later
point applying the resulting function:
```
sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs (0 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
_ =
  begin
    sucs (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    map suc (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    (1 ∷ 2 ∷ 3 ∷ [])
  ∎
```

Any type that is parameterised on another type, such as lists, has a
corresponding map, which accepts a function and returns a function
from the type parameterised on the domain of the function to the type
parameterised on the range of the function. Further, a type that is
parameterised on _n_ types will have a map that is parameterised on
_n_ functions.


#### Exercise `map-compose` (practice)

This exercise uses the composition operator discussed in the
[Functional section]({{ site.baseurl }}/Functional/#fnComposition),
which here we import from the `Function` module.

Prove that the map of a composition is equal to the composition of two maps:

    map (g ∘ f) xs ≡ (map g ∘ map f) xs

```
-- Your code goes here
```

#### Exercise `map-++-distribute` (practice)

Prove the following relationship between map and append:

    map f (xs ++ ys) ≡ map f xs ++ map f ys

```
-- Your code goes here
```

#### Exercise `map-Tree` (practice)

Consider a type of trees with leaves each containing a value of type
`A`, and internal branch nodes each containing a node of type `B`:

```
data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B
```

This representation is a bit more general than you may be used to.
The `leaf` constructor is like a sentinel node where in a language
like C or Java we might be tempted to use `null`.  The values
associated with each branch internal to the tree are all of type `B`,
and these internal branches are assembled with the `node` constructor.
So a tree which we might draw on paper as

               4
              / \
             /   \
            9   "Gamma"
           / \
          /   \
     "Alpha" "Beta"

would be formalized as

```
_ : Tree String ℕ
_ = node (node (leaf "Alpha") 9 (leaf "Beta")) 4 (leaf "Gamma")
```

Define a suitable map operator over trees.  Since there can be two
different types of value within the tree, we need two different
mapping functions which we lift into a map on trees.

    map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D

```
-- Your code goes here
```

## Fold {#Fold}

Fold takes an operator and a value, and uses the operator to combine
each of the elements of the list, taking the given value as the result
for the empty list:
```
foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs
```
Fold of the empty list is the given value.
Fold of a non-empty list uses the operator to combine
the head of the list and the fold of the tail of the list.

Here is an example showing how to use fold to find the sum of a list:
```
_ : foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 10
_ =
  begin
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
  ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎
```
Here we have an instance of `foldr` where `A` and `B` are both `ℕ`.
Fold requires time linear in the length of the list.

It is often convenient to exploit currying by applying
fold to an operator and a value to yield a new function,
and at a later point applying the resulting function:
```
sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 10
_ =
  begin
    sum (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    10
  ∎
```

Just as the list type has two constructors, `[]` and `_∷_`,
so the fold function takes two arguments, `e` and `_⊗_`
(in addition to the list argument).
In general, a data type with _n_ constructors will have
a corresponding fold function that takes _n_ arguments.

As another example, observe that

    foldr _∷_ [] xs ≡ xs

Here, if `xs` is of type `List A`, then we see we have an instance of
`foldr` where `A` is `A` and `B` is `List A`.  It follows that

    xs ++ ys ≡ foldr _∷_ ys xs

Demonstrating both these equations is left as an exercise.


#### Exercise `product` (recommended)

Use fold to define a function to find the product of a list of numbers.
For example:

    product (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 24

```
-- Your code goes here
```

#### Exercise `foldr-++` (recommended)

Show that fold and append are related as follows:

    foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs

```
-- Your code goes here
```

#### Exercise `foldr-∷` (practice)

Show

    foldr _∷_ [] xs ≡ xs

Show as a consequence of `foldr-++` above that

    xs ++ ys ≡ foldr _∷_ ys xs


```
-- Your code goes here
```

#### Exercise `map-is-foldr` (practice)

Show that map can be defined using fold:

    map f ≡ foldr (λ x xs → f x ∷ xs) []

The proof requires extensionality.

```
-- Your code goes here
```

#### Exercise `fold-Tree` (practice)

Define a suitable fold function for the type of trees given earlier:

    fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C


```
-- Your code goes here
```

#### Exercise `map-is-fold-Tree` (practice)

Demonstrate an analogue of `map-is-foldr` for the type of trees.

```
-- Your code goes here
```

#### Exercise `sum-downFrom` (stretch)

Define a function that counts down as follows:
```
downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n
```
For example:
```
_ : downFrom 3 ≡ (2 ∷ 1 ∷ 0 ∷ [])
_ = refl
```
Prove that the sum of the numbers `(n - 1) + ⋯ + 0` is
equal to `n * (n ∸ 1) / 2`:

    sum (downFrom n) * 2 ≡ n * (n ∸ 1)

## Properties in the standard library {#strProps}

The Agda standard library contains many pre-proven properties of the
data structures it defines, although they can be tricky to access.
The library has evolved a number of idioms which provide a framework
for storing properties.  The idioms give a high degree of consistency,
so that it is predictable where properties will be stored, and make
extensive use of records to bundle properties together.  However, the
structures can be daunting to approach for the first time.  This
section identifies a number of useful properties of `String` values
which will be useful in later sections.  To simplify this
presentation, we will postulate the results rather than delve into the
mechanics of Agda's more complicated proof features.

```
module String where
  open import Data.String using (_==_)
```

Note that we are naming these results inside a sub-module, so to use
these properties later we would write

    open import plc.vfp.DataProp as DP
    open DP.String

We compare strings with the operator `_==_`.  It is useful to know
that, as we would expect from any equality relationship, `_==_` forms
an equivalence relation, that is, it is reflexive, symmetric and
transitive:

```
  postulate ==-refl : ∀ {s : String} → (s == s) ≡ true
  postulate ==-sym : ∀ {s₁ s₂ : String} → (s₁ == s₂) ≡ (s₂ == s₁)
  postulate ==-trans : ∀ {s₁ s₂ s₃ : String}
                         → (s₁ == s₂) ≡ true → (s₂ == s₃) ≡ true
                           → (s₁ == s₃) ≡ true
  -- End of module String
```

## The `inspect` idiom {#inspect}

We have occasionally used the `with` keyword to refine our pattern
matching, such as in
[the `find` function for partial maps]({{ site.baseurl }}/NatData/).
One common difficulty in using a `with` clause for proofs is that
Agda keeps no link between the expression in the `with` clause and
the names or expressions associated with the results of evaluating it.
We work around this problem by applying `with` to a datatype which
returns the result value along with evidence
that the expression and the value are related.
The _design_ of this datatype uses advanced Agda techniques
which we will not discuss in detail,
but it is straightforward to _use_ this datatype in practice.

```
module Inspect where
```

Note that we are again naming these utilities inside a sub-module, so
to use them later we would write

    open import plc.vfp.DataProp as DP
    open DP.Inspect

The technical code behind `inspect` idiom is:

```
  data Inspection {a} {A : Set a} (x : A) : Set a where
    resultEvidence : (y : A) → x ≡ y → Inspection x

  inspect : ∀ {a} {A : Set a} (x : A) → Inspection x
  inspect x = resultEvidence x refl
  -- End of module Inspect
```

Consider this excerpt from the `find` function:

    find key (entry k v pm) with key ≡idᵇ k
    ...                        | true = ...
    ...                        | false = ...

If we needed evidence in the body of the first branch that
`key ≡idᵇ k ≡ true`, or in the second branch that
`key ≡idᵇ k ≡ false`, none is available.  However we can use `inspect`
to capture that evidence for later use:

    find key (entry k v pm) with inspect (key ≡idᵇ k)
    ...                        | resultEvidence true kkIsT = ...
    ...                        | resultEvidence false kkIsF = ...

In the first branch, the value of `kkIsT` will be evidence for
`key ≡idᵇ k ≡ true`; and in the second branch, the value of
`kkIsF` will be evidence for `key ≡idᵇ k ≡ false`.

We will apply this technique in the
[MapProps]({{ site.baseurl }}/MapProps/) section.

## Standard Library

Definitions similar to those in this section can be found in the
standard library:

```
import Data.List.Properties
  using (reverse-++-commute; map-compose; map-++-commute; foldr-++)
  renaming (mapIsFold to map-is-foldr)
```

## Unicode

This section uses the following Unicode symbols:

    λ   U+03BB  GREEK SMALL LETTER LAMDA  (\Gl, \lambda)
    ′  U+2032  PRIME (\')
    ℕ  U+2115  DOUBLE-STRUCK CAPITAL N (\bN)
    →  U+2192  RIGHTWARDS ARROW (\to, \r, \->)
    ∀  U+2200  FOR ALL (\forall, \all)
    ∷  U+2237  PROPORTION  (\::)
    ∸  U+2238  DOT MINUS (\.-)
    ≡  U+2261  IDENTICAL TO (\==)
    ⊗  U+2297  CIRCLED TIMES  (\otimes, \ox)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)

---

*This page is derived from Wadler et al., with some exercises from
Pierce et al., and some additional text by Maraist; for more information
see the [sources and authorship]({{ site.baseurl }}/Sources/) page.*
