---
title     : "Induction: Proof by Induction"
layout    : page
prev      : /Proof/
permalink : /Induction/
next      : /DataProp/
---

```
module plc.vfp.Induction where
```

> Induction makes you feel guilty for getting something out of nothing
> ... but it is one of the greatest ideas of civilization.
> -- Herbert Wilf

In this section we will look at the underlying technique we will use
for (most of) our proofs: _proof by induction_.  This approach was
already suggested in the last chapter, where we defined several
_inductive datatypes_.  Inductive proofs mirror the recursive
structure of these datatypes: one or more base cases which are not
recursive, and one or more recursive cases which rely on strictly
smaller uses of an assertion.  We will begin with inductive proofs
about the natural numbers and their operators; in the next section we
apply these techniques to data structures, in particular lists.

We first review some properties of the natual numbers, and then
introduce general Agda statements and proofs.

## Imports

We require equality as in the previous chapter, plus the naturals
and some operations upon them.  We also import a couple of new operations,
`cong`, `sym`, and `_≡⟨_⟩_`, which are explained below:
```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
```

## Properties of operators

Operators pop up all the time, and mathematicians have agreed on names
for some of the most common properties.  When we need to discuss
operators in general, we will use symbols like ⊕ and ⊗.

* _Identity_.  Operator `⊕` has left identity `z` if `z ⊕ n ≡ n`, and
  right identity `w` if `n ⊕ w ≡ n`, for all `n`. A value that is both
  a left and right identity is just called an identity.  Identity is
  also sometimes called _unit_.

  Addition of numbers `+` has zero as an identity, and concatenation
  of strings has the empty string as an identity.  Subtraction has
  zero as a right identity, and does not have a left identity.

* _Associativity_.   Operator `⊕` is associative if the location
  of parentheses does not matter: `(m ⊕ n) ⊕ p ≡ m ⊕ (n ⊕ p)`,
  for all `m`, `n`, and `p`.

* _Commutativity_.   Operator `⊕` is commutative if order of
  arguments does not matter: `m ⊕ n ≡ n ⊕ m`, for all `m` and `n`.

  Addition, multiplication, and string concatenation are all both
  associative and commutative, but subtraction and division are
  neither.

* _Distributivity_.   Operator `⊗` distributes over operator `⊕` from the
  left if `(m ⊕ n) ⊗ p ≡ (m ⊗ p) ⊕ (n ⊗ p)`, for all `m`, `n`, and `p`,
  and from the right if `m ⊗ (p ⊕ q) ≡ (m ⊗ p) ⊕ (m ⊗ q)`, for all `m`,
  `p`, and `q`.

  Multiplication distributes over addition, but addition does not
  distribute over multiplication.  For boolean operators, ∧
  distributes over ∨, _and_ ∨ distributes over ∧.

If you ever bump into an operator at a party, you now know how
to make small talk, by asking whether it has a unit and is
associative or commutative.  If you bump into two operators, you
might ask them if one distributes over the other.

Less frivolously, if you ever bump into an operator while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it has an identity, is associative or commutative, or
distributes over another operator.  A careful author will often call
out these properties — or their lack — for instance by pointing out
that a newly introduced operator is associative but not commutative.

#### Exercise `operators` (practice) {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.
(You do not have to prove these properties.)

Give an example of an operator that has an identity and is
associative but is not commutative.
(You do not have to prove these properties.)

## Associativity

One property of addition is that it is _associative_, that is, that the
location of the parentheses does not matter:

    (m + n) + p ≡ m + (n + p)

Here `m`, `n`, and `p` are variables that range over all natural numbers.

We can test the proposition by choosing specific numbers for the three
variables:
```
_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎
```
Here we have displayed the computation as a chain of equations, one
term to a line.  It is often easiest to read such chains from the top
down until one reaches the simplest term (in this case, `12`), and
then from the bottom up until one reaches the same term.

The test reveals that associativity is perhaps not as obvious as first
it appears.  Why should `7 + 5` be the same as `3 + 9`?  We might want
to gather more evidence, testing the proposition by choosing other
numbers.  But—since there are an infinite number of
naturals—testing can never be complete.  Is there any way we can be
sure that associativity holds for _all_ the natural numbers?

The answer is yes! We can prove a property holds for all naturals using
_proof by induction_.

## Proof by induction

Recall the definition of natural numbers consists of a _base case_
which tells us that `zero` is a natural, and an _inductive case_
which tells us that if `m` is a natural then `suc m` is also a natural.

Proof by induction follows the structure of this definition.  To prove
a property of natural numbers by induction, we need to prove two cases.
First is the _base case_, where we show the property holds for `zero`.
Second is the _inductive case_, where we assume the property holds for
an arbitrary natural `m` (we call this the _inductive hypothesis_), and
then show that the property must also hold for `suc m`.

If we write `P m` for a property of `m`, then what we need to
demonstrate are the following two inference rules:

    ------
    P zero

    P m
    ---------
    P (suc m)

Let's unpack these rules.  The first rule is the base case, and
requires we show that property `P` holds for `zero`.  The second rule
is the inductive case, and requires we show that if we assume the
inductive hypothesis — namely that `P` holds for `m` — then it follows
that `P` also holds for `suc m`.

Why does this work?  Again, it can be explained by a creation story.
To start with, we know no properties:

    -- In the beginning, no properties are known.

Now, we apply the two rules to all the properties we know about.  The
base case tells us that `P zero` holds, so we add it to the set of
known properties.  The inductive case tells us that if `P m` holds (on
the day before today) then `P (suc m)` also holds (today).  We didn't
know about any properties before today, so the inductive case doesn't
apply:

    -- On the first day, one property is known.
    P zero

Then we repeat the process, so on the next day we know about all the
properties from the day before, plus any properties added by the rules.
The base case tells us that `P zero` holds, but we already
knew that. But now the inductive case tells us that since `P zero`
held yesterday, then `P (suc zero)` holds today:

    -- On the second day, two properties are known.
    P zero
    P (suc zero)

And we repeat the process again. Now the inductive case
tells us that since `P zero` and `P (suc zero)` both hold, then
`P (suc zero)` and `P (suc (suc zero))` also hold. We already knew about
the first of these, but the second is new:

    -- On the third day, three properties are known.
    P zero
    P (suc zero)
    P (suc (suc zero))

You've got the hang of it by now:

    -- On the fourth day, four properties are known.
    P zero
    P (suc zero)
    P (suc (suc zero))
    P (suc (suc (suc zero)))

The process continues.  On the _n_'th day there will be _n_ distinct
properties that hold.  The property of every natural number will appear
on some given day.  In particular, the property `P n` first appears on
day _n+1_.


## Our first proof: associativity

To prove associativity, we take `P m` to be the property:

    (m + n) + p ≡ m + (n + p)

Here `n` and `p` are arbitrary natural numbers, so if we can show the
equation holds for all `m` it will also hold for all `n` and `p`.
The appropriate instances of the inference rules are:

    -------------------------------
    (zero + n) + p ≡ zero + (n + p)

    (m + n) + p ≡ m + (n + p)
    ---------------------------------
    (suc m + n) + p ≡ suc m + (n + p)

If we can demonstrate both of these, then associativity of addition
follows by induction.

Here is the proposition's statement and proof:
```
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎
```
We have named the proof `+-assoc`.  In Agda, identifiers can consist of
any sequence of characters not including spaces or the characters `@.(){};_`.

Let's unpack this code.  The signature states that we are
defining the identifier `+-assoc` which provides evidence for the
proposition:

    ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

The upside down A is pronounced "for all", and the proposition
asserts that for all natural numbers `m`, `n`, and `p`
the equation `(m + n) + p ≡ m + (n + p)` holds.  Evidence for the
proposition is a function that accepts three natural numbers, binds
them to `m`, `n`, and `p`, and returns evidence for the corresponding
instance of the equation.

For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

    n + p ≡ n + p

This holds trivially.  Reading the chain of equations in the base case
of the proof, the top and bottom of the chain match the two sides of
the equation to be shown, and reading down from the top and up from
the bottom takes us to `n + p` in the middle.  No justification other
than simplification is required.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the
equation:

    suc ((m + n) + p) ≡ suc (m + (n + p))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    (m + n) + p ≡ m + (n + p)

Reading the chain of equations in the inductive case of the proof, the
top and bottom of the chain match the two sides of the equation to be
shown, and reading down from the top and up from the bottom takes us
to the simplified equation above. The remaining equation, does not follow
from simplification alone, so we use an additional operator for chain
reasoning, `_≡⟨_⟩_`, where a justification for the equation appears
within angle brackets.  The justification given is:

    ⟨ cong suc (+-assoc m n p) ⟩

Here, the recursive invocation `+-assoc m n p` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.

A relation is said to be a _congruence_ for a given function if it is
preserved by applying that function.  If `e` is evidence that `x ≡ y`,
then `cong f e` is evidence that `f x ≡ f y`, for any function `f`.

Here the inductive hypothesis is not assumed, but instead proved by a
recursive invocation of the function we are defining, `+-assoc m n p`.
As with addition, this is well founded because associativity of
larger numbers is proved in terms of associativity of smaller numbers.
In this case, `assoc (suc m) n p` is proved using `assoc m n p`.
The correspondence between proof by induction and definition by
recursion is one of the most appealing aspects of Agda.

## Induction as recursion

As a concrete example of how induction corresponds to recursion, here
is the computation that occurs when instantiating `m` to `2` in the
proof of associativity.

```
+-assoc-2 : ∀ (n p : ℕ) → (2 + n) + p ≡ 2 + (n + p)
+-assoc-2 n p =
  begin
    (2 + n) + p
  ≡⟨⟩
    suc (1 + n) + p
  ≡⟨⟩
    suc ((1 + n) + p)
  ≡⟨ cong suc (+-assoc-1 n p) ⟩
    suc (1 + (n + p))
  ≡⟨⟩
    2 + (n + p)
  ∎
  where
  +-assoc-1 : ∀ (n p : ℕ) → (1 + n) + p ≡ 1 + (n + p)
  +-assoc-1 n p =
    begin
      (1 + n) + p
    ≡⟨⟩
      suc (0 + n) + p
    ≡⟨⟩
      suc ((0 + n) + p)
    ≡⟨ cong suc (+-assoc-0 n p) ⟩
      suc (0 + (n + p))
    ≡⟨⟩
      1 + (n + p)
    ∎
    where
    +-assoc-0 : ∀ (n p : ℕ) → (0 + n) + p ≡ 0 + (n + p)
    +-assoc-0 n p =
      begin
        (0 + n) + p
      ≡⟨⟩
        n + p
      ≡⟨⟩
        0 + (n + p)
      ∎
```

## Terminology and notation

The symbol `∀` appears in the statement of associativity to indicate that
it holds for all numbers `m`, `n`, and `p`.  We refer to `∀` as the _universal
quantifier_, and it is discussed further in the [Quantifiers]({{ site.baseurl }}/Quantifiers/) section.

Evidence for a universal quantifier is a function.  The notations

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

and

    +-assoc : ∀ (m : ℕ) → ∀ (n : ℕ) → ∀ (p : ℕ) → (m + n) + p ≡ m + (n + p)

are equivalent. They differ from a function type such as `ℕ → ℕ → ℕ`
in that variables are associated with each argument type, and the
result type may mention (or depend upon) these variables; hence they
are called _dependent functions_.

## Our second proof: commutativity

Another important property of addition is that it is _commutative_, that is,
that the order of the operands does not matter:

    m + n ≡ n + m

The proof requires that we first demonstrate two lemmas.

### The first lemma

The base case of the definition of addition states that zero
is a left-identity:

    zero + n ≡ n

Our first lemma states that zero is also a right-identity:

    m + zero ≡ m

Here is the lemma's statement and proof:
```
+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎
```
The signature states that we are defining the identifier `+-identityʳ` which
provides evidence for the proposition:

    ∀ (m : ℕ) → m + zero ≡ m

Evidence for the proposition is a function that accepts a natural
number, binds it to `m`, and returns evidence for the corresponding
instance of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + zero ≡ zero

Simplifying with the base case of addition, this is straightforward.

For the inductive case, we must show:

    (suc m) + zero = suc m

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + zero) = suc m

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + zero ≡ m

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation above.  The remaining
equation has the justification:

    ⟨ cong suc (+-identityʳ m) ⟩

Here, the recursive invocation `+-identityʳ m` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the first lemma.

### The second lemma

The inductive case of the definition of addition pushes `suc` on the
first argument to the outside:

    suc m + n ≡ suc (m + n)

Our second lemma does the same for `suc` on the second argument:

    m + suc n ≡ suc (m + n)

Here is the lemma's statement and proof:
```
+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎
```
The signature states that we are defining the identifier `+-suc` which provides
evidence for the proposition:

    ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

Evidence for the proposition is a function that accepts two natural numbers,
binds them to `m` and `n`, and returns evidence for the corresponding instance
of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + suc n ≡ suc (zero + n)

Simplifying with the base case of addition, this is straightforward.

For the inductive case, we must show:

    suc m + suc n ≡ suc (suc m + n)

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + suc n) ≡ suc (suc (m + n))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + suc n ≡ suc (m + n)

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation in the middle.  The remaining
equation has the justification:

    ⟨ cong suc (+-suc m n) ⟩

Here, the recursive invocation `+-suc m n` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the second lemma.

### The proposition

Finally, here is our proposition's statement and proof:

```
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎
```

The first line states that we are defining the identifier
`+-comm` which provides evidence for the proposition:

    ∀ (m n : ℕ) → m + n ≡ n + m

Evidence for the proposition is a function that accepts two
natural numbers, binds them to `m` and `n`, and returns evidence for the
corresponding instance of the equation.  The proof is by
induction on `n`.  (Not on `m` this time!)

For the base case, we must show:

    m + zero ≡ zero + m

Simplifying both sides with the base case of addition yields the equation:

    m + zero ≡ m

The remaining equation has the justification `⟨ +-identityʳ m ⟩`,
which invokes the first lemma.

For the inductive case, we must show:

    m + suc n ≡ suc n + m

Simplifying both sides with the inductive case of addition yields the equation:

    m + suc n ≡ suc (n + m)

We show this in two steps.  First, we have:

    m + suc n ≡ suc (m + n)

which is justified by the second lemma, `⟨ +-suc m n ⟩`.  Then we
have

    suc (m + n) ≡ suc (n + m)

which is justified by congruence and the induction hypothesis,
`⟨ cong suc (+-comm m n) ⟩`.  This completes the proof.

Agda requires that identifiers are defined before they are used,
so we must present the lemmas before the main proposition, as we
have done above.  In practice, one will often attempt to prove
the main proposition first, and the equations required to do so
will suggest what lemmas to prove.


## Our first corollary: rearranging {#sections}

We can apply associativity to rearrange parentheses however we like.
Here is an example:
```
+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎
```
No induction is required, we simply apply associativity twice.
A few points are worthy of note.

First, addition associates to the left, so `m + (n + p) + q`
stands for `(m + (n + p)) + q`.

Second, we use `sym` to interchange the sides of an equation.
Proposition `+-assoc n p q` shifts parentheses from right to left:

    (n + p) + q ≡ n + (p + q)

To shift them the other way, we use `sym (+-assoc n p q)`:

    n + (p + q) ≡ (n + p) + q

In general, if `e` provides evidence for `x ≡ y` then `sym e` provides
evidence for `y ≡ x`.

Third, Agda supports a variant of the _section_ notation introduced by
Richard Bird.  We write `(x +_)` for the function that applied to `y`
returns `x + y`.  Thus, applying the congruence `cong (m +_)` takes
the above equation into:

    m + (n + (p + q)) ≡ m + ((n + p) + q)

Similarly, we write `(_+ x)` for the function that applied to `y`
returns `y + x`; the same works for any infix operator.

#### Exercise `trySectioning` (starting) {#trySectioning}

Interact with Agda via Emacs to make sure you understand:

 - The difference between `(_∸_ 3)` and `(_∸ 3)`

 - The difference between `(_∸ 3)` and `(3 ∸_)`

Hint: We use `∸` rather than `+` in this exercise because `+` is
commutative, while `∸` is not.

### Getting used to errors {#errorExers}

In Agda as in all other programming languages, understanding error
messages is an essential skill.  The error messages arising from
proofs can be particularly hard to understand: the errors are often
subtle.  Moreover, when two parts of your proofs do not match up, it
can be difficult for Agda to work out which one is "right," so the
error messages are often very general.  The next few exercises will
lead you to break the proof of associativity in different ways, to see
how Agda reacts in different situations.

All of the code in this section is commented out — of course, since it
is intentionally broken!  Add the triple-ticks to code blocks one at a
time to allow Agda to raise they errors they exhibit.

For example, one of the key equations of the inductive case of
`+-comm` is

      suc (m + n)
    ≡⟨ cong suc (+-comm m n) ⟩
      suc (n + m)

If we forget to include the reason at all, it means that we are
telling Agda that the two sides of that equation can be demonstrated
just by rewriting according to the rules defined in function clauses.
But this isn't true — there are no instances of `zero + M` or
`(suc M) + N` in those terms.
If we were to use `≡⟨⟩` to link those two expressions,

    +-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
    +-comm' m zero =
      begin
        m + zero
      ≡⟨ +-identityʳ m ⟩
        m
      ≡⟨⟩
        zero + m
      ∎
    +-comm' m (suc n) =
      begin
        m + suc n
      ≡⟨ +-suc m n ⟩
        suc (m + n)
      ≡⟨⟩                --  <-- This reason dropped
        suc (n + m)
      ≡⟨⟩
        suc n + m
      ∎

Agda would raise an error,

    n != m of type ℕ
    when checking that the inferred type of an application
      suc (n + m) ≡ _y_312
    matches the expected type
      suc (m + n) ≡ suc n + m

and Emacs would highlight the last four lines in red,

      suc (n + m)
    ≡⟨⟩
      suc n + m
    ∎

The error is about the type that Agda attributes to that expression.
The type that Agda works out for the expression is not same as the
type that it needs for the place where it found the expression.  A
smaller example of this mismatch would be the incorrect expression

    3 + "what"

Agda works out that type of `"what"` is `String`, but that the type of
an expression in the context `3 + ...` is `Nat`.  In `+-comm'`, Agda
can tell from the signature and from the first lines of `+-comm'`

    +-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
    +-comm' m zero =
      begin
        m + zero
      ≡⟨ +-identityʳ m ⟩
        m
      ≡⟨⟩
        zero + m
      ∎
    +-comm' m (suc n) =
      begin
        m + suc n
      ≡⟨ +-suc m n ⟩
        suc (m + n)
      ≡⟨⟩
        ....

That it needs an expression of type

    suc (m + n) ≡ n + suc m

This is what the last two lines of the message tell us.  What does
Agda find that we put in this place?  In typing the expression

      suc (n + m)
    ≡⟨⟩
      suc n + m
    ∎

Agda finds that it has a `≡`-type, and that its left subexpression is
`suc (n + m)`.  This much is enough for Agda to raise the error: the
left subexpression of the type it needs is `suc (m + n)` — the
variables `m` and `n` are reversed.  Agda stops there, and reports the
error.  This is why we see the name `_y_312` in the error message:
that name is a marker that Agda would fill out later.

When we see this mismatch, it tells us that some part of the
transition

      suc (m + n)
    ≡⟨⟩
      suc (n + m)

is lacking.  But Agda cannot predict what we want: it could be that
the problem is part of the first expression `suc (m + n)`, part of the
evidence `refl` implied by `≡⟨⟩`, or part of the second expression
`suc (n + m)`.  It is up to us, as the author of the proof, to work
out which of these three we need to correct.

#### Exercise `ProofErr1` (starting) {#proofErr1}

Use Agda to find the error in this proof:

    +-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc' zero n p =
      begin
        (zero + n) + p
      ≡⟨⟩
        n + p
      ≡⟨⟩
        zero + (n + p)
      ∎
    +-assoc' (suc m) n p =
      begin
        (suc m + n) + p
      ≡⟨⟩
        suc (m + n) + p
      ≡⟨⟩
        suc ((m + n) + p)
      ≡⟨ +-assoc' m n p ⟩
        suc (m + (n + p))
      ≡⟨⟩
        suc m + (n + p)
      ∎

Agda is able to identify a much smaller suspected error in this
case. because a justification cannot fit with the expression before
it.  What type does a call to `+-assoc' X Y Z` return, assuming that
`X`, `Y` and `Z` are all of type `ℕ`?  What type does
`suc ((m + n) + p) ≡ X` have?
Why do they not match, no matter what `X` is?

#### Exercise `ProofErr2` (starting) {#proofErr2}

Use Emacs to find the error in this Agda proof:

    +-comm″ : ∀ (m n : ℕ) → m + n ≡ n + m
    +-comm″ m zero =
      begin
        m + zero
      ≡⟨ +-identityʳ m ⟩
        m
      ≡⟨⟩
        zero + m
      ∎
    +-comm″ m (suc n) =
      begin
        m + suc n
      ≡⟨ +-suc m n ⟩
        suc (m + n)
      ≡⟨ cong suc (+-comm″ m n) ⟩
        suc (m + n)
      ≡⟨⟩
        suc n + m
      ∎

What expression does Agda highlight as the source of the error?  What
type does it expect for the expression, and wha does it find?

{::options parse_block_html="true" /}
<div style="background-color: #fffff0; padding: 1em 1.5em 0.5em; margin-bottom: 1em">

### Debugging tip: fix a smaller chain of qualities {#debugsmall}

Let's say that you want to prove that M1 ≡ Mn, and that you have
written a long proof

    begin
      M1
    ≡⟨⟩
      M2
    ≡⟨⟩
      ...
    ≡⟨⟩
      M{n-1}
    ≡⟨⟩
      Mn
    ∎

but you have an error and are not sure where it is. (Some of the ≡⟨⟩'s
could be ≡⟨ evidence ⟩'s — this tip applies either way either way)
It's always a good idea to choose to debug less at a time instead of
more, to get one part compiling before moving on to the next.  But how
do you pare down a block like this one?

You can't really pare it down if you are rushing to prove all of M1 ≡
Mn at once — but you can instead try to prove that M1 is equal to
something earlier in the chain. You could try first

    _ : M1 ≡ M2
    _ = begin
          M1
        ≡⟨⟩
          M2
        ∎

Note that we are not simply chopping off the bottom of the proof!  We
have also changed what we are saying that M1 is equal to: M2 instead
of Mn.

Does this first step of the proof work? if not, you now have a much
smaller thing to debug, with less to distract you from the error. If
so, then you can move on to M3,

    _ : M1 ≡ M3
    _ = begin
          M1
        ≡⟨⟩
          M2
        ≡⟨⟩
          M3
        ∎

And so one, until you work out all the bugs on the way to Mn — or
decide to reconsider your original idea for how to get to Mn.  Debug
one step at a time, verifying that each step in the chain works,
before moving on to the next step.

</div>


## Creation, one last time

Returning to the proof of associativity, it may be helpful to view the inductive
proof (or, equivalently, the recursive definition) as a creation story.  This
time we are concerned with judgments asserting associativity:

     -- In the beginning, we know nothing about associativity.

Now, we apply the rules to all the judgments we know about.  The base
case tells us that `(zero + n) + p ≡ zero + (n + p)` for every natural
`n` and `p`.  The inductive case tells us that if 
`(m + n) + p ≡ m + (n + p)` (on the day before today) then
`(suc m + n) + p ≡ suc m + (n + p)` (today).
We didn't know any judgments about associativity before today, so that
rule doesn't give us any new judgments:

    -- On the first day, we know about associativity of 0.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...

Then we repeat the process, so on the next day we know about all the
judgments from the day before, plus any judgments added by the rules.
The base case tells us nothing new, but now the inductive case adds
more judgments:

    -- On the second day, we know about associativity of 0 and 1.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...

And we repeat the process again:

    -- On the third day, we know about associativity of 0, 1, and 2.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...

You've got the hang of it by now:

    -- On the fourth day, we know about associativity of 0, 1, 2, and 3.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...
    (3 + 0) + 0 ≡ 3 + (0 + 0)   ...   (3 + 4) + 5 ≡ 3 + (4 + 5)   ...

The process continues.  On the _m_'th day we will know all the
judgments where the first number is less than _m_.

There is also a completely finite approach to generating the same equations,
which is left as an exercise for the reader.

#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the
first four days using a finite story of creation, as
[earlier]({{ site.baseurl }}/Naturals/#finite-creation).

```
-- Your code goes here
```

## Associativity with rewrite

There is more than one way to skin a cat.  Here is a second proof of
associativity of addition in Agda, using `rewrite` rather than chains of
equations:
```
+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl
```

For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

    n + p ≡ n + p

This holds trivially. The proof that a term is equal to itself is written `refl`.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the equation:

    suc ((m + n) + p) ≡ suc (m + (n + p))

After rewriting with the inductive hypothesis these two terms are equal, and the
proof is again given by `refl`.  Rewriting by a given equation is indicated by
the keyword `rewrite` followed by a proof of that equation.  Rewriting avoids
not only chains of equations but also the need to invoke `cong`.


## Commutativity with rewrite

Here is a second proof of commutativity of addition, using `rewrite` rather than
chains of equations:
```
+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl
```
In the final line, rewriting with two equations is
indicated by separating the two proofs of the relevant equations by a
vertical bar; the rewrite on the left is performed before that on the
right.


## Building proofs interactively

It is instructive to see how to build the alternative proof of
associativity using the interactive features of Agda in Emacs.
Begin by typing:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = ?

The question mark indicates that you would like Agda to help with
filling in that part of the code.  If you type `C-c C-l` (control-c
followed by control-l), the question mark will be replaced:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = { }0

The empty braces are called a _hole_, and 0 is a number used for
referring to the hole.  The hole may display highlighted in green.
Emacs will also create a new window at the bottom of the screen
displaying the text:

    ?0 : ((m + n) + p) ≡ (m + (n + p))

This indicates that hole 0 is to be filled in with a proof of
the stated judgment.

We wish to prove the proposition by induction on `m`.  Move
the cursor into the hole and type `C-c C-c`.  You will be given
the prompt:

    pattern variables to case (empty for split on result):

Typing `m` will cause a split on that variable, resulting
in an update to the code:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = { }0
    +-assoc′ (suc m) n p = { }1

There are now two holes, and the window at the bottom tells you what
each is required to prove:

    ?0 : ((zero + n) + p) ≡ (zero + (n + p))
    ?1 : ((suc m + n) + p) ≡ (suc m + (n + p))

Going into hole 0 and typing `C-c C-,` will display the text:

    Goal: (n + p) ≡ (n + p)
    ------------------------------------------------------------
    p : ℕ
    n : ℕ

This indicates that after simplification the goal for hole 0 is as
stated, and that variables `p` and `n` of the stated types are
available to use in the proof.  The proof of the given goal is
trivial, and going into the goal and typing `C-c C-r` will fill it in.
Typing `C-c C-l` renumbers the remaining hole to 0:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p = { }0

Going into the new hole 0 and typing `C-c C-,` will display the text:

    Goal: suc ((m + n) + p) ≡ suc (m + (n + p))
    ------------------------------------------------------------
    p : ℕ
    n : ℕ
    m : ℕ

Again, this gives the simplified goal and the available variables.
In this case, we need to rewrite by the induction
hypothesis, so let's edit the text accordingly:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = { }0

Going into the remaining hole and typing `C-c C-,` will display the text:

    Goal: suc (m + (n + p)) ≡ suc (m + (n + p))
    ------------------------------------------------------------
    p : ℕ
    n : ℕ
    m : ℕ

The proof of the given goal is trivial, and going into the goal and
typing `C-c C-r` will fill it in, completing the proof:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

Sometimes, we need to type in a more complicated expression than just
`refl`.  We can type the expression inside the hole, and ask Agda to
typecheck it for us with `C-c C-SPACE`.  If the expression inside the
hole fits the type needed for the context of that hole, then Agda will
replace the hole with the text we have placed inside it, and we can
move on to the next hole.  There is a
[Quick Guide](https://agda.readthedocs.io/en/v2.5.4/getting-started/quick-guide.html)
to Agda mode with a summary of Emacs key bindings in the online
Agda documentation.


{::options parse_block_html="true" /}
<div style="background-color: #fffff0; padding: 1em 1.5em 0.5em; margin-bottom: 1em">

### General hint: aim for the induction hypothesis {#useTheIH}

As a general rule, the key step in the inductive case of a proof is
the use of the induction hypothesis.  In `+-assoc`, the induction
hypothesis was the _only_ step that was not rewriting according to
`refl` (via `≡⟨⟩`).  In `+-comm`, we used another lemma `+-suc`, but
this lemma served only to set up the use of the induction hypothesis.

Sometimes, if we should use the inductive hypothesis but instead try
to rely on outside lemmas only, we may find that we embark on a long
series of linked results, each one requiring the next, and maybe
seeming circular.  This situation is often a sign that we should go
back to the original proof, and look for a way to use the induction
hypothesis.

Again, this strategy is a _general_ rule for inductive proofs, not an
ironclad absolute for all proofs.  Below we will see some proofs which
require a case analysis but _not_ induction — it happens!  But these
instances tend not to be simpler.  When your search for a proof
instead seems to go down a rabbit hole of more and more complicated
lemmas, each depending on the next, one strategy is to re-focus on
finding the inductive case in the original result.

</div>


#### Exercise `+-swap` (recommended) {#plus-swap}

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.

```
-- Your code goes here
```


#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

```
-- Your code goes here
```


#### Exercise `*-assoc` (recommended) {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

```
-- Your code goes here
```


#### Exercise `*-comm` (practice) {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

```
-- Your code goes here
```


#### Exercise `0∸n≡0` (practice) {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

```
-- Your code goes here
```


#### Exercise `n∸n≡0` (practice) {#n-monus-n}

Show

    n ∸ n ≡ zero

for all naturals `n`.

```
postulate n∸n≡0 : ∀ (n : ℕ) → n ∸ n ≡ zero
-- Remove the keyword postulate, and fill in your proof here
```

This exercise is written a little differently than the other
exercises.  The `postulate` keyword allows us to use this lemma in
later sections, even if you are not able to complete all of the
exercises, or complete them in a different file.  When you work the
exercises, be sure to remove the `postulate` keyword when you add your
proof.


#### Exercise `∸-+-assoc` (practice) {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

```
-- Your code goes here
```

#### Exercise `double-+` (practice) {#double-plus}

Consider the following function, which doubles its argument:

```
double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))
```

Show that `double` is the same as adding a number to itself,

    double n ≡ n + n


#### Exercise `even-suc` (practice) {#even-suc}

Recall the `even` predicate from the
[Naturals]({{ site.baseurl }}/Naturals/) section:

```
open import Data.Bool
even : ℕ → Bool
even zero = true
even (suc zero) = false
even (suc (suc n)) = even n
```

Show how the result of `even` on any number is related to the result
of `even` on the successor of that number,

    even (suc n) ≡ not (even n)
    

#### Exercise `+*^` (stretch)

Show the following three laws

     m ^ (n + p) ≡ (m ^ n) * (m ^ p)  (^-distribˡ-+-*)
     (m * n) ^ p ≡ (m ^ p) * (n ^ p)  (^-distribʳ-*)
     (m ^ n) ^ p ≡ m ^ (n * p)        (^-*-assoc)

for all `m`, `n`, and `p`.

#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that
Exercise [Bin]({{ site.baseurl }}/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `b`
over bitstrings:

    from (inc b) ≡ suc (from b)
    to (from b) ≡ b
    from (to n) ≡ n

For each law: if it holds, prove; if not, give a counterexample.

```
-- Your code goes here
```

#### Exercise `plusIdExercise` (starting) {#plusIdExercise}

Prove the following statement:

    plusIdExercise : ∀ (n m o : ℕ) → n ≡ m → m ≡ o → n + m ≡ m + o
    -- Your code goes here

#### Exercise `multN1` (recommended) {#multN1}

Prove the following statement:

    multN1 : ∀ (p : ℕ) → p * 1 ≡ p
    -- Your code goes here

Remember that 1 is just `suc zero`.

### Additional exercises

These exercises may require any of the techniques in this section.

```
open import Data.Nat using (_≡ᵇ_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
```

#### Exercise `∧-comm` (starting) {#and-comm}

Prove that:

    ∧-comm : ∀ (b c : Bool) → b ∧ c ≡ c ∧ b
    -- Your code goes here

#### Exercise `notInvolutive` (recommended) {#notInvolutive}

Prove that:

    notInvolutive : ∀ (b : Bool) → not (not b) ≡ b
    -- Your code goes here

#### Exercise `mult0` (recommended) {#mult0}

Prove the following statement:

    mult0 : ∀ (n : ℕ) → n * 0 = 0
    -- Your code goes here

#### Exercise `plus1neq0` (recommended) {#plus1neq0}

Prove the following statement:

    plus1neq0 : ∀ (n : ℕ) → (n + 1 ≡ᵇ 0) ≡ false
    -- Your code goes here

You have at least two ways to prove this result.  Try to solve it both
with and without using earlier arithmetic theorems for rewriting.

#### Exercise `zeroNeq+1` (recommended) {#zeroNeqPlus1}

Prove the following statement:

    zeroNeq+1 : ∀ (n : ℕ) → (0 ≡ᵇ n + 1) ≡ false
    -- Your code goes here

#### Exercise `∧-true-elim` (practice) {#and-true-elim}

Prove the following statement:

    ∧-true-elim : ∀ (b c : Bool) → b ∧ c ≡ true → c ≡ true
    -- Your code goes here

#### Exercise `boolIdTwice` (practice) {#boolIdTwice}

Prove that:

    boolIdTwice : ∀ (f : Bool → Bool) →
                    (∀ (x : Bool) → f x ≡ x) →
                      ∀ (b : Bool) →
                        f (f b) ≡ b
    -- Your code goes here

Be very mindful of the parentheses in this and the next exercise.

#### Exercise `boolNotTwice` (practice) {#boolNotTwice}

Prove that:

    boolNotTwice : ∀ (f : Bool → Bool) →
                     (∀ (x : Bool) → f x ≡ not x) →
                       ∀ (b : Bool) →
                         f (f b) ≡ b
    -- Your code goes here

#### Exercise `∧≡∨` (practice) {#and-eq-or}

    ∧≡∨ : ∀ (b c : Bool) → (b ∧ c ≡ b ∨ c) → b ≡ c.
    -- Your code goes here

#### Exercise `suc-n+m` (practice) {#sucMinusNPlusM}

    suc-n+m : ∀ (n m : ℕ) → suc (n + m) ≡ n + suc m
    -- Your code goes here

#### Exercise `≡ᵇtrue` (practice) {#eqb-true}

    ≡ᵇtrue : ∀ (n : ℕ) → true ≡ (n ≡ᵇ n)
    -- Your code goes here

## Standard library

Definitions similar to those in this section can be found in the standard library:
```
import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
```

## Unicode

This section uses the following Unicode symbols:

    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    λ   U+03BB  GREEK SMALL LETTER LAMDA  (\Gl, \lambda)
    ᵇ  U+1D47  MODIFIER LETTER SMALL B (\^b)
    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\'')
    ‴  U+2034  TRIPLE PRIME (\'3)
    ⁗  U+2057  QUADRUPLE PRIME (\'4)
    ℕ  U+2115  DOUBLE-STRUCK CAPITAL N (\bN)
    →  U+2192  RIGHTWARDS ARROW (\to, \r, \->)
    ∀  U+2200  FOR ALL (\forall, \all)
    ∧  U_2227  LOCIGAL AND (\and)
    ∨  U+2228  LOGICAL OR (\or)
    ∸  U+2238  DOT MINUS (\.-)
    ≡  U+2261  IDENTICAL TO (\==)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)

Similar to `\r`, the command `\^r` gives access to a variety of
superscript rightward arrows, and also a superscript letter `r`.
The command `\'` gives access to a range of primes (`′ ″ ‴ ⁗`).

---

*This page is derived from Wadler et al., with some additional text by
Maraist.  Exercises `double-+` and `even-suc`, and the last two
sections and their exercises, are adapted from Pierce et al.  For more
information see the [sources and authorship]({{ site.baseurl
}}/Sources/) page.*
