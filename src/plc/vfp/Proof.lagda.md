---
title     : "Proof: Constructing evidence for formulas"
layout    : page
prev      : /Depend/
permalink : /Proof/
next      : /Induction/
---

```
module plc.vfp.Proof where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Bool
open import Data.Nat
```

In the last chapter we studied the basics of programming in a language
like Agda.  Now, our next step is to learn how to use Agda to discuss
— that is, to prove — properties of Agda programs.  By the end of this
chapter we will be stating and proving a variety of properties about
numbers, functions, and data structures.  We begin by generalizing the
unit tests which accompanied the examples and exercises of the
previous chapter.

### From unit tests to general statements

You have seen many situations where we have used `begin⋯≡⟨⟩⋯∎` blocks
to build tests for the functions we write.

```
module PropertiesWithNatData where
  open import plc.fp.NatData

  _ : 2 + 3 ≡ 5
  _ = begin
        2 + 3
      ≡⟨⟩
        5
      ∎

  _ : fst (swapPair (pair 5 (6 + 3))) ≡ 9
  _ = refl
```

We have also used `begin⋯≡⟨⟩⋯∎` blocks to spell out the individual
steps of evaluating an expression, to help us make sure that we
understand how the evaluation works.

```
  _ : fst (swapPair (pair 5 (6 + 3))) ≡ 9
  _ = begin
        fst (swapPair (pair 5 (6 + 3)))
      ≡⟨⟩
        fst (swapPair (pair 5 9))
      ≡⟨⟩
        fst (pair 9 5)
      ≡⟨⟩
        9
      ∎
```      

These examples are called _unit tests_ because they verify that
specific units of our program work as expected in some particular
case.  In the last of the examples above, the units we test are the
`fst`, `swapPair` and `pair` functions.  Unit tests are useful for
many reasons: as we develop our programs, they help us to be confident
that our work is correct.  When we run our tests later, as part of a
_regression test_ suite, they help us know that new developments in
our code has not broken older work.

But there is a limit to unit tests: they cannot give us certainty that
our code works in _all_ cases.  If we have _N_ tests, then we have
certainty about _N_ cases.  We may be confident that the other cases
work, but we have no direct evidence for it.

We have already seen Agda's mechanism for writing a formula that
describes correct behavior in all cases: universal quantification with
a `∀`-prefix.  Consider these unit tests:

```
  _ : fst (swapPair (pair 5 10)) ≡ 10
  _ = refl

  _ : fst (swapPair (pair 4 0)) ≡ 0
  _ = refl

  _ : fst (swapPair (pair 3 20)) ≡ 20
  _ = refl
```

The property these tests aim to verify is that if we build a pair from
`x` and `y`, swap the pair around, and extract the first element, then
we will retrieve the second element `y` of the original pair.  This
should be true for _any_ numbers `x` and `y`.  So instead of writing
unit test after unit test to raise our confidence in the general
result, we can state a general result to cover _all_ cases:

```
  swapThenFstNatPair : ∀ (m n : ℕ) → fst (swapPair (pair m n)) ≡ n
```

We can use `begin⋯≡⟨⟩⋯∎` blocks here, with the unbound parameters `x`
and `y`, just as we did in the earlier examples with concrete values.

```
  swapThenFstNatPair m n = begin
                             fst (swapPair (pair m n))
                           ≡⟨⟩    -- First step
                             fst (pair n m)
                           ≡⟨⟩    -- Second step
                             n
                           ∎
```

The first step uses the definition of `swapPair`,

    swapPair (pair x y) = pair y x

We write `=` and not `≡` because we are quoting the clause which is
part of how we defined `swapPair` to Agda: we use `=` with function
definitions, and `≡` in formulas.  The second step uses the definition
of `fst`,

    fst (pair x y) = x

We could also give the result in one step, since `≡⟨⟩` can refer to
multiple rewritings,

```
  swapThenFstNatPair′ : ∀ (m n : ℕ) → fst (swapPair (pair m n)) ≡ n
  swapThenFstNatPair′ m n = begin
                             fst (swapPair (pair m n))
                           ≡⟨⟩
                             n
                           ∎
```

Or, we could just use `refl` as the evidence we give for the formula.
The `⋯ ≡⟨⟩ ⋯` steps are simply a nice wrapper for referring to the
reflexive property of equality, in a context where Agda will apply
whatever rewrite rules are needed to each side of the equality.

```
  swapThenFstNatPair″ : ∀ (m n : ℕ) → fst (swapPair (pair m n)) ≡ n
  swapThenFstNatPair″ m n = refl
```

#### Exercise `≡ByRules` (starting) {#equal-by-rules}

All of these formulas can be justified with `refl`.  Set each one up
as a quantified formula in valid Agda declarations.  Use the given
name for each one.

 - `0 + n ≡ n`  (name the result `zeroPlusN`)
 - `2 + n ≡ suc (suc n)`  (name the result `twoPlusN`)
 - `x ∸ zero ≡ x`  (name the result `monusZero`)
 - `isEven (suc (suc p)) ≡ isEven p`  (name the result `secondSucSameIsEven`)

### Rewriting with premises

The following theorem does not require induction, but does require us
to use its premises as we show two values as equal

```
  plusIdExample : ∀ (n m : ℕ) → n ≡ m → n + n ≡ m + m
```

Instead of making a universal claim about all numbers `n` and `m`, it
talks about a more specialized property that only holds when `n ≡ m`.
In this case we pronounce the second arrow "implies."  Or, we can read
this formula as an if-then statement: if `n` and `m` are equal, then
`n + n` and `m + m` are also equal.

We start the proof in a way consistent with what we have before: both
quantified values and the premise of the implication correspond to
arguments.

```
  plusIdExample n m n≡m = 
```

Remember that in Agda, almost all characters can be part of a name,
including symbols like `≡`.  So when we write `n ≡ m` in the
signature, Agda sees three distinct items.  But when we write `n≡m` in
this clause, it is a single name with three characters.  The value
which we expect for this parameter is evidence that `n ≡ m`, and we
will use this evidence in our proof.

We are showing that two values are equal, and we use the familiar tool
of the `begin⋯∎` block to do so.  Our evidence will have this form:

    begin
      n + n
    
    
      m + m
    ∎

But the content is the middle is trickier than what we have
encountered so far.  Since n and m are arbitrary numbers, we cannot
just use simplification according to definitions to prove this
theorem.  Instead, we will need to apply this evidence that `m ≡ n` in
our proof.  We have an alternate form of `≡⟨⟩` for these cases, which
use evidence of the form `A ≡ B` to rewrite an occurrence of `A` as
`B`.

If the rewriting is at the top level of the term — that is, if it is
`A` which we are showing equal to something rather than some term
properly containing `A` — then the evidence is fine just as it is.
Otherwise we use a function to wrap the term linked by the the
evidence.  Here we would begin

    begin
      n + n
    ≡⟨ cong (λ x → x + n) n≡m ⟩
      m + n

We are rewriting the first `n` as `m`.  The lambda expression tells us
where this `n`/`m` is found in the overall term `n + n`.  If we apply
the function `(λ x → x + n)` to `n`, then we have the starting term
`n + n`.  If we apply that function to `m`, then we have the term
`m + n`.  Since `n ≡ m` holds from the evidence, the lambda expression
is exactly what we need to apply to each side of the formula supported
by this evidence to advance our proof.  Then we can rewrite again with
the same evidence, but a different context, to complete the result.

```
    begin
      n + n
    ≡⟨ cong (λ x → x + n) n≡m ⟩
      m + n
    ≡⟨ cong (λ x → m + x) n≡m ⟩
      m + m
    ∎
```

Notice that we write the evidence in between the `⟨` and `⟩`.  Here,
`cong` abbreviates _congruence_, the name for the principle that lets
us reason from the equality of two terms to the equality of using the
two different terms in the same way.

Agda gives us a shorthand notation for cases such as this one, where
we have the result by simply rewriting:

```
  plusIdExample′ : ∀ (n m : ℕ) → n ≡ m → n + n ≡ m + m
  plusIdExample′ n m n≡m rewrite n≡m = refl
```

Here we are telling Agda that all we need to do to transform `n + n`
into `m + m` is to rewrite according to the evidence we call `n≡m`
until we get the result we need.  Once we finish the rewriting, we
tell Agda that the result should be clear via `refl`.  In general we
will avoid using `rewrite` in this text; although it is a powerful
tool, it often hides too many details from the beginner.

### Separating into cases

Often when we reason, we will give separate arguments for different
situations.  For example: Can Sally give Betty a ride home?

 - If it rains, then Sally will go straight home.  Betty lives halfway
   from here to Sally's, so in this case it would be possible for
   Sally to drop Betty off.

 - If it does not rain, then Sally will go from here to soccer
   practice.  Betty lives about a mile past the ball field, but Sally
   expects to have ample time between class and practice.  So in this
   case too, it would be possible for Sally to drop Betty off.

The argumentation is different in each case, but in both cases we
reach the same conclusion.

Here is an analogous example in Agda.

```
plusOneNeq0 : ∀ (n : ℕ) → ((n + 1) ≡ᵇ 0) ≡ false
```

Remember that our definition of `_+_` uses pattern matching on its
_first_ argument.  If we do not know the structure of `n` — whether it
is `zero` or the successor of some other number — then we cannot apply
either clause of the definition of `_+_` to simplify the left-hand
expression.

   plusOneNeq0 n =
     begin
       (n + 1) ≡ᵇ 0
     ≡⟨⟩
       ?

We may not know whether the structure of `n` is `zero` or the
successor of some other number, but we _do_ know that `n` will have
one of these two structures — this is given in the definition of `ℕ`,
which identifies only those two ways to construct a natural number.
So we can split the one clause

    plusOneNeq0 n = ?

into two different cases

    plusOneNeq0 zero = ?
    plusOneNeq0 (suc n) = ?

In Emacs we can do this automatically with `C-c C-c`, just as we did
when writing functions in the previous chapter.  Now that we have
additional information in each case about the constructor associated
with `n`, we _can_ use simplification by matching definition clauses.

```
plusOneNeq0 zero =
  begin
    (0 + 1) ≡ᵇ 0
  ≡⟨⟩  -- Base case of _+_
    1 ≡ᵇ 0
  ≡⟨⟩  -- Base case of _≡ᵇ_
    false
  ∎
plusOneNeq0 (suc n) =
  begin
    ((suc n) + 1) ≡ᵇ 0
  ≡⟨⟩  -- Inductive case of _+_
    (suc (n + 1)) ≡ᵇ 0
  ≡⟨⟩  -- Base case of _≡ᵇ_
    false
  ∎
```

This technique is especially useful when we quantify over boolean
values, since there are only two simple possible boolean values.  Note
that in the first clause below we have written out the `begin⋯∎` block
for clarity, but it (like the right-hand side of the other clauses) is
just equivalent to `refl`.

```
∧-commutative : ∀ (b c : Bool) → b ∧ c ≡ c ∧ b
∧-commutative false false = begin false ∧ false ≡⟨⟩ false ∧ false ∎
∧-commutative false true = refl
∧-commutative true false = refl
∧-commutative true true = refl

∧3-exchange : ∀ (b c d : Bool) → (b ∧ c) ∧ d ≡ (b ∧ d) ∧ c
∧3-exchange false false false = refl
∧3-exchange false false true = refl
∧3-exchange false true false = refl
∧3-exchange false true true = refl
∧3-exchange true false false = refl
∧3-exchange true false true = refl
∧3-exchange true true false = refl
∧3-exchange true true true = refl
```

#### Exercise `∧3-exchange-shorter` (starting) {#and3-exchange-shorter}

Our implementation above for `∧3-exchange` uses more clauses than
necessary.  Use wildcard patterns `_` to simplify it as much as
possible.  You can re-order the clauses as convenient, since they are
all mutually exclusive.

#### Exercise `∧trueElim2` (starting) {#and-true-elim}

Prove the following formula:

    ∧trueElim2 : ∀ (b c : Bool) → b ∧ c ≡ true → c ≡ true
    -- Your code goes here

#### Exercise `zeroNotPlus1` (starting) {#zero-not-plus1}

Prove the following formula:

    zeroNotPlus1 : ∀ (n : ℕ) → (0 ≡ᵇ (n + 1)) ≡ false
    -- Your code goes here

## A bit of vocabulary {#vocab}

Starting with this chapter we will make use of a number of terms from
the practice of mathematics to describe the assertions of formulas
which we will make and prove.  You may not have encountered some of
these, or forgotten them since the last time you encountered them, so
it is worth a moment to refresh your memory.

 - A _theorem_ is the general name we give to the statement of a
   formula when we plan to give evidence that the formula is true.

 - When we use the word _result_ in the context of a theorem and
   proof, we usually mean the successful proof of the theorem.

 - _Lemma_ is a synonym for theorem, but it signifies a result which
   we consider to be less significant on its own.  If we have in mind
   some significant theorem, we will often first state and prove
   several lemmas, and then use those lemmas later in the proof of the
   theorem.  We choose to refer to a result as lemma or theorem to
   suggest its role in the overall story we are trying to tell.

 - A _corollary_ is a result which follows very easily from another
   theorem or lemma.  If we choose to describe a result as a
   corollary, then its proof should be a very short extension of
   simply referring to the preceding main result.

 - A _postulate_ or an _axiom_ is a formula which we will state and
   _not_ prove, but use as if it were proven anyway.  We will not
   encounter many postulates here: they are usually associated with
   the underlying mechanisms for reasoning.  We have already seen
   Agda's built-in mechanism of using simplification according to the
   definitions we give it in our code, and this mechanism is all we
   want to use for most of the situations we will model.  Later in
   this chapter, we will add a postulate which helps us to relate
   pairs of _function_ values, which do not give us constructors for
   reasoning in the way that `data` structures do.

## Unicode

This section uses the following Unicode symbols:

    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\'')
    ℕ  U+2115  DOUBLE-STRUCK CAPITAL N (\bN)
    →  U+2192  RIGHTWARDS ARROW (\to, \r, \->)
    ∀  U+2200  FOR ALL (\forall, \all)
    ∸  U+2238  DOT MINUS (\.-)
    ≡  U+2261  IDENTICAL TO (\==)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)

Similar to `\r`, the command `\^r` gives access to a variety of
superscript rightward arrows, and also a superscript letter `r`.
The command `\'` gives access to a range of primes (`′ ″ ‴ ⁗`).

---

*This page is by Maraist, with the "Separating into cases" and
"Rewriting with premises" sections derived from Pierce et al.  For
more information see the [sources and authorship]({{ site.baseurl
}}/Sources/) page.*
