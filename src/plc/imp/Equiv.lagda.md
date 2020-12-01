---
title     : "Equiv: What does it mean for two programs to be equivalent?"
layout    : page
prev      : /Imp/
permalink : /Equiv/
next      : /Hoare/
---

```
module plc.imp.Equiv where
open import Function using (case_of_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.String using (String) renaming (_==_ to _string=_)
open import Data.Nat using (ℕ; _∸_; _≡ᵇ_; _<ᵇ_; zero; suc)
open import Data.Bool using (Bool; true; false; not; _∨_; _∧_; if_then_else_)
open import plc.fp.Maps using (TotalMap; _↦_,_; ↪)
open import plc.vfp.Induction
import plc.vfp.VerifExers as VE
open VE.MapProps
open import plc.vfp.Relations using (_⇔_)
open _⇔_
open import plc.vfp.Logic
open import plc.imp.Imp
```

The proofs we'll do in this section are sufficiently complicated that
it is more or less impossible to complete them by random
experimentation or following your nose.  You need to start with an
idea about why the property is true and how the proof is going to go.
The best way to do this is to write out at least a sketch of an
informal proof on paper -- one that intuitively convinces you of the
truth of the theorem -- before starting to work on the formal one.
Alternately, grab a friend and try to convince them that the theorem
is true; then try to formalize your explanation.

## Behavioral equivalence

Earlier we investigated the correctness of a very simple program
transformation: the `optimize0plus` function.  The programming
language we were considering was the first version of the language of
arithmetic expressions — with no variables — so in that setting it was
very easy to define what it means for a program transformation to be
correct: it should always yield a program that evaluates to the same
number as the original.

To talk about the correctness of program transformations for the full
Imp language, in particular assignment, we need to consider the role
of variables and state.  In the last chapter, we studied a simple
transformation on arithmetic expressions and showed that it was
correct in the sense that it preserved the value of the expressions.
To play a similar game with programs involving mutable state, we need
a more sophisticated notion of correctness, called _behavioral
equivalence_.

### Definitions

For `aexp`s and `bexp`s with variables, the definition we want is
clear: Two `aexp`s or `bexp`s are _behaviorally equivalent_ if they
evaluate to the same result in every state.

```
_≡ᴬ_ : AExp → AExp → Set
a₁ ≡ᴬ a₂ = ∀ (st : State) → ⟦ a₁ ⟧ᴬ st ≡ ⟦ a₂ ⟧ᴬ st

_≡ᴮ_ : BExp → BExp → Set
a₁ ≡ᴮ a₂ = ∀ (st : State) → ⟦ a₁ ⟧ᴮ st ≡ ⟦ a₂ ⟧ᴮ st
```

Here are some simple examples of equivalences of arithmetic and
boolean expressions.

```
≡ᴬ-example : (id X - id X) ≡ᴬ (# 0)
```

The proof of this formula relies on the `n∸n≡0` lemma from the
Induction section.

    ≡ᴬ-example st = 
      begin
        ⟦ id X - id X ⟧ᴬ st
      ≡⟨⟩
        st X ∸ st X
      ≡⟨ n∸n≡0 (st X) ⟩
        0
      ≡⟨⟩
        (⟦ # 0 ⟧ᴬ st)
      ∎

Since the steps before and after the application of the `n∸n≡0` lemma
are just expansions of the definition of `⟦_⟧ᴬ_`, we can simplify the
proof to the key step of applying the lemma,

```
≡ᴬ-example st = n∸n≡0 (st X)
```

We can state a similar result for boolean evaluation.

```
≡ᴮ-example : ((id X - id X) == # 0) ≡ᴮ T 
≡ᴮ-example st = cong (_≡ᵇ 0) (n∸n≡0 (st X))
```

#### Exercise `≡ᴮ-example-verbose` (starting) {#bequiv-example-verbose}

Write a longer `begin ... ∎` version of the proof of `≡ᴮ-example`, in
the manner of the longer version of `≡ᴬ-example`.

<div align="center">
☙ ☙ ❧ ❧
</div>

For commands, the situation is a little more subtle.  We can't simply
say "two commands are behaviorally equivalent if they evaluate to the
same ending state whenever they are started in the same initial
state," because some commands, when run in some starting states, don't
terminate in any final state at all!  What we need instead is this:
two commands are behaviorally equivalent if, for any given starting
state, they either

 - Both diverge, or

 - Both terminate in the same final state.

A compact way to express this is "if the first one terminates in a
particular state then so does the second, and vice versa."  We do this
by defining command equivalence as "if the first one terminates in a
particular state then so does the second, and vice versa":

```
_≡ᶜ_ : Command → Command → Set
c₁ ≡ᶜ c₂ = ∀ (s₁ s₂ : State) → (s₁ =[ c₁ ]=> s₂) ⇔ (s₁ =[ c₂ ]=> s₂)
```

### Simple examples

For examples of command equivalence, let's start by looking at
some very simple program transformations involving `skip`.

The first example says that when we append `skip` before any command, the
result is equivalent.

```
skip_left : ∀ (c : Command) → (skip , c) ≡ᶜ c
```

Our conclusion is a `≡ᶜ`-formula, which means we must show a universal
quantification over the possible beginning- and ending states of
executing these commands.  These quantified values then appear as
additional arguments to the proof function.

    skip_left c s₁ s₂ = ?

Within the quantification the conclusion is a bi-implication, so we
will consider the forward and backward directions separately, and bind
those two results into the single record defined as evidence for `⇔`.

```
skip_left c s₁ s₂ = record { to = fwd; from = bkw }
```

We will define the `fwd` and `bkw` directions in a `where` clause.

In the forward direction we rely on the fact only certain forms of
evidence are possible: evaluation of a command `c, c′` can be
explained only with the `C,` constructor, so the only clause for `fwd`
is for that form of evidence.  Moreover, the evaluation of `skip` is
only by `Eskip`.  Since `Eskip` requires that its starting and ending
state are the same, the evidence for the evaluation of the `c`
subcommand in the premise serves as evidence for the conclusion as
well.

```
                     where fwd : (s₁ =[ skip , c ]=> s₂) → (s₁ =[ c ]=> s₂)
                           fwd (E, Eskip e) = e
```

In the backward direction, the evidence for the premise serves as the
evidence for the second of the command steps for the conclusion.

```
                           bkw : (s₁ =[ c ]=> s₂) → (s₁ =[ skip , c ]=> s₂)
                           bkw e = E, Eskip e
```

The second example simply swaps the two command in the first argument
around: it says that when we append `skip` _after_ any command, the
result is still equivalent.  The structure of these proofs is the same
as for the first example, but with the positions of the subcommands
reversed.

```
skip_right : ∀ (c : Command) → (c , skip) ≡ᶜ c
skip_right c s₁ s₂ = record { to = fwd; from = bkw }
                      where fwd : (s₁ =[ c , skip ]=> s₂) → (s₁ =[ c ]=> s₂)
                            fwd (E, ec Eskip) = ec

                            bkw : (s₁ =[ c ]=> s₂) → (s₁ =[ c , skip ]=> s₂)
                            bkw e = E, e Eskip
```

#### Exercise `ifTrueSimplify` (starting) {#ifTrueSimplify}

Show this similar equivalence for `if` expressions:

```
postulate ifTrueSimplify : ∀ (c₁ c₂ : Command) → 
                             (if T then c₁ else c₂ end) ≡ᶜ c₁
```

<div align="center">
☙ ☙ ❧ ❧
</div>

Of course, no (human) programmer would write a conditional whose guard
is literally `T`.  But they might write one whose guard can be shown
to be _equivalent_ to true: So we will show that if `b` is equivalent
to `T` then `if b then c₁ else c₂ end` is equivalent to `c₁`.

```
ifTrue : ∀ (b : BExp) (c₁ c₂ : Command)
           → b ≡ᴮ T
             → if b then c₁ else c₂ end ≡ᶜ c₁
```

As usual when showing `≡ᶜ`-formulas, we must show a universal
quantification over a bi-implication.  So its beginning- and
ending-states become additional parameters, and we define the two
directions in a `where` clause.

```
ifTrue b c₁ c₂ bIsT s₁ s₂ = record { to = fwd; from = bkw }
```

In the forward direction we must show that if the full `if`-statement
links the starting and ending state, then so does the affirmative
subcommand,

```
                           where fwd : s₁ =[ if b then c₁ else c₂ end ]=> s₂
                                         → s₁ =[ c₁ ]=> s₂
```

We can proceed by cases on the forms of evidence which justify the
premise, namely evidence constructed with either `EIfT` or
`EIfF`.

    fwd (EIfT bIsT₀ e) = ?
    fwd (EIfF bIsF₀ e) = ?

Suppose the final rule in the derivation of

    s₁ =[ if b then c₁ else c₂ end ]=> s₂

was `EIfT`.  Then the premises of `EIfT` would hold — in order words,
`s₁ =[ c₁ ]=> s₂`, which is what we set out to prove, would hold.

```
                                 fwd (EIfT bIsT₀ e) = e
```

On the other hand, suppose the final rule in the derivation of

    s₁ =[ if b then c₁ else c₂ end ]=> s₂

was `EIfF`.  We then know that `⟦ b ⟧ᴮ s₁ = false` and `s₁ =[ c₂ ]=>
s₂`.

Recall that our premise is that `b` is equivalent to `T`, that is, for
all states `s`, `⟦ b ⟧ᴮ s = ⟦ T ⟧ᴮ s`.  In particular, this means that
`⟦ b ⟧ᴮ s₁ = T`, since `⟦ T ⟧ᴮ s₁ = T`.  But this contradicts the
evidence associated with `EIfF`, which requires that `⟦ b ⟧ᴮ s₁ = F`.
Thus, the final rule could not have been `EIfF`.  In Agda, we can
compose the two pieces of evidence `bIsT` and `bIsF₀` to the formula
`true ≡ false`, which Agda sees can have no evidence.

```
                                 fwd (EIfF bIsF₀ e) with trueNotFalse (bIsT s₁) bIsF₀
                                 ...                  | ()
```

In the reverse direction, we must show for all `s₁` and `s₂` that if
`s₁ =[ c₁ ]=> s₂` then `s₁ =[ if b then c₁ else c₂ end ]=> s₂`.

Since `b` is equivalent to `true`, we know that `⟦ b ⟧ᴮ s₁` =
`⟦ T ⟧ᴮ s₁` = `true`.  Together with the assumption that
`s₁ =[ c₁ ]=> s₂`, we can apply `EIfT` to derive evidence that
`s₁ =[ if b then c₁ else c₂ end ]=> s₂`.

```
                                 bkw : s₁ =[ c₁ ]=> s₂
                                         → s₁ =[ if b then c₁ else c₂ end ]=> s₂
                                 bkw e = EIfT (bIsT s₁) e
```

#### Exercise `ifFalse` (starting) {#ifFalse}

Show the similar result for a condition which is equivalent to `F`,

```
postulate ifFalse : ∀ (b : BExp) (c₁ c₂ : Command)
           → b ≡ᴮ F
             → if b then c₁ else c₂ end ≡ᶜ c₂
```

#### Exercise `swapIfBranches` (recommended) {#swapIfBranches}

Show that we can swap the branches of an `if` if we also negate its
guard.

```
postulate swapIfBranches : ∀ (b : BExp) (c₁ c₂ : Command)
                             → if b then c₁ else c₂ end
                                  ≡ᶜ if ! b then c₂ else c₁ end
```

<div align="center">
☙ ☙ ❧ ❧
</div>

For `while` loops, we can give a similar pair of theorems.  A loop
whose guard is equivalent to false is equivalent to `skip`.  A loop
whose guard is equivalent to true will not terminate, so it is
equivalent to `while T loop skip end`, or to any other non-terminating
program.  The first of these facts is easy, but the second is tricky.

#### Exercise `whileFalse` (recommended) {#whileFalse}

Show that a loop whose guard is equivalent to `F` is equivalent to
`skip`.

```
postulate whileFalse : ∀ (b : BExp) (c : Command)
                         → b ≡ᴮ F
                           → while b loop c end ≡ᶜ skip
```

#### Exercise `whileTrue` (stretch) {#whileTrue}

Show that a loop whose guard is equivalent to true is equivalent to
the nonterminating loop `while T loop skip end`.

For this result you will need an auxiliary lemma stating that `while`
loops whose guards are equivalent to `true` never terminate.  This
proof is quite subtle — in particular in its use of the unduction
hypothesis — but it is worth the time to study as you complete this
exercise.  The postulated statement of `whileTrue` follows the proof
of this helper result.

```
whileTrueNonterm : ∀ (b : BExp) (c : Command) (s₁ s₂ : State)
                     → b ≡ᴮ T
                       →  ¬ (s₁ =[ while b loop c end ]=> s₂)
```

We are proving a negated formula, which is defined to mean that the
assumption of that formula allows us to conclude `⊥`.  So we have the
affirmative form of the conclusion as a premise:

    whileTrueNonterm b c s₁ s₂ bIsT converges = ?

We proceed by induction on the evidence of
`s₁ =[ while b loop c end ]=> s₂`, and we must show that this
premise leads to a contradiction.

    while b true c nonterm s .s bIsT (EWhileF bEvalsFalse) = ?
    while b true c nonterm s₁ s₂ bIsT (EWhileT bEvalsTrue evalFirst evalRest) = ?

Notice that we again see the dot pattern in the first clause: since a
while loop with `F` as its condition is equivalent to `skip`, the
state and ending state in that clause must be the same.  Moreover the
only two cases that we must consider are `EWhileF` and `EWhileT`: the
others are contradictory.

In the first case, where `s₁ =[ while b loop c end ]=> s₂` is proved
using rule `EWhileF`, the premise `bEvalsFalse` carries evidence that
`⟦ b ⟧ᴮ s₁ = false`.  But this contradicts the assumption that `b` is
equivalent to `true`.

```
whileTrueNonterm b c s .s bIsT (EWhileF bEvalsFalse) =
  trueNotFalse (bIsT s) bEvalsFalse
```

In the second case, where `s₁ =[ while b loop c end ]=> s₂` is proved
using rule `EWhileT`, we will use the induction hypothesis, but there
are some preliminaries.  First, we note that the premise `bIsT`
carries evidence that `⟦ b ⟧ᴮ s₁ = true`.  Next, when we use `EWhileT`
there is an implicit intermediate state which arises after running the
loop body once, but before running it for the rest of its iterations.
In the definition of `_=[_]=>_` we listed that quantified variable
_first_, so we can easily expose it here:
      
    whileTrueNonterm b c s₁ s₂ bIsT (EWhileT {s₁′} bEvalsTrue evalFirst evalRest) = ?

Now we can see how we can derive `⊥` from the induction hypothesis:
the evidence `evalRest`, like the original argument `converges`,
supports the formula `s₁ =[ while b loop c end ]=> s₂` — but since
this is a strictly smaller piece of evidence, Agda will accept that we
pass it to a recursive call to `whileTrueNonterm`:

```
whileTrueNonterm b c _ s₂ bIsT (EWhileT {s₁′} _ _ evalRest) =
  whileTrueNonterm b c s₁′ s₂ bIsT evalRest
```

Notice that in the recursive call, we pass `s₁′` rather than `s₁`
(which we no longer need to name): `s₁` was the starting state for the
_entire_ execution of the loop, but with our recursive call we are
considering what happens _after_ the first pass through the body.  So
we update the starting state to be this milestone.

```
postulate whileTrue : ∀ (b : BExp) (c : Command)
                        → b ≡ᴮ T
                          → while b loop c end ≡ᶜ while T loop skip end
```

<div align="center">
☙ ☙ ❧ ❧
</div>

A more interesting fact about `while` commands is that any number of
copies of the body can be "unrolled" without changing meaning.  Loop
unrolling is a common transformation in real compilers.

```
loopUnrolling : ∀ (b : BExp) (c : Command)
                  → while b loop c end
                      ≡ᶜ if b then (c , while b loop c end) else skip end
```

We are concluding a `≡ᶜ`-formula, which is defined as a shorthand for
a universal quantification over the starting and ending states of
command execution.  We see these quantified values as additional
parameters to the proof function.

    loopUnrolling b c s₁ s₂ = ?

Within the quantification there is a bi-implication, so we have the
usual record with one field for each direction of the implication.

```
loopUnrolling b c s₁ s₂ =
  record { to = fwd; from = bkw }
```

and the signatures of the two directions are

```
    where fwd : (s₁ =[ while b loop c end ]=> s₂)
                  → (s₁ =[ if b then (c , while b loop c end)
                                else skip end ]=> s₂)
          bkw : (s₁ =[ if b then (c , while b loop c end) else skip end ]=> s₂)
                  → (s₁ =[ while b loop c end ]=> s₂)
```

In each direction we will perform a case analysis of the possible
forms of evidence for the premise.  In the forward direction the
premise concerns a loop, so the possible forms of evidence will have
one of the `EWhileT` or `EWhileF` constructors.

    fwd (EWhileF bIsFalse) = ?
    fwd (EWhileT bIsTrue firstPass otherPasses) = ?

In each case we are constructing evidence about an if-statement, so we
will assemble the overall evidence for each of these two clauses with
either the `EIfT` or `EIfF` constructor.  In the first clause, we have
evidence that `b` evaluates to `F`, so use need the `EIfF` constructor

```
          fwd (EWhileF bIsFalse) = EIfF bIsFalse Eskip
```

In the second clause we have evidence that `b` is true.  For evidence
of the then-branch we use the `E,` constructor to use evidence for one
pass of the body, and for the remaining passes.

```
          fwd (EWhileT {s₁′} bIsTrue firstPass otherPasses) = 
            EIfT bIsTrue (E, firstPass otherPasses)
```

In the reverse direction the premise concerns an if-statement, with a
loop in its affirmative branch and `skip` in its negative branch.  We
will use the evidence of the evaluation of these elements in
describing the evaluation of the loop of the conclusion.

```
          bkw (EIfT bIsTrue (E, e e₁)) = EWhileT bIsTrue e e₁
          bkw (EIfF bIsFalse Eskip) = EWhileF bIsFalse
```

#### Exercise `seqAssoc` (recommended) {#seqAssoc}

Show the following result:

```
postulate seqAssoc : ∀ c₁ c₂ c₃ → ((c₁ , c₂) , c₃) ≡ᶜ (c₁ , (c₂ , c₃))
```

<div align="center">
☙ ☙ ❧ ❧
</div>

{::comment}

REVIEW `rewrite`, and review the startStatesSame/endStatesSame lemmas
from Imp.

{:/comment}


Proving program properties involving assignments is one place where
the fact that program states are treated extensionally (e.g., `x ↦ m x
, m` and `m` are equal maps) comes in handy.  For example, to show
that the assignment of a variable to itself does not change the
program state, we can simply use the equalities between the functions
used to implement states [which we showed earlier]({{ site.baseurl
}}/VerifExers/#properties-of-total-maps), specifically `tUpdateSame`.

```
identityFwd : ∀ x st → st =[ x := id x ]=> st
identityFwd x st = endStatesSame (tUpdateSame st x)
                                 (E:= (id x) (⟦ id x ⟧ᴬ st) refl)
```

Similarly, we can prove that if assigning a value to itself maps from
some starting state to some ending state, then these two states are
actually the same.

```
selfAssignSameState : ∀ (x : String) (st₁ : State) {st₂ : State}
                        → st₁ =[ x := id x ]=> st₂
                          → st₁ ≡ st₂
```

The only form of evidence for the assignment in the premise requires
that `st₂` have a specific form as well, and `tUpdateSame` gives us
exactly the relationship we need between the starting and ending
states.

```
selfAssignSameState x st₁ {.(x ↦ n , st₁)} (E:= .(id x) n evalsToN)
  rewrite sym evalsToN = sym (tUpdateSame st₁ x)
```

That result leads us directly to this corollary, that assignment of a
variable to itself is interchangeable with a `skip` statement.

```
identityAssignment : ∀ x → (x := id x) ≡ᶜ skip
identityAssignment x s₁ s₂ =
  record { to = fwd; from = bkw }
    where fwd : (s₁ =[ x := id x ]=> s₂) → (s₁ =[ skip ]=> s₂) 
          fwd eval = endStatesSame (selfAssignSameState x s₁ eval) Eskip

          bkw : (s₁ =[ skip ]=> s₂) → (s₁ =[ x := id x ]=> s₂)
          bkw Eskip = identityFwd x s₁
```

#### Exercise `:=-≡ᴬ` (recommended) {#assign-aequiv}

Prove this result:

```
postulate
  :=-≡ᴬ : forall (x : String) (a : AExp) → (id x) ≡ᴬ a -> skip ≡ᶜ (x := a)
```

#### Exercise `≡-classes` (recommended) {#equiv-classes}

Given the following programs, group together those that are equivalent
in Imp. Your answer should be given as a list of lists, where each
sub-list represents a group of equivalent programs. For example, if
you think programs (a) through (h) are all equivalent to each other,
but not to (i), your answer should look like this:

```
progA : Command
progA = while ! (id X <= # 0) loop X := id X + # 1 end

progB : Command
progB = if (id X == # 0)
        then X := id X + # 1 , Y := # 1
        else Y := # 0
        end ,
        X := id X - id Y ,
        Y := # 0 

progC : Command
progC = skip

progD : Command
progD = while ! (id X == # 0) loop
          X := (id X * id Y) + # 1
        end

progE : Command
progE = Y := # 0

progF : Command
progF = Y := id X + # 1 ,
        while ! (id X == id Y) loop
          Y := id X + # 1
        end

progG : Command
progG = while T loop
          skip
        end

progH : Command
progH = while ! (id X == id X) loop
          X := id X + # 1
        end

progI : Command
progI = while ! (id X == id Y) loop
          X := id Y + # 1
        end
```

## Properties of behavioral equivalence

We now consider some fundamental properties of program equivalence.

### Behavioral equivalence is an equivalence 

First, we verify that the equivalences on `AExp`s, `BExp`s, and
`Command`s really are _equivalences_ — i.e., that they are reflexive,
symmetric, and transitive.  The proofs all rely directly on the
evidence of the premises, and are quite short (and contrasting `≡ᴬ`
and `≡ᴮ`, repetitive).  Recall that the `≡ᴬ` and `≡ᴮ` relationships
are quantified over a single variable, so where we have a `≡ᴬ`- or
`≡ᴮ`-formula in a conclusion, we see that quantified variable as an
additional parameter to the proof function.  When concluding a
`≡ᶜ`-formula, we see two such parameters corresponding to its two
quantifications.

```
refl-≡ᴬ : ∀ {a : AExp} → a ≡ᴬ a
refl-≡ᴬ s = refl

sym-≡ᴬ : ∀ {a₁ a₂ : AExp} → a₁ ≡ᴬ a₂ → a₂ ≡ᴬ a₁
sym-≡ᴬ a1a2 s = sym (a1a2 s)

trans-≡ᴬ : ∀ {a₁ a₂ a₃ : AExp} → a₁ ≡ᴬ a₂ → a₂ ≡ᴬ a₃ → a₁ ≡ᴬ a₃
trans-≡ᴬ a1a2 a2a3 s = trans (a1a2 s) (a2a3 s)

refl-≡ᴮ : ∀ {b : BExp} → b ≡ᴮ b
refl-≡ᴮ s = refl

sym-≡ᴮ : ∀ {b₁ b₂ : BExp} → b₁ ≡ᴮ b₂ → b₂ ≡ᴮ b₁
sym-≡ᴮ b1b2 s = sym (b1b2 s)

trans-≡ᴮ : ∀ {b₁ b₂ b₃ : BExp} → b₁ ≡ᴮ b₂ → b₂ ≡ᴮ b₃ → b₁ ≡ᴮ b₃
trans-≡ᴮ b1b2 b2b3 s = trans (b1b2 s) (b2b3 s)
```

`≡ᶜ` is defined as a bi-implication under its quantifications, so we
construct the record of each reasoning direction.

```
refl-≡ᶜ : ∀ {c : Command} → c ≡ᶜ c
refl-≡ᶜ s₁ s₂ = record { to = λ x → x; from = λ x → x }

sym-≡ᶜ : ∀ {c₁ c₂ : Command} → c₁ ≡ᶜ c₂ → c₂ ≡ᶜ c₁
sym-≡ᶜ c1c2 s₁ s₂ = record { to = from (c1c2 s₁ s₂); from = to (c1c2 s₁ s₂) }
```

The last of these results `trans-≡ᶜ` has a bit more plumbing to it
than the others.

```
trans-≡ᶜ : ∀ {c₁ c₂ c₃ : Command} → c₁ ≡ᶜ c₂ → c₂ ≡ᶜ c₃ → c₁ ≡ᶜ c₃
trans-≡ᶜ c1c2 c2c3 s₁ s₂ = record {
  to = λ e₁ → to (c2c3 s₁ s₂) (to (c1c2 s₁ s₂) e₁) ;
  from = λ e₃ → from (c1c2 s₁ s₂) (from (c2c3 s₁ s₂) e₃) }
```

### Behavioral equivalence is a congruence

Less obviously, behavioral equivalence is also a _congruence_.  That
is, the equivalence of two subprograms implies the equivalence of
larger programs in which they are embedded:

            aequiv a a'
    -------------------------
    cequiv (x := a) (x := a')

         cequiv c₁ c1'
         cequiv c₂ c2'
    --------------------------
    cequiv (c1;c2) (c1';c2')

and so on for the other forms of commands.  (Note that we are using
the inference rule notation here not as part of a definition, but
simply to write down some valid implications in a readable format.  We
prove these implications below.)

The value of these results is that they let us replace a small part of
a large program with an equivalent small part and know that the whole
large programs are equivalent _without_ doing an explicit proof about
the non-varying parts.  In other words, the "proof burden" of a small
change to a large program is proportional to the size of the change,
not the program.

These properties allow us to reason that a large program behaves the
same when we replace a small part with something equivalent.

```
:=-congruence : ∀ (x : String) (a a′ : AExp) → a ≡ᴬ a′ → (x := a) ≡ᶜ (x := a′)
:=-congruence x a a′ aIsA′ s₁ s₂ =
  record { to = fwd; from = bkw }
```

In each direction we are given evidence of assignment with one of the
expressions, and assemble evidence of the assignment with the other
expression.

```
    where fwd : (s₁ =[ x := a ]=> s₂) → (s₁ =[ x := a′ ]=> s₂)
          fwd (E:= .a n a≡n) = E:= a′ n (begin
                                         ⟦ a′ ⟧ᴬ s₁
                                       ≡⟨ sym (aIsA′ s₁) ⟩
                                         ⟦ a ⟧ᴬ s₁
                                       ≡⟨ a≡n ⟩
                                         n
                                       ∎) 

          bkw : (s₁ =[ x := a′ ]=> s₂) → (s₁ =[ x := a ]=> s₂)
          bkw (E:= .a′ n a′≡n) = E:= a n (begin
                                         ⟦ a ⟧ᴬ s₁
                                       ≡⟨ aIsA′ s₁ ⟩
                                         ⟦ a′ ⟧ᴬ s₁
                                       ≡⟨ a′≡n ⟩
                                         n
                                       ∎)
```

The congruence property for loops is a little more interesting, since
it requires induction.  The idea that equivalence is a congruence for
`while` means that if both `b` is equivalent to `b′` and `c` is
equivalent to `c′`, then `while b loop c end` is equivalent to `while
b′ loop c′ end`:

```
while-congruence : ∀ (b b′ : BExp) (c c′ : Command)
                     → b ≡ᴮ b′ -> c ≡ᶜ c′
                       → while b loop c end ≡ᶜ while b′ loop c′ end
```

The two equivalences are premises, so our proof function receives
evidence that `b` is equivalent to `b′` and `c` is equivalent to `c′`.
We must show, for every `s₁` and `s₂`, that `s₁ =[ while b loop c end
]=> s₂` iff `s₁ =[ while b′ loop c′ end ]=> s₂`.  We consider the two
directions separately.

```
while-congruence b b′ c c′ bEqb′ cEqc′ s₁ s₂ = record { to = fwd s₁; from = bkw s₁ }
```

In the forward direction we use induction on the evidence that `s₁ =[
while b loop c end ]=> s₂`.  The only possible forms of evidence are
the two related to loops.  For the case of `EWhileF`, the form of the
rule gives us `⟦ b ⟧ᴮ s₁ ≡ false` and `s₁ ≡ s₂`.  But then, since `b`
and `b′` are equivalent, we have `⟦ b ⟧ᴮ s₁ ' = false`.  So we
construct evidence for our conclusion with `EWhileF`, giving us
`s₁ =[ while b′ loop c′ end ]=> s₂`, as required.

```
  where fwd : ∀ (s : State)
                → s =[ while b loop c end ]=> s₂
                  → s =[ while b′ loop c′ end ]=> s₂
        fwd s (EWhileF bEvalsF) = EWhileF (trans (sym (bEqb′ s)) bEvalsF)
```

The form of the rule now gives us `⟦ b ⟧ᴮ s = true`,
with `s =[ c ]=> s₂` and `intermedSt =[ while b loop c end ]=> s₂`
for some intermediate state `intermedSt`.

We identify three subsidiary results: first, since `b` and `b′` are
equivalent, we have `⟦ b ⟧ᴮ s ≡ true`.  Then since `c` and `c′` are
equivalent, we know that `s =[ c′ ]=> s₂`.  Finally we rely on the
induction hypothesis to translate the rest of the computation from
`intermedSt` to `s₂`.  These three subsidiary results correspond to
the three arguments which `EWhileT` requires for the forward
direction.

```
        fwd s (EWhileT {intermedSt} bEvalsT firstPass otherPasses) =
          EWhileT b′EvalsT firstPass′ otherPasses′
          where b′EvalsT : (⟦ b′ ⟧ᴮ s) ≡ true
                b′EvalsT = trans (sym (bEqb′ s)) (bEvalsT)

                firstPass′ : s =[ c′ ]=> intermedSt
                firstPass′ = to (cEqc′ s intermedSt) firstPass

                otherPasses′ : intermedSt =[ while b′ loop c′ end ]=> s₂
                otherPasses′ = fwd intermedSt otherPasses
```

The reverse direction is similar, starting with premises involving
`b′` and `c′`, and converting them to results involving `b` and `c`.
Notice that we use the `from` rather than `to` direction of the
bi-implications here.

```
        bkw : ∀ (s : State)
                → s =[ while b′ loop c′ end ]=> s₂
                  → s =[ while b loop c end ]=> s₂
        bkw s (EWhileF b′EvalsF) = EWhileF (trans (bEqb′ s₂) b′EvalsF)
        bkw s (EWhileT {intermedSt} b′EvalsT firstPass′ otherPasses′) =
          EWhileT bEvalsT firstPass otherPasses
          where bEvalsT : (⟦ b ⟧ᴮ s) ≡ true
                bEvalsT = trans (bEqb′ s) (b′EvalsT)

                firstPass : s =[ c ]=> intermedSt
                firstPass = from (cEqc′ s intermedSt) firstPass′

                otherPasses : intermedSt =[ while b loop c end ]=> s₂
                otherPasses = bkw intermedSt otherPasses′
```

So we have now shown that behavioral equivalence is a congruence in
the case of assignment; the following exercises ask you to show the
congruence in the cases of sequencing two commands one after the
other, and of if-statements.

#### Exercise `seq-congruence` (recommended) {#seq-congruence}

```
postulate seq-congruence : ∀ (c₁ c₁′ c₂ c₂′ : Command)
                             → c₁ ≡ᶜ c₁′ → c₂ ≡ᶜ c₂′
                               → (c₁ , c₂) ≡ᶜ (c₁′ , c₂′)
-- Remove the postulate keyword and add your proof here
```

#### Exercise `if-congruence` (recommended) {#if-congruence}

```
postulate if-congruence : ∀ (b b′ : BExp) (c₁ c₁′ c₂ c₂′ : Command)
                            → b ≡ᴮ b′ -> c₁ ≡ᶜ c₁′ → c₂ ≡ᶜ c₂′
                              → if b then c₁ else c₂ end
                                  ≡ᶜ if b′ then c₁′ else c₂′ end
-- Remove the postulate keyword and add your proof here
```

<div align="center">
☙ ☙ ❧ ❧
</div>

For example, here are two equivalent programs and a proof of their
equivalence.

```
congruenceExample :
  (X := # 0 , 
   if (id X == # 0) then Y := # 0 else Y := # 42 end)
    ≡ᶜ (X := # 0 , 
       if (id X == # 0) then Y := id X - id X else Y := # 42 end)
congruenceExample s₁ s₂ =
  record { to = fwd; from = bkw }
```

As before `≡ᶜ` is a bi-implication, and we prove each direction separately.

```
   where fwd : (s₁ =[ X := # 0 ,
                      if id X == # 0 then Y := # 0 else Y := # 42 end
                        ]=> s₂)
              → (s₁ =[ X := # 0 ,
                       if id X == # 0 then Y := id X - id X else Y := # 42 end
                         ]=> s₂)
         bkw : (s₁ =[ X := # 0 ,
                      if id X == # 0 then Y := id X - id X else Y := # 42 end
                        ]=> s₂)
               → (s₁ =[ X := # 0 ,
                        if id X == # 0 then Y := # 0 else Y := # 42 end
                          ]=> s₂)
```

Since we have specific programs which we are showing equivalent, must
of the evidence of the premises has a specific and detailed form:
starting from

    fwd e = ?

we can refine to just one possible case, since the result of the first
command predicts the evaluation of the conditional of the second
command.

    fwd (E, (E:= .(# 0) zero refl) (EIfT refl (E:= .(# 0) zero x₃))) = ?
    fwd (E, (E:= .(# 0) zero refl) (EIfF () (E:= .(# 42) n x₃)))

Then the evaluation of the command in the conclusion reflects the
structure of the command.

```
         fwd (E, (E:= .(# 0) zero refl) (EIfT refl (E:= .(# 0) zero refl))) =
           E, (E:= (# 0) 0 refl) (EIfT refl (E:= (id X - id X) 0 refl))
```

The reverse direction works the same way: we refine the evidence for
the premise until we have narrowed down to the one possible evaluation
for the command we are given in the conclusion.

```
         bkw (E, (E:= .(# 0) zero refl)
                 (EIfT refl (E:= .(id "X" - id "X") zero refl))) =
           E, (E:= (# 0) 0 refl) (EIfT refl (E:= (# 0) 0 refl))
```

#### Exercise `notCongruence` (practice) {#not-congruence}

We've shown that the `cequiv` relation is both an equivalence and a
congruence on commands.  Can you think of a relation on commands that
is an equivalence but _not_ a congruence?

## Program transformations 

A _program transformation_ is a function that takes a program as input
and produces some variant of the program as output.  Compiler
optimizations such as constant folding are a canonical example, but
there are many others.

A program transformation `f` is _sound_ if it preserves the behavior
of the original program.

```
soundᴬ : (AExp -> AExp) → Set
soundᴬ f = ∀ (a : AExp) → a ≡ᴬ (f a)

soundᴮ : (BExp -> BExp) → Set
soundᴮ f = ∀ (b : BExp) → b ≡ᴮ (f b)

soundᶜ : (Command -> Command) → Set
soundᶜ f = ∀ (c : Command) → c ≡ᶜ (f c)
```

### The constant-folding transformation

An expression is _constant_ when it contains no variable references.
_Constant folding_ is an optimization that finds constant expressions
and replaces them by their values.  Essentially, it converts run-time
work (which might be repeated inside a loop) to compile-time work.

```
foldConstantsᴬ : AExp → AExp
foldConstantsᴬ a@(# x) = a
foldConstantsᴬ a@(id x) = a
foldConstantsᴬ a@(a₁ + a₂) with foldConstantsᴬ a₁ | foldConstantsᴬ a₂
... | (# n₁) | (# n₂) = # (n₁ Data.Nat.+ n₂)
... | a₁′    | a₂'     = a₁′ + a₂'
foldConstantsᴬ a@(a₁ - a₂) with foldConstantsᴬ a₁ | foldConstantsᴬ a₂
... | (# n₁) | (# n₂) = # (n₁ Data.Nat.∸ n₂)
... | a₁′    | a₂'     = a₁′ - a₂'
foldConstantsᴬ a@(a₁ * a₂) with foldConstantsᴬ a₁ | foldConstantsᴬ a₂
... | (# n₁) | (# n₂) = # (n₁ Data.Nat.* n₂)
... | a₁′    | a₂'     = a₁′ * a₂'
```

For example,

```
_ : foldConstantsᴬ ((# 1 + # 2) * id "X") ≡ (# 3) * id "X"
_ = refl
```

Note that this version of constant folding doesn't eliminate trivial
additions of zero, multiplications by 0 or 1, etc.  We are focusing
attention on a single optimization for the sake of simplicity.  It is
not hard to incorporate other ways of simplifying expressions, but
then the definitions and proofs just get longer.

```
_ : foldConstantsᴬ (id "X" - ((# 0 * # 6) + id "Y")) ≡ id "X" - (# 0 + id "Y")
_ = refl
```

We can write a similar function to look for constant _boolean_
expressions and evaluate them in-place.  Moreover, this function can
also use `foldConstantsᴬ` to find simplifications to comparison
operators.

```
foldConstantsᴮ : BExp → BExp
foldConstantsᴮ T = T
foldConstantsᴮ F = F
foldConstantsᴮ (a₁ == a₂) with foldConstantsᴬ a₁ | foldConstantsᴬ a₂
... | (# n₁) | (# n₂) = if (n₁ ≡ᵇ n₂) then T else F
... | a₁′    | a₂'    = a₁′ == a₂'
foldConstantsᴮ (a₁ <= a₂) with foldConstantsᴬ a₁ | foldConstantsᴬ a₂
... | (# n₁) | (# n₂) = if (n₁ ≡ᵇ n₂) ∨ (n₁ <ᵇ n₂) then T else F
... | a₁′    | a₂'    = a₁′ <= a₂'
foldConstantsᴮ (! b) with foldConstantsᴮ b
... | T  = F
... | F  = T
... | b′ = ! b′
foldConstantsᴮ (b₁ && b₂) with foldConstantsᴮ b₁ | foldConstantsᴮ b₂
... | T | T = T
... | _ | F = F
... | F | _ = F
... | b₁′ | b₂′ = b₁′ && b₂′
foldConstantsᴮ (b₁ || b₂) with foldConstantsᴮ b₁ | foldConstantsᴮ b₂
... | F | F = F
... | b₁′ | T = b₁′
... | T | b₂′ = b₂′
... | b₁′ | b₂′ = b₁′ || b₂′

_ : foldConstantsᴮ (T && ! (F && T)) ≡ T
_ = refl

_ : foldConstantsᴮ ((id X == id Y) && (# 0 == (# 2 - (# 1 + # 1))))
     ≡ (id X == id Y) && T
_ = refl
```

To fold constants in a command, we apply the appropriate folding
functions on all embedded expressions.

```
foldConstantsᶜ : Command → Command
foldConstantsᶜ skip = skip
foldConstantsᶜ (x := a) = x := (foldConstantsᴬ a)
foldConstantsᶜ (c₁ , c₂) = foldConstantsᶜ c₁ , foldConstantsᶜ c₂
foldConstantsᶜ (if b then c₁ else c₂ end) with foldConstantsᴮ b
... | T = foldConstantsᶜ c₁
... | F = foldConstantsᶜ c₂
... | b′ = if foldConstantsᴮ b′ then foldConstantsᶜ c₁ else foldConstantsᶜ c₂ end
foldConstantsᶜ (while b loop c end) =
  while foldConstantsᴮ b loop foldConstantsᶜ c end

cmd1 : Command
cmd1 = (X := # 4 + # 5 ,
        Y := id X - # 3 ,
        if ((id X - id Y) == (# 2 + # 4))
          then skip
          else Y := # 0
          end ,
        if (# 0 <= (# 4 - (# 2 + # 1)))
          then Y := # 0
          else skip
          end ,
        while (id Y == # 0) loop
          X := id X + # 1
          end)

cmd2 : Command
cmd2 = (X := # 9 ,
        Y := id X - # 3 ,
        if ((id X - id Y) == # 6)
          then skip
          else Y := # 0
          end ,
        Y := # 0 ,
        while (id Y == # 0) loop
          X := id X + # 1
          end)

_ : foldConstantsᶜ cmd1 ≡ cmd2
_ = refl
```

### Soundness of constant folding

Now we need to show that what we've done is correct.
Here's the proof for arithmetic expressions:

```
foldConstantsᴬ_sound : soundᴬ foldConstantsᴬ
```

#### Exercise `foldBexpEqInformal` (practice) {#foldBexpEqInformal}

Here is an informal proof of the `BEq` case of the argument for
boolean expression constant folding.  Read it carefully and compare it
to the formal proof that follows.  Then fill in the `BLe` case of the
formal proof (without looking at the `BEq` case, if possible).

   _Theorem_: The constant folding function for booleans,
   `foldConstantsᴮ`, is sound.

   _Proof_: We must show that `b` is equivalent to `foldConstantsᴮ b`,
   for all boolean expressions `b`.  Proceed by induction on `b`.  We
   show just the case where `b` has the form `a1 = a2`.

   In this case, we must show
{[
       ⟦ <{ a1 = a2 }> ⟧ᴮ st
     = ⟦ (foldConstantsᴮ <{ a1 = a2 }>) ⟧ᴮ st.
]]
   There are two cases to consider:

     - First, suppose `foldConstantsᴬ a1 = ANum n1` and
       `foldConstantsᴬ a2 = ANum n2` for some `n1` and `n2`.

       In this case, we have
[[
           foldConstantsᴮ [[ a1 = a2 ]]
         = if n1 =? n2 then <{true}> else <{false}>
]]
       and
[[
           ⟦ <{a1 = a2}> ⟧ᴮ st
         = (aeval s₁ a1) =? (aeval s₁ a2).
]]
       By the soundness of constant folding for arithmetic
       expressions (Lemma `foldConstantsᴬ_sound`), we know
[[
           aeval s₁ a1
         = aeval s₁ (foldConstantsᴬ a1)
         = aeval s₁ (ANum n1)
         = n1
]]
       and
[[
           aeval s₁ a2
         = aeval s₁ (foldConstantsᴬ a2)
         = aeval s₁ (ANum n2)
         = n2,
]]
       so
[[
           ⟦ <{a1 = a2}> ⟧ᴮ st
         = (aeval a1) =? (aeval a2)
         = n1 =? n2.
]]
       Also, it is easy to see (by considering the cases `n1 = n2` and
       `n1 <> n2` separately) that
[[
           ⟦ if n1 =? n2 then T else F ⟧ᴮ st
         = if n1 =? n2 then beval s₁ <{true}> else ⟦ <{false}> ⟧ᴮ st
         = if n1 =? n2 then true else false
         = n1 =? n2.
]]
       So
[[
           beval s₁ (<{ a1 = a2 }>)
         = n1 =? n2.
         = ⟦ if n1 =? n2 then T else F ⟧ᴮ st,
]]
       as required.

     - Otherwise, one of `foldConstantsᴬ a1` and
       `foldConstantsᴬ a2` is not a constant.  In this case, we
       must show
[[
           ⟦ <{a1 = a2}> ⟧ᴮ st
         = ⟦ foldConstantsᴬ a1 ⟧ᴮ s₁ =
                         ⟦ foldConstantsᴬ a2 ⟧ᴮ st,
]]
       which, by the definition of `⟦_⟧ᴮ_` is the same as showing
[[
           (aeval s₁ a1) =? (aeval s₁ a2)
         = (aeval s₁ (foldConstantsᴬ a1)) =?
                   (aeval s₁ (foldConstantsᴬ a2)).
]]
       But the soundness of constant folding for arithmetic
       expressions (`foldConstantsᴬ_sound`) gives us
[[
         aeval s₁ a1 = aeval s₁ (foldConstantsᴬ a1)
         aeval s₁ a2 = aeval s₁ (foldConstantsᴬ a2),
]]
       completing the case.  [] *)


Theorem foldConstantsᴮ_sound:
  btrans_sound foldConstantsᴮ.


(* HIDE: compressed version of above [is this useful? -BCP]

    unfold btrans_sound; unfold bequiv.
    induction b; intros;
    try reflexivity;
    try
      (simpl;
       remember (foldConstantsᴬ a) as a′;
       remember (foldConstantsᴬ a0) as a0';
       assert (aeval s₁ a = aeval s₁ a′) as Ha;
       assert (aeval s₁ a0 = aeval s₁ a0') as Ha0;
         try (subst; apply foldConstantsᴬ_sound);
       destruct a′; destruct a0'; rewrite Ha; rewrite Ha0;
       simpl; (try destruct (n =? n0)); (try destruct (n <=? n0));
       reflexivity);
    try (simpl; destruct (foldConstantsᴮ b); rewrite IHb; reflexivity);
    try (simpl; destruct (foldConstantsᴮ b1);
         destruct (foldConstantsᴮ b2);
         rewrite IHb1; rewrite IHb2; reflexivity). *)


#### Exercise `foldConstantsCmdSound` (practice) {#foldConstantsCmdSound}

(* EX3 (foldConstantsᶜ_sound) *)
(** Complete the `while` case of the following proof. *)


Theorem foldConstantsᶜ_sound :
  ctrans_sound foldConstantsᶜ.




### Soundness of (0 + n) elimination, redux 

#### Exercise `optimize0+` (stretch) {#optimize-zero-plus}

(* EX4A? (optimize0plus) *)
(** Recall the definition `optimize0plus` from the \CHAPV1{Imp} chapter
    of _Logical Foundations_:
[[
    Fixpoint optimize0plus (a:aexp) : aexp :=
      match a with
      | ANum n =>
          ANum n
      | <{ 0 + a2 }> =>
          optimize0plus a2
      | <{ a1 + a2 }> =>
          <{ (optimize0plus a1) + (optimize0plus a2) }>
      | <{ a1 - a2 }> =>
          <{ (optimize0plus a1) - (optimize0plus a2) }>
      | <{ a1 * a2 }> =>
          <{ (optimize0plus a1) * (optimize0plus a2) }>
      end.
]]
   Note that this function is defined over the old `aexp`s,
   without states.

   Write a new version of this function that accounts for variables,
   plus analogous ones for `bexp`s and commands:
[[
     optimize0plus_aexp
     optimize0plus_bexp
     optimize0plus_com
]]
   Prove that these three functions are sound, as we did for
   `fold_constants_*`.  Make sure you use the congruence lemmas in
   the proof of `optimize0plus_com` — otherwise it will be _long_!

   Then define an optimizer on commands that first folds
   constants (using `foldConstantsᶜ`) and then eliminates `0 + n`
   terms (using `optimize0plus_com`).

   - Give a meaningful example of this optimizer's output.

   - Prove that the optimizer is sound.  (This part should be _very_
     easy.)  *)

(* SOLUTION *)

Fixpoint optimize0plus_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x
  | <{ 0 + a2 }> => optimize0plus_aexp a2
  | <{ a1 + a2 }> => <{ (optimize0plus_aexp a1) + (optimize0plus_aexp a2) }>
  | <{ a1 - a2 }> => <{ (optimize0plus_aexp a1) - (optimize0plus_aexp a2) }>
  | <{ a1 * a2 }> => <{ (optimize0plus_aexp a1) * (optimize0plus_aexp a2) }>
  end.

Fixpoint optimize0plus_bexp (b : bexp) : bexp :=
  match b with
  | <{true}>       => <{true}>
  | <{false}>      => <{false}>
  | <{ a1 = a2 }>  => <{ (optimize0plus_aexp a1) = (optimize0plus_aexp a2) }>
  | <{ a1 <= a2 }> => <{ (optimize0plus_aexp a1) <= (optimize0plus_aexp a2) }>
  | <{ ~ b1 }>     => <{ ~ (optimize0plus_bexp b1) }>
  | <{ b1 && b2 }> => <{ (optimize0plus_bexp b1) && (optimize0plus_bexp b2) }>
  end.

Fixpoint optimize0plus_com (c : com) : com :=
  match c with
  | <{ skip }>                     => <{ skip }>
  | <{ x := a }>                   => <{ x := optimize0plus_aexp a }>
  | <{ c₁ ; c₂ }>                  => <{ optimize0plus_com c₁ ;
                                         optimize0plus_com c₂ }>
  | <{ if b then c₁ else c₂ end }> =>
     <{ if (optimize0plus_bexp b)
        then (optimize0plus_com c1)
        else (optimize0plus_com c2)
        end }>
  | <{ while b loop c₁ end }>         => <{ while (optimize0plus_bexp b) do
                                          (optimize0plus_com c1)
                                         end }>
  end.

Theorem optimize0plus_aexp_sound:
  atrans_sound optimize0plus_aexp.
Proof.
  unfold atrans_sound, aequiv.
  intros a st.
  induction a;
    (* ANum and AId are immediate by definition *)
    try (reflexivity);
    (* AMinus and AMult are immediate by IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  - (* APlus *)
    destruct a1;
    (* everything but ANum and AId follow from the IH *)
    try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
    + (* ANum *)
      simpl. rewrite IHa2.
      destruct n as [| n'].
      * (* n = 0 *)
        apply plus_0_l.
      * (* n = S n' *)
        simpl. reflexivity.
    + (* AId *)
      simpl. rewrite IHa2. reflexivity.  Qed.

Theorem optimize0plus_bexp_sound :
  btrans_sound optimize0plus_bexp.
Proof.
  unfold btrans_sound, bequiv.
  intros b st. induction b; simpl;
               try reflexivity;
               try (rewrite IHb1; rewrite IHb2; reflexivity);
               try (rewrite <- optimize0plus_aexp_sound;
                    rewrite <- optimize0plus_aexp_sound;
                    reflexivity).
  - (* BNot *)
    rewrite IHb. reflexivity.  Qed.

Theorem optimize0plus_com_sound :
  ctrans_sound optimize0plus_com.
Proof.
  unfold ctrans_sound, cequiv.
  intros c.
  induction c;
  intros s₁ s₂. simpl.
  - (* skip *)
    apply refl_cequiv.
  - (* := *)
    apply :=-congruence.
    apply optimize0plus_aexp_sound.
  - (* ; *)
    apply CSeq_congruence; unfold cequiv.
    apply IHc1. apply IHc2.
  - (* if *)
    apply CIf_congruence; unfold cequiv.
    apply optimize0plus_bexp_sound.
    apply IHc1. apply IHc2.
  - (* while *)
    apply CWhile_congruence; unfold cequiv.
    apply optimize0plus_bexp_sound.
    apply IHc.  Qed.

Definition optimizer (c : com) := optimize0plus_com (foldConstantsᶜ c).

Theorem optimizer_sound :
  ctrans_sound optimizer.
Proof.
  unfold ctrans_sound. unfold optimizer.
  intros c.
  apply trans_cequiv with (foldConstantsᶜ c).
  apply foldConstantsᶜ_sound.
  apply optimize0plus_com_sound.  Qed.
(* /SOLUTION *)


### Proving inequivalence

(** Suppose that `c1` is a command of the form `X := a1; Y := a2`
    and `c2` is the command `X := a1; Y := a2'`, where `a2'` is
    formed by substituting `a1` for all occurrences of `X` in `a2`.
    For example, `c1` and `c2` might be:
[[
       c₁  =  (X := 42 + 53;
               Y := Y + X)
       c₂  =  (X := 42 + 53;
               Y := Y + (42 + 53))
]]
    Clearly, this _particular_ `c1` and `c2` are equivalent.  Is this
    true in general? *)

(** FULL: We will see in a moment that it is not, but it is worthwhile
    to pause, now, and see if you can find a counter-example on your
    own. *)

(** TERSE: *** *)

(** More formally, here is the function that substitutes an arithmetic
    expression `u` for each occurrence of a given variable `x` in
    another expression `a`: *)

Fixpoint subst_aexp (x : string) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n       =>
      ANum n
  | AId x'       =>
      if eqb_string x x' then u else AId x'
  | <{ a1 + a2 }>  =>
      <{ (subst_aexp x u a1) + (subst_aexp x u a2) }>
  | <{ a1 - a2 }> =>
      <{ (subst_aexp x u a1) - (subst_aexp x u a2) }>
  | <{ a1 * a2 }>  =>
      <{ (subst_aexp x u a1) * (subst_aexp x u a2) }>
  end.

Example subst_aexp_ex :
  subst_aexp X (42 + 53) <{ Y + X}>
  = <{ Y + (42 + 53)}>.

(** TERSE: *** *)

(** And here is the property we are interested in, expressing the
    claim that commands `c1` and `c2` as described above are
    always equivalent.  *)

Definition subst_equiv_property := forall x1 x2 a1 a2,
  cequiv <{ x1 := a1; x2 := a2 }>
         <{ x1 := a1; x2 := subst_aexp x1 a1 a2 }>.

(** TERSE: *** *)
(** Sadly, the property does _not_ always hold.

    We can show the following counterexample:
[[
       X := X + 1; Y := X
]]
    If we perform the substitution, we get
[[
       X := X + 1; Y := X + 1
]]
    which clearly isn't equivalent to the original program. [] *)
(* HIDE: An earlier, more tedious proof:

      Sadly, the property does _not_ always hold — i.e., it is not the
          case that, for all `x1`, `x2`, `a1`, and `a2`,
      [[
            cequiv (x1 ::= a1;; x2 ::= a2)
                   (x1 ::= a1;; x2 ::= subst_aexp x1 a1 a2).
      ]]
          To see this, suppose (for a contradiction) that for all `x1`, `x2`,
          `a1`, and `a2`, we have
      [[
            cequiv (x1 ::= a1;; x2 ::= a2)
                   (x1 ::= a1;; x2 ::= subst_aexp x1 a1 a2).
      ]]
          Consider the following program:
      [[
            X ::= X + 1;; Y ::= X
      ]]
          Note that
      [[
            empty_st =[ X ::= X + 1;; Y ::= X ]=> st1,
      ]]
          where `st1 = (Y !-> 1 ; X !-> 1)`.

          By assumption, we know that
      [[
            cequiv (X ::= X + 1;;
                    Y ::= X)
                   (X ::= X + 1;;
                    Y ::= X + 1)
      ]]
          so, by the definition of `cequiv`, we have
      [[
            empty_st =[ X ::= X + 1;; Y ::= X + 1 ]=> st1.
      ]]
          But we can also derive
      [[
            empty_st =[ X ::= X + 1;; Y ::= X + 1 ]=> st2,
      ]]
          where `st2 = (Y !-> 2 ; X !-> 1)`.  But `st1 <> st2`, which is a
          contradiction, since `ceval` is deterministic!  []
*)

Theorem subst_inequiv :
  ~ subst_equiv_property.


#### Exercise `betterSubst≡` (stretch) {#better-subst-equiv}

(* EX4? (better_subst_equiv) *)
(** The equivalence we had in mind above was not complete nonsense --
    it was actually almost right.  To make it correct, we just need to
    exclude the case where the variable `X` occurs in the
    right-hand-side of the first assignment statement. *)

Inductive var_not_used_in_aexp (x : string) : aexp -> Prop :=
  | VNUNum : forall n, var_not_used_in_aexp x (ANum n)
  | VNUId : forall y, x <> y -> var_not_used_in_aexp x (AId y)
  | VNUPlus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 + a2 }>)
  | VNUMinus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 - a2 }>)
  | VNUMult : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 * a2 }>).

Lemma aeval_weakening : forall x s₁ a ni,
  var_not_used_in_aexp x a ->
  aeval (x !-> ni ; st) a = aeval s₁ a.

(** Using `var_not_used_in_aexp`, formalize and prove a correct version
    of `subst_equiv_property`. *)

(* SOLUTION *)
Lemma aeval_subst : forall x s₁ a1 a2,
  var_not_used_in_aexp x a1 ->
  aeval (x !-> aeval s₁ a1 ; st) a2 =
  aeval (x !-> aeval s₁ a1 ; st) (subst_aexp x a1 a2).
Proof.
  intros x s₁ a1 a2 Hi.
  generalize dependent st.
  induction a2 as [| x' | | | ]; intros st;
    (* operator cases follow from the IH *)
    try (simpl; rewrite -> IHa2_1; rewrite -> IHa2_2; reflexivity).
  - (* ANum *)
    reflexivity.
  - (* AId *)
    unfold subst_aexp.
    destruct (eqb_stringP x x') as [H | H].
    + (* x = x' *)
      subst x'.
      rewrite aeval_weakening with (a := a1); try assumption.
      simpl. rewrite t_update_eq. reflexivity.
    + (* x <> x' *)
      reflexivity.  Qed.

Theorem subst_equiv : forall x1 x2 a1 a2,
  var_not_used_in_aexp x1 a1 ->
  cequiv <{ x1 := a1; x2 := a2 }>
         <{ x1 := a1; x2 := subst_aexp x1 a1 a2 }>.
Proof.
  unfold cequiv. intros x1 x2 a1 a2 Hi.
  split; intros Hce.
  - (* -> *)
    inversion Hce; subst.
    apply E_Seq with s₂.; try assumption.
    inversion H4; subst. apply E_Ass.
    inversion H1; subst. symmetry. apply aeval_subst.
    assumption.
  - (* <- *)
    inversion Hce; subst.
    apply E_Seq with s₂..
    assumption.
    inversion H4; subst. apply E_Ass.
    inversion H1; subst. apply aeval_subst.
    assumption.  Qed.
(* /SOLUTION *)

#### Exercise `≢-skip` (practice) {#inequiv-skip}

(* EX3 (inequiv_exercise) *)
(** Prove that an infinite loop is not equivalent to `skip` *)

Theorem inequiv_exercise:
  ~ cequiv <{ while true loop skip end }> <{ skip }>.



#### Extended exercise: nondeterministic Imp

(* HIDE: Mukund: This issue will need repetition when we introduce
   small-step semantics. There's also a nice exercise for Hoare.v in
   the midterm. *)
(* LATER: BCP: The Imp chapter has a exercise on extending AExps with
   `any`.  Might be nice to reuse that idea here instead of HAVOC. *)

(** As we have seen (in theorem `ceval_deterministic` in the `Imp`
    chapter), Imp's evaluation relation is deterministic.  However,
    _non_-determinism is an important part of the definition of many
    real programming languages. For example, in many imperative
    languages (such as C and its relatives), the order in which
    function arguments are evaluated is unspecified.  The program
    fragment
[[
      x = 0;
      f(++x, x)
]]
    might call `f` with arguments `(1, 0)` or `(1, 1)`, depending how
    the compiler chooses to order things.  This can be a little
    confusing for programmers, but it gives the compiler writer useful
    freedom.

    In this exercise, we will extend Imp with a simple
    nondeterministic command and study how this change affects
    program equivalence.  The new command has the syntax `HAVOC X`,
    where `X` is an identifier. The effect of executing `HAVOC X` is
    to assign an _arbitrary_ number to the variable `X`,
    nondeterministically. For example, after executing the program:
[[
      HAVOC Y;
      Z := Y * 2
]]
    the value of `Y` can be any number, while the value of `Z` is
    twice that of `Y` (so `Z` is always even). Note that we are not
    saying anything about the _probabilities_ of the outcomes — just
    that there are (infinitely) many different outcomes that can
    possibly happen after executing this nondeterministic code.

    In a sense, a variable on which we do `HAVOC` roughly corresponds
    to an uninitialized variable in a low-level language like C.  After
    the `HAVOC`, the variable holds a fixed but arbitrary number.  Most
    sources of nondeterminism in language definitions are there
    precisely because programmers don't care which choice is made (and
    so it is good to leave it open to the compiler to choose whichever
    will run faster).

    We call this new language _Himp_ (``Imp extended with `HAVOC`''). *)

Module Himp.

(** To formalize Himp, we first add a clause to the definition of
    commands. *)

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.                (* <--- NEW *)

Notation "'havoc′ l" := (CHavoc l)
                          (in custom com at level 60, l constr at level 0).
(* INSTRUCTORS: Copy of template com *)
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAss x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

#### Exercise `himpCevel` (recommended) {#himp-ceval}

(* EX2 (himp_ceval) *)
(** Now, we must extend the operational semantics. We have provided
   a template for the `ceval` relation below, specifying the big-step
   semantics. What rule(s) must be added to the definition of `ceval`
   to formalize the behavior of the `HAVOC` command? *)

(* INSTRUCTORS: Copy of template eval *)
Reserved Notation "st '=[' c ']=>' s₂.
         (at level 40, c custom com at level 99, s₁ constr,
          s₂ constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      s₁ =[ skip ]=> st
  | E_Ass  : forall s₁ a1 n x,
      aeval s₁ a1 = n ->
      s₁ =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c₁ c₂ s₁ s₂ s₂.,
      s₁  =[ c₁ ]=> s₂  ->
      s₂ =[ c₂ ]=> s₂. ->
      s₁  =[ c₁ ; c₂ ]=> s₂.
  | EIfT : forall s₁ s₂ b c₁ c2,
      ⟦ b ⟧ᴮ s₁  = true ->
      s₁ =[ c₁ ]=> s₂ ->
      s₁ =[ if b then c₁ else c₂ end ]=> s₂
  | EIfF : forall s₁ s₂ b c₁ c2,
      ⟦ b ⟧ᴮ s₁  = false ->
      s₁ =[ c₂ ]=> s₂ ->
      s₁ =[ if b then c₁ else c₂ end ]=> s₂
  | EWhileF : forall b s₁ c,
      ⟦ b ⟧ᴮ s₁  = false ->
      s₁ =[ while b loop c end ]=> st
  | EWhileT : forall s₁ s₂ s₂. b c,
      ⟦ b ⟧ᴮ s₁  = true ->
      s₁  =[ c ]=> s₂ ->
      s₂ =[ while b loop c end ]=> s₂. ->
      s₁  =[ while b loop c end ]=> s₂.
(* SOLUTION *)
  | E_Havoc : forall (s₁ : state) (X : string) (n : nat),
      s₁ =[ havoc X ]=> (X !-> n ; st)
(* /SOLUTION *)

  where "st =[ c ]=> s₂. := (ceval c s₁ s₂..

(** As a sanity check, the following claims should be provable for
    your definition: *)

Example havoc_example1 : empty_st =[ havoc X ]=> (X !-> 0).

Example havoc_example2 :
  empty_st =[ skip; havoc Z ]=> (Z !-> 42).


(** Finally, we repeat the definition of command equivalence from above: *)

Definition cequiv (c1 c₂ : com) : Prop := forall s₁ s₂ : state,
  s₁ =[ c₁ ]=> s₂ <-> s₁ =[ c₂ ]=> s₂.

(** Let's apply this definition to prove some nondeterministic
    programs equivalent / inequivalent. *)

#### Exercise `havocSwap` (practice) {#havoc-swap}

(* EX3 (havoc_swap) *)
(** Are the following two programs equivalent? *)

(* KK: The hack we did for variables bites back *)
Definition pXY :=
  <{ havoc X ; havoc Y }>.

Definition pYX :=
  <{ havoc Y; havoc X }>.

(** If you think they are equivalent, prove it. If you think they are
    not, prove that. *)
(* QUIETSOLUTION *)

Theorem pXY_approx_pYX :
  forall X Y s₁ s₂.
    s₁ =[ havoc X; havoc Y ]=> s₂ ->
    s₁ =[ havoc Y; havoc X ]=> s₂.
Proof.
  intros X Y s₁ s₂ H.
  destruct (eqb_stringP X Y) as [Hid | Hid].
  - (* X = Y *)
    subst.  assumption.
  - (* X <> Y *)
    inversion H; subst; clear H.
    inversion H2; subst; clear H2.
    inversion H5; subst; clear H5.
    apply E_Seq with (s₂ := (Y !-> n0 ; st)). constructor.
    rewrite t_update_permute.
    constructor. assumption.
Qed.
(* /QUIETSOLUTION *)

Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~cequiv pXY pYX.

#### Exercise `havocCopy` (stretch) {#havoc-copy}

(* EX4? (havoc_copy) *)
(** Are the following two programs equivalent? *)

Definition ptwice :=
  <{ havoc X; havoc Y }>.

Definition pcopy :=
  <{ havoc X; Y := X }>.

(** If you think they are equivalent, then prove it. If you think they
    are not, then prove that.  (Hint: You may find the `assert` tactic
    useful.) *)

Theorem ptwice_cequiv_pcopy :
  cequiv ptwice pcopy \/ ~cequiv ptwice pcopy.

(** The definition of program equivalence we are using here has some
    subtle consequences on programs that may loop forever.  What
    `cequiv` says is that the set of possible _terminating_ outcomes
    of two equivalent programs is the same. However, in a language
    with nondeterminism, like Himp, some programs always terminate,
    some programs always diverge, and some programs can
    nondeterministically terminate in some runs and diverge in
    others. The final part of the following exercise illustrates this
    phenomenon.
*)

#### Exercise `p1p2Term` (stretch) {#p1p2Term}

(* EX4A (p1_p2_term) *)
(** Consider the following commands: *)

Definition p1 : com :=
  <{ while ~ (X = 0) do
       havoc Y;
       X := X + 1
     end }>.

Definition p2 : com :=
  <{ while ~ (X = 0) do
       skip
     end }>.

(** Intuitively, `p1` and `p2` have the same termination behavior:
    either they loop forever, or they terminate in the same state they
    started in.  We can capture the termination behavior of `p1` and
    `p2` individually with these lemmas: *)

Lemma p1_may_diverge : forall s₁ s₂. s₁ X <> 0 ->
  ~ s₁ =[ p1 ]=> s₂.

Lemma p2_may_diverge : forall s₁ s₂. s₁ X <> 0 ->
  ~ s₁ =[ p2 ]=> s₂.

#### Exercise `p1p2Equiv` (stretch) {#p1p2Equiv}

(* EX4A (p1_p2_equiv) *)
(** Use these two lemmas to prove that `p1` and `p2` are actually
    equivalent. *)

Theorem p1_p2_equiv : cequiv p1 p2.

#### Exercise `p2p4Inequiv` (stretch) {#p2p4Inequiv}

(* EX4A (p3_p4_inequiv) *)
(** Prove that the following programs are _not_ equivalent.  (Hint:
    What should the value of `Z` be when `p3` terminates?  What about
    `p4`?) *)

Definition p3 : com :=
  <{ Z := 1;
     while ~(X = 0) do
       havoc X;
       havoc Z
     end }>.

Definition p4 : com :=
  <{ X := 0;
     Z := 1 }>.
(* QUIETSOLUTION *)

(** First, note that the programs `p3` and `p4` are not equivalent:
    when `p3` terminates, even though `X` definitely has value `0`,
    `Z` might have any natural number as the value. *)
(* /QUIETSOLUTION *)

Theorem p3_p4_inequiv : ~ cequiv p3 p4.

#### Exercise `p5p6Equiv` (stretch) {#p5p6Equiv}

(* EX5A? (p5_p6_equiv) *)
(** Prove that the following commands are equivalent.  (Hint: As
    mentioned above, our definition of `cequiv` for Himp only takes
    into account the sets of possible terminating configurations: two
    programs are equivalent if and only if the set of possible terminating
    states is the same for both programs when given a same starting state
    `st`.  If `p5` terminates, what should the final state be? Conversely,
    is it always possible to make `p5` terminate?) *)

Definition p5 : com :=
  <{ while ~(X = 1) do
       havoc X
     end }>.

Definition p6 : com :=
  <{ X := 1 }>.
(* QUIETSOLUTION *)

(** Programs `p5` and `p6` are equivalent although `p5` may diverge,
    while `p6` always terminates. The definition we took for `cequiv`
    cannot distinguish between these two scenarios. It accepts the two
    programs as equivalent on the basis that: if `p5` terminates it
    produces the same final state as `p6`, and there exists an
    execution in which `p5` terminates and does exactly as `p6`.

    There are two directions to the proof:

    `→`: Observe that whenever `p5` terminates, it does so with `X`
    set to `1`, and no other variable changed. But this is exactly the
    behavior of `p6`. Thus given a pair of states `st` and `st'` and
    that `s₁ =[ p5 ]=> s₂`, the answer to the question
    "Does `s₁ =[ p6 ]=> s₂`?"  is "Yes".

    `←` (and more controversially): Given that `s₁ =[ p6 ]=> s₂` for
    some `st` and `st'`, can we show that `s₁ =[ p5 ]=> s₂`? Observe
    that we can use the hypothesis to conclude that
    `st' = (X !-> 1 ; st)`.
    Is there some execution of `p5` starting from `st` which also
    ends up in `st'`? Yes!

    Hence their equivalence. *)

Lemma p5_summary : forall s₁ s₂.
    s₁ =[ p5 ]=> s₂ -> s₂ = (X !-> 1 ; st).
Proof.
  intros. remember p5 as p5' eqn:Heqp5'.
  induction H; inversion Heqp5'; subst.
  - (* EWhileF *)
    simpl in H. apply negb_false_iff in H. apply eqb_eq in H.
    rewrite <- H. rewrite t_update_same. reflexivity.
  - (* EWhileT *)
    apply IHceval2 in Heqp5'.
    inversion H0; subst.
    apply t_update_shadow.
Qed.
(* /QUIETSOLUTION *)

Theorem p5_p6_equiv : cequiv p5 p6.

End Himp.


(* HIDE *)
(* HIDE: BCP 2/16: This whole discussion seems like kind of a
   side-track, especially now that we've built extensionality into the
   earlier chapters even more deeply.  I'm removing it for now.  If
   people prefer to keep it, I wonder whether we could move it to an
   optional chapter by itself... *)

## Additional exercises

#### Exercise `` () {#}

(* EX4? (for_while_equiv) *)
(** This exercise extends the optional `add_for_loop` exercise from
    the \CHAPV1{Imp} chapter, where you were asked to extend the language
    of commands with C-style `for` loops.  Prove that the command:
[[
      for (c1; b; c2) {
          c3
      }
]]
    is equivalent to:
[[
       c1;
       while b do
         c3;
         c2
       end
]]
*)
(* SOLUTION *)
(* LATER: write a solution! *)
(* If you write a nice solution to this one, please send it to us! *)
(* /SOLUTION *)

#### Exercise `` () {#}

(* EX3? (swap_noninterfering_assignments) *)
(** (Hint: You'll need `functional_extensionality` for this one.) *)

Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
  l1 <> l2 ->
  var_not_used_in_aexp l1 a2 ->
  var_not_used_in_aexp l2 a1 ->
  cequiv
    <{ l1 := a1; l2 := a2 }>
    <{ l2 := a2; l1 := a1 }>.

#### Exercise `` () {#}

(* EX4A? (capprox) *)
(* HIDE: Question from 2012, UPenn Midterm 2. *)
(* LATER: Sampsa: This exercise is easily breakable *)
(** In this exercise we define an asymmetric variant of program
    equivalence we call _program approximation_. We say that a
    program `c1` _approximates_ a program `c2` when, for each of
    the initial states for which `c1` terminates, `c2` also terminates
    and produces the same final state. Formally, program approximation
    is defined as follows: *)

Definition capprox (c1 c₂ : com) : Prop := forall (s₁ s₂ : state),
  s₁ =[ c₁ ]=> s₂ -> s₁ =[ c₂ ]=> s₂.

(** For example, the program
[[
  c₁ = while ~(X = 1) do
         X ::= X - 1
       end
]]
    approximates `c2 = X ::= 1`, but `c2` does not approximate `c1`
    since `c1` does not terminate when `X = 0` but `c2` does.  If two
    programs approximate each other in both directions, then they are
    equivalent. *)

(** Find two programs `c3` and `c4` such that neither approximates
    the other. *)

Definition c3 : com
  (* ADMITDEF *) := <{ X := 1 }>. (* /ADMITDEF *)
Definition c4 : com
  (* ADMITDEF *) := <{ X := 2 }>. (* /ADMITDEF *)

Theorem c3_c4_different : ~ capprox c3 c4 /\ ~ capprox c4 c3.

(** Find a program `cmin` that approximates every other program. *)

Definition cmin : com
  (* ADMITDEF *) := <{ while true loop skip end }>. (* /ADMITDEF *)

Theorem cmin_minimal : forall c, capprox cmin c.

(** Finally, find a non-trivial property which is preserved by
    program approximation (when going from left to right). *)

Definition zprop (c : com) : Prop
  (* ADMITDEF *) := forall st, exists s₂. s₁ =[ c ]=> s₂. (* /ADMITDEF *)
(* QUIETSOLUTION *)

(** Intuitively, `zprop` holds of programs that terminate on all
    inputs. *)

(* /QUIETSOLUTION *)
Theorem zprop_preserving : forall c c′,
  zprop c -> capprox c c′ -> zprop c′.
(* HIDE *)

(** INSTRUCTORS: Several other non-trivial properties are also
    preserved by progam approximation. The following is a collection
    of interesting solutions harvested from last year's exams.  They
    could be turned into exercises at some point... *)
(* LATER: Lots of acknowledgments due here. :) *)

(** `zprop2` holds of programs that terminate on at least one
    input. *)

Definition zprop2 (c : com) : Prop :=
  exists s₁ s₂. s₁ =[ c ]=> s₂.

Theorem zprop2_preserving : forall c c′,
  zprop2 c -> capprox c c′ -> zprop2 c′.
Proof.
  unfold zprop2, capprox. intros.
  destruct H as [s₁ `st'` ]. intros.
  exists st, s₂. apply H0. assumption.
Qed.

(** `zprop3` holds of programs that behave like `skip`. *)

Definition zprop3 (c : com) : Prop :=
  forall st, s₁ =[ c ]=> st.

Theorem zprop3_preserving : forall c c′,
  zprop3 c -> capprox c c′ -> zprop3 c′.
Proof.
  unfold zprop3, capprox. intros.
  apply H0. apply H.
Qed.

(** `zprop4` is similar to `zprop3` — observe that `capprox`
    is transitive. *)

Definition zprop4 (c : com) : Prop :=
  capprox <{ skip }> c.

Theorem zprop4_preserving : forall c c′,
  zprop4 c -> capprox c c′ -> zprop4 c′.
Proof.
  unfold zprop4, capprox. intros.
  apply H0. apply H. assumption.
Qed.

Print All.

(* /HIDE *)


(* HIDE *)
(* Local Variables: *)
(* fill-column: 70 *)
(* outline-regexp: "(==>*==>* ==>*+==>|(==>* EX[1-5]..." *)
(* mode: outline-minor *)
(* outline-heading-end-regexp: "\n" *)
(* End: *)
(* /HIDE *)

## Unicode

This section uses the following Unicode symbols:

    ×  U+00D7  MULTIPLICATION SIGN (\x)
    →  U+2192  RIGHTWARDS ARROW (\to, \r, \->)
    ⇓  U+21D3  DOWNWARDS DOUBLE ARROW (\d=)
    ∀  U+2200  FOR ALL  (\all)
    ∷  U+2237  PROPORTION  (\::)
    ≡  U+2261  IDENTICAL TO (\==)
    ⟦    (\[[)
    ⟧    (\]])
    ᵃ    (\^a)
    ᵇ    (\^b)
    ÷    (\div)
    ′'    (\'')

---

*This page is derived from Pierce et al., with Agda translation and
additional material by Maraist; for more information see the [sources
and authorship]({{ site.baseurl }}/Sources/) page.*
