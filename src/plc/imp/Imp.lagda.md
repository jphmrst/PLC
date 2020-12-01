---
title     : "Imp: Simple imperative programs"
layout    : page
prev      : /ImpExprs/
permalink : /Imp/
next      : /Equiv/
---

```
module plc.imp.Imp where
open import Function using (case_of_)
open import Data.String using (String) renaming (_==_ to _string=_)
open import Data.Nat using (ℕ; _∸_; _≡ᵇ_; _<ᵇ_; zero; suc)
open import Data.Bool using (Bool; true; false; not; _∨_; _∧_; if_then_else_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import plc.fp.Maps using (TotalMap; _↦_,_; ↪)
import plc.vfp.VerifExers as VE
open VE.MapProps
open import plc.vfp.Relations using (_⇔_)
open import plc.vfp.Logic
open import plc.imp.ImpExprs public
```

## Commands

Now we are ready define the syntax and behavior of Imp _commands_
(sometimes called _statements_).

Informally, commands `c` are described by the following BNF grammar.

    c := skip | x := a
              | c , c
              | if b then c else c end
              | while b loop c end

For example, here's factorial in Imp:

    Z := X ,
    Y := 1 ,
    while ! (Z == 0) loop
      Y := Y * Z ,
      Z := Z - 1
    end

When this command terminates, the variable `Y` will contain the
factorial of the initial value of `X`.

Here is the formal definition of the abstract syntax of commands:

```
data Command : Set where
  skip : Command
  _:=_ : String → AExp → Command
  _,_ : Command → Command → Command
  if_then_else_end : BExp → Command → Command → Command
  while_loop_end : BExp → Command → Command

infixr 4 _,_
infixr 5 _:=_
```

Our factorial example is understood as an Agda expression once we add
the `#` and `id` constructors for `AExp`s.

```
factorialOfX : Command
factorialOfX = Z := id X ,
               Y := # 1 ,
               while ! (id Z == # 0) loop
                 Y := id Y * id Z ,
                 Z := id Z - # 1
               end
```

Some other examples of Imp expressions and commands:

```
_ : Command
_ = skip

_ : Command
_ = (skip , skip) , skip

_ : AExp
_ = # 1 + # 2

_ : BExp
_ = # 2 == # 1

_ : Command
_ = Z := id X

_ : Command
_ = Z := id X + # 3

addSkip : Command → Command
addSkip c = c , skip

_ : Command
_ = skip , addSkip skip

_ : Command
_ = if T then skip else skip end

_ : Command
_ = if T && T then skip , skip else skip , X := id X + # 1 end

_ : Command
_ = while ! (id Z == # 0) loop Y := id Y * id Z , Z := id Z - # 1 end
```

We will give names to these examples for later use:

```
plus2 : Command
plus2 = X := id X + # 2

XtimesYinZ : Command
XtimesYinZ = Z := id X * id Y

subtractSlowlyBody : Command
subtractSlowlyBody = Z := id Z - # 1 ,
                       X := id X - # 1

subtractSlowly : Command
subtractSlowly = while ! (id X == # 0) loop subtractSlowlyBody end

subtract3from5slowly : Command
subtract3from5slowly = X := # 3 ,
                       Z := # 5 ,
                       subtractSlowly

-- An infinite loop

forever : Command
forever = while T loop skip end

-- Exponentiation

expBody : Command
expBody = Z := id Z * id X ,
          Y := id Y - # 1
           
pexp : Command
pexp = while ! (id Y == # 0) loop
         expBody
       end
       -- Note that `pexp` should be run in a state where `Z` is `1`.
```

### Evaluating commands

Next we need to define what it means to evaluate an Imp command.  The
fact that `while` loops don't necessarily terminate makes defining an
evaluation function tricky.

Defining an evaluation *function* for commands will not work well.
But it will be insightful to try it anyway.  Unlike expression
evaluation, command evaluation does not have a simple integer or
boolean result.  The result of running a loop or an assignment is more
subtle than just a simple value.  These commands _change the state_.
So the result of executing the command is to transform a _starting
state_ to an _ending state_.

```
cmdEvalFn : State → Command → State
cmdEvalFn st skip = st
cmdEvalFn st (x := x₁) = x ↦ ⟦ x₁ ⟧ᴬ st , st
cmdEvalFn st (c₁ , c₂) = cmdEvalFn (cmdEvalFn st c₁) c₂
cmdEvalFn st (if x then c₁ else c₂ end) with ⟦ x ⟧ᴮ st
...                                    | true = cmdEvalFn st c₁
...                                    | false = cmdEvalFn st c₂
cmdEvalFn st (while x loop c end) = st
```

In a traditional functional programming language like OCaml or Haskell
we could add the `while` case as follows:

    cmdEvalFn : State → Command → State
    -- ...other cases unchanged...
    cmdEvalFn st (while x loop c end) with ⟦ x ⟧ᴮ st
    ...                                | true = cmdEvalFn (cmdEvalFn st c)
                                                          (while x loop c end)
    ...                                | false = st

Agda doesn't accept such a definition ("Termination checking failed")
because the function we want to define is not guaranteed to
terminate. Indeed, it _doesn't_ always terminate: for example, the
full version of the `cmdEvalFn` function applied to the `loop` program
in the examples above would never terminate.  Since Agda is not just a
functional programming language but also a consistent logic, any
potentially non-terminating function needs to be rejected.  So because
it doesn't terminate on all inputs, a version of `cmdEvalFn` that runs
while loops cannot be written in Agda — at least not without
additional tricks and workarounds.

A better way to define the evaluation of `while` loops is to define
`cmdEvalFn` as a _relation_ rather than a _function_, as we did for
`⇓ᵃ` and `⇓ᵇ` above.  This is an important change.  Besides freeing us
from awkward workarounds, it gives us much more flexibility in the
definition.  For example, if we add nondeterministic features like
`any` to the language, we want the definition of evaluation to be
nondeterministic — i.e., not only will it not be total, it will not
even be a function!

We'll use the notation `st =[ c ]=> st'` for the `ceval` relation:
`st =[ c ]=> st'` means that executing program `c` in a starting state
`st` results in an ending state `st'`.  This can be pronounced "`c`
takes state `st` to `st'`".  Here is an informal definition of
evaluation, presented as inference rules for readability:

                           -----------------                           (E_Skip)
                           st =[ skip ]=> st

                           aeval st a = n
                   -------------------------------                      (E_Ass)
                   st =[ x := a ]=> (x !-> n ; st)

                           st  =[ c1 ]=> st'
                           st' =[ c2 ]=> st′'
                        -----------------------                         (E_Seq)
                         st =[ c1 , c2 ]=> st′'

                          beval st b = true
                           st =[ c1 ]=> st'
                --------------------------------------               (E_IfTrue)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                           st =[ c2 ]=> st'
                --------------------------------------              (E_IfFalse)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                 ---------------------------------               (E_WhileFalse)
                  st =[ while b loop c end ]=> st

                          beval st b = true
                           st =[ c ]=> st'
                  st' =[ while b loop c end ]=> st′'
                ------------------------------------              (E_WhileTrue)
                  st  =[ while b loop c end ]=> st′'

Here is the formal definition.  Make sure you understand how it
corresponds to the inference rules.

```
data _=[_]=>_ : State → Command → State → Set where
  Eskip : ∀ { st : State } → st =[ skip ]=> st
  E:= : ∀ { st : State } { x : String } ( a : AExp ) ( n : ℕ ) →
           ⟦ a ⟧ᴬ st ≡ n →
             st =[ x := a ]=> ( x ↦ n , st )
  E, : ∀ { st' : State } { st st′' : State } { c₁ c₂ : Command } →
          st  =[ c₁ ]=> st'  ->
            st' =[ c₂ ]=> st′' ->
              st  =[ c₁ , c₂ ]=> st′'
  EIfT : ∀ { st st' : State } { b : BExp } { c1 c2 : Command } →
            ⟦ b ⟧ᴮ st ≡ true →
              st =[ c1 ]=> st' →
                st =[ if b then c1 else c2 end ]=> st'
  EIfF : ∀ { st st' : State } { b : BExp } { c1 c2 : Command } →
            ⟦ b ⟧ᴮ st ≡ false →
              st =[ c2 ]=> st' →
                st =[ if b then c1 else c2 end ]=> st'
  EWhileF : ∀ { st : State } { b : BExp } { c : Command } →
               ⟦ b ⟧ᴮ st ≡ false →
                 st =[ while b loop c end ]=> st
  EWhileT : ∀ { st' st st′' : State } { b : BExp } { c : Command } →
               ⟦ b ⟧ᴮ st ≡ true →
                 st =[ c ]=> st' →
                   st' =[ while b loop c end ]=> st′' →
                     st =[ while b loop c end ]=> st′'
infixr 3 _=[_]=>_
```

The cost of defining evaluation as a relation instead of a function is
that we now need to construct _proofs_ that some program evaluates to
some result state, rather than just letting Agda's computation
mechanism do it for us.  For example, for this program

    X := 2 ,
    if (X <= 1)
      then Y := 3
      else Z := 4
    end

informally we would have this proof tree:

                                                              -------------------------------------------------------------- E:=
                                                              X ↦ 2 , emptyState =[ Z := 4 ]=> Z ↦ 4 , X ↦ 2 , emptyState
     ---------------------------------------------- E:=    ------------------------------------------------------------------- EIfF
     emptyState =[ X := # 2 ]=> X ↦ 2 , emptyState         X ↦ 2 , emptyState =[ if ... end ]=> Z ↦ 4 , X ↦ 2 , emptyState
     -------------------------------------------------------------------------------------------------------------------------  E,
                                emptyState =[ X := # 2 , if ... end ]=> Z ↦ 4 , X ↦ 2 , emptyState

which translates into this formal proof:

```
_ : emptyState =[
      X := # 2 ,
      if (id X <= # 1)
        then Y := # 3
        else Z := # 4
      end
    ]=> Z ↦ 4 , X ↦ 2 , emptyState
_ = E, (E:= (# 2) 2 refl) (EIfF refl (E:= (# 4) 4 refl))
```

Here is another example,

```
_ : emptyState =[
      X := # 0 ,
      Y := # 1 ,
      Z := # 2
    ]=> Z ↦ 2 , Y ↦ 1 , X ↦ 0 , emptyState
_ = E, (E:= (# 0) 0 refl) (E, (E:= (# 1) 1 refl) (E:= (# 2) 2 refl))
```

We will make use later of a few simple lemmas about these relations.
If two states are equal, then we can exchange them as the starting
states of `_=[_]=>_`.

```
startStatesSame : ∀ {st₀ st₁ st : State} {c : Command}
                   → st₀ ≡ st₁
                     → st₀ =[ c ]=> st
                       → st₁ =[ c ]=> st
startStatesSame st₀≡st₁ eval0 rewrite st₀≡st₁ = eval0
```

Here we use the `rewrite` tool which we discussed [when we began
studying proofs]({{ site.baseurl }}/Proof/#rewriting-with-premises).
When we apply `rewrite`, it rewrites according to the given evidence
not only in the result we need to prove, but also in the proof
function's arguments.  So the `rewrite` transforms the evidence from
the argument into the evidence we need for the result.  We will also
use the related result from [Exercise sameEnd](#endStatesSame) below.

#### Exercise `pupToN` (recommended) {#pupToN}

Write an Imp program that sums the numbers from `1` to `X` (inclusive:
`1 + 2 + ... + X`) in the variable `Y`.  Your program should update
the state as shown in theorem below.  You can reverse-engineer that
state to discover the program you should write.  The proof of that
theorem will be somewhat lengthy.

    pupToN : Command
    pupToN = -- FILL IN YOUR PROGRAM HERE

    _ : X ↦ 2 , emptyState =[ pupToN ]=> X ↦ 0 , Y ↦ 3 , X ↦ 1 , Y ↦ 2 , Y ↦ 0 , X ↦ 2 , emptyState
    _ = -- FILL IN YOUR PROOF HERE

#### Exercise `endStatesSame` (recommended) {#endStatesSame}

Prove this companion result to `startStatesSame` above.

```
postulate endStatesSame : ∀ {st₀ st₁ st : State} {c : Command}
                   → st₀ ≡ st₁
                     → st =[ c ]=> st₀
                       → st =[ c ]=> st₁
-- Remove the postulate keyword and add your proof here
```


## Determinism of evaluation

Changing from a computational to a relational definition of evaluation
is a good move because it frees us from the artificial requirement
that evaluation should be a total function.  But it also raises a
question: Is the second definition of evaluation really a partial
_function_?  Or is it possible that, beginning from the same state
`st`, we could evaluate some command `c` in different ways to reach
two different output states `st'` and `st''`?

In fact, this cannot happen: `ceval` _is_ a partial function.  Note
that we will make use of some of the results on partial maps from
[Section VerifExers]({{ site.baseurl }}/VerifExers/) in this result.

We will actually prove a slightly more general lemma first, that
`ceval` preserves the equality relationship.  This technique is
helpful when intermediate steps need the more general result.  We
begin as usual with a signature stating the result we wish to show.

```
cevalPreserves≡ : ∀ (c : Command) (st₁ st₂ st₁' st₂' : State)
                    → st₁ ≡ st₂
                      → st₁ =[ c ]=> st₁'  
                        → st₂ =[ c ]=> st₂'
                          → st₁' ≡ st₂'
```

We can illustrate this statement in a diagram:

           =[ c ]=>
    st₁ ==============> st₁'
     |                  .
     | ≡                . ≡
     |                  .
    st₂ ==============> st₂'
           =[ c ]=>

The diagram uses solid lines to show relationships which we are
_given_, and a dotted line to show the relationship which we _want to
show_.  Each line is labeled with the relation which we are asserting
between the endpoints of that line.

This proof will probably be the most difficult, and certainly the
longest, that we have seen so far.  However, most of the techniques we
will see in the proof are techniques we have used before: case
analysis and induction, application of evidence to equation blocks,
propagation of constraints by dot-patterns.  The complexity of this
proof arises from a number of sources: First, the fact that we are
reasoning across three given erelationships, as the diagram shows.
The indirectness of the relationship between the four states in the
quantification requires additional reasoning steps.  Moreover, the
number of cases in both the semantic relation `_=[_]=>_` and the forms
of `Command` adds to the number of cases in the proof.  There are more
quantified values and premises to this theorem than our usual.  And
although the use of functions to model states does simplify our model
in some ways, the expressions which describe these state become longer
here.

We begin with the simple named parameters as usual.  The first five
parameters correspond to the five quantified values in the signature,
and the last three parameters correspond to the three premises of the
final conclusion, for which the body of the proof function builds
evidence.

    cevalPreserves≡ cmd st₁ st₂ st₁' st₂' st₁≡st₂ st₁=>st₁' st₂=>st₂' = ?

We can diagram these roles of each parameter,

    cevalPreserves≡ cmd st₁ st₂ st₁' st₂' st₁≡st₂ st₁=>st₁' st₂=>st₂'
                     |   \             /     |       |         |
                     |    \___________/      |       |         +-- Evidence that st₂ =[ c ]=> st₂'
                     |          |            |       |
                     |          |            |       +-- Evidence that st₁ =[ c ]=> st₁'
                     |          |            |
                     |          |            +-- Evidence that st₁ ≡ st₂
                     |          |     
                     |          +-- The four quantified states
                     |
                     +-- The quantified command

We proceed with a case analysis of the possible forms of statement.
The simplest case is for the no-operation command `skip`.

    cevalPreserves≡ skip st₁ st₂ st₁' st₂' st₁≡st₂ st₁=>st₁' st₂=>st₂' = ?

- The only evidence for the `_=[_]=>_` relation which pertains to the
   `skip` command is `Eskip`, so we can narrow the pattern for the
   `st₁=>st₁'` and `st₂=>st₂'` arguments to `Eskip` only.

       cevalPreserves≡ skip st₁ st₂ st₁' st₂' st₁≡st₂ Eskip Eskip = ?

 - In turn, the `Eskip` evidence tells us that the starting and ending
   states for each `_=[ skip ]=>_` relation _must be the same_.  So
   instead of giving distinct names to the `st₁'` and `st₂'`
   parameters, we can use a dot-pattern to assert the equalities among
   these values.

       cevalPreserves≡ skip st₁ st₂ .st₁ .st₂ st₁≡st₂ Eskip Eskip = ?

 - Our general goal for each of these clauses is to show that
   `st₁' ≡ st₂'`.  With the introduction of the dot-patterns,
   we have transformed that goal for _this_ clause to `st₁ ≡ st₂`.
   But this is exactly what the evidence of the `st₁≡st₂` argument
   demonstrates, so we can return that evidence for this clause.   

```
cevalPreserves≡ skip st₁ st₂ .st₁ .st₂ st₁≡st₂ Eskip Eskip = st₁≡st₂
```

Going forward it is important to keep in mind that we are
demonstrating an equality.  The evidence for this equality in the
previous `skip` clause was readily available, but it is more typical,
especially in inductive clauses, that we will need to build new
evience for the result.  The clause for the assignment statement `:=`
shows two typical techniques for establishing equality, both of which
we have seen in some form before.

 - We have frequently used equation blocks in the last chapter, and we
   see one here.  The evidence for justifications for the steps of
   this block is drawn from the arguments of the proof function.

 - Since the states whose equivalences we prove are on `TotalMap`
   functions, we will use the library of results from the
   [Section VerifExers]({{ site.baseurl }}/VerifExers/).

Once again we see that the form of command corresponds to only a
single form of evaluation evidence, and that that evidence in turn
restricts the possible forms of resulting states `st₁'` and `st₂'`.
Note that part of the evidence echoes part of the command: the
expression `a` appears explicitly in the evidence, and the local
dot-pattern in the evidence emphasizes that the expression must be the
same.  The expression `a` also appears implicitly a second time in
each piece of evidence, since it is a subject of the third element of
each `E:=` evidence value.  We use a `where` clause for readability,
to explicitly name a key element of the overall evidence.

```
cevalPreserves≡ (x := a) st₁ st₂ .( x ↦ n₁ , st₁ ) .( x ↦ n₂ , st₂ )
                st₁≡st₂ (E:= .a n₁ aEvalsToN₁) (E:= .a n₂ aEvalsToN₂) =
                  tSinglePoint≡Updates st₁ st₂ x n₁ n₂ st₁≡st₂ n₁≡n₂ 
                  where n₁≡n₂ : n₁ ≡ n₂
                        n₁≡n₂ = begin
                                  n₁
                                ≡⟨ sym aEvalsToN₁ ⟩ 
                                  (⟦ a ⟧ᴬ st₁)
                                ≡⟨ cong (⟦ a ⟧ᴬ_) st₁≡st₂ ⟩ 
                                  (⟦ a ⟧ᴬ st₂)
                                ≡⟨ aEvalsToN₂ ⟩
                                  n₂
                                ∎
```

In the result for sequential composition of commands, we are given the
existence of intermediate states which serve as the midpoint of
`_=[_]=>_`, as part of the evidence of the transition for the overall
composition.

          =[ c₁ ]=>           =[ c₂ ]=>
    st₁ -------------> stA -------------> st₁'
     |                  .                  .
     |                  .                  .
     | ≡                . ≡                . ≡
     |                  .                  .
     |                  .                  .
    st₂ -------------> stB -------------> st₂'
          =[ c₁ ]=>           =[ c₂ ]=>

The result follows by applying `cevalPreserves≡` for an induction
hypotehesis on each of the two steps of the reduction.  

```
cevalPreserves≡ (c₁ , c₂) st₁ st₂ st₁' st₂' st₁≡st₂
                (E, {stA} stStA stASt₁') (E, {stB} stStB stBSt₂') = 
  cevalPreserves≡ c₂ stA stB st₁' st₂' stA≡stB stASt₁' stBSt₂'
  where stA≡stB : stA ≡ stB
        stA≡stB = cevalPreserves≡ c₁ st₁ st₂ stA stB st₁≡st₂ stStA stStB
```

The next two clauses arise from `if`-commands.  Where the two states
`st₁` and `st₂` give the same result for the boolean condition `b`, we
have a simple inductive case on either `cTrue` or `cFalse`.

```
cevalPreserves≡ (if b then cTrue else cFalse end) st₁ st₂ st₁' st₂' st₁≡st₂
                (EIfT _ aEvalsToN₁) (EIfT _ aEvalsToN₂) =
  cevalPreserves≡ cTrue st₁ st₂ st₁' st₂' st₁≡st₂ aEvalsToN₁ aEvalsToN₂
cevalPreserves≡ (if b then cTrue else cFalse end) st₁ st₂ st₁' st₂' st₁≡st₂
                (EIfF _ aEvalsToN₁) (EIfF _ aEvalsToN₂) = 
  cevalPreserves≡ cFalse st₁ st₂ st₁' st₂' st₁≡st₂ aEvalsToN₁ aEvalsToN₂
```

The next two clauses also arise from `if`-commands, but these two
clauses — literally — do not make sense!  The clauses cover the
situations where the two evaluations of the condition `b`, one by
`st₁` and the other by `st₂`, give different results.  The reason we
say that there clauses do not make sense is that since `st₁ ≡ st₂`, as
we are given, we should also have that `⟦ b ⟧ᴮ st₁ ≡ ⟦ b ⟧ᴮ st₂`.  The
fact that we do not is a contradiction.  Since there is a
contradiction _in the setup_ of these clauses, we can use a technique
which tells Agda to disregard these clauses — that they are _absurd_.

Agda can rule out certain kinds of absurdity without our needing to
write an explicit clause for them.  One example of this kind of
absurdity would be one for a `skip` statement with `E,`-constructed
evidence: Agda notices that the statement forms are incompatible, and
does not expect to see such a clause.  But there are limits to the
reasoning that a system can make automatically, and Agda need us to
reveal the absurdity of these two clauses.

For Agda to acknowledge the absurdity of a clause, we must use the
evidence provided in that clause to construct evidence of a formula
that Agda can tell is impossible.  Here we use this construction:

    begin
      false
    ≡⟨ sym bIsFalse ⟩
      ⟦ b ⟧ᴮ st₂
    ≡⟨ cong (⟦ b ⟧ᴮ_) (sym st₁≡st₂) ⟩
      ⟦ b ⟧ᴮ st₁
    ≡⟨ bIsTrue ⟩
      true
    ∎

This proof has the type `false ≡ true`.  By combining the arguments to
the clause in this way, we produce a result that is clearly false to
Agda: Agda understands that different constructors of a type produce
values which **cannot** be equal.

Once we describe how to construct "evidence" of absurdity, we can use
that evidence in the structure

    case ( ... ) of λ ()

This structure asserts to Agda that it will never be possible to
invoke this clause, since calling the clause would involve
constructing impossible evidence.
 
```
cevalPreserves≡ (if b then c else c₁ end) st₁ st₂ _ _ st₁≡st₂
                (EIfT bIsTrue _) (EIfF bIsFalse _) =
  case (begin
          false
        ≡⟨ sym bIsFalse ⟩
          ⟦ b ⟧ᴮ st₂
        ≡⟨ cong (⟦ b ⟧ᴮ_) (sym st₁≡st₂) ⟩
          ⟦ b ⟧ᴮ st₁
        ≡⟨ bIsTrue ⟩
          true
        ∎) of λ ()
cevalPreserves≡ (if b then c else c₁ end) st₁ st₂ _ _ st₁≡st₂
                (EIfF bIsFalse _) (EIfT bIsTrue _) = 
  case (begin
          false
        ≡⟨ sym bIsFalse ⟩
          ⟦ b ⟧ᴮ st₁
        ≡⟨ cong (⟦ b ⟧ᴮ_) st₁≡st₂ ⟩
          ⟦ b ⟧ᴮ st₂
        ≡⟨ bIsTrue ⟩
          true
        ∎) of λ ()
```

There are four clauses related to `while` loops, mirroring the four
clauses for `if` blocks: two are applicable to real situations, and
two are absurd.  The real cases implement the two possibilities of the
loop condition evaluating to either `true` or `false`.

```
cevalPreserves≡ (while x loop c end) st₁ st₂ .st₁ .st₂ st₁≡st₂
                (EWhileF x₁) (EWhileF x₂) = st₁≡st₂
```

Note the pattern for the argument command in the `true` case:

    cmd@(while x loop c end)

This construction is called an _as-pattern_.  It allows us both to
refer to the argument as a whole through the name `cmd`, and to give
names to the components inside the argument.

```
cevalPreserves≡ cmd@(while x loop c end) st₁ st₂ st₁' st₂' st₁≡st₂
                (EWhileT {st₁*} _ st₁⇒st₁* st₁*⇒st₁')
                (EWhileT {st₂*} _ st₂⇒st₂* st₂*⇒st₂') = 
 cevalPreserves≡ cmd st₁* st₂* st₁' st₂' intermediates st₁*⇒st₁' st₂*⇒st₂'
 where intermediates : st₁* ≡ st₂*
       intermediates = cevalPreserves≡ c st₁ st₂ st₁* st₂* st₁≡st₂
                                        st₁⇒st₁* st₂⇒st₂*
```

Finally, these last two clauses address the absurd cases of different
results arising from the same boolean condition.

```
cevalPreserves≡ (while x loop c end) st₁ st₂ .st₁ st₂' st₁≡st₂
                (EWhileF xIsFalse) (EWhileT xIsTrue _ _) = 
  case (begin
          false
        ≡⟨ sym xIsFalse ⟩
          ⟦ x ⟧ᴮ st₁
        ≡⟨ cong (⟦ x ⟧ᴮ_) st₁≡st₂ ⟩
          ⟦ x ⟧ᴮ st₂
        ≡⟨ xIsTrue ⟩
          true
        ∎) of λ ()
cevalPreserves≡ (while x loop c end) st₁ st₂ _ _ st₁≡st₂
                (EWhileT xIsTrue _ _) (EWhileF xIsFalse) = 
  case (begin
          false
        ≡⟨ sym xIsFalse ⟩
          ⟦ x ⟧ᴮ st₂
        ≡⟨ cong (⟦ x ⟧ᴮ_) (sym st₁≡st₂) ⟩
          ⟦ x ⟧ᴮ st₁
        ≡⟨ xIsTrue ⟩
          true
        ∎) of λ ()
```

The determinism result we originally imagined is somewhat simpler than
the `cevalPreserves≡` lemma:

                st
               /  \
    =[ c ]=>  /    \  =[ c ]=>
             /      \
           st₁ - - - st₂
                 ≡
                 
But the proof determinism is immediate from the `cevalPreserves≡`
lemma, since every starting state is equal to itself.

```
cevalDeterministic : ∀ (c : Command) (st st₁ st₂ : State)
                       → st =[ c ]=> st₁  
                         → st =[ c ]=> st₂
                           -> st₁ ≡ st₂
cevalDeterministic c st st₁ st₂ = cevalPreserves≡ c st st st₁ st₂ refl
```

#### Exercise `cevalDeterministicRefl` (starting) {#cevalDeterministicRefl}

Why do we use `refl` as an argument in the body of `cevalDeterministic`?

#### Exercise `cevalDeterministicInformal` (starting) {#cevalDeterministicInformal}

To better understand the `cevalPreserves≡` and `cevalDeterministic`
proofs, write out the informal proofs of these results.

## Reasoning about Imp programs

{::comment}

LATER: This section doesn't seem very useful — to anybody!  It
takes too much time to go through it in class, and even for
advanced students it's too low-level and grubby to be a very
convincing motivation for what follows — i.e., to feel motivated
by its grubbiness, you have to understand it, but this takes more
time than it's worth.  Better to cut the whole rest of the
file (except the further exercises at the very end), or at least
make it optional.

(BCP 10/18: However, this removes quite a few exercises. Is the
homework assignment still meaty enough?  I'm going to leave it
as-is for now, but we should reconsider this later.) *)

{:/comment}

We'll get deeper into more systematic and powerful techniques for
reasoning about Imp programs in the next sections, but we can get some
distance just working with the bare definitions.  This section
explores some examples.

```
addingTwo : ∀ (st st' : State) (n : ℕ)
              → st X ≡ n
                → st =[ plus2 ]=> st'
                  → st' X ≡ n Data.Nat.+ 2
addingTwo st .( X ↦ n2 , st ) n xBoundToN
             (E:= {.st} {.X} .(id X + # 2) n2 aEvalN) = 
  begin
    ("X" ↦ n2 , st) X
  ≡⟨ cong (λ z → ("X" ↦ z , st) X) (sym aEvalN) ⟩
    ("X" ↦ (st X Data.Nat.+ 2) , st) X
  ≡⟨ tUpdateEq st X (st X Data.Nat.+ 2) ⟩
    st X Data.Nat.+ 2
  ≡⟨ cong (Data.Nat._+ 2) xBoundToN ⟩
    n Data.Nat.+ 2
  ∎
```

#### Exercise `XtimesYinZSpec` (practice) {#XtimesYinZSpec}

State and prove a similar specification of `XtimesYinZ`.

#### Exercise `loopNeverStops` (practice) {#loopNeverStops}

Prove this theorem about a nonterminating program:

```
postulate loopNeverStops : ∀ (st st' : State) → ¬ (st =[ forever ]=> st')
-- Remove the "postulate" keyword and add your proof code here
```

#### Exercise `noWhiles` (practice) {#noWhiles}

Consider the following function:

```
noWhiles : Command → Bool
noWhiles skip = true
noWhiles (x := x₁) = true
noWhiles (c , c₁) = noWhiles c ∧ noWhiles c₁
noWhiles if x then c else c₁ end = noWhiles c ∧ noWhiles c₁
noWhiles while x loop c end = false
```

This predicate yields `true` just on programs that have no while
loops.  Write a property `noWhilesR (c : Command) : Set` such that
`no_whilesR c` is provable exactly when `c` is a program with no while
loops.  Then prove its equivalence with `no_whiles`. 

#### Exercise `noWhilesTerminating` (stretch) {#noWhilesTerminating}

Imp programs that don't involve while loops always terminate.  State
and prove a theorem `noWhilesTerminating` that says this.

{::comment}

TODO --- Convert and un-comment

## Additional exercises 

(* EX3 (stack_compiler) *)
(** Old HP Calculators, programming languages like Forth and Postscript,
    and abstract machines like the Java Virtual Machine all evaluate
    arithmetic expressions using a _stack_. For instance, the expression
<<
      (2*3)+(3*(4-2))
>>
   would be written as
<<
      2 3 * 3 4 2 - * +
>>
   and evaluated like this (where we show the program being evaluated
   on the right and the contents of the stack on the left):
<<
      ` `           |    2 3 * 3 4 2 - * +
      `2`           |    3 * 3 4 2 - * +
      `3, 2`        |    * 3 4 2 - * +
      `6`           |    3 4 2 - * +
      `3, 6`        |    4 2 - * +
      `4, 3, 6`     |    2 - * +
      `2, 4, 3, 6`  |    - * +
      `2, 3, 6`     |    * +
      `6, 6`        |    +
      `12`          |
>>
  The goal of this exercise is to write a small compiler that
  translates `aexp`s into stack machine instructions.

  The instruction set for our stack language will consist of the
  following instructions:
     - `SPush n`: Push the number `n` on the stack.
     - `SLoad x`: Load the identifier `x` from the store and push it
                  on the stack
     - `SPlus`:   Pop the two top numbers from the stack, add them, and
                  push the result onto the stack.
     - `SMinus`:  Similar, but subtract the first number from the second.
     - `SMult`:   Similar, but multiply. *)

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

(** Write a function to evaluate programs in the stack language. It
    should take as input a state, a stack represented as a list of
    numbers (top stack item is the head of the list), and a program
    represented as a list of instructions, and it should return the
    stack after executing the program.  Test your function on the
    examples below.

    Note that it is unspecified what to do when encountering an
    `SPlus`, `SMinus`, or `SMult` instruction if the stack contains
    fewer than two elements.  In a sense, it is immaterial what we do,
    since a correct compiler will never emit such a malformed program.
    But for sake of later exercises, it would be best to skip the
    offending instruction and continue with the next one.  *)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat
  (* ADMITDEF *) :=
  match (prog, stack) with
  | (nil,             _           ) => stack
  | (SPush n::prog',  _           ) => s_execute st (n::stack) prog'
  | (SLoad x::prog',  _           ) => s_execute st (st x::stack) prog'
  | (SPlus::prog',    n::m::stack') => s_execute st ((m+n)::stack') prog'
  | (SMinus::prog',   n::m::stack') => s_execute st ((m-n)::stack') prog'
  | (SMult::prog',    n::m::stack') => s_execute st ((m*n)::stack') prog'
  | (_::prog',        _           ) => s_execute st stack prog'
                                       (* Bad state: skip *)
  end.
(* /ADMITDEF *)

Check s_execute.

Example s_execute1 :
     s_execute empty_st ``
       `SPush 5; SPush 3; SPush 1; SMinus`
   = `2; 5`.
(* ADMITTED *)
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
(* /ADMITTED *)
(* GRADE_THEOREM 1: s_execute1 *)

Example s_execute2 :
     s_execute (X ↦ 3) `3;4`
       `SPush 4; SLoad X; SMult; SPlus`
   = `15; 4`.
(* ADMITTED *)
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: s_execute2 *)

(** Next, write a function that compiles an `aexp` into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr
  (* ADMITDEF *) :=
  match e with
  | ANum n => `SPush n`
  | AId x => `SLoad x`
  | <{ a1 + a2 }> => s_compile a1 ++ s_compile a2 ++ `SPlus`
  | <{ a1 - a2 }>  => s_compile a1 ++ s_compile a2 ++ `SMinus`
  | <{ a1 * a2 }> => s_compile a1 ++ s_compile a2 ++ `SMult`
  end.
(* /ADMITDEF *)

(** After you've defined `s_compile`, prove the following to test
    that it works. *)

Example s_compile1 :
  s_compile <{ X - (2 * Y) }>
  = `SLoad X; SPush 2; SLoad Y; SMult; SMinus`.
(* ADMITTED *)
Proof. reflexivity. Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1.5: s_compile1 *)
(** `` *)

(* EX3 (execute_app) *)

(** Execution can be decomposed in the following sense: executing
    stack program `p1 ++ p2` is the same as executing `p1`, taking
    the resulting stack, and executing `p2` from that stack. Prove
    that fact. *)

Theorem execute_app : forall st p1 p2 stack,
    s_execute st stack (p1 ++ p2) = s_execute st (s_execute st stack p1) p2.
Proof.
  (* ADMITTED *)
  intros st. induction p1.
  - reflexivity.
  - intros p2 stack. destruct a; simpl; try apply IHp1;
    destruct stack as ` | x ` | y t ` `; simpl; try apply IHp1.
Qed.
(* /ADMITTED *)

(** `` *)

(* EX3 (stack_compiler_correct) *)

(* HIDE: MRC'20: this had been a 4-star advanced exercise.  I think
   it's a shame to relegate this to the advanced track, because it's
   really the payoff of this entire chapter.  Everyone deserves to
   prove the correctness of this little compiler!  It's such a
   rewarding, compelling result to prove.  In Spring 2019 I used the
   decomposition here, including the previous exercise, and students
   generally were successful. I'd like to propose making it the
   standard version. *)

(* HIDE: Adam Chlipala's book has a slicker solution which does it all
   in a single induction... APT: Slicker, but arguably harder to
   understand. *)

(** Now we'll prove the correctness of the compiler implemented in the
    previous exercise.  Begin by proving the following lemma. If it
    becomes difficult, consider whether your implementation of
    `s_execute` or `s_compile` could be simplified. *)

Lemma s_compile_correct_aux : forall st e stack,
  s_execute st stack (s_compile e) = aeval st e :: stack.
Proof.
  (* ADMITTED *)
  induction e;
    try reflexivity ; (* Push, Load *)
    intros; simpl;   (* Plus, Minus, Mult *)
      repeat rewrite execute_app;
      rewrite IHe1; rewrite IHe2; simpl; reflexivity.
Qed.
(* /ADMITTED *)

(** The main theorem should be a very easy corollary of that lemma. *)

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st `` (s_compile e) = ` aeval st e `.
Proof.
  (* ADMITTED *)
  intros. apply s_compile_correct_aux.
Qed.
(* /ADMITTED *)

(* GRADE_THEOREM 2.5: s_compile_correct_aux *)
(* GRADE_THEOREM 0.5: s_compile_correct *)

(** `` *)

(* TERSE: /HIDEFROMHTML *)

(* FULL *)
(* EX3? (short_circuit) *)
(** Most modern programming languages use a "short-circuit" evaluation
    rule for boolean `and`: to evaluate `BAnd b1 b2`, first evaluate
    `b1`.  If it evaluates to `false`, then the entire `BAnd`
    expression evaluates to `false` immediately, without evaluating
    `b2`.  Otherwise, `b2` is evaluated to determine the result of the
    `BAnd` expression.

    Write an alternate version of `beval` that performs short-circuit
    evaluation of `BAnd` in this manner, and prove that it is
    equivalent to `beval`.  (N.b. This is only true because expression
    evaluation in Imp is rather simple.  In a bigger language where
    evaluating an expression might diverge, the short-circuiting `BAnd`
    would _not_ be equivalent to the original, since it would make more
    programs terminate.) *)

(* SOLUTION *)
Fixpoint beval_sc (st : state) (e : bexp) : bool :=
  match e with
  | <{ true }>       => true
  | <{ false }>      => false
  | <{ a1 = a2 }>    => (aeval st a1) =? (aeval st a2)
  | <{ a1 <= a2 }>   => (aeval st a1) <=? (aeval st a2)
  | <{ ~ b1 }>       => negb (beval_sc st b1)
  | <{ b1 && b2 }>   =>  match (beval_sc st b1) with
                         | false => false
                         | true  => (beval_sc st b2)
                         end
  end.

(* This exercise turned out to be easier than we intended! *)
Theorem beval__beval_sc : forall st e,
  beval st e = beval_sc st e.
Proof.
  intros st e.
  destruct e; reflexivity.
Qed.
(* /SOLUTION *)
(** `` *)

Module BreakImp.
(* EX4A (break_imp) *)
(** Imperative languages like C and Java often include a `break` or
    similar statement for interrupting the execution of loops. In this
    exercise we consider how to add `break` to Imp.  First, we need to
    enrich the language of commands with an additional case. *)

Inductive com : Type :=
  | CSkip
  | CBreak                        (* <--- NEW *)
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'break'" := CBreak (in custom com at level 0).
(* INSTRUCTORS: Copy of template com *)
Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAss x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

(** Next, we need to define the behavior of `break`.  Informally,
    whenever `break` is executed in a sequence of commands, it stops
    the execution of that sequence and signals that the innermost
    enclosing loop should terminate.  (If there aren't any
    enclosing loops, then the whole program simply terminates.)  The
    final state should be the same as the one in which the `break`
    statement was executed.

    One important point is what to do when there are multiple loops
    enclosing a given `break`. In those cases, `break` should only
    terminate the _innermost_ loop. Thus, after executing the
    following...
``
       X := 0;
       Y := 1;
       while ~(0 = Y) do
         while true do
           break
         end;
         X := 1;
         Y := Y - 1
       end
``
    ... the value of `X` should be `1`, and not `0`.

    One way of expressing this behavior is to add another parameter to
    the evaluation relation that specifies whether evaluation of a
    command executes a `break` statement: *)

Inductive result : Type :=
  | SContinue
  | SBreak.

(* INSTRUCTORS: Copy of template eval *)
Reserved Notation "st '=`' c '`=>' st' '/' s"
     (at level 40, c custom com at level 99, st' constr at next level).

(** Intuitively, `st =[ c ]=> st' / s` means that, if `c` is started in
    state `st`, then it terminates in state `st'` and either signals
    that the innermost surrounding loop (or the whole program) should
    exit immediately (`s = SBreak`) or that execution should continue
    normally (`s = SContinue`).

    The definition of the "`st =[ c ]=> st' / s`" relation is very
    similar to the one we gave above for the regular evaluation
    relation (`st =[ c ]=> st'`) — we just need to handle the
    termination signals appropriately:

    - If the command is `skip`, then the state doesn't change and
      execution of any enclosing loop can continue normally.

    - If the command is `break`, the state stays unchanged but we
      signal a `SBreak`.

    - If the command is an assignment, then we update the binding for
      that variable in the state accordingly and signal that execution
      can continue normally.

    - If the command is of the form `if b then c1 else c2 end`, then
      the state is updated as in the original semantics of Imp, except
      that we also propagate the signal from the execution of
      whichever branch was taken.

    - If the command is a sequence `c1 ; c2`, we first execute
      `c1`.  If this yields a `SBreak`, we skip the execution of `c2`
      and propagate the `SBreak` signal to the surrounding context;
      the resulting state is the same as the one obtained by
      executing `c1` alone. Otherwise, we execute `c2` on the state
      obtained after executing `c1`, and propagate the signal
      generated there.

    - Finally, for a loop of the form `while b do c end`, the
      semantics is almost the same as before. The only difference is
      that, when `b` evaluates to true, we execute `c` and check the
      signal that it raises.  If that signal is `SContinue`, then the
      execution proceeds as in the original semantics. Otherwise, we
      stop the execution of the loop, and the resulting state is the
      same as the one resulting from the execution of the current
      iteration.  In either case, since `break` only terminates the
      innermost loop, `while` signals `SContinue`. *)

(** Based on the above description, complete the definition of the
    `ceval` relation. *)

(* SOLUTION *)

(** Because we include if syntax for the if syntax in com,
    we cannot use typical coq if syntax. We avoid this issues
    by making a function that encodes the behavior of if *)
if_then_else {A : Type} (b : bool) (l r : A) :=
  if b then l else r.

(* /SOLUTION *)

Inductive ceval : com -> state -> result -> state -> Prop :=
  | ESkip : forall st,
      st =[ CSkip ]=> st / SContinue
  (* SOLUTION *)
  | EBreak : forall st,
      st =[ CBreak ]=> st / SBreak
  | EAsgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (X ↦ n ; st) / SContinue
  | ESeqContinue : forall c1 c2 st st' st'' s,
      st =[ c1 ]=> st' / SContinue ->
      st' =[ c2 ]=> st'' / s ->
      st =[ c1 ; c2 ]=> st'' / s
  | ESeqBreak : forall c1 c2 st st',
      st =[ c1 ]=> st' / SBreak ->
      st =[ c1 ; c2 ]=> st' / SBreak
  | EIf : forall c1 c2 b st st' s,
      st =[ if_then_else (⟦ b ⟧ᴮ st) c1 c2 ]=> st' / s ->
      st =[ if b then c1 else c2 end ]=> st' / s
  | EWhileFalse : forall c b st,
      ⟦ b ⟧ᴮ st = false ->
      st =[ while b do c end ]=> st / SContinue
  | EWhileContinue : forall c b st st' st'',
      ⟦ b ⟧ᴮ st = true ->
      st  =[ c ]=> st' / SContinue ->
      st' =[ while b do c end ]=> st'' / SContinue ->
      st  =[ while b do c end ]=> st'' / SContinue
  | EWhileBreak : forall c b st st',
      ⟦ b ⟧ᴮ st = true ->
      st =[ c ]=> st' / SBreak ->
      st =[ while b do c end ]=> st' / SContinue
  (* /SOLUTION *)

  where "st '=`' c '`=>' st' '/' s" := (ceval c st s st').

(** Now prove the following properties of your definition of `ceval`: *)

Theorem break_ignore : forall c st st' s,
     st =[ break; c ]=> st' / s ->
     st = st'.
Proof.
  (* ADMITTED *)
  intros c st st' s H.
  inversion H; clear H; subst.
  inversion H2.
  inversion H5. subst. reflexivity.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1.5: break_ignore *)

Theorem while_continue : forall b c st st' s,
  st =[ while b do c end ]=> st' / s ->
  s = SContinue.
Proof.
  (* ADMITTED *)
  intros b c st st' s H. inversion H; reflexivity.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1.5: while_continue *)

Theorem while_stops_on_break : forall b c st st',
  ⟦ b ⟧ᴮ st = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ while b do c end ]=> st' / SContinue.
Proof.
  (* ADMITTED *)
  intros b c st st' H1 H2.
  apply EWhileBreak; assumption.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: while_stops_on_break *)
(** `` *)

(* EX3A? (while_break_true) *)
Theorem while_break_true : forall b c st st',
  st =[ while b do c end ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
(* ADMITTED *)
  intros b c st st' H Hb.
  remember <{ while b do c end }> as c'.
  induction H; inversion Heqc'; clear Heqc'; subst.
  - (* EWhileFalse *)
    rewrite Hb in H. discriminate H.
  - (* EWhileContinue *)
    clear IHceval1.
    apply IHceval2. reflexivity. assumption.
  - (* EWhileBreak *)
    exists st. assumption.
Qed.
(* /ADMITTED *)
(** `` *)

(* EX4A? (ceval_deterministic) *)
Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     st =[ c ]=> st1 / s1 ->
     st =[ c ]=> st2 / s2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  (* ADMITTED *)
  intros c st st1 st2 s1 s2 E1 E2.
  generalize dependent s2.
  generalize dependent st2.
  induction E1;
    intros st2 s2 E2;
    inversion E2; clear E2; subst;
(* HIDE:
   BCP: This proof could be better automated in general.
   AAA: The problem with this proof is that it is somewhat hard to automate
        without using `match`, which we haven't told them about yet. Each
        branch needs hypotheses with different names. Furthermore, `apply`
        by itself doesn't quite work as well, because we need to substitute
        some values in order for the unification to work. This is what I was
        able to do.
 *)
    try (rewrite H in H2; inversion H2);
    try (rewrite H in H5; inversion H5);
    try (apply IHE1_1 in H1; destruct H1 as `H11 H12`; try subst);
    try (apply IHE1_2 in H5; destruct H5 as `H51 H52`; try subst);
    try (apply IHE1_1 in H4; destruct H4 as `H41 H42`; inversion H42);
    try (apply IHE1 in H1; destruct H1 as `H11 H12`; try subst; inversion H12);
    try (apply IHE1 in H4; destruct H4 as `H41 H42`; try subst; inversion H42);
    try (apply IHE1_1 in H3; destruct H3 as `H31 H32`; try subst; inversion H32);
    try (apply IHE1_1 in H6; destruct H6 as `H61 H62`; try subst; inversion H62);
    try (apply IHE1_2 in H7; destruct H7 as `H71 H72`; try subst; inversion H72);
    try (apply IHE1 in H3; destruct H3 as `H31 H32`; try subst; inversion H32);
    try (apply IHE1 in H6; destruct H6 as `H61 H62`; try subst; inversion H62);
    try (split; reflexivity).
  - (* EIf *)
    apply IHE1. assumption.
Qed.
(* /ADMITTED *)

(** `` *)
End BreakImp.

(* HIDE *)
(* LATER: Should this exercise be un-hidden?  It needs a tiny bit
   more material to be really interesting, though it also leads to a
   very interesting exercise in Hoare2... *)
(* EX4A? (exn_imp) *)
Module ThrowImp.

(** Many programming languages include mechanisms for raising and
    handling exceptions.  In this problem (a variant of the above
    exercises on `break`), we'll experiment with a very simple
    version, with just a single exception called `THROW`.  First, we
    need to enrich the language of commands with an additional case
    for raising the `THROW` exception and a case for catching it. *)

Inductive com : Type :=
  | CSkip
  | CThrow                       (* <--- NEW *)
  | CTry (c1 c2 : com)           (* <--- NEW *)
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 x2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'throw'" := CThrow (in custom com at level 0).
Notation "'try' c1 'catch' c2 'end'" :=
         (CTry c1 c2)
            (in custom com at level 0,
             c1 custom com at level 99, c2 custom com at level 99).
(* INSTRUCTORS: Copy of template com *)
Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAss x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

(** Next, we need to define the behavior of `THROW`.  Informally,
    whenever `THROW` is executed, we immediately stop executing this
    command and start executing the `else` clause of the closest
    enclosing `try`.

    A simple way of achieving this effect is to add another parameter
    to the evaluation relation that specifies whether evaluation of a
    command executes a `THROW` statement: *)

Inductive status : Type :=
  | SNormal
  | SThrow.

(** Intuitively, `st =[ c ]=> st' / s` means that, if `c` is started in
    state `st`, then it terminates in state `st'` and either signals
    that an exception has been raised (`s = SThrow`) or that execution
    can continue normally (`s = SNormal`).

    - If the command is `skip`, then the state doesn't change and
      execution of any enclosing loop can continue normally.

    - If the command is `THROW`, the state stays unchanged but we
      signal a `SThrow`.

    - If the command is `try`, we begin by executing the first
      subcommand; if it terminates normally, then the whole `try`
      terminates in the same state; if it terminates with an
      exception, we execute the second subcommand instead.

    - If the command is an assignment, then we update the binding for
      that variable in the state accordingly and signal that execution
      can continue normally.

    - If the command is of the form `if b then c1 else c2 end`, then
      the state is updated as in the original semantics of Imp, except
      that we also propagate the signal from the execution of
      whichever branch was taken.

    - If the command is a sequence `c1 ; c2`, we first execute `c1`.
      If this yields a `SThrow`, we skip the execution of `c2` and
      propagate the `SThrow` signal to the surrounding context; the
      resulting state is the same as the one obtained by executing
      `c1` alone. Otherwise, we execute `c2` on the state obtained
      after executing `c1`, and propagate the signal generated there.

    - Finally, for a loop of the form `while b do c end`, when `b`
      evaluates to true, we execute `c` and check the signal that it
      raises.  If that signal is `SNormal`, the execution proceeds
      as in the original semantics. Otherwise, we stop the execution
      of the loop and signal `SThrow`. *)


(* SOLUTION *)

(** Because we include if syntax for the if syntax in com,
    we cannot use typical coq if syntax. We avoid this issues
    by making a function that encodes the behavior of if *)
if_then_else {A : Type} (b : bool) (l r : A) :=
  if b then l else r.

(* /SOLUTION *)

(** Based on the above description, complete the definition of the
    `ceval` relation. *)

(* INSTRUCTORS: Copy of template eval *)
Reserved Notation "st '=`' c '`=>' st' '/' s"
         (at level 40, c custom com at level 99, st' constr at next level).

(* SOONER: The EWhileContinue case in this solution should have `s`,
   not `SNormal`, in the last two lines — see fixed version in
   comment.  This will require a bit of fixing proofs. *)
Inductive ceval : com -> state -> status -> state -> Prop :=
  | ESkip : forall st,
      st =[ CSkip ]=> st / SNormal
  (* SOLUTION *)
  | EThrow : forall st,
      st =[ CThrow ]=> st / SThrow
  | ETryContinue : forall c1 c2 st st',
      st =[ c1 ]=> st' / SNormal ->
      st =[ try c1 catch c2 end ]=> st' / SNormal
  | ETryThrow : forall c1 c2 st st' st'' s,
      st  =[ c1 ]=> st'  / SThrow ->
      st' =[ c2 ]=> st'' / s ->
      st  =[ try c1 catch c2 end ]=> st'' / s
  | EAsgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (X ↦ n ; st) / SNormal
  | ESeqContinue : forall c1 c2 st st' st'' s,
      st  =[ c1 ]=> st'  / SNormal ->
      st' =[ c2 ]=> st'' / s ->
      st  =[ c1 ; c2 ]=> st'' / s
  | ESeqThrow : forall c1 c2 st st',
      st =[ c1 ]=> st' / SThrow ->
      st =[ c1 ; c2 ]=> st' / SThrow
  | EIf : forall c1 c2 b st st' s,
      st =[ if_then_else (⟦ b ⟧ᴮ st) c1 c2 ]=> st' / s ->
      st =[ if b then c1 else c2 end ]=> st' / s
  | EWhileFalse : forall c b st,
      ⟦ b ⟧ᴮ st = false ->
      st =[ while b do c end ]=> st / SNormal
  | EWhileContinue : forall c b st st' st'',
      ⟦ b ⟧ᴮ st = true ->
      st  =[ c ]=> st' / SNormal ->
      st' =[ while b do c end ]=> st'' / SNormal ->
      st  =[ while b do c end ]=> st'' / SNormal
(* HIDE: BETTER version!
  | EWhileContinue : forall c b st st' st'' s,
      ⟦ b ⟧ᴮ st = true ->
      c / st ==> SNormal / st' ->
      (while b do c end) / st' ==> s / st'' ->
      (while b do cend) / st ==> s / st''
*)
  | EWhileThrow : forall c b st st',
      ⟦ b ⟧ᴮ st = true ->
      st =[ c ]=> st' / SThrow ->
      st =[ while b do c end ]=> st' / SThrow
  (* /SOLUTION *)

  where "st '=`' c '`=>' st' '/' s" := (ceval c st s st').

(** Now prove the following properties of your definition of `ceval`: *)

(* LATER: It would be good to have some examples that verify
   that their implementation does the right thing on a few unit
   tests! *)

Theorem ceval_deterministic_throw: forall (c:com) st st1 st2 s1 s2,
     st =[ c ]=> st1 / s1 ->
     st =[ c ]=> st2 / s2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  (* ADMITTED *)
  intros c st st1 st2 s1 s2 E1 E2.
  generalize dependent s2.
  generalize dependent st2.
  induction E1;
    intros st2 s2 E2;
    inversion E2; clear E2; subst;
(* LATER: see comments in the break exercise *)
    try (rewrite H in H2; inversion H2);
    try (rewrite H in H5; inversion H5);
    try (apply IHE1_1 in H1; destruct H1 as `H11 H12`; try subst);
    try (apply IHE1_2 in H5; destruct H5 as `H51 H52`; try subst);
    try (apply IHE1_1 in H4; destruct H4 as `H41 H42`; inversion H42);
    try (apply IHE1 in H1; destruct H1 as `H11 H12`; try subst; inversion H12);
    try (apply IHE1 in H4; destruct H4 as `H41 H42`; try subst; inversion H42);
    try (apply IHE1_1 in H3; destruct H3 as `H31 H32`; try subst; inversion H32);
    try (apply IHE1_1 in H6; destruct H6 as `H61 H62`; try subst; inversion H62);
    try (apply IHE1_2 in H7; destruct H7 as `H71 H72`; try subst; inversion H72);
    try (apply IHE1 in H3; destruct H3 as `H31 H32`; try subst; inversion H32);
    try (apply IHE1 in H6; destruct H6 as `H61 H62`; try subst; inversion H62);
    try (split; reflexivity).
  - (* EIf *)
    apply IHE1. assumption.
Qed.
(* /ADMITTED *)

End ThrowImp.
(** `` *)
(* /HIDE *)

(* EX4? (add_for_loop) *)
(** Add C-style `for` loops to the language of commands, update the
    `ceval` definition to define the semantics of `for` loops, and add
    cases for `for` loops as needed so that all the proofs in this
    file are accepted by Agda.

    A `for` loop should be parameterized by (a) a statement executed
    initially, (b) a test that is run on each iteration of the loop to
    determine whether the loop should continue, (c) a statement
    executed at the end of each loop iteration, and (d) a statement
    that makes up the body of the loop.  (You don't need to worry
    about making up a concrete Notation for `for` loops, but feel free
    to play with this too if you like.) *)

(* SOLUTION *)
(* (Providing a solution for this exercise would involve changes
   in many places, so we'll leave this one to you!) *)
(* /SOLUTION *)
(** `] *)
(* /FULL *)

(* HIDE *)
(* Local Variables: *)
(* fill-column: 70 *)
(* outline-regexp: "(\\*\\* \\*+" *)
(* End: *)
(* mode: outline-minor *)
(* /HIDE *)

{:/comment}

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

*This page is derived from Pierce et al. with additional explanations
and exercises by Maraist; for more information see the [sources and
authorship]({{ site.baseurl }}/Sources/) page.*
