---
title     : "ImpExprs: Expression and values in Imp"
layout    : page
prev      : /MapProps/
permalink : /ImpExprs/
next      : /Imp/
---

```
module plc.imp.ImpExprs where
open import Data.String using (String) renaming (_==_ to _string=_)
open import Data.Nat using (ℕ; _∸_; _≡ᵇ_; _<ᵇ_; zero; suc)
open import Data.Bool using (Bool; true; false; not; _∨_; _∧_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import plc.fp.Maps using (TotalMap; _↦_,_; ↪)
open import plc.vfp.Relations using (_⇔_)
```

In this chapter we take a more serious look at how to use Agda to
study other things.  Our case study is a simple _imperative
programming language_ called Imp, embodying a tiny core fragment of
conventional mainstream languages such as C and Java.  Here is a
familiar mathematical function written in Imp.

    Z := X ,
    Y := # 1 ,
    while ~(Z == # 0) do
      Y := Y * Z ,
      Z := Z - # 1
    end

We concentrate here on defining the _syntax_ of Imp, and on how we
calculate the values of its _expressions_.  In the next section we
define the _semantics_ of its commands.  Then in later sections will
develop a theory of _program equivalence_ and introduce _Hoare Logic_,
a widely used logic for reasoning about imperative programs.

## Compilers, interpreters and parsing

{::comment}
(* LATER: At this point, I usually take some of the lecture time to
   give a high-level picture of the structure of an interpreter, the
   processes of lexing and parsing, the notion of ASTs, etc.  Might be
   nice to work some of those ideas into the notes. - BCP *)
{:/comment}

Compilers and interpreters have very similar structure internally.
Both of them are complicated programs, written with multiple _phases_
along the way from the plain text in which a human writes a program,
on the way to the output of machine code.  Usually, the first two
phases of the compiler are _scanning_ and _parsing_.

 - Scanning is the process of dividing the characters of an input file
   into _lexemes_, the basic units of a language: keywords like
   `module` or `import`, identifiers like `x` or `y`, numbers and
   other constants like `0` or `99`, punctuation like `;` or `.`.
   Another type of lexeme is whitespace.  In many languages (like Java
   or C) whitespace is simply ignored, while in Agda whitespace does
   impact the meaning of a program.

 - Parsing is the process of converting an unstructured, linear
   sequence of lexemes to a structured representation of a program's
   syntax (that is, a data structure) called an _abstract syntax tree_
   (AST).  For example, the AST for an assignment statement would have
   one child representing the left-hand side of the assignment, the
   location being assigned to, and another child representing the
   right-hand side of the assignment, the expression whose value
   should be assigned.

Scanning and parsing are interesting and challenging problems, but
they are not problems which we will consider in this class.  To simply
our study and focus on the meaning of languages, we will instead
construct ASTs directly.  Agda's flexible syntax will allow us to
write the ASTs in a way which looks like the source code: essentially,
we will exploit Agda's own parser to serve as the parser for Imp.

## Arithmetic and boolean expressions

We'll present Imp in three parts: first a core language of _arithmetic
and boolean expressions_, then an extension of these expressions with
_variables_, and finally a language of _commands_ including
assignment, conditions, sequencing, and loops.

### Formal and informal representations

How do we describe the syntax of a language?  As we discussed above,
we will define its representation within Agda, its syntax trees, as
data structures.  But how do we define the way a string of characters
which is part of the language should look?  One way is with a notation
called _Backus-Naur Form_ (BNF), which is a way of writing a _formal
grammar_.  Here is a BNF defining the syntax of arithmetic and boolean
expressions in IMP:

    a := n        where n ∈ ℕ
       | a + a
       | a - a
       | a * a

    b := T
       | F
       | a == a
       | a <= a
       | ! b
       | b && b
       | b || b

 - The `a` and `b` are called the _nonterminals_ of the grammar.
   Those two letters do not directly appear in any of the actual
   arithmetic or boolean expressions we are defining.  They are
   stand-ins which we use in other parts of the BNF.

 - When we write `x := S`, where `x` is a nonterminal and `S` is a
   string, we say that a string represented by `S` could take the form
   given by the string `S`.  `S` might contain other nonterminals, in
   which case we might recursively apply our understanding of what
   those nonterminals might represent.  At least some of the time, `S`
   will contain _terminal_ symbols, which do not represent anything
   else.  In the BNF above, `+`, `-`, `*`, `==`, `<=`, `!`, `&&` and
   `||` are all terminals.  We use the representation `n where n ∈ ℕ`
   to stand for several different terminals, but none of them are
   further rewritten.

 - So applying the understanding we have from the BNFs, we can see
   that `32 + 45` and `5 - 2 - 1` are both arithmetic expressions,
   that `T && F || ! F` and `3 == 4 || 3 <= 4` are both boolean
   expressions, and that `5 * T` is neither a boolean nor an
   arithmetic expression.

In some ways, a BNF is quite informal.  It does gives suggestions
about the surface syntax of expressions, like the fact that the
addition operation is written with an infix `+`.  But it also leaves
other aspects of lexical analysis and parsing unspecified, like the
relative precedence of `+`, `-`, and `*`, and the use of parentheses
to group subexpressions.  Some additional information — and human
intelligence — would be required to turn this description into a
formal definition, such as for implementing a compiler.

In other ways the BNF version is light and easy to read.  It is not
tied to any particular language's syntax, as we will shortly do when
we translate the BNFs to Agda data types.  Its informality makes it
flexible, a big advantage in situations like discussions at the
blackboard, where conveying general ideas is more important than
getting every detail nailed down precisely.

Indeed, there are dozens of BNF-like notations and people switch
freely among them, usually without bothering to say which kind of BNF
they're using because there is no need to: a rough-and-ready informal
understanding is all that's important.

From the BNFs we can formally define the _abstract syntax_ of
arithmetic and boolean expressions:

```
module ImpStage1 where
  data AExp : Set where
    # : ℕ → AExp
    _+_ : AExp → AExp → AExp 
    _-_ : AExp → AExp → AExp 
    _*_ : AExp → AExp → AExp 

  infixl 7  _*_
  infixl 6  _+_  _-_

  data BExp : Set where
    T : BExp
    F : BExp
    _==_ : AExp → AExp → BExp
    _<=_ : AExp → AExp → BExp
    ! : BExp → BExp
    _&&_ : BExp → BExp → BExp
    _||_ : BExp → BExp → BExp

  infixl 8  _&&_
  infixl 7  _||_
```

It is good to be comfortable with both sorts of notations: informal
notations like BNF for communicating between humans, and formal
notations like `data` declarations for carrying out implementations
and proofs.

### Evaluating expressions

_Evaluating_ an arithmetic expression produces a number.  Evaluation
is, of course, a function from arithmetic expressions to natural
numbers.  It is traditional to write functions which we understand as
a translation or interpretation from one representation to another in
a special way: using a pair of double-brackets, `⟦ ... ⟧`. with the
argument in the middle.  For the arithmetic expression evaluator, we
append a superscript `ᵃ` to the closing double-bracket.  Agda lets us
define these envelope-style functions using a similar method as for
infix operations, where we use the underscore to stand in the argument
position in the signature.

```
  ⟦_⟧ᴬ : AExp → ℕ
  ⟦ # n ⟧ᴬ = n
  ⟦ ae1 + ae2 ⟧ᴬ = ⟦ ae1 ⟧ᴬ Data.Nat.+ ⟦ ae2 ⟧ᴬ
  ⟦ ae1 - ae2 ⟧ᴬ = ⟦ ae1 ⟧ᴬ ∸ ⟦ ae2 ⟧ᴬ
  ⟦ ae1 * ae2 ⟧ᴬ = ⟦ ae1 ⟧ᴬ Data.Nat.* ⟦ ae2 ⟧ᴬ
```

Note that since we have defined our own version of `+` and `*` for
this module, we must explicitly clarify when we want to use the
version of `+` declared within the `Data.Nat` module.  We did import
the `∸` operator from `Data.Nat`, so we can use it without the module
prefix.

Similarly, evaluating a boolean expression yields a boolean.

```
  ⟦_⟧ᴮ : BExp → Bool
  ⟦ T ⟧ᴮ = true
  ⟦ F ⟧ᴮ = false
  ⟦ (ae1 == ae2) ⟧ᴮ = ⟦ ae1 ⟧ᴬ ≡ᵇ ⟦ ae2 ⟧ᴬ
  ⟦ (ae1 <= ae2) ⟧ᴮ = (v1 ≡ᵇ v2) ∨ (v1 <ᵇ v2)
                       where v1 : ℕ
                             v1 = ⟦ ae1 ⟧ᴬ
                             v2 : ℕ
                             v2 = ⟦ ae2 ⟧ᴬ
  ⟦ ! be ⟧ᴮ = not ⟦ be ⟧ᴮ
  ⟦ be1 && be2 ⟧ᴮ = ⟦ be1 ⟧ᴮ ∧ ⟦ be2 ⟧ᴮ
  ⟦ be1 || be2 ⟧ᴮ = ⟦ be1 ⟧ᴮ ∨ ⟦ be2 ⟧ᴮ
```

Notice that the boolean evaluator calls the arithmetic evaluator for
the comparison operators `==` and `<=`.  These operators take numeric
arguments, but return a boolean result.

#### Exercise `impeval1` (starting) {#impeval1}

What do these Imp expression evaluate to?  Which evaluation function
must you use for each?

 - `# 3 + (# 4 - # 1)`
 - `# 3 + # 4 * # 5`
 - `(# 4 - # 1) <= # 5`

### Optimization

We haven't defined very much yet, but we can already get some mileage
out of the definitions.  Suppose we define a function that takes an
arithmetic expression and slightly simplifies it, changing every
occurrence of `0 + e` (i.e., `# 0 + e`) into just `e`.

```
  optimize0plus : AExp → AExp
  optimize0plus ae@(# n) = ae
  optimize0plus (# 0 + ae2) = optimize0plus ae2
  optimize0plus (ae1 + ae2) = optimize0plus ae1 + optimize0plus ae2
  optimize0plus (ae1 - ae2) = optimize0plus ae1 - optimize0plus ae2
  optimize0plus (ae1 * ae2) = optimize0plus ae1 * optimize0plus ae2
```

To make sure our optimization is doing the right thing we can test it
on some examples.

```
  _ : optimize0plus (# 2 + (# 0 + (# 0 + # 1))) ≡ # 2 + # 1
  _ = refl

  _ : optimize0plus (# 2 + # 1) ≡ # 2 + # 1
  _ = refl
```

The second example shows that when there are no optimizations to
perform, `optimize0plus` leaves the expression alone.

But if we want to be sure that the optimization is correct — that
evaluating an optimized expression gives the same result as the
original — we should prove it.

{::comment}
  s1 : (x : AExp) → (y : AExp) →
         ⟦ optimize0plus (x * y) ⟧ᴬ ≡
           ⟦ optimize0plus x * optimize0plus y ⟧ᴬ
  s1 x y =
    begin
      ⟦ optimize0plus (x * y) ⟧ᴬ
    ≡⟨ refl ⟩
      ⟦ optimize0plus x * optimize0plus y ⟧ᴬ
    ∎
      

  o0pS_op : ∀ { x y : AExp } →
              (k : AExp → AExp → AExp) → (f : ℕ → ℕ → ℕ) →
                opt0+safe x → opt0+safe y →
                  (∀ { m n : AExp } → ⟦ k m n ⟧ᴬ ≡ f ⟦ m ⟧ᴬ ⟦ n ⟧ᴬ) → 
                    (optimize0plus (k x y) ≡ k (optimize0plus x) (optimize0plus y)) →
                      opt0+safe (k x y)
  o0pS_op {x} {y} k f sx sy kf kdown = 
    begin
      ⟦ optimize0plus (k x y) ⟧ᴬ
    ≡⟨ cong aeval kdown ⟩
      ⟦ k (optimize0plus x) (optimize0plus y) ⟧ᴬ
    ≡⟨ kf ⟩
      f ⟦ optimize0plus x ⟧ᴬ ⟦ optimize0plus y ⟧ᴬ
    ≡⟨ cong (λ x → f x ⟦ optimize0plus y ⟧ᴬ) sx ⟩
      f ⟦ x ⟧ᴬ ⟦ optimize0plus y ⟧ᴬ
    ≡⟨ cong (f ⟦ x ⟧ᴬ) sy ⟩
      f ⟦ x ⟧ᴬ ⟦ y ⟧ᴬ
    ≡⟨ sym kf ⟩
      ⟦ k x y ⟧ᴬ
    ∎
{:/comment}

```
  opt0+safe : AExp → Set
  opt0+safe m = ⟦ optimize0plus m ⟧ᴬ ≡ ⟦ m ⟧ᴬ

  plusHelper : (m n : AExp) →
                 opt0+safe m → opt0+safe n →
                   (optimize0plus (m + n) ≡ optimize0plus m + optimize0plus n) →
                     opt0+safe (m + n)
  plusHelper m n sm sn nonz = begin
      ⟦ optimize0plus (m + n) ⟧ᴬ
    ≡⟨ cong ⟦_⟧ᴬ nonz ⟩
      ⟦ optimize0plus m + optimize0plus n ⟧ᴬ
    ≡⟨⟩
      ⟦ optimize0plus m ⟧ᴬ Data.Nat.+ ⟦ optimize0plus n ⟧ᴬ
    ≡⟨ cong (Data.Nat._+ ⟦ optimize0plus n ⟧ᴬ) sm ⟩
      ⟦ m ⟧ᴬ Data.Nat.+ ⟦ optimize0plus n ⟧ᴬ
    ≡⟨ cong (⟦ m ⟧ᴬ Data.Nat.+_) sn ⟩
      ⟦ m ⟧ᴬ Data.Nat.+ ⟦ n ⟧ᴬ
    ≡⟨⟩
      ⟦ m + n ⟧ᴬ
    ∎

  opHelper : (x y : AExp) →
               (k : AExp → AExp → AExp) →
                 (f : ℕ → ℕ → ℕ) →
                   (∀ { m n : AExp } → ⟦ k m n ⟧ᴬ ≡ f ⟦ m ⟧ᴬ ⟦ n ⟧ᴬ) →
                     (optimize0plus (k x y) ≡ k (optimize0plus x) (optimize0plus y)) →
                       opt0+safe x → opt0+safe y →
                         opt0+safe (k x y)
  opHelper x y k f fk kpush sx sy = begin
      ⟦ optimize0plus (k x y) ⟧ᴬ
    ≡⟨ cong ⟦_⟧ᴬ kpush ⟩
      ⟦ k (optimize0plus x) (optimize0plus y) ⟧ᴬ
    ≡⟨ fk ⟩
      f (⟦ optimize0plus x ⟧ᴬ) (⟦ optimize0plus y ⟧ᴬ)
    ≡⟨ cong (λ m → f m (⟦ optimize0plus y ⟧ᴬ)) sx ⟩
      f ⟦ x ⟧ᴬ (⟦ optimize0plus y ⟧ᴬ)
    ≡⟨ cong (f ⟦ x ⟧ᴬ) sy ⟩
      f ⟦ x ⟧ᴬ ⟦ y ⟧ᴬ
    ≡⟨ sym fk ⟩
      ⟦ k x y ⟧ᴬ
    ∎

  optimize0plusSound : ∀ (a : AExp) → opt0+safe a
  optimize0plusSound (# n) = refl
  optimize0plusSound (# zero + y) = optimize0plusSound y
  optimize0plusSound (# (suc n) + y) = begin
      ⟦ optimize0plus (# (suc n) + y) ⟧ᴬ
    ≡⟨⟩
      ⟦ # (suc n) + optimize0plus y ⟧ᴬ
    ≡⟨⟩
      ⟦ # (suc n) ⟧ᴬ Data.Nat.+ ⟦ optimize0plus y ⟧ᴬ
    ≡⟨ cong (⟦ # (suc n) ⟧ᴬ Data.Nat.+_) (optimize0plusSound y) ⟩
      ⟦ # (suc n) + y ⟧ᴬ
    ∎
  optimize0plusSound (x + z + y) = plusHelper (x + z) y (optimize0plusSound (x + z)) (optimize0plusSound y) refl
  optimize0plusSound (x - z + y) = plusHelper (x - z) y (optimize0plusSound (x - z)) (optimize0plusSound y) refl
  optimize0plusSound (x * z + y) = plusHelper (x * z) y (optimize0plusSound (x * z)) (optimize0plusSound y) refl
  optimize0plusSound (x - y) = opHelper x y _-_ Data.Nat._∸_ refl refl (optimize0plusSound x) (optimize0plusSound y)
  optimize0plusSound (x * y) = opHelper x y _*_ Data.Nat._*_ refl refl (optimize0plusSound x) (optimize0plusSound y)
```

### Inference Rule Notation

In informal discussions, it is convenient to write the rules for
⇓ᵃ and similar relations in the more readable graphical form of
_inference rules_, where the premises above the line justify the
conclusion below the line (we have already seen them in the
\CHAP{IndProp} chapter).

For example, the constructor `E_APlus`

        EA_+ : ∀ {e1 e2 : AExp} {n1 n2 : ℕ} 
                 → e1 ⇓ᵃ n1 → e2 ⇓ᵃ n2
                 → (e1 + e2) ⇓ᵃ (n1 Data.Nat.+ n2)

would be written like this as an inference rule:

                                   e1 ⇓ᵃ n1    e2 ⇓ᵃ n2
                                   --------------------  (EA_+)
                                    e1 + e2 ⇓ᵃ n1 + n2

Formally, there is nothing deep about inference rules: they are just
implications.  You can read the rule name on the right as the name of
the constructor and read each of the linebreaks between the premises
above the line (as well as the line itself) as `→`.  All the variables
mentioned in the rule (`e1`, `n1`, etc.) are implicitly bound by
universal quantifiers at the beginning. (Such variables are often
called _metavariables_ to distinguish them from the variables of the
language we are defining.  At the moment, our arithmetic expressions
don't include variables, but we'll soon be adding them.)  The whole
collection of rules is understood as being wrapped in an `data`
declaration.  In informal prose, this is either elided or else
indicated by saying something like "Let `⇓ᵃ` be the smallest relation
closed under the following rules...".

So we could (informally) define `⇓ᵃ` as the smallest relation closed
under these rules:

                              ----------                              (E_ANum)
                               # n ⇓ᵃ n

                               e1 ⇓ᵃ n1
                               e2 ⇓ᵃ n2
                         --------------------                         (EA_+)
                          e1 + e2 ⇓ᵃ n1 + n2

                               e1 ⇓ᵃ n1
                               e2 ⇓ᵃ n2
                        ---------------------                        (E_AMinus)
                          e1 - e2 ⇓ᵃ n1 - n2

                               e1 ⇓ᵃ n1
                               e2 ⇓ᵃ n2
                         --------------------                         (E_AMult)
                          e1 * e2 ⇓ᵃ n1 * n2


We can use this notation for inference rules in other contexts as well.
For example, it is convenient for writing more more complicated theorems in a clearer way.

{::comment}

(* INSTRUCTORS: It might be useful to write the inference rules on the
   chalkboard, walking through the translation from the inductive
   definition, and then use these quizzes to check comprehension. *)

(* HIDE *)
  (* LATER: The first two quizzes here seem kind of boring. *)
  (* QUIZ *)
  (** Which rules are needed to prove the following?
  ``
     (AMult (APlus (ANum 3) (ANum 1)) (ANum 0)) ⇓ᵃ 0
  ``

    (1) `E_ANum` and `EA_+`

    (2) `E_ANum` only

    (3) `E_ANum` and `E_AMult`

    (4) `E_AMult` and `EA_+`

    (5) `E_ANum`, `E_AMult`, and `EA_+`

  *)
  (* /QUIZ *)
  (* QUIZ *)
  (** Which rules are needed to prove the following?
  ``
     (AMinus (ANum 3) (AMinus (ANum 2) (ANum 1))) ⇓ᵃ 2
  ``

    (1) `E_ANum` and `EA_+`

    (2) `E_ANum` only

    (3) `E_ANum` and `E_AMinus`

    (4) `E_AMinus` and `EA_+`

    (5) `E_ANum`, `E_AMinus`, and `EA_+`

  *)
  (* /QUIZ *)
(* /HIDE *)

{:/comment}


### Evaluation as a relation

We have presented `aeval` and `beval` as functions.  Another way to
think about evaluation — one that we will see is often more flexible —
is as a _relation_ between expressions and their values.  This leads
naturally to inductive definitions like the following one for
arithmetic expressions.

```
  data _⇓ᵃ_ : AExp → ℕ → Set where
    Eᵃℕ : ∀ {n : ℕ} → (# n) ⇓ᵃ n
    Eᵃ+ : ∀ {e1 : AExp} {n1 : ℕ} {e2 : AExp} {n2 : ℕ}
             → e1 ⇓ᵃ n1 → e2 ⇓ᵃ n2
             → e1 + e2 ⇓ᵃ n1 Data.Nat.+ n2
    Eᵃ- : ∀ {e1 : AExp} {n1 : ℕ} {e2 : AExp} {n2 : ℕ}
             → e1 ⇓ᵃ n1 → e2 ⇓ᵃ n2
             → e1 - e2 ⇓ᵃ n1 ∸ n2
    Eᵃ* : ∀ {e1 : AExp} {n1 : ℕ} {e2 : AExp} {n2 : ℕ}
             → e1 ⇓ᵃ n1 → e2 ⇓ᵃ n2
             → e1 * e2 ⇓ᵃ n1 Data.Nat.* n2
  infix 4 _⇓ᵃ_
```

Just as evaluation functions are traditionally written as surrounding
double-brackets, evaluation relations are traditionally written as a
downward double-arrow.

We can use the evaluation relation in the same way that we use the `≡`
relation: by stating a relationship, and proving it.  For example, as
an informal proof tree we might have

     -------- Eᵃℕ     -------- Eᵃℕ
     # 5 ⇓ᵃ 5           # 6 ⇓ᵃ 6
     ---------------------------- Eᵃ+     -------- Eᵃℕ
           # 5 + # 6 ⇓ᵃ 11                 # 2 ⇓ᵃ 2
          ------------------------------------------ Eᵃ*
                   (# 5 + # 6) * # 2 ⇓ᵃ 22

and as formal proofs,

```
  _ : # 2 ⇓ᵃ 2
  _ = Eᵃℕ

  _ : (# 5 + # 6) ⇓ᵃ 11
  _ = Eᵃ+ Eᵃℕ Eᵃℕ

  _ : ((# 5 + # 6) * # 2) ⇓ᵃ 22
  _ = Eᵃ* (Eᵃ+ Eᵃℕ Eᵃℕ) Eᵃℕ
```

#### Exercise `bevalRelation1` (recommended) {#bevalRelation1}

In a similar way, convert the `⟦ ... ⟧ᴮ` evaluator into a relation
`_⇓ᵇ_`.

### Equivalence of the evaluators

It is straightforward to prove that the relational and functional
definitions of evaluation agree, but we will need some new tools in
Agda to communicate the result.

    aevalFnRel : ∀ (a : AExp) (n : ℕ) → ⟦ a ⟧ᴬ ≡ n ↔ a ⇓ᵃ n

The theorem says that for any program `a` and number `n`, applying the
evaluation function to `a` returns `n` exactly when the evaluation
relation connects `a` and `n`.  The theorem does not guarantee that
either one are true — but if one holds, then the other will too.

We consider one direction at a time: first, that the evaluation
function implies the relation.

```
  aevalFnThenRel : ∀ (a : AExp) (n : ℕ) → ⟦ a ⟧ᴬ ≡ n → a ⇓ᵃ n
```

We start the proof in the usual way: the quantifications and premises
become arguments.

    aevalFnThenRel m a ma = ?

The proofs we have written so far have been on structures like natural
numbers and lists.  In most of those proofs, we enumerated the
different forms that the number or list could take.  The same approach
applies here: we ask Agda to create a clause for each possible form of
`AExp`.

    aevalFnThenRel (# m) n an = { }1
    aevalFnThenRel (a₁ + a₂) n an = { }2
    aevalFnThenRel (a₁ - a₂) n an = { }3
    aevalFnThenRel (a₁ * a₂) n an = { }4

We will need to complete each clause, one at a time.  In each case the
third argument, corresponding to the premise, is the evidence that the
evaluation function links the first two arguments.  The premise is an
equality — `≡` is the main connective.  As we saw in the last chapter,
`refl` is one justification for an equality relationship which Agda
understands.  In fact, `refl` is the *only* possible evidence for an
`≡`-assertion.

So if we use `C-c C-c` to enumerate the possible forms of evidence for
`an` in the first clause, Agda will produce only one resulting clause,
with `refl` as the evidence for the equality.

    aevalFnThenRel (# m) .m refl = { }1

Agda has also made a change to the second argument.  This is a _dot
pattern_.  Agda uses dot patterns to convey that only certain patterns
are possible in a clause.  Let's think through what this clause says:

 - The first clause tells us that we are only considering terms of the
   form `# m`.

 - The third clause tells us that the term and the value `n` have the
   relationship `⟦ a ⟧ᴬ ≡ n`; putting that together with knowing that
   `a` is `# m`, we have that `⟦ # m ⟧ᴬ ≡ n`.

 - The definition of `⟦_⟧ᴬ` tells us that `⟦ # m ⟧ᴬ` is `m`.

 - So Agda can figure out that the only valid possibility for the
   second argument is that it is the same as the number under the `#`.
   This is the meaning of the pattern for the second argument: the dot
   conveys the understanding only certain possible values will be
   consistent with the evidence in the other arguments.

What evidence should this clause return?  The signature tells us that
the result type is a `⇓ᵃ`, and we know from the `data _⇓ᵃ_`
declaration that there are four possible forms of evidence for `⇓ᵃ`.
However, only one of them makes a statement about `#`-terms — and this
form `Eᵃℕ` is the evidence for the first clause.

```
  aevalFnThenRel (# m) .m refl = Eᵃℕ
```

We proceed similarly in each of the other cases.  For each of the
other three forms of arithmetic expressions — addition, subtraction
(monus), multiplication — only one clause of `⟦_⟧ᴬ` can return a value
for that form of expression.  Agda recognizes this, and recognizes
that a dot-pattern for the corresponding value is appropriate.

```
  aevalFnThenRel (a₁ + a₂) .(⟦ a₁ ⟧ᴬ Data.Nat.+ ⟦ a₂ ⟧ᴬ) refl =
    Eᵃ+ (aevalFnThenRel a₁ ⟦ a₁ ⟧ᴬ refl) (aevalFnThenRel a₂ ⟦ a₂ ⟧ᴬ refl)
  aevalFnThenRel (a₁ - a₂) .(⟦ a₁ ⟧ᴬ ∸ ⟦ a₂ ⟧ᴬ) refl =
    Eᵃ- (aevalFnThenRel a₁ ⟦ a₁ ⟧ᴬ refl) (aevalFnThenRel a₂ ⟦ a₂ ⟧ᴬ refl)
  aevalFnThenRel (a₁ * a₂) .(⟦ a₁ ⟧ᴬ Data.Nat.* ⟦ a₂ ⟧ᴬ) refl =
    Eᵃ* (aevalFnThenRel a₁ ⟦ a₁ ⟧ᴬ refl) (aevalFnThenRel a₂ ⟦ a₂ ⟧ᴬ refl)
```

This should one direction of implication, that the evaluation function
implies the relation.  The other direction is that the evaluation
relation implies the function.

```
  aevalRelThenFn : ∀ (a : AExp) (n : ℕ) → a ⇓ᵃ n → ⟦ a ⟧ᴬ ≡ n
```

We begin with the usual starting clause

    aevalRelThenFn a n aRn = ?

and ask Agda to decompose into cases based on `a`:

Remember that the forms of evidence which our theorem functions return
is determined by the relation in the signature.  Above, the conclusion
was a `⇓ᵃ`-formula, so the forms of evidence were assembled with the
constructors of `⇓ᵃ`.  Here, the conclusion is a `≡`-formula, so the
evidence wil be either `refl`, or a chain of equations.

As for the other direction, the case of the constant expression is
simple.  Note that we use the dot pattern on the expression: the only
possible form of expression to which the `Eᵃℕ` constructor could apply
is an integer literal.  In this case the result value and the value in
the term must be the same.  So we name the result value, and use the
dot pattern to tell Agda that the name in the expression pattern is
defined elsewhere.

```
  aevalRelThenFn .(# n) n Eᵃℕ = refl
```

This clause needs only `refl` for evidence since `n` and `n` are
identical.

The pattens which Agda generates for the other clauses look a bit
strange,

    aevalRelThenFn .(_ + _) .(_ Data.Nat.+ _) (Eᵃ+ an₁ an₂) = ?

and so forth.  The subterms in the Imp expressions and the values
passed to the `Data.Nat` operators are related by the `an₁` and `an₂`
evidence.  But Agda cannot access these items because they are
_implicit_ arguments to `Eᵃ+` and the other constructors.  Carefully
chosen implicit arguments can save us work and make our programs
easier to read, but sometimes we need to expose the values.  If we
explicitly name them,

    aevalRelThenFn .(_ + _) .(_ Data.Nat.+ _) (Eᵃ+ {e1} {n1} {e2} {n2} an₁ an₂) = ?

then we can use those name in the slots Agda could not otherwise fill
in.

    aevalRelThenFn .(e1 + e2) .(n1 Data.Nat.+ n2) (Eᵃ+ {e1} {n1} {e2} {n2} an₁ an₂) = ?

We need to prove that `⟦ e1 + e2 ⟧ᴬ` and `n1 Data.Nat.+ n2` have the
same value, and it is easest to use a chain of equations,

```
  aevalRelThenFn .(e1 + e2) .(n1 Data.Nat.+ n2) (Eᵃ+ {e1} {n1} {e2} {n2} aRn aRn₁) = 
    begin
      ⟦ e1 + e2 ⟧ᴬ
    ≡⟨⟩
      ⟦ e1 ⟧ᴬ Data.Nat.+ ⟦ e2 ⟧ᴬ
    ≡⟨ cong (Data.Nat._+ ⟦ e2 ⟧ᴬ) (aevalRelThenFn e1 n1 aRn) ⟩
      n1 Data.Nat.+ ⟦ e2 ⟧ᴬ
    ≡⟨ cong (n1 Data.Nat.+_) (aevalRelThenFn e2 n2 aRn₁) ⟩
      n1 Data.Nat.+ n2
    ∎  
```

The reasoning is the same for the other two cases, which also
correspond directly to built-in arithmetic operators.

```
  aevalRelThenFn .(e1 - e2) .(n1 ∸ n2) (Eᵃ- {e1} {n1} {e2} {n2} aRn aRn₁) = 
    begin
      ⟦ e1 - e2 ⟧ᴬ
    ≡⟨⟩
      ⟦ e1 ⟧ᴬ ∸ ⟦ e2 ⟧ᴬ
    ≡⟨ cong (_∸ ⟦ e2 ⟧ᴬ) (aevalRelThenFn e1 n1 aRn) ⟩
      n1 ∸ ⟦ e2 ⟧ᴬ
    ≡⟨ cong (n1 ∸_) (aevalRelThenFn e2 n2 aRn₁) ⟩
      n1 ∸ n2
    ∎
  aevalRelThenFn .(e1 * e2) .(n1 Data.Nat.* n2) (Eᵃ* {e1} {n1} {e2} {n2} aRn aRn₁) = 
    begin
      ⟦ e1 * e2 ⟧ᴬ
    ≡⟨⟩
      ⟦ e1 ⟧ᴬ Data.Nat.* ⟦ e2 ⟧ᴬ
    ≡⟨ cong (Data.Nat._* ⟦ e2 ⟧ᴬ) (aevalRelThenFn e1 n1 aRn) ⟩
      n1 Data.Nat.* ⟦ e2 ⟧ᴬ
    ≡⟨ cong (n1 Data.Nat.*_) (aevalRelThenFn e2 n2 aRn₁) ⟩
      n1 Data.Nat.* n2
    ∎
```

With these two lemmas we can state an equivalence theorem.

```
  aevalFn⇔Rel : ∀ (a : AExp) (n : ℕ) → ⟦ a ⟧ᴬ ≡ n ⇔ a ⇓ᵃ n
  aevalFn⇔Rel a n = record
    { to   = λ aFn -> aevalFnThenRel a n aFn
    ; from = λ aRn -> aevalRelThenFn a n aRn
    }
```

#### Exercise `bevalRelationIffEval` (recommended) {#bevalRelationIffEval}

Prove that your evaluation function `⟦ ... ⟧ᴮ` and relation `_⇓ᵇ_` are
equivalent.

### Computational vs. relational definitions

For the definitions of evaluation for arithmetic and boolean
expressions, the choice of whether to use functional or relational
definitions is mainly a matter of taste: either way works.

However, there are circumstances where relational definitions of
evaluation work much better than functional ones.  For example,
suppose that we wanted to extend the arithmetic operations with
division:

    data AExp : Set where
      # : ℕ → AExp
      _+_ : AExp → AExp → AExp 
      _-_ : AExp → AExp → AExp 
      _*_ : AExp → AExp → AExp 
      _÷_ : AExp → AExp → AExp   --  <-- this one is new

Extending the definition of `⟦ ... ⟧̂ᵃ` to handle this new operation
would not be straightforward: What should we return as the result of
`# 5 ÷ # 0`?  But extending `⇓ᵃ` is very easy.

    data _⇓ᵃ_ : AExp → ℕ → Set where
      -- ... Constructors Eᵃℕ, Eᵃ+, Eᵃ-, Eᵃ* unchanged
      Eᵃ÷ : ∀ {n1 n2 : ℕ} {e1 e2 : AExp} 
               → e1 ⇓ᵃ n1 → e2 ⇓ᵃ n2
               → e1 * e2 ⇓ᵃ n1 Data.Nat.* n2

Notice that the evaluation relation has now become _partial_: There
are some inputs for which it simply does not specify an output.  This
is a crucial difference between relations and functions: a partial
relation is just fine, but all Agda functions **must** be total.

Or suppose that we want to extend the arithmetic operations by a
nondeterministic number generator `any` that, when evaluated, may
yield any number. Note that this is not the same as making a
_probabilistic_ choice among all possible numbers — we're not
specifying any particular probability distribution for the results,
just saying what results are _possible_.

    data AExp : Set where
      any : AExp
      # : ℕ → AExp
      -- Other constructors `#`, `_+_`, `_-_`, `_*_` unchanged 

Extending `⟦ ... ⟧̂ᵃ` would be tricky, since now evaluation is _not_ a
deterministic function from expressions to numbers.  A random number
generator could have many different results, which is not consistent
with the sense of "function" in a functional language.  But again,
extending `⇓ᵃ` would be straightforward:

    data _⇓ᵃ_ : AExp → ℕ → Set where
      -- ... Constructors Eᵃℕ, Eᵃ+, Eᵃ-, Eᵃ* unchanged
      Eᵃany : ∀ { n : ℕ } → any ⇓ᵃ n

At this point you maybe wondering: which style should I use by
default?  In the examples we've just seen, relational definitions
turned out to be more useful than functional ones.  For situations
like these, where the thing being defined is not easy to express as a
function, or indeed where it is _not_ a function, there is no real
choice.  But what about when both styles are workable?

One point in favor of relational definitions is that they can be more
elegant and easier to understand.
On the other hand, functional definitions can often be more
convenient:

 - Functions are by definition deterministic and defined on all
   arguments; for a relation we have to _prove_ these properties
   explicitly if we need them.

 - With functions we can also take advantage of Agda's computation
   mechanism, and rely on simple proofs techniques like `refl`.

Furthermore, we can use functions in runtime code if we compile to a
standalone binary.  Relations do not correspond to runtime-executable
code.

Ultimately, the choice often comes down to either the specifics of a
particular situation, or simply a question of taste.  Indeed, in large
programs it is common to see a definition given in _both_ functional
and relational styles, plus a lemma stating that the two coincide,
allowing further proofs to switch from one point of view to the other
at will.

```
  -- end of module ImpStage1
```

## Expressions with variables

Now we return to defining Imp. The next thing we need to do is to
enrich our arithmetic and boolean expressions with variables.  To keep
things simple, we'll assume that all variables are global and that
they only hold numbers.

What is the meaning of an expression with a variable in it?  What is
the value of `x + 3`?  In Imp or Agda, just as in any other language
you have seen, such as expression does not have any particular meaning
by itself.  It has meaning only in the context of the _state_ of a
running program.  The state gives the relationship between the names
of variables and the values we associate with them.  Some other
languages associate other information with the state as well, but to
keep Imp simple we will be use the state only for these name-value
bindings.

For simplicity, we assume that the state is defined for _all_
variables, even though any given program is only going to mention a
finite number of them.  The state captures all of the information
stored in memory.  For Imp programs, because each variable stores a
natural number, we can represent the state as a mapping from strings
to `nat`, and will use `0` as default value in the store.  For more
complex programming languages, the state might have more structure.
Fortunately we already have such a structure at hand — the [total
maps]({{ site.baseurl }}/Maps/) from the "Functional Programming"
chapter.

So our definition of a state is a straightforward use of `TotalMap`,
specialized to the numeric values we will store in Imp variables.

```
State : Set
State = TotalMap ℕ
```

Then we can add variables to the arithmetic expressions we had before
by simply adding one more constructor:

```
data AExp : Set where
  # : ℕ → AExp
  id : String → AExp          -- <--- This one is new
  _+_ : AExp → AExp → AExp
  _-_ : AExp → AExp → AExp 
  _*_ : AExp → AExp → AExp 

infixl 7  _*_
infixl 6  _+_  _-_
```

For convenience we will declare a few variable names.

```
X : String
X = "X"
Y : String
Y = "Y"
Z : String
Z = "Z"
W : String
W = "W"
```

This convention for naming program variables with upper-case letter
(`X`, `Y`, `Z`) clashes a bit with our earlier use of uppercase
letters for types.  Since we're not using polymorphism heavily in the
chapters developed to Imp, this overloading should not cause
confusion.

The definition of `bexp`s is unchanged, except that it now refers to
the new `aexp`s.

```
data BExp : Set where
  T : BExp
  F : BExp
  _==_ : AExp → AExp → BExp
  _<=_ : AExp → AExp → BExp
  ! : BExp → BExp
  _&&_ : BExp → BExp → BExp
  _||_ : BExp → BExp → BExp

infixl 8  _&&_
infixl 7  _||_
```

The main change to our evaluation functions is that they now that the
state as an extra argument.  Following tradition, we write the state
immediately after the double-brackets.  Otherwise, the way we extend
the two evaluators is straightforward.

```
⟦_⟧ᴬ_ : AExp → State → ℕ
⟦ # n ⟧ᴬ st = n
⟦ id name ⟧ᴬ st = st name
⟦ ae1 + ae2 ⟧ᴬ st = ⟦ ae1 ⟧ᴬ st Data.Nat.+ ⟦ ae2 ⟧ᴬ st
⟦ ae1 - ae2 ⟧ᴬ st = ⟦ ae1 ⟧ᴬ st ∸ ⟦ ae2 ⟧ᴬ st
⟦ ae1 * ae2 ⟧ᴬ st = ⟦ ae1 ⟧ᴬ st Data.Nat.* ⟦ ae2 ⟧ᴬ st

⟦_⟧ᴮ_ : BExp → State → Bool
⟦ T ⟧ᴮ st = true
⟦ F ⟧ᴮ st = false
⟦ ae1 == ae2 ⟧ᴮ st = ⟦ ae1 ⟧ᴬ st ≡ᵇ ⟦ ae2 ⟧ᴬ st
⟦ ae1 <= ae2 ⟧ᴮ st = (v1 ≡ᵇ v2) ∨ (v1 <ᵇ v2)
                    where v1 : ℕ
                          v1 = ⟦ ae1 ⟧ᴬ st
                          v2 : ℕ
                          v2 = ⟦ ae2 ⟧ᴬ st
⟦ ! be ⟧ᴮ st = not (⟦ be ⟧ᴮ st)
⟦ be1 && be2 ⟧ᴮ st = ⟦ be1 ⟧ᴮ st ∧ ⟦ be2 ⟧ᴮ st
⟦ be1 || be2 ⟧ᴮ st = ⟦ be1 ⟧ᴮ st ∨ ⟦ be2 ⟧ᴮ st
```

Since the default value for Imp variable not otherwise set in zero, we
can define an empty Imp state for convenience.

```
emptyState : State
emptyState = ↪ 0
```

For example, we can evaluate the expression `3+X*2` in an environment
where `Z` is bound to 5.

```
_ : ⟦ # 3 + id X * # 2 ⟧ᴬ (X ↦ 5 , emptyState) ≡ 13
_ = refl

_ : ⟦ T && ! (id X <= # 4) ⟧ᴮ (X ↦ 5 , emptyState) ≡ true
_ = refl
```

## Unicode

This section uses the following Unicode symbols:

{::comment}
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
{:/comment}

---

*This page is derived from Pierce et al. with some additional material
by Maraist; for more information see the [sources and authorship]({{
site.baseurl }}/Sources/) page.*
