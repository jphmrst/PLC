---
title     : "Imp: Simple imperative programs"
layout    : page
prev      : /Logic/
permalink : /Imp/
next      : /
---

```
module plc.imp.Imp where
open import Data.String using (String)
open import Data.Nat using (ℕ; _∸_; _≡ᵇ_; _<ᵇ_; zero; suc)
open import Data.Bool using (Bool; true; false; not; _∨_; _∧_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import plc.fp.Maps using (TotalMap; _↦_,_; ↪)
```

In this section we take a more serious look at how to use Agda to
study other things.  Our case study is a simple _imperative
programming language_ called Imp, embodying a tiny core fragment of
conventional mainstream languages such as C and Java.  Here is a
familiar mathematical function written in Imp.

    Z := X ,
    Y := # 1 ,
    while ~(Z = # 0) do
      Y := Y * Z ,
      Z := Z - # 1
    end

We concentrate here on defining the _syntax_ and _semantics_ of Imp;
later sections will develop a theory of _program equivalence_ and
introduce _Hoare Logic_, a widely used logic for reasoning about
imperative programs.

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
relative precedence of [+], [-], and [*], the use of parens to group
subexpressions.  Some additional information — and human intelligence
— would be required to turn this description into a formal definition,
such as for implementing a compiler.

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
  ⟦_⟧ᵃ : AExp → ℕ
  ⟦ # n ⟧ᵃ = n
  ⟦ ae1 + ae2 ⟧ᵃ = ⟦ ae1 ⟧ᵃ Data.Nat.+ ⟦ ae2 ⟧ᵃ
  ⟦ ae1 - ae2 ⟧ᵃ = ⟦ ae1 ⟧ᵃ ∸ ⟦ ae2 ⟧ᵃ
  ⟦ ae1 * ae2 ⟧ᵃ = ⟦ ae1 ⟧ᵃ Data.Nat.* ⟦ ae2 ⟧ᵃ
```

Note that since we have defined our own version of `+` and `*` for
this module, we must explicitly clarify when we want to use the
version of `+` declared within the `Data.Nat` module.  We did import
the `∸` operator from `Data.Nat`, so we can use it without the module
prefix.

Similarly, evaluating a boolean expression yields a boolean.

```
  ⟦_⟧ᵇ : BExp → Bool
  ⟦ T ⟧ᵇ = true
  ⟦ F ⟧ᵇ = false
  ⟦ (ae1 == ae2) ⟧ᵇ = ⟦ ae1 ⟧ᵃ ≡ᵇ ⟦ ae2 ⟧ᵃ
  ⟦ (ae1 <= ae2) ⟧ᵇ = (v1 ≡ᵇ v2) ∨ (v1 <ᵇ v2)
                       where v1 : ℕ
                             v1 = ⟦ ae1 ⟧ᵃ
                             v2 : ℕ
                             v2 = ⟦ ae2 ⟧ᵃ
  ⟦ ! be ⟧ᵇ = not ⟦ be ⟧ᵇ
  ⟦ be1 && be2 ⟧ᵇ = ⟦ be1 ⟧ᵇ ∧ ⟦ be2 ⟧ᵇ
  ⟦ be1 || be2 ⟧ᵇ = ⟦ be1 ⟧ᵇ ∨ ⟦ be2 ⟧ᵇ
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
         ⟦ optimize0plus (x * y) ⟧ᵃ ≡
           ⟦ optimize0plus x * optimize0plus y ⟧ᵃ
  s1 x y =
    begin
      ⟦ optimize0plus (x * y) ⟧ᵃ
    ≡⟨ refl ⟩
      ⟦ optimize0plus x * optimize0plus y ⟧ᵃ
    ∎
      

  o0pS_op : ∀ { x y : AExp } →
              (k : AExp → AExp → AExp) → (f : ℕ → ℕ → ℕ) →
                opt0+safe x → opt0+safe y →
                  (∀ { m n : AExp } → ⟦ k m n ⟧ᵃ ≡ f ⟦ m ⟧ᵃ ⟦ n ⟧ᵃ) → 
                    (optimize0plus (k x y) ≡ k (optimize0plus x) (optimize0plus y)) →
                      opt0+safe (k x y)
  o0pS_op {x} {y} k f sx sy kf kdown = 
    begin
      ⟦ optimize0plus (k x y) ⟧ᵃ
    ≡⟨ cong aeval kdown ⟩
      ⟦ k (optimize0plus x) (optimize0plus y) ⟧ᵃ
    ≡⟨ kf ⟩
      f ⟦ optimize0plus x ⟧ᵃ ⟦ optimize0plus y ⟧ᵃ
    ≡⟨ cong (λ x → f x ⟦ optimize0plus y ⟧ᵃ) sx ⟩
      f ⟦ x ⟧ᵃ ⟦ optimize0plus y ⟧ᵃ
    ≡⟨ cong (f ⟦ x ⟧ᵃ) sy ⟩
      f ⟦ x ⟧ᵃ ⟦ y ⟧ᵃ
    ≡⟨ sym kf ⟩
      ⟦ k x y ⟧ᵃ
    ∎
{:/comment}

```
  opt0+safe : AExp → Set
  opt0+safe m = ⟦ optimize0plus m ⟧ᵃ ≡ ⟦ m ⟧ᵃ

  plusHelper : (m n : AExp) →
                 opt0+safe m → opt0+safe n →
                   (optimize0plus (m + n) ≡ optimize0plus m + optimize0plus n) →
                     opt0+safe (m + n)
  plusHelper m n sm sn nonz = begin
      ⟦ optimize0plus (m + n) ⟧ᵃ
    ≡⟨ cong ⟦_⟧ᵃ nonz ⟩
      ⟦ optimize0plus m + optimize0plus n ⟧ᵃ
    ≡⟨⟩
      ⟦ optimize0plus m ⟧ᵃ Data.Nat.+ ⟦ optimize0plus n ⟧ᵃ
    ≡⟨ cong (Data.Nat._+ ⟦ optimize0plus n ⟧ᵃ) sm ⟩
      ⟦ m ⟧ᵃ Data.Nat.+ ⟦ optimize0plus n ⟧ᵃ
    ≡⟨ cong (⟦ m ⟧ᵃ Data.Nat.+_) sn ⟩
      ⟦ m ⟧ᵃ Data.Nat.+ ⟦ n ⟧ᵃ
    ≡⟨⟩
      ⟦ m + n ⟧ᵃ
    ∎

  opHelper : (x y : AExp) →
               (k : AExp → AExp → AExp) →
                 (f : ℕ → ℕ → ℕ) →
                   (∀ { m n : AExp } → ⟦ k m n ⟧ᵃ ≡ f ⟦ m ⟧ᵃ ⟦ n ⟧ᵃ) →
                     (optimize0plus (k x y) ≡ k (optimize0plus x) (optimize0plus y)) →
                       opt0+safe x → opt0+safe y →
                         opt0+safe (k x y)
  opHelper x y k f fk kpush sx sy = begin
      ⟦ optimize0plus (k x y) ⟧ᵃ
    ≡⟨ cong ⟦_⟧ᵃ kpush ⟩
      ⟦ k (optimize0plus x) (optimize0plus y) ⟧ᵃ
    ≡⟨ fk ⟩
      f (⟦ optimize0plus x ⟧ᵃ) (⟦ optimize0plus y ⟧ᵃ)
    ≡⟨ cong (λ m → f m (⟦ optimize0plus y ⟧ᵃ)) sx ⟩
      f ⟦ x ⟧ᵃ (⟦ optimize0plus y ⟧ᵃ)
    ≡⟨ cong (f ⟦ x ⟧ᵃ) sy ⟩
      f ⟦ x ⟧ᵃ ⟦ y ⟧ᵃ
    ≡⟨ sym fk ⟩
      ⟦ k x y ⟧ᵃ
    ∎

  optimize0plusSound : ∀ (a : AExp) → opt0+safe a
  optimize0plusSound (# n) = refl
  optimize0plusSound (# zero + y) = optimize0plusSound y
  optimize0plusSound (# (suc n) + y) = begin
      ⟦ optimize0plus (# (suc n) + y) ⟧ᵃ
    ≡⟨⟩
      ⟦ # (suc n) + optimize0plus y ⟧ᵃ
    ≡⟨⟩
      ⟦ # (suc n) ⟧ᵃ Data.Nat.+ ⟦ optimize0plus y ⟧ᵃ
    ≡⟨ cong (⟦ # (suc n) ⟧ᵃ Data.Nat.+_) (optimize0plusSound y) ⟩
      ⟦ # (suc n) + y ⟧ᵃ
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

TODO --- restore examples when params settle down

  _ : # 2 ⇓ᵃ 2
  _ = Eᵃℕ

  _ : (# 5 + # 6) ⇓ᵃ 11
  _ = Eᵃ+ Eᵃℕ Eᵃℕ

  _ : ((# 5 + # 6) * # 2) ⇓ᵃ 22
  _ = Eᵃ* (Eᵃ+ Eᵃℕ Eᵃℕ) Eᵃℕ

============================================================

#### Exercise `bevalRelation1` (recommended) {#bevalRelation1}

In a similar way, convert the `⟦ ... ⟧ᵇ` evaluator into a relation
`_⇓ᵇ_`.

### Equivalence of the evaluators

It is straightforward to prove that the relational and functional
definitions of evaluation agree, but we will need some new tools in
Agda to communicate the result.

    aevalFnRel : ∀ (a : AExp) (n : ℕ) → ⟦ a ⟧ᵃ ≡ n ↔ a ⇓ᵃ n

The theorem says that for any program `a` and number `n`, applying the
evaluation function to `a` returns `n` exactly when the evaluation
relation connects `a` and `n`.  The theorem does not guarantee that
either one are true — but if one holds, then the other will too.

We consider one direction at a time: first, that the evaluation
function implies the relation.

```
  aevalFnThenRel : ∀ (a : AExp) (n : ℕ) → ⟦ a ⟧ᵃ ≡ n → a ⇓ᵃ n
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
   relationship `⟦ a ⟧ᵃ ≡ n`; putting that together with knowing that
   `a` is `# m`, we have that `⟦ # m ⟧ᵃ ≡ n`.

 - The definition of `⟦_⟧ᵃ` tells us that `⟦ # m ⟧ᵃ` is `m`.

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
(monus), multiplication — only one clause of `⟦_⟧ᵃ` can return a value
for that form of expression.  Agda recognizes this, and recognizes
that a dot-pattern for the corresponding value is appropriate.

```
  aevalFnThenRel (a₁ + a₂) .(⟦ a₁ ⟧ᵃ Data.Nat.+ ⟦ a₂ ⟧ᵃ) refl =
    Eᵃ+ (aevalFnThenRel a₁ ⟦ a₁ ⟧ᵃ refl) (aevalFnThenRel a₂ ⟦ a₂ ⟧ᵃ refl)
  aevalFnThenRel (a₁ - a₂) .(⟦ a₁ ⟧ᵃ ∸ ⟦ a₂ ⟧ᵃ) refl =
    Eᵃ- (aevalFnThenRel a₁ ⟦ a₁ ⟧ᵃ refl) (aevalFnThenRel a₂ ⟦ a₂ ⟧ᵃ refl)
  aevalFnThenRel (a₁ * a₂) .(⟦ a₁ ⟧ᵃ Data.Nat.* ⟦ a₂ ⟧ᵃ) refl =
    Eᵃ* (aevalFnThenRel a₁ ⟦ a₁ ⟧ᵃ refl) (aevalFnThenRel a₂ ⟦ a₂ ⟧ᵃ refl)
```

This should one direction of implication, that the evaluation function
implies the relation.  The other direction is that the evaluation
relation implies the function.

```
  aevalRelThenFn : ∀ (a : AExp) (n : ℕ) → a ⇓ᵃ n → ⟦ a ⟧ᵃ ≡ n
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

We need to prove that `⟦ e1 + e2 ⟧ᵃ` and `n1 Data.Nat.+ n2` have the
same value, and it is easest to use a chain of equations,

```
  aevalRelThenFn .(e1 + e2) .(n1 Data.Nat.+ n2) (Eᵃ+ {e1} {n1} {e2} {n2} aRn aRn₁) = 
    begin
      ⟦ e1 + e2 ⟧ᵃ
    ≡⟨⟩
      ⟦ e1 ⟧ᵃ Data.Nat.+ ⟦ e2 ⟧ᵃ
    ≡⟨ cong (Data.Nat._+ ⟦ e2 ⟧ᵃ) (aevalRelThenFn e1 n1 aRn) ⟩
      n1 Data.Nat.+ ⟦ e2 ⟧ᵃ
    ≡⟨ cong (n1 Data.Nat.+_) (aevalRelThenFn e2 n2 aRn₁) ⟩
      n1 Data.Nat.+ n2
    ∎  
```

The reasoning is the same for the other two cases, which also
correspond directly to built-in arithmetic operators.

```
  aevalRelThenFn .(e1 - e2) .(n1 ∸ n2) (Eᵃ- {e1} {n1} {e2} {n2} aRn aRn₁) = 
    begin
      ⟦ e1 - e2 ⟧ᵃ
    ≡⟨⟩
      ⟦ e1 ⟧ᵃ ∸ ⟦ e2 ⟧ᵃ
    ≡⟨ cong (_∸ ⟦ e2 ⟧ᵃ) (aevalRelThenFn e1 n1 aRn) ⟩
      n1 ∸ ⟦ e2 ⟧ᵃ
    ≡⟨ cong (n1 ∸_) (aevalRelThenFn e2 n2 aRn₁) ⟩
      n1 ∸ n2
    ∎
  aevalRelThenFn .(e1 * e2) .(n1 Data.Nat.* n2) (Eᵃ* {e1} {n1} {e2} {n2} aRn aRn₁) = 
    begin
      ⟦ e1 * e2 ⟧ᵃ
    ≡⟨⟩
      ⟦ e1 ⟧ᵃ Data.Nat.* ⟦ e2 ⟧ᵃ
    ≡⟨ cong (Data.Nat._* ⟦ e2 ⟧ᵃ) (aevalRelThenFn e1 n1 aRn) ⟩
      n1 Data.Nat.* ⟦ e2 ⟧ᵃ
    ≡⟨ cong (n1 Data.Nat.*_) (aevalRelThenFn e2 n2 aRn₁) ⟩
      n1 Data.Nat.* n2
    ∎
```

TODO --- the bi-implication

#### Exercise `bevalRelationIffEval` (recommended) {#bevalRelationIffEval}

Prove that your evaluation function `⟦ ... ⟧ᵇ` and relation `_⇓ᵇ_` are
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
⟦_⟧ᵃ_ : AExp → State → ℕ
⟦ # n ⟧ᵃ st = n
⟦ id name ⟧ᵃ st = st name
⟦ ae1 + ae2 ⟧ᵃ st = ⟦ ae1 ⟧ᵃ st Data.Nat.+ ⟦ ae2 ⟧ᵃ st
⟦ ae1 - ae2 ⟧ᵃ st = ⟦ ae1 ⟧ᵃ st ∸ ⟦ ae2 ⟧ᵃ st
⟦ ae1 * ae2 ⟧ᵃ st = ⟦ ae1 ⟧ᵃ st Data.Nat.* ⟦ ae2 ⟧ᵃ st

⟦_⟧ᵇ_ : BExp → State → Bool
⟦ T ⟧ᵇ st = true
⟦ F ⟧ᵇ st = false
⟦ ae1 == ae2 ⟧ᵇ st = ⟦ ae1 ⟧ᵃ st ≡ᵇ ⟦ ae2 ⟧ᵃ st
⟦ ae1 <= ae2 ⟧ᵇ st = (v1 ≡ᵇ v2) ∨ (v1 <ᵇ v2)
                    where v1 : ℕ
                          v1 = ⟦ ae1 ⟧ᵃ st
                          v2 : ℕ
                          v2 = ⟦ ae2 ⟧ᵃ st
⟦ ! be ⟧ᵇ st = not (⟦ be ⟧ᵇ st)
⟦ be1 && be2 ⟧ᵇ st = ⟦ be1 ⟧ᵇ st ∧ ⟦ be2 ⟧ᵇ st
⟦ be1 || be2 ⟧ᵇ st = ⟦ be1 ⟧ᵇ st ∨ ⟦ be2 ⟧ᵇ st
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
_ : ⟦ # 3 + id X * # 2 ⟧ᵃ (X ↦ 5 , emptyState) ≡ 13
_ = refl

_ : ⟦ T && ! (id X <= # 4) ⟧ᵇ (X ↦ 5 , emptyState) ≡ true
_ = refl
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
cmdEvalFn st (x := x₁) = x ↦ ⟦ x₁ ⟧ᵃ st , st
cmdEvalFn st (c₁ , c₂) = cmdEvalFn (cmdEvalFn st c₁) c₂
cmdEvalFn st (if x then c₁ else c₂ end) with ⟦ x ⟧ᵇ st
...                                    | true = cmdEvalFn st c₁
...                                    | false = cmdEvalFn st c₂
cmdEvalFn st (while x loop c end) = st
```

In a traditional functional programming language like OCaml or Haskell
we could add the `while` case as follows:

    cmdEvalFn : State → Command → State
    -- ...other cases unchanged...
    cmdEvalFn st (while x loop c end) with ⟦ x ⟧ᵇ st
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

                           -----------------                            (E_Skip)
                           st =[ skip ]=> st

                           aeval st a = n
                   -------------------------------                      (E_Ass)
                   st =[ x := a ]=> (x !-> n ; st)

                           st  =[ c1 ]=> st'
                           st' =[ c2 ]=> st′'
                         ---------------------                           (E_Seq)
                         st =[ c1;c2 ]=> st′'

                          beval st b = true
                           st =[ c1 ]=> st'
                --------------------------------------               (E_IfTrue)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                           st =[ c2 ]=> st'
                --------------------------------------              (E_IfFalse)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                    -----------------------------                 (E_WhileFalse)
                    st =[ while b do c end ]=> st

                          beval st b = true
                           st =[ c ]=> st'
                  st' =[ while b do c end ]=> st′'
                  --------------------------------                 (E_WhileTrue)
                  st  =[ while b do c end ]=> st′'

*)

Here is the formal definition.  Make sure you understand how it
corresponds to the inference rules.

```
data _=[_]=>_ : State → Command → State → Set where
  Eskip : ∀ { st : State } → st =[ skip ]=> st
  E:= : ∀ { st : State } { a : AExp } { n : ℕ } { x : String } →
           ⟦ a ⟧ᵃ st ≡ n →
             st =[ x := a ]=> ( x ↦ n , st )
  E, : ∀ { st' : State } { st st′' : State } { c₁ c₂ : Command } →
          st  =[ c₁ ]=> st'  ->
            st' =[ c₂ ]=> st′' ->
              st  =[ c₁ , c₂ ]=> st′'
  EIfT : ∀ { st st' : State } { b : BExp } { c1 c2 : Command } →
            ⟦ b ⟧ᵇ st ≡ true →
              st =[ c1 ]=> st' →
                st =[ if b then c1 else c2 end ]=> st'
  EIfF : ∀ { st st' : State } { b : BExp } { c1 c2 : Command } →
            ⟦ b ⟧ᵇ st ≡ false →
              st =[ c2 ]=> st' →
                st =[ if b then c1 else c2 end ]=> st'
  EWhileF : ∀ { st : State } { b : BExp } { c : Command } →
               ⟦ b ⟧ᵇ st ≡ false →
                 st =[ while b loop c end ]=> st
  EWhileT : ∀ { st st' st′' : State } { b : BExp } { c : Command } →
               ⟦ b ⟧ᵇ st ≡ true →
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
_ = E, (E:= refl) (EIfF refl (E:= refl))
```

Here is another example,

```
_ : emptyState =[
      X := # 0 ,
      Y := # 1 ,
      Z := # 2
    ]=> Z ↦ 2 , Y ↦ 1 , X ↦ 0 , emptyState
_ = E, (E:= refl) (E, (E:= refl) (E:= refl))
```


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


(* HIDE: PR: I phrased these quizzes with the following alternatives:
   (1) Not true
   (2) True and easily provable in Agda
   (3) True and takes more work to prove in Agda
   (4) True and cannot be proved in Agda without additional axioms
*)
(* QUIZ *)
(** Is the following proposition provable?
``
      forall (c : com) (st st' : state),
        st =[ skip ; c ]=> st' ->
        st =[ c ]=> st'
``
    (1) Yes

    (2) No

    (3) Not sure

*)
(* HIDE *)
Lemma quiz1_answer :  forall c st st',
    st =[ skip ; c ]=> st' ->
    st =[ c ]=> st'.
Proof.
   intros c st st' E.
   inversion E.
   inversion H1.
   subst.
   assumption.
Qed.

(* /HIDE *)
(* /QUIZ *)
(* QUIZ *)
(** Is the following proposition provable?
``
      forall (c1 c2 : com) (st st' : state),
          st =[ c1;c2 ]=> st' ->
          st =[ c1 ]=> st ->
          st =[ c2 ]=> st'
``
    (1) Yes

    (2) No

    (3) Not sure

*)
(* INSTRUCTORS: Answer is given later as it depends on
   ceval_deterministic *)
(* /QUIZ *)
(* QUIZ *)
(** Is the following proposition provable?
``
      forall (b : bexp) (c : com) (st st' : state),
          st =[ if b then c else c end ]=> st' ->
          st =[ c ]=> st'
``
    (1) Yes

    (2) No

    (3) Not sure

*)
(* INSTRUCTORS *)
Lemma quiz3_answer: forall (b : bexp) (c : com) (st st' : state),
    st =[ if b then c else c end`=> st' ->
    st =[ c ]=> st'.
Proof.
  intros b c st st' H. inversion H.
  subst. assumption.
  subst. assumption.
Qed.
(* /INSTRUCTORS *)
(* /QUIZ *)
(* QUIZ *)
(** Is the following proposition provable?
``
      forall b : bexp,
         (forall st, ⟦ b ⟧ᵇ st = true) ->
         forall (c : com) (st : state),
           ~(exists st', st =[ while b do c end ]=> st')
``
    (1) Yes

    (2) No

    (3) Not sure

*)
(* HIDE *)
(* This one is tricky! *)
Lemma quiz4_answer: forall b : bexp,
    (forall st, ⟦ b ⟧ᵇ st = true) ->
    forall (c : com) (st : state),
      ~(exists st', st =[ while b do c end ]=> st').
Proof.
  intros b H c st.
  unfold not.
  intros W.
  destruct W as `st' WW`.
  remember <{ while b do c end }> as cc.
  induction WW; try discriminate Heqcc; inversion Heqcc; subst.
  - rewrite H in H0. discriminate H0.
  - apply IHWW2. reflexivity.
Qed.
(* /HIDE *)
(* /QUIZ *)
(* QUIZ *)
(** Is the following proposition provable?
``
      forall (b : bexp) (c : com) (st : state),
         ~(exists st', st =[ while b do c end ]=> st') ->
         forall st'', beval st'' b = true
``
    (1) Yes

    (2) No

    (3) Not sure

*)
(* HIDE *)
Lemma quiz5_answer: forall (b : bexp) (c : com) (st : state),
         ~(exists st', st =[ while b do c end ]=> st') ->
         forall st'', beval st'' b = true.
Proof.
  intros b c st H st''.
Abort. (* Can't make any progress - claim is false! *)
(* /HIDE *)
(* /QUIZ *)

(* ####################################################### *)
(** ** Determinism of Evaluation *)

(* LATER: Maybe this should go at the end of the file in a section
   marked optional?  Not everybody will want to spend time on it. *)
(* FULL *)
(** Changing from a computational to a relational definition of
    evaluation is a good move because it frees us from the artificial
    requirement that evaluation should be a total function.  But it
    also raises a question: Is the second definition of evaluation
    really a partial _function_?  Or is it possible that, beginning from
    the same state `st`, we could evaluate some command `c` in
    different ways to reach two different output states `st'` and
    `st''`?

    In fact, this cannot happen: `ceval` _is_ a partial function: *)
(* /FULL *)
(* LATER: Informal proof needed!  (And once can surely be found in
   some past CIS500 exam solutions!) *)

Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
(* FOLD *)
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  - (* ESkip *) reflexivity.
  - (* EAsgn *) reflexivity.
  - (* ESeq *)
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  - (* EIfTrue, b evaluates to true *)
      apply IHE1. assumption.
  - (* EIfTrue,  b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* EIfFalse, b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* EIfFalse, b evaluates to false *)
      apply IHE1. assumption.
  - (* EWhileFalse, b evaluates to false *)
    reflexivity.
  - (* EWhileFalse, b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  - (* EWhileTrue, b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* EWhileTrue, b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.  Qed.
(* /FOLD *)

(* HIDE *)
(* Answer to previous quiz. *)
Lemma quiz2_answer : forall c1 c2 st st',
    st =[ c1;c2 ]=> st' ->
    st =[ c1 ]=> st ->
    st =[ c2 ]=> st'.
Proof.
  intros c1 c2 st st' H1 H2.
  inversion H1. subst.
  rewrite ceval_deterministic with (c := c1) (st := st)
                                   (st1 := st) (st2 := st'0);
     assumption.
Qed.
(* /HIDE *)

(* FULL *)
(* ####################################################### *)
(** * Reasoning About Imp Programs *)

(* LATER: This section doesn't seem very useful — to anybody!  It
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

(** We'll get deeper into more systematic and powerful techniques for
    reasoning about Imp programs in _Programming Language
    Foundations_, but we can get some distance just working with the
    bare definitions.  This section explores some examples. *)

Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.

  (** Inverting `Heval` essentially forces Agda to expand one step of
      the `ceval` computation — in this case revealing that `st'`
      must be `st` extended with the new value of `X`, since `plus2`
      is an assignment. *)

  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.  Qed.

(* SOONER: This used to be recommended.  Should it be reinstated? *)
(* EX3? (XtimesYinZ_spec) *)
(** State and prove a specification of `XtimesYinZ`. *)

(* SOLUTION *)
(* Here is a specification in the style of plus2_spec *)
Theorem XtimesYinZ_spec1 : forall st nx ny st',
  st X = nx ->
  st Y = ny ->
  st =[ XtimesYinZ ]=> st' ->
  st' Z = nx * ny.
Proof.
  intros st nx ny st' HX HY Heval.
  (* Start by inverting the assignment *)
  inversion Heval. subst.
  apply t_update_eq.  Qed.

(* Though perhaps a cleaner specification would be: *)
Theorem XtimesYinZ_spec : forall st,
    st =[ XtimesYinZ ]=> (Z ↦ st X * st Y ; st ).
Proof. intros. apply EAsgn. reflexivity. Qed.

(* A less informative specification would be ... *)
Theorem XtimesYinZ_spec2 : forall st, exists st',
      st =[ XtimesYinZ ]=> st'.
Proof.
  intros. exists (Z ↦ st X * st Y ; st).
  apply EAsgn. reflexivity.
Qed.
(* /SOLUTION *)

(* GRADEMANUAL 3: XtimesYinZ_spec *)
(** `` *)

(* EX3! (loop_never_stops) *)
Theorem loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember <{ while true do skip end }> as loopdef
           eqn:Heqloopdef.

  (** Proceed by induction on the assumed derivation showing that
      `loopdef` terminates.  Most of the cases are immediately
      contradictory (and so can be solved in one step with
      `discriminate`). *)

  (* ADMITTED *)
  induction contra; try (discriminate Heqloopdef).
  - (* EWhileFalse *)
      injection Heqloopdef. intros H0 H1. rewrite -> H1 in H. discriminate H.
    - (* EWhileTrue *) apply IHcontra2. apply Heqloopdef. Qed.

(* /ADMITTED *)
(** `` *)

(* EX3 (no_whiles_eqv) *)
(** Consider the following function: *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | <{ skip }> =>
      true
  | <{ _ := _ }> =>
      true
  | <{ c1 ; c2 }> =>
      andb (no_whiles c1) (no_whiles c2)
  | <{ if _ then ct else cf end }> =>
      andb (no_whiles ct) (no_whiles cf)
  | <{ while _ do _ end }>  =>
      false
  end.

(** This predicate yields `true` just on programs that have no while
    loops.  Using `Inductive`, write a property `no_whilesR` such that
    `no_whilesR c` is provable exactly when `c` is a program with no
    while loops.  Then prove its equivalence with `no_whiles`. *)

Inductive no_whilesR: com -> Prop :=
 (* SOLUTION *)
 | nw_Skip: no_whilesR <{ skip }>
 | nw_Ass: forall x ae, no_whilesR <{ x := ae }>
 | nw_Seq: forall c1 c2,
     no_whilesR c1 ->
     no_whilesR c2 ->
     no_whilesR <{ c1 ; c2 }>
 | nw_If: forall be c1 c2,
     no_whilesR c1 ->
     no_whilesR c2 ->
     no_whilesR <{ if be then c1 else c2 end }>
(* /SOLUTION *)
.

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  (* ADMITTED *)
   intros; split.
  - (* -> *)
   induction c; intro Hc;
     try (simpl in Hc; rewrite andb_true_iff in Hc;
       destruct Hc as `Hc1 Hc2`);
     try constructor;
     try (apply IHc1; assumption); try (apply IHc2; assumption).
   + (* while *) discriminate Hc.
  - (* <- *)
    intro H. induction H; simpl;
      try reflexivity;
      try (rewrite IHno_whilesR1; rewrite IHno_whilesR2; reflexivity).
  Qed.
  (* /ADMITTED *)
(** `` *)

(* EX4 (no_whiles_terminating) *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem `no_whiles_terminating` that says this. *)
(** FULL: Use either `no_whiles` or `no_whilesR`, as you prefer. *)

(* SOLUTION *)
(* Here is a solution by induction on no_whilesR: *)
Theorem no_whiles_terminating : forall c st,
  no_whilesR c ->
  exists st',
  st =[ c ]=> st'.
Proof.
  intros c st H. generalize dependent st.
  induction H; intros; simpl.
  - (* nw_Skip *) exists st. constructor.
  - (* nw_Ass *) exists (x ↦ aeval st ae ; st).
    constructor. reflexivity.
  - (* nw_Seq *)
    destruct (IHno_whilesR1 st) as `st' IH'`.
    destruct (IHno_whilesR2 st') as `st'' IH''`.
    exists st''. apply ESeq with st'; assumption.
  - (* nw_If *)
    destruct (⟦ b ⟧ᵇ ste) eqn:Heqbv.
    + (* bv = true *)
      destruct (IHno_whilesR1 st) as `st' IH'`.
      exists st'. apply EIfTrue. rewrite Heqbv. reflexivity. assumption.
    + (* bv = false *)
      destruct (IHno_whilesR2 st) as `st' IH'`.
      exists st'. apply EIfFalse. rewrite Heqbv. reflexivity. assumption.
Qed.

(* And here is an alternative solution by induction on c: *)
Theorem no_whiles_terminating' : forall c st1,
  no_whiles c = true ->
  exists st2, st1 =[ c ]=> st2.
Proof.
  induction c; intros st1 Hb.

  - (* skip *)
    exists st1. apply ESkip.

  - (* := *)
    exists (x ↦ aeval st1 a ; st1). apply EAsgn. reflexivity.

  - (* ; *)
    simpl in Hb.
    rewrite andb_true_iff in Hb.
    destruct Hb as `Hb1 Hb2`.
    apply (IHc1 st1) in Hb1. destruct Hb1 as `st1' ceH1`.
    apply (IHc2 st1') in Hb2. destruct Hb2 as `st1'' ceH2`.
    exists st1''.
    apply ESeq with (st' := st1'); assumption.

  - (* if *)
    simpl in Hb. rewrite andb_true_iff in Hb.
    destruct Hb as `Hb1 Hb2`.
    destruct (beval st1 b) eqn:Heqbv.
    + (* EIfTrue *)
      apply (IHc1 st1) in Hb1.
      destruct Hb1 as `st2 Hce1`. exists st2.
      apply EIfTrue.
      * (* b is true *)
        rewrite <- Heqbv. reflexivity.
      * (* true branch eval *)
        assumption.
    + (* EIfFalse *)
      apply (IHc2 st1) in Hb2.
      destruct Hb2 as `st2 Hce2`. exists st2.
      apply EIfFalse.
      * (* b is false *)
        rewrite <- Heqbv. reflexivity.
      * (* false branch eval *)
        assumption.

  - (* while *)
    discriminate Hb.  Qed.
(* /SOLUTION *)

(* GRADE_MANUAL 6: no_whiles_terminating *)
(** `` *)
(* /FULL *)

(* LATER: The following section always gets skipped over when I (BCP)
   teach the course, because there isn't time to go through all the
   details and we're going to see the right way to do the same thing
   in a later chapter, so I am hiding it for now.  I wouldn't mind
   reinstating it for the use of advanced / self-study readers if
   somebody wants to write some text to really explain it, but what's
   there is a bit too telegraphic, so I'm removing it for now. *)
(* HIDE *)
(* ####################################################### *)
(** * Case Study (Optional) *)

(** Recall the factorial program (broken up into smaller pieces this
    time, for convenience of proving things about it).  *)

fact_body : Command
  <{ Y := Y * Z ;
     Z := Z - 1 }>.

fact_loop : Command
  <{ while ~(Z = 0) do
       fact_body
     end }>.

fact_com : Command
  <{ Z := X ;
     Y := 1 ;
     fact_loop }>.

(** Here is an alternative "mathematical" definition of the factorial
    function: *)

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

(** We would like to show that they agree — if we start `fact_com` in
    a state where variable `X` contains some number `n`, then it will
    terminate in a state where variable `Y` contains the factorial of
    `n`.

    To show this, we rely on the critical idea of a _loop
    invariant_. *)

fact_invariant (n:nat) (st:state) : Prop :=
  (st Y) * (real_fact (st Z)) = real_fact n.

(** We show that the body of the factorial loop preserves the invariant: *)

(* LATER: Needs an informal proof! *)
Theorem fact_body_preserves_invariant: forall st st' n,
     fact_invariant n st ->
     st Z <> 0 ->
     st =[ fact_body ]=> st' ->
     fact_invariant n st'.
(* FOLD *)
Proof.
  unfold fact_invariant, fact_body.
  intros st st' n Hm HZnz He.
  inversion He; subst; clear He.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  unfold t_update. simpl.
  (* Show that st Z = S z' for some z' *)
  destruct (st Z) as `| z'`.
    exfalso. apply HZnz. reflexivity.
  rewrite <- Hm. rewrite <- mult_assoc.
  replace (S z' - 1) with z' by lia.
  reflexivity.  Qed.
(* /FOLD *)

(** From this, we can show that the whole loop also preserves the
invariant: *)

Theorem fact_loop_preserves_invariant : forall st st' n,
     fact_invariant n st ->
     st =[ fact_loop ]=> st' ->
     fact_invariant n st'.
(* FOLD *)
Proof.
  intros st st' n H Hce.
  remember fact_loop as c.
  induction Hce; inversion Heqc; subst; clear Heqc.
  - (* EWhileFalse *)
    (* trivial when the loop doesn't run... *)
    assumption.
  - (* EWhileTrue *)
    (* if the loop does run, we know that fact_body preserves
       fact_invariant — we just need to assemble the pieces *)
    apply IHHce2.
      apply fact_body_preserves_invariant with st;
            try assumption.
      intros Contra. simpl in H0; subst.
      rewrite Contra in H0. inversion H0.
      reflexivity.  Qed.
(* /FOLD *)

(** Next, we show that, for any loop, if the loop terminates, then the
    condition guarding the loop must be false at the end: *)

Theorem guard_false_after_loop: forall b c st st',
     st =[ while b do c end ]=> st' ->
     beval st' b = false.
(* FOLD *)
Proof.
  intros b c st st' Hce.
  remember <{ while b do c end }> as cloop.
  induction Hce; inversion Heqcloop; subst; clear Heqcloop.
  - (* EWhileFalse *)
    assumption.
  - (* EWhileTrue *)
    apply IHHce2. reflexivity.  Qed.
(* /FOLD *)

(** Finally, we can patching it all together... *)

Theorem fact_com_correct : forall st st' n,
     st X = n ->
     st =[ fact_com ]=> st' ->
     st' Y = real_fact n.
(* FOLD *)
Proof.
  intros st st' n HX Hce.
  inversion Hce; subst; clear Hce.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  inversion H1; subst; clear H1.
  rename st' into st''. simpl in H5.
  (* The invariant is true before the loop runs... *)
  remember (Y ↦ 1 ; Z ↦ st X ; st) as st' eqn:Heqst'.
  assert (fact_invariant (st X) st').
    subst. unfold fact_invariant, t_update. simpl. lia.
  (* ...so when the loop is done running, the invariant
     is maintained *)
  assert (fact_invariant (st X) st'').
    apply fact_loop_preserves_invariant with st'; assumption.
  unfold fact_invariant in H0.
  (* Finally, if the loop terminated, then Z is 0; so Y must be
     factorial of X *)
  apply guard_false_after_loop in H5. simpl in H5.
  destruct (st'' Z) eqn:E.
  - (* st'' Z = 0 *) simpl in H0. lia.
  - (* st'' Z > 0 (impossible) *) inversion H5.
Qed.
(* /FOLD *)

(** One might wonder whether all this work with poking at states and
    unfolding definitions could be ameliorated with some more powerful
    lemmas and/or more uniform reasoning principles... Indeed, this is
    exactly the topic of the coming chapter \CHAP{Hoare} in _Programming
    Language Foundations_! *)

(* FULL *)
(* EX4? (subtractSlowly_spec) *)
(** Prove a specification for `subtractSlowly`, using the above
    specification of `fact_com` and the invariant below as
    guides. *)

ss_invariant (n:nat) (z:nat) (st:state) : Prop :=
  ((st Z) - st X) = (z - n).

(* SOLUTION *)
Theorem ss_body_preserves_invariant : forall st n z st',
     ss_invariant n z st ->
     st X <> 0 ->
     st =[ subtractSlowlyBody ]=> st' ->
     ss_invariant n z st'.
Proof.
  unfold ss_invariant.
  intros st n z st' H Hnz He.
  inversion He; subst; clear He.
  inversion H2; subst; clear H2.
  inversion H5; subst; clear H5.
  unfold t_update. simpl.
  lia.   (* Interestingly, this is all we need here  — although only after a perceptible delay! *)
Qed.

Theorem ss_preserves_invariant : forall st n z st',
     ss_invariant n z st ->
     st =[ subtractSlowly ]=> st'  ->
     ss_invariant n z st'.
Proof.
  intros st n z st' H He.
  remember subtractSlowly as c.
  induction He; inversion Heqc; subst; clear Heqc.
  - (* EWhileFalse *)
    assumption.
  - (* EWhileTrue *)
    apply IHHe2; try reflexivity.
    apply ss_body_preserves_invariant with st; try assumption.
    intros Contra. simpl in H0. rewrite Contra in H0. inversion H0.  Qed.

Theorem ss_correct : forall st n z st',
     st X = n ->
     st Z = z ->
     st =[ subtractSlowly ]=> st' ->
     st' Z = (z - n).
Proof.
  intros st n z st' HX HZ He.
  assert (ss_invariant n z st).
    unfold ss_invariant.
    subst.
    reflexivity.
  assert (ss_invariant n z st').
    apply ss_preserves_invariant with st; assumption.
  unfold ss_invariant in H0.
  apply guard_false_after_loop in He. simpl in He.
  destruct (st' X) eqn:E.
  - (* st' X = 0 *) lia.
  - (* st' X > 0 (impossible) *) inversion He.
Qed.
(* /SOLUTION *)
(** `` *)
(* /HIDE *)

(* TERSE: HIDEFROMHTML *)
(* HIDE: N.b.: No "FULL" here because this exercise is needed for the
   TERSE version of the Smallstep chapter. *)
(* ####################################################### *)
(** * Additional Exercises *)

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
      st =[ if_then_else (⟦ b ⟧ᵇ st) c1 c2 ]=> st' / s ->
      st =[ if b then c1 else c2 end ]=> st' / s
  | EWhileFalse : forall c b st,
      ⟦ b ⟧ᵇ st = false ->
      st =[ while b do c end ]=> st / SContinue
  | EWhileContinue : forall c b st st' st'',
      ⟦ b ⟧ᵇ st = true ->
      st  =[ c ]=> st' / SContinue ->
      st' =[ while b do c end ]=> st'' / SContinue ->
      st  =[ while b do c end ]=> st'' / SContinue
  | EWhileBreak : forall c b st st',
      ⟦ b ⟧ᵇ st = true ->
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
  ⟦ b ⟧ᵇ st = true ->
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
      st =[ if_then_else (⟦ b ⟧ᵇ st) c1 c2 ]=> st' / s ->
      st =[ if b then c1 else c2 end ]=> st' / s
  | EWhileFalse : forall c b st,
      ⟦ b ⟧ᵇ st = false ->
      st =[ while b do c end ]=> st / SNormal
  | EWhileContinue : forall c b st st' st'',
      ⟦ b ⟧ᵇ st = true ->
      st  =[ c ]=> st' / SNormal ->
      st' =[ while b do c end ]=> st'' / SNormal ->
      st  =[ while b do c end ]=> st'' / SNormal
(* HIDE: BETTER version!
  | EWhileContinue : forall c b st st' st'' s,
      ⟦ b ⟧ᵇ st = true ->
      c / st ==> SNormal / st' ->
      (while b do c end) / st' ==> s / st'' ->
      (while b do cend) / st ==> s / st''
*)
  | EWhileThrow : forall c b st st',
      ⟦ b ⟧ᵇ st = true ->
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
