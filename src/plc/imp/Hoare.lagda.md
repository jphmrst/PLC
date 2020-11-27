---
title     : "Hoare: A logic for imperative programs"
layout    : page
prev      : /Equiv/
permalink : /Hoare/
next      : /Step/
---

```
module plc.imp.Hoare where
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
open import plc.imp.Equiv
```

(* NOTATION: SOONER: The presentation in Hoare2.v and HoareAsLogic.v
   would be very much streamlined if we introduced a conjunction
   operator lifted to assertions (along with lifting
   implication)... This comment may be dead now -- check! *)
(* NOTATION: LATER: For consistency with formal decorated programs in
   Hoare2, we should put the annotation on Seq before the ; instead
   of after! *)
(* NOTATION: LATER: A more ambitious idea for streamlining notation:
  consider making P and Q in hoare triples be bexps instead of
  state->Prop.  Main issue is whether this is expressive enough to
  handle the assertions actually used in Hoare2!  E.g., what about
  max??  If it's just one or two like this, we can build them in, but
  if it's a lot... *)
(* LATER: What about typesetting multi-line triples as
      ⦃  P ⦄
         c
      ⦃  Q ⦄
   instead of
        ⦃  P ⦄
      c
        ⦃  Q ⦄
   when we print them? *)
(* SOONER: BCP 19: For the second midterm in the the 19fa instance of
   CIS500, we did a little experiment with setting up a
   total-correctness Hoare logic for Imp.  Would be fun to turn that
   into either an extended exercise or perhaps a little chapter on its
   own. I can give the .v file to anyone that wants. (It is
   technically pretty complete but needs words and a couple more
   examples.) *)
(* INSTRUCTORS: In the first (80-minute) lecture, going at a moderate
   pace, I (BCP) covered up through the sequencing rule.  The second
   lecture covered the rest of the file and a bit of Hoare2, with
   plenty of time for real-time clicker quizzes and WORKINCLASS coq
   experiments.  The students seemed to like these.

   Covering both Hoare and Hoare2 in one week (two 80-minute lectures)
   is challenging.  Don't get bogged down in digressions!
*)
(* INSTRUCTORS: One tricky presentation issue in this chapter is worth
   mentioning: We have two presentations of decorated programs, and the
   natural criteria for "where is it good to put the annotations?" are
   different.  For the informal ones, requiring a few more annotations
   is fine if it leads to rules that are simpler to explain or
   decorated programs that are easier to understand.  For the formal
   ones, it is nice to remove as many annotations as possible for the
   sake of elegance, shorter formal objects (decorated programs and
   proofs of their verification conditions), and a VC generator that
   is easier to explain.

   For purposes of teaching beginning students, we think the informal
   decorated programs are more important (we don't expect students to
   fully understand the formal ones or work with them very much), so
   we should favor their needs.  This has led us to the current
   presentation.

   It might be worth adding an (optional) exercise asking how many of
   the assertion annotations can be removed from dcom.  E.g.,
   Alexandre Pilkiewicz suggests the following alternate type for the
   decorated while construct:

     | DCWhile : bexp -> Assertion -> dcom -> dcom

   This leads to a simpler rule in the VC generator, which is much
   easier to explain:

     | DCWhile b P' c  => ((fun st => post c st /\ bassn b st) ->> P')
                         /\ (P ->> post c)
                         /\ verification_conditions P' c

   ([post c] is the loop invariant).
   His full development (based on an old version of our formalized
   decorated programs, unfortunately), can be found in the file
   /underconstruction/PilkiewiczFormalizedDecorated.v

   CH: I think we should make a distinction between a VCgen, which
   only needs a top-level spec and loop invariants, and the automation
   support we provide for formal decorated programs, whose main
   purpose is to be beautiful and easy to read complete correctness
   proofs, not terse hints to an obscure automatic VCgen tool
*)
(* HIDE: BCP 10/18: Introducing a symbolic operator for
   conjunction (and one for negation) of assertions might make things
   look smoother in some places, but I think overall it's not a win --
   too much conceptual overhead.  It's more tempting to go all the way
   and make up a whole new syntax for assertions. *)
(* HIDE: At some point we should try one more time to see if it's
   possible to use single curly braces for Hoare triples.  The Coq
   manual says "For the sake of factorization with Coq predefined
   rules, simple rules have to be observed for notations starting with
   a symbol: e.g., rules starting with { or ( should be put at level
   0."  Maybe this suggests a way forward...?
   BCP 10/18: Nope.  Writing
      Notation "'{' P '}' c '{' Q '}'" :=
        (hoare_triple P c Q) (at level 0, c at next level)
        : hoare_spec_scope.
   yields
       Error: A notation must include at least one symbol.
*)
(* SOONER: For the second midterm in 19fa for CIS500, we whacked
   together a little total-correctness Hoare logic. Might be fun to
   include it, either at the end of this chapter or in its own little
   chapter. Someone will need to write some words, though. *)
(* LATER: This file and all later ones should make a habit of always
   presenting both syntax and semantics of new language constructs in
   informal style as well as formal.  See MoreStlc.v for a
   template. *)
(* LATER: CH (2013): Where should the IF1, REPEAT, and HAVOC exercises
   come?  before or after decorated programs? (at least REPEAT is
   quite complicated to understand without understanding loop
   invariants)
*)
(* LATER: in the HTML, consider changing the sizes of some symbols,
   e.g. make forall bigger and make <<->> and ->> and |-> smaller.
   Check that both full and terse look good.
 *)


(** FULL: In the final chaper of _Logical Foundations_ (_Software
    Foundations_, volume 1), we began applying the mathematical tools
    developed in the first part of the course to studying the theory
    of a small programming language, Imp.

    - We defined a type of _abstract syntax trees_ for Imp, together
      with an _evaluation relation_ (a partial function on states)
      that specifies the _operational semantics_ of programs.

      The language we defined, though small, captures some of the key
      features of full-blown languages like C, C++, and Java,
      including the fundamental notion of mutable state and some
      common control structures.

    - We proved a number of _metatheoretic properties_ -- "meta" in
      the sense that they are properties of the language as a whole,
      rather than of particular programs in the language.  These
      included:

        - determinism of evaluation

        - equivalence of some different ways of writing down the
          definitions (e.g., functional and relational definitions of
          arithmetic expression evaluation)

        - guaranteed termination of certain classes of programs

        - correctness (in the sense of preserving meaning) of a number
          of useful program transformations

        - behavioral equivalence of programs (in the \CHAP{Equiv}
          chapter). *)

(** FULL: If we stopped here, we would already have something useful: a set
    of tools for defining and discussing programming languages and
    language features that are mathematically precise, flexible, and
    easy to work with, applied to a set of key properties.  All of
    these properties are things that language designers, compiler
    writers, and users might care about knowing.  Indeed, many of them
    are so fundamental to our understanding of the programming
    languages we deal with that we might not consciously recognize
    them as "theorems."  But properties that seem intuitively obvious
    can sometimes be quite subtle (sometimes also subtly wrong!).

    We'll return to the theme of metatheoretic properties of whole
    languages later in this volume when we discuss _types_ and _type
    soundness_.  In this chapter, though, we turn to a different set
    of issues.
*)

(* HIDE: MRC'20: The terse version used to start with just an outline of
   what we've done and of this chapter, but it never mentioned Hoare logic!
   This text seems like a better intro. *)
(** Our goal is to carry out some simple examples of _program
    verification_ -- i.e., to use the precise definition of Imp to
    prove formally that particular programs satisfy particular
    specifications of their behavior.  We'll develop a reasoning
    system called _Floyd-Hoare Logic_ -- often shortened to just
    _Hoare Logic_ -- in which each of the syntactic constructs of Imp
    is equipped with a generic "proof rule" that can be used to reason
    compositionally about the correctness of programs involving this
    construct.

    Hoare Logic originated in the 1960s, and it continues to be the
    subject of intensive research right up to the present day.  It
    lies at the core of a multitude of tools that are being used in
    academia and industry to specify and verify real software systems.

    Hoare Logic combines two beautiful ideas: a natural way of writing
    down _specifications_ of programs, and a _compositional proof
    technique_ for proving that programs are correct with respect to
    such specifications -- where by "compositional" we mean that the
    structure of proofs directly mirrors the structure of the programs
    that they are about. *)
(* LATER: Add some material talking about particular impressive
   examples of program verification using successors of Hoare logic.
   It would also be good to talk a little more about the history of
   Hoare logic and give some pointers to good books (Esp. JCR's). *)
(* HIDE: MRC'20: this is the former terse intro.
    What we've done so far:

    - Formalized Imp
         - identifiers and states
         - abstract syntax trees
         - evaluation functions (for [aexp]s and [bexp]s)
         - evaluation relation (for commands)

    - Proved some _metatheoretic_ properties
        - determinism of evaluation
        - equivalence of some different ways of writing down the
          definitions (e.g., functional and relational definitions of
          arithmetic expression evaluation)
        - guaranteed termination of certain classes of programs
        - meaning-preservation of some program transformations
        - behavioral equivalence of programs ([Equiv])

    We've dealt with a few sorts of properties of Imp programs:
      - Termination
      - Nontermination
      - Equivalence

    Topic:
      - A systematic method for reasoning about the _functional
        correctness_ of programs in Imp

    Goals:
      - a natural notation for _program specifications_ and
      - a _compositional_ proof technique for program correctness

    Plan:
      - specifications (assertions / Hoare triples)
      - proof rules
      - loop invariants
      - decorated programs
      - examples *)

(* ####################################################### *)
(** * Assertions *)

(** An _assertion_ is a claim about the current state of memory. We will
    use assertions to write program specifications. *)

Definition Assertion := state -> Prop.

(* HIDE: MRC'20: pulled up these examples from the quiz/optional
   exercise so that there would be some modeling of the kinds of
   answers we expect. *)

(** For example,

    - [fun st => st X = 3] holds if the value of [X] according to [st] is [3],

    - [fun st => True] always holds, and

    - [fun st => False] never holds. *)

(* FULL *)
(* EX1? (assertions) *)
(** Paraphrase the following assertions in English (or your favorite
    natural language). *)

Module ExAssertions.
Definition assn1 : Assertion := fun st => st X <= st Y.
Definition assn2 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition assn3 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition assn4 : Assertion :=
  fun st => st Z = max (st X) (st Y).
(* SOLUTION *)
(* SOONER: Double-check this -- looks wrong: *)
(*
   1) X contains the value 3.
   2) The value of X is less or equal than the value of Y.
   3) The value of X is 3 or is less or equal than the value of Y.
   4) The value of Z is the integer square root of X.
*)
(* /SOLUTION *)
End ExAssertions.
(** [] *)
(* /FULL *)

(** FULL: This way of writing assertions can be a little bit heavy,
    for two reasons: (1) every single assertion that we ever write is
    going to begin with [fun st => ]; and (2) this state [st] is the
    only one that we ever use to look up variables in assertions (we
    will never need to talk about two different memory states at the
    same time).  For discussing examples informally, we'll adopt some
    simplifying conventions: we'll drop the initial [fun st =>], and
    we'll write just [X] to mean [st X].  Thus, instead of writing *)
(** TERSE: *** *)
(** TERSE: Informally, instead of writing *)
(**

      fun st => st X = m

    we'll write just

      X = m

*)

(** FULL: This example also illustrates a convention that we'll use
    throughout the Hoare Logic chapters: in informal assertions,
    capital letters like [X], [Y], and [Z] are Imp variables, while
    lowercase letters like [x], [y], [m], and [n] are ordinary Coq
    variables (of type [nat]).  This is why, when translating from
    informal to formal, we replace [X] with [st X] but leave [m]
    alone. *)

(** TERSE: *** *)

(** Given two assertions [P] and [Q], we say that [P] _implies_ [Q],
    written [P ->> Q], if, whenever [P] holds in some state [st], [Q]
    also holds. *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Declare Scope hoare_spec_scope.
Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

(** FULL: (The [hoare_spec_scope] annotation here tells Coq that this
    notation is not global but is intended to be used in particular
    contexts.  The [Open Scope] tells Coq that this file is one such
    context.) *)

(** We'll also want the "iff" variant of implication between
    assertions: *)

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

(* LATER: Say more about that?? *)

(* HIDE: BCP 10/18: The following is a really good attempt (by
   Li-Yao) to lighten the notation for assertions.  It hasn't quite
   converged (e.g., we're not happy about [ap]), and there is an
   uncomfortable amount of magic to it, but we should think about it
   some more...

   One thing to consider adding is turning bassn into a coercion.
   APT: I've tried that and it helps.

   APT: Overall, I really like this new notation a LOT and I would
   favor switching to it. Remainder of this chapter and Hoare2
   are converted to use it.

   MRC'20:  The notation is great in the Coq source code!  Thanks for all the
   hard work.  It makes almost everything much more pleasant to read.  There are
   a couple further improvements that I wonder about.  (I'm not qualified to do them!)
     1. It would help to have a bit of explanation of what's going on, even
        if it were just hidden for instructors.  I do confess I don't understand some
        of this implicit coercion magic, nor does the Coq manual chapter on it read
        very easily for me.
     2. It's mysterious to me why sometimes I need to write [%assertion] or
        [: Assertion] to get parsing to work right.  Some more explanation of that,
        with some examples to play with, would be nice.
     3. Though the notations look great in the Coq source code, they work somewhat
        less well in the middle of a proof.  Coq almost immediately starts expanding
        them in the proof state, and that gets confusing (to me and my students)
        rather quickly.  I wonder whether there's a way to make Coq less aggressive
        about this?
 *)

(* HIDE: (* WORK IN PROGRESS... *) *)

(** TERSE: *** *)

(** Our convention can be implemented uses Coq coercions and anotation
    scopes (much as we did with [%imp] in \CHAP{Imp}) to automatically
    lift [aexp]s, numbers, and [Prop]s into [Assertion]s when they appear
    in the [%assertion] scope or when Coq knows the type of an
    expression is [Assertion]. *)

(* HIDE: Assertion-level arith expressions.  (BCP: Not sure this is
   an optimally clear name.) *)
Definition Aexp : Type := state -> nat.

(* HIDE: Some coercions *)
Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.

(* HIDE: maybe this one should be explicit. *)
Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.

(* HIDE: Make things easily unfoldable. *)
(* HIDE: MRC'20: Recording this here because it took a merry chase through
   the Coq manual to find it:  this version of the [Arguments] command is
   documented under [simpl]. *)
(* SOONER: Make sure Arguments is explained somewhere *)
Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.

Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.

(* HIDE: (APT) For some reason, True%assertion does not produce an
   assertion, whereas (True:Assertion) does. (Lyxia) This is because
   coercions ignore scope. *)

(* HIDE: Open assertion_scope locally. *)
Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).

(* NOTATION: BCP 20: It probably makes sense now to put all these in a
   custom grammar, so that we can really control how it looks and get
   rid of things like ap *)
Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st ->  assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <->  assert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.

(** TERSE: Lift functions to operate on assertion expressions. *)

(** FULL: One small limitation of this approach is that we don't have
    an automatic way to coerce function applications that appear
    within an assertion to make appropriate use of the state.
    Instead, we use an explicit [ap] operator to lift the function. *)

Definition ap {X} (f : nat -> X) (x : Aexp) :=
  fun st => f (x st).

Definition ap2 {X} (f : nat -> nat -> X) (x : Aexp) (y : Aexp) (st : state) :=
  f (x st) (y st).

Module ExPrettyAssertions.
Definition ex1 : Assertion := X = 3.
Definition ex2 : Assertion := True.
Definition ex3 : Assertion := False.

Definition assn1 : Assertion := X <= Y.
Definition assn2 : Assertion := X = 3 \/ X <= Y.
Definition assn3 : Assertion :=
  Z * Z <= X  /\  ~ (((ap S Z) * (ap S Z)) <= X).
Definition assn4 : Assertion :=
  Z = ap2 max X Y.
End ExPrettyAssertions.


(* ####################################################### *)
(** * Hoare Triples, Informally *)

(** A _Hoare triple_ is a claim about the state before and after executing
    a command.  A standard notation is

      {P} c {Q}

    meaning:

      - If command [c] begins execution in a state satisfying assertion [P],
      - and if [c] eventually terminates in some final state,
      - then that final state will satisfy the assertion [Q].

    Assertion [P] is called the _precondition_ of the triple, and [Q] is
    the _postcondition_.

    Because single braces are already used in other ways in Coq, we'll write
    Hoare triples with double braces:

       ⦃ P ⦄ c ⦃ Q⦄

 *)
(** TERSE: *** *)
(**
    For example,

    - [⦃ X = 0 ⦄ X := X + 1 ⦃ X = 1 ⦄] is a valid Hoare triple,
      stating that command [X := X + 1] would transform a state in which
      [X = 0] to a state in which [X = 1].

    - [⦃ X = m ⦄ X := X + 1 ⦃ X = m + 1 ⦄], is also a valid Hoare triple.
      It's even more descriptive of the exact behavior of that command than
      the previous example. *)
(* SOONER: BCP: Not 100% sure I agree with the wording.  When m is
   fixed, these descriptions are equally exact (though different,
   unless m is 0) *)

(* FULL *)
(* EX1? (triples) *)
(* /FULL *)
(* TERSE *)
(* /TERSE *)
(* TERSE: QUIETSOLUTION *)
(* FULL: SOLUTION *)

(*
1) If command c terminates starting in an arbitrary state it produces a
   state where the value of X is equal to 5.
2) Starting in a state where the value of X is m, if c terminates the
   value of X is equal to m+5.
3) Starting in a state where the value of X less or equal than the
   value of Y, if c terminates then the value of Y is less or equal
   than the value of X.
4) c doesn't terminate on any starting state
5) If c terminates then Y contains as a value the factorial of the
   initial value of X.
6) Starting in a state in which the value of X is equal to m, if c
   terminates starting in an arbitray state then Z contains the
   integer square root of the initial value of X.
*)
(* FULL: /SOLUTION *)
(* TERSE: /QUIETSOLUTION *)
(* FULL *)
(** [] *)

(* /FULL *)
(* INSTRUCTORS: SOLUTION: All are valid except the 5th. *)
(* FULL *)
(* EX1? (valid_triples) *)
(** Which of the following Hoare triples are _valid_ -- i.e., the
    claimed relation between [P], [c], and [Q] is true?

   1) ⦃ True ⦄ X := 5 ⦃ X = 5⦄

   2) ⦃ X = 2 ⦄ X := X + 1 ⦃ X = 3⦄

   3) ⦃ True ⦄ X := 5; Y := 0 ⦃ X = 5⦄

   4) ⦃ X = 2 /\ X = 3 ⦄ X := 5 ⦃ X = 0⦄

   5) ⦃ True ⦄ skip ⦃ False⦄

   6) ⦃ False ⦄ skip ⦃ True⦄

   7) ⦃ True ⦄ while true do skip end ⦃ False⦄

   8) ⦃ X = 0⦄
        while X = 0 do X := X + 1 end
      ⦃ X = 1⦄

   9) ⦃ X = 1⦄
        while ~(X = 0) do X := X + 1 end
      ⦃ X = 100⦄

*)
(* FULL: SOLUTION *)
(* All are valid except the 5th. *)
(* FULL: /SOLUTION *)
(** [] *)
(* /FULL *)

(* ####################################################### *)
(** * Hoare Triples, Formally *)

(** We can formalize Hoare triples and their notation in Coq as follows: *)

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st'  ->
     P st  ->
     Q st'.

Notation "⦃  P ⦄  c  ⦃ Q  ⦄" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.
Check (⦃ True ⦄ X := 0 ⦃ True ⦄).

(* HIDE: AAA: If I try to set the notation as {P} c {Q}, I get the
   following error:

     Error: A notation must include at least one symbol.

   Maybe we could use other braces? For instance, I tried it with [P]
   c [Q] and it seems to work (although I don't know how that would
   affect the rest of the book).

   BCP: Let's try with the "squashed" double braces for a while and
   see if we like it.

   P.S.
   This works:
      Notation "{ x }" := (x) (at level 0, x at level 99).
   But this doesn't:
      Notation "{ P }  c  { Q }" :=
        (hoare_triple P c Q)
        (at level 0, P at level 99, c at level 99, Q at level 99)
      : hoare_spec_scope.
   Why??
*)

(** TERSE: *** *)

(* EX1 (hoare_post_true) *)

(** Prove that if [Q] holds in every state, then any triple with [Q]
    as its postcondition is valid. *)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  ⦃ P ⦄ c ⦃ Q ⦄.
(** [] *)

(* EX1 (hoare_pre_false) *)

(** Prove that if [P] holds in no state, then any triple with [P] as
    its precondition is valid. *)

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  ⦃ P ⦄ c ⦃ Q ⦄.
(** [] *)

(* ####################################################### *)
(** * Proof Rules *)

(** FULL: The goal of Hoare logic is to provide a _compositional_
    method for proving the validity of specific Hoare triples.  That
    is, we want the structure of a program's correctness proof to
    mirror the structure of the program itself.  To this end, in the
    sections below, we'll introduce a rule for reasoning about each of
    the different syntactic forms of commands in Imp -- one for
    assignment, one for sequencing, one for conditionals, etc. -- plus
    a couple of "structural" rules for gluing things together.  We
    will then be able to prove programs correct using these proof
    rules, without ever unfolding the definition of [hoare_triple]. *)
(** TERSE: Plan:
      - introduce one "proof rule" for each Imp syntactic form...
      - plus a couple of "structural rules" that help glue proofs
        together;
      - prove programs correct using these proof rules, without ever
        unfolding the definition of [hoare_triple] *)

(* ####################################################### *)
(** ** Assignment *)

(* HIDE: MRC'20: the motivation of this rule had been stated in
   terms of transfering a property from the RHS of the assignment
   to the LHS.  That led to two issues, at least for me and my
   students.  First, "transfer" usually means moving from one
   place to another. (e.g., consider a money transfer.)  But that's
   not really what happens:  we don't have to lose the property
   on one side to gain it on the other.  Second and more importantly,
   the discussion had been focusing on moving from the precondition
   to the postcondition, which sets up exactly the wrong intuition
   for the backwards Hoare assignment rule.  That really tripped
   up students, and required some fancy talking on my part.

   So I propose the rewrite I give below, which attempts to establish
   from the beginning the intuition of moving from the postcondition
   to the precondition. *)

(** FULL: The rule for assignment is the most fundamental of the Hoare
    logic proof rules.  Here's how it works.

    Consider this incomplete Hoare triple:

       ⦃ ??? ⦄  X := Y  ⦃ X = 1 ⦄


    We want to assign [Y] to [X] and finish in a state where [X] is [1].
    What could the precondition be?

    One possibility is [Y = 1], because if [Y] is already [1] then
    assigning it to [X] causes [X] to be [1].  That leads to a valid
    Hoare triple:

       ⦃ Y = 1 ⦄  X := Y  ⦃ X = 1 ⦄

    It may seem as though coming up with that precondition must have
    taken some clever thought.  But there is a mechanical way we could
    have done it: if we take the postcondition [X = 1] and in it
    replace [X] with [Y]---that is, replace the left-hand side of the
    assignment statement with the right-hand side---we get the
    precondition, [Y = 1]. *)

(** TERSE: How can we complete this triple?

       ⦃ ??? ⦄  X := Y  ⦃ X = 1 ⦄

    One possibility is:

       ⦃ Y = 1 ⦄  X := Y  ⦃ X = 1 ⦄


    The precondition is just the postcondition, but with [X] replaced
    by [Y]. *)

(** FULL: That same technique works in more complicated cases.  For
    example,

       ⦃ ??? ⦄  X := X + Y  ⦃ X = 1 ⦄

    If we replace the [X] in [X = 1] with [X + Y], we get [X + Y = 1].
    That again leads to a valid Hoare triple:

       ⦃ X + Y = 1 ⦄  X := X + Y  ⦃ X = 1 ⦄

    Why does this technique work?  The postcondition identifies some
    property [P] that we want to hold of the variable [X] being
    assigned.  In this case, [P] is "equals [1]".  To complete the
    triple and make it valid, we need to identify a precondition that
    guarantees that property will hold of [X].  Such a precondition
    must ensure that the same property holds of _whatever is being
    assigned to_ [X].  So, in the example, we need "equals [1]" to
    hold of [X + Y].  That's exactly what the technique guarantees.
*)

(** TERSE: *** *)
(** TERSE: Another example:

       ⦃ ??? ⦄  X := X + Y  ⦃ X = 1 ⦄

    Replace [X] with [X + Y]:

       ⦃ X + Y = 1 ⦄  X := X + Y  ⦃ X = 1 ⦄

    This works because "equals 1" holding of [X] is guaranteed
    by "equals 1" holding of whatever is being assigned to [X]. *)

(** TERSE: *** *)

(** In general, the postcondition could be some arbitrary assertion
    [Q], and the right-hand side of the assignment could be some
    arithmetic expression [a]:

       ⦃ ??? ⦄  X := a  ⦃ Q ⦄

    The precondition would then be [Q], but with any occurrences of
    [X] in it replaced by [a].  Let's introduce a notation for this
    idea of replacing occurrences: Define [Q [X |-> a]] to mean "[Q]
    where [a] is substituted in place of [X]".

    That yields the Hoare logic rule for assignment:

      ⦃ Q [X |-> a] ⦄  X := a  ⦃ Q ⦄

    One way of reading that rule is: If you want statement [X := a]
    to terminate in a state that satisfies assertion [Q], then it
    suffices to start in a state that also satisfies [Q], except
    where [a] is substituted for every occurrence of [X].

    To many people, this rule seems "backwards" at first, because
    it proceeds from the postcondition to the precondition.  Actually
    it makes good sense to go in this direction: the postcondition is
    often what is more important, because it characterizes what we
    can assume afer running the code.

    Nonetheless, it's also possible to formulate a "forward" assignment
    rule.  We'll do that later in some exercises. *)

(** TERSE: *** *)

(** Here are some valid instances of the assignment rule:

      ⦃ (X <= 5) [X |-> X + 1] ⦄     (that is, X + 1 <= 5)
      X := X + 1
      ⦃ X <= 5 ⦄

      ⦃ (X = 3) [X |-> 3] ⦄          (that is, 3 = 3)
      X := 3
      ⦃ X = 3 ⦄

      ⦃ (0 <= X /\ X <= 5) [X |-> 3]  (that is, 0 <= 3 /\ 3 <= 5)
      X := 3
      ⦃ 0 <= X /\ X <= 5 ⦄

*)

(** TERSE: *** *)

(** To formalize the rule, we must first formalize the idea of
    "substituting an expression for an Imp variable in an assertion",
    which we refer to as assertion substitution, or [assn_sub].  That
    is, given a proposition [P], a variable [X], and an arithmetic
    expression [a], we want to derive another proposition [P'] that is
    just the same as [P] except that [P'] should mention [a] wherever
    [P] mentions [X]. *)

(** TERSE: *** *)
(** Since [P] is an arbitrary Coq assertion, we can't directly "edit"
    its text.  However, we can achieve the same effect by evaluating
    [P] in an updated state: *)

Definition assn_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level, a custom com).

(** That is, [P [X |-> a]] stands for an assertion -- let's call it [P'] --
    that is just like [P] except that, wherever [P] looks up the
    variable [X] in the current state, [P'] instead uses the value
    of the expression [a]. *)

(** TERSE: *** *)

(** To see how this works, let's calculate what happens with a couple
    of examples.  First, suppose [P'] is [(X <= 5) [X |-> 3]] -- that
    is, more formally, [P'] is the Coq expression

    fun st =>
      (fun st' => st' X <= 5)
      (X !-> aeval st 3 ; st),

    which simplifies to

    fun st =>
      (fun st' => st' X <= 5)
      (X !-> 3 ; st)

    and further simplifies to

    fun st =>
      ((X !-> 3 ; st) X) <= 5

    and finally to

    fun st =>
      3 <= 5.

    That is, [P'] is the assertion that [3] is less than or equal to
    [5] (as expected). *)

(** TERSE: *** *)

(** For a more interesting example, suppose [P'] is [(X <= 5) [X |->
    X + 1]].  Formally, [P'] is the Coq expression

    fun st =>
      (fun st' => st' X <= 5)
      (X !-> aeval st (X + 1) ; st),

    which simplifies to

    fun st =>
      (X !-> aeval st (X + 1) ; st) X <= 5

    and further simplifies to

    fun st =>
      (aeval st (X + 1)) <= 5.

    That is, [P'] is the assertion that [X + 1] is at most [5].
*)

(** TERSE: *** *)

(** Now, using the concept of substitution, we can give the precise
    proof rule for assignment:
[[[
      ------------------------------ (hoare_asgn)
      ⦃ Q [X |-> a] ⦄ X := a ⦃ Q⦄
]]]
*)

(** We can prove formally that this rule is indeed valid. *)

Theorem hoare_asgn : forall Q X a,
  ⦃ Q [X |-> a] ⦄ X := a ⦃ Q ⦄.
(* FOLD *)
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.
(* /FOLD *)

(** TERSE: *** *)

(** Here's a first formal proof using this rule. *)

Example assn_sub_example :
  ⦃ (X < 5) [X |-> X + 1]⦄
  X := X + 1
  ⦃ X < 5 ⦄.
Proof.
  (* WORKINCLASS *)
  apply hoare_asgn.  Qed.
(* /WORKINCLASS *)

(** TERSE: *** *)
(** (Of course, what would be even more helpful is to prove this
    simpler triple:

      ⦃ X < 4 ⦄ X := X + 1 ⦃ X < 5⦄

   We will see how to do so in the next section. *)

(* FULL *)

(* EX2M? (hoare_asgn_examples) *)
(* SOONER: There's no reason any more for this to be a manual exercise!! *)
(** Complete these Hoare triples...

    1) ⦃ ??? ⦄
       X ::= 2 * X
       ⦃ X <= 10 ⦄

    2) ⦃ ??? ⦄
       X := 3
       ⦃ 0 <= X /\ X <= 5 ⦄

   ...using the names [assn_sub_ex1] and [assn_sub_ex2], and prove
   both with just [apply hoare_asgn]. If you find that tactic doesn't
   suffice, double check that you have completed the triple properly. *)

(* SOLUTION *)
Example assn_sub_ex1 :
  ⦃ (X <= 10) [X |-> 2 * X] ⦄
  X := 2 * X
  ⦃ X <= 10  ⦄.
Proof.
  apply hoare_asgn. Qed.

Example assn_sub_ex2 :
  ⦃ (0 <= X /\ X <= 5) [X |-> 3] ⦄
  X := 3
  ⦃ 0 <=  X /\ X <= 5  ⦄.
Proof.
  apply hoare_asgn. Qed.
(* /SOLUTION *)

(* GRADE_MANUAL 2: hoare_asgn_examples *)
(** [] *)

(* EX2M! (hoare_asgn_wrong) *)
(** The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems puzzling, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:
[[[
      ------------------------------ (hoare_asgn_wrong)
      ⦃ True ⦄ X := a ⦃ X = a ⦄
]]]
    Give a counterexample showing that this rule is incorrect and
    argue informally that it is really a counterexample.  (Hint:
    The rule universally quantifies over the arithmetic expression
    [a], and your counterexample needs to exhibit an [a] for which
    the rule doesn't work.) *)

(* SOLUTION *)
(* If [a] itself mentions [X], then the value of [a] may be different
   in the final state because of this update. For example, if [a] is
   [X + 1], then setting [X] to [a] certainly does not achieve the
   postcondition [X = X + 1]!  The underlying problem is that the
   state in which the postcondition will be checked is different than
   the state in which [a] was evaluated when it was assigned to [X].

   Here is a formal proof that this rule is wrong (thanks to Nick
   Watson): *)

Theorem hoare_asgn_wrong : exists a:aexp,
  ~ ⦃ True ⦄ X := a ⦃ X = a  ⦄.
Proof.
  exists <{ X + 1 }>. intros Hc.
  unfold hoare_triple in Hc.
  remember (X !-> 1) as st1 eqn:Heqst1.
  assert (st1 X = aeval st1 <{ X + 1 }>) as H2.
  { apply Hc with (st := empty_st).
    - (* assignment *) rewrite -> Heqst1. apply E_Ass. reflexivity.
    - (* True *)  constructor. }
  rewrite -> Heqst1 in H2.  unfold t_update in H2.
  simpl in H2. discriminate.
Qed.
(* /SOLUTION *)

(* GRADE_MANUAL 2: hoare_asgn_wrong *)
(** [] *)

(* SOONER: MRC'20: It sure would be great for the next two exercises
   to use the updated notation.  However, I can't figure out how to
   get the postcondition to work with it.  The problem is that the
   substitution operator is defined on assertions, but I need a
   version of it defined on expressions.  BCP: Maybe possible now? *)

(* EX3A (hoare_asgn_fwd) *)
(** However, by using a _parameter_ [m] (a Coq number) to remember the
    original value of [X] we can define a Hoare rule for assignment
    that does, intuitively, "work forwards" rather than backwards.
[[[
       ------------------------------------------ (hoare_asgn_fwd)
       ⦃ fun st => P st /\ st X = m⦄
         X := a
       ⦃ fun st => P st' /\ st X = aeval st' a ⦄
       (where st' = (X !-> m ; st))
]]]
    Note that we use the original value of [X] to reconstruct the
    state [st'] before the assignment took place. Prove that this rule
    is correct.  (Also note that this rule is more complicated than
    [hoare_asgn].)
*)

Theorem hoare_asgn_fwd :
  forall m a P,
  ⦃ fun st => P st /\ st X = m⦄
    X := a
  ⦃ fun st => P (X !-> m ; st)
           /\ st X = aeval (X !-> m ; st) a  ⦄.
(** [] *)

(* EX2A? (hoare_asgn_fwd_exists) *)
(** Another way to define a forward rule for assignment is to
    existentially quantify over the previous value of the assigned
    variable.  Prove that it is correct.
[[[
      ------------------------------------ (hoare_asgn_fwd_exists)
      ⦃ fun st => P st⦄
        X := a
      ⦃ fun st => exists m, P (X !-> m ; st) /\
                     st X = aeval (X !-> m ; st) a ⦄
]]]
*)
(* INSTRUCTORS: This rule was proposed to BCP by Nick Giannarakis and
   Zoe Paraskevopoulou.
   APT: This is actually Floyd's original rule.  See Mike Gordon,
   "Background reading on Hoare Logic," p.21
   https://www.cl.cam.ac.uk/archive/mjcg/HL/Notes/Notes.pdf *)

Theorem hoare_asgn_fwd_exists :
  forall a P,
  ⦃ fun st => P st⦄
    X := a
  ⦃ fun st => exists m, P (X !-> m ; st) /\
                st X = aeval (X !-> m ; st) a  ⦄.
(** [] *)
(* /FULL *)

(* TERSE *)
(* SOONER: BCP 19: This sequence of quizzes seems confusing /
   confused. The "trivial" ones, as Robert points out, are NOT
   trivial... *)





(* INSTRUCTORS: Again, valid but not an instance of the rule.  This
   leads into the discussion of the rule of consequence. *)
(* /TERSE *)

(* ####################################################### *)
(** ** Consequence *)

(** Sometimes the preconditions and postconditions we get from the
    Hoare rules won't quite be the ones we want in the particular
    situation at hand -- they may be logically equivalent but have a
    different syntactic form that fails to unify with the goal we are
    trying to prove, or they actually may be logically weaker (for
    preconditions) or stronger (for postconditions) than what we need. *)

(** TERSE: *** *)
(** For instance, while

      ⦃ (X = 3) [X |-> 3] ⦄ X := 3 ⦃ X = 3 ⦄,

    follows directly from the assignment rule,

      ⦃ True ⦄ X := 3 ⦃ X = 3⦄

    does not.  This triple is valid, but it is not an instance of
    [hoare_asgn] because [True] and [(X = 3) [X |-> 3]] are not
    syntactically equal assertions.  However, they are logically
    _equivalent_, so if one triple is valid, then the other must
    certainly be as well.  We can capture this observation with the
    following rule:
[[[
                ⦃ P' ⦄ c ⦃ Q⦄
                  P <<->> P'
         -----------------------------   (hoare_consequence_pre_equiv)
                ⦃ P ⦄ c ⦃ Q⦄
]]]
*)

(** TERSE: *** *)

(** Taking this line of thought a bit further, we can see that
    strengthening the precondition or weakening the postcondition of a
    valid triple always produces another valid triple. This
    observation is captured by two _Rules of Consequence_.
[[[
                ⦃ P' ⦄ c ⦃ Q⦄
                   P ->> P'
         -----------------------------   (hoare_consequence_pre)
                ⦃ P ⦄ c ⦃ Q⦄

                ⦃ P ⦄ c ⦃ Q'⦄
                  Q' ->> Q
         -----------------------------    (hoare_consequence_post)
                ⦃ P ⦄ c ⦃ Q⦄
]]]
*)

(** TERSE: *** *)

(** Here are the formal versions: *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  ⦃ P' ⦄ c ⦃ Q ⦄ ->
  P ->> P' ->
  ⦃ P ⦄ c ⦃ Q ⦄.
(* FOLD *)
Proof.
  unfold hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.
(* /FOLD *)

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  ⦃ P ⦄ c ⦃ Q' ⦄ ->
  Q' ->> Q ->
  ⦃ P ⦄ c ⦃ Q ⦄.
(* FOLD *)
Proof.
  unfold hoare_triple, "->>".
  intros P Q Q' c Hhoare Himp st st' Heval Hpre.
  apply Himp.
  apply Hhoare with (st := st).
  - assumption.
  - assumption.
Qed.
(* /FOLD *)

(** TERSE: *** *)

(** For example, we can use the first consequence rule like this:

      ⦃ True ⦄ ->>
      ⦃ (X = 1) [X |-> 1] ⦄
    X := 1
      ⦃ X = 1 ⦄

    Or, formally... *)

Example hoare_asgn_example1 :
  ⦃ True ⦄ X := 1 ⦃ X = 1 ⦄.
Proof.
  (* WORKINCLASS *)
  apply hoare_consequence_pre with (P' := (X = 1) [X |-> 1]).
  - apply hoare_asgn.
  - unfold "->>", assn_sub, t_update.
    intros st _. simpl. reflexivity.
Qed.
(* /WORKINCLASS *)

(** TERSE: *** *)
(** We can also use it to prove the example mentioned earlier.

      ⦃ X < 4 ⦄ ->>
      ⦃ (X < 5)[X |-> X + 1] ⦄
    X := X + 1
      ⦃ X < 5 ⦄

   Or, formally ... *)

Example assn_sub_example2 :
  ⦃ X < 4⦄
  X := X + 1
  ⦃ X < 5 ⦄.
Proof.
  (* WORKINCLASS *)
  apply hoare_consequence_pre with (P' := (X < 5) [X |-> X + 1]).
  - apply hoare_asgn.
  - unfold "->>", assn_sub, t_update.
    intros st H. simpl in *. lia.
Qed.
(* /WORKINCLASS *)

(** TERSE: *** *)
(** Finally, here is a combined rule of consequence that allows us to
    vary both the precondition and the postcondition.

                ⦃ P' ⦄ c ⦃ Q'⦄
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                ⦃ P ⦄ c ⦃ Q⦄

*)

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  ⦃ P' ⦄ c ⦃ Q' ⦄ ->
  P ->> P' ->
  Q' ->> Q ->
  ⦃ P ⦄ c ⦃ Q ⦄.
(* FOLD *)
Proof.
  intros P P' Q Q' c Htriple Hpre Hpost.
  apply hoare_consequence_pre with (P' := P').
  - apply hoare_consequence_post with (Q' := Q').
    + assumption.
    + assumption.
  - assumption.
Qed.
(* /FOLD *)


(* ####################################################### *)
(** ** Automation *)

(** Many of the proofs we have done so far with Hoare triples can be
    streamlined using the automation techniques that we introduced in
    the \CHAPV1{Auto} chapter of _Logical Foundations_.

    Recall that the [auto] tactic can be told to [unfold] definitions
    as part of its proof search.  Let's give that hint for the
    definitions and coercions we're using: *)

Hint Unfold assert_implies hoare_triple assn_sub t_update : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.

(** Also recall that [auto] will search for a proof involving [intros]
    and [apply].  By default, the theorems that it will apply include
    any of the local hypotheses, as well as theorems in a core
    database. *)

(** FULL: The proof of [hoare_consequence_pre], repeated below, looks
    like an opportune place for such automation, because all it does
    is [unfold], [intros], and [apply].  It uses [assumption], too,
    but that's just application of a hypothesis. *)

(** TERSE: *** *)
(** TERSE: Here's a good candidate for automation: *)

Theorem hoare_consequence_pre' : forall (P P' Q : Assertion) c,
  ⦃ P' ⦄ c ⦃ Q ⦄ ->
  P ->> P' ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
  unfold hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.

(* FULL *)
(** Merely using [auto], though, doesn't complete the proof. *)

Theorem hoare_consequence_pre'' : forall (P P' Q : Assertion) c,
  ⦃ P' ⦄ c ⦃ Q ⦄ ->
  P ->> P' ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
  auto. (* no progress *)
Abort.

(** The problem is the [apply Hhoare with...] part of the proof.  Coq
    isn't able to figure out how to instantiate [st] without some help
    from us.  Recall, though, that there are versions of many tactics
    that will use _existential variables_ to make progress even when
    the regular versions of those tactics would get stuck.

    Here, the [eapply] tactic will introduce an existential variable
    [?st] as a placeholder for [st], and [eassumption] will
    instantiate [?st] with [st] when it discovers [st] in assumption
    [Heval].  By using [eapply] we are essentially telling Coq, "Be
    patient: The missing part is going to be filled in later in the
    proof." *)
(* /FULL *)

(** TERSE: *** *)
(** TERSE: Tactic [eapply] will find [st] for us. *)

Theorem hoare_consequence_pre''' : forall (P P' Q : Assertion) c,
  ⦃ P' ⦄ c ⦃ Q ⦄ ->
  P ->> P' ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
  unfold hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  eapply Hhoare.
  - eassumption.
  - apply Himp. assumption.
Qed.

(** TERSE: *** *)
(** Tactic [eauto] will use [eapply] as part of its proof search.
    So, the entire proof can be done in just one line. *)

Theorem hoare_consequence_pre'''' : forall (P P' Q : Assertion) c,
  ⦃ P' ⦄ c ⦃ Q ⦄ ->
  P ->> P' ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
  eauto.
Qed.

(** FULL: Of course, it's hard to predict that [eauto] suffices here
    without having gone through the original proof of
    [hoare_consequence_pre] to see the tactics it used. But now that
    we know [eauto] works, it's a good bet that it will also work for
    [hoare_consequence_post]. *)

(** TERSE: ...as can the same proof for the postcondition consequence
    rule. *)

Theorem hoare_consequence_post' : forall (P Q Q' : Assertion) c,
  ⦃ P ⦄ c ⦃ Q' ⦄ ->
  Q' ->> Q ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
  eauto.
Qed.

(** TERSE: *** *)
(** We can also use [eapply] to streamline a proof,
    [hoare_asgn_example1], that we did earlier as an example of using
    the consequence rule: *)

Example hoare_asgn_example1' :
  ⦃ True ⦄ X := 1 ⦃ X = 1 ⦄.
Proof.
  eapply hoare_consequence_pre. (* no need to state an assertion *)
  - apply hoare_asgn.
  - unfold "->>", assn_sub, t_update.
    intros st _. simpl. reflexivity.
Qed.

(** The final bullet of that proof also looks like a candidate for
    automation. *)

Example hoare_asgn_example1'' :
  ⦃ True ⦄ X := 1 ⦃ X = 1 ⦄.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - auto.
Qed.

(** Now we have quite a nice proof script: it simply identifies the
    Hoare rules that need to be used and leaves the remaining
    low-level details up to Coq to figure out. *)

(** FULL: By now it might be apparent that the _entire_ proof could be
    automated if we added [hoare_consequence_pre] and [hoare_asgn] to
    the hint database.  We won't do that in this chapter, so that we
    can get a better understanding of when and how the Hoare rules are
    used.  In the next chapter, \CHAP{Hoare2}, we'll dive deeper into
    automating entire proofs of Hoare triples. *)

(** TERSE: *** *)
(** The other example of using consequence that we did earlier,
    [hoare_asgn_example2], requires a little more work to automate.
    We can streamline the first line with [eapply], but we can't just use
    [auto] for the final bullet, since it needs [omega]. *)

Example assn_sub_example2' :
  ⦃ X < 4⦄
  X := X + 1
  ⦃ X < 5 ⦄.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - auto. (* no progress *)
    unfold "->>", assn_sub, t_update.
    intros st H. simpl in *. lia.
Qed.

(** Let's introduce our own tactic to handle both that bullet and the
    bullet from example 1: *)

Ltac assn_auto :=
  try auto;  (* as in example 1, above *)
  try (unfold "->>", assn_sub, t_update;
       intros; simpl in *; lia). (* as in example 2 *)

(** TERSE: *** *)
Example assn_sub_example2'' :
  ⦃ X < 4⦄
  X := X + 1
  ⦃ X < 5 ⦄.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assn_auto.
Qed.

Example hoare_asgn_example1''':
  ⦃ True ⦄ X := 1 ⦃ X = 1 ⦄.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assn_auto.
Qed.

(** Again, we have quite a nice proof script.  All the low-level
    details of proof about assertions have been taken care of
    automatically. Of course, [assn_auto] isn't able to prove
    everything we could possibly want to know about assertions --
    there's no magic here! But it's good enough so far. *)

(* FULL *)
(* EX2 (hoare_asgn_examples_2) *)
(** Prove these triples.  Try to make your proof scripts as nicely automated
    as those above. *)

Example assn_sub_ex1' :
  ⦃ X <= 5 ⦄
  X := 2 * X
  ⦃ X <= 10  ⦄.

Example assn_sub_ex2' :
  ⦃ 0 <= 3 /\ 3 <= 5 ⦄
  X := 3
  ⦃ 0 <= X /\ X <= 5  ⦄.

(* GRADE_THEOREM 1: assn_sub_ex1' *)
(* GRADE_THEOREM 1: assn_sub_ex2' *)
(** [] *)

(* LATER: Note here about equivalent preconditions

      ⦃ X + 1 <= 5 ⦄  X := X + 1  ⦃ X <= 5 ⦄

      ⦃ 3 = 3 ⦄  X := 3  ⦃ X = 3 ⦄

      ⦃ 0 <= 3 /\ 3 <= 5 ⦄  X := 3  ⦃ 0 <= X /\ X <= 5 ⦄

*)
(* /FULL *)

(* ####################################################### *)
(** ** Skip *)

(** Since [skip] doesn't change the state, it preserves any
    assertion [P]:

      --------------------  (hoare_skip)
      ⦃ P ⦄ skip ⦃ P ⦄

*)

Theorem hoare_skip : forall P,
     ⦃ P ⦄ skip ⦃ P ⦄.
(* FOLD *)
Proof.
  intros P st st' H HP. inversion H; subst. assumption.
Qed.
(* /FOLD *)

(* ####################################################### *)
(** ** Sequencing *)

(** If command [c1] takes any state where [P] holds to a state where
    [Q] holds, and if [c2] takes any state where [Q] holds to one
    where [R] holds, then doing [c1] followed by [c2] will take any
    state where [P] holds to one where [R] holds:
[[[
        ⦃ P ⦄ c1 ⦃ Q ⦄
        ⦃ Q ⦄ c2 ⦃ R ⦄
       ----------------------  (hoare_seq)
       ⦃ P ⦄ c1;c2 ⦃ R ⦄
]]]
*)

Theorem hoare_seq : forall P Q R c1 c2,
     ⦃ Q ⦄ c2 ⦃ R ⦄ ->
     ⦃ P ⦄ c1 ⦃ Q ⦄ ->
     ⦃ P ⦄ c1; c2 ⦃ R ⦄.
(* FOLD *)
Proof.
  unfold hoare_triple.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  eauto.
Qed.
(* /FOLD *)

(** FULL: Note that, in the formal rule [hoare_seq], the premises are
    given in backwards order ([c2] before [c1]).  This matches the
    natural flow of information in many of the situations where we'll
    use the rule, since the natural way to construct a Hoare-logic
    proof is to begin at the end of the program (with the final
    postcondition) and push postconditions backwards through commands
    until we reach the beginning. *)

(** TERSE: *** *)

(** Here's an example of a program involving sequencing.  Note the use
    of [hoare_seq] in conjunction with [hoare_consequence_pre] and the
    [eapply] tactic. *)

Example hoare_asgn_example3 : forall (a:aexp) (n:nat),
  ⦃ a = n⦄
  X := a; skip
  ⦃ X = n ⦄.
Proof.
  intros a n. eapply hoare_seq.
  - (* right part of seq *)
    apply hoare_skip.
  - (* left part of seq *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto.
Qed.

(** Informally, a nice way of displaying a proof using the sequencing
    rule is as a "decorated program" where the intermediate assertion
    [Q] is written between [c1] and [c2]:

      ⦃ a = n ⦄
    X := a;
      ⦃ X = n ⦄    <--- decoration for Q
    skip
      ⦃ X = n ⦄

*)
(* LATER: We're introducing decorated programs here, and perhaps we
   should make a slightly bigger deal out of them now (even though we
   won't really take up the topic till the next chapter)...  And we
   should talk about how decorations can include sequences of
   decorations separated by implications*)

(* FULL *)
(* EX2! (hoare_asgn_example4) *)
(** Translate this "decorated program" into a formal proof:

                   ⦃ True ⦄ ->>
                   ⦃ 1 = 1 ⦄
    X := 1;
                   ⦃ X = 1 ⦄ ->>
                   ⦃ X = 1 /\ 2 = 2 ⦄
    Y := 2
                   ⦃ X = 1 /\ Y = 2 ⦄

   Note the use of "[->>]" decorations, each marking a use of
   [hoare_consequence_pre].

   We've started you off by providing a use of [hoare_seq] that
   explicitly identifies [X = 1] as the intermediate assertion. *)

Example hoare_asgn_example4 :
  ⦃ True ⦄
  X := 1; Y := 2
  ⦃ X = 1 /\ Y = 2  ⦄.
(** [] *)

(* EX3 (swap_exercise) *)
(** Write an Imp program [c] that swaps the values of [X] and [Y] and
    show that it satisfies the following specification:

      ⦃ X <= Y ⦄ c ⦃ Y <= X⦄

    Your proof should not need to use [unfold hoare_triple].  (Hint:
    Remember that the assignment rule works best when it's applied
    "back to front," from the postcondition to the precondition.  So
    your proof will want to start at the end and work back to the
    beginning of your program.)  *)
(* LATER: One of the OPLSS students noticed that it is quite
   confusing to try to write out the decorated program version of this
   proof. *)
(* HIDE: CH: Here goes:

    ⦃ X <= Y ⦄
  Z := X;
    ⦃ Z <= Y ⦄
  X := Y;
    ⦃ Z <= X ⦄
  Y := Z
    ⦃ Y <= X ⦄

   The _only_ catch is that one needs to do it backwards, since that's
   how the hoare_asgn rule is defined.
   Maybe move this decorated program to the decorated programs
   section, since it's a good warm-up exercise.
*)

Definition swap_program : com

Theorem swap_exercise :
  ⦃ X <= Y⦄
  swap_program
  ⦃ Y <= X ⦄.
(** [] *)

(* EX4 (invalid_triple) *)
(* SOONER: MRC'20: should this be 3 or 4 stars? Also, I couldn't resist
   adding [specialize] here; I really wish we covered it back
   in volume 1, because my students start wanting it rather
   early on. *)
(** Show that

    ⦃ a = n ⦄
      X := 3;; Y := a
    ⦃ Y = n ⦄

    is not a valid Hoare triple for some choices of [a] and [n].

    Conceptual hint:  invent a particular [a] and [n] for which the triple
    in invalid, then use those to complete the proof.

    Technical hint: hypothesis [H], below, begins [forall a n, ...].
    You'll want to instantiate that for the particular [a] and [n]
    you've invented.  You can do that with [assert] and [apply], but
    Coq offers an even easier tactic: [specialize].  If you write

    specialize H with (a := your_a) (n := your_n)

    the hypothesis will be instantiated on [your_a] and [your_n].
 *)
(* SOONER: BCP 20: Yes, showing them [specialize] would be a good
   prelude to revealing that it is really just application. *)

Theorem invalid_triple : ~ forall (a : aexp) (n : nat),
    ⦃ a = n ⦄
      X := 3; Y := a
    ⦃ Y = n  ⦄.
(** [] *)
(* /FULL *)

(* ####################################################### *)
(** ** Conditionals *)

(** What sort of rule do we want for reasoning about conditional
    commands?

    Certainly, if the same assertion [Q] holds after executing
    either of the branches, then it holds after the whole conditional.
    So we might be tempted to write:
[[[
              ⦃ P ⦄ c1 ⦃ Q⦄
              ⦃ P ⦄ c2 ⦃ Q⦄
      ---------------------------------
      ⦃ P ⦄ if b then c1 else c2 ⦃ Q⦄
]]]
*)

(** TERSE: *** *)

(** However, this is rather weak. For example, using this rule,
   we cannot show

     ⦃ True ⦄
     if X = 0
       then Y := 2
       else Y := X + 1
     end
     ⦃ X <= Y ⦄

   since the rule tells us nothing about the state in which the
   assignments take place in the "then" and "else" branches. *)

(** FULL: Fortunately, we can say something more precise.  In the
    "then" branch, we know that the boolean expression [b] evaluates to
    [true], and in the "else" branch, we know it evaluates to [false].
    Making this information available in the premises of the rule gives
    us more information to work with when reasoning about the behavior
    of [c1] and [c2] (i.e., the reasons why they establish the
    postcondition [Q]). *)
(** TERSE: *** *)
(** TERSE: Better: *)
(**
[[[
              ⦃ P /\   b ⦄ c1 ⦃ Q⦄
              ⦃ P /\ ~ b ⦄ c2 ⦃ Q⦄
      ------------------------------------  (hoare_if)
      ⦃ P ⦄ if b then c1 else c2 end ⦃ Q⦄
]]]
*)

(** TERSE: *** *)

(** FULL: To interpret this rule formally, we need to do a little work.
    Strictly speaking, the assertion we've written, [P /\ b], is the
    conjunction of an assertion and a boolean expression -- i.e., it
    doesn't typecheck.  To fix this, we need a way of formally
    "lifting" any bexp [b] to an assertion.  We'll write [bassn b] for
    the assertion "the boolean expression [b] evaluates to [true] (in
    the given state)." *)
(** TERSE: To make this formal, we need a way of formally "lifting"
    any bexp [b] to an assertion.

    We'll write [bassn b] for the assertion "the boolean expression
    [b] evaluates to [true]." *)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).


(** TERSE: *** *)

(** Now we can formalize the Hoare proof rule for conditionals
    and prove it correct. *)

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  ⦃ P /\ b ⦄ c1 ⦃ Q ⦄ ->
  ⦃ P /\ ~ b ⦄ c2 ⦃ Q ⦄ ->
  ⦃ P ⦄ if b then c1 else c2 end ⦃ Q ⦄.
(** That is (unwrapping the notations):

      Theorem hoare_if : forall P Q b c1 c2,
        ⦃ fun st => P st /\ bassn b st ⦄ c1 ⦃ Q ⦄ ->
        ⦃ fun st => P st /\ ~ (bassn b st) ⦄ c2 ⦃ Q ⦄ ->
        ⦃ P ⦄ if b then c1 else c2 end ⦃ Q ⦄.

*)
(* FOLD *)
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst; eauto.
Qed.
(* /FOLD *)

(** *** Example *)

(** FULL: Here is a formal proof that the program we used to motivate the
    rule satisfies the specification we gave. *)

Example if_example :
    ⦃ True⦄
  if (X = 0)
    then Y := 2
    else Y := X + 1
  end
    ⦃ X <= Y ⦄.
(* FULL: FOLD *)
Proof.
  apply hoare_if.
  - (* Then *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto. (* no progress *)
      unfold "->>", assn_sub, t_update, bassn.
      simpl. intros st [_ H].
      apply eqb_eq in H.
      rewrite H. lia.
  - (* Else *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto.
Qed.

(** TERSE: *** *)

(** As we did earlier, it would be nice to eliminate all the low-level
    proof script that isn't about the Hoare rules.  Unfortunately, the
    [assn_auto] tactic we wrote wasn't quite up to the job.  Looking
    at the proof of [if_example], we can see why.  We had to unfold a
    definition ([bassn]) and use a theorem ([eqb_eq]) that we didn't
    need in earlier proofs.  So, let's add those into our tactic,
    and clean it up a little in the process. *)

(* HIDE: MRC'20: There's probably a better way to engineer this.
   I don't know Ltac very well though. *)
Ltac assn_auto' :=
  unfold "->>", assn_sub, t_update, bassn;
  intros; simpl in *;
  try rewrite -> eqb_eq in *; (* for equalities *)
  auto; try lia.

(** TERSE: *** *)

(** Now the proof is quite streamlined. *)

Example if_example'' :
  ⦃ True⦄
  if X = 0
    then Y := 2
    else Y := X + 1
  end
  ⦃ X <= Y ⦄.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto'.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto'.
Qed.

(** We can even shorten it a little bit more. *)

Example if_example''' :
  ⦃ True⦄
  if X = 0
    then Y := 2
    else Y := X + 1
  end
  ⦃ X <= Y ⦄.
Proof.
  apply hoare_if; eapply hoare_consequence_pre;
    try apply hoare_asgn; try assn_auto'.
Qed.

(** For later proofs, it will help to extend [assn_auto'] to handle
    inequalities, too. *)

Ltac assn_auto'' :=
  unfold "->>", assn_sub, t_update, bassn;
  intros; simpl in *;
  try rewrite -> eqb_eq in *;
  try rewrite -> leb_le in *;  (* for inequalities *)
  auto; try lia.

(* FULL *)
(* EX2 (if_minus_plus) *)
(** Prove the theorem below using [hoare_if].  Do not use [unfold
    hoare_triple]. *)

Theorem if_minus_plus :
  ⦃ True⦄
  if (X <= Y)
    then Z := Y - X
    else Y := X + Z
  end
  ⦃ Y = X + Z ⦄.
(* /FULL *)
(** [] *)

(* FULL *)
(* ####################################################### *)
(** *** Exercise: One-sided conditionals *)

(* HIDE: Question from 2012, Midterm 2. One-sided conditionals. *)
(** In this exercise we consider extending Imp with "one-sided
    conditionals" of the form [if1 b then c end]. Here [b] is a boolean
    expression, and [c] is a command. If [b] evaluates to [true], then
    command [c] is evaluated. If [b] evaluates to [false], then [if1 b
    then c end] does nothing.

    We recommend that you complete this exercise before attempting the
    ones that follow, as it should help solidify your understanding of
    the material. *)
(* SOONER: MRC'20: does that mean the exercise should be marked
   as recommended? *)

(** The first step is to extend the syntax of commands and introduce
    the usual notations.  (We've done this for you.  We use a separate
    module to prevent polluting the global name space.) *)

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Notation "'if1' x 'then' y 'end'" :=
         (CIf1 x y)
             (in custom com at level 0, x custom com at level 99).
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

(* EX2 (if1_ceval) *)

(** Add two new evaluation rules to relation [ceval], below, for
    [if1]. Let the rules for [if] guide you.*)

(* INSTRUCTORS: Copy of template eval *)
Reserved Notation "st '=[' c ']=>'' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
(* SOLUTION *)
  | E_If1True : forall (st st' : state) (b : bexp) (c : com),
                beval st b = true ->
                st =[ c ]=> st' ->
                st =[ if1 b then c end ]=> st'
  | E_If1False : forall (st : state) (b : bexp) (c : com),
                 beval st b = false ->
                 st =[ if1 b then c end ]=> st
(* /SOLUTION *)

where "st '=[' c ']=>' st'" := (ceval c st st').

Hint Constructors ceval : core.

(** The following unit tests should be provable simply by [eauto] if
    you have defined the rules for [if1] correctly. *)

Example if1true_test :
  empty_st =[ if1 X = 0 then X := 1 end ]=> (X !-> 1).

Example if1false_test :
  (X !-> 2) =[ if1 X = 0 then X := 1 end ]=> (X !-> 2).

(* GRADE_THEOREM 1: if1true_test *)
(* GRADE_THEOREM 1: if1false_test *)

(** [] *)

(** Now we have to repeat the definition and notation of Hoare triples,
    so that they will use the updated [com] type. *)

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
       st =[ c ]=> st' ->
       P st  ->
       Q st'.

Hint Unfold hoare_triple : core.

Notation "⦃  P ⦄  c  ⦃ Q  ⦄" := (hoare_triple P c Q)
                                  (at level 90, c custom com at level 99)
                                  : hoare_spec_scope.

(* EX2M (hoare_if1) *)

(** Invent a Hoare logic proof rule for [if1].  State and prove a
    theorem named [hoare_if1] that shows the validity of your rule.
    Use [hoare_if] as a guide. Try to invent a rule that is
    _complete_, meaning it can be used to prove the correctness of as
    many one-sided conditionals as possible.  Also try to keep your
    rule _compositional_, meaning that any Imp command that appears
    in a premise should syntactically be a part of the command
    in the conclusion.

    Hint: if you encounter difficulty getting Coq to parse part of
    your rule as an assertion, try manually indicating that it should
    be in the assertion scope.  For example, if you want [e] to be
    parsed as an assertion, write it as [(e)%assertion]. *)

(* SOLUTION *)
Theorem hoare_if1 : forall (b : bexp) (c : com) (P Q : Assertion),
  ⦃ P /\ b ⦄ c ⦃ Q ⦄ ->
  ( P /\ ~ b)%assertion ->> Q ->
  ⦃ P ⦄ (if1 b then c end) ⦃ Q  ⦄.
Proof.
  intros b c P Q Htrue Hfalse st st' Heval Hpre.
  inversion Heval; subst; eauto.
Qed.
(* /SOLUTION *)

(** For full credit, prove formally [hoare_if1_good] that your rule is
    precise enough to show the following valid Hoare triple:

  ⦃ X + Y = Z ⦄
  if1 ~(Y = 0) then
    X := X + Y
  end
  ⦃ X = Z ⦄

*)
(* GRADE_MANUAL 2: hoare_if1 *)
(** [] *)

(** Before the next exercise, we need to restate the Hoare rules of
    consequence (for preconditions) and assignment for the new [com]
    type. *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  ⦃ P' ⦄ c ⦃ Q ⦄ ->
  P ->> P' ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
  eauto.
Qed.

Theorem hoare_asgn : forall Q X a,
  ⦃ Q [X |-> a] ⦄ (X := a) ⦃ Q ⦄.
Proof.
  intros Q X a st st' Heval HQ.
  inversion Heval; subst.
  auto.
Qed.

(* EX2 (hoare_if1_good) *)

(** Prove that your [if1] rule is complete enough for the following
    valid Hoare triple.

    Hint: [assn_auto''] once more will get you most but not all the way
    to a completely automated proof.  You can finish manually, or
    tweak the tactic further. *)

(* QUIETSOLUTION *)
Ltac assn_auto''' :=
  unfold "->>", assn_sub, t_update, bassn;
  intros; simpl in *;
  try rewrite -> negb_true_iff in *;  (* new *)
  try rewrite -> not_false_iff_true in *;  (* new *)
  try rewrite -> eqb_eq in *;
  try rewrite -> leb_le in *;
  auto; try lia.
(* /QUIETSOLUTION *)

Lemma hoare_if1_good :
  ⦃ X + Y = Z ⦄
  if1 ~(Y = 0) then
    X := X + Y
  end
  ⦃ X = Z  ⦄.

(** [] *)

End If1.

(* /FULL *)

(* HIDE *)
(* TERSE *)
(* ####################################################### *)
(* HIDE: SAZ added this recap for Fall 2013 *)
(* INSTRUCTORS: FWIW, I (BCP, 10/17) didn't find it all that useful in
   lecture.
   MRC'20: If anything this just slowed me down at the end of a lecture, trying
   to get to [while] loops.  I'm suggesting we hide it. *)
(** ** Recap *)

(** Idea: create a _domain specific logic_ for reasoning about
    properties of Imp programs.
      - This hides the low-level details of the semantics of the program
      - Leads to a compositional reasoning process

    The basic structure is given by _Hoare triples_ of the form:

           ⦃ P ⦄ c ⦃ Q⦄

      - [P] and [Q] are assertions about the state of the Imp program.
      - "If command [c] is started in a state satisfying assertion [P],
         and if [c] eventually terminates in some final state, then this
         final state will satisfy the assertion [Q]." *)

(** TERSE: *** *)

(** The rules of Hoare Logic (so far):
[[[
             ----------------------------- (hoare_asgn)
             ⦃ Q [X |-> a] ⦄ X := a ⦃ Q⦄

             ----------------  (hoare_skip)
             ⦃ P ⦄ skip ⦃ P⦄

               ⦃ P ⦄ c1 ⦃ Q⦄
               ⦃ Q ⦄ c2 ⦃ R⦄
              ------------------  (hoare_seq)
              ⦃ P ⦄ c1;c2 ⦃ R⦄

              ⦃ P /\   b ⦄ c1 ⦃ Q⦄
              ⦃ P /\ ~ b ⦄ c2 ⦃ Q⦄
      ------------------------------------  (hoare_if)
      ⦃ P ⦄ if b then c1 else c2 end ⦃ Q⦄

                ⦃ P' ⦄ c ⦃ Q'⦄
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                ⦃ P ⦄ c ⦃ Q⦄
]]]
*)
(* /TERSE *)
(* /HIDE *)

(* ####################################################### *)
(** ** While Loops *)

(* HIDE: MRC'20: The previous exposition here implicitly assumed that
   one wanted [P] as both pre- and postcondition for the loop without
   ever explaining why, then in the last sentence said "P is an
   invariant".  That was mystifying.  I've revised to make the core
   idea of an invariant present from the beginning.  I've also revised
   to tease apart the concepts of being an "invariant" of a command vs.
   a "loop invariant". *)

(** FULL: The Hoare rule for [while] loops is based on the idea of an
    _invariant_: an assertion whose truth is guaranteed before and
    after executing a command.  An assertion [P] is an invariant of [c] if

      ⦃ P ⦄ c ⦃ P⦄

    holds.  Note that in the middle of executing [c], the invariant
    might temporarily become false, but by the end of [c], it must be
    restored. *)

(** TERSE: Assertion [P] is an _invariant_ of [c] if

      ⦃ P ⦄ c ⦃ P⦄

    holds. *)

(** FULL:  As a first attempt at a [while] rule, we could try:


             ⦃ P ⦄ c ⦃ P⦄
      ---------------------------
      ⦃ P} while b do c end ⦃ P⦄


    That rule is valid: if [P] is an invariant of [c], as the premise
    requires, then no matter how many times the loop body executes,
    [P] is going to be true when the loop finally finishes.

    But the rule also omits two crucial pieces of information.  First,
    the loop terminates when [b] becomes false.  So we can strengthen
    the postcondition in the conclusion:


              ⦃ P ⦄ c ⦃ P⦄
      ---------------------------------
      ⦃ P} while b do c end ⦃ P /\ ~b⦄


    Second, the loop body will be executed only if [b] is true.  So we
    can also strengthen the precondition in the premise:


            ⦃ P /\ b ⦄ c ⦃ P⦄
      --------------------------------- (hoare_while)
      ⦃ P} while b do c end ⦃ P /\ ~b⦄

 *)

(** TERSE: *** *)
(** TERSE: The Hoare while rule combines the idea of an invariant with
     information about when guard [b] does or does not hold.


            ⦃ P /\ b ⦄ c ⦃ P⦄
      --------------------------------- (hoare_while)
      ⦃ P} while b do c end ⦃ P /\ ~b⦄


*)

(** FULL: That is the Hoare [while] rule.  Note how it combines
    aspects of [skip] and conditionals:

    - If the loop body executes zero times, the rule is like [skip] in
      that the precondition survives to become (part of) the
      postcondition.

    - Like a conditional, we can assume guard [b] holds on entry to
      the subcommand.
*)

(* SOONER: The big comment will not display nicely.  But I guess it's
   folded... *)
Theorem hoare_while : forall P (b:bexp) c,
  ⦃ P /\ b ⦄ c ⦃ P ⦄ ->
  ⦃ P ⦄ while b do c end ⦃ P /\ ~ b ⦄.
(* FOLD *)
Proof.
  intros P b c Hhoare st st' Heval HP.
  (* We proceed by induction on [Heval], because, in the "keep looping" case,
     its hypotheses talk about the whole loop instead of just [c]. The
     [remember] is used to keep the original command in the hypotheses;
     otherwise, it would be lost in the [induction]. By using [inversion]
     we clear away all the cases except those involving [while]. *)
  remember <{while b do c end}> as original_command eqn:Horig.
  induction Heval;
    try (inversion Horig; subst; clear Horig);
    eauto.
Qed.
(* /FOLD *)

(** TERSE: *** *)

(** We say that [P] is a _loop invariant_ of [while b do c end] if [P]
    suffices to prove [hoare_while] for that loop.  Being a loop
    invariant is different from being an invariant of the body,
    because it means being able to prove correctness of the loop.  For
    example, [X = 0] is a loop invariant of

      while X = 2 do X := 1 end

    even though [X = 0] is not an invariant of [X := 1]. *)

(** TERSE: *** *)

(** This is a slightly (but crucially) weaker requirement.  For
    example, if [P] is the assertion [X = 0], then [P] _is_ an
    invariant of the loop

      while X = 2 do X := 1 end

    although it is clearly _not_ preserved by the body of the
    loop. *)

(* HIDE *)
(** For now, you have to accept on faith that this rule is
    "powerful enough". It is known that the proof rules we develop
    here for Hoare logic are _complete_, in that any valid Hoare
    triple can be proved simply by application of these theorems
    and an oracle for the underlying logic. In particular, given
    any while loop, and a valid Hoare triple for it, you can
    conjure a loop invariant [P] that leads you to the proof.

    We are not in a position here to prove this more formally,
    mostly because we have no notion of completeness for a bunch
    of theorems. The exercises below to prove Hoare triples for
    while programs should make you comfortable with identifying
    invariants. *)

(** Mukund: Possible motivation for [hoare_while]? *)

(** CH: Maybe the [while] could indeed be explained better, but ...
    The examples you propose here are one order or magnitude more
    complex than any of the examples considered in this whole file,
    and they use language features that are beyond the scope of this
    course (arrays). Also, you don't explain at all how to come up
    with loop invariants, you just take extremely complicated
    invariants out of the hat. Finally, this whole discussion about
    loop invariants better belongs to the decorated programs section
    where loop invariants are first used. *)

(** Let's look at the pseudo-code for two common procedures in
    introductory algorithms courses: insertion sort, and Euclid's GCD
    finding algorithm.

    Given: An array of n integers a[1...n].
    To calculate: Return an array A[1...n], containing the elements
      of a in sorted order.
    Do:
      Copy array a into A.
      Initialize i := 0.
      While i < n,
        Let j := i.
        While j > 0,
          Compare A[j] and A[j + 1].
          Swap if A[j] > A[j + 1].
        end
      end.

    Consider the following claim made of insertion sort. Always, just
    before the condition [i < n] is evaluated in the outer while loop,
    the following conditions hold:

    1. The elements A[1...i] are in sorted order.
    2. A[1...i] are a permutation of the elements a[1...i].
    3. The elements A[(i + 1)...n] are each equal to the elements of
       a[(i + 1)...n].
    4. i <= n.

    Observe that these conditions hold the first time the loop condition
    is evaluated. Also, if they hold before the loop body is evaluated,
    then they should hold afterwards. Thus, the conditions form a
    _loop invariant_.

    But why are they helpful? We now know that they hold after any finite
    number of iterations of the loop. In particular, they hold when
    (and if) the loop terminates. What happens then? Since the loop has
    terminated, we know that [i ~< n], and so [i = n]. Substituting n
    for i, we get that A[1...n] are a permutation of a[1...n], and in
    sorted order. And thus, (if insertion sort terminates), it is correct.

    Given: Two positive integers, a and b.
    To find: gcd(a, b)
    Do:
      Let A := a, B := b.
      If A = 0, return B.
      While B ~= 0,
        If A > B,
          A := A - B
        else
          B := B - A
        fi
      end
      Return A.

    We make the claim, just before the evaluation of the loop condition,
    the following condition always holds: "gcd(A, B) = gcd(a, b)".

    It is true at the beginning, and if they hold before executing the
    loop body, then they hold afterwards as well.

    This invariant allows us to prove the correctness of the algorithm:
    when the loop terminates, we know that gcd(A, B) = gcd(a, b), and that
    B = 0. But for all x, gcd(x, 0) = x, and so gcd(A, B) = gcd(A, 0) = A.
    Thus, A = gcd(a, b).

    In both cases, we did not answer the question: "Does this procedure
    always terminate?" But partial correctness is also a feature of Hoare
    logic -- we assume [st =[ c ]=> st'] before checking whether [st']
    satisfies the postcondition.

    The purpose of these two (extremely) informal proofs was to
    convince you that loop invariants are a common design pattern while
    proving the correctness of programs.

    We try to abstract this pattern into a Hoare rule.

    1. The loop invariant is itself an assertion [P]. Since it must
       hold at the beginning, [P] must be the precondition of the
       Hoare triple.
    2. The invariant is preserved by the loop body, but at termination,
       we know something more: recall how we finished the
       gcd-correctness proof -- "when the loop terminates, ..., and
       that B = 0. ..." Thus, the post-condition is [P /\ ~ b], where
       [b] is the loop condition.
    3. What do we demand of the loop body [c]? [⦃  P ⦄ c ⦃ P  ⦄]
       might be a good first guess, since we want [P] to be an
       invariant. But remember that we asserted [P] before evaluating
       the loop condition, and so we know that [b] must have
       evaluated to true. Thus, we want the loop body to satisfy
       the Hoare triple: [⦃  P /\ b ⦄ c ⦃ P  ⦄].

    Putting these together, we get the Hoare proof rule for while:

[[[
               ⦃ P /\ b ⦄ c ⦃ P⦄
        ----------------------------------  (hoare_while)
        ⦃ P ⦄ while b do c end ⦃ P /\ ~ b⦄
]]] *)

(* /HIDE *)

Example while_example :
    ⦃ X <= 3⦄
  while (X <= 2) do
    X := X + 1
  end
    ⦃ X = 3 ⦄.
(* FOLD *)
Proof.
  eapply hoare_consequence_post.
  - apply hoare_while.
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto''.
  - assn_auto''.
Qed.
(* /FOLD *)

(* SOONER: CJC: Maybe also a good place to talk about the structure of
   our logic - that we've set up the hoare_* lemmas and they are all
   the reasoning about Hoare triples that they should have to use (in
   both formal or informal proofs)?  Probably should talk about this
   somewhere or else we'll get back lots of proofs that unfold
   hoare_triple and reason at a low level everywhere. *)

(* HIDE *)
(* LATER: Next year, these should be moved up to the section on
   valid Hoare triples and proved directly there (using, in the
   second case, the fact that this loop does not terminate),
   rather than using the while rule. *)
(* LATER: Point out the trick using intros to do the splitting. *)
Theorem never_loop_hoare: forall P c,
  ⦃ P ⦄ while false do c end ⦃ P ⦄.
Proof.
  intros P c.
  eapply hoare_consequence_post. apply hoare_while.
  - (* loop body preserves invariant *)
    apply hoare_pre_false.
    intros st [HP HFalse]. inversion HFalse.
  - (* invariant and negation of guard imply postcondition *)
    simpl. intros st [Hinv Hguard]. assumption.
Qed.
(* /HIDE *)

(** TERSE: *** *)

(** If the loop never terminates, any postcondition will work. *)

(* INSTRUCTORS: This is good to work in class, but make sure you try
   it yourself beforehand!  Getting it to work smoothly depends on
   doing the right things at the beginning.
   MRC'20: Maybe I'm an outlier, but a WORKINCLASS that surprises me
   and maybe gets me stuck is not ideal. The truly interesting thing
   about this example is that it's provable --not the actual proof.
   I propose that it not be worked in class, but that the proof
   be provided.
   BCP 20: OK *)
(* LATER: MRC'20: It would be nice to automate the second bullet. *)
Theorem always_loop_hoare : forall Q,
  ⦃ True ⦄ while true do skip end ⦃ Q ⦄.
(* FULL: FOLD *)
Proof.
  intros Q.
  eapply hoare_consequence_post.
  - apply hoare_while. apply hoare_post_true. auto.
  - simpl. intros st [Hinv Hguard]. congruence.
Qed.
(* FULL: /FOLD *)

(* HIDE *)
(* A different way through the proof... *)
Theorem always_loop_hoare' : forall P Q,
  ⦃ P ⦄ while true do skip end ⦃ Q ⦄.
  intros P Q.
  apply hoare_consequence_pre with (P' := (True:Assertion)).
  eapply hoare_consequence_post.
  apply hoare_while.
  - (* Loop body preserves invariant *)
    apply hoare_post_true. intros st. apply I.
  - (* Loop invariant and negated guard imply postcondition *)
    simpl. intros st [Hinv Hguard].
    exfalso. apply Hguard. reflexivity.
  - (* Precondition implies invariant *)
    intros st H. constructor.  Qed.

(* And, of course, there is also the low-level way to do it, without using
   Hoare logic... *)
Theorem always_loop_hoare'' : forall P Q,
  ⦃ P ⦄ while true do skip end ⦃ Q ⦄.
Proof.
  intros. unfold hoare_triple.
  intros. remember <{ while true do skip end}> as c.
  induction H; inversion Heqc; subst.
  - inversion H.
  - apply IHceval2. reflexivity. inversion H1. subst. assumption.
Qed.
(* ... But this really misses the point! *)
(* /HIDE *)

(** FULL: Of course, this result is not surprising if we remember that
    the definition of [hoare_triple] asserts that the postcondition
    must hold _only_ when the command terminates.  If the command
    doesn't terminate, we can prove anything we like about the
    post-condition.

    Hoare rules that specify what happens _if_ commands terminate,
    without proving that they do, are said to describe a logic of
    _partial_ correctness.  It is also possible to give Hoare rules
    for _total_ correctness, which additionally specifies that
    commands must terminate. Total correctness is out of the scope of
    this textbook. *)

(* FULL *)
(* ####################################################### *)
(** *** Exercise: [REPEAT] *)
(* HIDE: I (BCP) think I see a much simpler way to do the 'for' stuff.
   Instead of [for x from a to b do c] define [for x downfrom a do c]
   that steps from a down to 0.  This will be much simpler to specify,
   though still an interesting challenge. (CJC: This still seemed hard
   to me, but I'm deleting it for now to get things looking right)
*)
(* HIDE: Coming up with the precise rule for REPEAT is tricky, and so
   is proving formally that the precise rule passes the litmus
   test (at this point we only ask them to convince themselves
   informally there).
*)
(* LATER: PLW: Chapters Imp and Equiv have exercises based on extending
   Imp with C-style FOR loops. Either this chapter should use C-style
   for loops in place of repeat, or those chapters should use repeat
   in place of C-style for loops. *)

(* EX4AM (hoare_repeat) *)
(** In this exercise, we'll add a new command to our language of
    commands: [REPEAT] c [until] b [end]. You will write the
    evaluation rule for [REPEAT] and add a new Hoare rule to the
    language for programs involving it.  (You may recall that the
    evaluation rule is given in an example in the \CHAPV1{Auto} chapter.
    Try to figure it out yourself here rather than peeking.) *)

Module RepeatExercise.

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

(** [REPEAT] behaves like [while], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once. *)

Notation "'repeat' e1 'until' b2 'end'" :=
          (CRepeat e1 b2)
              (in custom com at level 0,
               e1 custom com at level 99, b2 custom com at level 99).
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

(** Add new rules for [REPEAT] to [ceval] below.  You can use the rules
    for [while] as a guide, but remember that the body of a [REPEAT]
    should always execute at least once, and that the loop ends when
    the guard becomes true. *)

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
(* SOLUTION *)
  | E_RepeatEnd : forall st st' b c,
      ceval st c st' ->
      beval st' b = true ->
      st =[ repeat c until b end ]=> st'
  | E_RepeatLoop : forall st st' st'' b c,
      ceval st c st' ->
      beval st' b = false ->
      st' =[ repeat c until b end ]=> st'' ->
      st =[ repeat c until b end ]=> st''
(* /SOLUTION *)

where "st '=[' c ']=>' st'" := (ceval st c st').

(** A couple of definitions from above, copied here so they use the
    new [ceval]. *)

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion)
                        : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Notation "⦃  P ⦄  c  ⦃ Q  ⦄" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99).

(** To make sure you've got the evaluation rules for [repeat] right,
    prove that [ex1_repeat] evaluates correctly. *)

Definition ex1_repeat :=
  <{ repeat
       X := 1;
       Y := Y + 1
     until (X = 1) end }>.

Theorem ex1_repeat_works :
  empty_st =[ ex1_repeat ]=> (Y !-> 1 ; X !-> 1).
Proof.

(** Now state and prove a theorem, [hoare_repeat], that expresses an
    appropriate proof rule for [repeat] commands.  Use [hoare_while]
    as a model, and try to make your rule as precise as possible. *)

(* SOLUTION *)

(** Here is a very precise version of [hoare_repeat]. *)
(* LATER: A student in 2013 pointed out that this rule is OK as far
   as it goes, but it isn't going to lead to a nice rule for decorated
   programs, when we get to that, because it uses c twice, perhaps in
   different ways! *)

Theorem hoare_repeat : forall P Q (b:bexp) c,
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  ⦃ Q /\ ~ b ⦄ c ⦃ Q ⦄ ->
  ⦃ P ⦄ repeat c until b end ⦃ Q /\ b  ⦄.
Proof.
  intros.
  remember <{ repeat c until b end }> as cr. unfold hoare_triple.
  intros. generalize dependent P.
  induction H1; inversion Heqcr; subst; intros.

  - (* E_RepeatEnd *)
    split; [ apply H2 with (st := st) |]; assumption.

  - (* E_RepeatLoop *)
    apply IHceval2 with (P := (Q /\ ~ b)%assertion);
    [ reflexivity | assumption |].
    split.
    unfold hoare_triple in H1; apply H1 with (st := st); assumption.
    unfold bassn. unfold not. intros.
    destruct (beval st' b); [ inversion H | inversion H3 ].
Qed.
(* /SOLUTION *)

(** For full credit, make sure (informally) that your rule can be used
    to prove the following valid Hoare triple:

  ⦃ X > 0 ⦄
  repeat
    Y := X;
    X := X - 1
  until X = 0 end
  ⦃ X = 0 /\ Y > 0 ⦄

*)
(* QUIETSOLUTION *)

(** Although it was not required by the exercise, we can show formally
    that [hoare_repeat] can handle this litmus test: *)

Definition ex2_repeat :=
  <{ repeat
       Y := X;
       X := X - 1
     until (X = 0) end }>.

(** Before we can show anything about this program we need to repeat
    the proofs of some more Hoare rules from above (remember we're in
    a separate module, with a different definition of commands). *)

Theorem hoare_asgn : forall Q X a,
  ⦃ Q [X |-> a] ⦄ X := a ⦃ Q ⦄.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  ⦃ P' ⦄ c ⦃ Q' ⦄ ->
  P ->> P' ->
  Q' ->> Q ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  intros st st' Hc HP.
  apply HQ'Q. apply (Hht st st'). assumption.
  apply HPP'. assumption. Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  ⦃ P' ⦄ c ⦃ Q ⦄ ->
  P ->> P' ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption. Qed.

Theorem hoare_seq : forall P Q R c1 c2,
  ⦃ Q ⦄ c2 ⦃ R ⦄ ->
  ⦃ P ⦄ c1 ⦃ Q ⦄ ->
  ⦃ P ⦄ c1;c2 ⦃ R ⦄.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

(** Now we are ready to show [ex2_repeat] correct using [hoare_repeat]. *)
(* NOTATION : IY -- I've noticed this oddity in previous lemmas, but it's especially
            noticable here that an explicit state is given to the conditional statements.
 *)
Lemma ex2_repeat_hoare_repeat :
  ⦃ X > 0 ⦄
  ex2_repeat
  ⦃ X = 0 /\ Y > 0  ⦄.
Proof.
  unfold ex2_repeat.
  eapply hoare_consequence.
  apply hoare_repeat with (Q := (Y > 0)%assertion).
  eapply hoare_seq; apply hoare_asgn.
  eapply hoare_seq. apply hoare_asgn.
  eapply hoare_consequence_pre. apply hoare_asgn.
  - (* body of repeat if looping *)
    unfold assert_implies. intros.
    unfold assn_sub. simpl.
    rewrite t_update_neq; [| (intro X; inversion X)]. rewrite t_update_eq.
    destruct H as [H1 H2]. unfold bassn in H2.
    rewrite not_true_iff_false in H2. simpl in H2.
    apply eqb_neq in H2. lia.
  - (* body of repeat if exiting right away *)
    unfold assert_implies. intros st H. unfold assn_sub. simpl.
    rewrite t_update_neq; [| (intro X; inversion X)].
    rewrite t_update_eq. assumption.
  - (* final postcondition *)
    unfold assert_implies. intros. unfold bassn in H. simpl in H.
    destruct H as [H1 H2]. apply eqb_eq in H2.
    split; assumption.
Qed.

(** A sound but less precise variant of the [hoare_repeat] rule looks
    like this: *)

(* NOTATION: Here, too, the printing isn't as we write the notation. (As soon as we start
  the proof context). Is this intended? *)
Lemma hoare_repeat' : forall P b c,
  ⦃ P ⦄ c ⦃ P ⦄ ->
  ⦃ P ⦄ repeat c until b end ⦃ P /\ b  ⦄.
Proof.
  unfold hoare_triple.
  intros P b c H st st' He HP.
  remember <{ repeat c until b end }> as rcom.
  induction He; try (inversion Heqrcom); subst.
  - (* E_RepeatEnd *)
    split. apply H with st; assumption. assumption.
  - (* E_RepeatLoop *)
    assert (P st'' /\ bassn b st'') as C2.
    { (* Proof of assertion *) apply IHHe2. reflexivity.
      apply H with st. assumption. assumption. }
    inversion C2.
    split. assumption. assumption. Qed.

(** First, let's show that [hoare_repeat'] is implied by [hoare_repeat]. *)

Lemma hoare_repeat_implies_hoare_repeat' :
  (forall P Q (b:bexp) c,
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  ⦃ Q /\ ~ b ⦄ c ⦃ Q ⦄ ->
  ⦃ P ⦄ repeat c until b end ⦃ Q /\ b  ⦄)
  ->
  (forall P b c,
  ⦃ P ⦄ c ⦃ P ⦄ ->
  ⦃ P ⦄ repeat c until b end ⦃ P /\  b ⦄).
Proof.
  intro hoare_repeat. intros. apply hoare_repeat. assumption.
  eapply hoare_consequence_pre. eassumption.
  unfold assert_implies. intros. destruct H0. assumption.
Qed.

(* However, we can't prove [ex2_repeat] correct using [hoare_repeat'],
   even with a stronger initial precondition on [Y]. Here is a first
   failed proof attempt. *)

Lemma ex2_repeat_hoare_repeat'_fails1 :
  ⦃ X > 0 /\  Y > 0⦄
  ex2_repeat
  ⦃ X = 0 /\  Y > 0 ⦄.
Proof.
  eapply hoare_consequence.
  apply hoare_repeat' with (P := (Y > 0)%assertion).
  eapply hoare_seq. apply hoare_asgn.
  eapply hoare_consequence_pre. apply hoare_asgn.
  - (* body of repeat if looping *)
    unfold assert_implies. intros.
    unfold assn_sub. simpl.
    rewrite t_update_neq; [| (intro X; inversion X)]. rewrite t_update_eq.
    admit. (* loop invariant too weak on its own,
              we need the value of the previous guard *)
  - (* initial precondition *)
    unfold assert_implies. intros. destruct H. assumption.
    (* this only works with an additional Y > 0 precondition *)
  - (* final postcondition *)
    unfold assert_implies. intros. unfold bassn in H. simpl in H.
    destruct H as [H1 H2]. apply eqb_eq in H2.
    split; assumption.
Abort.

(* Here is a second failed attempt trying stronger invariant, but
   it is too strong to be an invariant. *)

Lemma ex2_repeat_hoare_repeat'_fails2 :
  ⦃ X > 0 /\ Y > 0⦄
  ex2_repeat
  ⦃ X = 0 /\ Y > 0 ⦄.
Proof.
  eapply hoare_consequence.
  apply hoare_repeat' with (P := (X > 0 /\ Y > 0)%assertion).
  eapply hoare_seq. apply hoare_asgn.
  eapply hoare_consequence_pre. apply hoare_asgn.
  - (* body of repeat if looping *)
    simpl. unfold assert_implies. intros.
    unfold assn_sub.
    repeat rewrite t_update_eq.
    rewrite t_update_neq; [| (intro X; inversion X)].
    rewrite t_update_eq. simpl.
    rewrite t_update_neq; [| (intro X; inversion X)].
    admit. (* loop invariant too strong *)
  - (* initial precondition *)
    unfold assert_implies. intros. assumption.
  - (* final postcondition *)
    unfold assert_implies. intros. unfold bassn in H. simpl in H.
    destruct H as [ [H1 H2] H3]. apply eqb_eq in H3.
    split; assumption.
Abort.

(* /QUIETSOLUTION *)
End RepeatExercise.

(* GRADE_MANUAL 6: hoare_repeat *)
(** [] *)
(* /FULL *)

(* ####################################################### *)
(** * Summary *)

(* LATER: Full version could use some more text.  Maybe this is a good
   place to say that we're not going to unfold the definition of Hoare
   triples any more in what follows.... *)

(** FULL: So far, we've introduced Hoare Logic as a tool for reasoning about
    Imp programs. *)
(** The rules of Hoare Logic are:
[[[
             --------------------------- (hoare_asgn)
             ⦃ Q [X |-> a] ⦄ X:=a ⦃ Q⦄

             --------------------  (hoare_skip)
             ⦃ P ⦄ skip ⦃ P ⦄

               ⦃ P ⦄ c1 ⦃ Q ⦄
               ⦃ Q ⦄ c2 ⦃ R ⦄
              ----------------------  (hoare_seq)
              ⦃ P ⦄ c1;c2 ⦃ R ⦄

              ⦃ P /\   b ⦄ c1 ⦃ Q⦄
              ⦃ P /\ ~ b ⦄ c2 ⦃ Q⦄
      ------------------------------------  (hoare_if)
      ⦃ P ⦄ if b then c1 else c2 end ⦃ Q⦄

               ⦃ P /\ b ⦄ c ⦃ P⦄
        -----------------------------------  (hoare_while)
        ⦃ P ⦄ while b do c end ⦃ P /\ ~ b⦄

                ⦃ P' ⦄ c ⦃ Q'⦄
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                ⦃ P ⦄ c ⦃ Q⦄
]]]
    In the next chapter, we'll see how these rules are used to prove
    that programs satisfy specifications of their behavior. *)

(* FULL *)
(* ####################################################### *)
(** * Additional Exercises *)

(* LATER: Possible exercise: Show that TRUE and FALSE are loop invariants
   of every while loop.  Explain why this is not useful. *)
(* LATER: Another interesting problem that we could try to work out in detail:
   total-correctness Hoare Logic.  The crucial rule would be something like this:

                 T not in vars(c)
         [P /\ b /\ a = T] c [P /\ a < T]
         --------------------------------
          [P] while b do c end [P /\ ~ b]

   We could define TC-triples, ask them to prove this rule, and then in
   Hoare2.v, as them to carry out some proofs as decorated programs.
   (Asking them to prove this rule might be a bit much, though -- probably
   requires some fanciness with Coq...) *)

(** ** Havoc *)

(** In this exercise, we will derive proof rules for a [HAVOC]
    command, which is similar to the nondeterministic [any] expression
    from the the \CHAP{Imp} chapter.

    First, we enclose this work in a separate module, and recall the
    syntax and big-step semantics of Himp commands. *)

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.

Notation "'havoc' l" := (CHavoc l)
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

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
  | E_Havoc : forall st X n,
      st =[ havoc X ]=> (X !-> n ; st)

where "st '=[' c ']=>' st'" := (ceval c st st').

Hint Constructors ceval : core.

(** The definition of Hoare triples is exactly as before. *)
(* LATER: This used to say: "Unlike our notion of program equivalence,
    which had some subtle consequences with possibly nonterminating
    commands (exercise [havoc_diverge]), this definition is still
    fully satisfactory. Convince yourself of this before proceeding."
    This exercise doesn't seem to have the same name anymore, and I'm
    not sure what was meant by the comment in any case, so I'm
    deleting it. BCP 2016 *)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Hint Unfold hoare_triple : core.

Notation "⦃  P ⦄  c  ⦃ Q  ⦄" := (hoare_triple P c Q)
                                  (at level 90, c custom com at level 99)
                                  : hoare_spec_scope.

(** And the precondition consequence rule is exactly as before. *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  ⦃ P' ⦄ c ⦃ Q ⦄ ->
  P ->> P' ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof. eauto. Qed.

(* EX3 (hoare_havoc) *)

(** Complete the Hoare rule for [HAVOC] commands below by defining
    [havoc_pre], and prove that the resulting rule is correct. *)

Definition havoc_pre (X : string) (Q : Assertion) (st : total_map nat) : Prop

Theorem hoare_havoc : forall (Q : Assertion) (X : string),
  ⦃ havoc_pre X Q ⦄ havoc X ⦃ Q  ⦄.

(** [] *)

(* EX3 (havoc_post) *)

(** Complete the following proof without changing any of the provided
    commands. If you find that it can't be completed, your definition of
    [havoc_pre] is probably too strong. Find a way to relax it so that
    [havoc_post] can be proved.

    Hint: the [assn_auto] tactics we've built won't help you here.
    You need to proceed manually. *)
(* INSTRUCTORS: for example, ⦃ false ⦄ HAVOC X ⦃ P ⦄ would
   be a sound but incomplete rule in which the precondition is
   too strong. *)
(* LATER: MRC'20: sure would be nice to automate this better. *)
(* INSTRUCTORS: can't unfold [havoc_pre] outside the ADMITTED block,
   because its definition is admitted. *)

Theorem havoc_post : forall (P : Assertion) (X : string),
  ⦃ P ⦄ havoc X ⦃ fun st => exists (n:nat), P [X |-> n] st  ⦄.

(** [] *)

End Himp.

(** ** Assert and Assume *)

(* EX4? (assert_vs_assume) *)

Module HoareAssertAssume.

(** In this exercise, we will extend IMP with two commands,
     [assert] and [ASSUME]. Both commands are ways
     to indicate that a certain statement should hold any time this part
     of the program is reached. However they differ as follows:

    - If an [assert] statement fails, it causes the program to go into
      an error state and exit.

    - If an [ASSUME] statement fails, the program fails to evaluate
      at all. In other words, the program gets stuck and has no
      final state.

    The new set of commands is: *)

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CAssert : bexp -> com
  | CAssume : bexp -> com.

(* NOTATION: LATER: Reconsider these precedences *)
Notation "'assert' l" := (CAssert l)
                           (in custom com at level 8, l custom com at level 0).
Notation "'assume' l" := (CAssume l)
                          (in custom com at level 8, l custom com at level 0).
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

(** To define the behavior of [assert] and [ASSUME], we need to add
    notation for an error, which indicates that an assertion has
    failed. We modify the [ceval] relation, therefore, so that
    it relates a start state to either an end state or to [error].
    The [result] type indicates the end value of a program,
    either a state or an error: *)

Inductive result : Type :=
  | RNormal : state -> result
  | RError : result.

(** Now we are ready to give you the ceval relation for the new language. *)

Inductive ceval : com -> state -> result -> Prop :=
  (* Old rules, several modified *)
  | E_Skip : forall st,
      st =[ skip ]=> RNormal st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> RNormal (x !-> n ; st)
  | E_SeqNormal : forall c1 c2 st st' r,
      st  =[ c1 ]=> RNormal st' ->
      st' =[ c2 ]=> r ->
      st  =[ c1 ; c2 ]=> r
  | E_SeqError : forall c1 c2 st,
      st =[ c1 ]=> RError ->
      st =[ c1 ; c2 ]=> RError
  | E_IfTrue : forall st r b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_IfFalse : forall st r b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> RNormal st
  | E_WhileTrueNormal : forall st st' r b c,
      beval st b = true ->
      st  =[ c ]=> RNormal st' ->
      st' =[ while b do c end ]=> r ->
      st  =[ while b do c end ]=> r
  | E_WhileTrueError : forall st b c,
      beval st b = true ->
      st =[ c ]=> RError ->
      st =[ while b do c end ]=> RError
  (* Rules for Assert and Assume *)
  | E_AssertTrue : forall st b,
      beval st b = true ->
      st =[ assert b ]=> RNormal st
  | E_AssertFalse : forall st b,
      beval st b = false ->
      st =[ assert b ]=> RError
  | E_Assume : forall st b,
      beval st b = true ->
      st =[ assume b ]=> RNormal st

where "st '=[' c ']=>' r" := (ceval c st r).

(** We redefine hoare triples: Now, [⦃ P ⦄ c ⦃ Q ⦄] means that,
    whenever [c] is started in a state satisfying [P], and terminates
    with result [r], then [r] is not an error and the state of [r]
    satisfies [Q]. *)

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st r,
     st =[ c ]=> r  -> P st  ->
     (exists st', r = RNormal st' /\ Q st').
(* LATER: I think the way I stated hoare triples may need cleaning
   up.  It doesn't work very well for the proofs of hoare rules to
   have [exists st'] in the conclusion.  BCP 10/18: Not sure what sort
   of cleaning up would be useful... *)

Notation "⦃  P ⦄  c  ⦃ Q  ⦄" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.

(** To test your understanding of this modification, give an example
    precondition and postcondition that are satisfied by the [ASSUME]
    statement but not by the [assert] statement.  Then prove that any
    triple for [assert] also works for [ASSUME]. *)

Theorem assert_assume_differ : exists (P:Assertion) b (Q:Assertion),
       (⦃ P ⦄ assume b ⦃ Q ⦄)
  /\ ~ (⦃ P ⦄ assert b ⦃ Q ⦄).

Theorem assert_implies_assume : forall P b Q,
     (⦃ P ⦄ assert b ⦃ Q ⦄)
  -> (⦃ P ⦄ assume b ⦃ Q ⦄).

(** Your task is now to state Hoare rules for [assert] and [assume],
    and use them to prove a simple program correct.  Name your hoare
    rule theorems [hoare_assert] and [hoare_assume].

    For your benefit, we provide proofs for the old hoare rules
    adapted to the new semantics. *)

Theorem hoare_asgn : forall Q X a,
  ⦃ Q [X |-> a] ⦄ X := a ⦃ Q ⦄.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  exists (X !-> aeval st a ; st). split; try reflexivity.
  assumption. Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  ⦃ P' ⦄ c ⦃ Q ⦄ ->
  P ->> P' ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption. Qed.

(* LATER: These proofs are a bit messy. Can it be made shorter? *)
Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  ⦃ P ⦄ c ⦃ Q' ⦄ ->
  Q' ->> Q ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st r Hc HP.
  unfold hoare_triple in Hhoare.
  assert (exists st', r = RNormal st' /\ Q' st').
  { apply (Hhoare st); assumption. }
  destruct H as [st' [Hr HQ'] ].
  exists st'. split; try assumption.
  apply Himp. assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
  ⦃ Q ⦄ c2 ⦃ R ⦄ ->
  ⦃ P ⦄ c1 ⦃ Q ⦄ ->
  ⦃ P ⦄ c1;c2 ⦃ R ⦄.
Proof.
  intros P Q R c1 c2 H1 H2 st r H12 Pre.
  inversion H12; subst.
  - eapply H1.
    + apply H6.
    + apply H2 in H3. apply H3 in Pre.
        destruct Pre as [st'0 [Heq HQ] ].
        inversion Heq; subst. assumption.
  - (* Find contradictory assumption *)
     apply H2 in H5. apply H5 in Pre.
     destruct Pre as [st' [C _] ].
     inversion C.
Qed.

(** State and prove your hoare rules, [hoare_assert] and
    [hoare_assume], below. *)

(* SOLUTION *)
Theorem hoare_assert : forall Q (b:bexp),
  ⦃ Q /\ b ⦄ assert b ⦃ Q ⦄.
Proof.
intros Q b st r HEval [Hst Hb].
exists st. inversion HEval; subst.
- split; auto.
- rewrite Hb in H0. inversion H0.
Qed.


(* Stating this in a backwards-direction friendly way. *)
Theorem hoare_assume : forall (Q: state -> Prop) (b:bexp),
  ⦃ b -> Q ⦄  assume b ⦃ Q ⦄.
Proof.
intros P b st r HEval Hst.
exists st. inversion HEval; subst.
split; try reflexivity.
apply Hst. apply H0.
Qed.
(* /SOLUTION *)

(* LATER: HIDE *)
(** Here are the other proof rules (sanity check) *)
(* NOTATION : IY -- Do we want <{ }> to be printing in here? *)
Theorem hoare_skip : forall P,
     ⦃ P ⦄ skip ⦃ P ⦄.
Proof.
  intros P st st' H HP. inversion H. subst.
  eexists. split. reflexivity. assumption.
Qed.

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  ⦃ P /\ b ⦄ c1 ⦃ Q ⦄ ->
  ⦃ P /\ ~ b ⦄ c2 ⦃ Q ⦄ ->
  ⦃ P ⦄ if b then c1 else c2 end ⦃ Q ⦄.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b is true *)
    apply (HTrue st st').
      assumption.
      split. assumption.
      apply bexp_eval_true. assumption.
  - (* b is false *)
    apply (HFalse st st').
      assumption.
      split. assumption.
      apply bexp_eval_false. assumption. Qed.

Theorem hoare_while : forall P (b:bexp) c,
  ⦃ P /\ b ⦄ c ⦃ P ⦄ ->
  ⦃ P ⦄ while b do c end ⦃ P /\ ~b ⦄.
Proof.
  intros P b c Hhoare st st' He HP.
  remember <{while b do c end}> as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *)
    eexists. split. reflexivity. split.
    assumption. apply bexp_eval_false. assumption.
  - (* E_WhileTrueNormal *)
    clear IHHe1.
    apply IHHe2. reflexivity.
    clear IHHe2 He2 r.
    unfold hoare_triple in Hhoare.
    apply Hhoare in He1.
    + destruct He1 as [st1 [Heq Hst1] ].
        inversion Heq; subst.
        assumption.
    + split; assumption.
  - (* E_WhileTrueError *)
     exfalso. clear IHHe.
     unfold hoare_triple in Hhoare.
     apply Hhoare in He.
     + destruct He as [st' [C _] ]. inversion C.
     + split; assumption.
Qed.
(* LATER: /HIDE *)

Example assert_assume_example:
  ⦃ True⦄
  assume (X = 1);
  X := X + 1;
  assert (X = 2)
  ⦃ True ⦄.

End HoareAssertAssume.
(** [] *)

(* HIDE *)
(* LATER: A possible exercise on hoare logic with exceptions... *)
(* EX4A? (throw_hoare) *)
(** In the [exn_imp] exercise in chapter \CHAPV1{Imp} of _Logical
    Foundations_, we saw how to add a simple mechanism for raising and
    handling exceptions to Imp.  We now consider how to extend Hoare
    logic to reason about this language. *)
Module ThrowHoare.
Import ThrowImp.

Definition hoare_quad
           (P:Assertion) (c:com) (Q:Assertion) (S:Assertion) : Prop :=
  forall st st' s,
     st =[ c ]=> st' / s ->
     P st  ->
     (s = SNormal -> Q st') /\ (s = SThrow -> S st').

Notation "⦃  P ⦄ c ⦃ Q ⦄ ⦃ S  ⦄" :=
  (hoare_quad P c Q S) (at level 90, c custom com at level 99)
  : hoare_spec_scope.

Theorem hoare_skip : forall P S,
     ⦃ P ⦄ skip ⦃ P ⦄ ⦃ S ⦄.

Theorem hoare_seq : forall P Q R S c1 c2,
     ⦃ Q ⦄ c2 ⦃ R ⦄ ⦃ S ⦄ ->
     ⦃ P ⦄ c1 ⦃ Q ⦄ ⦃ S ⦄ ->
     ⦃ P ⦄ c1;c2 ⦃ R ⦄ ⦃ S ⦄.

Theorem hoare_stop : forall Q S,
     ⦃ S ⦄ throw ⦃ Q ⦄ ⦃ S ⦄.

Lemma hoare_try : forall P Q S1 S2 c1 c2,
  ⦃ P ⦄ c1 ⦃ Q ⦄ ⦃ S1 ⦄ ->
  ⦃ S1 ⦄ c2 ⦃ Q ⦄ ⦃ S2 ⦄ ->
  ⦃ P ⦄ try c1 catch c2 end ⦃ Q ⦄ ⦃ S2 ⦄.

Lemma hoare_while : forall P S (b:bexp) c,
  ⦃ P /\ b ⦄ c ⦃ P ⦄ ⦃ S ⦄ ->
  ⦃ P ⦄ while b do c end ⦃ P /\ ~ b ⦄ ⦃ S ⦄.
End ThrowHoare.
(** [] *)
(* /HIDE *)
(* /FULL *)


(* HIDE *)
(* Local Variables: *)
(* fill-column: 70 *)
(* outline-regexp: "(\\*\\* \\*+\\|(\\* EX[1-5]..." *)
(* End: *)
(* mode: outline-minor *)
(* outline-heading-end-regexp: "\n" *)
(* /HIDE *)

(* SOONER: The vertical spacing of displays in HTML is particularly
   bad in this chapter, especially displays within bulleted lists! *)
(* LATER: Sampsa's comments:

   The exercise `if_minus_plus_reloaded` does not use `_`
   for fillable blanks as was done previously
   in `foo'` of `IndPrinciples`.

   In order to make proofs using `verify` robust
   with respect to variable renaming,
   I noticed that tactics like `assert (G : ~ st X <> 0) by assumption`
   work well and without having to introduce any new concepts
   (such as matching on the goal explicitly).
   Perhaps this could be used in the book as well.

   ======
   It would be nice if `X + 1` was written `1 + X`,
   so that using `Nat.add_1_r` everywhere would not be necessary.
   In general, everything flows smoother
   when the "most constant" argument is chosen
   to be the structurally decreasing one.
   This principle applies to many functional programming languages,
   so it is odd to see it ignored here.

   MRC'20: Hm, that's a good point, but I don't see anywhere that
   [add_1_r] is being used now.  I did discover that this is a good
   idea to streamline the proofs of [fib], so I made the change there.
   Maybe that addresses the comment as much as necessary?
   ======
*)
(* SOONER: FOLD some proofs *)
(* LATER: add some "why doesn't this invariant work?" exercises to the
   invariant finding / decorated programs section; we could give them
   many different wrong invariants for a program and ask them which of
   the 3 conditions breaks for each of them *)
(* LATER: There are some more exercises in John Reynolds's books
   (especially the old one).  One good one is fast exponentiation. *)
(* LATER: Maybe make an advanced exercise/example out of the GCD
   decorated program at the end of this file (BCP: low priority) *)
(* LATER:
   -- we don't explain very well how to specify programs
      -- e.g., it might be worth adding an exercise in which they have
         to add a Coq function / relation implementing / specifying
         the behavior of a given a piece of Imp code
      -- after this is properly explained we could hide (some of) the
         specifications that are now given to them in exercises, and
         ask them to find them out
      -- BCP: This would be great
   -- maybe hide less of the formally decorated programs "hidden
      appendix", and turn it instead into a "show off" for our
      mechanization?
      -- we need to be careful not to give spoilers for the exercises
         in the file, but other than this, why not?
      -- in general the exercises in the formal decorated programs
         sections are quite thin at the moment, and they are sometimes
         spoilers / spoiled by new exercises that come earlier *)
(* LATER: Here's a very nice problem that Arthur proposed but that we
   haven't found the time to write out in detail.  Not sure whether it
   belongs here or with the formal decorated programs.  (Maybe we
   should try to put most new examples there...)

      ⦃ X = n /\ n > 1 ⦄
    P := 1;
    D := 2;
    while D < X AND P = 1 do
      Y := X;
      while Y >= D do
        Y := Y - D
      end;
      ⦃ exists q, X = q * D + Y ⦄
      if Y = 0 then
        P := 0
      else
        skip
      end;
      D := D + 1
    end
      ⦃ I /\ (D >= X \/ P <> 1) ⦄ ->>
      ⦃ P = 1 -> (forall d, (exists q, n = d * q) -> d = 1 \/ d = n) ⦄

    I= (P = 1 -> (forall d, d <= D -> (exists q, X = d * q) -> d = 1 \/ d = n))
       /\ X = n /\ n > 1
*)
(* LATER: A possible (harder, perhaps advanced or optional)
   exercise -- nice because it has nested loops...

  ⦃ Y = n ⦄
  Z := 0;
  ⦃ I ⦄
  while Y > 0 do
    ⦃ I /\ Y>0 ⦄
    X := Y;
    while X > 0 do
      Z := Z + 1;
      X := X - 1
    end;
    Y := Y - 1
    ⦃ I ⦄
  end
  ⦃ I /\ ~(Y > 0) ⦄
  ⦃ Z = n*(n-1)/2 ⦄

  where I = Z + Y*(Y+1)/2 = n*(n+1)/2
 *)

(* LATER: MRC'20: Here are a bunch of improvements I wanted to make
   but didn't have time to get to.  Maybe next time if no one else
   gets to them first.

   1. This chapter feels largely disconnected from the style of the rest
      of the series, which is "100% Coq script".  There's a significant
      amount of "just comments" here instead.  I think we could make
      this much better by introducing formal decorated programs right
      after we informally define them.  Then in the examples that follow
      do each informal decorated program (to get students to find the right
      assertions, more or less) followed immediately by a formal version,
      instead of  delaying formal so far to the end. The `parity_formal`
      exercise is a good example of one that already almost does this already.
   2. There are several places where we are verifying Imp program schemas,
      not actual programs.  We're mixing Coq variables with Imp variables.
      That's confusing.  One example is [two_loops]; I've tried to mark
      others as I come across them.
   3. Weakest preconditions show up in this chapter as completely optional,
      then are revisited (and required) in HoareAsLogic.  Consider moving
      the entire treatment to that chapter.
   4. It seems a shame that the SparseAnnotations section is not visible
      in the full version, but only in a solution.  It's fantastic!
      It would be great to show it off.
*)


(* HIDE: ------------------------------------------------------------------ *)

(* TERSE *)



(* /TERSE *)

(* ####################################################### *)
(** * Decorated Programs *)

(* SOONER: Some theorems are not being redefined for the modified
   versions of Imp. We should either re-prove them or add hints (or
   exercises!) about this. *)
(* SOONER: Use informal mathematical notations everywhere we can! *)
(* LATER: Explain this better?... *)
(** The beauty of Hoare Logic is that it is _compositional_: the
    structure of proofs exactly follows the structure of programs.

    It follows that, as we saw in \CHAP{Hoare}, we can record the
    essential ideas of a proof (informally, and leaving out some
    low-level calculational details) by "decorating" a program with
    appropriate assertions on each of its commands.

    Such a _decorated program_ carries within it an argument for its
    own correctness. *)

(** TERSE: *** *)
(** For example, consider the program:

    X := m;
    Z := p;
    while ~(X = 0) do
      Z := Z - 1;
      X := X - 1
    end

*)
(** TERSE: *** *)
(** Here is one possible specification for this program:

      ⦃ True ⦄
    X := m;
    Z := p;
    while ~(X = 0) do
      Z := Z - 1;
      X := X - 1
    end
      ⦃ Z = p - m ⦄

   Note the _parameters_ [m] and [p], which stand for
   fixed-but-arbitrary numbers.  Formally, they are simply Coq
   variables of type [nat].
*)
(** TERSE: *** *)
(** Here is a decorated version of the program, embodying a
    proof of this specification:

      ⦃ True ⦄ ->>
      ⦃ m = m ⦄
    X := m;
      ⦃ X = m ⦄ ->>
      ⦃ X = m /\ p = p ⦄
    Z := p;
      ⦃ X = m /\ Z = p ⦄ ->>
      ⦃ Z - X = p - m ⦄
    while ~(X = 0) do
        ⦃ Z - X = p - m /\ X <> 0 ⦄ ->>
        ⦃ (Z - 1) - (X - 1) = p - m ⦄
      Z := Z - 1;
        ⦃ Z - (X - 1) = p - m ⦄
      X := X - 1
        ⦃ Z - X = p - m ⦄
    end
      ⦃ Z - X = p - m /\ ~ (X <> 0) ⦄ ->>
      ⦃ Z = p - m ⦄

*)

(* LATER: MRC'20: It bothers me a little in the proof above (and
   similarly throughout the whole file really when it comes to guards)
   that when we get to this part:

    while ~(X = 0) do ⦃ Z - X = p - m /\ X <> 0 ⦄ ->>

   we are inconsistent about [X <> 0] vs. [~(X=0)].  I admit they
   evaluate the same (er, sort of---the former is a [bexp] whereas the
   latter is an assertion), but they aren't syntactically the same.
   Since what we're teaching here (mechanized Hoare logic) is fussy
   about syntax, it strikes me as something we ought to be precise
   about. But it's an annoying change to propagate through the file,
   so I haven't done it. Is it worth a comment, or do others not get
   bothered by this?  Another way to fix this would be to add the [<>]
   operator to Imp, so that we can write the guard in the nicer way.

   BCP 20: I think adding in a few more boolean operators at the
   outside is the way to go... *)

(** Concretely, a decorated program consists of the program text
    interleaved with assertions (or possibly multiple assertions
    separated by implications). *)

(** TERSE: *** *)
(** To check that a decorated program represents a valid proof, we
    check that each individual command is _locally consistent_ with
    its nearby assertions in the following sense: *)

(* SOONER: BCP: We're inconsistent about whether we're defining
   "locally consistent" or "locally consistent wrt P and Q"... *)
(** - [skip] is locally consistent if its precondition and
      postcondition are the same:

          ⦃ P ⦄ skip ⦃ P ⦄

*)
(** TERSE: *** *)

(** - The sequential composition of [c1] and [c2] is locally
      consistent (with respect to assertions [P] and [R]) if [c1] is
      locally consistent (with respect to [P] and [Q]) and [c2] is
      locally consistent (with respect to [Q] and [R]):

          ⦃ P ⦄ c1; ⦃ Q ⦄ c2 ⦃ R ⦄

*)
(** TERSE: *** *)

(** - An assignment [X ::= a] is locally consistent with respect to
      a precondition of the form [P [X |-> a]] and the postcondition [P]:

          ⦃ P [X |-> a] ⦄
          X := a
          ⦃ P ⦄

*)
(** TERSE: *** *)

(** - A conditional is locally consistent with respect to assertions
      [P] and [Q] if its "then" branch is locally consistent with respect
      to [P /\ b] and [Q]) and its "else" branch is locally consistent
      with respect to [P /\ ~b] and [Q]:

          ⦃ P ⦄
          if b then
            ⦃ P /\ b ⦄
            c1
            ⦃ Q ⦄
          else
            ⦃ P /\ ~b ⦄
            c2
            ⦃ Q ⦄
          end
          ⦃ Q ⦄

*)
(** TERSE: *** *)

(** - A while loop with precondition [P] is locally consistent if its
      postcondition is [P /\ ~b], if the pre- and postconditions of
      its body are exactly [P /\ b] and [P], and if its body is
      locally consistent with respect to assertions [P /\ b] and [P]:

          ⦃ P ⦄
          while b do
            ⦃ P /\ b ⦄
            c1
            ⦃ P ⦄
          end
          ⦃ P /\ ~b ⦄

*)
(** TERSE: *** *)

(** - A pair of assertions separated by [->>] is locally consistent if
      the first implies the second:

          ⦃ P ⦄ ->>
          ⦃ P' ⦄

      This corresponds to the application of [hoare_consequence], and it
      is the _only_ place in a decorated program where checking whether
      decorations are correct is not fully mechanical and syntactic,
      but rather may involve logical and/or arithmetic reasoning. *)

(** FULL: These local consistency conditions essentially describe a
    procedure for _verifying_ the correctness of a given proof. This
    verification involves checking that every single command is
    locally consistent with the accompanying assertions.

    If we are instead interested in _finding_ a proof for a given
    specification, we need to discover the right assertions. This can
    be done in an almost mechanical way, with the exception of finding
    loop invariants. In the remainder of this section we explain in
    detail how to construct decorations for several short programs,
    all of which are loop-free or have simple loop invariants. We
    defer a full discussion of finding loop invariants to the next
    section. *)

(* ####################################################### *)
(** ** Example: Swapping Using Addition and Subtraction *)

(* INSTRUCTORS: Formal version below is called [swap_dec] *)

(** Here is a program that swaps the values of two variables using
    addition and subtraction (instead of by assigning to a temporary
    variable).

       X := X + Y;
       Y := X - Y;
       X := X - Y

    We can prove (informally) using decorations that this program is
    correct -- i.e., it always swaps the values of variables [X] and [Y]. *)
(* TERSE: WORK IN CLASS *)
(** FULL:

    (1)     ⦃ X = m /\ Y = n ⦄ ->>
    (2)     ⦃ (X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m ⦄
           X := X + Y;
    (3)     ⦃ X - (X - Y) = n /\ X - Y = m ⦄
           Y := X - Y;
    (4)     ⦃ X - Y = n /\ Y = m ⦄
           X := X - Y
    (5)     ⦃ X = n /\ Y = m ⦄

    The decorations can be constructed as follows:

      - We begin with the undecorated program (the unnumbered lines).

      - We add the specification -- i.e., the outer precondition (1)
        and postcondition (5). In the precondition, we use parameters
        [m] and [n] to remember the initial values of variables [X]
        and [Y] so that we can refer to them in the postcondition (5).

      - We work backwards, mechanically, starting from (5) and
        proceeding until we get to (2). At each step, we obtain the
        precondition of the assignment from its postcondition by
        substituting the assigned variable with the right-hand-side of
        the assignment. For instance, we obtain (4) by substituting
        [X] with [X - Y] in (5), and we obtain (3) by substituting [Y]
        with [X - Y] in (4).

    Finally, we verify that (1) logically implies (2) -- i.e., that
    the step from (1) to (2) is a valid use of the law of
    consequence. For this we substitute [X] by [m] and [Y] by [n] and
    calculate as follows:

            (m + n) - ((m + n) - n) = n /\ (m + n) - n = m
            (m + n) - m = n /\ m = m
            n = n /\ m = m


    Note that, since we are working with natural numbers rather than
    fixed-width machine integers, we don't need to worry about the
    possibility of arithmetic overflow anywhere in this argument.
    This makes life quite a bit simpler! *)

(* LATER: A quick / optional exercise using just assignment here
   would be good. *)

(* ####################################################### *)
(** ** Example: Simple Conditionals *)

(* INSTRUCTORS: Formal decorated version is called [if_minus_dec] *)

(* LATER: This is not such an interesting example... *)
(** TERSE: Here's a simple program using conditionals, with a possible
    specification:

         ⦃ True ⦄
       if X <= Y then
         Z := Y - X
       else
         Z := X - Y
       end
         ⦃ Z + X = Y \/ Z + Y = X ⦄

    Let's turn it into a decorated program...
*)
(* TERSE: WORK IN CLASS *)
(** FULL: Here is a simple decorated program using conditionals:

      (1)     ⦃ True⦄
            if X <= Y then
      (2)       ⦃ True /\ X <= Y ⦄ ->>
      (3)       ⦃ (Y - X) + X = Y \/ (Y - X) + Y = X⦄
              Z := Y - X
      (4)       ⦃ Z + X = Y \/ Z + Y = X⦄
            else
      (5)       ⦃ True /\ ~(X <= Y) ⦄ ->>
      (6)       ⦃ (X - Y) + X = Y \/ (X - Y) + Y = X⦄
              Z := X - Y
      (7)       ⦃ Z + X = Y \/ Z + Y = X⦄
            end
      (8)     ⦃ Z + X = Y \/ Z + Y = X⦄

These decorations were constructed as follows:

  - We start with the outer precondition (1) and postcondition (8).

  - We follow the format dictated by the [hoare_if] rule and copy the
    postcondition (8) to (4) and (7). We conjoin the precondition (1)
    with the guard of the conditional to obtain (2). We conjoin (1)
    with the negated guard of the conditional to obtain (5).

  - In order to use the assignment rule and obtain (3), we substitute
    [Z] by [Y - X] in (4). To obtain (6) we substitute [Z] by [X - Y]
    in (7).
  - Finally, we verify that (2) implies (3) and (5) implies (6). Both
    of these implications crucially depend on the ordering of [X] and
    [Y] obtained from the guard. For instance, knowing that [X <= Y]
    ensures that subtracting [X] from [Y] and then adding back [X]
    produces [Y], as required by the first disjunct of (3). Similarly,
    knowing that [~ (X <= Y)] ensures that subtracting [Y] from [X]
    and then adding back [Y] produces [X], as needed by the second
    disjunct of (6). Note that [n - m + m = n] does _not_ hold for
    arbitrary natural numbers [n] and [m] (for example, [3 - 5 + 5 =
    5]). *)
(** NOTATION: LATER: The [~] in that paragraph will typeset wrong if
    the space after it is removed.  Maybe it's better to give up on
    all the unicode hacks in the generated HTML...? *)

(* FULL *)
(* EX2M (if_minus_plus_reloaded) *)
(* INSTRUCTORS: Formal decorated program is called [if_minus_plus_dec] *)
(** Fill in valid decorations for the following program:

       ⦃ True ⦄
      if X <= Y then
          ⦃                         ⦄ ->>
          ⦃                         ⦄
        Z := Y - X
          ⦃                         ⦄
      else
          ⦃                         ⦄ ->>
          ⦃                         ⦄
        Y := X + Z
          ⦃                         ⦄
      end
        ⦃ Y = X + Z ⦄

    Briefly justify each use of [->>].
*)

(* GRADE_MANUAL 2: decorations_in_if_minus_plus_reloaded *)
(** [] *)
(* QUIETSOLUTION *)
(*

   ⦃ True ⦄
   if X <= Y then
     ⦃ True /\ X <= Y ⦄ ->>
     ⦃ Y = X + (Y - X) ⦄
     Z := Y - X
     ⦃ Y = X + Z ⦄
   else
     ⦃ True /\ ~(X <= Y) ⦄ ->>
     ⦃ X + Z = X + Z ⦄
     Y := X + Z
     ⦃ Y = X + Z ⦄
   end
   ⦃ Y = X + Z ⦄


The second use of consequence is trivial, while the first
crucially depends on the [X <= Y] condition, which ensures that
subtracting [X] from [Y] and then adding back [X] produces [Y]. *)
(* /QUIETSOLUTION *)
(* /FULL *)

(* ####################################################### *)
(** ** Example: Reduce to Zero *)

(* INSTRUCTORS: no _dec for this one: it's too simple and we prove it
   formally below anyway *)

(** TERSE: Here is a very simple [while] loop with a simple
    specification:

          ⦃ True ⦄
        while ~(X = 0) do
          X := X - 1
        end
          ⦃ X = 0 ⦄

*)
(* TERSE: WORK IN CLASS *)
(** FULL: Here is a [while] loop that is so simple that [True] suffices
    as a loop invariant.

        (1)      ⦃ True ⦄
               while ~(X = 0) do
        (2)        ⦃ True /\ X <> 0 ⦄ ->>
        (3)        ⦃ True ⦄
                 X := X - 1
        (4)        ⦃ True ⦄
               end
        (5)      ⦃ True /\ ~(X <> 0) ⦄ ->>
        (6)      ⦃ X = 0 ⦄

   The decorations can be constructed as follows:

     - Start with the outer precondition (1) and postcondition (6).

     - Following the format dictated by the [hoare_while] rule, we copy
       (1) to (4). We conjoin (1) with the guard to obtain (2). The guard
       is a Boolean expression [~(X = 0)], which for simplicity we
       express in assertion (2) as [X <> 0]. We also conjoin (1) with the
       negation of the guard to obtain (5).

     - Because the outer postcondition (6) does not syntactically match (5),
       we add an implication between them.

     - Using the assignment rule with assertion (4), we trivially substitute
       and obtain assertion (3).

     - We add the implication between (2) and (3).

   Finally we check that the implications do hold; both are trivial. *)

(** TERSE: *** *)
(** From an informal proof in the form of a decorated program, it is
    easy to read off a formal proof using the Coq versions of the
    Hoare rules.  Note that we do _not_ unfold the definition of
    [hoare_triple] anywhere in this proof -- the idea is to use the
    Hoare rules as a self-contained logic for reasoning about
    programs. *)

Definition reduce_to_zero' : com :=
  <{ while ~(X = 0) do
       X := X - 1
     end }>.

Theorem reduce_to_zero_correct' :
  ⦃ True⦄
    reduce_to_zero'
  ⦃ X = 0 ⦄.
Proof.
  unfold reduce_to_zero'.
  (* First we need to transform the postcondition so
     that hoare_while will apply. *)
  eapply hoare_consequence_post.
  - apply hoare_while.
    + (* Loop body preserves invariant *)
      (* Need to massage precondition before [hoare_asgn] applies *)
      eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * (* Proving trivial implication (2) ->> (3) *)
        unfold assn_sub, "->>". simpl. intros. exact I.
  - (* Invariant and negated guard imply postcondition *)
    intros st [Inv GuardFalse].
    unfold bassn in GuardFalse. simpl in GuardFalse.
    rewrite not_true_iff_false in GuardFalse.
    rewrite negb_false_iff in GuardFalse.
    apply eqb_eq in GuardFalse.
    apply GuardFalse.
Qed.

(** TERSE: *** *)
(** In \CHAP{Hoare} we introduced a series of tactics named [assn_auto]
    to automate proofs involving just assertions.  We can try using
    the most advanced of those tactics to streamline the previous proof: *)

Theorem reduce_to_zero_correct'' :
  ⦃ True⦄
  reduce_to_zero'
  ⦃ X = 0 ⦄.
Proof.
  unfold reduce_to_zero'.
  eapply hoare_consequence_post.
  - apply hoare_while.
    + eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * assn_auto''.
  - assn_auto''. (* doesn't succeed *)
Abort.

(** FULL: Let's introduce a (much) more sophisticated tactic that will
    help with proving assertions throughout the rest of this chapter.
    You don't need to understand the details of it. Briefly, it uses
    [split] repeatedly to turn all the conjunctions into separate
    subgoals, tries to use several theorems about booleans
    and (in)equalities, then uses [eauto] and [omega] to finish off as
    many subgoals as possible. What's left after [verify] does its
    thing is just the "interesting parts" of checking that the
    assertions correct --which might be nothing. *)
(** TERSE: *** *)
(** TERSE: Automation to the rescue! *)
(** SOONER: Explain any other bits of it? *)

Ltac verify_assn :=
  repeat split;
  simpl; unfold assert_implies;
  unfold ap in *; unfold ap2 in *;
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat (simpl in *;
          rewrite t_update_eq ||
          (try rewrite t_update_neq; [| (intro X; inversion X; fail)]));
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] => destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] => rewrite -> H in *; clear H
        | [H : _ = st _ |- _] => rewrite <- H in *; clear H
        end
    end;
  try eauto; try lia.

(** TERSE: *** *)
(** All that automation makes it easy to verify [reduce_to_zero']: *)

Theorem reduce_to_zero_correct''' :
  ⦃ True⦄
  reduce_to_zero'
  ⦃ X = 0 ⦄.
(* FOLD *)
Proof.
  unfold reduce_to_zero'.
  eapply hoare_consequence_post.
  - apply hoare_while.
    + eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * verify_assn.
  - verify_assn.
Qed.
(* /FOLD *)

(* ####################################################### *)
(** ** Example: Division *)

(* INSTRUCTORS: Formal decorated program called [div_mod_dec] *)

(* HIDE: Exercise adapted from final 2012 (original exercise by
   Loris). This might be a good example to show _before_ going into
   more advanced discussions about _finding_ loop invariants. As a
   consequence I've adapted this to keep the loop invariant as simple
   and as close to the final postcondition as possible. *)

(* LATER: Parameters may be a little puzzling to
   some students -- what does it mean to mix Coq variables and Imp
   variables in the same expression??  (In lecture I talk a lot about
   parameters, and I've tried in a few places to be more explicit
   about quantifiers (writing an explicit [forall m n : nat,] in from
   the following, for example), but it come out perfectly in the
   text at the moment.
   MRC'20: Parameters come up for the first time at the very
   beginning of the section titled Decorated Programs, about 600 lines
   above here.  Can we just say "parameters" here and leave it at that?
   That's the change I've made below, instead of re-explaining them. *)
(** The following Imp program calculates the integer quotient and
    remainder of parameters [m] and [n].

       X := m;
       Y := 0;
       while n <= X do
         X := X - n;
         Y := Y + 1
       end;

    If we replace [m] and [n] by numbers and execute the program, it
    will terminate with the variable [X] set to the remainder when [m]
    is divided by [n] and [Y] set to the quotient. *)
(** TERSE: *** *)
(** TERSE: Here's a possible specification:

        ⦃ True ⦄
      X := m;
      Y := 0;
      while n <= X do
        X := X - n;
        Y := Y + 1
      end
        ⦃ n * Y + X = m /\ X < n ⦄

*)

(* TERSE: WORK IN CLASS *)
(** FULL: In order to give a specification to this program we need to
    remember that dividing [m] by [n] produces a remainder [X] and a
    quotient [Y] such that [n * Y + X = m /\ X < n].

    It turns out that we get lucky with this program and don't have to
    think very hard about the loop invariant: the invariant is just
    the first conjunct [n * Y + X = m], and we can use this to
    decorate the program.

      (1)    ⦃ True ⦄ ->>
      (2)    ⦃ n * 0 + m = m ⦄
           X := m;
      (3)    ⦃ n * 0 + X = m ⦄
           Y := 0;
      (4)    ⦃ n * Y + X = m ⦄
           while n <= X do
      (5)      ⦃ n * Y + X = m /\ n <= X ⦄ ->>
      (6)      ⦃ n * (Y + 1) + (X - n) = m ⦄
             X := X - n;
      (7)      ⦃ n * (Y + 1) + X = m ⦄
             Y := Y + 1
      (8)      ⦃ n * Y + X = m ⦄
           end
      (9)    ⦃ n * Y + X = m /\ ~ (n <= X) ⦄ ->>
     (10)    ⦃ n * Y + X = m /\ X < n ⦄

    Assertions (4), (5), (8), and (9) are derived mechanically from
    the invariant and the loop's guard.  Assertions (8), (7), and (6)
    are derived using the assignment rule going backwards from (8)
    to (6).  Assertions (4), (3), and (2) are again backwards
    applications of the assignment rule.

    Now that we've decorated the program it only remains to check that
    the uses of the consequence rule are correct -- i.e., that (1)
    implies (2), that (5) implies (6), and that (9) implies (10). This
    is indeed the case:
      - (1) ->> (2):  trivial, by algebra.
      - (5) ->> (6):  because [n <= X], we are guaranteed that the
        subtraction in (6) does not get zero-truncated.  We can
        therefore rewrite (6) as [n * Y + n + X - n] and cancel the
        [n]s, which results in the left conjunct of (5).
      - (9) ->> (10):  if [~ (n <= X)] then [X < n].  That's straightforward
        from high-school algebra.
    So, we have a valid decorated program. *)

(* ####################################################### *)
(** * Finding Loop Invariants *)

(* INSTRUCTORS: This section is a Coq-free zone. :-)
   MRC'20: actually [parity] is not Coq-free, and it's better because
   of that.  I would like to see all the examples in here have Coq
   formalization, but I didn't have time to get to it this year.
*)

(** FULL: Once the outermost precondition and postcondition are
    chosen, the only creative part in verifying programs using Hoare
    Logic is finding the right loop invariants.  The reason this is
    difficult is the same as the reason that inductive mathematical
    proofs are:

    - Strengthening the *loop invariant* means that you have a stronger
      assumption to work with when trying to establish the
      postcondition of the loop body, but it also means that the loop
      body's postcondition is stronger and thus harder to prove.

    - Strengthening the *induction hypothesis* means that you have a
      stronger assumption to work with when trying to complete the
      induction step of the proof, but it also means that the
      statement being proved inductively is stronger and thus harder
      to prove.

    This section explains how to approach the challenge of finding
    loop invariants through a series of examples and exercises. *)

(** TERSE: Once the outer pre- and postcondition are chosen, the only
    creative part in verifying programs using Hoare Logic is finding
    the right loop invariants... *)

(** ** Example: Slow Subtraction *)

(* LATER: CH: After the latest changes I'm no fully longer
   convinced about the use of incrementality in this example (the
   reasoning at the end can be done directly on the original
   skeleton). Try to find another example in which the pre- +
   postcondition are enough to derive the invariant? *)

(* INSTRUCTORS: formal decorated program for this is called
   [subtract_slowly_dec], and it's given as an example in the formal
   decorated programs section *)

(** The following program subtracts the value of [X] from the value of
    [Y] by repeatedly decrementing both [X] and [Y].  We want to verify its
    correctness with respect to the pre- and postconditions shown:

             ⦃ X = m /\ Y = n ⦄
           while ~(X = 0) do
             Y := Y - 1;
             X := X - 1
           end
             ⦃ Y = n - m ⦄

*)

(** TERSE: *** *)
(** To verify this program, we need to find an invariant [Inv] for the
    loop.  As a first step we can leave [Inv] as an unknown and build a
    _skeleton_ for the proof by applying the rules for local
    consistency (working from the end of the program to the beginning,
    as usual, and without any thinking at all yet).

    This leads to the following skeleton:

        (1)      ⦃ X = m /\ Y = n ⦄  ->>             (a)
        (2)      ⦃ Inv ⦄
               while ~(X = 0) do
        (3)        ⦃ Inv /\ X <> 0 ⦄  ->>              (c)
        (4)        ⦃ Inv [X |-> X-1] [Y |-> Y-1] ⦄
                 Y := Y - 1;
        (5)        ⦃ Inv [X |-> X-1] ⦄
                 X := X - 1
        (6)        ⦃ Inv ⦄
               end
        (7)      ⦃ Inv /\ ~ (X <> 0) ⦄  ->>            (b)
        (8)      ⦃ Y = n - m ⦄

    By examining this skeleton, we can see that any valid [Inv] will
    have to respect three conditions:
    - (a) it must be _weak_ enough to be implied by the loop's
      precondition, i.e., (1) must imply (2);
    - (b) it must be _strong_ enough to imply the program's postcondition,
      i.e., (7) must imply (8);
    - (c) it must be _preserved_ by each iteration of the loop (given
      that the loop guard evaluates to true), i.e., (3) must imply (4). *)
(** LATER: Here's another opportunity for a bad [~] (in the proof)... *)

(* TERSE: WORK IN CLASS *)
(** FULL: These conditions are actually independent of the particular
    program and specification we are considering: every loop
    invariant has to satisfy them. One way to find an invariant that
    simultaneously satisfies these three conditions is by using an
    iterative process: start with a "candidate" invariant (e.g., a
    guess or a heuristic choice) and check the three conditions above;
    if any of the checks fails, try to use the information that we get
    from the failure to produce another -- hopefully better -- candidate
    invariant, and repeat.

    For instance, in the reduce-to-zero example above, we saw that,
    for a very simple loop, choosing [True] as an invariant did the
    job.  So let's try instantiating [Inv] with [True] in the skeleton
    above and see what we get...

        (1)      ⦃ X = m /\ Y = n ⦄ ->>       (a - OK)
        (2)      ⦃ True ⦄
               while ~(X = 0) do
        (3)        ⦃ True /\ X <> 0 ⦄  ->>    (c - OK)
        (4)        ⦃ True ⦄
                 Y := Y - 1;
        (5)        ⦃ True ⦄
                 X := X - 1
        (6)        ⦃ True ⦄
               end
        (7)      ⦃ True /\ ~(X <> 0) ⦄  ->>       (b - WRONG!)
        (8)      ⦃ Y = n - m ⦄

    While conditions (a) and (c) are trivially satisfied, condition
    (b) is wrong, i.e., it is not the case that [True /\ X = 0] (7)
    implies [Y = n - m] (8).  In fact, the two assertions are
    completely unrelated, so it is very easy to find a counterexample
    to the implication (say, [Y = X = m = 0] and [n = 1]).

    If we want (b) to hold, we need to strengthen the invariant so
    that it implies the postcondition (8).  One simple way to do
    this is to let the invariant _be_ the postcondition.  So let's
    return to our skeleton, instantiate [Inv] with [Y = n - m], and
    check conditions (a) to (c) again.

    (1)      ⦃ X = m /\ Y = n ⦄  ->>          (a - WRONG!)
    (2)      ⦃ Y = n - m ⦄
           while ~(X = 0) do
    (3)        ⦃ Y = n - m /\ X <> 0 ⦄  ->>   (c - WRONG!)
    (4)        ⦃ Y - 1 = n - m ⦄
             Y := Y - 1;
    (5)        ⦃ Y = n - m ⦄
             X := X - 1
    (6)        ⦃ Y = n - m ⦄
           end
    (7)      ⦃ Y = n - m /\ ~(X <> 0) ⦄  ->>      (b - OK)
    (8)      ⦃ Y = n - m ⦄

    This time, condition (b) holds trivially, but (a) and (c) are
    broken. Condition (a) requires that (1) [X = m /\ Y = n]
    implies (2) [Y = n - m].  If we substitute [Y] by [n] we have to
    show that [n = n - m] for arbitrary [m] and [n], which is not
    the case (for instance, when [m = n = 1]).  Condition (c) requires
    that [n - m - 1 = n - m], which fails, for instance, for [n = 1]
    and [m = 0]. So, although [Y = n - m] holds at the end of the loop,
    it does not hold from the start, and it doesn't hold on each
    iteration; it is not a correct invariant.

    This failure is not very surprising: the variable [Y] changes
    during the loop, while [m] and [n] are constant, so the assertion
    we chose didn't have much chance of being an invariant!

    To do better, we need to generalize (8) to some statement that is
    equivalent to (8) when [X] is [0], since this will be the case
    when the loop terminates, and that "fills the gap" in some
    appropriate way when [X] is nonzero.  Looking at how the loop
    works, we can observe that [X] and [Y] are decremented together
    until [X] reaches [0].  So, if [X = 2] and [Y = 5] initially,
    after one iteration of the loop we obtain [X = 1] and [Y = 4];
    after two iterations [X = 0] and [Y = 3]; and then the loop stops.
    Notice that the difference between [Y] and [X] stays constant
    between iterations: initially, [Y = n] and [X = m], and the
    difference is always [n - m].  So let's try instantiating [Inv] in
    the skeleton above with [Y - X = n - m].

    (1)      ⦃ X = m /\ Y = n ⦄  ->>               (a - OK)
    (2)      ⦃ Y - X = n - m ⦄
           while ~(X = 0) do
    (3)        ⦃ Y - X = n - m /\ X <> 0 ⦄  ->>    (c - OK)
    (4)        ⦃ (Y - 1) - (X - 1) = n - m ⦄
             Y := Y - 1;
    (5)        ⦃ Y - (X - 1) = n - m ⦄
             X := X - 1
    (6)        ⦃ Y - X = n - m ⦄
           end
    (7)      ⦃ Y - X = n - m /\ ~(X <> 0) ⦄  ->>       (b - OK)
    (8)      ⦃ Y = n - m ⦄

    Success!  Conditions (a), (b) and (c) all hold now.  (To
    verify (c), we need to check that, under the assumption that [X <>
    0], we have [Y - X = (Y - 1) - (X - 1)]; this holds for all
    natural numbers [X] and [Y].) *)

(* FULL *)
(* ####################################################### *)
(** ** Exercise: Slow Assignment *)

(* LATER: this is probably a better exercise than slow addition below *)

(* INSTRUCTORS: Formal decorated program for this is called
   [slow_assignment_dec] and is given as an exercise in the formal
   decorated programs section *)
(* EX2M (slow_assignment) *)
(** A roundabout way of assigning a number currently stored in [X] to
    the variable [Y] is to start [Y] at [0], then decrement [X] until
    it hits [0], incrementing [Y] at each step. Here is a program that
    implements this idea:

        ⦃ X = m ⦄
      Y := 0;
      while ~(X = 0) do
        X := X - 1;
        Y := Y + 1
      end
        ⦃ Y = m ⦄

    Write an informal decorated program showing that this procedure
    is correct, and justify each use of [->>]. *)

(* SOLUTION *)
(**

      ⦃ X = m ⦄ ->>
      ⦃ 0 + X = m ⦄
    Y := 0;
      ⦃ Y + X = m ⦄
    while ~(X = 0) do
        ⦃ Y + X = m /\ X <> 0 ⦄ ->>
        ⦃ (Y + 1) + (X - 1) = m ⦄
      X := X - 1;
        ⦃ (Y + 1) + X = m ⦄
      Y := Y + 1
        ⦃ Y + X = m ⦄
    end
      ⦃ Y + X = m /\ ~(X <> 0) ⦄
      ⦃ Y = m ⦄


    The first implication is trivial.  The second relies on using [X <>
    0] to show that the subtraction is not zero-truncated.  The third
    follows from observing that [X] must be [0].
*)
(* /SOLUTION *)

(* GRADE_MANUAL 2: decorations_in_slow_assignment *)
(** [] *)

(* ####################################################### *)
(** ** Exercise: Slow Addition *)
(* INSTRUCTORS: no formal decorated program for this one: it's too boring! *)
(* LATER: this is very very similar to slow subtraction; so a quite
   boring exercise; the specification part is also just copying what
   happened in slow subtraction.  Maybe we should just delete it? *)

(* EX3? (add_slowly_decoration) *)
(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z.

      while ~(X = 0) do
         Z := Z + 1;
         X := X - 1
      end

    Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly, and justify each use of [->>]. *)

(* SOLUTION *)
(**

    ⦃ X = m /\ Z = p ⦄ ->>
    ⦃ Z + X = p + m ⦄
  while ~(X = 0) do
       ⦃ Z + X = p + m /\ X <> 0 ⦄ ->>
       ⦃ (Z + 1) + (X - 1) = p + m ⦄
     Z := Z + 1;
       ⦃ Z + (X - 1) = p + m ⦄
     X := X - 1
       ⦃ Z + X = p + m ⦄
  end
    ⦃ Z + X = p + m /\ ~(X <> 0) ⦄ ->>
    ⦃ Z = p + m ⦄

    The first implication follows from substitution.  The second relies
    on using [X <> 0] to show that subtraction is not zero-truncated.
    The third follows from observing that [X] must be [0]. *)
(* /SOLUTION *)
(** [] *)
(* /FULL *)

(* ####################################################### *)
(** ** Example: Parity *)
(* INSTRUCTORS: This is the simplest implementation we could find of
   parity in Imp. *)
(* INSTRUCTORS: Formal decorated program called [parity_dec] *)

(** Here is a cute little program for computing the parity of the
    value initially stored in [X] (due to Daniel Cristofani).

         ⦃ X = m ⦄
       while 2 <= X do
         X := X - 2
       end
         ⦃ X = parity m ⦄

    The mathematical [parity] function used in the specification is
    defined in Coq as follows: *)

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

(* TERSE: WORK IN CLASS *)
(** FULL: The postcondition does not hold at the beginning of the loop,
    since [m = parity m] does not hold for an arbitrary [m], so we
    cannot use that as an invariant.  To find an invariant that works,
    let's think a bit about what this loop does.  On each iteration it
    decrements [X] by [2], which preserves the parity of [X].  So the
    parity of [X] does not change, i.e., it is invariant.  The initial
    value of [X] is [m], so the parity of [X] is always equal to the
    parity of [m]. Using [parity X = parity m] as an invariant we
    obtain the following decorated program:

        ⦃ X = m ⦄ ->>                               (a - OK)
        ⦃ parity X = parity m ⦄
      while 2 <= X do
          ⦃ parity X = parity m /\ 2 <= X ⦄  ->>    (c - OK)
          ⦃ parity (X-2) = parity m ⦄
        X := X - 2
          ⦃ parity X = parity m ⦄
      end
        ⦃ parity X = parity m /\ ~(2 <= X) ⦄  ->>       (b - OK)
        ⦃ X = parity m ⦄

    With this invariant, conditions (a), (b), and (c) are all
    satisfied. For verifying (b), we observe that, when [X < 2], we
    have [parity X = X] (we can easily see this in the definition of
    [parity]).  For verifying (c), we observe that, when [2 <= X], we
    have [parity X = parity (X-2)]. *)
(* HIDE: A more complexly phrased invariant for the same program

        ⦃ X = m ⦄  ->>                        (a - OK)
        ⦃ ev X <-> ev m ⦄
      while 2 <= X do
          ⦃ ev X <-> ev m /\ 2 <= X ⦄  ->>    (c - OK)
          ⦃ ev (X-2) <-> ev m ⦄
        X := X - 2
          ⦃ ev X <-> ev m ⦄
      end
        ⦃ (ev X <-> ev m) /\ ~(2 <= X) ⦄  ->>     (b - OK)
        ⦃ X=0 <-> ev m ⦄

*)
(* HIDE: find_parity'_dec; more complicated phrasing of invariant
   there is very little resamblance between the invariant and the
   postcondition -- the implication is also non-obvious, and the
   X <= m condition makes the invariant more complicated

    ⦃ X = m ⦄ ->>
    ⦃ X <= m /\ ev (m - X) ⦄
  while 2 <= X do
      ⦃ X <= m /\ ev (m - X) /\ 2 <= X ⦄ ->>
      ⦃ X - 2 <= m /\ ev (m - (X - 2)) ⦄
    X := X - 2
      ⦃ X <= m /\ ev (m - X) ⦄
  end
    ⦃ X <= m /\ ev (m - X) /\ ~(2 <= X) ⦄ ->>
    ⦃ X=0 <-> ev m ⦄

*)

(* FULL *)
(* EX3? (parity_formal) *)
(** Translate the above informal decorated program into a formal proof
    in Coq. Your proof should use the Hoare logic rules and should not
    unfold [hoare_triple]. Refer to [reduce_to_zero] for an example.

    To formally state the invariant, you will need the [ap] operator
    to apply [parity] to an Imp variable --e.g., [ap parity X].

    After using [verify_assn], you will be left needing to prove some facts
    about [parity]. The following lemmas will be helpful, as will
    [leb_complete] and [leb_correct]. *)

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
(* FOLD *)
Proof.
  induction x; intros; simpl.
  - reflexivity.
  - destruct x.
    + lia.
    + inversion H; subst; simpl.
      * reflexivity.
      * rewrite sub_0_r. reflexivity.
Qed.
(* /FOLD *)

Lemma parity_lt_2 : forall x,
  ~ 2 <= x ->
  parity x = x.
(* FOLD *)
Proof.
  induction x; intros; simpl.
  - reflexivity.
  - destruct x.
    + reflexivity.
    + lia.
Qed.
(* /FOLD *)

Theorem parity_correct : forall (m:nat),
  ⦃ X = m ⦄
  while 2 <= X do
    X := X - 2
  end
  ⦃  X = parity m  ⦄.
(** [] *)
(* /FULL *)

(* ####################################################### *)
(** ** Example: Finding Square Roots *)
(* INSTRUCTORS: Formal decorated program in [sqrt_dec] *)
(* INSTRUCTORS: the main idea introduced here is preserving equalities for
   variables that don't change, and it appears in its purest form *)

(** The following program computes the integer square root of [X]
    by naive iteration:

      ⦃ X=m ⦄
    Z := 0;
    while (Z+1)*(Z+1) <= X do
      Z := Z+1
    end
      ⦃ Z*Z<=m /\ m<(Z+1)*(Z+1) ⦄

*)

(* TERSE: WORK IN CLASS *)
(** FULL: As above, we can try to use the postcondition as a candidate
    invariant, obtaining the following decorated program:

    (1)  ⦃ X=m ⦄  ->>           (a - second conjunct of (2) WRONG!)
    (2)  ⦃ 0*0 <= m /\ m<(0+1)*(0+1) ⦄
       Z := 0;
    (3)  ⦃ Z*Z <= m /\ m<(Z+1)*(Z+1) ⦄
       while (Z+1)*(Z+1) <= X do
    (4)    ⦃ Z*Z<=m /\ (Z+1)*(Z+1)<=X ⦄  ->>             (c - WRONG!)
    (5)    ⦃ (Z+1)*(Z+1)<=m /\ m<((Z+1)+1)*((Z+1)+1) ⦄
         Z := Z+1
    (6)    ⦃ Z*Z<=m /\ m<(Z+1)*(Z+1) ⦄
       end
    (7)  ⦃ Z*Z<=m /\ m<(Z+1)*(Z+1) /\ ~((Z+1)*(Z+1)<=X) ⦄  ->> (b - OK)
    (8)  ⦃ Z*Z<=m /\ m<(Z+1)*(Z+1) ⦄

    This didn't work very well: conditions (a) and (c) both failed.
    Looking at condition (c), we see that the second conjunct of (4)
    is almost the same as the first conjunct of (5), except that (4)
    mentions [X] while (5) mentions [m]. But note that [X] is never
    assigned in this program, so we should always have [X=m]; we
    didn't propagate this information from (1) into the loop
    invariant, but we could!

    Also, we don't need the second conjunct of (8), since we can
    obtain it from the negation of the guard -- the third conjunct
    in (7) -- again under the assumption that [X=m].  This allows
    us to simplify a bit.

    So we now try [X=m /\ Z*Z <= m] as the loop invariant:

      ⦃ X=m ⦄  ->>                                      (a - OK)
      ⦃ X=m /\ 0*0 <= m ⦄
    Z := 0;
      ⦃ X=m /\ Z*Z <= m ⦄
    while (Z+1)*(Z+1) <= X do
        ⦃ X=m /\ Z*Z<=m /\ (Z+1)*(Z+1)<=X ⦄  ->>        (c - OK)
        ⦃ X=m /\ (Z+1)*(Z+1)<=m ⦄
      Z := Z + 1
        ⦃ X=m /\ Z*Z<=m ⦄
    end
      ⦃ X=m /\ Z*Z<=m /\ ~((Z+1)*(Z+1)<=X) ⦄  ->>           (b - OK)
      ⦃ Z*Z<=m /\ m<(Z+1)*(Z+1) ⦄

    This works, since conditions (a), (b), and (c) are now all
    trivially satisfied.

    Very often, if a variable is used in a loop in a read-only
    fashion (i.e., it is referred to by the program or by the
    specification and it is not changed by the loop), it is necessary
    to add the fact that it doesn't change to the loop invariant. *)

(* ####################################################### *)
(** ** Example: Squaring *)
(* HIDE: CH: it might make sense to show all the variants in a comment
   for future exercise builders, together with some hints on how to
   write programs that are easier to verify *)
(* INSTRUCTORS: using easier version of this: counting up, instead of
   counting down *)
(* INSTRUCTORS: Formal decorated program called [square_simpler_dec] *)

(** Here is a program that squares [X] by repeated addition:

    ⦃ X = m ⦄
  Y := 0;
  Z := 0;
  while ~(Y = X)  do
    Z := Z + X;
    Y := Y + 1
  end
    ⦃ Z = m*m ⦄

*)

(* TERSE: WORK IN CLASS *)
(** FULL: The first thing to note is that the loop reads [X] but doesn't
    change its value. As we saw in the previous example, it can be a good idea
    in such cases to add [X = m] to the invariant.  The other thing
    that we know is often useful in the invariant is the postcondition,
    so let's add that too, leading to the candidate invariant
    [Z = m * m /\ X = m].

      ⦃ X = m ⦄ ->>                            (a - WRONG)
      ⦃ 0 = m*m /\ X = m ⦄
    Y := 0;
      ⦃ 0 = m*m /\ X = m ⦄
    Z := 0;
      ⦃ Z = m*m /\ X = m ⦄
    while ~(Y = X) do
        ⦃ Z = m*m /\ X = m /\ Y <> X ⦄ ->>     (c - WRONG)
        ⦃ Z+X = m*m /\ X = m ⦄
      Z := Z + X;
        ⦃ Z = m*m /\ X = m ⦄
      Y := Y + 1
        ⦃ Z = m*m /\ X = m ⦄
    end
      ⦃ Z = m*m /\ X = m /\ ~(Y <> X) ⦄ ->>         (b - OK)
      ⦃ Z = m*m ⦄


    Conditions (a) and (c) fail because of the [Z = m*m] part.  While
    [Z] starts at [0] and works itself up to [m*m], we can't expect
    [Z] to be [m*m] from the start.  If we look at how [Z] progresses
    in the loop, after the 1st iteration [Z = m], after the 2nd
    iteration [Z = 2*m], and at the end [Z = m*m].  Since the variable
    [Y] tracks how many times we go through the loop, this leads us to
    derive a new invariant candidate: [Z = Y*m /\ X = m].

      ⦃ X = m ⦄ ->>                               (a - OK)
      ⦃ 0 = 0*m /\ X = m ⦄
    Y := 0;
      ⦃ 0 = Y*m /\ X = m ⦄
    Z := 0;
      ⦃ Z = Y*m /\ X = m ⦄
    while ~(Y = X) do
        ⦃ Z = Y*m /\ X = m /\ Y <> X ⦄ ->>        (c - OK)
        ⦃ Z+X = (Y+1)*m /\ X = m ⦄
      Z := Z + X;
        ⦃ Z = (Y+1)*m /\ X = m ⦄
      Y := Y + 1
        ⦃ Z = Y*m /\ X = m ⦄
    end
      ⦃ Z = Y*m /\ X = m /\ ~(Y <> X) ⦄ ->>           (b - OK)
      ⦃ Z = m*m ⦄


    This new invariant makes the proof go through: all three
    conditions are easy to check.

    It is worth comparing the postcondition [Z = m*m] and the [Z =
    Y*m] conjunct of the invariant. It is often the case that one has
    to replace parameters with variables -- or with expressions
    involving both variables and parameters, like [m - Y] -- when
    going from postconditions to invariants. *)

(* HIDE: the more complicated version from 2012's class

Here is a program that squares X by repeated addition:

  X := n;
  Y := X;
  Z := 0;
  while ~(Y = 0) do
    Z := Z + X;
    Y := Y - 1
  end


  Bob's simpler invariant for squaring [square_dec]:
  (a very similar invariant given as solution in 2011 final; exercise 3)


  ⦃ True ⦄
  X := n;
  ⦃ X = n ⦄
  Y := X;
  ⦃ X = n /\ Y = n ⦄
  Z := 0;
  ⦃ X = n /\ Y = n /\ Z = 0 ⦄ ->>
  ⦃ Z + X * Y = n * n ⦄
  while ~(Y = 0) do
    ⦃ Z + X * Y = n * n /\ (Y <> 0) ⦄ ->>
    ⦃ Z + X + X * (Y - 1) = n * n ⦄
    Z := Z + X;
    ⦃ Z + X * (Y - 1) = n * n ⦄
    Y := Y - 1
    ⦃ Z + X * Y = n * n ⦄
  end
  ⦃ Z + X * Y = n * n /\ ~(Y <> 0) ⦄ ->>
  ⦃ Z = n * n ⦄


The other invariant [square_dec']:

  ⦃ True ⦄
  X := n;
  ⦃ X = n ⦄
  Y := X;
  ⦃ X = n /\ Y = n ⦄
  Z := 0;
  ⦃ X = n /\ Y = n /\ Z = 0 ⦄ ->>
  ⦃ Z = X * (X - Y) /\ X = n /\ Y <= X ⦄
  while ~(Y = 0) do
    ⦃ Z = X * (X - Y) /\ X = n /\ Y <= X /\ (Y <> 0) ⦄ ->>
    ⦃ Z + X = X * (X - (Y - 1)) /\ X = n /\ (Y - 1) <= X ⦄
    Z := Z + X;
    ⦃ Z = X * (X - (Y - 1)) /\ X = n /\ (Y - 1) <= X ⦄
    Y := Y - 1
    ⦃ Z = X * (X - Y) /\ X = n /\ Y <= X ⦄
  end
  ⦃ Z = X * (X - Y) /\ X = n /\ Y <= X /\ ~(Y <> 0) ⦄ ->>
  ⦃ Z = n * n ⦄

*)

(* FULL *)
(* ####################################################### *)
(** ** Exercise: Factorial *)

(* INSTRUCTORS: Formal decorated program called [factorial_dec] *)
(* HIDE: CH: Note that this partly spoils the (optional) exercise from the
   formal section. *)
(* LATER: LY: Many are tempted to use division in their propositions here,
   with the invariant [Y = m!/X!].
   Informally, such a decorated program can be correct if we assume
   they use real division (in Q or R). The issue is that formally in Coq,
   the notation / is also in scope and means integer division, so a pedantic
   interpretation would mark those answers wrong, even though that is most
   likely *not* what students intended (thus making the grading unfair).
   Should we explicitly forbid use of division for this exercise?
   (I added a note to that effect in the problem statement).
   MRC'20: I strengthened your note so that it explicitly advises
   against division (and subtraction). *)
(* EX3M (factorial) *)
(** Recall that [n!] denotes the factorial of [n] (i.e., [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:

    ⦃ X = m ⦄
  Y := 1 ;
  while ~(X = 0)
  do
     Y := Y * X ;
     X := X - 1
  end
    ⦃ Y = m! ⦄

    Fill in the blanks in following decorated program. Bear in mind
    that we are working with natural numbers, for which both division
    and subtraction can behave differently than with real numbers.
    Excluding both operations from your loop invariant is advisable.

    ⦃ X = m ⦄ ->>
    ⦃                                      ⦄
  Y := 1;
    ⦃                                      ⦄
  while ~(X = 0)
  do   ⦃                                      ⦄ ->>
       ⦃                                      ⦄
     Y := Y * X;
       ⦃                                      ⦄
     X := X - 1
       ⦃                                      ⦄
  end
    ⦃                                      ⦄ ->>
    ⦃ Y = m! ⦄

    Briefly justify each use of [->>].
*)
(* QUIETSOLUTION *)

(** Solution:


    ⦃ X = m ⦄ ->>
    ⦃ 1 * X! = m! ⦄
  Y := 1;
    ⦃ Y * X! = m! ⦄
  while ~(X = 0)
  do   ⦃ Y * X! = m! /\ X <> 0 ⦄ ->>
       ⦃ Y * X * (X - 1)! = m! ⦄
     Y := Y * X;
       ⦃ Y * (X - 1)! = m! ⦄
     X := X - 1
       ⦃ Y * X! = m! ⦄
  end
    ⦃ Y * X! = m! /\ ~(X <> 0) ⦄ ->>
    ⦃ Y = m! ⦄

    The first implication holds by substitution and algebra.  The
    second holds because [X <> 0] (as in previous examples), and
    algebra.  The third holds because [X] must be [0] and [0!] is 1,
    from there by algebra.
*)
(* /QUIETSOLUTION *)
(* GRADE_MANUAL 3: decorations_in_factorial *)
(** [] *)

(* LATER: Here's a variant that I (BCP) tried working out.  I'm not
   sure I've got it quite right yet, but it's probably worth finishing
   because it nicely illustrates the point that the way you write the
   program often determines how hard it is to verify...

    ⦃ True ⦄ ->>
    ⦃ m! = 1 * m!/0! /\ 0 <= m ⦄
  Y := 1;
    ⦃ m! = Y * m!/0! /\ 0 <= m ⦄
  X := 0;
    ⦃ m! = Y * m!/X! /\ X <= m ⦄
  while X .< m do
      ⦃ m! = Y * m!/X! /\ X <= m /\ X < m ⦄ ->>
      ⦃ ... needs work here! ... ⦄ ->>
      ⦃ m! = (Y*(X+1)) * m!/(X+1)! /\ (X+1) <= m ⦄ ->>
    X := X + 1;
      ⦃ m! = (Y*X) * m!/X! /\ X <= m ⦄ ->>
    Y := Y * X
      ⦃ m! = Y * m!/X! /\ X <= m ⦄
  end
    ⦃ m! = Y * m!/X! /\ X <= m /\ ~(X < m) ⦄ ->>
    ⦃ Y = m! ⦄
 *)
(* HIDE: MRC'20: That's not really an Imp program though: it is a schema
   for an Imp program.  [m] is not an Imp variable nor a constant. *)
(* HIDE: LY: I saw one submission for [factorial_dec] use a program
   like that instead of the one already given by the informal
   exercise. I accepted it because the exercise does not require to
   reuse the given program, and we did not strictly define what it
   means to "implement" factorial in Imp.  This other one "implements"
   factorial in the same way two_loops_dec "implements" the sum (a + b
   + c). *)

(* ####################################################### *)
(** ** Exercise: Min *)

(* LATER: LY: in this exercise, many end up writing the following implication
   after the while line:

   ⦃ Z = min a b - min X Y /\ ... ⦄ ->>
   ⦃ Z+1 = min a b - min (X-1) (Y-1) /\ ... ⦄

   that is invalid if you interpret [-] pedantically as [sub : nat -> nat -> nat],
   which takes nonnegative values only. But if we are more generous and interpret
   these informal proofs in more intuitive domains (Z, Q, or R), then these proofs
   look fine. I made the former choice in my grading because I assume at this
   point they should know to be careful around [-] with [nat]. *)

(* EX3M (Min_Hoare) *)

(** Fill in valid decorations for the following program, and justify
    the uses of [->>].  As in [factorial], be careful about natural
    numbers, especially subtraction.

    In your justifications, you may rely on the following facts about min:

  Lemma lemma1 : forall x y,
    (x<>0 /\ y<>0) -> min x y <> 0.
  Lemma lemma2 : forall x y,
    min (x-1) (y-1) = (min x y) - 1.

    plus standard high-school algebra, as always. *)

(**

  ⦃ True ⦄ ->>
  ⦃                    ⦄
  X := a;
  ⦃                       ⦄
  Y := b;
  ⦃                       ⦄
  Z := 0;
  ⦃                       ⦄
  while ~(X = 0) && ~(Y = 0) do
    ⦃                                     ⦄ ->>
    ⦃                                ⦄
    X := X - 1;
    ⦃                            ⦄
    Y := Y - 1;
    ⦃                        ⦄
    Z := Z + 1
    ⦃                       ⦄
  end
  ⦃                            ⦄ ->>
  ⦃ Z = min a b ⦄

*)
(* QUIETSOLUTION *)

(* HIDE: MRC'20: It bothers me a bit that the [&&] in the guard below
   becomes a [/\] in the assertion.  We've never explained that it's okay
   to do a translation like that. *)
(** Solution:


  ⦃ True ⦄
  ->>
  ⦃ 0 + min a b = min a b ⦄
  X := a;
  ⦃ 0 + min X b = min a b ⦄
  Y := b;
  ⦃ 0 + min X Y = min a b ⦄
  Z := 0;
  ⦃ Z + min X Y = min a b ⦄
  while ~(X = 0) && ~(Y = 0) do
    ⦃ Z + min X Y = min a b /\ (X<>0 /\ Y<>0) ⦄
    ->>
    ⦃ Z+1 + min (X-1) (Y-1) = min a b ⦄
    X := X - 1;
    ⦃ Z+1 + min X (Y-1) = min a b ⦄
    Y := Y - 1;
    ⦃ Z+1 + min X Y = min a b ⦄
    Z := Z + 1
    ⦃ Z + min X Y = min a b ⦄
  end
  ⦃ Z + min X Y = min a b /\ ~(X<>0 /\ Y<>0) ⦄
  ->>
  ⦃ Z = min a b ⦄

    - The first implication holds by substitution and algebra.
    - The second holds because:
        + by lemma2 we can rewrite [Z+1 + min (X-1) (Y-1)] as
          [Z+1 + (min x y) - 1]
        + by lemma1 and [X<>0 /\ Y<>0], [min x y <> 0],
          so [(min x y) - 1] is not zero-truncated.
        + so we can rewrite [Z+1 + (min x y) - 1] as [Z + min x y].
    - The third holds because the second conjunct implies [X] and [Y]
      are both [0].
*)
(* /QUIETSOLUTION *)
(* GRADE_MANUAL 3: decorations_in_Min_Hoare *)
(** [] *)

(* HIDE: Taken from midterm 2, 2012 *)

(* INSTRUCTORS: Formal decorated program called [two_loops_dec] *)

(* EX3M (two_loops) *)
(** Here is a very inefficient way of adding 3 numbers:

     X := 0;
     Y := 0;
     Z := c;
     while ~(X = a) do
       X := X + 1;
       Z := Z + 1
     end;
     while ~(Y = b) do
       Y := Y + 1;
       Z := Z + 1
     end

    Show that it does what it should by filling in the blanks in the
    following decorated program.

      ⦃ True ⦄ ->>
      ⦃                                        ⦄
    X := 0;
      ⦃                                        ⦄
    Y := 0;
      ⦃                                        ⦄
    Z := c;
      ⦃                                        ⦄
    while ~(X = a) do
        ⦃                                        ⦄ ->>
        ⦃                                        ⦄
      X := X + 1;
        ⦃                                        ⦄
      Z := Z + 1
        ⦃                                        ⦄
    end;
      ⦃                                        ⦄ ->>
      ⦃                                        ⦄
    while ~(Y = b) do
        ⦃                                        ⦄ ->>
        ⦃                                        ⦄
      Y := Y + 1;
        ⦃                                        ⦄
      Z := Z + 1
        ⦃                                        ⦄
    end
      ⦃                                        ⦄ ->>
      ⦃ Z = a + b + c ⦄

*)
(* LATER: MRC'20: Again, the above isn't an IMP program, but a program
   schema.  What about using the following instead?

       ⦃ X = a /\ Y = b /\ Z = c ⦄
     I ::= 0;;
     while ~(I = X) do
       I ::= I + 1;;
       Z ::= Z + 1
     end;;
     I ::= 0;;
     while ~(I = Y) do
       I ::= I + 1;;
       Z ::= Z + 1
     end
       ⦃ Z = a + b + c ⦄

*)

(* QUIETSOLUTION *)
(**
Solution:

    ⦃ True ⦄ ->>
    ⦃ c = 0 + c /\ 0 = 0 ⦄
  X := 0;
    ⦃ c = X + c /\ 0 = 0 ⦄
  Y := 0;
    ⦃ c = X + c /\ Y = 0 ⦄
  Z := c;
    ⦃ Z = X + c /\ Y = 0 ⦄
  while ~(X = a) do
      ⦃ Z = X + c /\ Y = 0 /\ X <> a ⦄ ->>
      ⦃ Z + 1 = X + 1 + c /\ Y = 0 ⦄
    X := X + 1;
      ⦃ Z + 1 = X + c /\ Y = 0 ⦄
    Z := Z + 1
      ⦃ Z = X + c /\ Y = 0 ⦄
  end;
    ⦃ Z = X + c /\ Y = 0 /\ ~(X <> a) ⦄ ->>
    ⦃ Z = a + Y + c ⦄
  while ~(Y = b) do
      ⦃ Z = a + Y + c /\ Y <> b ⦄ ->>
      ⦃ Z + 1 = a + Y + 1 + c ⦄
    Y := Y + 1;
      ⦃ Z + 1 = a + Y + c ⦄
    Z := Z + 1
      ⦃ Z = a + Y + c ⦄
  end
    ⦃ Z = a + Y + c /\ ~(Y <> b) ⦄ ->>
    ⦃ Z = a + b + c ⦄


Another solution follows.  It doesn't require carrying an additional
[Y = 0] conjunct through the first loop, but instead carries an
additional [ + Y] term through it.


      ⦃ True ⦄ ->>
        ⦃ c = 0 + 0 + c ⦄
    X := 0;
        ⦃ c = X + 0 + c ⦄
    Y := 0;
        ⦃ c = X + Y + c ⦄
    Z := c;
        ⦃ Z = X + Y + c ⦄
    while ~(X = a) do
        ⦃ Z = X + Y + c /\ X <> a ⦄ ->>
        ⦃ Z + 1 = (X + 1) + Y + c ⦄
      X := X + 1;
        ⦃ Z + 1 = X + Y + c ⦄
      Z := Z + 1
        ⦃ Z = X + Y + c ⦄
    end;
      ⦃ Z = X + Y + c /\ ~(X <> a) ⦄ ->>
      ⦃ Z = a + Y + c ⦄
    while ~(Y = b) do
        ⦃ Z = a + Y + c /\ (Y <> b) ⦄ ->>
        ⦃ Z + 1 = a + (Y + 1) + c ⦄
      Y := Y + 1;
        ⦃ Z + 1 = a + Y + c ⦄
      Z := Z + 1
        ⦃ Z = a + Y + c ⦄
    end
      ⦃ Z = a + Y + c /\ ~(Y <> b) ⦄ ->>
      ⦃ Z = a + b + c ⦄

*)
(* /QUIETSOLUTION *)
(* GRADE_MANUAL 3: decorations_in_two_loops *)
(** [] *)
(* FULL *)

(* ####################################################### *)
(** ** Exercise: Power Series *)

(* INSTRUCTORS: Formal decorated program called [dpow2_down_correct] *)

(* HIDE: MRC'20: this is a nit, but, why is the exercise named [...down...]?
   The variables are all going _up_.

   Also, this is again a program schema rather than a program.  Why not...

      ⦃ True ⦄
    X ::= 0;;
    Y ::= 1;;
    Z ::= 1;;
    while ~(X = W) do
      Z ::= 2 * Z;;
      Y ::= Y + Z;;
      X ::= X + 1
    end
      ⦃ Y = 2 ^ (W + 1) - 1 ⦄

   ...?
*)

(* EX4? (dpow2_down) *)
(** Here is a program that computes the series:
    [1 + 2 + 2^2 + ... + 2^m = 2^(m+1) - 1]

    X := 0;
    Y := 1;
    Z := 1;
    while ~(X = m) do
      Z := 2 * Z;
      Y := Y + Z;
      X := X + 1
    end

    Write a decorated program for this, and justify each use of [->>]. *)

(* SOLUTION *)
(**

  ⦃ True ⦄ ->>
  ⦃ 1 = 2^(0+1)-1 /\ 1 = 2^0 ⦄
  X := 0;
  ⦃ 1 = 2^(X+1)-1 /\ 1 = 2^X ⦄
  Y := 1;
  ⦃ Y = 2^(X+1)-1 /\ 1 = 2^X ⦄
  Z := 1;
  ⦃ Y = 2^(X+1)-1 /\ Z = 2^X ⦄
  while ~(X = m) do
    ⦃ Y = 2^(X+1)-1 /\ Z = 2^X /\ (X <> m) ⦄ ->>
    ⦃ Y + 2 * Z = 2^(X+2)-1 /\ 2 * Z = 2^(X+1) ⦄
    Z := 2 * Z;
    ⦃ Y + Z = 2^(X+2)-1 /\ Z = 2^(X+1) ⦄
    Y := Y + Z;
    ⦃ Y = 2^(X+2)-1 /\ Z = 2^(X+1) ⦄
    X := X + 1
    ⦃ Y = 2^(X+1)-1 /\ Z = 2^X ⦄
  end
  ⦃ Y = 2^(X+1)-1 /\ Z = 2^X /\ ~(X <> m) ⦄ ->>
  ⦃ Y = 2^(m+1)-1 ⦄


Checking the only non-trivial application of consequence:

    ⦃ Y = 2^(X+1)-1 /\ Z = 2^X /\ (X <> m) ⦄ ->>
    ⦃ Y + 2 * Z = 2^(X+1+1)-1 /\ 2 * Z = 2^(X+1) ⦄


Need to show these two conditions:


  2^(X+1)-1 + 2 * 2^X = 2^(X+1+1)-1
  2^(X+1) + 2^(X+1) = 2^(X+2) (OK)



  2 * 2^X = 2^(X+1) (OK)


Deriving the invariant for Z mathematically:


  ⦃ Y = 2^(X+1)-1 /\ (X <> m) ⦄ ->> ⦃ Y + 2*Z = 2^(X+1+1)-1 ⦄

  2^(X+1)-1 + 2*Z = 2^(X+1+1)-1
  2*Z = 2^(X+2) - 2^(X+1)
  2*Z = 2^(X+1)
  Z = 2^X

*)
(* /SOLUTION *)
(** [] *)
(* /FULL *)

(* LATER: Another nice problem (from 09-final):

For each of the while programs below, we have provided a precondition
and postcondition. In the blank before each loop, fill in an invariant
that would allow us to annotate the rest of the program. Assume X, Y
and Z are distinct program variables.
(a)
(b)
    X := ANum n;
    Y := A1;
    while (BNot (!X === A0)) do (
         Y := !Y *** A2;
         X := !X --- A1
    )
Answer: Y = 2^(n-X)
    X := ANum x;
    Y := ANum y;
    Z := A0
{ True }
{ _______________________________________ }
{ Y = 2^n }
{ True }
                                   { _______________________________________ }
    while (BAnd (BNot (!X === A0)) (BNot (!Y === A0))) do (
         X := !X --- A1;
         Y := !Y --- A1;
         Z := !Z +++ A1
)
(where min is the mathematical "minimum" function)
Answer: Z = min(x,y) - min(X,Y)
*)
(* FULL *)
(* ####################################################### *)
(** * Weakest Preconditions (Optional) *)

(** FULL: Some preconditions are more interesting than others.
    For example,

      ⦃ False ⦄  X := Y + 1  ⦃ X <= 5 ⦄

    is _not_ very interesting: although it is perfectly valid Hoare
    triple, it tells us nothing useful.  Since the precondition isn't
    satisfied by any state, it doesn't describe any situations where
    we can use the command [X ::= Y + 1] to achieve the postcondition
    [X <= 5].

    By contrast,

      ⦃ Y <= 4 /\ Z = 0 ⦄  X := Y + 1 ⦃ X <= 5 ⦄

    has a useful precondition: it tells us that, if we can somehow
    create a situation in which we know that [Y <= 4 /\ Z = 0], then
    running this command will produce a state satisfying the
    postcondition.  However, this precondition is not as useful as it
    could be, because the [Z = 0] clause in the precondition actually
    has nothing to do with the postcondition [X <= 5].

    The most useful precondition is this one:

      ⦃ Y <= 4 ⦄  X := Y + 1  ⦃ X <= 5 ⦄

    Assertion [Y <= 4] is the _weakest precondition_ of command [X ::=
    Y + 1] for postcondition [X <= 5]. *)
(** TERSE: A useless (though valid) Hoare triple:

      ⦃ False ⦄  X := Y + 1  ⦃ X <= 5 ⦄

    A better precondition:

      ⦃ Y <= 4 /\ Z = 0 ⦄  X := Y + 1 ⦃ X <= 5 ⦄

    The _best_ precondition:

      ⦃ Y <= 4 ⦄  X := Y + 1  ⦃ X <= 5 ⦄

*)

(** Assertion [Y <= 4] is a _weakest precondition_ of command [X ::=
    Y + 1] with respect to postcondition [X <= 5].  Think of _weakest_
    here as meaning "easiest to satisfy": a weakest precondition is
    one that as many states as possible can satisfy.

    [P] is a weakest precondition of command [c] for postcondition [Q]
    if:

      - [P] is a precondition, that is, [⦃ P ⦄ c ⦃ Q ⦄]; and
      - [P] is at least as weak as all other preconditions, that is,
        if [⦃ P' ⦄ c ⦃ Q ⦄] then [P' ->> P].
 *)

(** FULL: Note that weakest preconditions need not be unique.  For
    example, [Y <= 4] was a weakest precondition above, but so are the
    logically equivalent assertions [Y < 5], [Y <= 2 * 2], etc.  *)

Definition is_wp P c Q :=
  ⦃ P ⦄ c ⦃ Q ⦄ /\
  forall P', ⦃ P' ⦄ c ⦃ Q ⦄ -> (P' ->> P).

(* LATER: Make a quiz based on this? *)
(* EX1? (wp) *)
(** What are weakest preconditions of the following commands
    for the following postconditions?

  1) ⦃ ? ⦄  skip  ⦃ X = 5 ⦄

  2) ⦃ ? ⦄  X := Y + Z ⦃ X = 5 ⦄

  3) ⦃ ? ⦄  X := Y  ⦃ X = Y ⦄

  4) ⦃ ? ⦄
     if X = 0 then Y := Z + 1 else Y := W + 2 end
     ⦃ Y = 5 ⦄

  5) ⦃ ? ⦄
     X := 5
     ⦃ X = 0 ⦄

  6) ⦃ ? ⦄
     while true do X := 0 end
     ⦃ X = 0 ⦄

*)
(* SOLUTION *)
(*
   1) X = 5
   2) Y + Z = 5
   3) True
   4) (X = 0 /\ Z = 4) \/ (X <> 0 /\ W = 3)
   5) False
   6) True
*)
(* /SOLUTION *)
(** [] *)

(* LATER: Another similar problem:

For each of the following Hoare triples, give a weakest precondition
that makes the triple valid.
(a)
    ⦃ ? ⦄
while Y <= X do
X := X - 1 end
⦃  Y > X ⦄
    ⦃ ? ⦄
if X .> 3 then Z := X else Z := Y end
⦃  Z = W ⦄
    ⦃ ? ⦄
while IsCons X do
  N := N + 1;
  X := Tail(X)
end
⦃  X = [ ] ∧ N = length l ⦄

---------
And:

In the Imp program below, we have provided a precondition and
postcondition. In the blank before the loop, fill in an invariant
that would allow us to annotate the rest of the program.
X := n
Y := X
Z := 0
while Y <> 0 do
    Z := Z + X;
Y := Y - 1 end
{ True }
{ _____________________________________________ }
{ Z = n*n }

*)

(* EX3A? (is_wp_formal) *)
(** Prove formally, using the definition of [hoare_triple], that [Y <= 4]
    is indeed a weakest precondition of [X ::= Y + 1] with respect to
    postcondition [X <= 5]. *)

Theorem is_wp_example :
  is_wp (Y <= 4) <{X := Y + 1}> (X <= 5).
(** [] *)

(* EX2A? (hoare_asgn_weakest) *)
(** Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) <{ X := a }> Q.
(* GRADE_THEOREM 2: hoare_asgn_weakest *)
(** [] *)

(* EX2A? (hoare_havoc_weakest) *)
(** Show that your [havoc_pre] function from the [himp_hoare] exercise
    in the \CHAP{Hoare} chapter returns a weakest precondition. *)

Lemma hoare_havoc_weakest : forall (P Q : Assertion) (X : string),
  ⦃ P ⦄ havoc X ⦃ Q ⦄ ->
  P ->> havoc_pre X Q.
(** [] *)

(* HIDE: Another (very) good exercise from 09-mid2 -- just needs typeset

The notion of weakest precondition has a natural dual : given a
precondition and a command, we can ask what is the strongest
postcondition of the command with respect to the
precondition. Formally, we can define it like this:

Q is the strongest postcondition of c for P if:

(a) ⦃ P ⦄ c ⦃ Q ⦄, and

(b) if Q′ is an assertion such that ⦃ P ⦄c⦃ Q′ ⦄,
    then Q st implies Q′ st, for all states st.

Q is the strongest (most difficult to satisfy) assertion that is
guaranteed to hold after c if P holds before. For example, the
strongest postcondition of the command skip with respect to the
precondition Y = 1 is Y = 1. Similarly, the postcondition in...

         ⦃ Y = y ⦄
           if !Y === A0 then X ::= A0 else Y ::= !Y *** A2
         ⦃ (Y = y = X = 0) ∨ (Y = 2*y ∧ y <> 0) ⦄

...is the strongest one.

Complete each of the following Hoare triples with the strongest
postcondition for the given command and precondition.

(a) ⦃ Y=1 ⦄ X::=!Y+++A1 ⦃ ?⦄
(b) ⦃ True ⦄ X::=A5 ⦃ ?⦄
(c) ⦃ True ⦄ skip ⦃ ? ⦄
(d) ⦃ True ⦄ while true do skip ⦃ ? ⦄
(e) ⦃ X = x ∧ Y = y ⦄
    while BNot (!X === A0) do (
                    Y ::= !Y +++ A2;;
                    X ::= !X --- A1
                  )
    ⦃ ? ⦄
*)
(* /FULL *)

(* ####################################################### *)
(** * Formal Decorated Programs (Advanced) *)

(* LATER: We might consider adding [add_slowly] someplace? *)
(** FULL: Our informal conventions for decorated programs amount to a
    way of displaying Hoare triples, in which commands are annotated
    with enough embedded assertions that checking the validity of a
    triple is reduced to simple logical and algebraic calculations
    showing that some assertions imply others.  In this section, we
    show that this presentation style can actually be made completely
    formal -- and indeed that checking the validity of decorated
    programs can mostly be automated.  *)

(** TERSE: With a little more work, we can formalize the definition of
    well-formed decorated programs and mostly automate the mechanical
    steps when filling in decorations. *)

(** ** Syntax *)

(** FULL: The first thing we need to do is to formalize a variant of the
    syntax of commands with embedded assertions.  We call the new
    commands _decorated commands_, or [dcom]s.

    The choice of exactly where to put assertions in the definition of
    [dcom] is a bit subtle.  The simplest thing to do would be to
    annotate every [dcom] with a precondition and postcondition.  But
    this would result in very verbose programs with a lot of repeated
    annotations: for example, a program like [skip;skip] would have to
    be annotated as

        ⦃ P ⦄ (⦃ P ⦄ skip ⦃ P ⦄) ; (⦃ P ⦄ skip ⦃ P ⦄) ⦃ P ⦄,

    with pre- and post-conditions on each [skip], plus identical pre-
    and post-conditions on the semicolon!

    We don't want both preconditions and postconditions on each
    command, because a sequence of two commands would contain
    redundant decorations--the postcondition of the first likely being
    the same as the precondition of the second.

    Instead, we'll omit preconditions whenever possible, trying to
    embed just the postcondition. *)

(** TERSE: _Decorated commands_ contain assertions mostly just as
    postconditions, omitting preconditions where possible and letting
    the context supply them.

    The alternative--decorating every command with both a pre- and
    postcondition--would be too heavyweight. E.g., [skip; skip] would
    become:

        ⦃ P ⦄ (⦃ P ⦄ skip ⦃ P ⦄) ; (⦃ P ⦄ skip ⦃ P ⦄) ⦃ P ⦄,

*)

(** Specifically, we decorate as follows:

    - Command [skip] is decorated only with its postcondition, as
      [skip ⦃ Q  ⦄].

    - Sequence [d1 ;; d2] contains no additional decoration.  Inside
      [d2] there will be a postcondition; that serves as the
      postcondition of [d1 ;; d2].  Inside [d1] there will also be a
      postcondition; it additionally serves as the precondition for
      [d2].

    - Assignment [X ::= a] is decorated only with its postcondition,
      as [X ::= a ⦃ Q  ⦄].

    - If statement [if b then d1 else d2] is decorated with a
      postcondition for the entire statement, as well as preconditions
      for each branch, as
      [if b then ⦃ P1 ⦄ d1 else ⦃ P2 ⦄ d2 end ⦃ Q  ⦄].

    - While loop [while b do d end] is decorated with its
      postcondition and a precondition for the body, as
      [while b do ⦃ P ⦄ d end ⦃ Q  ⦄].  The postcondition inside
      [d] serves as the loop invariant.

    - Implications [->>] are added as decorations for a precondition
      as [->> ⦃ P ⦄ d], or for a postcondition as [d ->> ⦃ Q  ⦄].
      The former is waiting for another precondition to eventually be
      supplied, e.g., [⦃  P' ⦄ ->> ⦃ P ⦄ d], and the latter relies
      on the postcondition already embedded in [d].
*)

Inductive dcom : Type :=
| DCSkip (Q : Assertion)
  (* skip ⦃ Q ⦄ *)
| DCSeq (d1 d2 : dcom)
  (* d1 ;; d2 *)
| DCAsgn (X : string) (a : aexp) (Q : Assertion)
  (* X := a ⦃ Q ⦄ *)
| DCIf (b : bexp) (P1 : Assertion) (d1 : dcom)
       (P2 : Assertion) (d2 : dcom) (Q : Assertion)
  (* if b then ⦃ P1 ⦄ d1 else ⦃ P2 ⦄ d2 end ⦃ Q ⦄ *)
| DCWhile (b : bexp) (P : Assertion) (d : dcom) (Q : Assertion)
  (* while b do ⦃ P ⦄ d end ⦃ Q ⦄ *)
| DCPre (P : Assertion) (d : dcom)
  (* ->> ⦃ P ⦄ d *)
| DCPost (d : dcom) (Q : Assertion)
  (* d ->> ⦃ Q ⦄ *)
.

(** [DCPre] is used to provide the weakened precondition from
    the rule of consequence. To provide the initial precondition
    at the very top of the program, we use [Decorated]: *)

Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.

(** TERSE: *** *)

(** To avoid clashing with the existing [Notation] definitions for
    ordinary [com]mands, we introduce these notations in a custom entry
    notation called [dcom]. *)

(* FOLD *)
Declare Scope dcom_scope.
(* INSTRUCTORS: Definition of template dcom *)
Notation "'skip' ⦃ P  ⦄"
      := (DCSkip P)
      (in custom com at level 0, P constr) : dcom_scope.
Notation "l ':=' a ⦃ P  ⦄"
      := (DCAsgn l a P)
      (in custom com at level 0, l constr at level 0,
          a custom com at level 85, P constr, no associativity) : dcom_scope.
Notation "'while' b 'do' ⦃ Pbody ⦄ d 'end' ⦃ Ppost  ⦄"
      := (DCWhile b Pbody d Ppost)
           (in custom com at level 89, b custom com at level 99,
           Pbody constr, Ppost constr) : dcom_scope.
Notation "'if' b 'then' ⦃ P ⦄ d 'else' ⦃ P' ⦄ d' 'end' ⦃ Q  ⦄"
      := (DCIf b P d P' d' Q)
           (in custom com at level 89, b custom com at level 99,
               P constr, P' constr, Q constr) : dcom_scope.
Notation "'->>' ⦃ P ⦄ d"
      := (DCPre P d)
      (in custom com at level 12, right associativity, P constr) : dcom_scope.
Notation "d '->>' ⦃ P  ⦄"
      := (DCPost d P)
      (in custom com at level 10, right associativity, P constr) : dcom_scope.
Notation " d ; d' "
      := (DCSeq d d')
      (in custom com at level 90, right associativity) : dcom_scope.
Notation "⦃  P ⦄ d"
      := (Decorated P d)
      (in custom com at level 91, P constr) : dcom_scope.

Open Scope dcom_scope.

Example dec0 :=
  <{ skip ⦃ True ⦄ }>.
Example dec1 :=
  <{ while true do ⦃ True ⦄ skip ⦃ True ⦄ end
  ⦃ True ⦄ }>.

(* /FOLD *)

(* FULL *)
(** Recall that you can [Set Printing All] to see how all that
    notation is desugared. *)
Set Printing All.
Print dec1.
Unset Printing All.
(* /FULL *)

(** An example [decorated] program that decrements [X] to [0]: *)

Example dec_while : decorated :=
  <{
  ⦃ True ⦄
  while ~(X = 0)
  do
    ⦃ True /\ (X <> 0) ⦄
    X := X - 1
    ⦃ True ⦄
  end
  ⦃ True /\  X = 0 ⦄ ->>
  ⦃ X = 0 ⦄ }>.

(** TERSE: *** *)

(** It is easy to go from a [dcom] to a [com] by erasing all
    annotations. *)

Fixpoint extract (d : dcom) : com :=
  match d with
  | DCSkip _           => CSkip
  | DCSeq d1 d2        => CSeq (extract d1) (extract d2)
  | DCAsgn X a _       => CAss X a
  | DCIf b _ d1 _ d2 _ => CIf b (extract d1) (extract d2)
  | DCWhile b _ d _    => CWhile b (extract d)
  | DCPre _ d          => extract d
  | DCPost d _         => extract d
  end.

Definition extract_dec (dec : decorated) : com :=
  match dec with
  | Decorated P d => extract d
  end.

(** TERSE: *** *)

(* INSTRUCTORS: the [unfold] isn't needed, but it lets us recall
   what [dec_while] is without having to print it. *)
Example extract_while_ex :
  extract_dec dec_while = <{while ~ X = 0 do X := X - 1 end}>.
Proof.
  unfold dec_while.
  reflexivity.
Qed.

(** TERSE: *** *)

(** It is straightforward to extract the precondition and
    postcondition from a decorated program. *)

Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip P                => P
  | DCSeq d1 d2             => post d2
  | DCAsgn X a Q            => Q
  | DCIf  _ _ d1 _ d2 Q     => Q
  | DCWhile b Pbody c Ppost => Ppost
  | DCPre _ d               => post d
  | DCPost c Q              => Q
  end.

Definition pre_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => P
  end.

Definition post_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => post d
  end.

(** TERSE: *** *)

Example pre_dec_while : pre_dec dec_while = True.
Proof. reflexivity. Qed.

Example post_dec_while : post_dec dec_while = (X = 0)%assertion.
Proof. reflexivity. Qed.

(** TERSE: *** *)

(** FULL: We can express what it means for a decorated program to be
    correct as follows: *)

(** TERSE: When is a decorated program correct? *)

Definition dec_correct (dec : decorated) :=
  ⦃ pre_dec dec ⦄ extract_dec dec ⦃ post_dec dec ⦄.

Example dec_while_triple_correct :
  dec_correct dec_while
 = ⦃ True ⦄
   while ~(X = 0) do X := X - 1 end
   ⦃ X = 0  ⦄.
Proof. reflexivity. Qed.

(** To check whether this Hoare triple is _valid_, we need a way to
    extract the "proof obligations" from a decorated program. These
    obligations are often called _verification conditions_, because
    they are the facts that must be verified to see that the
    decorations are logically consistent and thus constitute a proof
    of correctness. *)

(** ** Extracting Verification Conditions *)

(** The function [verification_conditions] takes a [dcom] [d] together
    with a precondition [P] and returns a _proposition_ that, if it
    can be proved, implies that the triple [⦃ P ⦄ (extract d) ⦃ post d ⦄]
    is valid. It does this by walking over [d] and generating a big
    conjunction that includes

    - all the local consistency checks, plus

    - many uses of [->>] to bridge the gap between (i) assertions
      found inside decorated commands and (ii) assertions used by the
      local consistency checks.  These uses correspond applications of
      the consequence rule. *)

(* HIDE: There was some discussion in 2016 about whether the VC
   generator should should use equivalence or implication in a few
   places.  I (BCP) believe Phil (Wadler) changed some instances of
   the former to the latter. *)
(* LATER: We need all the "unwrapping" and "rewrapping" of assertions
   here because we haven't lifted /\ to assertions!  Would this be a
   good idea, or would it make things harder to understand?  If we do
   it here, we should do it right at the beginning and use it all the
   way through!  (BCP 12/16: I think lifting it, everywhere, is a good
   idea!) (BCP 10/18: No longer convinced... See comments in Hoare.v)
   (APT: well, in this version, we're doing it! *)
(* LATER: MRC'20: a written explanation of each part of this would
   be quite nice. *)
Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSkip Q =>
      (P ->> Q)
  | DCSeq d1 d2 =>
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q =>
      (P ->> Q [X |-> a])
  | DCIf b P1 d1 P2 d2 Q =>
      ((P /\ b) ->> P1)%assertion
      /\ ((P /\ ~ b) ->> P2)%assertion
      /\ (post d1 ->> Q) /\ (post d2 ->> Q)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Pbody d Ppost =>
      (* post d is the loop invariant and the initial
         precondition *)
      (P ->> post d)
      /\ ((post d  /\ b) ->> Pbody)%assertion
      /\ ((post d  /\ ~ b) ->> Ppost)%assertion
      /\ verification_conditions Pbody d
  | DCPre P' d =>
      (P ->> P') /\ verification_conditions P' d
  | DCPost d Q =>
      verification_conditions P d /\ (post d ->> Q)
  end.

(** TERSE: *** *)

(** And now the key theorem, stating that [verification_conditions]
    does its job correctly.  Not surprisingly, we need to use each of
    the Hoare Logic rules at some point in the proof. *)

Theorem verification_correct : forall d P,
  verification_conditions P d -> ⦃ P ⦄ extract d ⦃ post d ⦄.
(* FOLD *)
Proof.
  induction d; intros; simpl in *.
  - (* Skip *)
    eapply hoare_consequence_pre.
      + apply hoare_skip.
      + assumption.
  - (* Seq *)
    destruct H as [H1 H2].
    eapply hoare_seq.
      + apply IHd2. apply H2.
      + apply IHd1. apply H1.
  - (* Asgn *)
    eapply hoare_consequence_pre.
      + apply hoare_asgn.
      + assumption.
  - (* If *)
    destruct H as [HPre1 [HPre2 [Hd1 [Hd2 [HThen HElse] ] ] ] ].
    apply IHd1 in HThen. clear IHd1.
    apply IHd2 in HElse. clear IHd2.
    apply hoare_if.
      + eapply hoare_consequence; eauto.
      + eapply hoare_consequence; eauto.
  - (* While *)
    destruct H as [Hpre [Hbody1 [Hpost1  Hd] ] ].
    eapply hoare_consequence; eauto.
    apply hoare_while.
    eapply hoare_consequence_pre; eauto.
  - (* Pre *)
    destruct H as [HP Hd].
    eapply hoare_consequence_pre; eauto.
  - (* Post *)
    destruct H as [Hd HQ].
    eapply hoare_consequence_post; eauto.
Qed.
(* /FOLD *)

(* HIDE: The reverse implication of the theorem above doesn't
   hold. *)

(** Now that all the pieces are in place, we can verify an entire program. *)

Definition verification_conditions_dec (dec : decorated) : Prop :=
  match dec with
  | Decorated P d => verification_conditions P d
  end.

Corollary verification_correct_dec : forall dec,
  verification_conditions_dec dec -> dec_correct dec.
Proof.
  intros [P d]. apply verification_correct.
Qed.

(** TERSE: *** *)
(** The propositions generated by [verification_conditions] are fairly
    big, and they contain many conjuncts that are essentially trivial.
    Our [verify_assn] can often take care of them. *)

(* HIDE: MRC'20: The conditions here used to be just [Eval]ed instead of
   and duplicated in a comment.  They were actually incorrect because of
   changes to notation.  Putting them in as an [Example] will force
   us to keep them up-to-date. *)
Example vc_dec_while :
  verification_conditions_dec dec_while =
    ((((fun _ : state => True) ->> (fun _ : state => True)) /\
    ((fun st : state => True /\ negb (st X =? 0) = true) ->>
     (fun st : state => True /\ st X <> 0)) /\
    ((fun st : state => True /\ negb (st X =? 0) <> true) ->>
     (fun st : state => True /\ st X = 0)) /\
    (fun st : state => True /\ st X <> 0) ->> (fun _ : state => True) [X |-> X - 1]) /\
   (fun st : state => True /\ st X = 0) ->> (fun st : state => st X = 0)).
Proof. verify_assn. Qed.

(** ** Automation *)

(** To automate the entire process of verification, we can use
    [verification_correct] to extract the verification conditions,
    then use [verify_assn] to verify them (if it can).  *)
Ltac verify :=
  intros;
  apply verification_correct;
  verify_assn.

Theorem Dec_while_correct :
  dec_correct dec_while.
Proof. verify. Qed.

(** Let's use that automation to verify formal decorated programs
    corresponding to informal ones we have seen. *)

(** *** Slow Subtraction *)

Example subtract_slowly_dec (m : nat) (p : nat) : decorated :=
  <{
    ⦃ X = m /\  Z = p ⦄ ->>
    ⦃ Z - X = p - m ⦄
  while ~(X = 0)
  do   ⦃ Z - X = p - m /\ X  <>  0 ⦄ ->>
       ⦃ (Z - 1) - (X - 1) = p - m ⦄
     Z := Z - 1
       ⦃ Z - (X - 1) = p - m ⦄ ;
     X := X - 1
       ⦃ Z - X = p - m ⦄
  end
    ⦃ Z - X = p - m /\ X = 0 ⦄ ->>
    ⦃ Z = p - m ⦄ }>.

Theorem subtract_slowly_dec_correct : forall m p,
  dec_correct (subtract_slowly_dec m p).
Proof. verify. (* this grinds for a bit! *) Qed.

(** *** Swapping Using Addition and Subtraction *)

(* Definition swap : com := *)
(*   <{ X := X + Y; *)
(*      Y := X - Y; *)
(*      X := X - Y }>. *)

Definition swap_dec (m n:nat) : decorated :=
  <{
   ⦃ X = m /\ Y = n ⦄ ->>
   ⦃ (X + Y) - ((X + Y) - Y) = n
                /\ (X + Y) - Y = m ⦄
  X := X + Y
   ⦃ X - (X - Y) = n /\ X - Y = m  ⦄;
  Y := X - Y
   ⦃ X - Y = n /\ Y = m  ⦄;
  X := X - Y
   ⦃ X = n /\ Y = m ⦄ }>.

Theorem swap_correct : forall m n,
  dec_correct (swap_dec m n).
Proof. verify.   Qed.

(* SOONER: MRC hid some proofs here so as not to spoil earlier exercises.
   Consider the pros and cons of this. *)
(* HIDE *)
(* spoils an earlier exercise *)

(** *** Simple Conditionals *)

(* SOONER: Is this needed? *)
Definition if_minus_plus_com : com :=
  <{ if (X <= Y)
       then Z := Y - X
       else Y := X + Z
     end }>.

Definition if_minus_plus_dec :=
  <{
  ⦃ True⦄
  if (X <= Y) then
      ⦃ True /\ X <= Y ⦄ ->>
      ⦃ Y = X + (Y - X) ⦄
    Z := Y - X
      ⦃ Y = X + Z ⦄
  else
      ⦃ True /\ ~(X <= Y) ⦄ ->>
      ⦃ X + Z = X + Z ⦄
    Y := X + Z
      ⦃ Y = X + Z ⦄
  end
  ⦃ Y = X + Z ⦄ }>.

Theorem if_minus_plus_correct :
  dec_correct if_minus_plus_dec.
Proof. verify. Qed.

(** TERSE: *** *)
Definition if_minus_dec :=
  <{
  ⦃ True⦄
  if (X <= Y) then
      ⦃ True /\ X <= Y ⦄ ->>
      ⦃ (Y - X) + X = Y
               \/ (Y - X) + Y = X⦄
    Z := Y - X
      ⦃ Z + X = Y \/ Z + Y = X⦄
  else
      ⦃ True /\ ~(X <= Y) ⦄ ->>
      ⦃ (X - Y) + X = Y
               \/ (X - Y) + Y = X⦄
    Z := X - Y
      ⦃ Z + X = Y \/ Z + Y = X⦄
  end
    ⦃ Z + X = Y \/ Z + Y = X ⦄ }>.

Theorem if_minus_correct :
  dec_correct if_minus_dec.
Proof. verify. Qed.

(* /HIDE *)

(** TERSE: *** *)
(** TERSE: See the full version of the chapter for the rest... *)
(* FULL *)
(** *** Division *)

Definition div_mod_dec (a b : nat) : decorated :=
  <{
  ⦃ True ⦄ ->>
  ⦃ b * 0 + a = a ⦄
  X := a
  ⦃ b * 0 + X = a  ⦄;
  Y := 0
  ⦃ b * Y + X = a  ⦄;
  while b <= X do
    ⦃ b * Y + X = a /\ b <= X ⦄ ->>
    ⦃ b * (Y + 1) + (X - b) = a ⦄
    X := X - b
    ⦃ b * (Y + 1) + X = a  ⦄;
    Y := Y + 1
    ⦃ b * Y + X = a ⦄
  end
  ⦃ b * Y + X = a /\ ~(b <= X) ⦄ ->>
  ⦃ b * Y + X = a /\ (X < b) ⦄ }>.

Theorem div_mod_dec_correct : forall a b,
  dec_correct (div_mod_dec a b).
Proof.
  verify.
Qed.


(** *** Parity *)

Definition find_parity : com :=
  <{ while 2 <= X do
       X := X - 2
     end }>.

(** There are actually several ways to phrase the loop invariant for
    this program.  Here is one natural one, which leads to a rather
    long proof: *)

(* LATER: This might be better phrased in terms of the boolean
   evenness test from the standard library... *)
Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n : nat, ev n -> ev (S (S n)).

Definition find_parity_dec (m:nat) : decorated :=
  <{
   ⦃ X = m ⦄ ->>
   ⦃ X <= m /\ ap ev (m - X) ⦄
  while 2 <= X do
     ⦃ (X <= m /\ ap ev (m - X)) /\ 2 <= X ⦄ ->>
     ⦃ X - 2 <= m /\ ap ev (m - (X - 2)) ⦄
     X := X - 2
     ⦃ X <= m /\ ap ev (m - X) ⦄
  end
   ⦃ (X <= m /\ ap ev (m - X)) /\ X < 2 ⦄ ->>
   ⦃  X = 0 <-> ev m ⦄ }>.

Lemma l1 : forall m n p,
  p <= n ->
  n <= m ->
  m - (n - p) = m - n + p.
Proof. intros. lia. Qed.

Lemma l2 : forall m,
  ev m ->
  ev (m + 2).
Proof. intros. rewrite plus_comm. simpl. constructor. assumption. Qed.

Lemma l3' : forall m,
  ev m ->
  ~ev (S m).
Proof. induction m; intros H1 H2. inversion H2. apply IHm.
       inversion H2; subst; assumption. assumption. Qed.

Lemma l3 : forall m,
  1 <= m ->
  ev m ->
  ev (m - 1) ->
  False.
Proof. intros. apply l2 in H1.
       assert (G : m - 1 + 2 = S m). clear H0 H1. lia.
       rewrite G in H1. apply l3' in H0. apply H0. assumption. Qed.

Theorem find_parity_correct : forall m,
  dec_correct (find_parity_dec m).
Proof.
  verify;
    (* simplification too aggressive ... reverting a bit *)
    fold (2 <=? (st X)) in *;
    try rewrite leb_iff in *;
    try rewrite leb_iff_conv in *; eauto; try lia.
  - (* invariant holds initially *)
    rewrite minus_diag. constructor.
  - (* invariant preserved *)
    rewrite l1; try assumption.
    apply l2; assumption.
  - (* invariant strong enough to imply conclusion
         (-> direction) *)
    rewrite <- minus_n_O in H2. assumption.
  - (* invariant strong enough to imply conclusion
         (<- direction) *)
    destruct (st X) as [| [| n] ].
    (* by H1 X can only be 0 or 1 *)
    + (* st X = 0 *)
      reflexivity.
    + (* st X = 1 *)
      apply l3 in H; try assumption. inversion H.
    + (* st X = 2 *)
      lia.
Qed.

(** Here is a more intuitive way of writing the invariant: *)

Definition find_parity_dec' (m:nat) : decorated :=
  <{
  ⦃ X = m ⦄ ->>
  ⦃ ap ev X <-> ev m ⦄
 while 2 <= X do
    ⦃ (ap ev X <-> ev m) /\ 2 <= X ⦄ ->>
    ⦃ ap ev (X - 2) <-> ev m ⦄
    X := X - 2
    ⦃ ap ev X <-> ev m ⦄
 end
 ⦃ (ap ev X <-> ev m) /\ ~(2 <= X) ⦄ ->>
 ⦃  X=0 <-> ev m ⦄ }>.

Lemma l4 : forall m,
  2 <= m ->
  (ev (m - 2) <-> ev m).
Proof.
  induction m; intros. split; intro; constructor.
  destruct m. inversion H. inversion H1. simpl in *.
  rewrite <- minus_n_O in *. split; intro.
    constructor. assumption.
    inversion H0. assumption.
Qed.

Theorem find_parity_correct' : forall m,
  dec_correct (find_parity_dec' m).
Proof.
  verify;
    (* simplification too aggressive ... reverting a bit *)
    fold (2 <=? (st X)) in *;
    try rewrite leb_iff in *;
    try rewrite leb_iff_conv in *; intuition; eauto; try lia.
  - (* invariant preserved (part 1) *)
    rewrite l4 in H0; eauto.
  - (* invariant preserved (part 2) *)
    rewrite l4; eauto.
  - (* invariant strong enough to imply conclusion
       (-> direction) *)
    apply H0. constructor.
  - (* invariant strong enough to imply conclusion
       (<- direction) *)
      destruct (st X) as [| [| n] ]. (* by H1 X can only be 0 or 1 *)
      + (* st X = 0 *)
        reflexivity.
      + (* st X = 1 *)
        inversion H.
      + (* st X = 2 *)
        lia.
Qed.

(* HIDE *)
(* spoils an earlier exercise *)

(** Here is the simplest invariant we've found for this program: *)

Definition parity_dec (m:nat) : decorated :=
  <{
  ⦃ X = m ⦄ ->>
  ⦃ ap parity X = parity m ⦄
 while 2 <= X do
    ⦃ ap parity X = parity m /\ 2 <= X ⦄ ->>
    ⦃ ap parity (X - 2) = parity m ⦄
    X := X - 2
    ⦃ ap parity X = parity m ⦄
 end
 ⦃ ap parity X = parity m /\ ~(2 <= X) ⦄ ->>
 ⦃ X = parity m ⦄ }>.

Theorem parity_dec_correct : forall m,
  dec_correct (parity_dec m).
Proof.
  verify;
    (* simplification too aggressive ... reverting a bit *)
    fold (2 <=? (st X)) in *;
    try rewrite leb_iff in *;
    try rewrite leb_iff_conv in *; eauto; try lia.
  - (* invariant preserved *)
    rewrite <- H. apply parity_ge_2. assumption.
  - (* invariant strong enough *)
    rewrite <- H. symmetry. apply parity_lt_2. assumption.
Qed.

(* /HIDE *)

(** *** Square Roots *)

Definition sqrt_dec (m:nat) : decorated :=
  <{
    ⦃ X = m ⦄ ->>
    ⦃ X = m /\ 0*0 <= m ⦄
  Z := 0
    ⦃ X = m /\ Z*Z <= m  ⦄;
  while ((Z+1)*(Z+1) <= X) do
      ⦃ (X = m /\ Z*Z<=m)
                   /\ (Z + 1)*(Z + 1) <= X ⦄ ->>
      ⦃ X = m /\ (Z+1)*(Z+1)<=m ⦄
    Z := Z + 1
      ⦃ X = m /\ Z*Z<=m ⦄
  end
    ⦃ (X = m /\ Z*Z<=m)
                   /\ ~((Z + 1)*(Z + 1) <= X) ⦄ ->>
    ⦃ Z*Z<=m /\ m<(Z+1)*(Z+1) ⦄ }>.

Theorem sqrt_correct : forall m,
  dec_correct (sqrt_dec m).
Proof. verify. Qed.

(** *** Squaring *)

(** Again, there are several ways of annotating the squaring program.
    The simplest variant we've found, [square_simpler_dec], is given
    last. *)

Definition square_dec (m : nat) : decorated :=
  <{
  ⦃ X = m ⦄
  Y := X
  ⦃ X = m /\ Y = m  ⦄;
  Z := 0
  ⦃ X = m /\ Y = m /\ Z = 0 ⦄ ->>
  ⦃ Z + X * Y = m * m  ⦄;
  while ~(Y = 0) do
    ⦃ Z + X * Y = m * m /\ Y <> 0 ⦄ ->>
    ⦃ (Z + X) + X * (Y - 1) = m * m ⦄
    Z := Z + X
    ⦃ Z + X * (Y - 1) = m * m  ⦄;
    Y := Y - 1
    ⦃ Z + X * Y = m * m ⦄
  end
  ⦃ Z + X * Y = m * m /\ Y = 0 ⦄ ->>
  ⦃ Z = m * m ⦄ }>.

Theorem square_dec_correct : forall m,
  dec_correct (square_dec m).
Proof.
  verify.
  - (* invariant preserved *)
    destruct (st Y) as [| y'].
    + exfalso. auto.
    + simpl. rewrite <- minus_n_O.
    assert (G : forall n m, n * S m = n + n * m). {
      clear. intros. induction n. reflexivity. simpl.
      rewrite IHn. lia. }
    rewrite <- H. rewrite G. lia.
Qed.

Definition square_dec' (n : nat) : decorated :=
  <{
  ⦃ True ⦄
  X := n
  ⦃ X = n  ⦄;
  Y := X
  ⦃ X = n /\ Y = n  ⦄;
  Z := 0
  ⦃ X = n /\ Y = n /\ Z = 0 ⦄ ->>
  ⦃ Z = X * (X - Y)
               /\ X = n /\ Y <= X  ⦄;
  while ~(Y = 0) do
    ⦃ (Z = X * (X - Y)
                /\ X = n /\ Y <= X)
                /\  Y <> 0 ⦄
    Z := Z + X
    ⦃ Z = X * (X - (Y - 1))
                 /\ X = n /\ Y <= X  ⦄;
    Y := Y - 1
    ⦃ Z = X * (X - Y)
                 /\ X = n /\ Y <= X ⦄
  end
  ⦃ (Z = X * (X - Y)
              /\ X = n /\ Y <= X)
               /\ Y = 0 ⦄ ->>
  ⦃ Z = n * n ⦄ }>.

Theorem square_dec'_correct : forall (n:nat),
  dec_correct (square_dec' n).
Proof.
  verify.
  (* invariant holds initially, proven by verify  *)
  (* invariant preserved *) subst.
  rewrite mult_minus_distr_l.
  repeat rewrite mult_minus_distr_l. rewrite mult_1_r.
  assert (G : forall n m p,
             m <= n -> p <= m -> n - (m - p) = n - m + p).
  intros. lia.
  rewrite G. reflexivity. apply mult_le_compat_l. assumption.
  destruct (st Y).
  - exfalso. auto.
  - lia.
  (* invariant + negation of guard imply
       desired postcondition proven by [verify] *)
Qed.

Definition square_simpler_dec (m : nat) : decorated :=
  <{
  ⦃ X = m ⦄ ->>
  ⦃ 0 = 0*m /\ X = m ⦄
  Y := 0
  ⦃ 0 = Y*m /\ X = m  ⦄;
  Z := 0
  ⦃ Z = Y*m /\ X = m  ⦄;
  while ~(Y = X) do
    ⦃ (Z = Y*m /\ X = m)
        /\ Y <> X ⦄ ->>
    ⦃ Z + X = (Y + 1)*m /\ X = m ⦄
    Z := Z + X
    ⦃ Z = (Y + 1)*m /\ X = m  ⦄;
    Y := Y + 1
    ⦃ Z = Y*m /\ X = m ⦄
  end
  ⦃ (Z = Y*m /\ X = m) /\ Y = X ⦄ ->>
  ⦃ Z = m*m ⦄ }>.

Theorem square_simpler_dec_correct : forall m,
  dec_correct (square_simpler_dec m).
Proof.
  verify.
Qed.

(* HIDE *)
(* spoils an earlier exercise *)

(** *** Two loops *)

Definition two_loops_dec (a b c : nat) : decorated :=
  <{
  ⦃ True ⦄ ->>
  ⦃ c = 0 + c /\ 0 = 0 ⦄
  X := 0
  ⦃ c = X + c /\ 0 = 0  ⦄;
  Y := 0
  ⦃ c = X + c /\ Y = 0  ⦄;
  Z := c
  ⦃ Z = X + c /\ Y = 0  ⦄;
  while ~(X = a) do
    ⦃ (Z = X + c /\ Y = 0) /\ X <> a ⦄ ->>
    ⦃  Z + 1 = X + 1 + c /\ Y = 0 ⦄
    X := X + 1
    ⦃ Z + 1 = X + c /\ Y = 0  ⦄;
    Z := Z + 1
    ⦃ Z = X + c /\ Y = 0 ⦄
  end
  ⦃ (Z = X + c /\ Y = 0) /\ X = a ⦄ ->>
  ⦃ Z = a + Y + c  ⦄;
  while ~(Y = b) do
    ⦃ Z = a + Y + c /\ Y <> b ⦄ ->>
    ⦃ Z + 1 = a + Y + 1 + c ⦄
    Y := Y + 1
    ⦃ Z + 1 = a + Y + c  ⦄;
    Z := Z + 1
    ⦃ Z = a + Y + c ⦄
  end
  ⦃ Z = a + Y + c /\ Y = b ⦄ ->>
  ⦃ Z = a + b + c ⦄ }>.

Theorem two_loops_correct : forall a b c,
  dec_correct (two_loops_dec a b c).
Proof. verify. Qed.

(* /HIDE *)

(** *** Power Series *)

Fixpoint pow2 n :=
  match n with
  | 0 => 1
  | S n' => 2 * (pow2 n')
  end.

Definition dpow2_down (n : nat) :=
  <{
  ⦃ True ⦄ ->>
  ⦃ 1 = (pow2 (0 + 1))-1 /\ 1 = pow2 0 ⦄
  X := 0
  ⦃ 1 = (pow2 (0 + 1))-1 /\ 1 = ap pow2 X  ⦄;
  Y := 1
  ⦃ Y = (ap pow2 (X + 1))-1 /\ 1 = ap pow2 X ⦄;
  Z := 1
  ⦃ Y = (ap pow2 (X + 1))-1 /\ Z = ap pow2 X  ⦄;
  while ~(X = n) do
    ⦃ (Y = (ap pow2 (X + 1))-1 /\ Z = ap pow2 X)
                 /\ X <> n ⦄ ->>
    ⦃ Y + 2 * Z = (ap pow2 (X + 2))-1
                 /\ 2 * Z = ap pow2 (X + 1) ⦄
    Z := 2 * Z
    ⦃ Y + Z = (ap pow2 (X + 2))-1
                 /\ Z = ap pow2 (X + 1)  ⦄;
    Y := Y + Z
    ⦃ Y = (ap pow2 (X + 2))-1
                 /\ Z = ap pow2 (X + 1)  ⦄;
    X := X + 1
    ⦃ Y = (ap pow2 (X + 1))-1
                 /\ Z = ap pow2 X ⦄
  end
  ⦃ (Y = (ap pow2 (X + 1))-1 /\ Z = ap pow2 X)
               /\ X = n ⦄ ->>
  ⦃ Y = pow2 (n+1) - 1 ⦄ }>.

Lemma pow2_plus_1 : forall n,
  pow2 (n+1) = pow2 n + pow2 n.
Proof. induction n; simpl. reflexivity. lia. Qed.

Lemma pow2_le_1 : forall n, pow2 n >= 1.
Proof. induction n. simpl. constructor. simpl. lia. Qed.

Theorem dpow2_down_correct : forall n,
  dec_correct (dpow2_down n).
Proof.
  intros m. verify.
  - (* 1 *)
    rewrite pow2_plus_1. rewrite <- H0. reflexivity.
  - (* 2 *)
    rewrite <- plus_n_O.
    rewrite <- pow2_plus_1. remember (st X) as x.
    replace (pow2 (x + 1) - 1 + pow2 (x + 1))
       with (pow2 (x + 1) + pow2 (x + 1) - 1) by lia.
    rewrite <- pow2_plus_1.
    replace (x + 1 + 1) with (x + 2) by lia.
    reflexivity.
  - (* 3 *)
    rewrite <- plus_n_O. rewrite <- pow2_plus_1.
    reflexivity.
  - (* 4 *)
    replace (st X + 1 + 1) with (st X + 2) by lia.
    reflexivity.
Qed.

(** ** Further Exercises *)

(* EX3A (slow_assignment_dec) *)
(** Transform the informal decorated program your wrote for
    [slow_assignment] into a formal decorated program.  If all goes
    well, the only change you will need to make is to move semicolons,
    which go after the postcondition of an assignment in a formal
    decorated program.  For example,


    ⦃ X = m /\ 0 = 0 ⦄
  Y := 0;
    ⦃ X = m /\ Y = 0 ⦄

becomes

    ⦃ X = m /\ 0 = 0 ⦄
  Y ::= 0
    ⦃ X = m /\ Y = 0 ⦄ ;;

*)

Example slow_assignment_dec (m : nat) : decorated

(** Now prove the correctness of your decorated program.  If all goes well,
    you will need only [verify]. *)

Theorem slow_assignment_dec_correct : forall m,
  dec_correct (slow_assignment_dec m).

(* GRADE_MANUAL 1: check_defn_of_slow_assignment_dec *)
(* GRADE_THEOREM 2: slow_assignment_dec_correct *)
(** [] *)

(* EX4AM (factorial_dec)  *)
(** The factorial function is defined recursively in the Coq standard
    library in a way that is equivalent to the following:


Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (fact n')
  end.

     *)

Compute fact 5. (* ==> 120 *)

(** Using your solutions to [factorial] and [slow_assignment_dec] as a
    guide, write a formal decorated program [factorial_dec] that
    implements the factorial function.  Hint: recall the use of [ap]
    in assertions to apply a function to an Imp variable.

    Then state a theorem named [factorial_dec_correct] that says
    [factorial_dec] is correct, and prove the theorem.  If all goes
    well, [verify] will leave you with just two subgoals, each of
    which requires establishing some mathematical property of [fact],
    rather than proving anything about your program.

    Hint: if those two subgoals become tedious to prove, give some
    though to how you could restate your assertions such that the
    mathematical operations are more amenable to manipulation in Coq.
    For example, recall that [1 + ...] is easier to work with than
    [... + 1]. *)

(* SOLUTION *)
Example factorial_dec (m:nat) : decorated :=
  <{
    ⦃ X = m ⦄ ->>
    ⦃ 1 * ap fact X = fact m ⦄
  Y := 1
    ⦃ Y * ap fact X = fact m  ⦄;
  while ~(X = 0)
  do   ⦃ Y * ap fact X = fact m /\ X <> 0 ⦄
     Y := Y * X
       ⦃ Y * ap fact (X - 1) = fact m ⦄ ;
     X := X - 1
       ⦃ Y * ap fact X = fact m ⦄
  end
    ⦃ Y * ap fact X = fact m /\ X = 0 ⦄
    ->>
    ⦃ Y = fact m ⦄ }>.

Lemma fact_sub1 : forall m,
  m<>0 -> m * fact (m-1) = fact m.
Proof.
  intros. destruct m.
  - contradiction.
  - simpl. rewrite <- minus_n_O. reflexivity.
Qed.

Theorem factorial_dec_correct : forall m,
  dec_correct (factorial_dec m).
Proof.
  verify.
  - rewrite <- mult_assoc. rewrite -> fact_sub1; assumption.
  - simpl in *. lia.
Qed.
(* /SOLUTION *)

(* GRADE_MANUAL 6: factorial_dec *)
(** [] *)
(* NOTATION: SOONER: BCP: Can we fix the inconsistency about where the semicolon
   goes?  I guess we have to fix it in Hoare.v... *)
(* SOONER: CH: Hints on how to transform informal decorated
    programs into formal ones:

    Hint #1: We are a less picky about the syntax of formal
    decorations (as long as things are logically equivalent), since we
    found out that being too picky on syntax causes unnecessary
    pain. Still, please try to stick with the way of decorating
    proposed in the informal decorated programs section, since that
    will render your decorations more readable.

    Hint #2: We don't strictly enforce that the uses of the
    consequence rule are made explicit for premises; but we still
    encourage you to make all uses of consequence explicit in order to
    increase readability. *)

(* EX2A? (fib_eqn) *)
(** The Fibonacci function is usually written like this:

      Fixpoint fib n :=
        match n with
        | 0 => 1
        | 1 => 1
        | _ => fib (pred n) + fib (pred (pred n))
        end.

   This doesn't pass Coq's termination checker, but here is a
   slightly clunkier definition that does: *)

Fixpoint fib n :=
  match n with
  | 0 => 1
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib n' + fib n''
            end
  end.

(** Prove that [fib] satisfies the following equation.  You will need this
    as a lemma in the next exercise. *)

Lemma fib_eqn : forall n,
  n > 0 ->
  fib n + fib (pred n) = fib (1 + n).
(** [] *)

(* EX4A? (fib) *)
(** The following Imp program leaves the value of [fib n] in the
    variable [Y] when it terminates:

    X ::= 1;;
    Y ::= 1;;
    Z ::= 1;;
    while ~(X = 1 + n) do
      T ::= Z;;
      Z ::= Z + Y;;
      Y ::= T;;
      X ::= 1 + X
    end

    Fill in the following definition of [dfib] and prove that it
    satisfies this specification:

      ⦃ True ⦄ dfib ⦃ Y = fib n ⦄

    If all goes well, your proof will be very brief.
    Hint: you will need many uses of [ap] in your assertions.
*)

Definition T : string := "T".

Definition dfib (n : nat) : decorated

Theorem dfib_correct : forall n,
  dec_correct (dfib n).
(** [] *)

(* HIDE *)
(* ####################################################### *)
(* LATER: some potential additional examples and exercises;
   sort them out at some point *)

(** *** Euclid's Greatest Common Divisor (GCD) Algorithm *)

(* LATER: CH: this might make a good advanced/optional
   exercise. But what exactly can we ask the students to do?
   Translating from informal to formal is trivial, and the only
   hard to prove part are the 3 lemmas, which I didn't prove either
   since they have nothing to do with Hoare logics *)

(** RECALL: The greatest common divisor (GCD) of two numbers [m] and
    [n], written [gcd m n], is the largest number that evenly divides
    both [m] and [n].

    SOME USEFUL FACTS:
    - If y1>y2 then gcd y1 y2 = gcd (y1-y2) y2
    - If y1<y2 then gcd y1 y2 = gcd y1 (y2-y1)
    - gcd n n = n

    Euclid's algorithm for calculating GCDs:

    ⦃ X = m /\ Y = n ⦄
  while ~(X = Y) do
    if Y <= X
      then
         X := X - Y
      else
         Y := Y - X
    end
  end
    ⦃ X = gcd m n ⦄


    Informal decorated program:

    ⦃ X = m /\ Y = n ⦄ ->>
    ⦃ gcd m n = gcd X Y ⦄
  while ~(X = Y) do
      ⦃ gcd m n = gcd X Y /\ X<>Y ⦄
    if Y <= X
      then
          ⦃ gcd m n = gcd X Y /\ X<>Y /\ Y<=X ⦄ ->>
          ⦃ gcd m n = gcd (X-Y) Y ⦄
        X := X - Y
          ⦃ gcd m n = gcd X Y ⦄
      else
          ⦃ gcd m n = gcd X Y /\ X<>Y /\ ~(Y<=X) ⦄ ->>
          ⦃ gcd m n = gcd X (Y-X) ⦄
        Y := Y - X
          ⦃ gcd m n = gcd X Y ⦄
    end
  end
    ⦃ gcd m n = gcd X Y /\ ~(X<>Y) ⦄ ->>
    ⦃ gcd m n = gcd X Y /\ X=Y ⦄ ->>
    ⦃ gcd m n = X ⦄


    Formal decorated program:
*)

(* SOONER: Fix the concrete syntax, if we ever uncomment this! *)
Require Import NPeano. (* includes definition of gcd *)
Print gcd. (* this actually uses Euclid's algorithm internally;
              the more efficient version with mod not minus *)

Definition gcd_dec (m n:nat) : decorated :=
  <{
    ⦃ X = m /\ Y = n ⦄ ->>
    ⦃ gcd m n = ap2 gcd X Y ⦄
  while BNot (BEq (AId X) (AId Y)) do
      ⦃ gcd m n = ap2 gcd X Y /\ X <> Y ⦄
    if (Y <= X)
      then
          ⦃ gcd m n = ap2 gcd X Y
                       /\ X<> Y /\  Y<= X ⦄ ->>
          ⦃ gcd m n = ap2 gcd (X - Y) Y ⦄
        X := AMinus (AId X) (AId Y)
          ⦃ gcd m n = ap2 gcd X Y ⦄
      else

      ⦃ gcd m n = ap2 gcd X Y /\
                        X<> Y /\ ~(Y<=X) ⦄ ->>
          ⦃ gcd m n = ap2 gcd X (Y - X) ⦄
        Y := AMinus (AId Y) (AId X)
          ⦃ gcd m n = ap2 gcd X Y ⦄
    end
      ⦃ gcd m n = ap2 gcd X Y ⦄
  end
    ⦃ gcd m n = ap2 gcd X Y /\ ~(X <> Y) ⦄ ->>
    ⦃ gcd m n = ap2 gcd X Y /\ X =  Y ⦄ ->>
    ⦃ gcd m n =  X ⦄ }>.

Lemma gcd_eq : forall n, gcd n n = n.
Proof.
  apply Nat.gcd_diag.
Qed.

Lemma gcd_gt1 : forall y1 y2,
  y1 > y2 ->
  gcd y1 y2 = gcd (y1 - y2) y2.
Proof.
  intros.
  rewrite Nat.gcd_comm.
  rewrite <- Nat.gcd_sub_diag_r.
  - apply Nat.gcd_comm.
  - lia.
Qed.

Lemma gcd_gt2 : forall y1 y2,
  y1 < y2 ->
  gcd y1 y2 = gcd y1 (y2 - y1).
Proof.
  intros.
  rewrite Nat.gcd_sub_diag_r. auto.
  lia.
Qed.

Theorem gcd_correct : forall m n,
  dec_correct (gcd_dec m n).
Proof. verify.
  - (* 1 *) rewrite H. apply gcd_gt1. lia.
  - (* 2 *) rewrite H. apply gcd_gt2. lia.
  - (* 3 *) rewrite H. apply gcd_eq.
Qed.

(* ---------------------------------------------- *)
(* Absurdly slow multiplication *)

(*
PROGRAM AND SPEC:

  { X = m } ->>
Z := 0;
while ~(X = 0) do
  W := n;
  while ~(W = 0) do
    Z := Z + 1;
    W := W - 1
  end;
  X := X - 1
end
  { Z = m * n }


DECORATED PROGRAM:

  { X = m } ->>
  { 0 = (m-X) * n /\ X<=m }
Z := 0;
  { Z = (m-X) * n /\ X<=m }
while ~(X = 0) do
    { Z = (m-X) * n /\ X<=m /\ X<>0 } ->>
    { Z = (m-X) * n + (n-n) /\ X<=m }
  W := n;
    { Z = (m-X) * n + (n-W) /\ X<=m /\ W<=n }
  while ~(W = 0) do
      { Z = (m-X) * n + (n-W) /\ X<=m /\ W<=n /\ W<>0 } ->>
      { Z + 1 = (m-X) * n + (n-W) + 1 /\ X<=m /\ W-1<=n /\ W<>0 } ->>
      { Z + 1 = (m-X) * n + (n-(W-1)) /\ X<=m /\ W-1<=n }
    Z := Z + 1;
      { Z = (m-X) * n + (n-(W-1)) /\ X<=m /\ W-1<=n }
    W := W - 1
      { Z = (m-X) * n + (n-W) /\ X<=m /\ W<=n }
  end;
    { Z = (m-X) * n + (n-W) /\ X<=m /\ W<=n /\ ~(W<>0) } ->>
    { Z = (m-X) * n + n /\ X<=m } ->>
    { Z = ((m-X)+1) * n /\ X<=m } ->>
    { Z = (m-(X-1)) * n /\ X<=m }
  X := X - 1
    { Z = (m-X) * n /\ X<=m }
end
  { Z = (m-X) * n /\ X<=m /\ ~(X<>0) } ->>
  { Z = (m-X) * n /\ X=0 } ->>
  { Z = m * n }
*)

(* LATER: From 2009 final

   Give the weakest precondition for each of the following commands.
   (Use the informal notation for assertions rather than Coq notation,
   i.e., write X = 5, not fun st => st X = 5.)
   (a) ⦃ ? ⦄ X ::= (ANum 5) ⦃ X = 6 ⦄
   Answer: False
   (b) ⦃ ? ⦄
   testif (BLe (AId X) (AId Y))
   then skip
   else Z := (AId Y); Y := (AId X); X := (AId Z)
   ⦃ X <= Y ⦄
   Answer: True
   (c) ⦃ ? ⦄ while BNot (BEq (AId Y) (ANum 5)) do Y := APlus (AId Y) (ANum 1) ⦃ Y = 5 ⦄
   Answer: True
   (d) ⦃ ? ⦄ while BEq (AId X) (ANum 0) do Y := (ANum 1) ⦃ Y = 5 ⦄
   Answer: X=0 \/ Y=5

   --------------------

   For each of the while programs below, we have provided a precondition
   and postcondition. In the blank before each loop, in an invariant that
   would allow us to annotate the rest of the program. Assume X, Y and Z
   are distinct program variables.
   (a) { True }
   X := ANum n;
   Y := (ANum 1);
   { _______________________________________ }
   while (BNot (BEq (AId X) (ANum 0))) do (
   Y := AMult (AId Y) (ANum 2);
   X := AMinus (AId X) (ANum 1)
   )
   { Y = 2^n }
   Answer: Y = 2^(n-X)
   (b) { True }
   X := ANum m;
   Y := ANum n;
   Z := (ANum 0);
   { _______________________________________ }
   while (BAnd (BNot (BEq (AId X) (ANum 0))) (BNot (BEq (AId Y) (ANum 0)))) do (
   X := AMinus (AId X) (ANum 1);
   Y := AMinus (AId Y) (ANum 1);
   Z := APlus (AId Z) (ANum 1)
   )
   { Z = min(m,n) }
   (where min is the mathematical minimum function)
   Answer: Z = min(m,n) - min(X,Y)

*)

(* /HIDE *)

(* EX5A? (improve_dcom) *)
(** The formal decorated programs defined in this section are intended
    to look as similar as possible to the informal ones defined earlier
    in the chapter.  If we drop this requirement, we can eliminate
    almost all annotations, just requiring final postconditions and
    loop invariants to be provided explicitly.  Do this -- i.e., define a
    new version of dcom with as few annotations as possible and adapt the
    rest of the formal development leading up to the [verification_correct]
    theorem. *)

(* SOLUTION *)

(** This solution also allows optional post-condition assertions at any point,
    since these are quite useful in practice when debugging the results of
    more-or-less automated vc solvers. *)

Module SparseAnnotations.

Inductive dcom : Type :=
  | DCSkip : dcom
  | DCSeq : dcom -> dcom -> dcom
  | DCAsgn : string -> aexp -> dcom
  | DCIf : bexp -> dcom -> dcom -> dcom
  | DCWhile : bexp -> Assertion -> dcom -> dcom
  | DCAssert : Assertion -> dcom
.

Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> Assertion -> decorated.

(* INSTRUCTORS: Almost a copy of template dcom *)
Notation "'skip' ⦃ P  ⦄"
      := (DCSkip P)
           (in custom com at level 0, P constr) : dcom_scope.
Notation "l ':=' a"
      := (DCAsgn l a)
           (in custom com at level 0, l constr at level 0,
               a custom com at level 85, no associativity) : dcom_scope.
Notation "'while' b 'do' ⦃ Pbody ⦄ d 'end'"
      := (DCWhile b Pbody d)
           (in custom com at level 89, b custom com at level 99,
           Pbody constr) : dcom_scope.
Notation "'if' b 'then' d 'else' d' 'end'"
      :=   (DCIf b d d')
           (in custom com at level 89, b at level 99,
            d at level 99, d' at level 99) : dcom_scope.
Notation " d ; d' "
      := (DCSeq d d')
          (in custom com at level 90, right associativity) : dcom_scope.
Notation "⦃⦃ P ⦄⦄ d ⦃⦃ Q ⦄⦄"
      := (Decorated P d Q)
          (at level 0, d custom com at level 99, P constr, Q constr) : dcom_scope.

(** Here's how our decorated programs look now: *)

Example dec_while :=
  ⦃⦃ True ⦄⦄
  while ~(X = 0)
  do
    ⦃ True ⦄
    X := (X - 1)
  end
  ⦃⦃ X = 0 ⦄⦄.


(** It is easy to go from a [dcom] to a [com] by erasing all
    annotations. *)

Delimit Scope com_scope with com.

Fixpoint extract (d : dcom) : com :=
  match d with
  | DCSkip             => <{ skip }>
  | DCSeq d1 d2        => <{ extract d1 ; extract d2 }>%com
  | DCAsgn X a         => <{ X := a }>%com
  | DCIf b d1 d2       => <{ if b then extract d1 else extract d2 end }>%com
  | DCWhile b _ d      => <{ while b do extract d end }>
  | DCAssert _         => <{ skip }>
  end.

(** We can express what it means for a decorated program to be
    correct as follows: *)

Definition dec_correct (dec : decorated) :=
  match dec with
  | Decorated P d Q => ⦃ P ⦄ extract d ⦃ Q⦄
  end
.

(* This VC generator is derived from from Mike Gordon,
   "Background reading on Hoare Logic,"
   https://www.cl.cam.ac.uk/archive/mjcg/HL/Notes/Notes.pdf
*)

Fixpoint awp (P: Assertion) (d:dcom) : Assertion :=
  match d with
  | DCSkip => P
  | DCSeq d1 d2 => awp (awp P d2) d1
  | DCAsgn X a => P [X |-> a]
  | DCIf b d1 d2 => (b /\ awp P d1) \/ (~b /\ awp P d2)
  | DCAssert Q => Q /\ P
  | DCWhile b Q d0 => Q
  end.

Fixpoint vc (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSeq d1 d2 => vc (awp P d2) d1 /\ vc P d2
  | DCIf b d1 d2 => vc P d1 /\ vc P d2
  | DCWhile b Q d0 => (forall st, (Q /\ ~b -> P)%assertion st)
                      /\ (forall st, (Q /\ b -> awp Q d0)%assertion st)
                      /\ vc Q d0
  | _ => True
  end.

Theorem vc_correct: forall d P,
  vc P d -> ⦃ awp P d ⦄ extract d ⦃ P ⦄.
Proof.
 induction d; intros P H; simpl in *.
  - (* Skip *)
    apply hoare_skip.
  - (* Seq *)
    destruct H as [H1 H2].
    eapply hoare_seq.
      apply IHd2. apply H2.
      apply IHd1. apply H1.
  - (* Asgn *)
    apply hoare_asgn.
  - (* If *)
    destruct H as [HThen HElse].
    apply IHd1 in HThen. clear IHd1.
    apply IHd2 in HElse. clear IHd2.
    apply hoare_if.
      + eapply hoare_consequence_pre.
        eapply HThen; eauto.
        intro st. intros [H1 H2]. simpl in H2.
        intuition.
      + eapply hoare_consequence_pre.
        eapply HElse; eauto.
        intro st. intros [H1 H2]. simpl in H2.
        intuition.
  - (* While *)
    rename a into Q.
    destruct H as [H1 [H2 H3] ].
    apply IHd in H3.
    clear IHd.
    eapply hoare_consequence_post.
    eapply hoare_while.
    eapply hoare_consequence_pre.
    eapply H3.
    auto.  auto.
  - (* Assert *)
    unfold hoare_triple. intros.
    inversion H0. subst. intuition.
Qed.

Definition verification_conditions_dec (dec : decorated) : Prop :=
  match dec with
  | Decorated P d Q => P ->> awp Q d /\ vc Q d
  end.

Lemma verification_correct : forall dec,
  verification_conditions_dec dec -> dec_correct dec.
Proof.
  intros [P d Q]. simpl. intros. destruct H. eapply hoare_consequence_pre.
  apply vc_correct. auto. auto.
Qed.

Ltac verify :=
  intros;
  apply verification_correct;
  verify_assn.

(* HIDE *)
(* Let's redo all the examples to date. *)
Theorem dec_while_correct :
  dec_correct dec_while.
Proof.
  verify.
Qed.

Definition swap_dec (m n:nat) : decorated :=
   ⦃⦃ X = m /\ Y = n⦄⦄
  X := (X + Y);
  Y := (X - Y);
  X := (X - Y)
   ⦃⦃ X = n /\ Y = m⦄⦄.

Theorem swap_correct : forall m n,
  dec_correct (swap_dec m n).
Proof. verify.   Qed.

Definition if_minus_dec :=
  ⦃⦃True⦄⦄
  if X <= Y then
    Z := (Y - X)
  else
    Z := (X - Y)
  end
  ⦃⦃Z + X = Y \/ Z + Y = X⦄⦄.

Theorem if_minus_correct :
  dec_correct if_minus_dec.
Proof. verify. Qed.

Definition if_minus_plus_dec :=
  ⦃⦃True⦄⦄
  if X <= Y then
    Z := (Y - X)
  else
    Y := (X + Z)
  end
  ⦃⦃ Y = X + Z ⦄⦄.

Theorem if_minus_plus_correct :
  dec_correct if_minus_plus_dec.
Proof. verify. Qed.

Definition div_mod_dec (a b : nat) : decorated :=
  ⦃⦃ True ⦄⦄
  X := a;
  Y := 0;
  while b <= X do
    ⦃ b * Y + X = a ⦄
    X := (X - b);
    Y := (Y + 1)
  end
  ⦃⦃ b * Y + X = a /\ (X < b) ⦄⦄.

Theorem div_mod_dec_correct : forall a b,
  dec_correct (div_mod_dec a b).
Proof.
  verify.
Qed.

Definition parity_dec (m:nat) : decorated :=
⦃⦃ X = m ⦄⦄
 while 2 <= X do
    ⦃ ap parity X = parity m ⦄
    X := (X - 2)
 end
 ⦃⦃ X = parity m ⦄⦄.

Theorem parity_dec_correct :
  forall m, dec_correct (parity_dec m).
Proof.
intros.
verify;
    (* simplification too aggressive ... reverting a bit *)
    fold (2 <=? (st X)) in *;
    try rewrite leb_iff in *;
    try rewrite leb_iff_conv in *; eauto; try lia.
- rewrite <- H. rewrite parity_lt_2; auto; try lia.
- rewrite <- H. rewrite parity_ge_2; auto.
Qed.

Definition sqrt_dec (m:nat) : decorated :=
    ⦃⦃ X = m ⦄⦄
  Z := 0;
  while (Z+1)*(Z+1) <= X do
      ⦃ (X = m /\ Z*Z<=m) ⦄
    Z := (Z + 1)
  end
    ⦃⦃ Z*Z<=m /\ m<(Z+1)*(Z+1) ⦄⦄.

Theorem sqrt_correct : forall m,
  dec_correct (sqrt_dec m).
Proof. verify. Qed.


(** *** Squaring *)

(** Again, there are several ways of annotating the squaring program.
    The simplest variant we've found, [square_simpler_dec], is given
    last. *)

Definition square_dec (m : nat) : decorated :=
  ⦃⦃ X = m ⦄⦄
  Y := X;
  Z := 0;
  while ~ (Y = 0) do
    ⦃ Z + X * Y = m * m ⦄
    Z := (Z + X);
    Y := (Y - 1)
  end
  ⦃⦃ Z = m * m ⦄⦄.

Theorem square_dec_correct : forall m,
  dec_correct (square_dec m).
Proof.
  verify.
  - (* invariant preserved *)
    destruct (st Y) as [| y'].
    + exfalso. auto.
    + simpl. rewrite <- minus_n_O.
    assert (G : forall n m, n * S m = n + n * m). {
      clear. intros. induction n. reflexivity. simpl.
      rewrite IHn. lia. }
    rewrite <- H. rewrite G. lia.
Qed.

Definition square_dec' (n : nat) : decorated :=
  ⦃⦃ True ⦄⦄
  X := n;
  Y := X;
  Z := 0;
  while ~(Y = 0) do
    ⦃ (Z = X * (X - Y)
                /\ X = n /\ Y <= X) ⦄
    Z := (Z + X);
    Y := (Y - 1)
  end
  ⦃⦃ Z = n * n ⦄⦄.

Theorem square_dec'_correct : forall (n:nat),
  dec_correct (square_dec' n).
Proof.
  verify.
  - (* invariant preserved *)
    simpl.
    rewrite mult_minus_distr_l.
    repeat rewrite mult_minus_distr_l. rewrite mult_1_r.
    assert (G : forall n m p,
                  m <= n -> p <= m -> n - (m - p) = n - m + p).
      intros. lia.
    rewrite G. reflexivity. apply mult_le_compat_l. assumption.
    destruct (st Y).
    + exfalso. auto.
    + clear. rewrite mult_succ_r. rewrite plus_comm.
      apply le_plus_l.
Qed.

Definition square_simpler_dec (m : nat) : decorated :=
  ⦃⦃ X = m ⦄⦄
  Y := 0;
  Z := 0;
  while ~(Y = X) do
    ⦃ (Z = Y*m /\ X = m) ⦄
    Z := (Z + X);
    Y := (Y + 1)
  end
  ⦃⦃ Z = m*m ⦄⦄.

Theorem square_simpler_dec_correct : forall m,
  dec_correct (square_simpler_dec m).
Proof.
  verify.
Qed.

Definition two_loops_dec (a b c : nat) : decorated :=
  ⦃⦃ True ⦄⦄
  X := 0;
  Y := 0;
  Z := c;
  while ~(X = a) do
    ⦃ (Z = X + c /\ Y = 0) ⦄
    X := (X + 1);
    Z := (Z + 1)
  end;
  while ~(Y = b) do
    ⦃ Z = a + Y + c ⦄
    Y := (Y + 1);
    Z := (Z + 1)
  end
  ⦃⦃ Z = a + b + c ⦄⦄.

Theorem two_loops_correct : forall a b c,
  dec_correct (two_loops_dec a b c).
Proof. verify. Qed.

Example subtract_slowly_dec (m : nat) (p : nat) : decorated :=
    ⦃⦃ X = m /\  Z = p ⦄⦄
  while ~(X = 0)
  do   ⦃ Z - X = p - m ⦄
     Z := (Z - 1);
     X := (X - 1)
  end
    ⦃⦃ Z = p - m ⦄⦄.

Theorem subract_slowly_dec : forall m p,
  dec_correct (subtract_slowly_dec m p).
Proof. verify. Qed.

Definition dpow2_down (n : nat) :=
  ⦃⦃ True ⦄⦄
  X := 0;
  Y := 1;
  Z := 1;
  while ~(X = n) do
    ⦃ (Y = (ap pow2 (X + 1))-1 /\ Z = ap pow2 X) ⦄
    Z := (2 * Z);
    Y := (Y + Z);
    X := (X + 1)
  end
  ⦃⦃ Y = pow2 (n+1) - 1 ⦄⦄.

Lemma pow2_plus_1 : forall n,
  pow2 (n+1) = pow2 n + pow2 n.
Proof. induction n; simpl. reflexivity. lia. Qed.

Lemma pow2_le_1 : forall n, pow2 n >= 1.
Proof. induction n. simpl. constructor. simpl. lia. Qed.

Theorem dpow2_down_correct : forall n,
  dec_correct (dpow2_down n).
Proof.
  verify.
  - rewrite <- plus_n_O.
    rewrite <- pow2_plus_1. remember (st X) as x.
    replace (pow2 (x + 1) - 1 + pow2 (x + 1))
       with (pow2 (x + 1) + pow2 (x + 1) - 1) by lia.
    rewrite <- pow2_plus_1.
    replace (x + 1 + 1) with (x + 2) by lia.
    reflexivity.
  - rewrite <- plus_n_O. rewrite <- pow2_plus_1.
    reflexivity.
Qed.

Example factorial_dec (m:nat) : decorated :=
    ⦃⦃ X = m ⦄⦄
  Y := 1;
  while ~(X = 0)
  do   ⦃ Y * ap real_fact X = real_fact m ⦄
     Y := (Y * X);
     X := (X - 1)
  end
  ⦃⦃ Y = real_fact m ⦄⦄.

Lemma fact_sub1 : forall m,
  m<>0 -> m * real_fact (m-1) = real_fact m.
Proof.
  intros. destruct m. exfalso. auto.
  simpl. rewrite <- minus_n_O. reflexivity.
Qed.

Theorem factorial_dec_correct : forall m,
  dec_correct (factorial_dec m).
Proof.
  verify.
    simpl in *. lia.
    rewrite <- mult_assoc. rewrite -> fact_sub1; assumption.
Qed.

Definition T : string := "T".

Definition dfib (n : nat) : decorated :=
  ⦃⦃ True ⦄⦄
  X := 1;
  Y := 1;
  Z := 1;
  while ~(X = 1 + n) do
    ⦃ Z = ap fib X
       /\ Y = ap fib (ap pred X)
       /\ X > 0 ⦄
    T := Z;
    Z := (Z + Y);
    Y := T;
    X := (1 + X)
  end
  ⦃⦃ Y = fib n ⦄⦄.

Theorem dfib_correct : forall n,
  dec_correct (dfib n).
Proof.
  verify. rewrite fib_eqn; auto.
Qed.
(* /HIDE *)

End SparseAnnotations.

(* /SOLUTION *)
(** [] *)

(* /FULL *)
(* HIDE *)
(* Local Variables: *)
(* fill-column: 70 *)
(* outline-regexp: "(\\*\\* \\*+\\|(\\* EX[1-5]..." *)
(* End: *)
(* mode: outline-minor *)
(* outline-heading-end-regexp: "\n" *)
(* /HIDE *)


## Unicode

This section uses the following Unicode symbols:

    ¬  U+00AC  NOT SIGN (\neg)
    ×  U+00D7  MULTIPLICATION SIGN (\x)
    η  U+03B7  GREEK SMALL LETTER ETA (\eta)
    ⊎  U+228E  MULTISET UNION (\u+)
    ⊤  U+22A4  DOWN TACK (\top)
    ⊥  U+22A5  UP TACK (\bot)
    ≢  U+2262  NOT IDENTICAL TO (\==n)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)
    ⦃  U+2983  LEFT WHITE CURLY BRACKET
    ⦄  U+2984  RIGHT WHITE CURLY BRACKET


---

*This page is derived from Pierce et al.; for more information see the
[sources and authorship]({{ site.baseurl }}/Sources/) page.*
