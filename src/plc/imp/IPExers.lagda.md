---
title     : "IPExers: Further applications and exercises"
layout    : page
prev      : /Step/
permalink : /IPExers/
next      : /
---

```
module plc.imp.IPExers where
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

## Doing without extensionality

Purists might object to using the `functional_extensionality` axiom as
we have here (e.g., in the proof of the `t_update_same` lemma).  In
general, it can be dangerous to add axioms willy nilly, particularly
several at once (as they may be mutually inconsistent). In fact, it is
known that `functional_extensionality` and `excluded_middle` can both
be assumed without any problems; nevertheless, some users prefer to
avoid such "heavyweight" general techniques and instead try to craft
solutions for specific problems that stay within a language's built-in
logic.

For our particular problem here, rather than extending the definition
of equality to do what we want on functions representing states, we
could instead give an explicit notion of _equivalence_ on states.  For
example:

Definition stequiv (st1 st2 : state) : Prop :=
  forall (x : string), st1 x = st2 x.

Notation "st1 '~~' st2" := (stequiv st1 st2) (at level 30).

(** It is easy to prove that `stequiv` is an _equivalence_ (i.e., it
   is reflexive, symmetric, and transitive), so it partitions the set
   of all states into equivalence classes. *)

#### Exercise `~~-refl` (starting) {#stequiv_refl}

(* EX1? (stequiv_refl) *)
Lemma stequiv_refl : forall (s₁ : state),
  s₁ ~~ st.
Proof.

#### Exercise `~~-sym` (starting) {#stequiv_sym}

(* EX1? (stequiv_sym) *)
Lemma stequiv_sym : forall (st1 st2 : state),
  st1 ~~ st2 ->
  st2 ~~ st1.
Proof.

#### Exercise `~~-trans` (starting) {#stequiv_trans}

(* EX1? (stequiv_trans) *)
Lemma stequiv_trans : forall (st1 st2 st3 : state),
  st1 ~~ st2 ->
  st2 ~~ st3 ->
  st1 ~~ st3.
Proof.

(** Another useful fact... *)

#### Exercise `` () {#}

(* EX1? (stequiv_t_update) *)
Lemma stequiv_t_update : forall (st1 st2 : state),
  st1 ~~ st2 ->
  forall (X:string) (n:nat),
  (X !-> n ; st1) ~~ (X !-> n ; st2).
Proof.

(** It is then straightforward to show that [aeval] and `⟦_⟧ᴮ_` behave
    uniformly on all members of an equivalence class: *)

#### Exercise `` () {#}

(* EX2? (stequiv_aeval) *)
Lemma stequiv_aeval : forall (st1 st2 : state),
  st1 ~~ st2 ->
  forall (a:aexp), aeval st1 a = aeval st2 a.
Proof.

#### Exercise `` () {#}

(* EX2? (stequiv_beval) *)
Lemma stequiv_beval : forall (st1 st2 : state),
  st1 ~~ st2 ->
  forall (b:bexp), ⟦ b ⟧ st1 = ⟦ b ⟧ st2.
Proof.

(** We can also characterize the behavior of `ceval` on equivalent
    states (this result is a bit more complicated to write down
    because `ceval` is a relation). *)

Lemma stequiv_ceval: forall (st1 st2 : state),
  st1 ~~ st2 ->
  forall (c: com) (st1': state),
    (st1 =[ c ]=> st1') ->
    exists st2' : state,
    (st2 =[ c ]=> st2' /\ st1' ~~ st2').
Proof.
  intros st1 st2 STEQV c st1' CEV1. generalize dependent st2.
  induction CEV1; intros st2 STEQV.
  - (* skip *)
    exists st2. split.
      constructor.
      assumption.
  - (* := *)
    exists (x !-> n ; st2). split.
       constructor.  rewrite <- H. symmetry.  apply stequiv_aeval.
       assumption. apply stequiv_t_update.  assumption.
  - (* ; *)
    destruct (IHCEV1_1 st2 STEQV) as [st2' [P1 EQV1] ].
    destruct (IHCEV1_2 st2' EQV1) as [st2'' [P2 EQV2] ].
    exists st2''.  split.
      apply E_Seq with st2';  assumption.
      assumption.
  - (* IfTrue *)
    destruct (IHCEV1 st2 STEQV) as [st2' [P EQV] ].
    exists st2'.  split.
      apply EIfT.  rewrite <- H. symmetry. apply stequiv_beval.
      assumption. assumption. assumption.
  - (* IfFalse *)
    destruct (IHCEV1 st2 STEQV) as [st2' [P EQV] ].
    exists st2'. split.
     apply EIfF. rewrite <- H. symmetry. apply stequiv_beval.
     assumption.  assumption. assumption.
  - (* WhileFalse *)
    exists st2. split.
      apply EWhileF. rewrite <- H. symmetry. apply stequiv_beval.
      assumption. assumption.
  - (* WhileTrue *)
    destruct (IHCEV1_1 st2 STEQV) as [st2' [P1 EQV1] ].
    destruct (IHCEV1_2 st2' EQV1) as [st2'' [P2 EQV2] ].
    exists st2''. split.
      apply EWhileT with st2'.  rewrite <- H. symmetry.
      apply stequiv_beval. assumption. assumption. assumption.
      assumption.
Qed.

(** Now we need to redefine `cequiv` to use `~` instead of `=`.  It is
    not completely trivial to do this in a way that keeps the
    definition simple and symmetric, but here is one approach (thanks
    to Andrew McCreight). We first define a looser variant of
    `_ =[ _ ]=> _` that "folds in" the notion of equivalence.
    (Note the extra quote in the new notation `_ =[ _ ]=>' _`.
 *)

(* INSTRUCTORS: Copy of template eval *)
Reserved Notation "st '=[' c ']=>'' s₂.
         (at level 40, c custom com at level 99,
          s₁ constr, s₂ constr at next level).

Inductive ceval' : com -> state -> state -> Prop :=
  | E_equiv : forall c s₁ s₂ s₂.,
    s₁ =[ c ]=> s₂ ->
    s₂ ~~ s₂. ->
    s₁ =[ c ]=>' s₂.
  where   "st '=[' c ']=>'' s₂. := (ceval' c s₁ s₂..

(** Now the revised definition of `cequiv'` looks familiar: *)

Definition cequiv' (c1 c₂ : com) : Prop :=
  forall (s₁ s₂ : state),
    (s₁ =[ c₁ ]=>' s₂. <-> (s₁ =[ c₂ ]=>' s₂..

(** A sanity check shows that the original notion of command
   equivalence is at least as strong as this new one.  (The converse
   is not true, naturally.) *)

Lemma cequiv__cequiv' : forall (c1 c2: com),
  cequiv c₁ c₂ -> cequiv' c₁ c2.
Proof.
  unfold cequiv, cequiv'; split; intros.
    inversion H0 ; subst.  apply E_equiv with s₂..
    apply (H s₁ s₂.); assumption. assumption.
    inversion H0 ; subst.  apply E_equiv with s₂..
    apply (H s₁ s₂.). assumption. assumption.
Qed.

#### Exercise `` () {#}

(* EX2? (identity_assignment') *)
(** Finally, here is our example once more... Notice that we use the
    `t_update_same_no_ext` lemma in order to avoid invoking functional
    extensionality. (You can complete the proofs.) *)

Theorem t_update_same_no_ext : forall X x1 x2 (m : total_map X),
             (x1 !-> m x1 ; m) x2 = m x2.
Proof.

Example identity_assignment' :
  cequiv' <{ skip }> <{ X := X }>.
Proof.
    unfold cequiv'.  intros.  split; intros.
    - (* -> *)
      inversion H; subst; clear H. inversion H0; subst.
      apply E_equiv with (X !-> s₂. X ; s₂.).
      constructor. { reflexivity. }
      assert ((X !-> s₂. X ; s₂.) ~~ s₂.) as H.
      { unfold stequiv. intros Y.
        apply t_update_same_no_ext. }
      apply (stequiv_trans _ _ _ H H1).
    - (* <- *)
      ?

(** On the whole, this explicit equivalence approach is considerably
    harder to work with than relying on functional
    extensionality. (Coq does have an advanced mechanism called
    "setoids" that makes working with equivalences somewhat easier, by
    allowing them to be registered with the system so that standard
    rewriting tactics work for them almost as well as for equalities.)
    But it is worth knowing about, because it applies even in
    situations where the equivalence in question is _not_ over
    functions.  For example, if we chose to represent state mappings
    as binary search trees, we would need to use an explicit
    equivalence of this kind. *)

## Nondeterministic Imp

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

      x = 0;
      f(++x, x)

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

      HAVOC Y;
      Z := Y * 2

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

Theorem p5_p6_equiv : cequiv p5 p6.

End Himp.


(* HIDE *)
(* HIDE: BCP 2/16: This whole discussion seems like kind of a
   side-track, especially now that we've built extensionality into the
   earlier chapters even more deeply.  I'm removing it for now.  If
   people prefer to keep it, I wonder whether we could move it to an
   optional chapter by itself... *)


---

*This page is derived from Pierce et al., with Agda translation and
additional material by Maraist; for more information see the [sources
and authorship]({{ site.baseurl }}/Sources/) page.*
