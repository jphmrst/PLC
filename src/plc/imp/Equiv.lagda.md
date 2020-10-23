---
title     : "Equiv: What does it mean for two programs to be equivalent?"
layout    : page
prev      : /Imp/
permalink : /Equiv/
next      : /
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
open import plc.vfp.MapProps
open import plc.vfp.Relations using (_⇔_)
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


Theorem bequiv_example: bequiv <{ X - X = 0 }> <{ true }>.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  intros st. unfold beval.
  rewrite ≡ᴬ-example. reflexivity.
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)

(** FULL: For commands, the situation is a little more subtle.  We can't
    simply say "two commands are behaviorally equivalent if they
    evaluate to the same ending state whenever they are started in the
    same initial state," because some commands, when run in some
    starting states, don't terminate in any final state at all!  What
    we need instead is this: two commands are behaviorally equivalent
    if, for any given starting state, they either (1) both diverge
    or (2) both terminate in the same final state.  A compact way to
    express this is "if the first one terminates in a particular state
    then so does the second, and vice versa." *)
(** TERSE: For commands, we need to deal with the possibility of
    nontermination.

    We do this by defining command equivalence as "if the first one
    terminates in a particular state then so does the second, and vice
    versa": *)

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

(* TERSE *)
(* QUIZ *)
(** Are these two programs equivalent?
[[
    X := 1;
    Y := 2
]]
    and
[[
    Y := 2;
    X := 1
]]

    (1) Yes

    (2) No

    (3) Not sure
*)
(* /QUIZ *)

(* QUIZ *)
(** What about these?

[[
    X := 1;
    Y := 2
]]
    and
[[
    X := 2;
    Y := 1
]]

    (1) Yes

    (2) No

    (3) Not sure
*)
(* /QUIZ *)

(* QUIZ *)
(** What about these?

[[
    while 1 <= X do
      X := X + 1
    end
]]
    and
[[
    while 2 <= X do
      X := X + 1
    end
]]

    (1) Yes

    (2) No

    (3) Not sure

*)
(* INSTRUCTORS: No. (When started in a state where variable X has value 1,
    the first program diverges while the second one halts.) *)
(* /QUIZ *)

(* QUIZ *)
(** These?
[[
    while true do
      while false do X := X + 1 end
    end
]]
    and
[[
    while false do
      while true do X := X + 1 end
    end
]]

    (1) Yes

    (2) No

    (3) Not sure
*)
(* INSTRUCTORS: No. (The first program always diverges; the second
   always halts.) *)
(* /QUIZ *)
(* /TERSE *)

(* ####################################################### *)
(** ** Simple Examples *)

(** For examples of command equivalence, let's start by looking at
    some trivial program transformations involving `skip`: *)

Theorem skip_left : forall c,
  cequiv
    <{ skip; c }>
    c.
Proof.
  (* WORKINCLASS *)
  intros c st st'.
  split; intros H.
  - (* -> *)
    inversion H. subst.
    inversion H2. subst.
    assumption.
  - (* <- *)
    apply E_Seq with st.
    apply E_Skip.
    assumption.
Qed.
(* /WORKINCLASS *)


(* EX2 (skip_right) *)
(** Prove that adding a `skip` after a command results in an
    equivalent program *)

Theorem skip_right : forall c,
  cequiv
    <{ c ; skip }>
    c.
Proof.
  (* ADMITTED *)
  intros c st st'.
  split; intros H.
  - (* -> *)
    inversion H. subst.
    inversion H5. subst.
    assumption.
  - (* <- *)
    apply E_Seq with st'.
    assumption. apply E_Skip.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: skip_right *)


(** TERSE: *** *)

(** Similarly, here is a simple transformation that optimizes `if`
    commands: *)

Theorem if_true_simple : forall c1 c2,
  cequiv
    <{ if true then c1 else c2 end }>
    c1.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  intros c1 c2.
  split; intros H.
  - (* -> *)
    inversion H; subst. assumption. discriminate.
  - (* <- *)
    apply E_IfTrue. reflexivity. assumption.  Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)

(** Of course, no (human) programmer would write a conditional whose
    guard is literally `true`.  But they might write one whose guard
    is _equivalent_ to true: *)

(** _Theorem_: If `b` is equivalent to `true`, then `if b then c1
    else c2 end` is equivalent to `c1`. *)
(**
   _Proof_:

     - (`→`) We must show, for all `st` and `st'`, that if
       `st =[ if b then c1 else c2 end ]=> st'` then
       `st =[ c1 ]=> st'`.

       Proceed by cases on the rules that could possibly have been
       used to show `st =[ if b then c1 else c2 end ]=> st'a, namely
       `E_IfTrue` and `E_IfFalse`.

       - Suppose the final rule in the derivation of
         `st =[ if b then c1 else c2 end ]=> st'`
         was `E_IfTrue`.  We then have,
         by the premises of `E_IfTrue`, that `st =[ c1 ]=> st'`.
         This is exactly what we set out to prove.

       - On the other hand, suppose the final rule in the derivation
         of `st =[ if b then c1 else c2 end ]=> st'` was `E_IfFalse`.
         We then know that `beval st b = false` and `st =[ c2 ]=> st'`.

         Recall that `b` is equivalent to `true`, i.e., forall `st`,
         `beval st b = beval st <{true}>`.  In particular, this means
         that `beval st b = true`, since `beval st <{true}> = true`.  But
         this is a contradiction, since `E_IfFalse` requires that
         `beval st b = false`.  Thus, the final rule could not have
         been `E_IfFalse`.

     - (`←`) We must show, for all `st` and `st'`, that if
       `st =[ c1 ]=> st'` then
       `st =[ if b then c1 else c2 end ]=> st'`.

       Since `b` is equivalent to `true`, we know that `beval st b` =
       `beval st <{true}>` = `true`.  Together with the assumption that
       `st =[ c1 ]=> st'`, we can apply `E_IfTrue` to derive
       `st =[ if b then c1 else c2 end ]=> st'`. 

   Here is the formal version of this proof:


Theorem if_true: forall b c1 c2,
  bequiv b <{true}>  ->
  cequiv
    <{ if b then c1 else c2 end }>
    c1.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* b evaluates to true *)
      assumption.
    + (* b evaluates to false (contradiction) *)
      unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      discriminate.
  - (* <- *)
    apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    apply Hb. Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(** TERSE: Similarly: *)

(* FULL: EX2! (if_false) *)
Theorem if_false : forall b c1 c2,
  bequiv b <{false}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c2.
(* TERSE: HIDEFROMHTML *)
Proof.
  (* ADMITTED *)
  intros b c1 c2 Hb.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* b evaluates to true (contradiction) *)
      rewrite Hb in H5.
      discriminate.
    + (* b evaluates to false *)
      assumption.
  - (* <- *)
    apply E_IfFalse; try assumption.
    apply Hb. Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: if_false *)
(** FULL: [] *)
(* TERSE: /HIDEFROMHTML *)


(* EX3 (swap_if_branches) *)
(** Show that we can swap the branches of an `if` if we also negate its
    guard. *)

Theorem swap_if_branches : forall b c1 c2,
  cequiv
    <{ if b then c1 else c2 end }>
    <{ if ~ b then c2 else c1 end }>.
Proof.
  (* ADMITTED *)
  intros b c1 c2 st st'.
  split; intros Hce.
  - (* -> *)
    inversion Hce; subst.
    + (* b is true *)
      apply E_IfFalse; try assumption.
      simpl. rewrite H4. reflexivity.
    + (* b is false *)
      apply E_IfTrue; try assumption.
      simpl. rewrite H4. reflexivity.
  - (* <- *)
    inversion Hce; subst.
    + (* b is false *)
      simpl in H4. symmetry in H4; apply negb_sym in H4. simpl in H4.
      apply E_IfFalse; assumption.
    + (* b is true *)
      simpl in H4. symmetry in H4; apply negb_sym in H4. simpl in H4.
      apply E_IfTrue; assumption.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: swap_if_branches *)


(** TERSE: *** *)

(** For `while` loops, we can give a similar pair of theorems.  A loop
    whose guard is equivalent to `false` is equivalent to `skip`,
    while a loop whose guard is equivalent to `true` is equivalent to
    `while true do skip end` (or any other non-terminating program).
    The first of these facts is easy. *)

Theorem while_false : forall b c,
  bequiv b <{false}> ->
  cequiv
    <{ while b do c end }>
    <{ skip }>.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  intros b c Hb. split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* E_WhileFalse *)
      apply E_Skip.
    + (* E_WhileTrue *)
      rewrite Hb in H2. discriminate.
  - (* <- *)
    inversion H; subst.
    apply E_WhileFalse.
    apply Hb.  Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)


(* EX2A? (while_false_informal) *)
(** Write an informal proof of `while_false`.

(* LATER: (BCP 10/17) Not that happy with the wording of this... *)
(* SOLUTION *)
   Theorem: forall `b` `c`, if `b` is equivalent to `false`,
   then `while b do c end` is equivalent to `skip`.

   Proof:

   - (`→`) We know that `b` is equivalent to `false`.  We must
     show, for all `st` and `st'`, that if
     `st =[ while b do c end ]=> st'` then `st =[ skip ]=> st'`.

     There are only two ways we can have
     `st =[ while b do c end ]=> st'`: using
     `E_WhileFalse` and `E_WhileTrue`.

     - Suppose the final rule used to show
       `st =[ while b do c end ]=> st'` was `E_WhileFalse`.  We then
       know that `st = st'`; by `E_Skip`, we know that
       `st =[ skip ]=> st`.

     - Suppose the final rule used to show
       `st =[ while b do c end ]=> st'` was `E_WhileTrue`.  But this
       rule only applies when `beval st b = true`.  However, we are
       assuming that that `b` is equivalent to `false`, i.e., forall
       `st`, `beval st b = beval st <{false}> = false`. So we have a
       contradiction, and the final rule could not have been
       `E_WhileTrue` after all.

   - (<-) We know that `b` is equivalent to `false`.  We must
     show, for all `st` and `st'`, that if `st =[ skip ]=> st'`
     then `st =[ while b do c end ]=> st'`.

     `E_Skip` is the only rule that could have proven
     `st =[ skip ]=> st'`, so we know that `st' = st`.  We must show
     that `st =[ while b do c LOOP ]=> st`.

     Since `b` is equivalent to `false`, we know that
     `beval st b = false`.  By `E_WhileFalse`, then, we can derive that
     `st =[ while b do c end ]=> st`, and we are done.
(* /SOLUTION *)
*)


(** TERSE: *** *)

(** To prove the second fact, we need an auxiliary lemma stating that
    `while` loops whose guards are equivalent to `true` never
    terminate. *)

(* LATER: This proof is quite subtle. In particular, it's not
   easy to explain how the induction hypothesis comes about. *)
(** FULL: _Lemma_: If `b` is equivalent to `true`, then it cannot be
    the case that `st =[ while b do c end ]=> st'`.

    _Proof_: Suppose that `st =[ while b do c end ]=> st'`.  We show,
    by induction on a derivation of `st =[ while b do c end ]=> st'`,
    that this assumption leads to a contradiction. The only two cases
    to consider are `E_WhileFalse` and `E_WhileTrue`, the others
    are contradictory.

    - Suppose `st =[ while b do c end ]=> st'` is proved using rule
      `E_WhileFalse`.  Then by assumption `beval st b = false`.  But
      this contradicts the assumption that `b` is equivalent to
      `true`.

    - Suppose `st =[ while b do c end ]=> st'` is proved using rule
      `E_WhileTrue`.  We must have that:

      1. `beval st b = true`,
      2. there is some `st0` such that `st =[ c ]=> st0` and
         `st0 =[ while b do c end ]=> st'`,
      3. and we are given the induction hypothesis that
         `st0 =[ while b do c end ]=> st'` leads to a contradiction,

      We obtain a contradiction by 2 and 3. [] *)

Lemma while_true_nonterm : forall b c st st',
  bequiv b <{true}> ->
  ~( st =[ while b do c end ]=> st' ).
Proof.
  (* WORKINCLASS *)
  intros b c st st' Hb.
  intros H.
  remember <{ while b do c end }> as cw eqn:Heqcw.
  induction H;
  (* Most rules don't apply; we rule them out by inversion: *)
  inversion Heqcw; subst; clear Heqcw.
  (* The two interesting cases are the ones for while loops: *)
  - (* E_WhileFalse *) (* contradictory — b is always true! *)
    unfold bequiv in Hb.
    (* `rewrite` is able to instantiate the quantifier in `st` *)
    rewrite Hb in H. discriminate.
  - (* E_WhileTrue *) (* immediate from the IH *)
    apply IHceval2. reflexivity.  Qed.
(* /WORKINCLASS *)


(* EX2? (while_true_nonterm_informal) *)
(** Explain what the lemma `while_true_nonterm` means in English.

(* SOLUTION *) `while_true_nonterm` claims that if a `bexp` `b` is
   equivalent to `true` (i.e., if `forall st, beval st b = true`),
   then it is not possible to construct a derivation
   `st =[ while b do c end ]=> st'` for any `st`, `st'`, or `c`.

   We can understand this lack of a derivation as nontermination: the
   reason a derivation can't be constructed is because the
   `E_WhileTrue` rule would need to be applied infinitely many times,
   but derivations are finite.
(* /SOLUTION *)
*)


(* FULL: EX2! (while_true) *)
(** FULL: Prove the following theorem. _Hint_: You'll want to use
    `while_true_nonterm` here. *)

Theorem while_true : forall b c,
  bequiv b <{true}>  ->
  cequiv
    <{ while b do c end }>
    <{ while true do skip end }>.
(* TERSE: HIDEFROMHTML *)
Proof.
  (* ADMITTED *)
  intros b c Hb.
  split; intros H.
  - (* -> *)
    exfalso.
    apply while_true_nonterm with b c st st'; assumption.
  - (* <- *)
    exfalso.
    apply while_true_nonterm with <{ true }> <{ skip }> st st'.
    unfold bequiv. reflexivity.
    apply H.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: while_true *)
(** FULL: [] *)
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)

(** A more interesting fact about `while` commands is that any number
    of copies of the body can be "unrolled" without changing meaning.
    Loop unrolling is a common transformation in real compilers. *)

Theorem loop_unrolling : forall b c,
  cequiv
    <{ while b do c end }>
    <{ if b then c ; while b do c end else skip end }>.
Proof.
  (* WORKINCLASS *)
(* FOLD *)
  intros b c st st'.
  split; intros Hce.
  - (* -> *)
    inversion Hce; subst.
    + (* loop doesn't run *)
      apply E_IfFalse. assumption. apply E_Skip.
    + (* loop runs *)
      apply E_IfTrue. assumption.
      apply E_Seq with (st' := st'0). assumption. assumption.
  - (* <- *)
    inversion Hce; subst.
    + (* loop runs *)
      inversion H5; subst.
      apply E_WhileTrue with (st' := st'0).
      assumption. assumption. assumption.
    + (* loop doesn't run *)
      inversion H5; subst. apply E_WhileFalse. assumption.  Qed.
(* /FOLD *)
(* /WORKINCLASS *)


(* EX2? (seq_assoc) *)
(** _Note: Coq 8.12.0 has a printing bug that makes both sides of this
    theorem look the same in the Goals buffer. This should be fixed in
    8.12.1_. *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv <{(c1;c2);c3}> <{c1;(c2;c3)}>.
Proof. (* SOONER: Parens were missing here!! Recheck when 8.12.1 comes out! *)
  (* ADMITTED *)
  intros c1 c2 c3 st st'.
  split; intros Hce.
  - (* -> *)
    inversion Hce. subst. inversion H1. subst.
    apply E_Seq with (st' := st'1); try assumption.
    apply E_Seq with (st' := st'0); try assumption.
  - (* <- *)
    inversion Hce. subst. inversion H4. subst.
    apply E_Seq with (st' := st'1); try assumption.
    apply E_Seq with (st' := st'0); try assumption.  Qed.
(* /ADMITTED *)

(** Proving program properties involving assignments is one place
    where the fact that program states are treated
    extensionally (e.g., `x !-> m x ; m` and `m` are equal maps) comes
    in handy. *)

(* LATER: This proof could be streamlined if we had
   `rewrite ... at ...`. *)
Theorem identity_assignment : forall x,
  cequiv
    <{ x := x }>
    <{ skip }>.
Proof.
  intros.
  split; intro H; inversion H; subst; clear H.
  - (* -> *)
    rewrite t_update_same.
    apply E_Skip.
  - (* <- *)
    assert (Hx : st' =[ x := x ]=> (x !-> st' x ; st')).
    { apply E_Ass. reflexivity. }
    rewrite t_update_same in Hx.
    apply Hx.
Qed.

(* EX2! (assign_aequiv) *)
Theorem assign_aequiv : forall (x : string) a,
  aequiv x a ->
  cequiv <{ skip }> <{ x := a }>.
Proof.
  (* ADMITTED *)
  intros x a Ha st st'. split; intros H.
  - (* -> *)
    rewrite <- (t_update_same _ st' x).
    inversion H. subst. constructor. rewrite <- Ha. reflexivity.
  - (* <- *)
    inversion H. subst. rewrite <- Ha. simpl.
    rewrite t_update_same. constructor.
Qed.
  (* /ADMITTED *)
(* GRADE_THEOREM 2: assign_aequiv *)

(* EX2M (equiv_classes) *)
(* HIDE: taken from 2012 midterm 2 *)
(* HIDE: Sampsa: I feel that the exercise `equiv_classes` would
   benefit from being proven or checked somehow.  Such exercises are
   difficult to evaluate alone.
   BCP: There's some (hidden) infrastructure here for doing that, but
   it's not clear how to incorporate it into the current grading tools. *)

(** Given the following programs, group together those that are
    equivalent in Imp. Your answer should be given as a list of lists,
    where each sub-list represents a group of equivalent programs. For
    example, if you think programs (a) through (h) are all equivalent
    to each other, but not to (i), your answer should look like this:
[[
       [ [prog_a;prog_b;prog_c;prog_d;prog_e;prog_f;prog_g;prog_h] ;
         [prog_i] ]
]]
    Write down your answer below in the definition of
    `equiv_classes`. *)

Definition prog_a : com :=
  <{ while ~(X <= 0) do
       X := X + 1
     end }>.

Definition prog_b : com :=
  <{ if (X = 0) then
       X := X + 1;
       Y := 1
     else
       Y := 0
     end;
     X := X - Y;
     Y := 0 }>.

Definition prog_c : com :=
  <{ skip }> .

Definition prog_d : com :=
  <{ while ~(X = 0) do
       X := (X * Y) + 1
     end }>.

Definition prog_e : com :=
  <{ Y := 0 }>.

Definition prog_f : com :=
  <{ Y := X + 1;
     while ~(X = Y) do
       Y := X + 1
     end }>.

Definition prog_g : com :=
  <{ while true do
       skip
     end }>.

Definition prog_h : com :=
  <{ while ~(X = X) do
       X := X + 1
     end }>.

Definition prog_i : com :=
  <{ while ~(X = Y) do
       X := Y + 1
     end }>.

Definition equiv_classes : list (list com)
  (* ADMITDEF *) :=
  [ [prog_a; prog_d] ;
    [prog_b; prog_e] ;
    [prog_c; prog_h] ;
    [prog_f; prog_g] ;
    [prog_i] ].
(* /ADMITDEF *)
(* HIDE *)

Fixpoint eqb_aexp (a1 a2 : aexp) : bool :=
  match a1, a2 with
  | ANum n1, ANum n2 => n1 =? n2
  | AId x1, AId x2 => eqb_string x1 x2
  | <{ a11 + a12 }>, <{ a21 + a22 }> =>
    eqb_aexp a11 a21 && eqb_aexp a12 a22
  | <{ a11 - a12 }>, <{ a21 - a22 }> =>
    eqb_aexp a11 a21 && eqb_aexp a12 a22
  | <{ a11 * a12 }>, <{ a21 * a22 }> =>
    eqb_aexp a11 a21 && eqb_aexp a12 a22
  | _, _ => false
  end.

Lemma eqb_aexp_true_iff :
  forall a1 a2, eqb_aexp a1 a2 = true <-> a1 = a2.
Proof.
  intros a1.
  induction a1 as [n1|x1|a11 IH1 a12 IH2|a11 IH1 a12 IH2|a11 IH1 a12 IH2];
  intros [n2|x2|a21 a22|a21 a22|a21 a22];
  simpl;
  try solve [ intuition congruence
            | rewrite andb_true_iff, IH1, IH2; intuition congruence ].
  - rewrite eqb_eq. intuition congruence.
  - rewrite eqb_string_true_iff. intuition congruence.
Qed.

Fixpoint eqb_bexp (b1 b2 : bexp) : bool :=
  match b1, b2 with
  | <{true}>, <{true}> => true
  | <{false}>, <{false}> => true
  | <{ a11 = a12 }>, <{ a21 = a22 }> =>
    eqb_aexp a11 a21 && eqb_aexp a12 a22
  | <{ a11 <= a12 }>, <{ a21 <= a22 }> =>
    eqb_aexp a11 a21 && eqb_aexp a12 a22
  | <{ ~ b11 }>, <{ ~ b21 }> => eqb_bexp b11 b21
  | <{ b11 && b12 }>, <{ b21 && b22 }> =>
    eqb_bexp b11 b21 && eqb_bexp b12 b22
  | _, _ => false
  end.

Lemma eqb_bexp_true_iff :
  forall b1 b2, eqb_bexp b1 b2 = true <-> b1 = b2.
Proof.
  intros b1.
  induction b1 as [| |b11 b12|b11 b12|b11 IH|b11 IH1 b12 IH2];
  intros [| |b21 b22|b21 b22|b21|b21 b22];
  simpl;
  try solve [ intuition congruence
            | rewrite andb_true_iff, eqb_aexp_true_iff, eqb_aexp_true_iff;
              intuition congruence ].
  - rewrite IH. intuition congruence.
  - rewrite andb_true_iff, IH1, IH2. intuition congruence.
Qed.

Fixpoint eqb_com (c1 c2 : com) : bool :=
  match c1, c2 with
  | CSkip, CSkip => true
  | CAss x1 a1, CAss x2 a2 =>
    eqb_string x1 x2 && eqb_aexp a1 a2
  | CSeq c11 c12, CSeq c21 c22 =>
    eqb_com c11 c21 && eqb_com c12 c22
  | CIf b1 c11 c12, CIf b2 c21 c22 =>
    eqb_bexp b1 b2 && eqb_com c11 c21 && eqb_com c12 c22
  | CWhile b1 c11, CWhile b2 c21 =>
    eqb_bexp b1 b2 && eqb_com c11 c21
  | _, _ => false
  end.

Lemma eqb_com_true_iff :
  forall c1 c2, eqb_com c1 c2 = true <-> c1 = c2.
Proof.
  intros c1.
  induction c1 as [|x1 e1|c11 IH1 c12 IH2|e1 c11 IH1 c12 IH2|e1 c1 IH];
  intros [|x2 e2|c21 c22|e2 c21 c22|e2 c2];
  simpl;
  try solve [ intuition congruence ]; repeat rewrite andb_true_iff.
  - rewrite eqb_string_true_iff. rewrite eqb_aexp_true_iff. intuition congruence.
  - rewrite IH1, IH2. intuition congruence.
  - rewrite eqb_bexp_true_iff, IH1, IH2. intuition congruence.
  - rewrite eqb_bexp_true_iff, IH. intuition congruence.
Qed.

Fixpoint remove_if_unique {A} (p : A -> bool) (l : list A) : option (list A) :=
  match l with
  | nil => None
  | a :: l => if p a then
                match remove_if_unique p l with
                | Some l' => None
                | None => Some l
                end
              else
                match remove_if_unique p l with
                | Some l' => Some (a :: l')
                | None => None
                end
  end.

Fixpoint list_equiv {A} (r : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1 with
  | nil => match l2 with | nil => true | _ => false end
  | a :: l1 => match remove_if_unique (r a) l2 with
               | Some l2 => list_equiv r l1 l2
               | None => false
               end
  end.

Definition check_equiv_classes : list (list com) -> bool :=
  list_equiv (list_equiv eqb_com) equiv_classes.
(* /HIDE *)

(* GRADE_MANUAL 2: equiv_classes *)


(* ####################################################### *)
(** * Properties of Behavioral Equivalence *)

(** We next consider some fundamental properties of program
    equivalence. *)

(* ####################################################### *)
(** ** Behavioral Equivalence Is an Equivalence *)

(** First, we verify that the equivalences on `aexps`, `bexps`, and
    `com`s really are _equivalences_ — i.e., that they are reflexive,
    symmetric, and transitive.  The proofs are all easy. *)

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  intros a st. reflexivity.  Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  intros a1 a2 H. intros st. symmetry. apply H.  Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  unfold bequiv. intros b st. reflexivity.  Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H.  Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

Lemma refl_cequiv : forall (c : com), cequiv c c.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  unfold cequiv. intros c st st'. reflexivity.  Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  rewrite H. reflexivity.
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  rewrite H12. apply H23.
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(* ######################################################## *)
(** ** Behavioral Equivalence Is a Congruence *)

(* SOONER: BCP 19: One question that comes up practically every year
   is "What is an example of a program equivalence that is not a
   congruence?"  This section should address that question.

     - A simple but contrived example: If c = skip and d = skip;;skip,
       then

          E = { (c,c), (c,d), (d,c), (d,d) }

       is certainly a congruence.  But

          (skip;;c, skip;;d)

       is not in E, so E is not a congruence.

    - A more realistic and less contrived example: The relation

          { (c,d) | d can be obtained from c by permuting the names of
                    variables }

      is an equivalence but not a congruence.

   Put one or both of these in the text (and/or exercises).
*)
(** Less obviously, behavioral equivalence is also a _congruence_.
    That is, the equivalence of two subprograms implies the
    equivalence of the larger programs in which they are embedded:
[[[
                 aequiv a a'
         -------------------------
         cequiv (x := a) (x := a')

              cequiv c1 c1'
              cequiv c2 c2'
         --------------------------
         cequiv (c1;c2) (c1';c2')
]]]
    ... and so on for the other forms of commands. *)

(** FULL: (Note that we are using the inference rule notation here not
    as part of a definition, but simply to write down some valid
    implications in a readable format. We prove these implications
    below.) *)

(** FULL: We will see a concrete example of why these congruence
    properties are important in the following section (in the proof of
    `fold_constants_com_sound`), but the main idea is that they allow
    us to replace a small part of a large program with an equivalent
    small part and know that the whole large programs are equivalent
    _without_ doing an explicit proof about the non-varying parts --
    i.e., the "proof burden" of a small change to a large program is
    proportional to the size of the change, not the program. *)
(** TERSE: *** *)
(** TERSE: These properties allow us to reason that a large program
    behaves the same when we replace a small part with something
    equivalent. *)

Theorem CAss_congruence : forall x a a',
  aequiv a a' ->
  cequiv <{x := a}> <{x := a'}>.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  intros x a a' Heqv st st'.
  split; intros Hceval.
  - (* -> *)
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.
  - (* <- *)
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.  Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(** FULL: The congruence property for loops is a little more interesting,
    since it requires induction.

    _Theorem_: Equivalence is a congruence for `while` — that is, if
    `b` is equivalent to `b'` and `c` is equivalent to `c'`, then
    `while b do c end` is equivalent to `while b' do c' end`.

    _Proof_: Suppose `b` is equivalent to `b'` and `c` is
    equivalent to `c'`.  We must show, for every `st` and `st'`, that
    `st =[ while b do c end ]=> st'` iff `st =[ while b' do c' end ]=> st'`.  We consider the two directions separately.

      - (`→`) We show that `st =[ while b do c end ]=> st'` implies
        `st =[ while b' do c' end ]=> st'`, by induction on a
        derivation of `st =[ while b do c end ]=> st'`.  The only
        nontrivial cases are when the final rule in the derivation is
        `E_WhileFalse` or `E_WhileTrue`.

          - `E_WhileFalse`: In this case, the form of the rule gives us
            `beval st b = false` and `st = st'`.  But then, since
            `b` and `b'` are equivalent, we have `beval st b' = false`, and `E_WhileFalse` applies, giving us
            `st =[ while b' do c' end ]=> st'`, as required.

          - `E_WhileTrue`: The form of the rule now gives us `beval st b = true`, with `st =[ c ]=> st'0` and `st'0 =[ while b do c end ]=> st'` for some state `st'0`, with the
            induction hypothesis `st'0 =[ while b' do c' end ]=> st'`.

            Since `c` and `c'` are equivalent, we know that `st =[ c' ]=> st'0`.  And since `b` and `b'` are equivalent,
            we have `beval st b' = true`.  Now `E_WhileTrue` applies,
            giving us `st =[ while b' do c' end ]=> st'`, as
            required.

      - (`←`) Similar. [] *)

Theorem CWhile_congruence : forall b b' c c',
  bequiv b b' -> cequiv c c' ->
  cequiv <{ while b do c end }> <{ while b' do c' end }>.
Proof.
  (* WORKINCLASS *)

  (* We will prove one direction in an "assert"
     in order to reuse it for the converse. *)
  assert (A: forall (b b' : bexp) (c c' : com) (st st' : state),
             bequiv b b' -> cequiv c c' ->
             st =[ while b do c end ]=> st' ->
             st =[ while b' do c' end ]=> st').
  { unfold bequiv,cequiv.
    intros b b' c c' st st' Hbe Hc1e Hce.
    remember <{ while b do c end }> as cwhile
      eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + (* E_WhileFalse *)
      apply E_WhileFalse. rewrite <- Hbe. apply H.
    + (* E_WhileTrue *)
      apply E_WhileTrue with (st' := st').
      * (* show loop runs *) rewrite <- Hbe. apply H.
      * (* body execution *)
        apply (Hc1e st st').  apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity. }

  intros. split.
  - apply A; assumption.
  - apply A.
    + apply sym_bequiv. assumption.
    + apply sym_cequiv. assumption.
Qed.
(* /WORKINCLASS *)

(* FULL: EX3? (CSeq_congruence) *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ c1;c2 }> <{ c1';c2' }>.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  (* ADMITTED *)
  unfold cequiv. intros c1 c1' c2 c2' Hc1 Hc2 st st'.
  split; intros Hc; inversion Hc; subst.
  - (* -> *)
    apply E_Seq with (st' := st'0).
    + (* c1 *)
      apply (Hc1 st st'0). assumption.
    + (* c2 *)
      apply (Hc2 st'0 st'). assumption.
  - (* <- *)
    apply E_Seq with (st' := st'0).
    + (* c1 *)
      apply (Hc1 st st'0). assumption.
    + (* c2 *)
      apply (Hc2 st'0 st').  assumption.  Qed.
(* /ADMITTED *)
(** FULL: [] *)
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(* FULL: EX3 (CIf_congruence) *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ if b then c1 else c2 end }>
         <{ if b' then c1' else c2' end }>.
(* TERSE: HIDEFROMHTML *)
Proof.
  (* ADMITTED *)
  unfold bequiv,cequiv.
  intros b b' c1 c1' c2 c2' Hbe Hc1e Hc2e st st'.
  split; intros Hce.
  - (* -> *)
    inversion Hce; subst.
    + (* E_IfTrue *)
      rewrite -> Hbe in H4. apply Hc1e in H5.
      apply E_IfTrue; assumption.
    + (* E_IfFalse *)
      rewrite -> Hbe in H4. apply Hc2e in H5.
      apply E_IfFalse; assumption.
  - (* <- *)
    inversion Hce; subst.
    + (* E_IfTrue *)
      rewrite <- Hbe in H4. apply Hc1e in H5.
      apply E_IfTrue; assumption.
    + (* E_IfFalse *)
      rewrite <- Hbe in H4. apply Hc2e in H5.
      apply E_IfFalse; assumption.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: CIf_congruence *)
(** FULL: [] *)
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)

(** For example, here are two equivalent programs and a proof of their
    equivalence... *)

Example congruence_example:
  cequiv
    (* Program 1: *)
    <{ X := 0;
       if (X = 0)
       then
         Y := 0
       else
         Y := 42
       end }>
    (* Program 2: *)
    <{ X := 0;
       if (X = 0)
       then
         Y := X - X   (* <--- Changed here *)
       else
         Y := 42
       end }>.
Proof.
  apply CSeq_congruence.
  - apply refl_cequiv.
  - apply CIf_congruence.
    + apply refl_bequiv.
    + apply CAss_congruence. unfold aequiv. simpl.
      symmetry. apply minus_diag.
    + apply refl_cequiv.
Qed.


(* EX3A? (not_congr) *)
(** We've shown that the `cequiv` relation is both an equivalence and
    a congruence on commands.  Can you think of a relation on commands
    that is an equivalence but _not_ a congruence? *)

(* SOLUTION *)

(** Here's one: *)

Reserved Notation "c1 ~~~ c2" (at level 80).

Inductive weirdrel : com -> com -> Prop :=
| w_refl : forall c1, c1 ~~~ c1
| w_symm : forall c1 c2, c1 ~~~ c2 -> c2 ~~~ c1
| w_trans : forall c1 c2 c3, c1 ~~~ c2 -> c2 ~~~ c3 -> c1 ~~~ c3
| w_weird : <{ skip }> ~~~ <{ X := X }>

where "c1 ~~~ c2" := (weirdrel c1 c2).

(* /SOLUTION *)

(* LATER: Ori: perhaps another (more meaningful?) solution:
  c1 ~ c2 iff (both terminate) or (both do not terminate) ?
*)



(* ####################################################### *)
(** * Program Transformations *)

(** A _program transformation_ is a function that takes a program as
    input and produces some variant of the program as output.
    Compiler optimizations such as constant folding are a canonical
    example, but there are many others. *)

(** A program transformation is _sound_ if it preserves the
    behavior of the original program. *)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

(* ######################################################## *)
(** ** The Constant-Folding Transformation *)

(** An expression is _constant_ when it contains no variable
    references.

    Constant folding is an optimization that finds constant
    expressions and replaces them by their values. *)

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId x        => AId x
  | <{ a1 + a2 }>  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => <{ a1' + a2' }>
    end
  | <{ a1 - a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => <{ a1' - a2' }>
    end
  | <{ a1 * a2 }>  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => <{ a1' * a2' }>
    end
  end.

(** TERSE: *** *)

Example fold_aexp_ex1 :
    fold_constants_aexp <{ (1 + 2) * X }>
  = <{ 3 * X }>.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(** Note that this version of constant folding doesn't eliminate
    trivial additions, etc. — we are focusing attention on a single
    optimization for the sake of simplicity.  It is not hard to
    incorporate other ways of simplifying expressions; the definitions
    and proofs just get longer. *)

Example fold_aexp_ex2 :
  fold_constants_aexp <{ X - ((0 * 6) + Y) }> = <{ X - (0 + Y) }>.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)
(** Not only can we lift `fold_constants_aexp` to `bexp`s (in the
    `BEq` and `BLe` cases); we can also look for constant _boolean_
    expressions and evaluate them in-place. *)

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | <{true}>        => <{true}>
  | <{false}>       => <{false}>
  | <{ a1 = a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' = a2' }>
      end
  | <{ a1 <= a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <= a2' }>
      end
  | <{ ~ b1 }>  =>
      match (fold_constants_bexp b1) with
      | <{true}> => <{false}>
      | <{false}> => <{true}>
      | b1' => <{ ~ b1' }>
      end
  | <{ b1 && b2 }>  =>
      match (fold_constants_bexp b1,
             fold_constants_bexp b2) with
      | (<{true}>, <{true}>) => <{true}>
      | (<{true}>, <{false}>) => <{false}>
      | (<{false}>, <{true}>) => <{false}>
      | (<{false}>, <{false}>) => <{false}>
      | (b1', b2') => <{ b1' && b2' }>
      end
  end.

(** TERSE: *** *)

Example fold_bexp_ex1 :
  fold_constants_bexp <{ true && ~(false && true) }>
  = <{ true }>.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

Example fold_bexp_ex2 :
  fold_constants_bexp <{ (X = Y) && (0 = (2 - (1 + 1))) }>
  = <{ (X = Y) && true }>.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)
(** To fold constants in a command, we apply the appropriate folding
    functions on all embedded expressions. *)

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | <{ skip }> =>
      <{ skip }>
  | <{ x := a }> =>
      <{ x := (fold_constants_aexp a) }>
  | <{ c1 ; c2 }>  =>
      <{ fold_constants_com c1 ; fold_constants_com c2 }>
  | <{ if b then c1 else c2 end }> =>
      match fold_constants_bexp b with
      | <{true}>  => fold_constants_com c1
      | <{false}> => fold_constants_com c2
      | b' => <{ if b' then fold_constants_com c1
                       else fold_constants_com c2 end}>
      end
  | <{ while b do c1 end }> =>
      match fold_constants_bexp b with
      | <{true}> => <{ while true do skip end }>
      | <{false}> => <{ skip }>
      | b' => <{ while b' do (fold_constants_com c1) end }>
      end
  end.

(** TERSE: *** *)
Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    <{ X := 4 + 5;
       Y := X - 3;
       if ((X - Y) = (2 + 4)) then skip
       else Y := 0 end;
       if (0 <= (4 - (2 + 1))) then Y := 0
       else skip end;
       while (Y = 0) do
         X := X + 1
       end }>
  = (* After constant folding: *)
    <{ X := 9;
       Y := X - 3;
       if ((X - Y) = 6) then skip
       else Y := 0 end;
       Y := 0;
       while (Y = 0) do
         X := X + 1
       end }>.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(* ################################################### *)
(** ** Soundness of Constant Folding *)

(** Now we need to show that what we've done is correct. *)

(** FULL: Here's the proof for arithmetic expressions: *)

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  induction a; simpl;
    (* ANum and AId follow immediately *)
    try reflexivity;
    (* APlus, AMinus, and AMult follow from the IH
       and the observation that
              aeval st (<{ a1 + a2 }>)
            = ANum ((aeval st a1) + (aeval st a2))
            = aeval st (ANum ((aeval st a1) + (aeval st a2)))
       (and similarly for AMinus/minus and AMult/mult) *)
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity). Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)


(* EX3? (fold_bexp_Eq_informal) *)
(** Here is an informal proof of the `BEq` case of the soundness
    argument for boolean expression constant folding.  Read it
    carefully and compare it to the formal proof that follows.  Then
    fill in the `BLe` case of the formal proof (without looking at the
    `BEq` case, if possible).

   _Theorem_: The constant folding function for booleans,
   `fold_constants_bexp`, is sound.

   _Proof_: We must show that `b` is equivalent to `fold_constants_bexp b`,
   for all boolean expressions `b`.  Proceed by induction on `b`.  We
   show just the case where `b` has the form `a1 = a2`.

   In this case, we must show
{[
       beval st <{ a1 = a2 }>
     = beval st (fold_constants_bexp <{ a1 = a2 }>).
]]
   There are two cases to consider:

     - First, suppose `fold_constants_aexp a1 = ANum n1` and
       `fold_constants_aexp a2 = ANum n2` for some `n1` and `n2`.

       In this case, we have
[[
           fold_constants_bexp [[ a1 = a2 ]]
         = if n1 =? n2 then <{true}> else <{false}>
]]
       and
[[
           beval st <{a1 = a2}>
         = (aeval st a1) =? (aeval st a2).
]]
       By the soundness of constant folding for arithmetic
       expressions (Lemma `fold_constants_aexp_sound`), we know
[[
           aeval st a1
         = aeval st (fold_constants_aexp a1)
         = aeval st (ANum n1)
         = n1
]]
       and
[[
           aeval st a2
         = aeval st (fold_constants_aexp a2)
         = aeval st (ANum n2)
         = n2,
]]
       so
[[
           beval st <{a1 = a2}>
         = (aeval a1) =? (aeval a2)
         = n1 =? n2.
]]
       Also, it is easy to see (by considering the cases `n1 = n2` and
       `n1 <> n2` separately) that
[[
           beval st (if n1 =? n2 then <{true}> else <{false}>)
         = if n1 =? n2 then beval st <{true}> else beval st <{false}>
         = if n1 =? n2 then true else false
         = n1 =? n2.
]]
       So
[[
           beval st (<{ a1 = a2 }>)
         = n1 =? n2.
         = beval st (if n1 =? n2 then <{true}> else <{false}>),
]]
       as required.

     - Otherwise, one of `fold_constants_aexp a1` and
       `fold_constants_aexp a2` is not a constant.  In this case, we
       must show
[[
           beval st <{a1 = a2}>
         = beval st (<{ (fold_constants_aexp a1) =
                         (fold_constants_aexp a2) }>),
]]
       which, by the definition of `beval`, is the same as showing
[[
           (aeval st a1) =? (aeval st a2)
         = (aeval st (fold_constants_aexp a1)) =?
                   (aeval st (fold_constants_aexp a2)).
]]
       But the soundness of constant folding for arithmetic
       expressions (`fold_constants_aexp_sound`) gives us
[[
         aeval st a1 = aeval st (fold_constants_aexp a1)
         aeval st a2 = aeval st (fold_constants_aexp a2),
]]
       completing the case.  [] *)


Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
(* TERSE: HIDEFROMHTML *)
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* true and false are immediate *)
    try reflexivity.
  - (* BEq *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n =? n0); reflexivity.
  - (* BLe *)
    (* ADMIT *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    (* a slightly alternative approach using asserts: *)
    assert (aeval st a1 = aeval st a1') as H1. {
      subst a1'. apply fold_constants_aexp_sound. }
    assert (aeval st a2 = aeval st a2') as H2. {
      subst a2'. apply fold_constants_aexp_sound. }
    rewrite H1. rewrite H2.
    destruct a1'; destruct a2'; try reflexivity.
      (* Again, the only interesting case is when both a1 and a2
          become constants after folding *)
      simpl. destruct (n <=? n0); reflexivity.
    (* /ADMIT *)
  - (* BNot *)
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
(* ADMITTED *)
Qed.
(* /ADMITTED *)
(* TERSE: /HIDEFROMHTML *)


(* HIDE: compressed version of above [is this useful? -BCP]

    unfold btrans_sound; unfold bequiv.
    induction b; intros;
    try reflexivity;
    try
      (simpl;
       remember (fold_constants_aexp a) as a';
       remember (fold_constants_aexp a0) as a0';
       assert (aeval st a = aeval st a') as Ha;
       assert (aeval st a0 = aeval st a0') as Ha0;
         try (subst; apply fold_constants_aexp_sound);
       destruct a'; destruct a0'; rewrite Ha; rewrite Ha0;
       simpl; (try destruct (n =? n0)); (try destruct (n <=? n0));
       reflexivity);
    try (simpl; destruct (fold_constants_bexp b); rewrite IHb; reflexivity);
    try (simpl; destruct (fold_constants_bexp b1);
         destruct (fold_constants_bexp b2);
         rewrite IHb1; rewrite IHb2; reflexivity). *)


(* EX3 (fold_constants_com_sound) *)
(** Complete the `while` case of the following proof. *)


Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
(* TERSE: HIDEFROMHTML *)
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* skip *) apply refl_cequiv.
  - (* := *) apply CAss_congruence.
              apply fold_constants_aexp_sound.
  - (* ; *) apply CSeq_congruence; assumption.
  - (* if *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
      (* (If the optimization doesn't eliminate the if, then the
          result is easy to prove from the IH and
          `fold_constants_bexp_sound`.) *)
    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply if_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply if_false; assumption.
  - (* while *)
    (* ADMITTED *)
    assert (bequiv b (fold_constants_bexp b)).
    { (* Pf of assertion *) apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      (* Again, the cases where `fold_constants_com` doesn't change
          the test or don't change the loop body follow from the IH
          and `fold_constants_bexp_sound` *)
      try (apply CWhile_congruence; assumption).
    + (* b always true *)
      apply while_true; assumption.
    + (* b always false *)
      apply while_false; assumption.  Qed.
(* /ADMITTED *)
(* TERSE: /HIDEFROMHTML *)

(* GRADE_THEOREM 3: fold_constants_com_sound *)



(* ########################################################## *)
(** *** Soundness of (0 + n) Elimination, Redux *)

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
   constants (using `fold_constants_com`) and then eliminates `0 + n`
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
  | <{ c1 ; c2 }>                  => <{ optimize0plus_com c1 ;
                                         optimize0plus_com c2 }>
  | <{ if b then c1 else c2 end }> =>
     <{ if (optimize0plus_bexp b)
        then (optimize0plus_com c1)
        else (optimize0plus_com c2)
        end }>
  | <{ while b do c1 end }>         => <{ while (optimize0plus_bexp b) do
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
  intros st st'; simpl.
  - (* skip *)
    apply refl_cequiv.
  - (* := *)
    apply CAss_congruence.
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

Definition optimizer (c : com) := optimize0plus_com (fold_constants_com c).

Theorem optimizer_sound :
  ctrans_sound optimizer.
Proof.
  unfold ctrans_sound. unfold optimizer.
  intros c.
  apply trans_cequiv with (fold_constants_com c).
  apply fold_constants_com_sound.
  apply optimize0plus_com_sound.  Qed.
(* /SOLUTION *)


(* ####################################################### *)
(** * Proving Inequivalence *)

(** Suppose that `c1` is a command of the form `X := a1; Y := a2`
    and `c2` is the command `X := a1; Y := a2'`, where `a2'` is
    formed by substituting `a1` for all occurrences of `X` in `a2`.
    For example, `c1` and `c2` might be:
[[
       c1  =  (X := 42 + 53;
               Y := Y + X)
       c2  =  (X := 42 + 53;
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
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof. simpl. (* KK: For some reason this fails... Is it an associativity issue? *)
       Admitted.
       (* reflexivity.  Qed. *)
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

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
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  unfold subst_equiv_property.
  intros Contra.

  (* Here is the counterexample: assuming that `subst_equiv_property`
     holds allows us to prove that these two programs are
     equivalent... *)
  remember <{ X := X + 1;
              Y := X }>
      as c1.
  remember <{ X := X + 1;
              Y := X + 1 }>
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).
  clear Contra.

  (* ... allows us to show that the command `c2` can terminate
     in two different final states:
        st1 = (Y !-> 1 ; X !-> 1)
        st2 = (Y !-> 2 ; X !-> 1). *)
  remember (Y !-> 1 ; X !-> 1) as st1.
  remember (Y !-> 2 ; X !-> 1) as st2.
  assert (H1 : empty_st =[ c1 ]=> st1);
  assert (H2 : empty_st =[ c2 ]=> st2);
  try (subst;
       apply E_Seq with (st' := (X !-> 1));
       apply E_Ass; reflexivity).
  clear Heqc1 Heqc2.

  apply H in H1.
  clear H.

  (* Finally, we use the fact that evaluation is deterministic
     to obtain a contradiction. *)
  assert (Hcontra : st1 = st2)
    by (apply (ceval_deterministic c2 empty_st); assumption).
  clear H1 H2.

  assert (Hcontra' : st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. discriminate. Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)


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

Lemma aeval_weakening : forall x st a ni,
  var_not_used_in_aexp x a ->
  aeval (x !-> ni ; st) a = aeval st a.
Proof.
  (* ADMITTED *)
  intros x st a.
  induction a; intros nx Hx;
    (* the binary operators follow from the IH *)
    try (simpl; inversion Hx; subst;
         rewrite IHa1; try assumption;
         rewrite IHa2; try assumption;
         reflexivity).
  - (* ANum *)
    reflexivity.
  - (* AId *)
    inversion Hx; subst. simpl.
    apply t_update_neq. assumption. Qed.
  (* /ADMITTED *)

(** Using `var_not_used_in_aexp`, formalize and prove a correct version
    of `subst_equiv_property`. *)

(* SOLUTION *)
Lemma aeval_subst : forall x st a1 a2,
  var_not_used_in_aexp x a1 ->
  aeval (x !-> aeval st a1 ; st) a2 =
  aeval (x !-> aeval st a1 ; st) (subst_aexp x a1 a2).
Proof.
  intros x st a1 a2 Hi.
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
    apply E_Seq with st'0; try assumption.
    inversion H4; subst. apply E_Ass.
    inversion H1; subst. symmetry. apply aeval_subst.
    assumption.
  - (* <- *)
    inversion Hce; subst.
    apply E_Seq with st'0.
    assumption.
    inversion H4; subst. apply E_Ass.
    inversion H1; subst. apply aeval_subst.
    assumption.  Qed.
(* /SOLUTION *)

(* EX3 (inequiv_exercise) *)
(** Prove that an infinite loop is not equivalent to `skip` *)

Theorem inequiv_exercise:
  ~ cequiv <{ while true do skip end }> <{ skip }>.
Proof.
  (* ADMITTED *)
  intros Contra.
  assert (~(empty_st =[ while true do skip end ]=> empty_st)) as H.
  { apply while_true_nonterm. apply refl_bequiv. }
  apply H.
  apply (Contra empty_st empty_st).
  apply E_Skip. Qed.
(* /ADMITTED *)



(* ################################################################## *)
(** * Extended Exercise: Nondeterministic Imp *)

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

(* EX2 (himp_ceval) *)
(** Now, we must extend the operational semantics. We have provided
   a template for the `ceval` relation below, specifying the big-step
   semantics. What rule(s) must be added to the definition of `ceval`
   to formalize the behavior of the `HAVOC` command? *)

(* INSTRUCTORS: Copy of template eval *)
Reserved Notation "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99, st constr,
          st' constr at next level).

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
  | E_Havoc : forall (st : state) (X : string) (n : nat),
      st =[ havoc X ]=> (X !-> n ; st)
(* /SOLUTION *)

  where "st =[ c ]=> st'" := (ceval c st st').

(** As a sanity check, the following claims should be provable for
    your definition: *)

Example havoc_example1 : empty_st =[ havoc X ]=> (X !-> 0).
Proof.
(* ADMITTED *)
  constructor. Qed.
(* /ADMITTED *)

Example havoc_example2 :
  empty_st =[ skip; havoc Z ]=> (Z !-> 42).
Proof.
(* ADMITTED *)
  eapply E_Seq; constructor. Qed.
(* /ADMITTED *)

(* GRADE_MANUAL 2: Check_rule_for_HAVOC *)

(** Finally, we repeat the definition of command equivalence from above: *)

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  st =[ c1 ]=> st' <-> st =[ c2 ]=> st'.

(** Let's apply this definition to prove some nondeterministic
    programs equivalent / inequivalent. *)

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
  forall X Y st st',
    st =[ havoc X; havoc Y ]=> st' ->
    st =[ havoc Y; havoc X ]=> st'.
Proof.
  intros X Y st st' H.
  destruct (eqb_stringP X Y) as [Hid | Hid].
  - (* X = Y *)
    subst.  assumption.
  - (* X <> Y *)
    inversion H; subst; clear H.
    inversion H2; subst; clear H2.
    inversion H5; subst; clear H5.
    apply E_Seq with (st' := (Y !-> n0 ; st)). constructor.
    rewrite t_update_permute.
    constructor. assumption.
Qed.
(* /QUIETSOLUTION *)

Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~cequiv pXY pYX.
Proof. (* ADMITTED *)
  left. intros st st'.
  split; apply pXY_approx_pYX; reflexivity.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: Himp.pXY_cequiv_pYX *)

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
Proof. (* ADMITTED *)
  right. intro Hc. unfold cequiv in Hc.
  assert (empty_st =[ ptwice ]=> (Y !-> 1 ; X !-> 0)).
    apply E_Seq with (X !-> 0); constructor.
  rewrite Hc in H. inversion H. inversion H2. inversion H5. subst.
  simpl in H13. rewrite t_update_eq in H13.
  (* LATER: This trick with `f_equal` is non-evident but highly
     useful to process contradictory equalities on functions.
     See `p3_p4_inequiv` for a more drastic reduction in code. *)
  assert (H0 : n = 1).
  { apply (f_equal (fun st => st Y)) in H13.
    apply H13. }
  assert (H1 : n = 0).
  { apply (f_equal (fun st => st X)) in H13.
    apply H13. }
  rewrite H0 in H1. discriminate.
Qed.
(* /ADMITTED *)

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

(* GRADE_THEOREM 3: Himp.p1_may_diverge *)
Lemma p1_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p1 ]=> st'.
Proof. (* ADMITTED *)
  intros. intros Hcontra.
  remember p1 as p1' eqn:Heqp1'. remember st' as st'' eqn:Heqst''.
  induction Hcontra; inversion Heqp1'.
  - (* E_WhileFalse *) subst. simpl in H0.
    apply negb_false_iff in H0. apply eqb_eq in H0.
    apply H in H0. assumption.
  - (* E_WhileTrue *) subst. apply IHHcontra2; try reflexivity.
    inversion Hcontra1. subst.
    inversion H3; subst. inversion H6; subst.
    rewrite t_update_eq. simpl. lia.
Qed. (* /ADMITTED *)

(* GRADE_THEOREM 3: Himp.p2_may_diverge *)
Lemma p2_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p2 ]=> st'.
Proof.
(* ADMITTED *)
  intros. intros Hcontra.
  remember p2 as p2' eqn:Heqp2'. remember st' as st'' eqn:Heqst''.
  induction Hcontra; inversion Heqp2'.
  - (* E_WhileFalse *) subst. simpl in H0.
    apply negb_false_iff in H0. apply eqb_eq in H0.
    apply H in H0. assumption.
  - (* E_WhileTrue *) subst. apply IHHcontra2; try reflexivity.
    inversion Hcontra1. subst.
    assumption.
Qed. (* /ADMITTED *)

(* EX4A (p1_p2_equiv) *)
(** Use these two lemmas to prove that `p1` and `p2` are actually
    equivalent. *)

Theorem p1_p2_equiv : cequiv p1 p2.
Proof. (* ADMITTED *)
  split; intros.
  - remember p1 as p1' eqn:Heqp1'.
    destruct H; inversion Heqp1'; subst.
    + (* E_WhileFalse *) apply E_WhileFalse. assumption.
    + (* E_WhileTrue *) apply p1_may_diverge in H1.
      inversion H1.
      simpl in H. apply negb_true_iff in H. apply eqb_neq in H.
      inversion H0; subst. inversion H4; subst. inversion H7; subst.
      rewrite t_update_eq. simpl. lia.
  - remember p2 as p2' eqn:Heqp2'.
    destruct H; inversion Heqp2'; subst.
    + (* E_WhileFalse *) apply E_WhileFalse. assumption.
    + (* E_WhileTrue *) apply p2_may_diverge in H1.
      inversion H1.
      simpl in H. apply negb_true_iff in H. apply eqb_neq in H.
      inversion H0; subst. assumption.
Qed. (* /ADMITTED *)
(* GRADE_THEOREM 6: Himp.p1_p2_equiv *)

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
Proof. (* ADMITTED *)
  intros Hcontra.
  unfold cequiv in Hcontra.
  remember (X !-> 1) as st.
  assert (st =[ p3 ]=> (Z !-> 0 ; X !-> 0 ; Z !-> 1 ; st)).
  - eapply E_Seq. constructor. reflexivity.
    simpl. eapply E_WhileTrue.
    + subst. reflexivity.
    + eapply E_Seq; constructor.
    + apply E_WhileFalse.
      reflexivity.
  - apply Hcontra in H.
    inversion H. subst.
    inversion H2. subst.
    inversion H5. subst.
    simpl in H6.
    apply (f_equal (fun st => st Z)) in H6.
    discriminate H6.
Qed. (* /ADMITTED *)
(* GRADE_THEOREM 6: Himp.p3_p4_inequiv *)

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
    that `st =[ p5 ]=> st'`, the answer to the question
    "Does `st =[ p6 ]=> st'`?"  is "Yes".

    `←` (and more controversially): Given that `st =[ p6 ]=> st'` for
    some `st` and `st'`, can we show that `st =[ p5 ]=> st'`? Observe
    that we can use the hypothesis to conclude that
    `st' = (X !-> 1 ; st)`.
    Is there some execution of `p5` starting from `st` which also
    ends up in `st'`? Yes!

    Hence their equivalence. *)

Lemma p5_summary : forall st st',
    st =[ p5 ]=> st' -> st' = (X !-> 1 ; st).
Proof.
  intros. remember p5 as p5' eqn:Heqp5'.
  induction H; inversion Heqp5'; subst.
  - (* E_WhileFalse *)
    simpl in H. apply negb_false_iff in H. apply eqb_eq in H.
    rewrite <- H. rewrite t_update_same. reflexivity.
  - (* E_WhileTrue *)
    apply IHceval2 in Heqp5'.
    inversion H0; subst.
    apply t_update_shadow.
Qed.
(* /QUIETSOLUTION *)

Theorem p5_p6_equiv : cequiv p5 p6.
Proof. (* ADMITTED *)
  split; intros.
  - (* -> *)
    apply p5_summary in H. subst. constructor. reflexivity.
  - (* <- *) inversion H. subst.
    simpl. simpl in H.
    destruct ((st X) =? 1) eqn:Heqb.
    + (* X = 1 *)
      apply eqb_eq in Heqb.
      rewrite <- Heqb.
      rewrite t_update_same.
      apply E_WhileFalse. simpl. rewrite -> Heqb.
      reflexivity.
    + (* X <> 1 *)
      apply E_WhileTrue with (st' := (X !-> 1 ; st)).
      simpl. rewrite Heqb. reflexivity.
      constructor.
      apply E_WhileFalse. reflexivity.
Qed. (* /ADMITTED *)

End Himp.


(* HIDE *)
(* HIDE: BCP 2/16: This whole discussion seems like kind of a
   side-track, especially now that we've built extensionality into the
   earlier chapters even more deeply.  I'm removing it for now.  If
   people prefer to keep it, I wonder whether we could move it to an
   optional chapter by itself... *)

(* ####################################################### *)
(** * Doing Without Extensionality (Optional) *)

(** Purists might object to using the `functional_extensionality`
    axiom as we have here (e.g., in the proof of the `t_update_same`
    lemma).  In general, it can be dangerous to add axioms willy
    nilly, particularly several at once (as they may be mutually
    inconsistent). In fact, it is known that
    `functional_extensionality` and `excluded_middle` can both be
    assumed without any problems; nevertheless, some Coq users prefer
    to avoid such "heavyweight" general techniques and instead try to
    craft solutions for specific problems that stay within Coq's
    built-in logic.

    For our particular problem here, rather than extending the
    definition of equality to do what we want on functions
    representing states, we could instead give an explicit notion of
    _equivalence_ on states.  For example: *)

Definition stequiv (st1 st2 : state) : Prop :=
  forall (x : string), st1 x = st2 x.

Notation "st1 '~~' st2" := (stequiv st1 st2) (at level 30).

(** It is easy to prove that `stequiv` is an _equivalence_ (i.e., it
   is reflexive, symmetric, and transitive), so it partitions the set
   of all states into equivalence classes. *)

(* EX1? (stequiv_refl) *)
Lemma stequiv_refl : forall (st : state),
  st ~~ st.
Proof.
  (* ADMITTED *)
  unfold stequiv. intros. reflexivity. Qed.
  (* /ADMITTED *)

(* EX1? (stequiv_sym) *)
Lemma stequiv_sym : forall (st1 st2 : state),
  st1 ~~ st2 ->
  st2 ~~ st1.
Proof.
  (* ADMITTED *)
  unfold stequiv. intros. rewrite H. reflexivity. Qed.
  (* /ADMITTED *)

(* EX1? (stequiv_trans) *)
Lemma stequiv_trans : forall (st1 st2 st3 : state),
  st1 ~~ st2 ->
  st2 ~~ st3 ->
  st1 ~~ st3.
Proof.
  (* ADMITTED *)
  unfold stequiv. intros.  rewrite H. rewrite H0. reflexivity.  Qed.
  (* /ADMITTED *)

(** Another useful fact... *)
(* EX1? (stequiv_t_update) *)
Lemma stequiv_t_update : forall (st1 st2 : state),
  st1 ~~ st2 ->
  forall (X:string) (n:nat),
  (X !-> n ; st1) ~~ (X !-> n ; st2).
Proof.
  (* ADMITTED *)
  unfold stequiv. intros. 
  destruct (eqb_stringP X x) as [Hid | Hid].
  - subst. rewrite t_update_eq. rewrite t_update_eq. reflexivity.
  - rewrite t_update_neq; [|assumption].
    rewrite t_update_neq; [|assumption].
    auto. Qed.
  (* /ADMITTED *)

(** It is then straightforward to show that [aeval] and `beval` behave
    uniformly on all members of an equivalence class: *)

(* EX2? (stequiv_aeval) *)
Lemma stequiv_aeval : forall (st1 st2 : state),
  st1 ~~ st2 ->
  forall (a:aexp), aeval st1 a = aeval st2 a.
Proof.
  (* ADMITTED *)
  intros.
  induction a; simpl; try rewrite IHa1; try rewrite IHa2; try reflexivity.
  apply H. Qed. (* /ADMITTED *)

(* EX2? (stequiv_beval) *)
Lemma stequiv_beval : forall (st1 st2 : state),
  st1 ~~ st2 ->
  forall (b:bexp), beval st1 b = beval st2 b.
Proof.
  (* ADMITTED *)
  intros.
  induction b; simpl; try reflexivity.
  - (* BEq *)
   repeat rewrite (stequiv_aeval _ _ H). reflexivity.
  - (* BLe *)
   repeat rewrite (stequiv_aeval _ _ H). reflexivity.
  - (* BNot *)
   rewrite IHb. reflexivity.
  - (* BAnd *)
   rewrite IHb1. rewrite IHb2. reflexivity. Qed.
  (* /ADMITTED *)

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
      apply E_IfTrue.  rewrite <- H. symmetry. apply stequiv_beval.
      assumption. assumption. assumption.
  - (* IfFalse *)
    destruct (IHCEV1 st2 STEQV) as [st2' [P EQV] ].
    exists st2'. split.
     apply E_IfFalse. rewrite <- H. symmetry. apply stequiv_beval.
     assumption.  assumption. assumption.
  - (* WhileFalse *)
    exists st2. split.
      apply E_WhileFalse. rewrite <- H. symmetry. apply stequiv_beval.
      assumption. assumption.
  - (* WhileTrue *)
    destruct (IHCEV1_1 st2 STEQV) as [st2' [P1 EQV1] ].
    destruct (IHCEV1_2 st2' EQV1) as [st2'' [P2 EQV2] ].
    exists st2''. split.
      apply E_WhileTrue with st2'.  rewrite <- H. symmetry.
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
Reserved Notation "st '=[' c ']=>'' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval' : com -> state -> state -> Prop :=
  | E_equiv : forall c st st' st'',
    st =[ c ]=> st' ->
    st' ~~ st'' ->
    st =[ c ]=>' st''
  where   "st '=[' c ']=>'' st'" := (ceval' c st st').

(** Now the revised definition of `cequiv'` looks familiar: *)

Definition cequiv' (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=>' st') <-> (st =[ c2 ]=>' st').

(** A sanity check shows that the original notion of command
   equivalence is at least as strong as this new one.  (The converse
   is not true, naturally.) *)

Lemma cequiv__cequiv' : forall (c1 c2: com),
  cequiv c1 c2 -> cequiv' c1 c2.
Proof.
  unfold cequiv, cequiv'; split; intros.
    inversion H0 ; subst.  apply E_equiv with st'0.
    apply (H st st'0); assumption. assumption.
    inversion H0 ; subst.  apply E_equiv with st'0.
    apply (H st st'0). assumption. assumption.
Qed.

(* EX2? (identity_assignment') *)
(** Finally, here is our example once more... Notice that we use the
    `t_update_same_no_ext` lemma in order to avoid invoking functional
    extensionality. (You can complete the proofs.) *)

Theorem t_update_same_no_ext : forall X x1 x2 (m : total_map X),
             (x1 !-> m x1 ; m) x2 = m x2.
Proof.
  (* ADMITTED *)
  intros X x1 x2 m.
  destruct (eqb_stringP x1 x2) as [H | H].
  - (* x1 = x2 *)
    subst. rewrite t_update_same. reflexivity.
  - (* false *)
    rewrite t_update_neq. reflexivity. assumption.  Qed.
(* /ADMITTED *)

Example identity_assignment' :
  cequiv' <{ skip }> <{ X := X }>.
Proof.
    unfold cequiv'.  intros.  split; intros.
    - (* -> *)
      inversion H; subst; clear H. inversion H0; subst.
      apply E_equiv with (X !-> st'0 X ; st'0).
      constructor. { reflexivity. }
      assert ((X !-> st'0 X ; st'0) ~~ st'0) as H.
      { unfold stequiv. intros Y.
        apply t_update_same_no_ext. }
      apply (stequiv_trans _ _ _ H H1).
    - (* <- *)
      (* ADMITTED *)
      inversion H; subst; clear H. inversion H0; subst.
      simpl in H1.
      apply (E_equiv _ st st). { constructor. }
      apply (stequiv_trans _ (X !-> st X ; st)).
      unfold stequiv. intros. rewrite t_update_same_no_ext; reflexivity.
      assumption. Qed. (* /ADMITTED *)

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

(* ####################################### *)

(* For the record, here's how we could use setoids here. I don't think
   this is worth showing, though. *)

(* Require Import Setoid. *)

(* Add Parametric Relation : state stequiv *)
(*   reflexivity proved by stequiv_refl *)
(*   symmetry proved by stequiv_sym *)
(*   transitivity proved by stequiv_trans *)
(*   as stequiv_rel. *)

(* Add Parametric Morphism : t_update with *)
(*   signature stequiv ==> @eq string ==> @eq nat ==> stequiv as t_update_mor. *)
(* exact stequiv_t_update. *)
(* Qed. *)

(* Add Parametric Morphism : aeval with *)
(*   signature stequiv ==> @eq aexp ==> @eq nat as aeval_mor. *)
(* exact stequiv_aeval. *)
(* Qed. *)

(* (* We can redo this proof using setoid rewriting... *) *)
(* Lemma stequiv_beval' : forall (st1 st2 : state), *)
(*   st1 ~~ st2 -> *)
(*   forall (b:bexp), beval st1 b = beval st2 b. *)
(* Proof. *)
(*   intros. induction b; simpl; try reflexivity. *)
(*   rewrite H; reflexivity. *)
(*   rewrite H; reflexivity. *)
(*   rewrite IHb; reflexivity. *)
(*   rewrite IHb1; rewrite IHb2; reflexivity. *)
(* Qed. *)

(* Add Parametric Morphism : beval with *)
(*   signature stequiv ==> @eq bexp ==> @eq bool as beval_mor. *)
(* exact stequiv_beval. *)
(* Qed. *)

(* (* And this one... *) *)
(* Lemma stequiv_ceval': forall (st1 st2 : state), *)
(*   st1 ~~ st2 -> *)
(*   forall (c: com) (st1': state), *)
(*     (st1 =[ c ]=> st1') -> *)
(*     exists st2' : state, *)
(*     ((st2 =[ c ]=> st2') /\  st1' ~~ st2'). *)
(* Proof. *)
(* intros st1 st2 STEQV c st1' CEV1. generalize dependent st2. induction CEV1; intros st2 STEQV. *)
(*   - (* skip *) *)
(*     exists st2. split.  constructor. assumption. *)
(*   - (* := *) *)
(*     exists (t_update st2 x n). split. constructor. *)
(*     rewrite STEQV in H; assumption. rewrite STEQV; reflexivity. *)
(*   - (* ; *) *)
(*     destruct (IHCEV1_1 st2 STEQV) as [st2' [P1 EQV1]]. *)
(*     destruct (IHCEV1_2 st2' EQV1) as [st2'' [P2 EQV2]]. *)
(*     exists st2''.  split.  apply E_Seq with st2'; assumption. assumption. *)
(*   - (* IfTrue *) *)
(*     destruct (IHCEV1 st2 STEQV) as [st2' [P EQV]]. *)
(*     exists st2'.  split. apply E_IfTrue. *)
(*     rewrite STEQV in H; assumption. assumption. assumption. *)
(*   - (* IfFalse *) *)
(*     destruct (IHCEV1 st2 STEQV) as [st2' [P EQV]]. *)
(*     exists st2'. split. apply E_IfFalse. *)
(*     rewrite STEQV in H; assumption. assumption. assumption. *)
(*   - (* WhileFalse *) *)
(*     exists st2. split. apply E_WhileFalse. *)
(*     rewrite STEQV in H; assumption. assumption. *)
(*   - (* WhileTrue *) *)
(*     destruct (IHCEV1_1 st2 STEQV) as [st2' [P1 EQV1]]. *)
(*     destruct (IHCEV1_2 st2' EQV1) as [st2'' [P2 EQV2]]. *)
(*     exists st2''. split. apply E_WhileTrue with st2'. *)
(*     rewrite STEQV in H; assumption. assumption. assumption. assumption. *)
(* Qed. *)

(* Definition eqv (P1 P2 : Prop) := P1 <-> P2. *)

(* Add Parametric Morphism : ceval' with *)
(*    signature (@eq com) ==> stequiv ==> stequiv ==> eqv as ceval_mor. *)
(* intros. split; intro. *)
(*  inversion H1; subst. *)
(*    destruct (stequiv_ceval' _ _ H y  _ H2) as [st [P1 P2]]. *)
(*    apply E_equiv with st. assumption. apply stequiv_trans with st'. *)
(*    symmetry. assumption. *)
(*      apply stequiv_trans with x0;  assumption. *)
(*  inversion H1; subst. *)
(*    symmetry in H. *)
(*    destruct (stequiv_ceval' _ _ H y  _ H2) as [st [P1 P2]]. *)
(*    apply E_equiv with st. assumption. apply stequiv_trans with st'. *)
(*    symmetry. assumption. *)
(*      apply stequiv_trans with y1.   assumption. symmetry. assumption. *)
(* Qed. *)

(* (* The example gets slightly simpler too... *) *)
(* Example identity_assignment'' : *)
(*   cequiv' skip (X ::= X). *)
(* Proof. *)
(*     unfold cequiv'.  intros.  split; intros. *)
(*     - (* -> *) *)
(*       inversion H; subst; clear H. inversion H0; subst. *)
(*       apply E_equiv with (t_update st'0 X (st'0 X)). *)
(*       constructor. reflexivity.  rewrite <- H1.   unfold stequiv. *)
(*       intro. apply t_update_same_no_ext. *)
(*     - (* <- *) *)
(*       inversion H; subst; clear H. inversion H0; subst. *)
(*       simpl in H1.  apply E_equiv with st. *)
(*       constructor.  rewrite <- H1.  unfold stequiv. *)
(*       intro. rewrite t_update_same_no_ext; reflexivity. *)
(* Qed. *)
(* /HIDE *)


(* ####################################################### *)
(** * Additional Exercises *)

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

(* EX3? (swap_noninterfering_assignments) *)
(** (Hint: You'll need `functional_extensionality` for this one.) *)

Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
  l1 <> l2 ->
  var_not_used_in_aexp l1 a2 ->
  var_not_used_in_aexp l2 a1 ->
  cequiv
    <{ l1 := a1; l2 := a2 }>
    <{ l2 := a2; l1 := a1 }>.
Proof.
(* ADMITTED *)
intros l1 l2 a1 a2 NEQ VNU1 VNU2.
  unfold cequiv. intros st st'.
  remember (l1 !-> aeval st a1 ; st) as st1.
  remember (l2 !-> aeval st a2 ; st) as st2.
  assert (aeval st a1 = aeval st2 a1) as AE1.
  { subst st2. rewrite aeval_weakening; try reflexivity; try assumption. }
  assert (aeval st a2 = aeval st1 a2) as AE2.
  { subst st1. rewrite aeval_weakening; try reflexivity; try assumption. }
  assert ((l2 !-> aeval st1 a2 ; st1) =
          (l1 !-> aeval st2 a1 ; st2)) as EQST.
  { rewrite <- AE1.  rewrite <- AE2. subst st1 st2.
    apply t_update_permute. assumption. }
  split; intro.
  - (* -> *)
    inversion H.
    inversion H2.
    inversion H5.
    apply E_Seq with st2; subst.
       apply E_Ass. reflexivity.
       rewrite EQST. apply E_Ass. reflexivity.
  - (* <- *)
    inversion H.
    inversion H2.
    inversion H5.
    apply E_Seq with st1; subst.
       apply E_Ass. reflexivity.
       rewrite <- EQST. apply E_Ass. reflexivity.  Qed.
(* /ADMITTED *)

(* EX4A? (capprox) *)
(* HIDE: Question from 2012, UPenn Midterm 2. *)
(* LATER: Sampsa: This exercise is easily breakable *)
(** In this exercise we define an asymmetric variant of program
    equivalence we call _program approximation_. We say that a
    program `c1` _approximates_ a program `c2` when, for each of
    the initial states for which `c1` terminates, `c2` also terminates
    and produces the same final state. Formally, program approximation
    is defined as follows: *)

Definition capprox (c1 c2 : com) : Prop := forall (st st' : state),
  st =[ c1 ]=> st' -> st =[ c2 ]=> st'.

(** For example, the program
[[
  c1 = while ~(X = 1) do
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
Proof. (* ADMITTED *)
  unfold not, capprox; split; intros.

  assert (empty_st =[ c3 ]=> (X !-> 1)).
    constructor. reflexivity.
  apply H in H0. inversion H0; subst. simpl in H5.
  assert ((X !-> 2) X = 2).
    reflexivity.
  assert ((X !-> 1) X = 1).
    reflexivity.
  rewrite -> H5 in H1. rewrite -> H2 in H1. inversion H1.

  assert (empty_st =[ c4 ]=> (X !-> 2)).
    constructor. reflexivity.
  apply H in H0. inversion H0; subst. simpl in H5.
  assert ((X !-> 2) X = 2).
    reflexivity.
  assert ((X !-> 1) X = 1).
    reflexivity.
  rewrite -> H5 in H2. rewrite -> H1 in H2. inversion H2.
Qed. (* /ADMITTED *)

(** Find a program `cmin` that approximates every other program. *)

Definition cmin : com
  (* ADMITDEF *) := <{ while true do skip end }>. (* /ADMITDEF *)

Theorem cmin_minimal : forall c, capprox cmin c.
Proof. (* ADMITTED *)
  unfold capprox. intros.
  apply loop_never_stops in H.
  inversion H.
Qed. (* /ADMITTED *)

(** Finally, find a non-trivial property which is preserved by
    program approximation (when going from left to right). *)

Definition zprop (c : com) : Prop
  (* ADMITDEF *) := forall st, exists st', st =[ c ]=> st'. (* /ADMITDEF *)
(* QUIETSOLUTION *)

(** Intuitively, `zprop` holds of programs that terminate on all
    inputs. *)

(* /QUIETSOLUTION *)
Theorem zprop_preserving : forall c c',
  zprop c -> capprox c c' -> zprop c'.
Proof. (* ADMITTED *)
  unfold zprop, capprox. intros.
  specialize (H st). inversion H as `st'`.
  apply H0 in H1. exists st'. assumption.
Qed. (* /ADMITTED *)
(* HIDE *)

(** INSTRUCTORS: Several other non-trivial properties are also
    preserved by progam approximation. The following is a collection
    of interesting solutions harvested from last year's exams.  They
    could be turned into exercises at some point... *)
(* LATER: Lots of acknowledgments due here. :) *)

(** `zprop2` holds of programs that terminate on at least one
    input. *)

Definition zprop2 (c : com) : Prop :=
  exists st st', st =[ c ]=> st'.

Theorem zprop2_preserving : forall c c',
  zprop2 c -> capprox c c' -> zprop2 c'.
Proof.
  unfold zprop2, capprox. intros.
  destruct H as [st `st'` ]. intros.
  exists st, st'. apply H0. assumption.
Qed.

(** `zprop3` holds of programs that behave like `skip`. *)

Definition zprop3 (c : com) : Prop :=
  forall st, st =[ c ]=> st.

Theorem zprop3_preserving : forall c c',
  zprop3 c -> capprox c c' -> zprop3 c'.
Proof.
  unfold zprop3, capprox. intros.
  apply H0. apply H.
Qed.

(** `zprop4` is similar to `zprop3` — observe that `capprox`
    is transitive. *)

Definition zprop4 (c : com) : Prop :=
  capprox <{ skip }> c.

Theorem zprop4_preserving : forall c c',
  zprop4 c -> capprox c c' -> zprop4 c'.
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
