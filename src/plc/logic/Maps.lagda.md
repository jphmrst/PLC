
```
module plc.logic.Maps where
open import Data.Bool
open import Data.Nat

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
```

(** * Maps: Total and Partial Maps *)

(* SOONER: (BCP 12/18) I'm still not satisfied with the notations for
   t_update and update -- the !-> hack is ugly, and both flavors of
   update are the wrong way around to my eye.  But I'm having a hard
   time improving them. :-(  Suggestions welcome!
*)
(* SOONER: put TERSE: HIDEFROMHTML around FOLDed proofs *)
(** _Maps_ (or _dictionaries_) are ubiquitous data structures both
    generally and in the theory of programming languages in
    particular; we're going to need them in many places in the coming
    chapters.  They also make a nice case study using ideas we've seen
    in previous chapters, including building data structures out of
    higher-order functions (from [Basics] and [Poly]) and the use of
    reflection to streamline proofs (from [IndProp]).

    We'll define two flavors of maps: _total_ maps, which include a
    "default" element to be returned when a key being looked up
    doesn't exist, and _partial_ maps, which return an [option] to
    indicate success or failure.  The latter is defined in terms of
    the former, using [None] as the default element. *)
(** HIDE: Recall the type [partial_map] from the \CHAP{Lists} chapter.  Its
    basic operations were [empty], the constant empty map, [update],
    which takes a map and returns a new map with one key bound to a
    new value, and [find], which looks up a key in a map. *)

(* ###################################################################### *)
(** * The Coq Standard Library *)

(** FULL: One small digression before we begin...

    Unlike the chapters we have seen so far, this one does not
    [Require Import] the chapter before it (and, transitively, all the
    earlier chapters).  Instead, in this chapter and from now, on
    we're going to import the definitions and theorems we need
    directly from Coq's standard library stuff.  You should not notice
    much difference, though, because we've been careful to name our
    own definitions and theorems the same as their counterparts in the
    standard library, wherever they overlap. *)

(** TERSE: We'll import things from the standard library from now on... *)

From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

(** FULL: Documentation for the standard library can be found at
    #<a href="https://coq.inria.fr/library/">#https://coq.inria.fr/library/#</a>#.

    The [Search] command is a good way to look for theorems involving
    objects of specific types.  Take a minute now to experiment with it. *)
(** SOONER: [Locate] is also useful to find where an identifier
    or notation (!) comes from and detect ambiguity/shadowing. *)
(* SOONER: Search vs SearchAbout? *)

(* ###################################################################### *)
(** * Identifiers *)

(** First, we need a type for the keys that we use to index into our
    maps.  In [Lists.v] we introduced a fresh type [id] for a similar
    purpose; here and for the rest of _Software Foundations_ we will
    use the [string] type from Coq's standard library. *)

(** To compare strings, we define the function [eqb_string], which
    internally uses the function [string_dec] from Coq's string
    library. *)

(** SOONER: Robert Rand: Why not just use nats? Do concrete strings ever
    appear in this context? *)

(** SOONER: Robert Rand: Coq 8.9 actually has an eqb function on strings, as
    well as the lemmas eqb_[refl|sym|eq|neq], so this section is no
    longer needed. *)


Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

(** FULL: (The function [string_dec] comes from Coq's string library.
    If you check the result type of [string_dec], you'll see that it
    does not actually return a [bool], but rather a type that looks
    like [{x = y} + {x <> y}], called a [sumbool], which can be
    thought of as an "evidence-carrying boolean."  Formally, an
    element of [{x = y} + {x <> y}] is either a proof that [x] and [y] are equal
    or a proof that they are unequal, together with a tag indicating
    which.  But for present purposes you can think of it as just a
    fancy [bool].) *)

(** TERSE: *** *)
(** Now we need a few basic properties of string equality... *)
Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  intros s. unfold eqb_string.
  destruct (string_dec s s) as [Hs_eq | Hs_not_eq].
  - reflexivity.
  - destruct Hs_not_eq. reflexivity.
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(** FULL: Two strings are equal according to [eqb_string] iff they
    are equal according to [=].  So [=] is reflected in [eqb_string],
    in the sense of "reflection" as discussed in \CHAP{IndProp}. *)

Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
   intros x y.
   unfold eqb_string.
   destruct (string_dec x y) as [Hs_eq | Hs_not_eq].
   - rewrite Hs_eq. split. reflexivity. reflexivity.
   - split.
     + intros contra. discriminate contra.
     + intros H. rewrite H in Hs_not_eq. destruct Hs_not_eq. reflexivity.
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(** FULL: Similarly: *)

Theorem eqb_string_false_iff : forall x y : string,
    eqb_string x y = false <-> x <> y.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(* HIDEFROMHTML *)
(* HIDE: N.B., the next theorem is never used in LF but is
   used frequently in PLF. *)
(** This corollary follows just by rewriting: *)

Theorem false_eqb_string : forall x y : string,
   x <> y -> eqb_string x y = false.
(* FOLD *)
Proof.
  intros x y. rewrite eqb_string_false_iff.
  intros H. apply H. Qed.
(* /FOLD *)
(* /HIDEFROMHTML *)

(* ###################################################################### *)
(** * Total Maps *)

(** Our main job in this chapter will be to build a definition of
    partial maps that is similar in behavior to the one we saw in the
    \CHAP{Lists} chapter, plus accompanying lemmas about its behavior.

    This time around, though, we're going to use _functions_, rather
    than lists of key-value pairs, to build maps.  The advantage of
    this representation is that it offers a more _extensional_ view of
    maps, where two maps that respond to queries in the same way will
    be represented as literally the same thing (the very same function),
    rather than just "equivalent" data structures.  This, in turn,
    simplifies proofs that use maps. *)

(** TERSE: *** *)
(** We build partial maps in two steps.  First, we define a type of
    _total maps_ that return a default value when we look up a key
    that is not present in the map. *)

Definition total_map (A : Type) := string -> A.

(** Intuitively, a total map over an element type [A] is just a
    function that can be used to look up [string]s, yielding [A]s. *)

(** TERSE: *** *)
(** The function [t_empty] yields an empty total map, given a default
    element; this map always returns the default element when applied
    to any string. *)

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

(** TERSE: *** *)
(** More interesting is the [update] function, which (as before) takes
    a map [m], a key [x], and a value [v] and returns a new map that
    takes [x] to [v] and takes every other key to whatever [m] does. *)

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

(** This definition is a nice example of higher-order programming:
    [t_update] takes a _function_ [m] and yields a new function
    [fun x' => ...] that behaves like the desired map. *)

(** TERSE: *** *)
(** For example, we can build a map taking [string]s to [bool]s, where
    ["foo"] and ["bar"] are mapped to [true] and every other key is
    mapped to [false], like this: *)

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

(** TERSE: *** *)
(** Next, let's introduce some new notations to facilitate working
    with maps. *)

(** First, we will use the following notation to create an empty
    total map with a default value. *)
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).

(** TERSE: *** *)
(** We then introduce a convenient notation for extending an existing
    map with some bindings. *)
(* SOONER: It would be nice if this notation bound tighter than the
   typing relation G |- t : T so that we don't need parens around G
   when it's an update expression. *)
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

(** TERSE: *** *)
(** The [examplemap] above can now be defined as follows: *)

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _     !-> false
  ).

(** HIDE: Annoyingly, annotating [examplemap' : total_map bool]
    confuses the parser when we apply it like in the next examples,
    whereas [string_scope] gets opened if we leave the inferred type
    alone: [string -> bool]. *)
(** FULL: This completes the definition of total maps.  Note that we
    don't need to define a [find] operation because it is just
    function application! *)

(* HIDEFROMHTML *)
Example update_example1 : examplemap' "baz" = false.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

Example update_example2 : examplemap' "foo" = true.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

Example update_example3 : examplemap' "quux" = false.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

Example update_example4 : examplemap' "bar" = true.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
(* /HIDEFROMHTML *)

(** TERSE: *** *)
(** To use maps in later chapters, we'll need several fundamental
    facts about how they behave. *)

(** FULL: Even if you don't work the following exercises, make sure
    you thoroughly understand the statements of the lemmas! *)

(** (Some of the proofs require the functional extensionality axiom,
    which is discussed in the \CHAP{Logic} chapter.) *)
(* TERSE: HIDEFROMHTML *)

(* EX1? (t_apply_empty) *)
(** First, the empty map returns its default element for all keys: *)
(* TERSE: /HIDEFROMHTML *)

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
(* TERSE: FOLD *)
Proof.
  (* ADMITTED *)
  reflexivity.
Qed.
(* /ADMITTED *)
(* TERSE: /FOLD *)
(* TERSE: HIDEFROMHTML *)
(** [] *)

(* EX2? (t_update_eq) *)
(** Next, if we update a map [m] at a key [x] with a new value [v]
    and then look up [x] in the map resulting from the [update], we
    get back [v]: *)
(* TERSE: /HIDEFROMHTML *)

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
(* TERSE: FOLD *)
Proof.
  (* ADMITTED *)
  intros. unfold t_update.  rewrite <- eqb_string_refl.
  reflexivity.
Qed.
(* /ADMITTED *)
(* TERSE: /FOLD *)
(* TERSE: HIDEFROMHTML *)
(** [] *)

(* EX2? (t_update_neq) *)
(** On the other hand, if we update a map [m] at a key [x1] and then
    look up a _different_ key [x2] in the resulting map, we get the
    same result that [m] would have given: *)
(* TERSE: /HIDEFROMHTML *)

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
(* TERSE: FOLD *)
Proof.
  (* ADMITTED *)
  intros A m x1 x2 v.
  rewrite <- eqb_string_false_iff.
  intros Hneq.
  unfold t_update.
  rewrite -> Hneq.
  reflexivity.  Qed.
(* /ADMITTED *)
(* TERSE: /FOLD *)
(* TERSE: HIDEFROMHTML *)
(** [] *)

(* EX2? (t_update_shadow) *)
(** If we update a map [m] at a key [x] with a value [v1] and then
    update again with the same key [x] and another value [v2], the
    resulting map behaves the same (gives the same result when applied
    to any key) as the simpler map obtained by performing just
    the second [update] on [m]: *)
(* TERSE: /HIDEFROMHTML *)

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
(* TERSE: FOLD *)
Proof.
  (* ADMITTED *)
  intros A m x v1 v2.
  apply functional_extensionality. intros x'.
  unfold t_update. destruct (eqb_string x x').
    - reflexivity.
    - reflexivity.
Qed.
(* LATER: Ori likes this better instead of the last three lines:
      destruct (eqb_string x x') eqn:EQ.
      - apply eqb_string_true_iff in EQ.
        rewrite EQ.
        rewrite t_update_eq.
        rewrite t_update_eq.
        reflexivity.
      - apply eqb_string_false_iff in EQ.
        rewrite (t_update_neq _ _ _ _ _ EQ).
        rewrite (t_update_neq _ _ _ _ _ EQ).
        rewrite (t_update_neq _ _ _ _ _ EQ).
        reflexivity.
  Why? *)
(* /ADMITTED *)
(* TERSE: /FOLD *)
(* TERSE: HIDEFROMHTML *)
(** [] *)
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)
(** For the final two lemmas about total maps, it's convenient to use
    the reflection idioms introduced in chapter \CHAP{IndProp}.  We begin
    by proving a fundamental _reflection lemma_ relating the equality
    proposition on strings with the boolean function [eqb_string]. *)

(* TERSE: HIDEFROMHTML *)
(* EX2? (eqb_stringP) *)
(** Use the proof of [eqbP] in chapter \CHAP{IndProp} as a template to
    prove the following: *)
(* TERSE: /HIDEFROMHTML *)

Lemma eqb_stringP : forall x y : string,
    reflect (x = y) (eqb_string x y).
(* TERSE: FOLD *)
Proof.
  (* ADMITTED *)
  intros x y.
  apply iff_reflect. rewrite eqb_string_true_iff.
  reflexivity.
Qed.
(* /ADMITTED *)
(* TERSE: /FOLD *)
(* TERSE: HIDEFROMHTML *)
(** [] *)
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)
(** Now, given [string]s [x1] and [x2], we can use the tactic
    [destruct (eqb_stringP x1 x2)] to simultaneously perform case
    analysis on the result of [eqb_string x1 x2] and generate
    hypotheses about the equality (in the sense of [=]) of [x1]
    and [x2]. *)

(* TERSE: HIDEFROMHTML *)
(* EX2 (t_update_same) *)
(** With the example in chapter \CHAP{IndProp} as a template, use
    [eqb_stringP] to prove the following theorem, which states that
    if we update a map to assign key [x] the same value as it already
    has in [m], then the result is equal to [m]: *)
(* TERSE: /HIDEFROMHTML *)

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
(* TERSE: FOLD *)
Proof.
  (* ADMITTED *)
  intros A m x1. apply functional_extensionality. intros x2.
  unfold t_update.
  destruct (eqb_stringP x1 x2) as [H | H].
  - (* x1 = x2 *)
    rewrite H. reflexivity.
  - (* false *)
    reflexivity.  Qed.
(* /ADMITTED *)
(* TERSE: /FOLD *)
(* TERSE: HIDEFROMHTML *)
(** [] *)

(* EX3! (t_update_permute) *)
(** Use [eqb_stringP] to prove one final property of the [update]
    function: If we update a map [m] at two distinct keys, it doesn't
    matter in which order we do the updates. *)
(* TERSE: /HIDEFROMHTML *)

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1 ; x2 !-> v2 ; m)
    =
    (x2 !-> v2 ; x1 !-> v1 ; m).
(* TERSE: FOLD *)
Proof.
  (* ADMITTED *)
  intros A m v1 v2 x1 x2 H.
  apply functional_extensionality. intros x3.
  rewrite <- eqb_string_false_iff in H.
  unfold t_update.
  destruct (eqb_stringP x1 x3) as [Heq | Hneq].
  - (* eqb_id x1 x3 = true *)
    rewrite Heq in H. rewrite H. reflexivity.
  - (* eqb_id x1 x3 = false *) reflexivity.
Qed.
(* /ADMITTED *)
(* TERSE: /FOLD *)
(* TERSE: HIDEFROMHTML *)
(* GRADE_THEOREM 3: t_update_permute *)
(** [] *)
(* TERSE: /HIDEFROMHTML *)

(* ###################################################################### *)
(** * Partial maps *)

(** Finally, we define _partial maps_ on top of total maps.  A partial
    map with elements of type [A] is simply a total map with elements
    of type [option A] and default element [None]. *)

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

(* HIDE: Notation "'\empty'" := empty. *)

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

(** TERSE: *** *)
(** We introduce a similar notation for partial maps: *)
Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

(** We can also hide the last case when it is empty. *)
Notation "x '|->' v" := (update empty x v)
  (at level 100).

Example examplepmap :=
  ("Church" |-> true ; "Turing" |-> false).

(** TERSE: *** *)
(** We now straightforwardly lift all of the basic lemmas about total
    maps to partial maps.  *)

Lemma apply_empty : forall (A : Type) (x : string),
    @empty A x = None.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
    (x |-> v ; m) x = Some v.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
    x2 <> x1 ->
    (x2 |-> v ; m) x1 = m x1.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
    m x = Some v ->
    (x |-> v ; m) = m.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

(* HIDE *)
(*
Local Variables:
fill-column: 70
End:
*)
(* /HIDE *)
