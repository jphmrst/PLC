---
title     : "MapProps: Properties of total and partial maps"
layout    : page
prev      : /Lists/
permalink : /MapProps/
next      : /
---

```
module plc.vfp.MapProps where
```

In this section we revisit the partial and total map types we defined
earlier, and study their properties.

## Imports

```
open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.String
open import plc.fp.Maps

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
```

## Properties of total maps

Recall that we used _functions_, rather than lists of key-value pairs,
to build maps.

    TotalMap : Set → Set
    TotalMap A = String → A

We will see some payoff from that choice in this section, since this
design simplifies some of the proofs we will construct.

#### Exercise `tApplyEmpty` (recommended)

Show that the empty map returns its default element for all keys:

    tApplyEmpty : ∀ (A : Set) (x : string) (v : A) → (↦ v) x = v
    -- Fill in your proof here
    
#### Exercise `tUpdateEq` (recommended)

Show that if we update a map `m` at a key `x` with a new value `v` and
then look up `x` in the map resulting from the `update`, we get back
`v`.

    tUpdateEq : ∀ (A : Set) (m : TotalMap A) x (v : A) → (x ↦ v , m) x = v
    -- Fill in your proof here
    
#### Exercise `tUpdateNeq` (recommended)

On the other hand, show that if we update a map `m` at a key `x1` and
then look up a _different_ key `x2` in the resulting map, we get the
same result that `m` would have given.

    tUpdateNeq : ∀ (A : Set) (m : TotalMap A) x1 x2 v → 
                   not (x1 == x2) → (x1 ↦ v , m) x2 = m x2
    -- Fill in your proof here

#### Exercise `tUpdateShadow` (recommended)

Show that if we update a map `m` at a key `x` with a value `v1`, and
then update again with the same key `x` and another value `v2`, the
resulting map behaves the same (gives the same result when applied to
any key) as the simpler map obtained by performing just the *second*
`update` on `m`:

    tUpdateShadow : ∀ (A : Set) (m : TotalMap A) x v1 v2 → 
                          (x ↦ v2 , x ↦ v1 , m) = (x ↦ v2 , m)
    -- Fill in your proof here

TODO Convert from here on

(** TERSE: *** *)
(** For the final two lemmas about total maps, it's convenient to use
    the reflection idioms introduced in chapter \CHAP{IndProp}.  We begin
    by proving a fundamental _reflection lemma_ relating the equality
    proposition on strings with the boolean function `eqb_string`. *)

(* TERSE: HIDEFROMHTML *)
(* EX2? (eqb_stringP) *)
(** Use the proof of `eqbP` in chapter \CHAP{IndProp} as a template to
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
(** `` *)
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)
(** Now, given `string`s `x1` and `x2`, we can use the tactic
    `destruct (eqb_stringP x1 x2)` to simultaneously perform case
    analysis on the result of `eqb_string x1 x2` and generate
    hypotheses about the equality (in the sense of `=`) of `x1`
    and `x2`. *)

(* TERSE: HIDEFROMHTML *)
(* EX2 (t_update_same) *)
(** With the example in chapter \CHAP{IndProp} as a template, use
    `eqb_stringP` to prove the following theorem, which states that
    if we update a map to assign key `x` the same value as it already
    has in `m`, then the result is equal to `m`: *)
(* TERSE: /HIDEFROMHTML *)

Theorem t_update_same : forall (A : Set) (m : TotalMap A) x,
    (x ↦ m x ; m) = m.
(* TERSE: FOLD *)
Proof.
  (* ADMITTED *)
  intros A m x1. apply functional_extensionality. intros x2.
  unfold t_update.
  destruct (eqb_stringP x1 x2) as `H | H`.
  - (* x1 = x2 *)
    rewrite H. reflexivity.
  - (* false *)
    reflexivity.  Qed.
(* /ADMITTED *)
(* TERSE: /FOLD *)
(* TERSE: HIDEFROMHTML *)
(** `` *)

(* EX3! (t_update_permute) *)
(** Use `eqb_stringP` to prove one final property of the `update`
    function: If we update a map `m` at two distinct keys, it doesn't
    matter in which order we do the updates. *)
(* TERSE: /HIDEFROMHTML *)

Theorem t_update_permute : forall (A : Set) (m : TotalMap A)
                                  v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 ↦ v1 ; x2 ↦ v2 ; m)
    =
    (x2 ↦ v2 ; x1 ↦ v1 ; m).
(* TERSE: FOLD *)
Proof.
  (* ADMITTED *)
  intros A m v1 v2 x1 x2 H.
  apply functional_extensionality. intros x3.
  rewrite <- eqb_string_false_iff in H.
  unfold t_update.
  destruct (eqb_stringP x1 x3) as `Heq | Hneq`.
  - (* eqb_id x1 x3 = true *)
    rewrite Heq in H. rewrite H. reflexivity.
  - (* eqb_id x1 x3 = false *) reflexivity.
Qed.
(* /ADMITTED *)
(* TERSE: /FOLD *)
(* TERSE: HIDEFROMHTML *)
(* GRADE_THEOREM 3: t_update_permute *)
(** `` *)
(* TERSE: /HIDEFROMHTML *)

## Properties of partial maps

(** Finally, we define _partial maps_ on top of total maps.  A partial
    map with elements of type `A` is simply a total map with elements
    of type `option A` and default element `None`. *)

Definition partial_map (A : Set) := TotalMap (option A).

Definition empty {A : Set} : partial_map A :=
  t_empty None.

(* HIDE: Notation "'\empty'" := empty. *)

Definition update {A : Set} (m : partial_map A)
           (x : string) (v : A) :=
  (x ↦ Some v ; m).

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

Lemma apply_empty : forall (A : Set) (x : string),
    @empty A x = None.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

Lemma update_eq : forall (A : Set) (m : partial_map A) x v,
    (x |-> v ; m) x = Some v.
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

Theorem update_neq : forall (A : Set) (m : partial_map A) x1 x2 v,
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

Lemma update_shadow : forall (A : Set) (m : partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
(* TERSE: HIDEFROMHTML *)
(* FOLD *)
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.
(* /FOLD *)
(* TERSE: /HIDEFROMHTML *)

Theorem update_same : forall (A : Set) (m : partial_map A) x v,
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

Theorem update_permute : forall (A : Set) (m : partial_map A)
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

---

*This page is derived from Pierce et al.; for more information see the
[sources and authorship]({{ site.baseurl }}/Sources/) page.*
