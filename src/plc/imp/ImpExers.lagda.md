---
title     : "ImpExers: Further applications and exercises"
layout    : page
prev      : /Step/
permalink : /ImpExers/
next      : /
---

```
module plc.imp.ImpExers where
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

---

*This page is derived from Pierce et al., with Agda translation and
additional material by Maraist; for more information see the [sources
and authorship]({{ site.baseurl }}/Sources/) page.*
