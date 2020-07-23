---
title     : "NatData: Data structures with natural numbers"
layout    : page
prev      : /Naturals/
permalink : /Logic-NatData/
next      : /Induction/
---

```
module plc.logic.NatData where
open import plc.fp.Naturals
-- open import plc.fp.NatData
```


(** Now let's try to prove a few simple facts about pairs.

    If we state properties of pairs in a slightly peculiar way, we can
    sometimes complete their proofs with just reflexivity (and its
    built-in simplification): *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.

(** TERSE: *** *)
(** But [reflexivity] is not enough if we state the lemma in a more
    natural way: *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

(** TERSE: *** *)
(** FULL: Instead, we need to expose the structure of [p] so that
    [simpl] can perform the pattern match in [fst] and [snd].  We can
    do this with [destruct]. *)
(** TERSE: Solution: use [destruct]. *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as [n m].  simpl.  reflexivity.  Qed.

(** FULL: Notice that, unlike its behavior with [nat]s, where it
    generates two subgoals, [destruct] generates just one subgoal
    here.  That's because [natprod]s can only be constructed in one
    way. *)

(* /HIDEFROMADVANCED *)
(* FULL *)
(* EX1 (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  (* ADMITTED *)
  intros p.  destruct p as [n m].  simpl.  reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX1? (fst_swap_is_snd) *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  (* ADMITTED *)
  intros p. destruct p as [n m].  simpl.  reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(* ###################################################### *)
(** * Lists of Numbers *)

(** FULL: Generalizing the definition of pairs, we can describe the
    type of _lists_ of numbers like this: "A list is either the empty
    list or else a pair of a number and another list." *)
(** TERSE: An inductive definition of _lists_ of numbers: *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

(** FULL: For example, here is a three-element list: *)

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(** TERSE: *** *)
(** FULL: As with pairs, it is more convenient to write lists in
    familiar programming notation.  The following declarations
    allow us to use [::] as an infix [cons] operator and square
    brackets as an "outfix" notation for constructing lists. *)
(** TERSE: Some notation for lists to make our lives easier: *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** FULL: It is not necessary to understand the details of these
    declarations, but here is roughly what's going on in case you are
    interested.  The "[right associativity]" annotation tells Coq how to
    parenthesize expressions involving multiple uses of [::] so that,
    for example, the next three declarations mean exactly the same
    thing: *)
(** TERSE: Now these all mean exactly the same thing: *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(** FULL: The "[at level 60]" part tells Coq how to parenthesize
    expressions that involve both [::] and some other infix operator.
    For example, since we defined [+] as infix notation for the [plus]
    function at level 50,
[[
  Notation "x + y" := (plus x y)
                      (at level 50, left associativity).
]]
    the [+] operator will bind tighter than [::], so [1 + 2 :: [3]]
    will be parsed, as we'd expect, as [(1 + 2) :: [3]] rather than
    [1 + (2 :: [3])].

    (Expressions like "[1 + 2 :: [3]]" can be a little confusing when
    you read them in a [.v] file.  The inner brackets, around 3, indicate
    a list, but the outer brackets, which are invisible in the HTML
    rendering, are there to instruct the "coqdoc" tool that the bracketed
    part should be displayed as Coq code rather than running text.)

    The second and third [Notation] declarations above introduce the
    standard square-bracket notation for lists; the right-hand side of
    the third one illustrates Coq's syntax for declaring n-ary
    notations and translating them to nested sequences of binary
    constructors. *)

(** *** Repeat *)

(** FULL: Next let's look at several functions for constructing and
    manipulating lists.  First, the [repeat] function takes a number
    [n] and a [count] and returns a list of length [count] in which
    every element is [n]. *)
(** TERSE: Some useful list-manipulation functions: *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(** *** Length *)

(** FULL: The [length] function calculates the length of a list. *)

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(** *** Append *)

(** FULL: The [app] function concatenates (appends) two lists. *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

(** FULL: Since [app] will be used extensively, it is again convenient
    to have an infix operator for it. *)

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

(* HIDEFROMADVANCED *)
Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

(* /HIDEFROMADVANCED *)

(** *** Head and Tail *)

(** FULL: Here are two smaller examples of programming with lists.
    The [hd] function returns the first element (the "head") of the
    list, while [tl] returns everything but the first element (the
    "tail").  Since the empty list has no first element, we pass
    a default value to be returned in that case.  *)

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

(* HIDEFROMADVANCED *)
Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity.  Qed.

(* QUIZ *)
(** What does the following function do? *)

Fixpoint foo (n:nat) : natlist :=
  match n with
  | 0 => nil
  | S n' => n :: (foo n')
  end.

(** (Submit any response when you have the answer.) *)
(* /QUIZ *)

(* /HIDEFROMADVANCED *)

(* FULL *)
(** *** Exercises *)

(* EX2! (list_funs) *)
(** Complete the definitions of [nonzeros], [oddmembers], and
    [countoddmembers] below. Have a look at the tests to understand
    what these functions should do. *)

Fixpoint nonzeros (l:natlist) : natlist
  (* ADMITDEF *) :=
  match l with
  | nil => nil
  | h :: t =>
      match h with
      | O => nonzeros t
      | S h' => h :: (nonzeros t)
      end
  end.
(* /ADMITDEF *)

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  (* ADMITTED *)
Proof. reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: NatList.test_nonzeros *)

Fixpoint oddmembers (l:natlist) : natlist
  (* ADMITDEF *) :=
  match l with
  | nil => nil
  | h :: t =>
      match (oddb h) with
      | true => h :: (oddmembers t)
      | false => oddmembers t
      end
  end.
(* /ADMITDEF *)

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  (* ADMITTED *)
Proof. reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: NatList.test_oddmembers *)

Definition countoddmembers (l:natlist) : nat
  (* ADMITDEF *) :=
  length (oddmembers l).
(* /ADMITDEF *)

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  (* ADMITTED *)
Proof. reflexivity.  Qed.
(* /ADMITTED *)

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  (* ADMITTED *)
Proof. reflexivity.  Qed.
(* /ADMITTED *)

Example test_countoddmembers3:
  countoddmembers nil = 0.
  (* ADMITTED *)
Proof. reflexivity.  Qed.
(* GRADE_THEOREM 0.5: NatList.test_countoddmembers2 *)
(* GRADE_THEOREM 0.5: NatList.test_countoddmembers3 *)
(* /ADMITTED *)
(** [] *)

(* EX3A (alternate) *)
(** Complete the following definition of [alternate], which
    interleaves two lists into one, alternating between elements taken
    from the first list and elements from the second.  See the tests
    below for more specific examples.

    (Note: one natural and elegant way of writing [alternate] will
    fail to satisfy Coq's requirement that all [Fixpoint] definitions
    be "obviously terminating."  If you find yourself in this rut,
    look for a slightly more verbose solution that considers elements
    of both lists at the same time.  One possible solution involves
    defining a new kind of pairs, but this is not the only way.)  *)
(* HIDE *)
(* This is the "natural" way that doesn't work (we introduce [Fail] in
   [Poly.v]): *)
Fail Fixpoint alternate (l1 l2:natlist)  : natlist :=
  match l1 with
  | nil => l2
  | h1::t1 => h1::(alternate l2 t1)
  end.

(* /HIDE *)
(* QUIETSOLUTION *)
(* /QUIETSOLUTION *)
Fixpoint alternate (l1 l2 : natlist) : natlist
  (* ADMITDEF *) :=
  match l1, l2 with
  | nil, _ => l2
  | _, nil => l1
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
  end.
(* /ADMITDEF *)
(* QUIETSOLUTION *)

(** Or: *)
Fixpoint alternate' (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h1::t1 => match l2 with
              | nil => l1
              | h2::t2 => h1 :: h2 :: (alternate' t1 t2)
              end
  end.

(* /QUIETSOLUTION *)
Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  (* ADMITTED *)
Proof. reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: NatList.test_alternate1 *)

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
  (* ADMITTED *)
Proof. reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: NatList.test_alternate2 *)

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
  (* ADMITTED *)
Proof. reflexivity.  Qed.
(* /ADMITTED *)

Example test_alternate4:
  alternate [] [20;30] = [20;30].
  (* ADMITTED *)
Proof. reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: NatList.test_alternate4 *)
(** [] *)

(* ###################################################### *)
(** *** Bags via Lists *)

(** A [bag] (or [multiset]) is like a set, except that each element
    can appear multiple times rather than just once.  One possible
    representation for a bag of numbers is as a list. *)

Definition bag := natlist.

(* EX3! (bag_functions) *)
(** Complete the following definitions for the functions
    [count], [sum], [add], and [member] for bags. *)

Fixpoint count (v:nat) (s:bag) : nat
  (* ADMITDEF *) :=
  match s with
  | nil => 0
  | h :: t =>
      match h =? v with
      | false => count v t
      | true => S (count v t)
      end
  end.
(* /ADMITDEF *)

(** All these proofs can be done just by [reflexivity]. *)

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)
(* GRADE_THEOREM 0.5: NatList.test_count2 *)

(** Multiset [sum] is similar to set [union]: [sum a b] contains all
    the elements of [a] and of [b].  (Mathematicians usually define
    [union] on multisets a little bit differently -- using max instead
    of sum -- which is why we don't call this operation [union].)  For
    [sum], we're giving you a header that does not give explicit names
    to the arguments.  Moreover, it uses the keyword [Definition]
    instead of [Fixpoint], so even if you had names for the arguments,
    you wouldn't be able to process them recursively.  The point of
    stating the question this way is to encourage you to think about
    whether [sum] can be implemented in another way -- perhaps by
    using one or more functions that have already been defined.  *)

Definition sum : bag -> bag -> bag
  (* ADMITDEF *) :=
  app.
(* /ADMITDEF *)

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)
(* GRADE_THEOREM 0.5: NatList.test_sum1 *)

Definition add (v:nat) (s:bag) : bag
  (* ADMITDEF *) :=
  v :: s.
(* /ADMITDEF *)

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)
(* GRADE_THEOREM 0.5: NatList.test_add1 *)
(* GRADE_THEOREM 0.5: NatList.test_add2 *)

Definition member (v:nat) (s:bag) : bool
  (* ADMITDEF *) :=
  negb ((count v s) =? 0).
(* /ADMITDEF *)

Example test_member1:             member 1 [1;4;1] = true.
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)
(* GRADE_THEOREM 0.5: NatList.test_member1 *)
(* GRADE_THEOREM 0.5: NatList.test_member2 *)

Example test_member2:             member 2 [1;4;1] = false.
(* ADMITTED *)
Proof. reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX3? (bag_more_functions) *)
(* HIDE: The exercise is optional but the solution is automatable -- worth doing that? *)
(** Here are some more [bag] functions for you to practice with. *)

(** When [remove_one] is applied to a bag without the number to
    remove, it should return the same bag unchanged.  (This exercise
    is optional, but students following the advanced track will need
    to fill in the definition of [remove_one] for a later
    exercise.) *)

Fixpoint remove_one (v:nat) (s:bag) : bag
  (* ADMITDEF *) :=
  match s with
  | nil => nil
  | h :: t =>
      match h =? v with
      | true => t
      | false => h :: (remove_one v t)
      end
  end.
(* /ADMITDEF *)

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
  (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)

Fixpoint remove_all (v:nat) (s:bag) : bag
  (* ADMITDEF *) :=
  match s with
  | nil => nil
  | h :: t =>
      match h =? v with
      | true => remove_all v t
      | false => h :: (remove_all v t)
      end
  end.
(* /ADMITDEF *)

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)
Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)
Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)
Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)

Fixpoint subset (s1:bag) (s2:bag) : bool
  (* ADMITDEF *) :=
  match s1 with
  | nil => true
  | h1 :: t1 =>
      andb (member h1 s2)
               (subset t1 (remove_one h1 s2))
  end.
(* /ADMITDEF *)

Example test_subset1:              subset [1;2] [2;1;4;1] = true.
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)
(** [] *)

(* EX2M! (bag_theorem) *)
(** Write down an interesting theorem [bag_theorem] about bags
    involving the functions [count] and [add], and prove it.  Note
    that, since this problem is somewhat open-ended, it's possible
    that you may come up with a theorem that is true but whose proof
    requires techniques you haven't learned yet.  Ask for help if you
    get stuck! *)

(*
Theorem bag_theorem : ...
Proof.
  ...
Qed.
*)
(* QUIETSOLUTION *)

(** Some possibilities... *)

Theorem bag_theorem1 :
  forall s:bag, forall v:nat,
  count v (add v s) = 1 + count v s.
Proof.
  intros s v. simpl.
  rewrite <- eqb_refl.
  reflexivity.
Qed.

Theorem bag_theorem2 : forall v s,
    count v (add v s) = S (count v s).
Proof.
  intros v s.
  induction s as [| x s' IHs' ].
  - simpl. rewrite <- eqb_refl. reflexivity.
  - simpl. rewrite <- eqb_refl.
    destruct (x =? v).
    (* note that we can use [destruct] on any term having an inductive type,
       not just on simple identifiers *)
    + reflexivity.
    + reflexivity.
Qed.
(* /QUIETSOLUTION *)
(* GRADE_MANUAL 2: bag_theorem *)
(* HIDE: Note to instructors: For silly technical reasons, in this
   file (only) you will need to write [Some (Datatypes.pair 3 ""%string)]
   rather than [Some (3,""%string)] to enter your grade and comments. *)
(** [] *)

(* /FULL *)
(* ###################################################### *)
(** * Reasoning About Lists *)

(** FULL: As with numbers, simple facts about list-processing
    functions can sometimes be proved entirely by simplification.  For
    example, just the simplification performed by [reflexivity] is
    enough for this theorem... *)
(** TERSE: As for numbers, some proofs about list functions need only
    simplification... *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

(** FULL: ...because the [[]] is substituted into the
    "scrutinee" (the expression whose value is being "scrutinized" by
    the match) in the definition of [app], allowing the match itself
    to be simplified. *)

(** FULL: Also, as with numbers, it is sometimes helpful to perform case
    analysis on the possible shapes (empty or non-empty) of an unknown
    list. *)
(** TERSE: *** *)
(** TERSE: ...and some need case analysis. *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.  Qed.

(** FULL: Here, the [nil] case works because we've chosen to define
    [tl nil = nil]. Notice that the [as] annotation on the [destruct]
    tactic here introduces two names, [n] and [l'], corresponding to
    the fact that the [cons] constructor for lists takes two
    arguments (the head and tail of the list it is constructing). *)

(** Usually, though, interesting theorems about lists require
    induction for their proofs.  We'll see how to do this next. *)

(* FULL *)
(** (Micro-Sermon: As we get deeper into this material, simply
    _reading_ proof scripts will not get you very far!  It is
    important to step through the details of each one using Coq and
    think about what each step achieves.  Otherwise it is more or less
    guaranteed that the exercises will make no sense when you get to
    them.  'Nuff said.) *)

(* /FULL *)
(* ###################################################### *)
(** ** Induction on Lists *)

(** FULL: Proofs by induction over datatypes like [natlist] are a
    little less familiar than standard natural number induction, but
    the idea is equally simple.  Each [Inductive] declaration defines
    a set of data values that can be built up using the declared
    constructors.  For example, a boolean can be either [true] or
    [false]; a number can be either [O] or [S] applied to another
    number; and a list can be either [nil] or [cons] applied to a
    number and a list.   Moreover, applications of the declared
    constructors to one another are the _only_ possible shapes
    that elements of an inductively defined set can have.

    This last fact directly gives rise to a way of reasoning about
    inductively defined sets: a number is either [O] or else it is [S]
    applied to some _smaller_ number; a list is either [nil] or else
    it is [cons] applied to some number and some _smaller_ list;
    etc. So, if we have in mind some proposition [P] that mentions a
    list [l] and we want to argue that [P] holds for _all_ lists, we
    can reason as follows:

      - First, show that [P] is true of [l] when [l] is [nil].

      - Then show that [P] is true of [l] when [l] is [cons n l'] for
        some number [n] and some smaller list [l'], assuming that [P]
        is true for [l'].

    Since larger lists can always be broken down into smaller ones,
    eventually reaching [nil], these two arguments together establish
    the truth of [P] for all lists [l].  Here's a concrete example: *)

(** TERSE: Coq generates an induction principle for every [Inductive]
    definition, including lists.  We can use the [induction] tactic on
    lists to prove things like the associativity of list-append... *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** FULL: Notice that, as when doing induction on natural numbers, the
    [as...] clause provided to the [induction] tactic gives a name to
    the induction hypothesis corresponding to the smaller list [l1']
    in the [cons] case.

    Once again, this Coq proof is not especially illuminating as a
    static document -- it is easy to see what's going on if you are
    reading the proof in an interactive Coq session and you can see
    the current goal and context at each point, but this state is not
    visible in the written-down parts of the Coq proof.  So a
    natural-language proof -- one written for human readers -- will
    need to include more explicit signposts; in particular, it will
    help the reader stay oriented if we remind them exactly what the
    induction hypothesis is in the second case. *)

(* HIDEFROMADVANCED *)
(** TERSE: *** *)
(** For comparison, here is an informal proof of the same theorem. *)

(** _Theorem_: For all lists [l1], [l2], and [l3],
   [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)].

   _Proof_: By induction on [l1].

   - First, suppose [l1 = []].  We must show
[[
       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),
]]
     which follows directly from the definition of [++].

   - Next, suppose [l1 = n::l1'], with
[[
       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)
]]
     (the induction hypothesis). We must show
[[
       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).
]]
     By the definition of [++], this follows from
[[
       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),
]]
     which is immediate from the induction hypothesis.  [] *)
(* /HIDEFROMADVANCED *)

(** *** Reversing a List *)

(* HIDEFROMADVANCED *)
(** FULL: For a slightly more involved example of inductive proof over
    lists, suppose we use [app] to define a list-reversing
    function [rev]: *)
(** TERSE: A bigger example of induction over lists. *)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

(* HIDEFROMADVANCED *)
Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.
(* /HIDEFROMADVANCED *)

(** FULL: For something a bit more challenging than the proofs
    we've seen so far, let's prove that reversing a list does not
    change its length.  Our first attempt gets stuck in the successor
    case... *)
(** TERSE: *** *)
(** TERSE: Let's try to prove [length (rev l) = length l]. *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = n :: l' *)
(* FULL *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
(* /FULL *)
    simpl.
(* FULL *)
    (* Now we seem to be stuck: the goal is an equality
       involving [++], but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
(* /FULL *)
    rewrite <- IHl'.
(* FULL *)
    (* ... but now we can't go any further. *)
(* /FULL *)
Abort.

(** FULL: So let's take the equation relating [++] and [length] that
    would have enabled us to make progress at the point where we got
    stuck and state it as a separate lemma. *)
(** TERSE: We can prove a lemma to bridge the gap. *)

(** TERSE: *** *)

(* SOONER: There's a potential for confusion while working through
   this proof. The :: and ++ operators have the same precedence, but
   it may appear as though :: should bind tighter, which makes the
   proof state hard to understand! *)
Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKINCLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.
(* /WORKINCLASS *)

(** FULL: Note that, to make the lemma as general as possible, we
    quantify over _all_ [natlist]s, not just those that result from an
    application of [rev].  This should seem natural, because the truth
    of the goal clearly doesn't depend on the list having been
    reversed.  Moreover, it is easier to prove the more general
    property. *)

(** TERSE: *** *)
(* HIDEFROMADVANCED *)
(** Now we can complete the original proof. *)
(* /HIDEFROMADVANCED *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length.
    simpl. rewrite -> IHl'. rewrite plus_comm.
    reflexivity.
Qed.

(* HIDEFROMADVANCED *)
(* TERSE *)

(* QUIZ *)
(** To prove the following theorem, which tactics will we need besides
    [intros], [simpl], [rewrite], and [reflexivity]?  (1) none, (2) [destruct],
    (3) [induction on n], (4) [induction on l], or (5) can't be
    done with the tactics we've seen.
[[
      Theorem foo1 : forall n :nat, forall l: natlist,
        repeat n 0 = l -> length l = 0.
]]
*)
(* HIDE *)
Theorem foo1 : forall n : nat, forall l : natlist,
  repeat n 0 = l -> length l = 0.
Proof.
  simpl. intros n l H.
  rewrite <- H. reflexivity.
Qed.
(* /HIDE *)
(* /QUIZ *)

(* QUIZ *)
(** What about the next one?
[[
      Theorem foo2 :  forall n m:nat, forall l: natlist,
        repeat n m = l -> length l = m.
]]
    Which tactics do we need besides [intros], [simpl], [rewrite], and
    [reflexivity]?  (1) none, (2) [destruct],
    (3) [induction on m], (4) [induction on l], or (5) can't be
    done with the tactics we've seen.
*)
(* HIDE *)
Theorem foo2 :  forall n m : nat, forall l : natlist,
  repeat n m = l -> length l = m.
Proof.
intros n m. induction m as [| m' IHm'].
- intros. rewrite <- H. reflexivity.
- simpl. intros. rewrite <- H.
  simpl. rewrite IHm'. reflexivity.
  reflexivity.
Qed.
(* N.b.: Induction on l doesn't work!  (Requires an inner induction on
   m anyway.) *)
(* LATER: (mrc) the proof above relies on leaving [l] universally
   quantified in the inductive hypothesis; that technique isn't
   taught until Tactics.v.  So although it's reasonable to ask what to
   induct upon here, it's not entirely reasonable to expect readers
   to be able to complete the proof.  It would be beneficial
   to replace [foo2] with a different theorem that can be proved
   using techniques that are known at this point. *)
(* /HIDE *)
(* /QUIZ *)

(* QUIZ *)

(* SOONER: Robert Rand: I don't know what the answer is supposed to be
     to this.  This can clearly be done using the tactics we've seen,
     (see foo3' below) though we may need to assert app_length and
     plus_comm. *)

(** What about this one?
[[
      Theorem foo3: forall n :nat, forall l1 l2: natlist,
        l1 ++ [n] = l2 -> (1 <=? (length l2)) = true.
]]
    Which tactics do we need besides [intros], [simpl], [rewrite], and
    [reflexivity]?  (1) none, (2) [destruct],
    (3) [induction on n], (4) [induction on l1], (5) [induction on l2],
    (6) can't be done with the tactics we've seen.
*)
(* HIDE *)
(*
Theorem foo3 :  forall n :nat, forall l1 l2: natlist,
l1 ++ [n] = l2 -> (1 <=? (length l2)) = true.
Proof.
  intros n l1 l2 H. rewrite <- H. rewrite app_length. simpl.
Qed.

Theorem foo3' :  forall n :nat, forall l1 l2: natlist,
l1 ++ [n] = l2 -> (1 <=? (length l2)) = true.
Proof.
  intros n l1 l2 H. rewrite <- H. rewrite app_length. rewrite plus_comm. simpl. reflexivity.
Qed.


*)
(* /HIDE *)
(* /QUIZ *)
(* /TERSE *)
(* /HIDEFROMADVANCED *)

(* FULL *)
(** For comparison, here are informal proofs of these two theorems:

    _Theorem_: For all lists [l1] and [l2],
       [length (l1 ++ l2) = length l1 + length l2].

    _Proof_: By induction on [l1].

    - First, suppose [l1 = []].  We must show
[[
        length ([] ++ l2) = length [] + length l2,
]]
      which follows directly from the definitions of
      [length], [++], and [plus].

    - Next, suppose [l1 = n::l1'], with
[[
        length (l1' ++ l2) = length l1' + length l2.
]]
      We must show
[[
        length ((n::l1') ++ l2) = length (n::l1') + length l2.
]]
      This follows directly from the definitions of [length] and [++]
      together with the induction hypothesis. [] *)

(** _Theorem_: For all lists [l], [length (rev l) = length l].

    _Proof_: By induction on [l].

      - First, suppose [l = []].  We must show
[[
          length (rev []) = length [],
]]
        which follows directly from the definitions of [length]
        and [rev].

      - Next, suppose [l = n::l'], with
[[
          length (rev l') = length l'.
]]
        We must show
[[
          length (rev (n :: l')) = length (n :: l').
]]
        By the definition of [rev], this follows from
[[
          length ((rev l') ++ [n]) = S (length l')
]]
        which, by the previous lemma, is the same as
[[
          length (rev l') + length [n] = S (length l').
]]
        This follows directly from the induction hypothesis and the
        definition of [length]. [] *)

(** TERSE: These proofs are rather longwinded.  We'd normally write
    them in a more compressed style: *)
(** FULL: The style of these proofs is rather longwinded and pedantic.
    After reading a couple like this, we might find it easier to
    follow proofs that give fewer details (which we can easily work
    out in our own minds or on scratch paper if necessary) and just
    highlight the non-obvious steps.  In this more compressed style,
    the above proof might look like this: *)

(** _Theorem_: For all lists [l], [length (rev l) = length l].

    _Proof_: First, observe that [length (l ++ [n]) = S (length l)]
     for any [l], by a straightforward induction on [l].  The main
     property again follows by induction on [l], using the observation
     together with the induction hypothesis in the case where [l =
     n'::l']. [] *)

(** FULL: Which style is preferable in a given situation depends on
    the sophistication of the expected audience and how similar the
    proof at hand is to ones that they will already be familiar with.
    The more pedantic style is a good default for our present
    purposes. *)

(* /FULL *)

(* FULL *)
(* ###################################################### *)
(** ** [Search] *)

(** We've seen that proofs can make use of other theorems we've
    already proved, e.g., using [rewrite].  But in order to refer to a
    theorem, we need to know its name!  Indeed, it is often hard even
    to remember what theorems have been proven, much less what they
    are called.

    Coq's [Search] command is quite helpful with this.  Typing [Search
    foo] into your .v file and evaluating this line will cause Coq to
    display a list of all theorems involving [foo].  For example, try
    uncommenting the following line to see a list of theorems that we
    have proved about [rev]: *)

(*  Search rev. *)

(** Keep [Search] in mind as you do the following exercises and
    throughout the rest of the book; it can save you a lot of time!

    If you are using ProofGeneral, you can run [Search] with
    [C-c C-a C-a]. Pasting its response into your buffer can be
    accomplished with [C-c C-;]. *)
(* /FULL *)

(* FULL *)
(* ###################################################### *)
(** ** List Exercises, Part 1 *)

(* EX3 (list_exercises) *)
(** More practice with lists: *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  (* ADMITTED *)
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> IHl'. reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: NatList.app_nil_r *)

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* ADMITTED *)
  intros l1 l2. induction l1 as [|x1 l1' IH].
  - rewrite app_nil_r. reflexivity.
  - simpl. rewrite IH. rewrite app_assoc. reflexivity.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: NatList.rev_app_distr *)

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  (* ADMITTED *)
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> rev_app_distr. rewrite -> IHl'. reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: NatList.rev_involutive *)

(** There is a short solution to the next one.  If you find yourself
    getting tangled up, step back and try to look for a simpler
    way. *)

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* ADMITTED *)
  intros l1 l2 l3 l4.
  rewrite -> app_assoc. rewrite -> app_assoc.
  reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: NatList.app_assoc4 *)

(** An exercise about your implementation of [nonzeros]: *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  (* ADMITTED *)
  intros l1 l2.  induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. destruct n as [| n'].
    + (* n = 0 *)
      rewrite -> IHl1'. reflexivity.
    + (* n = S n' *)
      rewrite -> IHl1'. reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: NatList.nonzeros_app *)
(** [] *)

(* EX2 (eqblist) *)
(* GRADE_THEOREM 2: NatList.eqblist_refl *)
(** Fill in the definition of [eqblist], which compares
    lists of numbers for equality.  Prove that [eqblist l l]
    yields [true] for every list [l]. *)

Fixpoint eqblist (l1 l2 : natlist) : bool
  (* ADMITDEF *) :=
  match l1,l2 with
  | nil,nil => true
  | h1::t1,h2::t2 => andb (h1 =? h2) (eqblist t1 t2)
  | _,_ => false
  end.
(* /ADMITDEF *)

Example test_eqblist1 :
  (eqblist nil nil = true).
 (* ADMITTED *)
Proof. reflexivity.  Qed.
(* /ADMITTED *)

Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
(* ADMITTED *)
Proof. reflexivity.  Qed.
(* /ADMITTED *)

Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  (* ADMITTED *)
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl.  rewrite <- eqb_refl.  rewrite <- IHl'.
    reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)

(* ###################################################### *)
(** ** List Exercises, Part 2 *)

(** Here are a couple of little theorems to prove about your
    definitions about bags above. *)

(* EX1 (count_member_nonzero) *)
Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  (* ADMITTED *)
  intros s.  reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)

(** The following lemma about [leb] might help you in the next exercise. *)
(* LATER: This should be lifted out of the section, since it is useful
   in later chapters. *)

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl.  reflexivity.
  - (* S n' *)
    simpl.  rewrite IHn'.  reflexivity.  Qed.

(** Before doing the next exercise, make sure you've filled in the
   definition of [remove_one] above. *)
(* EX3A (remove_does_not_increase_count) *)
(* HIDE *)
(* SOONER: CH: The following exercise is not so simple.  Also the
   shape of the theorem (with a magic constant [0]), and the fact that
   n needs to be destructed seem like big and ugly hacks. The
   hack-free theorem looks like this: *)
Lemma count_remove_one : forall v s,
  count v (remove_one v s) = pred (count v s).
Proof.
  intros v s. induction s as [| h t IHt].
  - (* s = nil *) reflexivity.
  - (* s = h :: t *) simpl.
    (* XXX they don't know about remember or eqn: yet !!! *)
    destruct (h =? v) eqn : Heqb.
    simpl. reflexivity.
    simpl. rewrite Heqb. rewrite IHt. reflexivity.
Qed.

Lemma leb_pred_n_n : forall n,
  (pred n) <=? n = true.
Proof.
  intros n. destruct n; simpl. reflexivity. rewrite leb_n_Sn. reflexivity.
Qed.

Theorem remove_does_not_increase_count': forall (s : bag) (n : nat),
  (count n (remove_one n s)) <=? (count n s) = true.
Proof.
  intros s n. induction s. simpl. reflexivity.
  rewrite count_remove_one. rewrite leb_pred_n_n. reflexivity.
Qed.
(* LATER: The only problem with this is that it uses remember, which
   they don't know yet. And it's a bit complicated.  BCP 9/16: Would
   be nice to include it as a separate (advanced, 3- or 4-star)
   exercise.  But we need to make sure there's a way for them to prove
   it using just what they know right now! APT 9/18: They now
   know about eqn: but still not officially about destructing
   over expressions, not just identifiers. *)

(* /HIDE *)
Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  (* ADMITTED *)
  intros s.  induction s as [| n s' IHs'].
  - (* s = nil *)
    simpl.  reflexivity.
  - (* s = cons *)
    simpl. destruct n as [| n'].
    + (* 0 *)
      simpl.  rewrite leb_n_Sn. reflexivity.
    + (* S n' *)
      simpl. rewrite IHs'. reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX3M? (bag_count_sum) *)
(** Write down an interesting theorem [bag_count_sum] about bags
    involving the functions [count] and [sum], and prove it using
    Coq.  (You may find that the difficulty of the proof depends on
    how you defined [count]!) *)
(* LATER: APT: This is the obvious theorem, and everyone came up with
   it.  But how hard it is to prove (in terms of Coq mechanics)
   depends critically on how the student defined [count] -- the
   solution for which has not been given at this point, and is not so
   obvious. BCP 9/16: For the moment, I've just added an explicit
   warning to this effect - not sure whether we can do better. (Is
   there a hint we could give about how count should have been
   defined, to make this easier?  There's no problem giving a hint
   here, since they'll already have solved the count exercise once
   before getting to this point.) MRC 1/19: The proof uses [destruct]
   on a term that is not merely an identifier. That usage has not
   been introduced yet. *)
(* SOLUTION *)
(** Here is one possible solution: *)

Theorem bag_count_sum : forall (s1 s2:bag), forall v:nat,
  count v (sum s1 s2) = count v s1 + count v s2.
Proof.
  intros s1 s2 v.
  induction s1 as [|v' s1'].
  - (* s1 = nil *)
    reflexivity.
  - (* s1 = v' :: s1' *)
    simpl. destruct (v' =? v).
    + (* v' = v *)
      rewrite IHs1'. simpl.
      reflexivity.
    + (* v' <> v *)
      apply IHs1'.   Qed.
(* /SOLUTION *)
(** [] *)

(* EX4AM (rev_injective) *)
(** Prove that the [rev] function is injective -- that is,
[[
    forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
]]
    (There is a hard way and an easy way to do this.) *)

(* HIDE: KK: Would it make sense to use this exercise to reiterate on
   the use of [Search]? We could add a hint in the lines of "If only
   there was a way to find already proven lemmas about rev". This
   change might however make this exercise be worth less than 4
   stars. *)

(* SOLUTION *)
(** The easy way is to use the fact that [rev] is an involution.  In
    general, every involution is injective.  The hard way is to go by
    induction on [l1], but this requires proving a bunch of subsidiary
    lemmas. *)
Theorem rev_injective : forall l1 l2, rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 Heq.
  rewrite <- rev_involutive.
  rewrite <- Heq.
  rewrite rev_involutive.
  reflexivity.
Qed.
(* /SOLUTION *)

(* GRADE_MANUAL 6: rev_injective *)
(** [] *)

(* /FULL *)
(* ###################################################### *)
(** * Options *)

(* HIDEFROMADVANCED *)
(** FULL: Suppose we want to write a function that returns the [n]th
    element of some list.  If we give it type [nat -> natlist -> nat],
    then we'll have to choose some number to return when the list is
    too short... *)
(** TERSE: We'd like to write a function to retrieve the [n]th element
    of a list, but what if the list is too short? *)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42
  | a :: l' => match n with
               | 0 => a
               | S n' => nth_bad l' n'
               end
  end.

(** TERSE: *** *)
(** FULL: This solution is not so good: If [nth_bad] returns [42], we
    can't tell whether that value actually appears on the input
    without further processing. A better alternative is to change the
    return type of [nth_bad] to include an error value as a possible
    outcome. We call this type [natoption]. *)
(* TERSE *)

(** The solution: [natoption]. *)
(* /TERSE *)
(* /HIDEFROMADVANCED *)

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

(* HIDEFROMADVANCED *)
(* LATER: Is it worth a comment that [Some] and [None] are capitalized
   when all our other constructors so far are lowercase?  Is there a
   sensible explanation of this, or is Coq's choice here random? *)

(* HIDE: KK: Maybe we should be explicit and note that constructors
   can also be capitalized (or all-caps), and that we capitalized
   these just to mirror Coq's option definition? *)

(** FULL: We can then change the above definition of [nth_bad] to
    return [None] when the list is too short and [Some a] when the
    list has enough members and [a] appears at position [n]. We call
    this new function [nth_error] to indicate that it may result in an
    error. *)
(* /HIDEFROMADVANCED *)

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

(* HIDEFROMADVANCED *)
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(* /HIDEFROMADVANCED *)
(** FULL: (In the HTML version, the boilerplate proofs of these
    examples are elided.  Click on a box if you want to see one.)

    This example is also an opportunity to introduce one more small
    feature of Coq's programming language: conditional
    expressions... *)
(* SOONER: Is it confusing that the version above matches on the
   number, while the version below matches (using "if") on a
   boolean? *)
(** TERSE: *** *)

(** TERSE: We can also write this function using Coq's "if" expressions.  *)

Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if n =? O then Some a
               else nth_error' l' (pred n)
  end.
(* HIDEFROMADVANCED *)

(* FULL *)
(** Coq's conditionals are exactly like those found in any other
    language, with one small generalization.  Since the [bool] type
    is not built in, Coq actually supports conditional expressions over
    _any_ inductively defined type with exactly two constructors.  The
    guard is considered true if it evaluates to the first constructor
    in the [Inductive] definition and false if it evaluates to the
    second. *)

(** The function below pulls the [nat] out of a [natoption], returning
    a supplied default in the [None] case. *)

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.
(* /HIDEFROMADVANCED *)

(* EX2 (hd_error) *)
(** Using the same idea, fix the [hd] function from earlier so we don't
    have to pass a default element for the [nil] case.  *)

Definition hd_error (l : natlist) : natoption
  (* ADMITDEF *) :=
  match l with
  | nil    => None
  | n :: l => Some n
  end.
(* /ADMITDEF *)

Example test_hd_error1 : hd_error [] = None.
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)

Example test_hd_error2 : hd_error [1] = Some 1.
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)

Example test_hd_error3 : hd_error [5;6] = Some 5.
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)
(** [] *)

(* EX1? (option_elim_hd) *)
(* GRADE_THEOREM 2: NatList.option_elim_hd *)
(** This exercise relates your new [hd_error] to the old [hd]. *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  (* ADMITTED *)
  intros l. destruct l as [|n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.  Qed.
  (* /ADMITTED *)
(** [] *)

(* /FULL *)
End NatList.

(* HIDEFROMADVANCED *)
(* ###################################################### *)
(** * Partial Maps *)

(** As a final illustration of how data structures can be defined in
    Coq, here is a simple _partial map_ data type, analogous to the
    map or dictionary data structures found in most programming
    languages. *)

(** First, we define a new inductive datatype [id] to serve as the
    "keys" of our partial maps. *)

Inductive id : Type :=
  | Id (n : nat).

(** Internally, an [id] is just a number.  Introducing a separate type
    by wrapping each nat with the tag [Id] makes definitions more
    readable and gives us more flexibility. *)

(** TERSE: *** *)
(** We'll also need an equality test for [id]s: *)

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

(* TERSE: HIDEFROMHTML *)
(* EX1 (eqb_id_refl) *)
(* GRADE_THEOREM 1: eqb_id_refl *)
Theorem eqb_id_refl : forall x, true = eqb_id x x.
Proof.
  (* ADMITTED *)
  intros [n]. simpl. rewrite <- eqb_refl. reflexivity. Qed.
(* /ADMITTED *)
(** [] *)
(* TERSE: /HIDEFROMHTML *)

(** TERSE: *** *)
(** Now we define the type of partial maps: *)
(* TERSE: HIDEFROMHTML *)

Module PartialMap.
Export NatList.
(* TERSE: /HIDEFROMHTML *)
  (* HIDE: For natoption *)

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

(* FULL *)
(** This declaration can be read: "There are two ways to construct a
    [partial_map]: either using the constructor [empty] to represent an
    empty partial map, or applying the constructor [record] to
    a key, a value, and an existing [partial_map] to construct a
    [partial_map] with an additional key-to-value mapping." *)
(* /FULL *)

(** TERSE: *** *)
(** The [update] function overrides the entry for a given key in a
    partial map by shadowing it with a new one (or simply adds a new
    entry if the given key is not already present). *)

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

(* FULL *)
(** Last, the [find] function searches a [partial_map] for a given
    key.  It returns [None] if the key was not found and [Some val] if
    the key was associated with [val]. If the same key is mapped to
    multiple values, [find] will return the first one it
    encounters. *)
(* /FULL *)
(** TERSE: *** *)
(** TERSE: We can define functions on [partial_map] by pattern
    matching, as always. *)

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

(* QUIZ *)
(** Is the following claim true or false? *)
Theorem quiz1 : forall (d : partial_map)
                       (x : id) (v: nat),
  find x (update d x v) = Some v.

(* HIDEFROMHTML *)
Proof.
(* ADMITTED *)
  intros d x v.
  simpl.
  rewrite <- eqb_id_refl.
  reflexivity.
Qed. (* /ADMITTED *)
(* /HIDEFROMHTML *)

(** (1) True

    (2) False

    (3) Not sure
*)
(* /QUIZ *)

(* QUIZ *)
(** Is the following claim true or false? *)

Theorem quiz2 : forall (d : partial_map)
                       (x y : id) (o: nat),
  eqb_id x y = false ->
  find x (update d y o) = find x d.
(* HIDEFROMHTML *)
Proof.
(* ADMITTED *)
  destruct d as [|y' d'].
  - (* empty partial_map *)
    simpl. intros x y o H. rewrite H.
    reflexivity.
  - (* nonempty partial_map *)
    simpl. intros x n1 o H. rewrite H.
    reflexivity.
Qed. (* /ADMITTED *)
(* /HIDEFROMHTML *)

(** (1) True

    (2) False

    (3) Not sure
*)

(* /QUIZ *)
(* FULL *)
(* EX1 (update_eq) *)
(* GRADE_THEOREM 1: PartialMap.update_eq *)
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
 (* ADMITTED *)
intros d x v.
simpl. rewrite <- eqb_id_refl. reflexivity.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX1 (update_neq) *)
(* GRADE_THEOREM 1: PartialMap.update_neq *)
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
 (* ADMITTED *)
intros d x y o H0.
simpl. rewrite -> H0. reflexivity.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)
(* /HIDEFROMADVANCED *)
(* TERSE: HIDEFROMHTML *)
End PartialMap.
(* TERSE: /HIDEFROMHTML *)

(* HIDE: KK: Also this exercise comes out of the blue without any
   motivation/introduction. *)

(* FULL *)
(* EX2M (baz_num_elts) *)
(* LATER: I'm not sure the material covered up to here suffices
   to understand that Inductive types must have finite elements
   and avoid the trap of coming up with infinite lists. *)
(** Consider the following inductive definition: *)

Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).

(** How _many_ elements does the type [baz] have? (Explain in words,
    in a comment.) *)

(* SOLUTION *)
(** None!  In order to create an element of type [baz], we would need
    to use one of the two constructors [Baz1] and [Baz2]; but both of
    these require a [baz] as an argument.  So this definition cannot
    get off the ground: in order to create a [baz] we would need to
    already have one. *)
(* /SOLUTION *)
(* LATER: Rework this exercise for easier grading? *)

(* HIDE *)

(* LATER: KK: I am not sure whether this point should be made through a
   "manual" exercise like the one below. The students who don't know
   (or notice) that an Inductive definition needs a base case will
   just fail this exercise and will only see the reason in the grader
   comment. It is very easy for a student to falsely think that they
   have the right answer here and just move on without thinking about
   it. I think that it would be better to either add a small section
   that clearly explains this concept, or maybe add a hint similar to
   the one below: *)

(* Hint: Try to write a value of type baz for which the following
   lemma [one_true_baz] holds. *)

Fixpoint count_trues (x : baz) : nat :=
  match x with
  | Baz1 x' => count_trues x'
  | Baz2 x' true => 1 + count_trues x'
  | Baz2 x' _ => count_trues x'
  end.

(* Lemma one_true_baz : count_trues (your baz here) = 1. *)

(* /HIDE *)

(* GRADE_MANUAL 2: baz_num_elts *)
(** [] *)

(* /FULL *)
(* HIDE *)
(* Local Variables: *)
(* fill-column: 70  *)
(* End:             *)
(* /HIDE *)
