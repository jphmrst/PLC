---
title     : "NatData: Data structures with natural numbers"
layout    : page
prev      : /Naturals/
permalink : /NatData/
next      : /
---

```
module plc.fp.NatData where
open import plc.fp.Naturals
open import Data.Bool

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
```

## Pairs of numbers

In a `data` definition, each constructor can take any number of
arguments — none (as with `true`, `false` and `zero`), one (as with
`suc`), or more than one:

```
data NatProd : Set where
  pair : ℕ → ℕ → NatProd
```

This declaration can be read: "The one and only way to construct a
pair of numbers is by applying the constructor `pair` to two arguments
of type ℕ."

#### Exercise `trynatpair` (starting) {#trynatpair}

Write an expression for forming a `NatProd` from the natural numbers
`3` and `5`.  Use the `C-c C-n` key sequence as in Exercise
`try-nat-defs` to check your expression.

### Extractng the elements of a pair

Here are simple functions for extracting the first and second
components of a pair:

```
fst : NatProd → ℕ
fst (pair x y) = x

snd : NatProd → ℕ
snd (pair x y) = y
```

And here is a function for swapping the two elements of a pair:

```
swapPair : NatProd → NatProd
swapPair (pair x y) = pair y x
```

## Lists of numbers

Pairs have only one possible form.  But to represent singly-linked
lists, we must account for two possible forms in the same way that
natural numbers have two possible forms.  A list of natural numbers is
either the empty list, or else a pair of a number and another list.

```
infixr 5 _::_

data NatList : Set where
  [] : NatList
  _::_ : ℕ → NatList → NatList
```

We are using symbols here rather than a name written with letters as
before — but Agda has very few "special" characters, so these are
valid names just as `pair` is a valid name.  The name `[]`, often
pronounced _nil_, represents the empty list.  It is a constructor, but
needs no arguments to construct the value.  The constructor `::` is
often pronounced _cons_.  The first argument to a `::` constructor is
what we call the _head_ or a list, and the second argument is what we
call the _tail_.

The underscores `_` _are_ special characters, and are not part of the
name.  As with operators like `≡` and `+` which we have seen before,
the underscore shows how `::` shows be written with its first argument
before it, and its second argument after it.

The `infixr` declaration tells Agda that we want `::` to be
_right-associative_.  That is, if we write `x :: y :: z` for some
expressions `x`, `y` and `z`, then we want Agda to understand that
expressions to be the same as `x :: (y :: z)`, and **not** `(x :: y)
:: z`.  The number `5` tells Agda that most other operations should be
grouped before applying `::`.  So for example, `x :: y + 2 :: z` will
mean `x :: (y + 2) :: z`, and not `(x :: y) + (2 :: z)`.  This value
is called the _precedence_ of the `::` operator.

For example, here is a three-element list:

```
mylist : NatList
mylist = 10 :: 20 :: 30 :: []
```

#### Exercise `trynatlist` (starting) {#trynatlist}

Write an expression for the list containing the numbers 10, 9, 8, 7
and 6 (in that order).

### Functions on lists

Next let's look at several functions for constructing and manipulating
lists.  First, the `repeat` function takes a number `n` and a `count`
and returns a list of length `count` in which every element is `n`.

```
repeat : ℕ -> ℕ -> NatList
repeat n zero = []
repeat n (suc count') = n :: repeat n count'
```

The `length` function calculates the length of a list.

```
length : NatList -> ℕ
length [] = 0
length (x :: xs) = 1 + length xs
```

The `++` function (pronounced "append") concatenates two lists.

```
infixr 5 _++_

_++_ : NatList → NatList → NatList
[] ++ ys = ys
(x :: xs) ++ ys = x :: xs ++ ys
```

A list appended to a non-empty list yields a list with the head the
same as the head of the non-empty list, and a tail the same as the
other list appended to tail of the non-empty list.

#### Exercise `tryrepeat` (starting) {#tryrepeat}

Does the expression `repeat 3 5` produce a list of length 3 containing
the number 5, or a list of length 5 containing the number 3?  Work out
your answer from the definition before using a call to Agda to check
your idea.  What happens if either the first or last argument is an
empty list?  Both?

#### Exercise `nonzeros` (practice) {#nonzeros}

Complete the definition of `nonzeros`.  The assertion after the
definition template shows (to both you and to Agda) what the function
should do.  The exercises will often include these statements, which
serve as tests for your code: if Agda cannot transform the expression
`nonzeros (0 :: 1 :: 0 :: 2 :: 3 :: 0 :: 0 :: [])` into the expression
`1 :: 2 :: 3 :: []` using your definition of `nonzeros`, then loading
the file will raise an error.

But as in earlier examples, you must add a third backtick to the code
below so that Agda actually does load your code and the test.  Having
this file load successfully because Agda ignores your code for this
exercise is not a form of success on the exercise!

    nonzeros : NatList → NatList
    nonzeros [] = []
    -- Add your cases here

    _ : nonzeros (0 :: 1 :: 0 :: 2 :: 3 :: 0 :: 0 :: []) ≡ (1 :: 2 :: 3 :: [])
    _ = refl

#### Exercise `oddmembers` (practice) {#oddmembers}

Complete the definition of `oddmembers`. Have a look at the test to
understand what it should do, and use the function `odd` from Chapter
Naturals.

    oddmembers : NatList -> NatList
    -- Add your cases here

    _ : oddmembers (0 :: 1 :: 2 :: 3 :: 3 :: 0 :: []) ≡ (1 :: 3 :: 3 :: [])
    _ = refl

#### Exercise `countoddmembers` (practice) {#countoddmembers}

Complete the definition of `countoddmembers`, using the tests
to understand what these functions should do.

    countoddmembers : NatList -> ℕ
    -- Your definition goes here
    
    _ : countoddmembers (0 :: 1 :: 2 :: 3 :: 3 :: 0 :: []) ≡ 3
    _ = refl
    
    _ : countoddmembers (0 :: 2 :: 0 :: []) ≡ 0
    _ = refl
    
    _ : countoddmembers [] ≡ 0
    _ = refl

#### Exercise `alternate` (practice) {#alternate}

Complete the following definition of `alternate`, which interleaves
two lists into one, alternating between elements taken from the first
list and elements from the second.  See the tests below for more
specific examples.

Hint: one natural and elegant way of writing `alternate` will fail to
satisfy Coq's requirement that all function definitions be "obviously
terminating."  If you find yourself in this rut, look for a slightly
more verbose solution that considers elements of both lists at the
same time.  One possible solution involves defining a new kind of
pairs, but this is not the only way.

    alternate : NatList → NatList → NatList
    -- Your solution goes here

    _ : alternate (1 :: 2 :: 3 :: []) (4 :: 5 :: 6 :: [])
                   ≡ (1 :: 4 :: 2 :: 5 :: 3 :: 6 :: [])
    _ = refl

    _ : alternate (1 :: 2 :: 3 :: []) (4 :: []) ≡ (1 :: 4 :: 2 :: 3 :: [])
    _ = refl

## Bags via lists

A _bag_ (or _multiset_) is like a set, except that each element can
appear multiple times rather than just once.  One possible
representation for a bag of numbers is as a list.

```
Bag : Set
Bag = NatList
``

#### Exercise `bagcount` (practice) {#bagcount}

Complete the following definition of `count` which returns the number
of times a particular value occurs in a bag.

    count : ℕ → bag → ℕ
    -- Your definition goes here

    _ : count 1 [1;2;3;1;4;1] = 3
    _ = refl

    _ : count 6 [1;2;3;1;4;1] = 0
    _ = refl

#### Exercise `bagsum` (practice) {#bagsum}

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

Theorem nil_app : forall l:NatList,
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

Theorem tl_length_pred : forall l:NatList,
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

(** FULL: Proofs by induction over datatypes like [NatList] are a
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

Theorem app_assoc : forall l1 l2 l3 : NatList,
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

Fixpoint rev (l:NatList) : NatList :=
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

Theorem rev_length_firsttry : forall l : NatList,
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
Theorem app_length : forall l1 l2 : NatList,
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
    quantify over _all_ [NatList]s, not just those that result from an
    application of [rev].  This should seem natural, because the truth
    of the goal clearly doesn't depend on the list having been
    reversed.  Moreover, it is easier to prove the more general
    property. *)

(** TERSE: *** *)
(* HIDEFROMADVANCED *)
(** Now we can complete the original proof. *)
(* /HIDEFROMADVANCED *)

Theorem rev_length : forall l : NatList,
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
      Theorem foo1 : forall n :nat, forall l: NatList,
        repeat n 0 = l -> length l = 0.
]]
*)
(* HIDE *)
Theorem foo1 : forall n : nat, forall l : NatList,
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
      Theorem foo2 :  forall n m:nat, forall l: NatList,
        repeat n m = l -> length l = m.
]]
    Which tactics do we need besides [intros], [simpl], [rewrite], and
    [reflexivity]?  (1) none, (2) [destruct],
    (3) [induction on m], (4) [induction on l], or (5) can't be
    done with the tactics we've seen.
*)
(* HIDE *)
Theorem foo2 :  forall n m : nat, forall l : NatList,
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
      Theorem foo3: forall n :nat, forall l1 l2: NatList,
        l1 ++ [n] = l2 -> (1 <=? (length l2)) = true.
]]
    Which tactics do we need besides [intros], [simpl], [rewrite], and
    [reflexivity]?  (1) none, (2) [destruct],
    (3) [induction on n], (4) [induction on l1], (5) [induction on l2],
    (6) can't be done with the tactics we've seen.
*)
(* HIDE *)
(*
Theorem foo3 :  forall n :nat, forall l1 l2: NatList,
l1 ++ [n] = l2 -> (1 <=? (length l2)) = true.
Proof.
  intros n l1 l2 H. rewrite <- H. rewrite app_length. simpl.
Qed.

Theorem foo3' :  forall n :nat, forall l1 l2: NatList,
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

Theorem app_nil_r : forall l : NatList,
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

Theorem rev_app_distr: forall l1 l2 : NatList,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* ADMITTED *)
  intros l1 l2. induction l1 as [|x1 l1' IH].
  - rewrite app_nil_r. reflexivity.
  - simpl. rewrite IH. rewrite app_assoc. reflexivity.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: NatList.rev_app_distr *)

Theorem rev_involutive : forall l : NatList,
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

Theorem app_assoc4 : forall l1 l2 l3 l4 : NatList,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* ADMITTED *)
  intros l1 l2 l3 l4.
  rewrite -> app_assoc. rewrite -> app_assoc.
  reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 0.5: NatList.app_assoc4 *)

(** An exercise about your implementation of [nonzeros]: *)

Lemma nonzeros_app : forall l1 l2 : NatList,
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

Fixpoint eqblist (l1 l2 : NatList) : bool
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

Theorem eqblist_refl : forall l:NatList,
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
    forall (l1 l2 : NatList), rev l1 = rev l2 -> l1 = l2.
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
    element of some list.  If we give it type [nat -> NatList -> nat],
    then we'll have to choose some number to return when the list is
    too short... *)
(** TERSE: We'd like to write a function to retrieve the [n]th element
    of a list, but what if the list is too short? *)

Fixpoint nth_bad (l:NatList) (n:nat) : nat :=
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

Fixpoint nth_error (l:NatList) (n:nat) : natoption :=
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

Fixpoint nth_error' (l:NatList) (n:nat) : natoption :=
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

Definition hd_error (l : NatList) : natoption
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

Theorem option_elim_hd : forall (l:NatList) (default:nat),
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

---

*This page is derived from Pierce et al., with some short exceprts
from Wadler et al.; for more information see the [sources and
authorship]({{ site.baseurl }}/Sources/) page.*
