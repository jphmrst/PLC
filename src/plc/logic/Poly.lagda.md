
```
module plc.logic.Poly where
open import Data.Bool
open import Data.Nat

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
```

(** * Poly: Polymorphism and Higher-Order Functions *)

## Properties of lists

(* TERSE: HIDEFROMHTML *)
(* ###################################################### *)
(** *** Exercises *)

(* EX2? (poly_exercises) *)
(** Here are a few simple exercises, just like ones in the [Lists]
    chapter, for practice with polymorphism.  Complete the proofs below. *)

(* INSTRUCTORS: There's a little inconsistency between this definition
   and the standard library one: in the library, the type argument is
   implicit. :-( I (BCP) have chosen to leave things inconsistent to
   avoid having to explain about implicit arguments to theorems, which
   wouldn't make sense at this point. *)
Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  (* ADMITTED *)
  intros X l. induction l as [|x l' IH].
  - reflexivity.
    - simpl. rewrite IH. reflexivity.
Qed.
(* /ADMITTED *)

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  (* ADMITTED *)
  intros A l m n.
  induction l as [|a l' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
(* /ADMITTED *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  (* ADMITTED *)
  intros X l1. induction l1 as [|x l1'].
  - (* l1 = nil *) reflexivity.
  - (* l1 = x::l1' *) intros l2.  simpl. rewrite -> IHl1'. reflexivity. Qed.
(* /ADMITTED *)
(** [] *)

(* EX2? (more_poly_exercises) *)
(** Here are some slightly more interesting ones... *)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* ADMITTED *)
  intros X l1 l2. induction l1 as [|x1 l1' IH].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IH. rewrite app_assoc. reflexivity. Qed.
(* /ADMITTED *)

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  (* ADMITTED *)
  intros X l. induction l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> rev_app_distr. rewrite -> IHl'. reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)
(* /HIDEFROMADVANCED *)
(* HIDEFROMADVANCED *)
(* TERSE: /HIDEFROMHTML *)
(* /HIDEFROMADVANCED *)
(* HIDE: CH: With -advanced the HIDEFROMHTML command above was appearing in
         the generated slides, so I put it inside HIDEFROMADVANCED  *)

(* ###################################################### *)
(** ** Polymorphic Pairs *)

(** FULL: Following the same pattern, the definition for pairs of
    numbers that we gave in the last chapter can be generalized to
    _polymorphic pairs_, often called _products_: *)
(** TERSE: Similarly... *)

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.

(** FULL: As with lists, we make the type arguments implicit and define the
    familiar concrete notation. *)

Notation "( x , y )" := (pair x y).

(* HIDEFROMADVANCED *)
(** We can also use the [Notation] mechanism to define the standard
    notation for product _types_: *)

(* /HIDEFROMADVANCED *)
Notation "X * Y" := (prod X Y) : type_scope.

(** (The annotation [: type_scope] tells Coq that this abbreviation
    should only be used when parsing types, not when parsing
    expressions.  This avoids a clash with the multiplication
    symbol.) *)

(** FULL: It is easy at first to get [(x,y)] and [X*Y] confused.
    Remember that [(x,y)] is a _value_ built from two other values,
    while [X*Y] is a _type_ built from two other types.  If [x] has
    type [X] and [y] has type [Y], then [(x,y)] has type [X*Y]. *)
(** TERSE: Be careful not to get [(X,Y)] and [X*Y] confused! *)
(** TERSE: *** *)

(** FULL: The first and second projection functions now look pretty
    much as they would in any functional programming language. *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(** FULL: The following function takes two lists and combines them
    into a list of pairs.  In other functional languages, it is often
    called [zip]; we call it [combine] for consistency with Coq's
    standard library. *)
(** TERSE: *** *)
(** TERSE: What does this function do? *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(* FULL *)
(* EX1M? (combine_checks) *)
(** Try answering the following questions on paper and
    checking your answers in Coq:
    - What is the type of [combine] (i.e., what does [Check
      @combine] print?)
    - What does
[[
        Compute (combine [1;2] [false;false;true;true]).
]]
      print? *)
(** [] *)

(* EX2! (split) *)
(** The function [split] is the right inverse of [combine]: it takes a
    list of pairs and returns a pair of lists.  In many functional
    languages, it is called [unzip].

    Fill in the definition of [split] below.  Make sure it passes the
    given unit test. *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y)
  (* ADMITDEF *) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.
(* /ADMITDEF *)

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
(* ADMITTED *)
  reflexivity.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: split *)
(* GRADE_THEOREM 1: test_split *)
(** [] *)
(* /FULL *)

## Polymorphic options

Our last polymorphic type for now is _polymorphic options_, which
generalize [natoption] from the previous chapter.  (We put the
definition inside a module because the standard library already
defines [option] and it's this one that we want to use below.)

Module OptionPlayground.

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X} _.
Arguments None {X}.

End OptionPlayground.

(** TERSE: *** *)
(** FULL: We can now rewrite the [nth_error] function so that it works
    with any type of lists. *)

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if n =? O then Some a else nth_error l' (pred n)
  end.

(* HIDEFROMADVANCED *)
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
Example test_nth_error3 : nth_error [true] 2 = None.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(* /HIDEFROMADVANCED *)
(* FULL *)
(* EX1? (hd_error_poly) *)
(** Complete the definition of a polymorphic version of the
    [hd_error] function from the last chapter. Be sure that it
    passes the unit tests below. *)

Definition hd_error {X : Type} (l : list X) : option X
  (* ADMITDEF *) :=
  match l with
  | [] => None
  | a :: l' => Some a
  end.
(* /ADMITDEF *)

(** Once again, to force the implicit arguments to be explicit,
    we can use [@] before the name of the function. *)

Check @hd_error : forall X : Type, list X -> option X.

Example test_hd_error1 : hd_error [1;2] = Some 1.
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)
Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1].
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)
(** [] *)
(* /FULL *)

(* ###################################################### *)
(** * Functions as Data *)

(* HIDEFROMADVANCED *)
(** FULL: Like most modern programming languages -- especially other
    "functional" languages, including OCaml, Haskell, Racket, Scala,
    Clojure, etc. -- Coq treats functions as first-class citizens,
    allowing them to be passed as arguments to other functions,
    returned as results, stored in data structures, etc. *)
(* /HIDEFROMADVANCED *)

(* ###################################################### *)
(** ** Higher-Order Functions *)

(* HIDEFROMADVANCED *)
(** FULL: Functions that manipulate other functions are often called
    _higher-order_ functions.  Here's a simple one: *)
(** TERSE: Functions in Coq are _first class_. *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

(** FULL: The argument [f] here is itself a function (from [X] to
    [X]); the body of [doit3times] applies [f] three times to some
    value [n]. *)

Check @doit3times : forall X : Type, (X -> X) -> X -> X.

Example test_doit3times: doit3times minustwo 9 = 3.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

Example test_doit3times': doit3times negb true = false.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(* ###################################################### *)
(** ** Filter *)

(* /HIDEFROMADVANCED *)
(* INSTRUCTORS: We've tried to be careful with terminology in the rest
   of the notes: "(boolean) predicate" for boolean functions and
   "property" for propositions indexed by one parameter. *)
(** FULL: Here is a more useful higher-order function, taking a list
    of [X]s and a _predicate_ on [X] (a function from [X] to [bool])
    and "filtering" the list, returning a new list containing just
    those elements for which the predicate returns [true]. *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(** FULL: For example, if we apply [filter] to the predicate [evenb]
    and a list of numbers [l], it returns a list containing just the
    even members of [l]. *)

(* HIDEFROMADVANCED *)
Example test_filter1: filter evenb [1;2;3;4] = [2;4].
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(** TERSE: *** *)
Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(** TERSE: *** *)
(* LATER: This material would sink in better if it were made clearer
   why map and filter and such were useful in the real world.  Talk
   about map/reduce, collection-oriented programming, etc.  Esp in the
   terse version. *)
(** TERSE: The [filter] function -- together with some other functions
    we'll see later -- enables a powerful _collection-oriented_
    programming style. *)
(** FULL: We can use [filter] to give a concise version of the
    [countoddmembers] function from the \CHAP{Lists} chapter. *)

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
Example test_countoddmembers'3:   countoddmembers' nil = 0.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(* /HIDEFROMADVANCED *)
(* ###################################################### *)
(** ** Anonymous Functions *)

(* LATER: Why not show them [fix] here?  It's not that complicated and
   it fills out the story.  At least as a little optional section.

   BAY: I'm not convinced it's "not that complicated" for people who
   have never seen much functional programming before.  I think adding
   a discussion of fix could easily take 20 minutes of class time.

   BCP: Yes, this doesn't belong in lecture, probably.  But it might
   still be useful as an optional section for people to read.

   (2013: Now that we've created the idea of "advanced" sections, this
   seems like a nice candidate.) *)

(** FULL: It is arguably a little sad, in the example just above, to
    be forced to define the function [length_is_1] and give it a name
    just to be able to pass it as an argument to [filter], since we
    will probably never use it again.  Moreover, this is not an
    isolated example: when using higher-order functions, we often want
    to pass as arguments "one-off" functions that we will never use
    again; having to give each of these functions a name would be
    tedious.

    Fortunately, there is a better way.  We can construct a function
    "on the fly" without declaring it at the top level or giving it a
    name. *)
(** TERSE: Functions can be constructed "on the fly" without giving
    them names. *)
(* HIDEFROMADVANCED *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(** The expression [(fun n => n * n)] can be read as "the function
    that, given a number [n], yields [n * n]." *)

(* /HIDEFROMADVANCED *)
(** FULL: Here is the [filter] example, rewritten to use an anonymous
    function. *)

Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(* FULL *)
(* EX2 (filter_even_gt7) *)
(** Use [filter] (instead of [Fixpoint]) to write a Coq function
    [filter_even_gt7] that takes a list of natural numbers as input
    and returns a list of just those that are even and greater than
    7. *)

Definition filter_even_gt7 (l : list nat) : list nat
  (* ADMITDEF *) :=
  filter (fun n => andb (evenb n) (ltb 7 n)) l.
  (* /ADMITDEF *)

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
 (* ADMITTED *)
Proof. reflexivity. Qed.
 (* /ADMITTED *)

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
 (* ADMITTED *)
Proof. reflexivity. Qed.
 (* /ADMITTED *)
(* GRADE_THEOREM 1: test_filter_even_gt7_1 *)
(* GRADE_THEOREM 1: test_filter_even_gt7_2 *)
(** [] *)

(* EX3 (partition) *)
(** Use [filter] to write a Coq function [partition]:
[[
      partition : forall X : Type,
                  (X -> bool) -> list X -> list X * list X
]]
   Given a set [X], a predicate of type [X -> bool] and a [list X],
   [partition] should return a pair of lists.  The first member of the
   pair is the sublist of the original list containing the elements
   that satisfy the test, and the second is the sublist containing
   those that fail the test.  The order of elements in the two
   sublists should be the same as their order in the original list. *)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X
  (* ADMITDEF *) :=
  (filter test l, filter (fun x => negb (test x)) l).
(* /ADMITDEF *)

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
(* ADMITTED *)
Proof. reflexivity. Qed.
(* /ADMITTED *)
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
(* ADMITTED *)
Proof. reflexivity. Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: partition *)
(* GRADE_THEOREM 1: test_partition1 *)
(* GRADE_THEOREM 1: test_partition2 *)
(** [] *)
(* /FULL *)

(* ###################################################### *)
(** ** Map *)

(** FULL: Another handy higher-order function is called [map]. *)

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(** FULL: It takes a function [f] and a list [ l = [n1, n2, n3, ...] ]
    and returns the list [ [f n1, f n2, f n3,...] ], where [f] has
    been applied to each element of [l] in turn.  For example: *)

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(* HIDEFROMADVANCED *)
(** FULL: The element types of the input and output lists need not be
    the same, since [map] takes _two_ type arguments, [X] and [Y]; it
    can thus be applied to a list of numbers and a function from
    numbers to booleans to yield a list of booleans: *)

Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(** FULL: It can even be applied to a list of numbers and
    a function from numbers to _lists_ of booleans to
    yield a _list of lists_ of booleans: *)

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(* TERSE *)
(* QUIZ *)
(** Recall the definition of [map]:
[[
      Fixpoint map {X Y: Type} (f:X->Y) (l:list X)
                   : (list Y) :=
        match l with
        | []     => []
        | h :: t => (f h) :: (map f t)
        end.
]]
    What is the type of [map]?

    (1) [forall X Y : Type, X -> Y -> list X -> list Y]

    (2) [X -> Y -> list X -> list Y]

    (3) [forall X Y : Type, (X -> Y) -> list X -> list Y]

    (4) [forall X : Type, (X -> X) -> list X -> list X]
*)
(* /QUIZ *)

(* HIDE *)
  (* HIDE: This one relies on partial application, which hasn't
     been explained. *)
  (* QUIZ *)
  (** Recall that [evenb] has type [nat -> bool].

      What is the type of [map evenb]?

      (1) [forall X Y : Type, (X -> Y) -> list X -> list Y]

      (2) [list nat -> list bool]

      (3) [list nat -> list Y]

      (4) [forall Y : Type, list nat -> list Y] *)
  (* /QUIZ *)
(* /HIDE *)
(* /TERSE *)

(** TERSE: *** *)
(** FULL: *** Exercises *)

(* FULL *)
(* EX3 (map_rev) *)
(** Show that [map] and [rev] commute.  You may need to define an
    auxiliary lemma. *)
(* QUIETSOLUTION *)

Theorem map_app : forall (A B : Type) (f : A -> B) (l l' : list A),
  map f (l ++ l') = map f l ++ map f l'.
Proof.
  intros A B f l l'. induction l as [|x l1 IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* /QUIETSOLUTION *)
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  (* ADMITTED *)
  intros X Y f l. induction l as [| v l' IHl'].
  - (* l = [] *)
    reflexivity.
  - (* l = v :: l' *)
    simpl. rewrite -> map_app. rewrite -> IHl'. reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: map_rev *)
(** [] *)

(* EX2! (flat_map) *)
(** The function [map] maps a [list X] to a [list Y] using a function
    of type [X -> Y].  We can define a similar function, [flat_map],
    which maps a [list X] to a [list Y] using a function [f] of type
    [X -> list Y].  Your definition should work by 'flattening' the
    results of [f], like so:
[[
        flat_map (fun n => [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].
]]
*)

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : (list Y)
  (* ADMITDEF *) :=
  match l with
  | []     => []
  | h :: t => (f h) ++ (flat_map f t)
  end.
(* /ADMITDEF *)

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)
(* GRADE_THEOREM 1: flat_map *)
(* GRADE_THEOREM 1: test_flat_map1 *)
(** [] *)
(* /FULL *)
(* HIDEFROMADVANCED *)

(** Lists are not the only inductive type for which [map] makes sense.
    Here is a [map] for the [option] type: *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(* /HIDEFROMADVANCED *)
(* FULL *)
(* EX2? (implicit_args) *)
(** The definitions and uses of [filter] and [map] use implicit
    arguments in many places.  Replace the curly braces around the
    implicit arguments with parentheses, and then fill in explicit
    type parameters where necessary and use Coq to check that you've
    done so correctly.  (This exercise is not to be turned in; it is
    probably easiest to do it on a _copy_ of this file that you can
    throw away afterwards.)
*)
(** [] *)
(* /FULL *)
(* /HIDEFROMADVANCED *)

(* ###################################################### *)
(** ** Fold *)

(** FULL: An even more powerful higher-order function is called
    [fold].  This function is the inspiration for the "[reduce]"
    operation that lies at the heart of Google's map/reduce
    distributed programming framework. *)

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** TERSE: This is the "reduce" in map/reduce... *)

(* HIDEFROMADVANCED *)
(** TERSE: *** *)

(** FULL: Intuitively, the behavior of the [fold] operation is to
    insert a given binary operator [f] between every pair of elements
    in a given list.  For example, [ fold plus [1;2;3;4] ] intuitively
    means [1+2+3+4].  To make this precise, we also need a "starting
    element" that serves as the initial second input to [f].  So, for
    example,
[[
       fold plus [1;2;3;4] 0
]]
    yields
[[
       1 + (2 + (3 + (4 + 0))).
]]
    Some more examples: *)

Check (fold andb) : list bool -> bool -> bool.

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

Example fold_example3 :
  fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4].
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(* TERSE *)
(* QUIZ *)
(** Here is the definition of [fold] again:
[[
     Fixpoint fold {X Y: Type}
                   (f: X->Y->Y) (l: list X) (b: Y)
                 : Y :=
       match l with
       | nil => b
       | h :: t => f h (fold f t b)
       end.
]]
    What is the type of [fold]?

    (1) [forall X Y : Type, (X -> Y -> Y) -> list X -> Y -> Y]

    (2) [X -> Y -> (X -> Y -> Y) -> list X -> Y -> Y]

    (3) [forall X Y : Type, X -> Y -> Y -> list X -> Y -> Y]

    (4) [X -> Y->  X -> Y -> Y -> list X -> Y -> Y]

*)
(* /QUIZ *)

(* QUIZ *)
(** What is the type of [fold plus]?

    (1) [forall X Y : Type, list X -> Y -> Y]

    (2) [nat -> nat -> list nat -> nat -> nat]

    (3) [forall Y : Type, list nat -> Y -> nat]

    (4) [list nat -> nat -> nat]

    (5) [forall X Y : Type, list nat -> nat -> nat]

*)
(* /QUIZ *)

(* QUIZ *)
(** What does [fold plus [1;2;3;4] 0] simplify to?

   (1) [[1;2;3;4]]

   (2) [0]

   (3) [10]

   (4) [[3;7;0]]

*)
(* /QUIZ *)
(* /TERSE *)
(* /HIDEFROMADVANCED *)

(* FULL *)
(* EX1AM (fold_types_different) *)
(** Observe that the type of [fold] is parameterized by _two_ type
    variables, [X] and [Y], and the parameter [f] is a binary operator
    that takes an [X] and a [Y] and returns a [Y].  Can you think of a
    situation where it would be useful for [X] and [Y] to be
    different? *)

(* SOLUTION *)
(** There are many.  For example, we could use [fold] to count the
    number of [true] elements in a list of booleans.  Here [X] would
    be [bool] and [Y] would be [nat]. *)
(* /SOLUTION *)
(* SOONER: make this easier for advanced grading? *)

(* GRADE_MANUAL 1: fold_types_different *)
(** [] *)
(* /FULL *)

(* HIDEFROMADVANCED *)
(* ###################################################### *)
(** ** Functions That Construct Functions *)

(** FULL: Most of the higher-order functions we have talked about so
    far take functions as arguments.  Let's look at some examples that
    involve _returning_ functions as the results of other functions.
    To begin, here is a function that takes a value [x] (drawn from
    some type [X]) and returns a function from [nat] to [X] that
    yields [x] whenever it is called, ignoring its [nat] argument. *)
(** TERSE: Here are two more functions that _return_ functions
    as results. *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

Example constfun_example2 : (constfun 5) 99 = 5.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(** FULL: In fact, the multiple-argument functions we have already
    seen are also examples of passing functions as data.  To see why,
    recall the type of [plus]. *)
(** TERSE: *** *)
(** TERSE: A two-argument function in Coq is actually a function that
    returns a function! *)

Check plus : nat -> nat -> nat.

(** FULL: Each [->] in this expression is actually a _binary_ operator
    on types.  This operator is _right-associative_, so the type of
    [plus] is really a shorthand for [nat -> (nat -> nat)] -- i.e., it
    can be read as saying that "[plus] is a one-argument function that
    takes a [nat] and returns a one-argument function that takes
    another [nat] and returns a [nat]."  In the examples above, we
    have always applied [plus] to both of its arguments at once, but
    if we like we can supply just the first.  This is called _partial
    application_. *)

Definition plus3 := plus 3.
Check plus3 : nat -> nat.

Example test_plus3 :    plus3 4 = 7.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
Example test_plus3' :   doit3times plus3 0 = 9.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(* FULL *)
(* ##################################################### *)
(** * Additional Exercises *)

Module Exercises.

(* EX2 (fold_length) *)
(** Many common functions on lists can be implemented in terms of
    [fold].  For example, here is an alternative definition of [length]: *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(** Prove the correctness of [fold_length].  (Hint: It may help to
    know that [reflexivity] simplifies expressions a bit more
    aggressively than [simpl] does -- i.e., you may find yourself in a
    situation where [simpl] does nothing but [reflexivity] solves the
    goal.) *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
(* ADMITTED *)
  induction l as [| x l' IHl'].
  - (* l = [] *) reflexivity.
  - (* l = x :: l' *) simpl.
    rewrite <- IHl'.
    reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: Exercises.fold_length_correct *)
(** [] *)

(* LATER: Can we grade this automatically? One challenge is that
   [fold_map_correct] may vary in the order of variables and arguments of (=).
   However there is a rather small number of variations so automation does not
   seem entirely out of reach. *)
(* EX3M (fold_map) *)
(** We can also define [map] in terms of [fold].  Finish [fold_map]
    below. *)

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y
  (* ADMITDEF *) :=
  fold (fun x l' => f x :: l') l nil.
(* /ADMITDEF *)

(** Write down a theorem [fold_map_correct] in Coq stating that
   [fold_map] is correct, and prove it.  (Hint: again, remember that
   [reflexivity] simplifies expressions a bit more aggressively than
   [simpl].) *)

(* SOLUTION *)
Theorem fold_map_correct : forall X Y (f : X -> Y) (l : list X),
  fold_map f l = map f l.
Proof.
  induction l as [| x l' IHl'].
  - (* l = [] *) reflexivity.
  - (* l = x :: l' *) simpl.
    rewrite <- IHl'.
    reflexivity.  Qed.
(* /SOLUTION *)

(* GRADE_MANUAL 3: fold_map *)
(** [] *)

(* EX2A (currying) *)
(** In Coq, a function [f : A -> B -> C] really has the type [A
    -> (B -> C)].  That is, if you give [f] a value of type [A], it
    will give you function [f' : B -> C].  If you then give [f'] a
    value of type [B], it will return a value of type [C].  This
    allows for partial application, as in [plus3].  Processing a list
    of arguments with functions that return functions is called
    _currying_, in honor of the logician Haskell Curry.

    Conversely, we can reinterpret the type [A -> B -> C] as [(A *
    B) -> C].  This is called _uncurrying_.  With an uncurried binary
    function, both arguments must be given at once as a pair; there is
    no partial application. *)

(** We can define currying as follows: *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(** As an exercise, define its inverse, [prod_uncurry].  Then prove
    the theorems below to show that the two are inverses. *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z
  (* ADMITDEF *) :=
    match p with
      | (x,y) => f x y
    end.
(* /ADMITDEF *)

(** As a (trivial) example of the usefulness of currying, we can use it
    to shorten one of the examples that we saw above: *)

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(** Thought exercise: before running the following commands, can you
    calculate the types of [prod_curry] and [prod_uncurry]? *)

Check @prod_curry.
Check @prod_uncurry.

(* HIDE: Maybe this is a good place to introduce the lack of
   functional extensionality? Here, at the latest, the reader may have
   started to wonder why the next two theorems, rather than claiming
   the equality of functions, claim equalities for their values...
   BCP 9/16: On reflection, I think this is not the place.  It's an
   advanced exercise, so not everybody will see it, and we do come
   back to it in detail in a couple chapters. *)
Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  (* ADMITTED *)
  intros X Y Z f x y.
  reflexivity.  Qed.
(* /ADMITTED *)

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  (* ADMITTED *)
  intros X Y Z f p.
  destruct p as [x y].
  reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: Exercises.uncurry_curry *)
(* GRADE_THEOREM 1: Exercises.curry_uncurry *)
(** [] *)

(* EX2AM (nth_error_informal) *)
(** Recall the definition of the [nth_error] function:
[[
   Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | [] => None
     | a :: l' => if n =? O then Some a else nth_error l' (pred n)
     end.
]]
   Write an informal proof of the following theorem:
[[
   forall X l n, length l = n -> @nth_error X l n = None
]]
*)
(* SOLUTION *)
(** Theorem: For all types [X], lists [l], and natural numbers [n],
    if [length l = n] then [nth_error X l n = None].

    Proof: By induction on [l]. There are two cases to consider:

      - If [l = nil], we must show [nth_error [] n = None].  This follows
        immediately from the definition of [nth_error].

      - Otherwise, [l = x :: l'] for some [x] and [l'], and the
        induction hypothesis tells us that [length l' = n' => nth_error l'
        n' = None] for any [n'].

        Let [n] be a number such that [length l = n].  We must show
        that [nth_error (x :: l') n = None].

        But we know that [n = length l = length (x :: l') = S (length l')].
        So it's enough to show [nth_error l' (length l') = None], which
        follows directly from the induction hypothesis, picking [length l']
        for [n']. *)
(* /SOLUTION *)

(* GRADE_MANUAL 2: informal_proof *)
(** [] *)

(** The following exercises explore an alternative way of defining
    natural numbers, using the so-called _Church numerals_, named
    after mathematician Alonzo Church.  We can represent a natural
    number [n] as a function that takes a function [f] as a parameter
    and returns [f] iterated [n] times. *)

Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.

(** Let's see how to write some numbers with this notation. Iterating
    a function once should be the same as just applying it.  Thus: *)

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

(** Similarly, [two] should apply [f] twice to its argument: *)

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(** Defining [zero] is somewhat trickier: how can we "apply a function
    zero times"?  The answer is actually simple: just return the
    argument untouched. *)

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(** More generally, a number [n] can be written as [fun X f x => f (f
    ... (f x) ...)], with [n] occurrences of [f].  Notice in
    particular how the [doit3times] function we've defined previously
    is actually just the Church representation of [3]. *)

Definition three : cnat := @doit3times.

(** Complete the definitions of the following functions. Make sure
    that the corresponding unit tests pass by proving them with
    [reflexivity]. *)

(* EX1A (church_succ) *)

(** Successor of a natural number: given a Church numeral [n],
    the successor [succ n] is a function that iterates its
    argument once more than [n]. *)
Definition succ (n : cnat) : cnat
  (* ADMITDEF *) :=
  fun X f x => f (n X f x).
  (* /ADMITDEF *)

Example succ_1 : succ zero = one.
Proof. (* ADMITTED *) reflexivity. Qed. (* /ADMITTED *)

Example succ_2 : succ one = two.
Proof. (* ADMITTED *) reflexivity. Qed. (* /ADMITTED *)

Example succ_3 : succ two = three.
Proof. (* ADMITTED *) reflexivity. Qed. (* /ADMITTED *)

(* GRADE_THEOREM 0.5: Exercises.Church.succ_2 *)
(* GRADE_THEOREM 0.5: Exercises.Church.succ_3 *)
(** [] *)

(* EX1A (church_plus) *)

(** Addition of two natural numbers: *)
Definition plus (n m : cnat) : cnat
  (* ADMITDEF *) :=
  fun X f x => n X f (m X f x).
  (* /ADMITDEF *)

Example plus_1 : plus zero one = one.
Proof. (* ADMITTED *) reflexivity. Qed. (* /ADMITTED *)

Example plus_2 : plus two three = plus three two.
Proof. (* ADMITTED *) reflexivity. Qed. (* /ADMITTED *)

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. (* ADMITTED *) reflexivity. Qed. (* /ADMITTED *)

(* GRADE_THEOREM 0.5: Exercises.Church.plus_2 *)
(* GRADE_THEOREM 0.5: Exercises.Church.plus_3 *)
(** [] *)

(* EX2A (church_mult) *)

(** Multiplication: *)
Definition mult (n m : cnat) : cnat
  (* ADMITDEF *) :=
  fun X f x => n X (m X f) x.
  (* /ADMITDEF *)
(* SOONER: The more natural way to write this...
   Definition mult (n m : cnat) : cnat := n cnat (plus m) one.
*)

Example mult_1 : mult one one = one.
Proof. (* ADMITTED *) reflexivity. Qed. (* /ADMITTED *)

Example mult_2 : mult zero (plus three three) = zero.
Proof. (* ADMITTED *) reflexivity. Qed. (* /ADMITTED *)

Example mult_3 : mult two three = plus three three.
Proof. (* ADMITTED *) reflexivity. Qed. (* /ADMITTED *)

(* GRADE_THEOREM 0.5: Exercises.Church.mult_1 *)
(* GRADE_THEOREM 0.5: Exercises.Church.mult_2 *)
(* GRADE_THEOREM 1: Exercises.Church.mult_3 *)
(** [] *)

(* EX2A (church_exp) *)

(** Exponentiation: *)

(** (_Hint_: Polymorphism plays a crucial role here.  However,
    choosing the right type to iterate over can be tricky.  If you hit
    a "Universe inconsistency" error, try iterating over a different
    type.  Iterating over [cnat] itself is usually problematic.) *)

Definition exp (n m : cnat) : cnat
  (* ADMITDEF *) :=
  fun X f x => m (X -> X) (n X) f x.
  (* /ADMITDEF *)

Example exp_1 : exp two two = plus two two.
Proof. (* ADMITTED *) reflexivity. Qed. (* /ADMITTED *)

Example exp_2 : exp three zero = one.
Proof. (* ADMITTED *) reflexivity. Qed. (* /ADMITTED *)

Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. (* ADMITTED *) reflexivity. Qed. (* /ADMITTED *)

(* GRADE_THEOREM 0.5: Exercises.Church.exp_1 *)
(* GRADE_THEOREM 0.5: Exercises.Church.exp_2 *)
(* GRADE_THEOREM 1: Exercises.Church.exp_3 *)
(** [] *)

End Church.

End Exercises.

(* /HIDEFROMADVANCED *)
(* /FULL *)


(* HIDE *)
(*
Local Variables:
fill-column: 70
End:
*)
(* /HIDE *)
