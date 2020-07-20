---
title     : "Poly: Generic data structures and functions"
layout    : page
prev      : /NatData/
permalink : /Poly/
next      : /Maps/
---

```
module plc.fp.Poly where
open import Data.Bool
open import Data.Nat

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
```

## Polymorphic Lists

In the last section, we worked with lists containing just numbers.
Obviously, interesting programs also need to be able to manipulate
lists with elements from other types — lists of booleans, lists of
lists, etc.  We _could_ just define a new inductive datatype for each
of these, for example...

```
data BoolList : Set where
  boolNil : BoolList
  boolCons : Bool -> BoolList -> BoolList
```

...but this would quickly become tedious, partly because we have to
make up different constructor names for each datatype, but mostly
because we would also need to define new versions of all our list
manipulating functions (`length`, `rev`, etc.) for each new datatype
definition.

To avoid all this repetition, Agda supports _polymorphic_ inductive
type definitions.  For example, here is a _polymorphic list_ datatype.

```
module ExplicitType where
data List : Set -> Set where
  [] : (x : Set) -> List x
  _::_ : (x : Set) -> x -> List x
```

This is exactly like the definition of `NatList` from the previous
chapter, except that the `nat` argument to the cons constructor has
been replaced by an arbitrary type `x`, a binding for `x` has been
added to the function header on the first line, and the occurrences of
`NatList` in the types of the constructors have been replaced by `List x`.

    What sort of thing is `list` itself?  A good way to think about it
    is that the definition of `list` is a _function_ from `Type`s to
    `Inductive` definitions; or, to put it more concisely, `list` is a
    function from `Type`s to `Type`s.  For any particular type `X`,
    the type `list X` is the `Inductive`ly defined set of lists whose
    elements are of type `X`. *)

(** TERSE: `list` itself is a _function_ from types to (inductively
    defined) types. *)

Check list : Type -> Type.

(** TERSE: *** *)
(* LATER: Is this clear enough? *)
(** FULL: The parameter `X` in the definition of `list` automatically
    becomes a parameter to the constructors `nil` and `cons` — that
    is, `nil` and `cons` are now polymorphic constructors; when we use
    them, we must now provide a first argument that is the type of the
    list they are building. For example, `nil nat` constructs the
    empty list of type `nat`. *)

(** TERSE: The parameter `X` in the definition of `list` becomes
    a parameter to the list constructors. *)

Check (nil nat) : list nat.

(** FULL: Similarly, `cons nat` adds an element of type `nat` to a list of
    type `list nat`. Here is an example of forming a list containing
    just the natural number 3. *)

Check (cons nat 3 (nil nat)) : list nat.

(* SOONER: Unclear - Reword *)
(** FULL: What might the type of `nil` be? We can read off the type
    `list X` from the definition, but this omits the binding for `X`
    which is the parameter to `list`. `Type -> list X` does not
    explain the meaning of `X`. `(X : Type) -> list X` comes
    closer. Coq's notation for this situation is `forall X : Type,
    list X`. *)

Check nil : forall X : Type, list X.

(* SOONER: Ditto - Reword *)
(** FULL: Similarly, the type of `cons` from the definition looks like
    `X -> list X -> list X`, but using this convention to explain the
    meaning of `X` results in the type `forall X, X -> list X -> list
    X`. *)

Check cons : forall X : Type, X -> list X -> list X.

(** FULL: (Side note on notation: In .v files, the "forall" quantifier
    is spelled out in letters.  In the generated HTML files and in the
    way various IDEs show .v files, depending on the settings of their
    display controls, `forall` is usually typeset as the usual
    mathematical "upside down A," though you'll still see the
    spelled-out "forall" in a few places.  This is just a quirk of
    typesetting: there is no difference in meaning.) *)
(** TERSE: Notation: In .v files, the "forall" quantifier is spelled
    out in letters.  In the generated HTML files, it is usually
    typeset as the usual mathematical "upside down A." *)

(* HIDEFROMADVANCED *)
(* LATER: Maybe explain better?  (Maybe NOT using the "forall is a
   funny kind of function type" intuition.) *)
(** FULL: Having to supply a type argument for every single use of a
    list constructor would be rather burdensome; we will soon see ways
    of reducing this annotation burden. *)

Check (cons nat 2 (cons nat 1 (nil nat)))
      : list nat.

(** FULL: We can now go back and make polymorphic versions of all the
    list-processing functions that we wrote before.  Here is `repeat`,
    for example: *)

(* /HIDEFROMADVANCED *)
(** TERSE: *** *)
(** TERSE: We can now define polymorphic versions of the functions
    we've already seen... *)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

(** FULL: As with `nil` and `cons`, we can use `repeat` by applying it
    first to a type and then to an element of this type (and a number): *)
(* HIDEFROMADVANCED *)

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(** FULL: To use `repeat` to build other kinds of lists, we simply
    instantiate it with an appropriate type parameter: *)

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(* QUIZ *)
(** Recall the types of `cons` and `nil`:
``
       nil : forall X : Type, list X
       cons : forall X : Type, X -> list X -> list X
``
    What is the type of `cons bool true (cons nat 3 (nil nat))`?

    (1) `nat -> list nat -> list nat`

    (2) `forall (X:Type), X -> list X -> list X`

    (3) `list nat`

    (4) `list bool`

    (5) Ill-typed
*)
(* /QUIZ *)

(* QUIZ *)
(** Recall the definition of `repeat`:
``
    Fixpoint repeat (X : Type) (x : X) (count : nat)
                  : list X :=
      match count with
      | 0 => nil X
      | S count' => cons X x (repeat X x count')
      end.
``
    What is the type of `repeat`?

    (1) `nat -> nat -> list nat`

    (2) `X -> nat -> list X`

    (3) `forall (X Y: Type), X -> nat -> list Y`

    (4) `forall (X:Type), X -> nat -> list X`

    (5) Ill-typed
*)
(* /QUIZ *)

(* QUIZ *)
(** What is the type of `repeat nat 1 2`?

    (1) `list nat`

    (2) `forall (X:Type), X -> nat -> list X`

    (3) `list bool`

    (4) Ill-typed
*)
(* /QUIZ *)
(* FULL *)
(* HIDE: It might be nicer to put this Module declaration inside the
   exercise, but it confuses coqdoc... :-( *)

(* EX2M (mumble_grumble) *)
(** Consider the following two inductively defined types. *)

Module MumbleGrumble.

Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.

Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).

(** Which of the following are well-typed elements of `grumble X` for
    some type `X`?  (Add YES or NO to each line.)
      - `d (b a 5)`
      - `d mumble (b a 5)`
      - `d bool (b a 5)`
      - `e bool true`
      - `e mumble (b c 0)`
      - `e bool (b c 0)`
      - `c`  *)
(* SOLUTION *)
(**   - `d mumble (b a 5)`
      - `d bool (b a 5)`
      - `e bool true`
      - `e mumble (b c 0)`  *)
(* /SOLUTION *)
(* LATER: Is there a better way to write the problem for easier grading? *)
End MumbleGrumble.

(* GRADE_MANUAL 2: mumble_grumble *)
(** `` *)
(* /FULL *)

(* ###################################################### *)
(** *** Type Annotation Inference *)

(** Let's write the definition of `repeat` again, but this time we
    won't specify the types of any of the arguments.  Will Coq still
    accept it? *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(** TERSE: *** *)
(** Indeed it will.  Let's see what type Coq has assigned to `repeat'`: *)

Check repeat'
  : forall X : Type, X -> nat -> list X.
Check repeat
  : forall X : Type, X -> nat -> list X.

(** TERSE: Coq has used _type inference_ to deduce the proper types
    for `X`, `x`, and `count`. *)
(** FULL: It has exactly the same type as `repeat`.  Coq was able to
    use _type inference_ to deduce what the types of `X`, `x`, and
    `count` must be, based on how they are used.  For example, since
    `X` is used as an argument to `cons`, it must be a `Type`, since
    `cons` expects a `Type` as its first argument; matching `count`
    with `0` and `S` means it must be a `nat`; and so on.

    This powerful facility means we don't always have to write
    explicit type annotations everywhere, although explicit type
    annotations can still be quite useful as documentation and sanity
    checks, so we will continue to use them much of the time. *)
(* HIDE: (BCP '19) Deleted, for streamlining: "You should try to find
    a balance in your own code between too many type
    annotations (which can clutter and distract) and too few (which
    can sometimes require readers to perform complex type inference in
    their heads in order to understand your code)." *)

(* ###################################################### *)
(** *** Type Argument Synthesis *)

(** FULL: To use a polymorphic function, we need to pass it one or
    more types in addition to its other arguments.  For example, the
    recursive call in the body of the `repeat` function above must
    pass along the type `X`.  But since the second argument to
    `repeat` is an element of `X`, it seems entirely obvious that the
    first argument can only be `X` — why should we have to write it
    explicitly?

    Fortunately, Coq permits us to avoid this kind of redundancy.  In
    place of any type argument we can write a "hole" `_`, which can be
    read as "Please try to figure out for yourself what belongs here."
    More precisely, when Coq encounters a `_`, it will attempt to
    _unify_ all locally available information — the type of the
    function being applied, the types of the other arguments, and the
    type expected by the context in which the application appears --
    to determine what concrete type should replace the `_`.

    This may sound similar to type annotation inference — and, indeed,
    the two procedures rely on the same underlying mechanisms.  Instead
    of simply omitting the types of some arguments to a function, like
``
      repeat' X x count : list X :=
``
    we can also replace the types with holes
``
      repeat' (X : _) (x : _) (count : _) : list X :=
``
    to tell Coq to attempt to infer the missing information.

    Using holes, the `repeat` function can be written like this: *)
(** TERSE: Supplying every _type argument_ is also boring, but Coq
    can usually infer them: *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

(* FULL *)
(** In this instance, we don't save much by writing `_` instead of
    `X`.  But in many cases the difference in both keystrokes and
    readability is nontrivial.  For example, suppose we want to write
    down a list containing the numbers `1`, `2`, and `3`.  Instead of
    this... *)

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

(** ...we can use holes to write this: *)
(* /FULL *)

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ###################################################### *)
(** *** Implicit Arguments *)

(** In fact, we can go further and even avoid writing `_`'s in most
    cases by telling Coq _always_ to infer the type argument(s) of a
    given function.

    The `Arguments` directive specifies the name of the function (or
    constructor) and then lists its argument names, with curly braces
    around any arguments to be treated as implicit.  (If some
    arguments of a definition don't have a name, as is often the case
    for constructors, they can be marked with a wildcard pattern
    `_`.) *)
(* /HIDEFROMADVANCED *)
(* ADVANCED *)
(** TERSE: *** *)
(* /ADVANCED *)

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

(* HIDEFROMADVANCED *)
(** Now, we don't have to supply type arguments at all: *)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(** TERSE: *** *)

(** FULL: Alternatively, we can declare an argument to be implicit
    when defining the function itself, by surrounding it in curly
    braces instead of parens.  For example: *)
(** TERSE: Alternatively, we can declare arguments implicit by
    surrounding them with curly braces instead of parens: *)

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

(* FULL *)
(** (Note that we didn't even have to provide a type argument to the
    recursive call to `repeat'''`.  Indeed, it would be invalid to
    provide one, because Coq is not expecting it.)

    We will use the latter style whenever possible, but we will
    continue to use explicit `Argument` declarations for `Inductive`
    constructors.  The reason for this is that marking the parameter
    of an inductive type as implicit causes it to become implicit for
    the type itself, not just for its constructors.  For instance,
    consider the following alternative definition of the `list`
    type: *)

Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').

(** Because `X` is declared as implicit for the _entire_ inductive
    definition including `list'` itself, we now have to write just
    `list'` whether we are talking about lists of numbers or booleans
    or anything else, rather than `list' nat` or `list' bool` or
    whatever; this is a step too far. *)
(* /FULL *)

(** TERSE: *** *)
(** FULL: Let's finish by re-implementing a few other standard list
    functions on our new polymorphic lists... *)
(** TERSE: Here are polymorphic versions of a few more functions that
    we'll need later:*)

(* /HIDEFROMADVANCED *)
Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

(** TERSE: *** *)
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

(* HIDEFROMADVANCED *)
Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

Example test_rev2:
  rev (cons true nil) = cons true nil.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
(* /HIDEFROMADVANCED *)

(** *** Supplying Type Arguments Explicitly *)

(** FULL: One small problem with declaring arguments `Implicit` is
    that, once in a while, Coq does not have enough local information
    to determine a type argument; in such cases, we need to tell Coq
    that we want to give the argument explicitly just this time.  For
    example, suppose we write this: *)
(** TERSE: We prefer to tell Coq to always try to infer type arguments.
    But, occasionally this can lead to problems: *)

Fail Definition mynil := nil.

(* LATER: We only use "Fail Definition" in one other place at the moment.
   Is it worth keeping? *)
(** FULL: (The `Fail` qualifier that appears before `Definition` can be
    used with _any_ command, and is used to ensure that that command
    indeed fails when executed. If the command does fail, Coq prints
    the corresponding error message, but continues processing the rest
    of the file.)

    Here, Coq gives us an error because it doesn't know what type
    argument to supply to `nil`.  We can help it by providing an
    explicit type declaration (so that Coq has more information
    available when it gets to the "application" of `nil`): *)
(** TERSE: We can fix this with an explicit type declaration: *)

Definition mynil : list nat := nil.

(** Alternatively, we can force the implicit arguments to be explicit by
   prefixing the function name with `@`. *)

Check @nil : forall X : Type, list X.

Definition mynil' := @nil nat.

(** TERSE: *** *)
(** FULL: Using argument synthesis and implicit arguments, we can
    define convenient notation for lists, as before.  Since we have
    made the constructor type arguments implicit, Coq will know to
    automatically infer these when we use the notations. *)
(** TERSE: Using argument synthesis and implicit arguments, we can
    define concrete notations that work for lists of any type. *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "` `" := nil.
Notation "` x ; .. ; y `" := (cons x .. (cons y ``) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(** FULL: Now lists can be written just the way we'd hope: *)

Definition list123''' := `1; 2; 3`.

(* HIDEFROMADVANCED *)
(* TERSE *)
(* QUIZ *)
(** Which type does Coq assign to the following expression? *)
(* HIDEFROMHTML *)
(** (The square brackets here and in the following quizzes are list
    brackets, not "this is a Coq expression inside a comment" brackets.) *)
(* /HIDEFROMHTML *)
(**
``
       `1,2,3`
``

    (1) `list nat`

    (2) `list bool`

    (3) `bool`

    (4) No type can be assigned
*)
(* /QUIZ *)
(* INSTRUCTORS: (4) Commas, not semi colons *)

(* QUIZ *)
(** What about this one?
``
       `3 + 4` ++ nil
``

    (1) `list nat`

    (2) `list bool`

    (3) `bool`

    (4) No type can be assigned
*)
(* /QUIZ *)
(* INSTRUCTORS: (1) *)

(* QUIZ *)
(** What about this one?
``
       andb true false ++ nil
``

    (1) `list nat`

    (2) `list bool`

    (3) `bool`

    (4) No type can be assigned
*)
(* /QUIZ *)
(* INSTRUCTORS: (4) *)

(* QUIZ *)
(** What about this one?
``
        `1; nil`
``

    (1) `list nat`

    (2) `list (list nat)`

    (3) `list bool`

    (4) No type can be assigned
*)
(* /QUIZ *)
(* INSTRUCTORS: (4) *)

(* QUIZ *)
(** What about this one?
``
        ``1`; nil`
``

    (1) `list nat`

    (2) `list (list nat)`

    (3) `list bool`

    (4) No type can be assigned
*)
(* /QUIZ *)
(* INSTRUCTORS: (2) *)

(* QUIZ *)
(** And what about this one?
``
         `1` :: `nil`
``

    (1) `list nat`

    (2) `list (list nat)`

    (3) `list bool`

    (4) No type can be assigned
*)
(* /QUIZ *)
(* INSTRUCTORS: (2) *)

(* QUIZ *)
(** This one?
``
        @nil bool
``

    (1) `list nat`

    (2) `list (list nat)`

    (3) `list bool`

    (4) No type can be assigned
*)
(* /QUIZ *)
(* INSTRUCTORS: (3) *)

(* QUIZ *)
(** This one?
``
        nil bool
``

    (1) `list nat`

    (2) `list (list nat)`

    (3) `list bool`

    (4) No type can be assigned
*)
(* /QUIZ *)
(* INSTRUCTORS: (4) *)

(* QUIZ *)
(** This one?
``
        @nil 3
``

    (1) `list nat`

    (2) `list (list nat)`

    (3) `list bool`

    (4) No type can be assigned
*)
(* /QUIZ *)
(* INSTRUCTORS: (4) *)
(* /TERSE *)

(* TERSE: HIDEFROMHTML *)
(* ###################################################### *)
(** *** Exercises *)

(* EX2? (poly_exercises) *)
(** Here are a few simple exercises, just like ones in the `Lists`
    chapter, for practice with polymorphism.  Complete the proofs below. *)

(* INSTRUCTORS: There's a little inconsistency between this definition
   and the standard library one: in the library, the type argument is
   implicit. :-( I (BCP) have chosen to leave things inconsistent to
   avoid having to explain about implicit arguments to theorems, which
   wouldn't make sense at this point. *)
Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ `` = l.
Proof.
  (* ADMITTED *)
  intros X l. induction l as `|x l' IH`.
  - reflexivity.
    - simpl. rewrite IH. reflexivity.
Qed.
(* /ADMITTED *)

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  (* ADMITTED *)
  intros A l m n.
  induction l as `|a l' IH`.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
(* /ADMITTED *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  (* ADMITTED *)
  intros X l1. induction l1 as `|x l1'`.
  - (* l1 = nil *) reflexivity.
  - (* l1 = x::l1' *) intros l2.  simpl. rewrite -> IHl1'. reflexivity. Qed.
(* /ADMITTED *)
(** `` *)

(* EX2? (more_poly_exercises) *)
(** Here are some slightly more interesting ones... *)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* ADMITTED *)
  intros X l1 l2. induction l1 as `|x1 l1' IH`.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IH. rewrite app_assoc. reflexivity. Qed.
(* /ADMITTED *)

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  (* ADMITTED *)
  intros X l. induction l as `| n l'`.
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> rev_app_distr. rewrite -> IHl'. reflexivity.  Qed.
(* /ADMITTED *)
(** `` *)
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
(** We can also use the `Notation` mechanism to define the standard
    notation for product _types_: *)

(* /HIDEFROMADVANCED *)
Notation "X * Y" := (prod X Y) : type_scope.

(** (The annotation `: type_scope` tells Coq that this abbreviation
    should only be used when parsing types, not when parsing
    expressions.  This avoids a clash with the multiplication
    symbol.) *)

(** FULL: It is easy at first to get `(x,y)` and `X*Y` confused.
    Remember that `(x,y)` is a _value_ built from two other values,
    while `X*Y` is a _type_ built from two other types.  If `x` has
    type `X` and `y` has type `Y`, then `(x,y)` has type `X*Y`. *)
(** TERSE: Be careful not to get `(X,Y)` and `X*Y` confused! *)
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
    called `zip`; we call it `combine` for consistency with Coq's
    standard library. *)
(** TERSE: *** *)
(** TERSE: What does this function do? *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | ``, _ => ``
  | _, `` => ``
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(* FULL *)
(* EX1M? (combine_checks) *)
(** Try answering the following questions on paper and
    checking your answers in Coq:
    - What is the type of `combine` (i.e., what does `Check
      @combine` print?)
    - What does
``
        Compute (combine `1;2` `false;false;true;true`).
``
      print? *)
(** `` *)

(* EX2! (split) *)
(** The function `split` is the right inverse of `combine`: it takes a
    list of pairs and returns a pair of lists.  In many functional
    languages, it is called `unzip`.

    Fill in the definition of `split` below.  Make sure it passes the
    given unit test. *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y)
  (* ADMITDEF *) :=
  match l with
  | `` => (``, ``)
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.
(* /ADMITDEF *)

Example test_split:
  split `(1,false);(2,false)` = (`1;2`,`false;false`).
Proof.
(* ADMITTED *)
  reflexivity.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: split *)
(* GRADE_THEOREM 1: test_split *)
(** `` *)
(* /FULL *)

(* ###################################################### *)
(** ** Polymorphic Options *)

(** FULL: Our last polymorphic type for now is _polymorphic options_,
    which generalize `natoption` from the previous chapter.  (We put
    the definition inside a module because the standard library
    already defines `option` and it's this one that we want to use
    below.) *)

Module OptionPlayground.

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X} _.
Arguments None {X}.

End OptionPlayground.

(** TERSE: *** *)
(** FULL: We can now rewrite the `nth_error` function so that it works
    with any type of lists. *)

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | `` => None
  | a :: l' => if n =? O then Some a else nth_error l' (pred n)
  end.

(* HIDEFROMADVANCED *)
Example test_nth_error1 : nth_error `4;5;6;7` 0 = Some 4.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
Example test_nth_error2 : nth_error ``1`;`2`` 1 = Some `2`.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
Example test_nth_error3 : nth_error `true` 2 = None.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(* /HIDEFROMADVANCED *)
(* FULL *)
(* EX1? (hd_error_poly) *)
(** Complete the definition of a polymorphic version of the
    `hd_error` function from the last chapter. Be sure that it
    passes the unit tests below. *)

Definition hd_error {X : Type} (l : list X) : option X
  (* ADMITDEF *) :=
  match l with
  | `` => None
  | a :: l' => Some a
  end.
(* /ADMITDEF *)

(** Once again, to force the implicit arguments to be explicit,
    we can use `@` before the name of the function. *)

Check @hd_error : forall X : Type, list X -> option X.

Example test_hd_error1 : hd_error `1;2` = Some 1.
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)
Example test_hd_error2 : hd_error  ``1`;`2``  = Some `1`.
 (* ADMITTED *)
Proof. reflexivity.  Qed.
 (* /ADMITTED *)
(** `` *)
(* /FULL *)
