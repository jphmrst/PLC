
```
module plc.logic.Poly where
open import Data.Bool
open import Data.Nat

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
```

(** * Poly: Polymorphism and Higher-Order Functions *)

(* INSTRUCTORS: To get through this plus Tactics.v in two 80-minute
   lectures is a bit tight -- if that's your plan, don't dawdle on
   this chapter.

*)
(* HIDEFROMHTML *)
(* FULL *)
(* Final reminder: Please do not put solutions to the exercises in
   publicly accessible places.  Thank you!! *)

(* /FULL *)
(* /HIDEFROMHTML *)
(* HIDEFROMHTML *)
(* Suppress some annoying warnings from Coq: *)
Set Warnings "-notation-overridden,-parsing".
(* /HIDEFROMHTML *)
(* TERSE: HIDEFROMHTML *)
From LF Require Export Lists.
(* TERSE: /HIDEFROMHTML *)

(* HIDEFROMADVANCED *)
(* ###################################################### *)
(* FULL *)
(** * Polymorphism *)

(** In this chapter we continue our development of basic
    concepts of functional programming.  The critical new ideas are
    _polymorphism_ (abstracting functions over the types of the data
    they manipulate) and _higher-order functions_ (treating functions
    as data).  We begin with polymorphism. *)

(* /FULL *)
(* ###################################################### *)
(** ** Polymorphic Lists *)

(** FULL: For the last chapter, we've been working with lists
    containing just numbers.  Obviously, interesting programs also
    need to be able to manipulate lists with elements from other
    types -- lists of booleans, lists of lists, etc.  We _could_ just
    define a new inductive datatype for each of these, for
    example... *)

(** TERSE: Instead of defining new lists for each type, like
    this... *)

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

(** FULL: ... but this would quickly become tedious, partly because we
    have to make up different constructor names for each datatype, but
    mostly because we would also need to define new versions of all
    our list manipulating functions ([length], [rev], etc.) and all
    their properties ([rev_length], [app_assoc], etc.) for each
    new datatype definition. *)

(** TERSE: *** *)

(** FULL: To avoid all this repetition, Coq supports _polymorphic_
    inductive type definitions.  For example, here is a _polymorphic
    list_ datatype. *)
(* /HIDEFROMADVANCED *)
(** TERSE: ...Coq lets us give a _polymorphic_ definition that allows
    list elements of any type: *)

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

(** FULL: This is exactly like the definition of [natlist] from the
    previous chapter, except that the [nat] argument to the [cons]
    constructor has been replaced by an arbitrary type [X], a binding
    for [X] has been added to the function header on the first line,
    and the occurrences of [natlist] in the types of the constructors
    have been replaced by [list X].

    What sort of thing is [list] itself?  A good way to think about it
    is that the definition of [list] is a _function_ from [Type]s to
    [Inductive] definitions; or, to put it more concisely, [list] is a
    function from [Type]s to [Type]s.  For any particular type [X],
    the type [list X] is the [Inductive]ly defined set of lists whose
    elements are of type [X]. *)

(** TERSE: [list] itself is a _function_ from types to (inductively
    defined) types. *)

Check list : Type -> Type.

(** TERSE: *** *)
(* LATER: Is this clear enough? *)
(** FULL: The parameter [X] in the definition of [list] automatically
    becomes a parameter to the constructors [nil] and [cons] -- that
    is, [nil] and [cons] are now polymorphic constructors; when we use
    them, we must now provide a first argument that is the type of the
    list they are building. For example, [nil nat] constructs the
    empty list of type [nat]. *)

(** TERSE: The parameter [X] in the definition of [list] becomes
    a parameter to the list constructors. *)

Check (nil nat) : list nat.

(** FULL: Similarly, [cons nat] adds an element of type [nat] to a list of
    type [list nat]. Here is an example of forming a list containing
    just the natural number 3. *)

Check (cons nat 3 (nil nat)) : list nat.

(* SOONER: Unclear - Reword *)
(** FULL: What might the type of [nil] be? We can read off the type
    [list X] from the definition, but this omits the binding for [X]
    which is the parameter to [list]. [Type -> list X] does not
    explain the meaning of [X]. [(X : Type) -> list X] comes
    closer. Coq's notation for this situation is [forall X : Type,
    list X]. *)

Check nil : forall X : Type, list X.

(* SOONER: Ditto - Reword *)
(** FULL: Similarly, the type of [cons] from the definition looks like
    [X -> list X -> list X], but using this convention to explain the
    meaning of [X] results in the type [forall X, X -> list X -> list
    X]. *)

Check cons : forall X : Type, X -> list X -> list X.

(** FULL: (Side note on notation: In .v files, the "forall" quantifier
    is spelled out in letters.  In the generated HTML files and in the
    way various IDEs show .v files, depending on the settings of their
    display controls, [forall] is usually typeset as the usual
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
    list-processing functions that we wrote before.  Here is [repeat],
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

(** FULL: As with [nil] and [cons], we can use [repeat] by applying it
    first to a type and then to an element of this type (and a number): *)
(* HIDEFROMADVANCED *)

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(** FULL: To use [repeat] to build other kinds of lists, we simply
    instantiate it with an appropriate type parameter: *)

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(* QUIZ *)
(** Recall the types of [cons] and [nil]:
[[
       nil : forall X : Type, list X
       cons : forall X : Type, X -> list X -> list X
]]
    What is the type of [cons bool true (cons nat 3 (nil nat))]?

    (1) [nat -> list nat -> list nat]

    (2) [forall (X:Type), X -> list X -> list X]

    (3) [list nat]

    (4) [list bool]

    (5) Ill-typed
*)
(* /QUIZ *)

(* QUIZ *)
(** Recall the definition of [repeat]:
[[
    Fixpoint repeat (X : Type) (x : X) (count : nat)
                  : list X :=
      match count with
      | 0 => nil X
      | S count' => cons X x (repeat X x count')
      end.
]]
    What is the type of [repeat]?

    (1) [nat -> nat -> list nat]

    (2) [X -> nat -> list X]

    (3) [forall (X Y: Type), X -> nat -> list Y]

    (4) [forall (X:Type), X -> nat -> list X]

    (5) Ill-typed
*)
(* /QUIZ *)

(* QUIZ *)
(** What is the type of [repeat nat 1 2]?

    (1) [list nat]

    (2) [forall (X:Type), X -> nat -> list X]

    (3) [list bool]

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

(** Which of the following are well-typed elements of [grumble X] for
    some type [X]?  (Add YES or NO to each line.)
      - [d (b a 5)]
      - [d mumble (b a 5)]
      - [d bool (b a 5)]
      - [e bool true]
      - [e mumble (b c 0)]
      - [e bool (b c 0)]
      - [c]  *)
(* SOLUTION *)
(**   - [d mumble (b a 5)]
      - [d bool (b a 5)]
      - [e bool true]
      - [e mumble (b c 0)]  *)
(* /SOLUTION *)
(* LATER: Is there a better way to write the problem for easier grading? *)
End MumbleGrumble.

(* GRADE_MANUAL 2: mumble_grumble *)
(** [] *)
(* /FULL *)

(* ###################################################### *)
(** *** Type Annotation Inference *)

(** Let's write the definition of [repeat] again, but this time we
    won't specify the types of any of the arguments.  Will Coq still
    accept it? *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(** TERSE: *** *)
(** Indeed it will.  Let's see what type Coq has assigned to [repeat']: *)

Check repeat'
  : forall X : Type, X -> nat -> list X.
Check repeat
  : forall X : Type, X -> nat -> list X.

(** TERSE: Coq has used _type inference_ to deduce the proper types
    for [X], [x], and [count]. *)
(** FULL: It has exactly the same type as [repeat].  Coq was able to
    use _type inference_ to deduce what the types of [X], [x], and
    [count] must be, based on how they are used.  For example, since
    [X] is used as an argument to [cons], it must be a [Type], since
    [cons] expects a [Type] as its first argument; matching [count]
    with [0] and [S] means it must be a [nat]; and so on.

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
    recursive call in the body of the [repeat] function above must
    pass along the type [X].  But since the second argument to
    [repeat] is an element of [X], it seems entirely obvious that the
    first argument can only be [X] -- why should we have to write it
    explicitly?

    Fortunately, Coq permits us to avoid this kind of redundancy.  In
    place of any type argument we can write a "hole" [_], which can be
    read as "Please try to figure out for yourself what belongs here."
    More precisely, when Coq encounters a [_], it will attempt to
    _unify_ all locally available information -- the type of the
    function being applied, the types of the other arguments, and the
    type expected by the context in which the application appears --
    to determine what concrete type should replace the [_].

    This may sound similar to type annotation inference -- and, indeed,
    the two procedures rely on the same underlying mechanisms.  Instead
    of simply omitting the types of some arguments to a function, like
[[
      repeat' X x count : list X :=
]]
    we can also replace the types with holes
[[
      repeat' (X : _) (x : _) (count : _) : list X :=
]]
    to tell Coq to attempt to infer the missing information.

    Using holes, the [repeat] function can be written like this: *)
(** TERSE: Supplying every _type argument_ is also boring, but Coq
    can usually infer them: *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

(* FULL *)
(** In this instance, we don't save much by writing [_] instead of
    [X].  But in many cases the difference in both keystrokes and
    readability is nontrivial.  For example, suppose we want to write
    down a list containing the numbers [1], [2], and [3].  Instead of
    this... *)

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

(** ...we can use holes to write this: *)
(* /FULL *)

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ###################################################### *)
(** *** Implicit Arguments *)

(** In fact, we can go further and even avoid writing [_]'s in most
    cases by telling Coq _always_ to infer the type argument(s) of a
    given function.

    The [Arguments] directive specifies the name of the function (or
    constructor) and then lists its argument names, with curly braces
    around any arguments to be treated as implicit.  (If some
    arguments of a definition don't have a name, as is often the case
    for constructors, they can be marked with a wildcard pattern
    [_].) *)
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
    recursive call to [repeat'''].  Indeed, it would be invalid to
    provide one, because Coq is not expecting it.)

    We will use the latter style whenever possible, but we will
    continue to use explicit [Argument] declarations for [Inductive]
    constructors.  The reason for this is that marking the parameter
    of an inductive type as implicit causes it to become implicit for
    the type itself, not just for its constructors.  For instance,
    consider the following alternative definition of the [list]
    type: *)

Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').

(** Because [X] is declared as implicit for the _entire_ inductive
    definition including [list'] itself, we now have to write just
    [list'] whether we are talking about lists of numbers or booleans
    or anything else, rather than [list' nat] or [list' bool] or
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

(** FULL: One small problem with declaring arguments [Implicit] is
    that, once in a while, Coq does not have enough local information
    to determine a type argument; in such cases, we need to tell Coq
    that we want to give the argument explicitly just this time.  For
    example, suppose we write this: *)
(** TERSE: We prefer to tell Coq to always try to infer type arguments.
    But, occasionally this can lead to problems: *)

Fail Definition mynil := nil.

(* LATER: We only use "Fail Definition" in one other place at the moment.
   Is it worth keeping? *)
(** FULL: (The [Fail] qualifier that appears before [Definition] can be
    used with _any_ command, and is used to ensure that that command
    indeed fails when executed. If the command does fail, Coq prints
    the corresponding error message, but continues processing the rest
    of the file.)

    Here, Coq gives us an error because it doesn't know what type
    argument to supply to [nil].  We can help it by providing an
    explicit type declaration (so that Coq has more information
    available when it gets to the "application" of [nil]): *)
(** TERSE: We can fix this with an explicit type declaration: *)

Definition mynil : list nat := nil.

(** Alternatively, we can force the implicit arguments to be explicit by
   prefixing the function name with [@]. *)

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
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(** FULL: Now lists can be written just the way we'd hope: *)

Definition list123''' := [1; 2; 3].

(* HIDEFROMADVANCED *)
(* TERSE *)
(* QUIZ *)
(** Which type does Coq assign to the following expression? *)
(* HIDEFROMHTML *)
(** (The square brackets here and in the following quizzes are list
    brackets, not "this is a Coq expression inside a comment" brackets.) *)
(* /HIDEFROMHTML *)
(**
[[
       [1,2,3]
]]

    (1) [list nat]

    (2) [list bool]

    (3) [bool]

    (4) No type can be assigned
*)
(* /QUIZ *)
(* INSTRUCTORS: (4) Commas, not semi colons *)

(* QUIZ *)
(** What about this one?
[[
       [3 + 4] ++ nil
]]

    (1) [list nat]

    (2) [list bool]

    (3) [bool]

    (4) No type can be assigned
*)
(* /QUIZ *)
(* INSTRUCTORS: (1) *)

(* QUIZ *)
(** What about this one?
[[
       andb true false ++ nil
]]

    (1) [list nat]

    (2) [list bool]

    (3) [bool]

    (4) No type can be assigned
*)
(* /QUIZ *)
(* INSTRUCTORS: (4) *)

(* QUIZ *)
(** What about this one?
[[
        [1; nil]
]]

    (1) [list nat]

    (2) [list (list nat)]

    (3) [list bool]

    (4) No type can be assigned
*)
(* /QUIZ *)
(* INSTRUCTORS: (4) *)

(* QUIZ *)
(** What about this one?
[[
        [[1]; nil]
]]

    (1) [list nat]

    (2) [list (list nat)]

    (3) [list bool]

    (4) No type can be assigned
*)
(* /QUIZ *)
(* INSTRUCTORS: (2) *)

(* QUIZ *)
(** And what about this one?
[[
         [1] :: [nil]
]]

    (1) [list nat]

    (2) [list (list nat)]

    (3) [list bool]

    (4) No type can be assigned
*)
(* /QUIZ *)
(* INSTRUCTORS: (2) *)

(* QUIZ *)
(** This one?
[[
        @nil bool
]]

    (1) [list nat]

    (2) [list (list nat)]

    (3) [list bool]

    (4) No type can be assigned
*)
(* /QUIZ *)
(* INSTRUCTORS: (3) *)

(* QUIZ *)
(** This one?
[[
        nil bool
]]

    (1) [list nat]

    (2) [list (list nat)]

    (3) [list bool]

    (4) No type can be assigned
*)
(* /QUIZ *)
(* INSTRUCTORS: (4) *)

(* QUIZ *)
(** This one?
[[
        @nil 3
]]

    (1) [list nat]

    (2) [list (list nat)]

    (3) [list bool]

    (4) No type can be assigned
*)
(* /QUIZ *)
(* INSTRUCTORS: (4) *)
(* /TERSE *)

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

(* ###################################################### *)
(** ** Polymorphic Options *)

(** FULL: Our last polymorphic type for now is _polymorphic options_,
    which generalize [natoption] from the previous chapter.  (We put
    the definition inside a module because the standard library
    already defines [option] and it's this one that we want to use
    below.) *)

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
