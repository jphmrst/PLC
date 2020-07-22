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

## Polymorphic lists

In the last section, we worked with lists containing just numbers.
Obviously, interesting programs also need to be able to manipulate
lists with elements from other types — lists of booleans, lists of
lists, etc.  We _could_ just define a new inductive datatype for each
of these, for example

```
data BoolList : Set where
  []bool : BoolList
  _::bool_ : Bool → BoolList → BoolList
```

But this would quickly become tedious, partly because we have to make
up different constructor names for each datatype, but mostly because
we would also need to define new versions of all our list manipulating
functions (`length`, `rev`, etc.) for each new datatype definition.

To avoid all this repetition, Agda supports _polymorphic_ inductive
type definitions.  Single-type lists like `NatList` or `BoolList` are
*monomorphic*, literally meaning that they have one form.  A
polyporphic datatype can be applied to different elements types — it
has *many* forms, not just one.  For example, here is a first version
of a _polymorphic list_ datatype.

```
module Poly1 where
  data List : Set → Set where
    [] : (x : Set) → List x
    cons : (x : Set) → x → List x → List x
```

This is just like the definition of `NatList` from the previous
chapter, except that the `ℕ` argument to the cons constructor has
been replaced by an arbitrary type `x`, a binding for `x` has been
added to the function header on the first line, and the occurrences of
`NatList` in the types of the constructors have been replaced by `List x`.

We will improve this datatype shortly, so we have wrapped this first
draft in its own local `module` declaration.  This way, we can reuse
the same names in other modules, and avoid having to write
`++version2` or similar silliness.

What sort of thing is `List` itself?  A good way to think about it is
that the definition of `List` is a _function_ from one datatype to
another, inductively-defined datatype.  In other words, `List` is a
function from one type to another.  For any particular type `x`, the
type `List x` is the inductively defined set of lists whose elements
are of type `x`.

#### Exercise `typelist1` (starting) {#typelist1}

Use `C-c C-d` to verify that `List` (or since we have defined it
within a local module, `Poly1.List`) has type `Set → Set`.

The parameter `x` in this version of `List` automatically becomes a
parameter to the constructors `[]` and `cons` — that is, `[]` and
`cons` are now polymorphic constructors; when we use them, we must now
provide a first argument that is the type of the List they are
building. For example, `[] ℕ` constructs the empty List of type
`ℕ`.

#### Exercise `typenil1` (starting) {#typenil1}

Use `C-c C-d` to verify that

 - `Poly1.[] ℕ` has type `Poly1.List ℕ`.
 - `Poly1.cons ℕ 3 (Poly1.[] ℕ)` has type `Poly1.List ℕ`.

### Quantification for type arguments

In our first version of polymorphic lists, the type of the elements of
the list was an argument to both the type name `List`, and to its two
constructors.  It is more common to structure generic types to use
*quantification* for the type argument in the constructors:

```
data List : (x : Set) → Set where
  [] : ∀ {x : Set} → List x
  _::_ : ∀ {x : Set} → x → List x → List x

infixr 5 _::_
```

The symbol ∀ is pronounced "for all."  There is a sense in which these
constructors are equivalent to our earlier ones, but there are
advantages to using quantification for constructors and functions.  In
particular, we can ask Agda to infer the arguments of a type
automatically by writing them in curly braces `{` and `}` instead of
parentheses `(` and `)`:

For both of these constructors, `x` becomes an *implicit* type
argument.  Now when we write a list of natural numbers, we do not need
to write the type argument with every name use.  For example, you can
use `C-c C-d` to check that

    1 :: 2 :: 3 :: []

is a well-typed expression, with type `List ℕ`.

What is the type of `[]`?  `C-c C-d` gives us a cryptic result:

    List _x_17

(Your system may show you a different number than 17 — which is fine.)
Clearly, and unsurprisingly, it is a `List`.  But what is this type
`_x_17` for the elements?  We have asked Agda to work out the element
type for `[]` itself, but when we describe the empty list there are no
elements from which Agda can work out the right type!  So Agda uses
`_x_17` as a placeholder, unless and until a particular use allows it
to figure out a more specific type.

But we can be more specific about the element type if we want for this
empty list.  We can pass an *explicit* type to `[]` or `_::_` by
enclosing the type argment is curly braces.  So

 - `[] {ℕ}` has the type `List ℕ`
 - `[] {Bool}` has the type `List Bool`

even though there are no other elements of the list to require these
specific element types.

Note that although our construction of `List` does allow lists with
different element types, for any single list the element type **must
be consistent**.  We can describe a list of numbers, a list of boolean
values, a list of pairs where each pair contains one number and one
boolean.  But we **cannot** describe a list which contains both
numbers and booleans.  If we try, Agda gives us an error.  For
example, we get an error if we evaluate or typecheck this expression:

    1 :: true :: []

The type of `_::_` states that its left element has the same type as
the elements of the list it should expect for its right element.  So
when Agda sees a list which begins

    1 ::

since `1` has type `ℕ`, Agda expects that the expression which follows
the `::` should have type `List ℕ`.  But `true :: []` does not have
this type, and the evaluator reports an error.

The following defiition of `List` is equivalent to the one above:

    data List (x : Set) : Set where
      [] : List x
      _::_ : x → List x → List x

When we move the argument declaration `(x : Set)` to the left side of
the colon `:`, Agda knows that it should be implicitly quantified for
each of the constructors.

### Polymorphic list functions

We can now define polymorphic versions of the functions we've already
seen for `NatList`.  Like the constructors for polymorphic `List`,
each of these functions will be quantified over the type of the
elements of the list.

Our monomorphic version of the `repeat` function took a **number** `n`
and a `count` of how many times `n` should be repeated in the result
list.  In our polymorphic version, we quantify over an element type
`x`, and the first explicit value argument of `repeat` is some value
of type `x`:

```
repeat : ∀ {x : Set} → x → ℕ → List x
repeat _ 0 = []
repeat x (suc n) = x :: repeat x n

_ : repeat 5 2 ≡ 5 :: 5 :: []
_ = refl

_ : repeat true 4 ≡ true :: true :: true :: true :: []
_ = refl
```

As with `[]` we can make the type argument explicit if we wish:

    repeat {ℕ} 5 2
    repeat {Bool} true 4

but we must use the curly braces to make the implicit argument
explicit.

You should try to find a balance in your own code between too many
type annotations (which can clutter and distract) and too few (which
can sometimes require readers to perform complex type inference in
their heads in order to understand your code).

#### Exercise `mumbegrumble` (starting) {#mumbegrumble}

Consider the following two inductively defined types.

```
module MumbleGrumble where

  data mumble : Set where
    a : mumble
    b : mumble → ℕ → mumble
    c : mumble

  data grumble : Set -> Set where
    d : ∀ {x : Set} → mumble → grumble x
    e : ∀ {x : Set} → grumble x
```

Which of the following are well-typed elements of `grumble x` for some
type `x`?  Try to answer without using `C-c C-d` or `C-c C-l` before
checking your answer.

 - `d (b a 5)`
 - `d mumble (b a 5)`
 - `d bool (b a 5)`
 - `e bool true`
 - `e mumble (b c 0)`
 - `e bool (b c 0)`
 - `c`

#### Exercise `genericlength` (practice) {#genericlength}

Write a polymorphic version of `length`:

    length : ∀ {x} -> List x -> ℕ
    -- Your clauses go here

    _ : length (true :: []) ≡ 1
    _ = refl

    _ : length (2 :: 4 :: 6 :: []) ≡ 3
    _ = refl

#### Exercise `genericappend` (practice) {#genericappend}

Write a polymorphic function `_++_` for appending two lists:

    infixr 5 _++_
    _++_ : ∀ {x : Set} -> List x -> List x -> List x
    -- Your clauses go here

    _ : [] ++ (1 :: []) ≡ 1 :: []
    _ = refl

    _ : (2 :: 4 :: 6 :: []) ++ (8 :: 10 :: []) ≡ (2 :: 4 :: 6 :: 8 :: 10 :: [])
    _ = refl

#### Exercise `genericreverse` (practice) {#genericreverse}

    reverse : ∀ (x : Set) → List x → List x
    -- Your clauses go here

    _ : rev (1 :: []) ≡ 1 :: []
    _ = refl

    _ : rev (10 :: 20 :: 30 :: []) ≡ (30 :: 20 :: 10 :: [])
    _ = refl

## Polymorphic pairs

Following the same pattern, the definition for pairs of numbers that
we gave in the last chapter can be generalized to _polymorphic pairs_,
often called _products_.

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
    type `x` and `y` has type `Y`, then `(x,y)` has type `X*Y`. *)
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
    into a List of pairs.  In other functional languages, it is often
    called `zip`; we call it `combine` for consistency with Coq's
    standard library. *)
(** TERSE: *** *)
(** TERSE: What does this function do? *)

Fixpoint combine {X Y : Type} (lx : List X) (ly : List Y)
           : List (X*Y) :=
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
    List of pairs and returns a pair of lists.  In many functional
    languages, it is called `unzip`.

    Fill in the definition of `split` below.  Make sure it passes the
    given unit test. *)

Fixpoint split {X Y : Type} (l : List (X*Y))
               : (List X) * (List Y)
  (* ADMITDEF *) :=
  match l with
  | `` => (``, ``)
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.
(* /ADMITDEF *)
`<
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

## Polymorphic options

Our last polymorphic type for now is _polymorphic options_, which
generalize `natoption` from the previous chapter.  (We put the
definition inside a module because the standard library already
defines `option` and it's this one that we want to use below.)

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

Fixpoint nth_error {X : Type} (l : List X) (n : ℕ)
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

Definition hd_error {X : Type} (l : List X) : option X
  (* ADMITDEF *) :=
  match l with
  | `` => None
  | a :: l' => Some a
  end.
(* /ADMITDEF *)

(** Once again, to force the implicit arguments to be explicit,
    we can use `@` before the name of the function. *)

Check @hd_error : forall X : Type, List X → option X.

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
