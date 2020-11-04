---
title     : "Logic: Connectives and deduction"
layout    : page
prev      : /DataRel/
permalink : /Logic/
next      : /MapProps/
---

```
module plc.vfp.Logic where
```

<!-- The ⊥ ⊎ A ≅ A exercise requires a (inj₁ ()) pattern,
     which the reader will not have seen. Restore this
     exercise, and possibly also associativity? Take the
     exercises from the final sections on distributivity
     and exponentials? -->

This section introduces the basic logical connectives, and the ways we
can use them in proofs in Agda.


## Imports

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Bool
open import Data.List
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Function using (_∘_)
open import plc.vfp.Induction using (+-comm)
open import plc.vfp.Relations using (_≃_; _⇔_)
open import plc.vfp.DataRel using (_∈_; All; []; _∷_; Any; here; there)
open _⇔_
```

## Conjunction {#conj}

Given two propositions `A` and `B`, the conjunction `A × B` holds
if both `A` holds and `B` holds.  We formalise this idea by
declaring a suitable inductive type:
```
data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B
```
Evidence that `A × B` holds is of the form `⟨ M , N ⟩`, where `M`
provides evidence that `A` holds and `N` provides evidence that `B`
holds.

Given evidence that `A × B` holds, we can conclude that either
`A` holds or `B` holds:
```
proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ x , y ⟩ = y
```
If `L` provides evidence that `A × B` holds, then `proj₁ L` provides evidence
that `A` holds, and `proj₂ L` provides evidence that `B` holds.

Equivalently, we could also declare conjunction as a record type:
```
record _×′_ (A B : Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B
open _×′_
```
Here record construction

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

corresponds to the term

    ⟨ M , N ⟩

where `M` is a term of type `A` and `N` is a term of type `B`.

When `⟨_,_⟩` appears in a term on the right-hand side of an equation
we refer to it as a _constructor_, and when it appears in a pattern on
the left-hand side of an equation we refer to it as a _destructor_.
We may also refer to `proj₁` and `proj₂` as destructors, since they
play a similar role.

In other situations, you will find `⟨_,_⟩` referred to as
_introducing_ a conjunction, and `proj₁` and `proj₂` as _eliminating_
a conjunction.  In fact, the former is sometimes given the name `×-I`
and the latter two the names `×-E₁` and `×-E₂`.  As we read the rules
from top to bottom, introduction and elimination do what they say on
the tin: the first _introduces_ a formula for the connective, which
appears in the conclusion but not in the hypotheses; the second
_eliminates_ a formula for the connective, which appears in a
hypothesis but not in the conclusion.  An introduction rule describes
under what conditions we say the connective holds — how to _define_
the connective. An elimination rule describes what we may conclude
when the connective holds — how to _use_ the connective.

(The paragraph above was adopted from "Propositions as Types", Philip Wadler,
_Communications of the ACM_, December 2015.)

In this case, applying each destructor and reassembling the results with the
constructor is the identity over products:
```
η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl
```
The pattern matching on the left-hand side is essential, since
replacing `w` by `⟨ x , y ⟩` allows both sides of the
propositional equality to simplify to the same term.

We set the precedence of conjunction so that it binds less
tightly than anything save disjunction, which we will define below:
```
infixr 2 _×_
```
Thus, `m ≤ n × n ≤ p` parses as `(m ≤ n) × (n ≤ p)`.

You may have noticed that `×` seems very similar to the `Prod` type of
the last chapter.  In fact, it is exactly the same, except for its
name!

Given two types `A` and `B`, we refer to `A × B` as the
_product_ of `A` and `B`.  In set theory, it is also sometimes
called the _Cartesian product_, and in computing it corresponds
to a _record_ type. Among other reasons for
calling it the product, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A × B` has `m * n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members:

```
data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri
```

Then the type `Bool × Tri` has six members:

    ⟨ true  , aa ⟩    ⟨ true  , bb ⟩    ⟨ true ,  cc ⟩
    ⟨ false , aa ⟩    ⟨ false , bb ⟩    ⟨ false , cc ⟩

For example, the following function enumerates all
possible arguments of type `Bool × Tri`:

```
×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩  =  1
×-count ⟨ true  , bb ⟩  =  2
×-count ⟨ true  , cc ⟩  =  3
×-count ⟨ false , aa ⟩  =  4
×-count ⟨ false , bb ⟩  =  5
×-count ⟨ false , cc ⟩  =  6
```


## A unit of truth

Truth `⊤` always holds.  We formalise this idea by
declaring a suitable inductive type:

```
data ⊤ : Set where

  tt :
    --
    ⊤
```

Evidence that `⊤` holds is of the form `tt`.  Note that `⊤` is not a
capital letter T; it is a Unicode character which we pronounce "unit".

There is an introduction rule, but no elimination rule.
Given evidence that `⊤` holds, there is nothing more of interest we
can conclude.  Since truth always holds, knowing that it holds tells
us nothing new.

The nullary case of `η-×` is `η-⊤`, which asserts that any
value of type `⊤` must be equal to `tt`:
```
η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl
```
The pattern matching on the left-hand side is essential.  Replacing
`w` by `tt` allows both sides of the propositional equality to
simplify to the same term.


## Disjunction

Given two propositions `A` and `B`, the disjunction `A ⊎ B` holds
if either `A` holds or `B` holds.  We formalise this idea by
declaring a suitable inductive type:
```
data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B
```
Evidence that `A ⊎ B` holds is either of the form `inj₁ M`, where `M`
provides evidence that `A` holds, or `inj₂ N`, where `N` provides
evidence that `B` holds.

Given evidence that `A → C` and `B → C` both hold, then given
evidence that `A ⊎ B` holds we can conclude that `C` holds:
```
case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y
```
Pattern matching against `inj₁` and `inj₂` is typical of how we exploit
evidence that a disjunction holds.

When `inj₁` and `inj₂` appear on the right-hand side of an equation we
refer to them as _constructors_, and when they appear on the
left-hand side we refer to them as _destructors_.  We also refer to
`case-⊎` as a destructor, since it plays a similar role.  Other
terminology refers to `inj₁` and `inj₂` as _introducing_ a
disjunction, and to `case-⊎` as _eliminating_ a disjunction; indeed
the former are sometimes given the names `⊎-I₁` and `⊎-I₂` and the
latter the name `⊎-E`.

Applying the destructor to each of the constructors is the identity:
```
η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl
```
More generally, we can also throw in an arbitrary function from a disjunction:
```
uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl
```
The pattern matching on the left-hand side is essential.  Replacing
`w` by `inj₁ x` allows both sides of the propositional equality to
simplify to the same term, and similarly for `inj₂ y`.

We set the precedence of disjunction so that it binds less tightly
than any other declared operator:
```
infixr 1 _⊎_
```
Thus, `A × C ⊎ B × C` parses as `(A × C) ⊎ (B × C)`.

Given two types `A` and `B`, we refer to `A ⊎ B` as the _sum_ of `A`
and `B`.  In set theory, it is also sometimes called the _disjoint
union_, and in computing it corresponds to a _variant record_
type. Among other reasons for calling it the sum, note that if type
`A` has `m` distinct members, and type `B` has `n` distinct members,
then the type `A ⊎ B` has `m + n` distinct members.  For instance,
consider again types `Bool` and `Tri`: the type `Bool ⊎ Tri` has five
members:

    inj₁ true     inj₂ aa
    inj₁ false    inj₂ bb
                  inj₂ cc

For example, the following function enumerates all
possible arguments of type `Bool ⊎ Tri`:
```
⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)   =  1
⊎-count (inj₁ false)  =  2
⊎-count (inj₂ aa)     =  3
⊎-count (inj₂ bb)     =  4
⊎-count (inj₂ cc)     =  5
```

## False is empty

False `⊥` never holds.  We formalise this idea by declaring
a suitable inductive type:
```
data ⊥ : Set where
  -- no clauses!
```
There is no possible evidence that `⊥` holds.

Dual to `⊤`, for `⊥` there is no introduction rule but an elimination rule.
Since false never holds, knowing that it holds tells us we are in a
paradoxical situation.  Given evidence that `⊥` holds, we might
conclude anything!  This is a basic principle of logic, known in
medieval times by the Latin phrase _ex falso_, and known to children
through phrases such as "if pigs had wings, then I'd be the Queen of
Sheba".  We formalise it as follows:
```
⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()
```
This is our first use of the _absurd pattern_ `()`.
Here since `⊥` is a type with no members, we indicate that it is
_never_ possible to match against a value of this type by using
the pattern `()`.  Since we are claiming that the pattern never
matches, we do not give it a right-hand side.

The nullary case of `case-⊎` is `⊥-elim`.  By analogy,
we might have called it `case-⊥`, but chose to stick with the name
in the standard library.

The nullary case of `uniq-⊎` is `uniq-⊥`, which asserts that `⊥-elim`
is equal to any arbitrary function from `⊥`:
```
uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()
```
Using the absurd pattern asserts there are no possible values for `w`,
so the equation holds trivially.

We refer to `⊥` as the _empty_ type. And, indeed,
type `⊥` has no members. For example, the following function
enumerates all possible arguments of type `⊥`:
```
⊥-count : ⊥ → ℕ
⊥-count ()
```
Here again the absurd pattern `()` indicates that no value can match
type `⊥`.

## Negation

Given a proposition `A`, the negation `¬ A` holds if `A` cannot hold.
We formalise this idea by declaring negation to be the same
as implication of false:
```
¬_ : Set → Set
¬ A = A → ⊥
```
This is a form of _proof by contradiction_: if assuming `A` leads
to the conclusion `⊥` (a contradiction), then we must have `¬ A`.

Evidence that `¬ A` holds is of the form

    λ{ x → N }

where `N` is a term of type `⊥` containing as a free variable `x` of type `A`.
In other words, evidence that `¬ A` holds is a function that converts evidence
that `A` holds into evidence that `⊥` holds.

Given evidence that both `¬ A` and `A` hold, we can conclude that `⊥` holds.
In other words, if both `¬ A` and `A` hold, then we have a contradiction:
```
¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x
```
Here we write `¬x` for evidence of `¬ A` and `x` for evidence of `A`.  This
means that `¬x` must be a function of type `A → ⊥`, and hence the application
`¬x x` must be of type `⊥`.  Note that this rule is just a special case of `→-elim`.

We set the precedence of negation so that it binds more tightly
than disjunction and conjunction, but less tightly than anything else:
```
infix 3 ¬_
```
Thus, `¬ A × ¬ B` parses as `(¬ A) × (¬ B)` and `¬ m ≡ n` as `¬ (m ≡ n)`.

In _classical_ logic, we have that `A` is equivalent to `¬ ¬ A`.
As we discuss below, in Agda we use _intuitionistic_ logic, where
we have only half of this equivalence, namely that `A` implies `¬ ¬ A`:
```
¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x  =  λ{¬x → ¬x x}
```
Let `x` be evidence of `A`. We show that assuming
`¬ A` leads to a contradiction, and hence `¬ ¬ A` must hold.
Let `¬x` be evidence of `¬ A`.  Then from `A` and `¬ A`
we have a contradiction, evidenced by `¬x x`.  Hence, we have
shown `¬ ¬ A`.

An equivalent way to write the above is as follows:
```
¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x
```
Here we have simply converted the argument of the lambda term
to an additional argument of the function.  We will usually
use this latter style, as it is more compact.

We cannot show that `¬ ¬ A` implies `A`, but we can show that
`¬ ¬ ¬ A` implies `¬ A`:
```
¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)
```
Let `¬¬¬x` be evidence of `¬ ¬ ¬ A`. We will show that assuming
`A` leads to a contradiction, and hence `¬ A` must hold.
Let `x` be evidence of `A`. Then by the previous result, we
can conclude `¬ ¬ A`, evidenced by `¬¬-intro x`.  Then from
`¬ ¬ ¬ A` and `¬ ¬ A` we have a contradiction, evidenced by
`¬¬¬x (¬¬-intro x)`.  Hence we have shown `¬ A`.

Another law of logic is _contraposition_,
stating that if `A` implies `B`, then `¬ B` implies `¬ A`:
```
contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)
```
Let `f` be evidence of `A → B` and let `¬y` be evidence of `¬ B`.  We
will show that assuming `A` leads to a contradiction, and hence `¬ A`
must hold. Let `x` be evidence of `A`.  Then from `A → B` and `A` we
may conclude `B`, evidenced by `f x`, and from `B` and `¬ B` we may
conclude `⊥`, evidenced by `¬y (f x)`.  Hence, we have shown `¬ A`.

Using negation, it is straightforward to define inequality:
```
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)
```
It is trivial to show distinct numbers are not equal:
```
_ : 1 ≢ 2
_ = λ()
```
This is our first use of an absurd pattern in a lambda expression.
The type `M ≡ N` is occupied exactly when `M` and `N` simplify to
identical terms. Since `1` and `2` simplify to distinct normal forms,
Agda determines that there is no possible evidence that `1 ≡ 2`.
As a second example, it is also easy to validate
Peano's postulate that zero is not the successor of any number:
```
peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()
```
The evidence is essentially the same, as the absurd pattern matches
all possible evidence of type `zero ≡ suc m`.

Given the correspondence of implication to exponentiation and
false to the type with no members, we can view negation as
raising to the zero power.  This indeed corresponds to what
we know for arithmetic, where

    0 ^ n  ≡  1,  if n ≡ 0
           ≡  0,  if n ≢ 0

Indeed, there is exactly one proof of `⊥ → ⊥`.  We can write
this proof two different ways:
```
id₁ : ⊥ → ⊥
id₁ x = x

id₂ : ⊥ → ⊥
id₂ ()
```

### Non-inclusion

In the DataRel section we built a predicate `_∈_` to test whether a
list contains a particular element.  With negation we can define a
non-inclusion predicate `_∉_`,

```
infix 4 _∉_

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)
```

Extending the example list `(0 ∷ 1 ∷ 0 ∷ 2 ∷ [])` of that predicate we
can demonstrate that three is not in the list, because any possible
proof that it is in the list leads to contradiction:

```
not-in : 3 ∉ (0 ∷ 1 ∷ 0 ∷ 2 ∷ [])
not-in (here ())
not-in (there (here ()))
not-in (there (there (here ())))
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))
```

The five occurrences of `()` attest to the fact that there is no
possible evidence for `3 ≡ 0`, `3 ≡ 1`, `3 ≡ 0`, `3 ≡ 2`, and
`3 ∈ []`, respectively.

## Implication

Given two propositions `A` and `B`, the implication `A → B` holds if
whenever `A` holds then `B` must also hold.  We have used implication
throughout this chapter, using Agda's built-in function type.

Evidence that `A → B` holds is of the form

    λ (x : A) → N

where `N` is a term of type `B` containing as a free variable `x` of type `A`.
Given a term `L` providing evidence that `A → B` holds, and a term `M`
providing evidence that `A` holds, the term `L M` provides evidence that
`B` holds.  In other words, evidence that `A → B` holds is a function that
converts evidence of `A` holding into evidence that `B` holds.

Put another way, if we know that `A → B` and `A` both hold,
then we may conclude that `B` holds:
```
→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M
```
In medieval times, this rule was known by the name _modus ponens_.
It corresponds to function application.

Defining a function, whether with a named definition or a lambda abstraction,
is referred to as _introducing_ a function,
while applying a function is referred to as _eliminating_ the function.

Elimination followed by introduction is the identity:
```
η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl
```

Implication binds less tightly than any other operator. Thus, `A ⊎ B →
B ⊎ A` parses as `(A ⊎ B) → (B ⊎ A)`.

Given two types `A` and `B`, we refer to `A → B` as the _function_
space from `A` to `B`.  It is also sometimes called the _exponential_,
with `B` raised to the `A` power.  Among other reasons for calling
it the exponential, note that if type `A` has `m` distinct
members, and type `B` has `n` distinct members, then the type
`A → B` has `nᵐ` distinct members.  For instance, consider a
type `Bool` with two members and a type `Tri` with three members,
as defined earlier. Then the type `Bool → Tri` has nine (that is,
three squared) members:

    λ{true → aa; false → aa}  λ{true → aa; false → bb}  λ{true → aa; false → cc}
    λ{true → bb; false → aa}  λ{true → bb; false → bb}  λ{true → bb; false → cc}
    λ{true → cc; false → aa}  λ{true → cc; false → bb}  λ{true → cc; false → cc}

For example, the following function enumerates all possible
arguments of the type `Bool → Tri`:
```
→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...          | aa     | aa      =   1
...          | aa     | bb      =   2
...          | aa     | cc      =   3
...          | bb     | aa      =   4
...          | bb     | bb      =   5
...          | bb     | cc      =   6
...          | cc     | aa      =   7
...          | cc     | bb      =   8
...          | cc     | cc      =   9
```

## Logical equivalence

Recall that [in an earlier exercise we defined]({{ site.baseurl
}}/Relation/#iff) the `⇔` connective to correspond to implication in
both direction, where either proposition defines the other.

    record _⇔_ (A B : Set) : Set where
      field
        to   : A → B
        from : B → A

We can use this logical equivalence to state and prove familiar laws
such as the commutativity and associativity of various operators, the
De Morgan laws, and the distributivity laws.  For example:

```
×-comm : ∀ (A B : Set) → (A × B) ⇔ (B × A)
×-comm AB BA = record
  { to = λ AB×BA → ⟨ proj₂ AB×BA , proj₁ AB×BA ⟩
  ; from = λ BA×AB → ⟨ proj₂ BA×AB , proj₁ BA×AB ⟩
  }
```

### All and append

A predicate holds for every element of one list appended to another if and
only if it holds for every element of both lists:
```
All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to       =  to' xs ys
    ; from     =  from' xs ys
    }
  where

  to' : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to' [] ys Pys = ⟨ [] , Pys ⟩
  to' (x ∷ xs) ys (Px ∷ Pxs++ys) with to' xs ys Pxs++ys
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from' : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from' [] ys ⟨ [] , Pys ⟩ = Pys
  from' (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from' xs ys ⟨ Pxs , Pys ⟩
```

#### Exercise `Any-++-⇔` (recommended)

Prove a result similar to `All-++-⇔`, but with `Any` in place of `All`, and a suitable
replacement for `_×_`.  As a consequence, demonstrate an equivalence relating
`_∈_` and `_++_`.

```
-- Your code goes here
```

#### Exercise `All-++-≃` (stretch)

Show that the equivalence `All-++-⇔` can be extended to an isomorphism.

```
-- Your code goes here
```

#### Exercise `¬Any⇔All¬` (recommended)

Show that `Any` and `All` satisfy a version of De Morgan's Law:

    (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs

(Can you see why it is important that here `_∘_` is generalised
to arbitrary levels, as described in the section on
[universe polymorphism]({{ site.baseurl }}/Equality/#unipoly)?)

Do we also have the following?

    (¬_ ∘ All P) xs ⇔ Any (¬_ ∘ P) xs

If so, prove; if not, explain why.


```
-- Your code goes here
```

#### Exercise `All-∀` (practice)

Show that `All P xs` is isomorphic to `∀ {x} → x ∈ xs → P x`.

```
-- You code goes here
```


#### Exercise `Any-∃` (practice)

Show that `Any P xs` is isomorphic to `∃[ x ] (x ∈ xs × P x)`.

```
-- You code goes here
```

## More exercises

#### Exercise `⊎-comm` (starting) {#or-comm}

Show that `⊎` is commutative under `⇔`:

```
postulate ⊎-comm : ∀ (A B : Set) → A ⊎ B ⇔ B ⊎ A
-- Remove the "postulate" keyword and add your proof code here
```

#### Exercise `×-assoc` (starting) {#prod-assoc}

Show that `×` is associative under `⇔`:

```
postulate ×-assoc : ∀ (A B C : Set) → (A × B) × C ⇔ A × (B × C)
-- Remove the "postulate" keyword and add your proof code here
```

#### Exercise `⊎-assoc` (starting) {#or-assoc}

Show that `⊎` is associative under `⇔`:

```
postulate ⊎-assoc : ∀ (A B C : Set) → (A ⊎ B) ⊎ C ⇔ A ⊎ (B ⊎ C)
-- Remove the "postulate" keyword and add your proof code here
```

#### Exercise `×-id-⊤` (starting) {#prod-id}

Show that `⊤` is an identity for `×`:

```
postulate ×-id-⊤ᴸ : ∀ A → (⊤ × A) ⇔ A
-- Remove the "postulate" keyword and add your proof code here

postulate ×-id-⊤ᴿ : ∀ A → (A × ⊤) ⇔ A
-- Remove the "postulate" keyword and add your proof code here
```

#### Exercise `⊎-id-⊥` (practice) {#prod-id}

Show that `⊥` is an identity for `⊎`:

```
postulate ⊎-id-⊥ᴸ : ∀ A → (⊥ ⊎ A) ⇔ A
-- Remove the "postulate" keyword and add your proof code here
```

```
postulate ⊎-id-⊥ᴿ : ∀ A → (A ⊎ ⊥) ⇔ A
-- Remove the "postulate" keyword and add your proof code here
```

#### Exercise `⇔defn` (starting) {#iff-defn}

Show that:

```
postulate ↔-defn : ∀ (A B : Set) → (A ⇔ B) ⇔ ((A → B) × (B → A))
-- Remove the "postulate" keyword and add your proof code here
```

#### Exercise `⊎-weak-×` (recommended)

Show that the following property holds:
```
postulate
  ⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
-- Remove the "postulate" keyword and add your proof code here
```
This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.


#### Exercise `⊎×-implies-×⊎` (practice)

Show that a disjunct of conjuncts implies a conjunct of disjuncts:
```
postulate
  ⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
-- Remove the "postulate" keyword and add your proof code here
```
Does the converse hold? If so, prove; if not, give a counterexample.


#### Exercise `demorgan` (practice)

Show De Morgan's laws:

```
postulate ×-demorgan : ∀ {A B : Set} → (¬ (A × B)) ⇔ ((¬ A) ⊎ (¬ B))
-- Remove the "postulate" keyword and add your proof code here

postulate ⊎-demorgan : ∀ {A B : Set} → (¬ (A ⊎ B)) ⇔ ((¬ A) × (¬ B))
-- Remove the "postulate" keyword and add your proof code here
```



#### Exercise `<-irreflexive` (recommended)

Using negation, show that
[strict inequality]({{ site.baseurl }}/Relations/#strict-inequality)
is irreflexive, that is, `n < n` holds for no `n`.

```
-- Your code goes here
```

#### Exercise `trichotomy` (practice)

Show that strict inequality satisfies
[trichotomy]({{ site.baseurl }}/Relations/#trichotomy),
that is, for any naturals `m` and `n` _exactly_ one of the following holds:

* `m < n`
* `m ≡ n`
* `m > n`

Here "exactly one" means that not only one of the three must hold,
but that when one holds the negation of the other two must also hold.

```
-- Your code goes here
```

#### Exercise `Classical` (stretch)

Consider the following principles:

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

Show that each of these implies all the others.

```
-- Your code goes here
```

#### Exercise `Stable` (stretch)

Say that a formula is _stable_ if double negation elimination holds for it:
```
Stable : Set → Set
Stable A = ¬ ¬ A → A
```
Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.

```
-- Your code goes here
```

## Universal quantification

_Quantifiers_ are structures in the language of formulas which define
a scope for a name.  The name is available for use within that scope,
but is not available outside of that scope.

We have made very frequent use already of one quantifier: universal
quantification `∀`.  The quantifier is pronounced "for all," and means
exactly what we pronounce.  In a formula `∀ (x: A) → B`, the name `x`
may occur within `B`.  If this quantification holds, then the formula
we obtain by replacing `x` in `B` with any elements of `A` will also
hold.  Like the evidence for an implication, evidence for the
quantification is a function.  Given evidence for `A`, a function
serving as evidence for `∀ (x: A) → B` produces evidence for `B`.

Despite our frequent use of universals, so far we have really only
used them in one way: at the very top level of a signature,

    name : ∀ (binding₁) (binding₂) ... (bindingₙ) → ...

In fact, we can use universals _anywhere_ in a formula that we could
use any other formula.  For example, we could prove

    ∀ {A : Set} {B : A → Set}
      → (∀ (x : A) → B x)
      → (M : A)
        ----------------------
      → B M

There is a top-level universal as usual, but notice that there is a
second universal inside the first premise.  The scope of the name `x`
is restricted to that premise, from the right side of the quantifier's
arrow, to the closing parenthesis on that line:

    ∀ (x : A) → B x

It would be meaningless to, for example, declare `M : x` instead of `M
: A` — the name `x` is simply not visible from that line.

The formula above serves as an elimination rule for `∀`, telling us
how we can use a formula headed by a universal to conclude evidence
for another formula:

```
∀-elim : ∀ {A : Set} {B : A → Set}
  → (∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
```

`B` is a predicate which takes a single argument of type `A`, and
returns a formula.  The evidence provided for the first premise `∀ (x
: A) → B x` will be a function which takes evidence for `A` named `x`,
and returns evidence for the formula obtained by passing `x` to `B`.
Since the second premise of `∀-elim` is `A` has evidence `M`, we can
simply pass its evidence to that function to obtain evidence of `B M`.

```
∀-elim L M = L M
```


#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction:
```
postulate
  ∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
```
Compare this with the result (`→-distrib-×`) in
the [Connectives]({{ site.baseurl }}/LogicRedux/) section.


#### Exercise `⊎∀-implies-∀⊎` (practice)

Show that a disjunction of universals implies a universal of disjunctions:
```
postulate
  ⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
```
Does the converse hold? If so, prove; if not, explain why.


## Extensionality {#extensionality}

Extensionality asserts that the only way to distinguish functions is
by applying them; if two functions applied to the same argument always
yield the same result, then they are the same function.

Agda does not presume extensionality, but we can postulate that it holds:
```
postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
```
Postulating extensionality does not lead to difficulties, as it is
known to be consistent with the theory that underlies Agda.

Note that the ∀-quantification in the first premise of
`extensionality` is local: the scope of the `x` is only in that
premise.  The evidence supplied for this premise is a function which
maps any `x` of suitable type to the evidence that `f x` and `g x` are
equal.

As an example, consider that we need results from two libraries,
one where addition is defined, as in
Chapter [Naturals]({{ site.baseurl }}/Naturals/),
and one where it is defined the other way around.
```
_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)
```
Applying commutativity, it is easy to show that both operators always
return the same result given the same arguments:
```
same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
  helper m zero    = refl
  helper m (suc n) = cong suc (helper m n)
```
However, it might be convenient to assert that the two operators are
actually indistinguishable. This we can do via two applications of
extensionality:
```
same : _+′_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))
```

#### Exercise `extDouble` (starting) {#extDouble}

Use extensionality to show that `λ x → x * x` and `2 *_` are equal.

    _ : (λ x → x * x) ≡ (2 *_)
    _ = -- Your proof code goes here

#### Exercise `map-compose-ext` (practice)

Use extensionality to prove a more minimal version of Exercise
`map-compose` from the DataProps section:

    map-compose : map (g ∘ f) ≡ (map g ∘ map f)

```
-- Your code goes here
```

#### Exercise `∀-×` (stretch)

Recall the `Tri` datatype from the Conjunction section above.
Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.
Hint: you will need to postulate a version of extensionality that
works for dependent functions.

#### Exercise `¬Any≃All¬` (stretch)

Show that the equivalence `¬Any⇔All¬` can be extended to an isomorphism.
You will need to use extensionality.

```
-- Your code goes here
```


## Existential quantification

Existentials are less common and more subtle than universals.  Rather
than requiring that the body hold for _all_ values of the quantified
variable, we require evidence that the body holds for _at least one_
value of the quantified variable.  What is the form of such evidence?
For one thing, we must identify the value which satisfies the body.
This value is called a _witness_.  Along with the witness, we must
provide evidence for the version of the formula using the witness.  So
the evidence for an existential is a pair.

Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the existentially quantified
proposition `Σ[ x ∈ A ] B x` holds if for some term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  Variable `x` appears free in `B x` but bound in
`Σ[ x ∈ A ] B x`.

To formalize this idea, we begin with the inductive type:

```
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B
```

We define a convenient syntax for existentials as follows:

```
Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B
```

This is our first use of a `syntax` declaration, which specifies that
the term on the left may be written with the syntax on the right.  The
special syntax is available only when the identifier `Σ-syntax` is
imported.  Agda will apply the rewriting associated with this
declaration before it checks the scope of names: after rewriting
according to `syntax`, `B` becomes the body of a lambda expression
whose parameter is `x`.  So this means that in the expression `Σ[ x ∈
A ] B`, we can use `x` in `B` — the rewriting will bring the uses of
`x` in `B` into the scope of `x`.

A common notation for existentials is `∃` (analogous to `∀` for universals).
We follow the convention of the Agda standard library, and reserve this
notation for the case where the domain of the bound variable is left implicit:
```
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B
```
The special syntax is available only when the identifier `∃-syntax` is imported.
We will tend to use this syntax, since it is shorter and more familiar.

Given evidence that `∀ x → B x → C` holds, where `C` does not contain
`x` as a free variable, and given evidence that `∃[ x ] B x` holds, we
may conclude that `C` holds:
```
∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y
```
In other words, if we know for every `x` of type `A` that `B x`
implies `C`, and we know for some `x` of type `A` that `B x` holds,
then we may conclude that `C` holds.  This is because we may
instantiate that proof that `∀ x → B x → C` to any value `x` of type
`A` and any `y` of type `B x`, and exactly such values are provided by
the evidence for `∃[ x ] B x`.

Indeed, the converse also holds, and the two together form an isomorphism:
```
∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }
```
The result can be viewed as a generalisation of currying.  Indeed, the code to
establish the isomorphism is identical to what we wrote when discussing
[implication]({{ site.baseurl }}/LogicRedux/#implication).

#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction:
```
postulate
  ∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
```

#### Exercise `∃×-implies-×∃` (practice)

Show that an existential of conjunctions implies a conjunction of existentials:
```
postulate
  ∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
```
Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-⊎` (practice)

Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.

## An existential example

Recall the definitions of `even` and `odd` from
the [Relations]({{ site.baseurl }}/Relations/) section:
```
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
```
A number is even if it is zero or the successor of an odd number, and
odd if it is the successor of an even number.

We will show that a number is even if and only if it is twice some
other number, and odd if and only if it is one more than twice
some other number.  In other words, we will show:

`even n`   iff   `∃[ m ] (    m * 2 ≡ n)`

`odd  n`   iff   `∃[ m ] (1 + m * 2 ≡ n)`

By convention, one tends to write constant factors first and to put
the constant term in a sum last. Here we've reversed each of those
conventions, because doing so eases the proof.

Here is the proof in the forward direction:
```
even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero                       =  ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩
```
We define two mutually recursive functions. Given
evidence that `n` is even or odd, we return a
number `m` and evidence that `m * 2 ≡ n` or `1 + m * 2 ≡ n`.
We induct over the evidence that `n` is even or odd:

* If the number is even because it is zero, then we return a pair
consisting of zero and the evidence that twice zero is zero.

* If the number is even because it is one more than an odd number,
then we apply the induction hypothesis to give a number `m` and
evidence that `1 + m * 2 ≡ n`. We return a pair consisting of `suc m`
and evidence that `suc m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

* If the number is odd because it is the successor of an even number,
then we apply the induction hypothesis to give a number `m` and
evidence that `m * 2 ≡ n`. We return a pair consisting of `suc m` and
evidence that `1 + m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

This completes the proof in the forward direction.

Here is the proof in the reverse direction:
```
∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even-zero
∃-even ⟨ suc m , refl ⟩  =  even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd-suc (∃-even ⟨ m , refl ⟩)
```
Given a number that is twice some other number we must show it is
even, and a number that is one more than twice some other number we
must show it is odd.  We induct over the evidence of the existential,
and in the even case consider the two possibilities for the number
that is doubled:

- In the even case for `zero`, we must show `zero * 2` is even, which
follows by `even-zero`.

- In the even case for `suc n`, we must show `suc m * 2` is even.  The
inductive hypothesis tells us that `1 + m * 2` is odd, from which the
desired result follows by `even-suc`.

- In the odd case, we must show `1 + m * 2` is odd.  The inductive
hypothesis tell us that `m * 2` is even, from which the desired result
follows by `odd-suc`.

This completes the proof in the backward direction.

#### Exercise `∃-even-odd` (practice)

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

```
-- Your code goes here
```

#### Exercise `∃-+-≤` (practice)

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

```
-- Your code goes here
```

## Existentials, Universals, and Negation

Negation of an existential is isomorphic to the universal
of a negation.  Considering that existentials are generalised
disjunction and universals are generalised conjunction, this
result is analogous to the one which tells us that negation
of a disjunction is isomorphic to a conjunction of negations:
```
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from =  λ{ ∀¬xy → refl }
    }
```
In the `to` direction, we are given a value `¬∃xy` of type
`¬ ∃[ x ] B x`, and need to show that given a value
`x` that `¬ B x` follows, in other words, from
a value `y` of type `B x` we can derive false.  Combining
`x` and `y` gives us a value `⟨ x , y ⟩` of type `∃[ x ] B x`,
and applying `¬∃xy` to that yields a contradiction.

In the `from` direction, we are given a value `∀¬xy` of type
`∀ x → ¬ B x`, and need to show that from a value `⟨ x , y ⟩`
of type `∃[ x ] B x` we can derive false.  Applying `∀¬xy`
to `x` gives a value of type `¬ B x`, and applying that to `y` yields
a contradiction.

The two inverse proofs are straightforward, where one direction
requires extensionality.


#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal:
```
postulate
  ∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
    → ∃[ x ] (¬ B x)
      --------------
    → ¬ (∀ x → B x)
```
Does the converse hold? If so, prove; if not, explain why.


## Standard library

Definitions similar to those in this section can be found in the standard
library: 
```
import Data.Product using (_×_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
import Data.Unit using (⊤; tt)
import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
import Data.Empty using (⊥; ⊥-elim)
import Function.Equivalence using (_⇔_)
import Relation.Nullary using (¬_)
import Relation.Nullary.Negation using (contraposition)
```
The standard library constructs pairs with `_,_` whereas we use `⟨_,_⟩`.
The former makes it convenient to build triples or larger tuples from pairs,
permitting `a , b , c` to stand for `(a , (b , c))`.  But it conflicts with
other useful notations, such as `[_,_]` to construct a list of two elements in
the [Lists]({{ site.baseurl }}/Lists/) section
and `Γ , A` to extend environments in
the [DeBruijn]({{ site.baseurl }}/DeBruijn/) section.
The standard library `_⇔_` is similar to ours, but the one in the
standard library is less convenient, since it is parameterised with
respect to an arbitrary notion of equivalence.


## Unicode

This section uses the following Unicode symbols:

    ¬  U+00AC  NOT SIGN (\neg)
    ×  U+00D7  MULTIPLICATION SIGN (\x)
    η  U+03B7  GREEK SMALL LETTER ETA (\eta)
    ⊎  U+228E  MULTISET UNION (\u+)
    ⊤  U+22A4  DOWN TACK (\top)
    ⊥  U+22A5  UP TACK (\bot)
    ≢  U+2262  NOT IDENTICAL TO (\==n)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)

---

*This page is derived from Wadler et al., with additional text and
exercises by Maraist; for more information see the [sources and
authorship]({{ site.baseurl }}/Sources/) page.*
