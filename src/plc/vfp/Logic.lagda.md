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
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Function using (_∘_)
open import plc.vfp.Induction using (+-comm)
open import plc.vfp.Relations using (_≃_; _⇔_)
open import plc.vfp.DataRel using (_∈_; here; there)
open _⇔_
```


## Conjunction

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
matches, we do not giv it a right-hand side.

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
De Morgan laws, and the disributivity laws.  For example:

```
×-comm : ∀ (A B : Set) → (A × B) ⇔ (B × A)
×-comm AB BA = record
  { to = λ AB×BA → ⟨ proj₂ AB×BA , proj₁ AB×BA ⟩
  ; from = λ BA×AB → ⟨ proj₂ BA×AB , proj₁ BA×AB ⟩
  }
```

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


## More exercises

#### Exercise `⊎-comm` (starting) {#or-comm}

Show that `⊎` is commutative under `⇔`:

```
postulate ⊎-comm : ∀ (A B : Set) → A ⊎ B ⇔ B ⊎ A
-- Remove the "postulate" keyword and add your proof code here
```

#### Exercise `×-assoc` (starting) {#or-assoc}

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

## Standard library

Definitions similar to those in this section can be found in the standard
library: 
```
import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
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
