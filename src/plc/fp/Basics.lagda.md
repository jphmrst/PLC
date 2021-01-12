---
title     : "Basics: Functional Programming in Agda"
layout    : page
prev      : /Sources/
permalink : /Basics/
next      : /Naturals/
---

```
module plc.fp.Basics where
```

The functional programming style brings programming closer to
mathematics: If a procedure or method has no side effects, then pretty
much all you need to understand about it is how it maps inputs to
outputs — that is, you can think of its behavior as just computing a
mathematical function. This is one reason for the word "functional" in
"functional programming." This direct connection between programs and
simple mathematical objects supports both sound informal reasoning and
formal proofs of correctness.

The other sense in which functional programming is "functional" is
that it emphasizes the use of functions (or methods) as
_first-class values_ — i.e., values that can be passed as
arguments to other functions, returned as results, stored in data
structures, etc. The recognition that functions can be treated as data
in this way enables a host of useful idioms, as we will see.  Other
common features of functional languages include _algebraic data
types_ and _pattern matching_, which make it easy to construct
and manipulate rich data structures, and sophisticated
_polymorphic type systems_ that support abstraction and code
reuse. Agda shares all of these features.

## Enumerated types

One unusual aspect of Agda is that its set of built-in features is
extremely small. For example, instead of providing the usual palette
of atomic data types (booleans, integers, strings, etc.), Agda offers
an extremely powerful mechanism for defining new data types from
scratch — so powerful that all these familiar types arise as
instances.

Agda has a standard library that comes with definitions of booleans,
numbers, and many common data structures like lists. But there is
nothing magic or primitive about these library definitions: they are
ordinary user code.  To see how this works, let's start with a very
simple example.

### Days of the week

The following declaration tells Agda that we are defining a new set of
data values — a type.

```
data Day : Set where
  Monday    : Day
  Tuesday   : Day
  Wednesday : Day
  Thursday  : Day
  Friday    : Day
  Saturday  : Day
  Sunday    : Day
```

The type is called Day, and its members are Monday, Tuesday, etc. The
second line of the definition can be read "Monday is a day;" the third
line can be read "Tuesday is a day;" and so on.

Having defined the type `Day`, we can do several things with the
definition.  We can write a definition of a name which uses the values
we define:

```
myFavoriteDay : Day
myFavoriteDay = Saturday

```

We can also write functions that operate on that type.

```
nextDay : Day → Day
nextDay Monday    = Tuesday
nextDay Tuesday   = Wednesday
nextDay Wednesday = Thursday
nextDay Thursday  = Friday
nextDay Friday    = Saturday
nextDay Saturday  = Sunday
nextDay Sunday    = Monday
```

You may have noticed that `→` does not appear on your keyboard.  It is
a _unicode_ symbol.  At the end of each section is a list of all
unicode symbols introduced in that section including instructions on
how to type them in the Emacs text editor.  Here _type_ refers to
typing with fingers as opposed to data types!

Another thing to notice is that the argument and return types of this
function, like the type of the name `yFavriteDay`, are explicitly
declared.  Some functional programming languages can work out these
types even if they are not given explicitly — i.e., they perform type
inference.  Agda performs some inference, but we will always include
these type _signatures_ for the functions we write.  The type
signature for this function tells us that `nextDay` transforms a value
of type `Day` into a (possibly different, possibly the same) value of
type `Day`.

This function definition may look strange at first.  It is as if we
are defining the function seven times!  What we are actually doing is
telling Agda the different _cases_ that it might find when `nextDay`
is run.  This is a different style than in languages like Java or C,
where we make a single function definition, within which we would use
a statement like `switch`.  This style which we find in Agda is the
_pattern matching_ style, where we give a different clause for each of
the different combinations of patterns.  A `Day` value can take one of
seven forms, so we give seven different clauses, one for each form.
We will soon learn techniques which allow us to give fewer clauses
when different cases have overlaping results.

One very important thing to note is that Agda expects all of its
functions to be _total_, that is, to have a well-defined result for
all possible arguments.  The reason for this restriction has to do
with the use of Agda as a tool for logical reasoning — we will discuss
both the ideas behind why this restriction exists, and how we account
for failing cases in programs, in later sections.  For now, we must
simply be aware that Agda will refuse to compile a function which does
not satisfy totality.

Once we have defined a name or a function, we can use it in subsequent
definitions.

```
threeDaysAfterMyFavoriteDay : Day
threeDaysAfterMyFavoriteDay = nextDay (nextDay (nextDay myFavoriteDay))
```

Here is another function on `Day` values:

```
sameDay : Day → Day
sameDay d = d
```

Instead of matching the first argument to different cases, we instead
_name_ the argument, and refer to that name in the result.  Of course
you are used to naming function (or method) arguments!  In Agda, we
can also view naming the argument as one way in which we refer to many
forms of a value all at once.

#### Exercise `try-days` (starting) {#try-days}

Having defined a function, we should check that it works on some
examples.  This exercise will help you step through the use of
`agda-mode` to examine and evaluate expressions.  When we load a
source file into an Agda process, we can use the constructors, values,
and other names which that file defines.

 - First, open this source file `Basics.lagda.md` in Emacs, and load
   it into an Agda process with `C-c C-l`.

 - Next, type `C-c C-n`.  Emacs will ask for an expression; try
   entering `nextDay (nextDay Tuesday)`, and press the Enter key.

 - Emacs will display the result of simplifying this expression in a
   new-subwindow.

There is a similar tool for _typechecking_: when we give an expression
to `C-c C-d`, Agda will tell us the type of the expression.  Checking
the type can be useful for figuring out how we can use some expression
which we may not yet fully understand.

Expression typechecking and evaluation with `C-c C-d` and `C-c C-n`
will be a regular tool for you as we encounter new definitions.  Both
here and for the definitions we encounter later, take the time to
experiment with evaluating different expressions to make sure that you
understand all of the definitions we will encounter.

#### Exercise `exploreNontotal` (starting) {#exploreNontotal}

What error does Agda give when we define a function which is not
total?  Delete one of the clauses from `nextDay` to see how the system
reacts when you reload the file.

#### Exercise `nextWeekday` (recommended) {#nextWeekday}

Write a function `nextWeekday` which takes a day, and returns the next
weekday after that day (so skipping past Saturday and Sunday to
Monday).

    nextWeekday : Day → Day
    nextWeekday d = ?

When working exercises by filling out the source code in the book, you
will notice that the template code for the exercises is formatted
slightly differently than (for example) the definitions of `Day` and
`nextDay` above.  Up there, the code blocks are surrounded by lines
containing **three** backticks `` ` ``, but here the code is indented
instead.  In order make Agda pay attention to your implementation of
`nextWeekday`, you must both remove the indentation, and add the three
backticks before and after the code.  The indented code is simply
taken as another comment like the rest of this text.  The backticks
surround actual Agda code.

#### Exercise `monthsAndSeasons` (recommended) {#monthsAndSeasons}

Write a data type `Month` with twelve constructors, one for each
month.  Write a function `monthSeason` which maps a month to its
season,

    data Season : Set where
      winter : Season
      spring : Season
      summer : Season
      fall : Season

{::options parse_block_html="true" /}
<div style="background-color: #f0fff0; padding: 1em 1.5em 0.5em; margin-bottom: 1em">

### Booleans

In a similar way, we can define the type `Bool` of booleans, with
members `true` and `false`.

```
data Bool : Set where
  true  : Bool
  false : Bool
```

Although we are rolling our own booleans here for the sake of seeing
how to build everything from scratch, Agda does, of course, provide a
default implementation of the booleans in its standard library,
together with a multitude of useful functions.  Whenever possible,
we'll name our own definitions so that they exactly coincide with the
ones in the standard library.

Functions over booleans can be defined in the same way as above:

```
not : Bool → Bool
not true  = false
not false = true

_∧_ : Bool → Bool → Bool
true ∧ t  = t
false ∧ _ = false

_∨_ : Bool → Bool → Bool
true ∨ _  = true
false ∨ t = t 
```

There are a few uses of the underscore character `_` in these
definitions.  The underscore is a special character in Agda, and we
use it in two different ways here.  In the line

    _∧_ : Bool → Bool → Bool

the underscores help us to define `∧` as an _infix_ operator, that is,
a function which we write in between its arguments instead of before
its arguments.  When we use the underscore in a declaration line, it
tells Agda where to find the arguments to the operator function we are
defining.

The second way that we use the underscore is in a line like

    true ∨ _  = true

Here the underscore represents an argument which we choose not to
name.  We choose not to give a name to the second argument in this
clause because we do not use it: if the first argument to `∨` is
`true`, then the result is `true` *no matter what* the second argument
is — we do not refer to the second argument at all in calculating the
result in this case.  Since we do not use the argument, we prefer not
to bother giving it a name.  This anonymity simplifies the definition,
and it makes it more immediately clear to the reader that the argument
is unused in this case.  This use of an underscore in the pattern of
an argument is called a _wildcard pattern_.  Wildcards are one way in
which we can avoid spelling out different cases when they make no
difference to the result: we do not need to divide this clause into
separate clauses for each value of the second argument, when there is
no difference to the result.

{::options parse_block_html="true" /}
<div style="background-color: #f0fff0; padding: 1em 1.5em 0.5em; margin-bottom: 1em">

### Remember! {#underscore-summary}

The underscore is a special character in Agda with multiple uses.

 - As a parameter by itself, it denotes a value which we will not use,
   and do not name.

 - As part of the name in a signature, it shows where the arguments
   can go when an operator is written in between its argument.

Do not try to use an underscore in your function or argument names.

</div>


#### Imports

It is useful for us to see how we can define the boolean type and its
basic operations.  But later we will use the boolean type
defined in Agda's standard library rather than defining them
ourselves.  So at the start of these files, you will often see the
declaration

    open import Data.Bool

Shortly we will want to write some equations that hold between terms
involving boolean values.  To support doing so, we import Agda's
definition of the equality relation and a way to give evidence for it
from the Agda standard library:

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
```

The first line brings the standard library module that defines
equality into scope and gives it the name `Eq`. The second line
opens that module, that is, adds all the names specified in the
`using` clause into the current scope. In this case the names added
are `_≡_`, the equality operator, and `refl`, the name for evidence
that two terms are equal.

Agda uses underbars to indicate where terms appear in infix or mixfix
operators. So `_≡_` is an infix operator.  We will see more kinds of
operators in later sections.  Parentheses and semicolons are among the
few characters that cannot appear in names, so we do not need the
extra spaces that we have in the `using` list.

#### Exercise `nand` (recommended) {#nand}

Define the following function to represent the `nand` logic operator,
given by the following truth table:

  | `A`   | `B`   | `nand A B` |
  |:-----:|:-----:|:----------:|
  | false | false | true       |
  | false | true  | true       | 
  | true  | false | true       |
  | true  | true  | false      |

    nand : Bool → Bool → Bool
    nand a b = ?

Try to give as few clauses as you can in your definition.  You could
just directly translate the lines of the table into clauses with a
specific pattern for each argument.  But instead, can you combine the
first two lines into one clause using a wildcard?  Can you combine the
last two lines into one clause by naming the argument, and using a
call to a different function which we have already defined?  Try all
of these variations to convince yourself that they are all possible
ways to correctly define `nand`.

#### Exercise `and3` (practice) {#and3}

Implement the `and3` function that returns the conjunction of three
boolean values.

    and3 : Bool → Bool → Bool → Bool
    and3 a b c = ?

    _ : and3 true true true ≡ true
    _ = refl

    _ : and3 true true false ≡ false
    _ = refl

    _ : and3 true false false ≡ false
    _ = refl

    _ : and3 false false false ≡ false
    _ = refl

The two uses of `refl` above tell Agda can it can use evaluation to
show that the two expressions on either side of the `≡` actually are
equal.  We are using `refl` to write _unit tests_, tests for a
function each using a specific given example.

{::options parse_block_html="true" /}
<div style="background-color: #f0fff0; padding: 1em 1.5em 0.5em; margin-bottom: 1em">

### Remember! {#boolean-summary}

Agda uses different symbols for boolean operators than what many other
languages use.  They use Unicode symbols, and are traditional symbols
for these operations.

</div>

## Standard library

At the end of each section, we will show where in the standard library
to find definitions relevant to the program we write in that section.
The booleans, their constructors, and basic operators upon them are
defined in the standard library module `Data.Bool`:

```
-- import Data.Bool using (Bool, true, false, if_then_else_)
```

Normally, we will show an import as running code, so Agda will
complain if we attempt to import a definition that is not available.
This time, since we are defining the booleans manually, we have only
shown the import as a comment.

### Strings and characters

In addition to boolean values, Agda also has string and character
values built in (and numbers as well, which we study in the next
section).  The type of stirngs is `String`, and we can use them in
our programs with

```
open import Data.String
```

Aside from the functions which the module provides, we must import
those libraries in order to use the usual quotation mechanisms for
writing down string data.

```
myName : String
myName = "John Jacob Jingleheimer Schmidt"
```

The library provides several of the usual string utilities, such as:

 - `++`, written between two arguments, concatenating two strings.
   Use `C-c C-n` to evaluate

       "hello" ++ " there"

 - `==`, written between two arguments, returning `true` (in the
   standard library's implementation of `Bool`) if its arguments are
   the same string.

       "hello" == "hello"
       "hello" == "hi"

The type of characters is `Char`, and we import them with

```
open import Data.Char hiding (isLower)

myInitial : Char
myInitial = 'J'
```

This library also provides several functions on characters

 - Testing for certain character classes with `isLower`, `isDigit`,
   `isAlpha`, `isSpace`, `isAscii`, `isLatin1`, `isPrint`,
   `isHexDigit`.  Since the exercise below is to write `isLower`, we
   use the `hiding` clause above to suppress loading it.

 - Transforming one character to a related character with `toUpper`,
   `toLower`.

#### Exercise `isLower` (practice) {#isLower}

Implement the `isLower` function that returns `true` when its argument
is a lower-case letter, and returns `false` otherwise.

    isLower : Char → Bool
    isLower c = ?

    _ : isLower 'c' ≡ true
    _ = refl

    _ : isLower 'C' ≡ false
    _ = refl

Write your own version of `isLower`, without using the one in the
standard library.

### Remember! {#basics-summary}

 - In functional programming, we describe computation as a mapping
   from inputs to outputs.  There are no side-effects, or variables
   whose values can be rebound within one call to a function.

 - We can define our own data types which may have different,
   alternative forms.  The different forms each have their own
   _constructors_.  

 - Functions consist of a _signature_ followed by one or more
   _defining clauses_.

 - We can give multiple defining clauses to correspond to different
   cases of possible argument values.  One way to distinguish the
   cases is by the constructors used to create an argument value.

 - Agda functions must be _total_, so the defining clauses must
   address any possible combination of inputs.

 - Agda's type for boolean values is defined using this `data`
   declaration.  Its two constructors are `true` and `false`.

</div>


## Unicode

This section uses the following Unicode symbols:

    →  U+2192  RIGHTWARDS ARROW (\to, \r, \->)
    ∧  U_2227  LOCIGAL AND (\and)
    ∨  U+2228  LOGICAL OR (\or)
    ≡  U+2261  IDENTICAL TO (\==)

Each line consists of the Unicode character (`→`), the corresponding
code point (`U+2192`), the name of the character (`RIGHTWARDS ARROW`),
and the sequence to type into Emacs to generate the character (`\->`).
If we forget a character which we use in a section, and leave it out
of the table, please let us know!

For a full list of supported characters, use
`agda-input-show-translations` with:

    M-x agda-input-show-translations

All the characters supported by `agda-mode` are shown. We write M-x to
stand for typing `ESC` followed by `x`.

If you want to know how you input a specific Unicode character in an
agda file, move the cursor onto the character and use `quail-show-key`
with:

    M-x quail-show-key

You'll see a key sequence of the character in the minibuffer at the
bottom of your Emacs window.  If you run `M-x quail-show-key` on (for
example) `∸`, you will see `\.-` for the character.

---

*This page is derived from Geraldo Ribeiro's translation of Pierce et
al., with some short exceprts from Wadler et al..  Exercise
monthsAndSeasons is adapted from Thompson.  For more information see
the [sources and authorship]({{ site.baseurl }}/Sources/) page.*
