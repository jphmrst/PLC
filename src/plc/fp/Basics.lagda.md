---
title     : "Basics: Functional Programming in Agda"
layout    : page
prev      : /Preface/
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
\textit{first-class values} — i.e., values that can be passed as
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
second through eighth lines of the definition can be read "Monday is a
day", "Tuesday is a day," and so on.

Having defined the type `Day`, we can write functions that operate on
that type.

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
symbols in _unicode_.  At the end of each chapter is a list of all
unicode symbols introduced in the chapter, including instructions on
how to type them in the Emacs text editor.  Here _type_ refers to
typing with fingers as opposed to data types!

Another thing to notice is that the argument and return types of this
function are explicitly declared.  Some functional programming
languages can work out these types even if they are not given
explicitly — i.e., they perform type inference.  Agda performs some
inference, but we will always include these type _signatures_ for the
functions we write.

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

#### Exercise `next-weekday` (practice) {#next-weekday}

Write a function `nextWeekday` which takes a day, and returns the next
weekday after that day (so skipping past Saturday and Sunday to
Monday).

``
nextWeekday : Day → Day
nextWeekday d = ?
``

When working exercises by filling out the source code in the book, you
will notice that the template code for the exercises is formatted
slightly differently than (for example) the definitions of `Day` and
`nextDay` above.  Up there, the code blocks are surrounded by lines
containing **three** backticks `` ` ``, but here the code is
surrounded by lines containing only two backticks.  In order make Agda
pay attention to your implementation of `nextWeekday`, you must add
the third backticks to those delimiters.

### Booleans

In a similar way, we can define the type `Bool` of booleans, with
members `true` and `false`.

```
data Bool : Set where
  True  : Bool
  False : Bool
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
not True  = False
not False = True

and : Bool → Bool → Bool
and True t  = t
and False _ = False

or : Bool → Bool → Bool
or True _  = True
or False t = t 
```

It is useful for us to see how we can define the boolean type and its
basic operations.  But in later chapters, we will use the boolean type
defined in Agda's standard library rather than defining them
ourselves.  So at the start of these files, you will often see the
declaration

    open import Data.Bool

#### Exercise `nand` (practice) {#nand}

Define the following function to represent the `nand` logic operator,
given by the following truth table:

  | `A`   | `B`   | `nand A B` |
  | ---   | ---   | ---------- |
  | False | False | True       |
  |False | True | True| 
  |True |False  |True| 
  |True |True  |False|

``
nand : Bool → Bool → Bool
nand a b = ?
``

#### Exercise `and3` (practice) {#and3}

Implement the `and3` function that returns the conjunction of three
boolean values.

``
and3 : Bool → Bool → Bool → Bool
and3 a b c = ?
``

## Unicode

This chapter uses the following unicode:

    →  U+2192  RIGHTWARDS ARROW (\to, \r, \->)

Each line consists of the Unicode character (`→`), the corresponding
code point (`U+2192), the name of the character (`RIGHTWARDS ARROW`),
and the sequence to type into Emacs to generate the character (`\->`).

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
al., with some short exceprts from Wadler et al.; for more information
see the [sources and authorship]({{ site.baseurl }}/Sources/) page.*
