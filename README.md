---
layout: page
title: Installing and configuring your Agda environment
prev :     /Intro/
permalink: /Setup/
next :     /Sources/
---

<!-- Links -->

[coursepackURL]: http://plfa.inf.ed.ac.uk
[coursepack-dev]: https://github.com/jphmrst/plfa.github.io/archive/dev.zip

[plfa]: http://plfa.inf.ed.ac.uk
[plfa-dev]: https://github.com/plfa/plfa.github.io/archive/dev.zip
[plfa-status]: https://travis-ci.org/plfa/plfa.github.io.svg?branch=dev
[plfa-travis]: https://travis-ci.org/plfa/plfa.github.io
[plfa-master]: https://github.com/plfa/plfa.github.io/archive/master.zip

[agda]: https://github.com/agda/agda/releases/tag/v2.6.0.1
[agda-version]: https://img.shields.io/badge/agda-v2.6.0.1-blue.svg
[agda-docs-emacs-mode]: https://agda.readthedocs.io/en/v2.6.0.1/tools/emacs-mode.html
[agda-docs-emacs-notation]: https://agda.readthedocs.io/en/v2.6.0.1/tools/emacs-mode.html#notation-for-key-combinations
[agda-docs-package-system]: https://agda.readthedocs.io/en/v2.6.0.1/tools/package-system.html#example-using-the-standard-library

[agda-stdlib-version]: https://img.shields.io/badge/agda--stdlib-v1.1-blue.svg
[agda-stdlib]: https://github.com/agda/agda-stdlib/releases/tag/v1.1

[haskell-stack]:  https://docs.haskellstack.org/en/stable/README/
[haskell-ghc]: https://www.haskell.org/ghc/
[haskell-windows]: https://www.haskell.org/platform/windows.html

[gnuemacsDownload]: https://www.gnu.org/software/emacs/download.html

[mononoki]: https://madmalik.github.io/mononoki/

[ruby]: https://www.ruby-lang.org/en/documentation/installation/
[ruby-bundler]: https://bundler.io/#getting-started
[ruby-jekyll]: https://jekyllrb.com/
[ruby-html-proofer]: https://github.com/gjtorikian/html-proofer

[kramdown]: https://kramdown.gettalong.org/syntax.html
[pandoc]: https://pandoc.org/installing.html
[epubcheck]: https://github.com/w3c/epubcheck


<!-- Status & Version Badges -->

[![Build Status][plfa-status]][plfa-travis]
[![Agda][agda-version]][agda]
[![agda-stdlib][agda-stdlib-version]][agda-stdlib]

You can read [the online version of the course pack][coursepackURL]
without installing anything.  However, to interact with the code and
complete the exercises, you need several things:

  - [Agda][agda], which needs several other software systems
  - The [Agda standard library][agda-stdlib]
  - [The source code version of the course pack][coursepack-dev]

The course pack source is tested against specific versions of Agda and
the standard library, which are shown in the badges above.  There are
several versions of Agda and its standard library online.  If you are
using a Mac or linux repository system (like brew or Debian apt), then
the version of Agda which the repository holds may be out-of-date for
what the course pack expects.  Agda is under active development, so if
you install the development version of Agda from its GitHub
repository, you may find that the developers have introduced changes
which break the code in the course pack.  So it is important to have
the specific versions of Agda and its libraries shown above.

You will also need an editor for writing and changing Agda source
code.  Agda's best IDE is in Emacs, and we include steps below or
installing Emacs, familiarizing yourself with its basic editing
features, and with its Agda mode.

# On Macs, install the [Xcode Developer Tools](https://developer.apple.com/xcode/)

Include at least the Developer Tools Essentials and UNIX Development
Support modules.

# Installing the Haskell Tool Stack

Agda is built against the [Haskell Tool Stack][haskell-stack], and
outputs code for the GHC compiler, so as a preliminary step you will
need to install these systems.

 1. **Installing Stack.**

    - *On Unix systems (including linux and Macs)*.  Your repository
       probably offers Stack as a pre-packaged software, and this
       option is probably the easiest.  Alternatively, there are
       instructions for downloading and running a shell script on the
       [Stack site][haskell-stack].

      Once you have Stack installed, make sure you include its binary
      installation area in your `PATH` by including a line like
      ```bash
      export PATH=${HOME}/.local/bin:${PATH}
      ```
      in your `${HOME}/.bashrc` or `${HOME}/.profile` file.

    - *On Windows*.  There is a 64-bit Windows installer on the [Stack
       site][haskell-stack].

 2. **Updating Stack.** Stack is able to update itself.  So after you
    install it, run the command
    ```bash
    stack upgrade
    ```

# Installing GHC and Cabal

These systems are used for installing Agda, and for its runtme
environment.  

 - *With Unix repository systems*.  Again, your repository is
    probably the easiest option; an exact version for these more
    stable systems is less of an issue than with Agda itself.  On
    Debian, for example, the necessary packages are
    ```bash
    sudo apt-get install ghc cabal-install
    ```
    and packages `ghc-doc` and `haskell-mode` are also nice to
    have.

 - *On Windows*.  See the [Haskell Platform site][haskell-windows].

# Install Git

You will need Git to access the specific version of Agda we use.  If
you do not already have Git installed on your system, see the [git
downloads page](https://git-scm.com/downloads).

# Installing Agda and its standard libraries

To install the specific version of Agda we need, we will first
download that version, and then ask Stack to install it for us.

 1. *Downloading Agda*.  If you have installed Git, you can fetch a copy
    of Agda with:
    ```bash
    git clone https://github.com/agda/agda.git
    cd agda
    git checkout v2.6.0.1
    ```

    Alternatively, you can download a ZIP archive of that version from
    [the GitHub site][agda].

 2. *Base Agda installation.*  From the Agda source directory, run:

    ```bash
    stack install --stack-yaml stack-8.6.5.yaml
    ```

    **This step will take a while to complete.** Moreover, if your
    system is old or fragile, then your best results may come from
    exiting other programs and leaving it alone to complete.

 3. *Downloading the standard libraries* is similar to downloading
    Agda itself:
    ```bash
    git clone https://github.com/agda/agda-stdlib.git
    cd agda-stdlib
    git checkout v1.1
    ```

    Again, it is possible as an alternative to download a ZIP archive
    of that version from [the library GitHub site][agda-stdlib].

 4. *Let Agda know where to find the standard libraries.* Follow the
    instructions [here][agda-docs-package-system] to set up your
    `.agda` drectory.

 5. *Update Agda for output binaries.* 
    ```bash
    cabal v2-repl --build-dep fail
    cabal v2-install --lib Agda ieee754 -v
    ```

    **The second command will take a while to complete.** Moreover, if
    your system is old or fragile, then your best results may come
    from exiting other programs and leaving it alone to complete.

*Verifying the Agda installation.* When you finish those five numbered
steps, you should be able to compile and run a Hello World program:

 - Create a new directory, and save the following lines as the file
   `hello-world.agda`:
   ```
   module hello-world where
   open import IO
   main = run (putStrLn "Hello, World!")
   ```

 - From that directory, run the command
   ```bash
   agda --compile hello-world.agda
   ```

   The first time you run this command, it will need to compile many
   library files.  Note also that it will generate a directory
   `MAlonzo`, which you can ignore.

 - You should then see an executable file `hello-world`, which you can
   run for a nice message.

# Installing the Course Pack sources

You can get the latest version of the Course Pack sources from GitHub,
either by cloning the repository, or by downloading [the zip
archive][coursepack-dev]:

```bash
git clone https://github.com/jphmrst/plfa.github.io.git
```

It is possible to set up the Course Pack sources as an Agda library as
well.  If you want to complete the exercises found in the `courses`
folder, or to import modules from the book, you need to do this.  To
do so, add the path to `plfa.agda-lib` to `~/.agda/libraries` and add
`plfa` to `~/.agda/defaults`, both on lines of their own.

# Install Emacs, and familiarize yourself with it

Emacs is a text editor which offers a good IDE for Agda.

To install Emacs:

 - *On linux systems*, the version of GNU Emacs in your repository is
    probably fine as long as it is fairly recent.  There are also
    links to the most recent release on the [GNU Emacs downloads
    page][gnuemacsDownload].

 - *On MacOS*, [Aquamacs](http://aquamacs.org/) is the generally
    preferred version of Emacs; the Agda wiki notes that people have
    had success with agda-mode on Aquamacs.

 - *On Windows*.  See the [GNU Emacs downloads page][gnuemacsDownload]
    for instructions.

Make sure that you are able to open, edit, and save text files with
your installation.  The [tour of
Emacs](https://www.gnu.org/software/emacs/tour/) page on the GNU Emacs
site describes how to access the tutorial within your Emacs
installation.

# Install and configure agda-mode

The recommended editor for Agda is Emacs with `agda-mode`. Agda ships
with `agda-mode`, so if you’ve installed Agda, all you have to do to
configure `agda-mode` is run:

```bash
agda-mode setup
agda-mode compile
```

If you are already an Emacs user, you may want to note the
configuration which the `setup` appends to your `.emacs` file, and
integrate it with your own preferred setup.

*Verifying agda-mode*.  Open the `hello-world.agda` file which you set
 up earlier.

 - To load and type-check the file, use
   [`C-c C-l`][agda-docs-emacs-notation].

 - To compile the file and generate the executable, use `C-c C-x C-c`.
   This will not actually run the executable file, but you can run it
   yourself from the command line.

*Auto-loading `agda-mode` in Emacs.* Since version 2.6.0, Agda has had
support for literate editing with Markdown, using the `.lagda.md`
extension.  One issue is that Emacs will default to Markdown editing
mode for files with a `.md` suffix.  In order to have `agda-mode`
automatically loaded whenever you open a file ending with `.agda` or
`.lagda.md`, all the following line to your Emacs configuration file:

```elisp
(setq auto-mode-alist
   (append
     '(("\\.agda\\'" . agda2-mode)
       ("\\.lagda.md\\'" . agda2-mode))
     auto-mode-alist))
```

If you already have settings to `auto-mode-alist` in your
configuration, put these *after* the ones you already have (or combine
them, if you are comfortable with Emacs Lisp).  The configuration file
for Emacs is normally located in `~/.emacs` or `~/.emacs.d/init.el`,
but Aquamacs users might need to move their startup settings to the
`Preferences.el` file in `~/Library/Preferences/Aquamacs
Emacs/Preferences`.

# Using mononoki in Emacs

Agda uses Unicode characters for many key symbols, and it is important
that the font which you use to view and edit Agda programs shows these
symbols correctly.  So we recommend that you install the font
[mononoki][mononoki] and direct Emacs to use it.

 1. *Installing mononoki*.  You can install directly from a download
    from [mononoki's GitHub][mononoki], but it may be easier if your
    system repository provided a pre-packaged version.  For example,
    on Debian `apt` there is a package `fonts-mononoki`.

 2. *Using mononoki from Emacs*.  Add the following to the end of your
    emacs configuration file `~/.emacs`:

    ``` elisp
    ;; default to mononoki
    (set-face-attribute 'default nil
    		        :family "mononoki"
    		        :height 120
    		        :weight 'normal
    		        :width  'normal)
    ```

# Entering Unicode characters in Emacs `agda-mode`

When you write agda code, you will need to insert characters which are
not found on standard keyboards.  Emacs `agda-mode` makes it easier to
do this by defining character translations: when you enter certain
sequences of ordinary characters (the kind you find on any keyboard),
Emacs will replace them in your Agda file with the corresponding
special character.

For example, we can add a comment line to our `hello-world.agda` file.
Let's say we want to add a comment line that reads

```
{- I am excited to type ∀ and → and ≤ and ≡ !! -}
```

 - The first few characters are ordinary, so we would just type them as usual

   ```
   {- I am excited to type 
   ```

 - But after that last space, we do not find ∀ on the keyboard.  The
   code for this character is the four characters `\all` --- so we
   type those four characters, and when we finish, Emacs will replace
   them with what we want


   ```
   {- I am excited to type ∀
   ```

 - We can continue with the codes for the other characters.  Sometimes
   the characters will change as we type them, because a prefix of our
   character's code is the code of another character.  This happens
   with the arrow, whose code is `\->`.  After typing `\-` we see

   ```
   {- I am excited to type ∀ and ­
   ```

   because the code `\->` corresponds to a hyphen of a certain width.
   When we add the `>`, the `­` becomes `→`.

 - The code for `≤` is `\<=`, and the code for `≡` is `\==`.
 
   ```
   {- I am excited to type ∀ and → and ≤ and ≡
   ```

 - Finally the last few characters are ordinary again,
 
   ```
   {- I am excited to type ∀ and → and ≤ and ≡ !! -}
   ```

The end of each page of the course pack should provide a list of the
Unicode characters introduced on that page.

Emacs and `agda-mode` have a number of commands which can help you
when you solve exercises:

 - For a full list of supported characters, use
   `agda-input-show-translations` with:

      M-x agda-input-show-translations

   All the supported characters in `agda-mode` are shown.

 - If you want to know how you input a specific Unicode character in
   agda file, move the cursor onto the character and type the
   following command:

      M-x quail-show-key

   You'll see the key sequence of the character in mini buffer.

## Appendix: about `agda-mode`

Agda is edited “interactively, which means that one can type check code which is not yet complete: if a question mark (?) is used as a placeholder for an expression, and the buffer is then checked, Agda will replace the question mark with a “hole” which can be filled in later. One can also do various other things in the context of a hole: listing the context, inferring the type of an expression, and even evaluating an open term which mentions variables bound in the surrounding context.”

Agda is edited interactively, using “holes”, which are bits of the program that are not yet filled in. If you use a question mark as an expression, and load the buffer using `C-c C-l`, Agda replaces the question mark with a hole. There are several things you can to while the cursor is in a hole:

    C-c C-c x    split on variable x
    C-c C-space  fill in hole
    C-c C-r      refine with constructor
    C-c C-a      automatically fill in hole
    C-c C-,      goal type and context
    C-c C-.      goal type, context, and inferred type

See [the emacs-mode docs][agda-docs-emacs-mode] for more details.

If you want to see messages beside rather than below your Agda code, you can do the following:

  - Open your Agda file, and load it using `C-c C-l`;
  - type `C-x 1` to get only your Agda file showing;
  - type `C-x 3` to split the window horizontally;
  - move your cursor to the right-hand half of your frame;
  - type `C-x b` and switch to the buffer called “Agda information”.

Now, error messages from Agda will appear next to your file, rather than squished beneath it.

---

*This page is derived from Wadler et al.; for more information see the [sources and authorship]({{ site.baseurl }}/Sources/) page.*
