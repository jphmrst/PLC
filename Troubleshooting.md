---
layout: page
title: Troubleshooting your Agda installation
prev :     /UWL/
permalink: /Troubleshooting/
next :     /Sources/
---

## Recheck your configuration {#recheck}

 1. Make sure you have a local Agda config directory.

     - On *nix systems (linux and Mac), it is `~/.agda`.

     - On Windows, you should have the `AGDA_DIR` environment variable
       set to the path of some directory which does exist.

 2. Make sure there is a file `defaults` in the local Agda config
    directory, and that it contains the line:

        standard-library

 3. Make sure there is a file `libraries` in the local Agda config
    directory, and that it contains the line:

        /PATH/TO/STANDARD/LIBRARY/standard-library.agda-lib

    {::comment}

    If you have installed the textbook sources as a standard library,
    then there should also be a line
    
    {:/comment}

 4. Make sure that

     - The directory `/PATH/TO/STANDARD/LIBRARY` from the previous
       step exists

     - The file `/PATH/TO/STANDARD/LIBRARY/standard-library.agda-lib`
       exists

     - That the latter file contains the lines

           name: standard-library
           include: src

     - That the following files (among many others in that directory)
       all exist:
    
           /PATH/TO/STANDARD/LIBRARY/src/Function.agda
           /PATH/TO/STANDARD/LIBRARY/src/Data/Nat.agda
           /PATH/TO/STANDARD/LIBRARY/src/Codata/Colist/Bisimilarity.agda

If any of these files are missing or are misaligned, then Agda will
either not be able to run, or will not be able to find standard
libraries.

## Google your error messages!

When you get an error message, feed it to Google.  You are not likely
to be the only person ever to have triggered this error!  Of course
you must be thoughtful about grabbing solutions from online --- try to
understand whether the situation (as opposed to just the error) you
find is really the same as your situation, and make sure that they are
applicable to the same platform/version as you are running.

You probably know that, like most faculty, I take plagiarism very
seriously.  However, there is a world of difference between getting
outside help to *install tools*, and getting help to avoid learning
the course material.  This is not a class in installing software!  It
is fine to get help either online or from your colleagues to install
and configure the basic tools we will use.

## Problems installing the standard libraries {#stdlib}

This section applies
 - **After** you have successfully installed Agda, and have
   compiled the `testdefs` example in the ["Installing the core Agda
   system" section]({{ site.baseurl }}/Setup/#core) without error.
 - **Before** you have compiled the `testnats` example in the
   ["Installing the Agda standard libraries" section]({{ site.baseurl
   }}/Setup/#stdlib) without error.

### The `libraries` file contains the wrong directory {#wrong-libraries-dir}

If you are seeing output like this:

    Failed to find source of module Data.Nat in any of the following
    locations:
      /home/jm/Edu/421/agda/Data/Nat.agda
      /home/jm/Edu/421/agda/Data/Nat.lagda
      /home/jm/Lib/deb/agda-stdlib-mock/src/Data/Nat.agda
      /home/jm/Lib/deb/agda-stdlib-mock/src/Data/Nat.lagda
      [Possibly other files here]

Then you may have an incorrect directory in your `libraries` file, or
your Agda environment may be unable to find your `libraries` file.

#### incorrect directory in your `libraries` file

 1. If your `libraries` file contains the line

        /SOME/PATH/standard-library.agda-lib

    then the directory `/SOME/PATH` should look something like this:

        AllNonAsciiChars.hs    HACKING.md	     README.agda
        CHANGELOG/	       Header		     README.md
        CHANGELOG.md	       lib.cabal	     Setup.hs
        dist/		       LICENCE		     src/
        dist-newstyle/	       notes/		     standard-library.agda-lib
        GenerateEverything.hs  publish-listings.sh*  travis/
        GNUmakefile	       README/

    The directory `/SOME/PATH` should **not** contain a subdirectory
    `prim`, or a sibdirectory `Agda`, especially if is they are the
    only thing there!

 2. In Step 1 of [the "Installing the Agda standard libraries"
    section]({{ site.baseurl }}/Setup/#stdlib), you ran these
    commands:

    ```bash
    git clone https://github.com/agda/agda-stdlib.git
    cd agda-stdlib
    git checkout v1.1
    ```

    If you ran these commands from a directory `/WHERE/GIT/RAN`, then
    the contents of the `libraries` file should be
    `/WHERE/GIT/RAN/agda-stdlib/standard-library.agda-lib`.

    The contents of the `libraries` file should **not** be something
    within a `.stack` or similar generated directory.  It should be
    within the actual Git repository which you checked out.

#### Agda unable to find your `libraries` file

If Agda is not able to find the directory containing your `libraries`
and `defaults` files, then it will be unable to read them.

 - On a linux or Mac system, make sure that you have put those files
   in `~/.agda`.  (`~` abbreviates the home directory in *nix
   systems.)

 - If you are on a Windows system, or if you have verified the correct
   directory on a *nix system, then use the `AGDA_DIR` environment
   variable to name this directory.  Make sure that the environment
   variable is set before re-running Emacs or Agda.

---

*This page is by Maraist; for more information see the [sources and
authorship]({{ site.baseurl }}/Sources/) page.*

