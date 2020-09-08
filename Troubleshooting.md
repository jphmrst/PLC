---
layout: page
title: Troubleshooting your Agda installation
prev :     /UWL/
permalink: /Troubleshooting/
next :     /Sources/
---

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

Then you have an incorrect directory in your `libraries` file.

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

---

*This page is by Maraist; for more information see the [sources and
authorship]({{ site.baseurl }}/Sources/) page.*

