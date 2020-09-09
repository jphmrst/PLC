---
layout: page
title: Accessing and configuring Agda on UWL machines
prev :     /Setup/
permalink: /UWL/
next :     /Troubleshooting/
---

This page contains information about three ways of using Agda on UWL
machines, instead of installing it on your own machine.

 1. [ITS general-access Windows PCs](#ITSPC)
 2. [The ITS Windows Virtual Desktop](#ITSVIRT)
 3. [CS lab macs](#CSMAC)
     - [Remote access to the CS lab Macs](#CSREMOTE)

## ITS general-access Windows PCs {#ITSPC}

Agda and Emacs are installed on general-access ITS Windows machines,
such as the ones in the library.  It is installed on some classroom
podium computers, but not on most of them.

To use the Agda on ITS Windows PCs, you must still perform some
configuration within your account to fetch the the standard libraries,
and point Agda to them.  The links in this list of tasks point to
sections of the [Getting started]({{ site.baseurl }}/Setup/) page which you will need to do.

 - The ITS Wondows PC setup takes care of the first tasks up to and
   including the "Installing the core Agda system" section.  So you
   should start with the *Verifying the base Agda system* paragraph
   [in that "Installing the core Agda system" section]({{ site.baseurl
   }}/Setup/#core).  Use the "Emacs for Agda" entry in the menu of
   programs to open an editing window, open a new file in some
   directory of yours, paste in the program shown, and press `C-c C-l`
   (that's an abbreviation for pressing first control+c, and then
   control+l).

 - Next take the steps in the ["Installing the Agda standard
   libraries" section]({{ site.baseurl }}/Setup/#stdlib), making sure
   that the directories match exactly as shown.  Don't forget to check
   the `testnats` program, but do check it via Emacs rather than the
   command line.

 - Set up the textbook files as described in the ["Installing this
   book's sources" section]({{ site.baseurl }}/Setup/#pack) section.

 - Skip the Emacs and agda-mode setup, but do not skip the Emacs
   customizations and overviews.
 
## The ITS Windows Virtual Desktop {#ITSVIRT}

**I have not yet tried the remote desktop steps myself.  Please report
successes/failures so that I can update these notes as needed.**

The ITS Windows Virtual Desktop offers almost the same software (and
changes) that the library computers do, and includes Agda. The Virtual
Desktop can be accessed at
[virtual.uwlax.edu](https://virtual.uwlax.edu/).

ITS recommends installing the VMware Horizon client for the best
experience.  However, if your system does not allow the client, then
you can use the HTML access which uses a standard web browser.

You should then use the General Desktop which launches the Windows
computer.  Log in with your NetID (without the `@uwlax.edu` part of
your full email address) and password (it does not require DUO).

**Important note about the Virtual Desktop.** The Virtual Desktop is a
_non-persistent_ computer.  This means that when you log off, the
computer is deleted and re-created - and any files you create will be
gone!  Regularly save your files to your student network drive, to
Google Drive, to OneDrive, or (if you are using the VMware Horizon
client) to your local personal computer.  ITS will **not** be able to
restore files lost when exiting the Virtual Desktop; they do **not**
back them up.

## CS lab macs {#CSMAC}

This installation is in progress, and this section will be updated
with instructions when it is ready.

### Remote access to the CS lab Macs {#CSREMOTE}

Information forthcoming.

---

*This page is edited by Maraist with contributions from [Justin
 Bolstad](https://www.uwlax.edu/profile/jbolstad/); for further
 information see the [sources and authorship]({{ site.baseurl
 }}/Sources/) page.*
