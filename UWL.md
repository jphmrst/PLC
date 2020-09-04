---
layout: page
title: Accessing and configuring Agda on UWL machines
prev :     /Setup/
permalink: /UWL/
next :     /Sources/
---

This page contains information about using Agda on UWL machines,
instead of installing it on your own machine.

## ITS general-access Windows PCs

**This installation is in progress, and may not work yet.  This
section will be updated with additional details when everything is
working.**

 Agda and Emacs are installed on general-access ITS Windows machines,
 such as the ones in the library.  It is installed on some classroom
 podium computers, not not on most of them.

 To use the Agda on ITS Windows PCs, you must still configure your
 account's localization files to point Agda to the standard libraries.
 (This is Step 2 of section *Installing the Agda standard libraries*
 on the [Getting started]({{ site.baseurl }}/Setup/) page.)  The steps
 are:

  1. Set the `AGDA_DIR` environment variable.

      - Click on the "This PC" icon on the desktop.

      - Select the "Computer" item from the menubar at the top of
        the window.

      - Select "System properties" from the menu.

      - Enter the word `environment` into the search bar near the
        upper-left corner of the window.

      - Select "Edit the environment variables from your account"
        from the options which pop up.

      - A separate window called "Environment variables" will open.
        Sometimes this window will appear behind the "System
        properties" window, so look for it there if nothing seems to
        happen.

      - Check to see if the variable `AGDA_DIR` already exists.  If
        it does, use the `Edit...` button to set it value; if it
        does not, use the `New...` button to create it.  Its value
        should be `C:\Users\USERNAME\Documents\agda-config`,
        replacing `USERNAME` with your actual login name (omitting
        the `@uwlax.edu` part).

  2. Now actually create the `C:\Users\USERNAME\Documents\agda-config`
     folder inside of your Documents folder, and create the two files
     described in the setup sheets.

      - `C:\Users\USERNAME\Documents\agda-config\libraries` should
        contain the line

            C:\Program Files\Agda\stdlib\standard-library.agda-lib

      - `C:\Users\USERNAME\Documents\agda-config\defaults` should
        contain the line

            standard-library

Then to launch an Agda-aware Emacs, look for "Emacs for Agda" in the
Windows start menu (lower-left corner) of applications.

 - Your local Agda files --- such as your local copy (copies) of the
   Course Pack --- should go somewhere within the
   `C:\Users\YOURACCOUNT\Documents` directories, replacing
   `YOURACCOUNT` with your Windows user ID.

You can verify your setup by creating and loading the `testnats.agda`
file described in the _Installing the Agda standard libraries_ section
of the [main setup sheet]({{ site.baseurl }}/Setup/).

### Access to ITS Windows PCs via the Virtual Desktop

**I have not yet tried the remote desktop steps myself.  Please report
successes/failures so that I can update these notes as needed.**

The UWL Virtual Desktop offers almost the same software (and changes)
that the library computers do, and includes Agda. The Virtual Desktop
can be accessed at [virtual.uwlax.edu](https://virtual.uwlax.edu/).

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

## CS lab macs

This installation is in progress, and this section will be updated
with instructions when it is ready.

### Remote access to the CS lab Macs

Information forthcoming.

---

*This page is edited by Maraist with contributions from [Justin
 Bolstad](https://www.uwlax.edu/profile/jbolstad/); for further
 information see the [sources and authorship]({{ site.baseurl
 }}/Sources/) page.*
