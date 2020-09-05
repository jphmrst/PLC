---
layout: page
title: Accessing and configuring Agda on UWL machines
prev :     /Setup/
permalink: /UWL/
next :     /Sources/
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

To use the Agda on ITS Windows PCs, you must still configure your
account to point Agda to the standard libraries.  (This is Step 2 of
section *Installing the Agda standard libraries* on the [Getting
started]({{ site.baseurl }}/Setup/) page.)  There are a few steps and
decisions for this configuration.

### Getting a copy of the Agda standard library

There are two ways you can get a copy of the Agda standard library.

 - The simpler method is to use the copy which is already on the ITS
   PCs.  Because this method uses a copy of the standard library which
   you do not have authorization to delete or change, it is the more
   stable of the two, and I recommend this method over the other one
   below.  **However, this method may not work yet.  ITS and I are
   working to solve the technical issues behind the problem.**

   This copy of the standard library has its _locator file_ at

       C:\Program Files\Agda\stdlib\standard-library.agda-lib

 - The more complicated method is to download your own copy of the
   standard library.  Because you can accidentally tamper with your
   own installation, this method is a little bit more fragile.  **This
   method should work right now, although I have not yet had a chance
   to test it on one of the machines in the library.**

    1. Create the folder `C:\Users\USERNAME\Documents\agda-stdlib`
       inside your `Documents` folder, where `USERNAME` is your actual
       login name (omitting the `@uwlax.edu` part).  (Or choose a
       different folder name/location, and consistently use it instead
       in the rest of these steps.)

    2. Download the right version of the Agda standard library into the
       new `C:\Users\USERNAME\Documents\agda-stdlib` folder, as
       described in the [main setup sheet]({{ site.baseurl }}/Setup/).
       When you have it in place, you should have (among other files
       and folders) a file
       `C:\Users\USERNAME\Documents\agda-stdlib\standard-library.agda-lib`
       and a folder `C:\Users\USERNAME\Documents\agda-stdlib\src`.

   This copy of the standard library has its _locator file_ at

       C:\Users\USERNAME\Documents\agda-stdlib\standard-library.agda-lib

### Locating the standard library on ITS PC
 
   1. Create a folder inside of your Documents folder called
      `C:\Users\USERNAME\Documents\agda-config`.  You can choose a
      different folder name/location so long as you consistently use
      it instead.

   2. Inside the new `agda-config` folder, create a file called
      `C:\Users\USERNAME\Documents\agda-config\libraries`.  It should
      contain one line, with just the locator file of the Agda
      standard library copy you chose in the previous section.

   3. Create another file inside of the `agda-config` folder, called
      `C:\Users\USERNAME\Documents\agda-config\defaults`.  This file
      should contain the line
 
          standard-library

   4. Set the `AGDA_DIR` environment variable to
      `C:\Users\USERNAME\Documents\agda-config`.  

       - Click on the "This PC" icon on the desktop.
       
       - Select the "Computer" item from the menubar at the top of the
         window.
       
       - Select "System properties" from the menu.
       
       - Enter the word `environment` into the search bar near the
         upper-left corner of the window.
       
       - Select "Edit the environment variables from your account" from the
         options which pop up.
       
       - A separate window called "Environment variables" will open.
         Sometimes this window will appear behind the "System properties"
         window, so look for it there if nothing seems to happen.
       
       - Check to see if the variable `AGDA_DIR` already exists.  If it
         does, use the `Edit...` button to set it value; if it does not, use
         the `New...` button to create it and give it a value.

### After you locate the standard library on an ITS PC

Then to launch an Agda-aware Emacs, look for "Emacs for Agda" in the
Windows start menu (lower-left corner) of applications.

You can verify your setup by creating and loading the `testnats.agda`
file described in the _Installing the Agda standard libraries_ section
of the [main setup sheet]({{ site.baseurl }}/Setup/).

Your local Agda files --- such as your local copy (copies) of the
Course Pack --- should go somewhere within the
`C:\Users\YOURACCOUNT\Documents` directories, replacing `YOURACCOUNT`
with your Windows user ID.

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
