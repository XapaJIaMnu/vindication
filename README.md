vindication
===========

An extension to the Carneades framework, aiming to simulate a court case.

This project is based on the Haskell Carneades argumentation [framework](http://www.cs.nott.ac.uk/~bmv/CarneadesDSL/index.html)

I extended the framework in order to enable it to represent loosely how a court case is heard, how
the burden of proof shifts from the prosecution to the defense and vice versa.

I post the project here with the permission of Bas van Gijzel.

Compilation
-----------
`cd src`
`sh build.sh`

It produces a file called carneades

Running
-------

To run do a (of course after compiling first):

`./carneades filename proposition_to_check`

Please check the READMEs folder for more information.

Examples
--------

Several examples are provided in the src directory. To run the framework with them do:

`./carneades Hans_Reiser murderer`

`./carneades the_thief_murderer intent`

The configfiles are plain text files. Information about the format is found in the READMEs directory.

Interactive
-----------

The framework can also be loaded in ghci and used in an interactive way.

To do so do:

`ghci Runme.hs`

`testProp filename prop`

Where filename is the name of your file and prop is the name of the proposition you want to test.
both filename and prop should strings (Which means they should be supplied in quotes ("")

As always to check for negative proposition you should put a - in front of it ("-prop")
