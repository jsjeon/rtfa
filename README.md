Remapping Transformer for Field Affinity (RTFA)
===============================================

RTFA is a [CIL][cil]-based C compiler that optimizes the program's
memory layout according to its memory access patterns.

[cil]: https://github.com/kerneis/cil

Publications
------------

* [Layout Transformations for Heap Objects Using Static Access Patterns.][cc07]
  Jinseong Jeon, Keoncheol Shin, and Hwansoo Han.
  In International Conference on Compiler Construction (CC '07), Mar 2007.

* [Abstracting Access Patterns of Dynamic Memory Using Regular Expressions.][TACO09]
  Jinseong Jeon, Keoncheol Shin, and Hwansoo Han.
  ACM Transactions on Architecture and Code Optimization (TACO), Vol. 5(4), Article 18, Mar 2009.

[cc07]: http://dx.doi.org/10.1007/978-3-540-71229-9_13
[TACO09]: http://dx.doi.org/10.1145/1498690.1498693

Build
-----

First of all, copy RTFA source files into CIL's ext folder:

    $ cp -rf <rtfa_path> <cil_path>/src/ext/rtfa

Next, change CIL's Makefile to point to RTFA source
and add the corresponding feature into CIL's main module:

    $ cd <cil_path>
    $ patch Makefile.in < src/ext/rtfa/Makefile.in.patch
    $ patch src/main.ml < src/ext/rtfa/main.ml.patch

Then, follow the CIL's build process as follows:

    $ ./configure
    $ make

You can see RTFA's various options in CIL command:

    $ ./bin/cilly

