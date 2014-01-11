BLAMda
======

An Unlambda to C compiler written in Haskell.


Compiling
---------

To build the blamda executable, run the following commands:

```bash
cd BLAMda/src
ghc --make -O3 blamda.hs
```

Using
-----

To compile an unlambda file named 'foo.unl' into a c file named 'foo.c',
run the following:

```bash
blamda foo.unl foo.c
gcc -O3 foo.c
```

