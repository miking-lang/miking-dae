# An Differential-Algebraic Equations (DAEs) DSL
This repository contains a DSL for expressing and numerically solving high-index
DAEs. The DAEs may include recursive functions and the compilation use the
forward-mode Partial Evaluation of Automatic Differentiation (PEAD) method[^1].

## Installation Instructions

Install the following dependencies (we assume that you have `make` in your path).

### OCaml
See the Opam installation guide for how to install
[link](https://opam.ocaml.org/doc/Install.html).

Create the Opam 4.14.0 switch named miking-sundials:
```
opam update
opam switch create miking-sundials 4.14.0
eval $(opam env)
```
Install the required opam packages

```
opam install dune linenoise sundialsml ocamlbuild
```

This should also prompt you to install the sundials C library.

### Miking

You need to download and install the [Miking](http://miking.org/)
compiler. Because some changes to the compiler and standard library have not yet
been merged, clone the following fork:

```
git clone git@github.com:br4sco/miking.git
```

and checkout `develop-pead`

```
git checkout develop-pead
```

Then build and install the Miking compiler with

```
make clean && make install
```

This will install the compiler and standard library to `$HOME/.local`. To remove
it you can use

```
make uninstall
```

In the following we will assume that `$HOME/.local/bin` is in your
path. Otherwise you can call the miking compiler with `$HOME/.local/bin/mi`.

### Test the Sundials solver

When you have installed Miking, you can in the Miking source root folder run

```
make test-sundials
```

to make sure that you have Sundials up and working.

### Install PEAD DAE

From the root of this repository do the following.

Set the environment variable:

```
export PEADAE=$(pwd)/miking-dae
```

compile the PEAD DAE compiler

```
make clean && make
```

This gives you an executable `peadae` under `build`. If you want to, you can add
it to your path with

```
PATH=$PATH:$(pwd)/build
```

## Testing Examples

The folder `examples` contains some example DAEs (they have `.dae`
suffices). Some of these DAE models have been generated from Equation-Based
Object-Oriented Models implemented in [Modelyze](https://www.modelyze.org/). If
you want to re-generate these, see further down.

One of these examples is the Furuta pendulum. To compile the model to simulation
code do

```
./build/peadae --cse --debug --jac-spec-absolute 2 examples/furuta.dae > furuta.mc
```

where we used common sub-expression elimination before the index reduction
transform to remove some of the expression swell introduced by the Modelyze
interpreter and where we specialize all Jacobian columns that have 2 or fewer
non-zero elements. We also pass the debug flag to get some feedback on how our
model is compiled.

To compile without partial evaluation you can compile with the `--disable-peval`
flag.

### Compile the Simulation Code to an Executable

We can now compile our Miking program to produce a simulation binary with the
following command:

```
mi compile furuta.mc
```

### Simulate

To get a simulation trace you can just run the executable

```
./furuta --interval 20
```

You can visualize the trace with the plotting script `csvplot` in the `tools`
directory as follows

```
./furuta --interval 20 | ./tools/csvplot
```

This script uses [gnuplot](http://www.gnuplot.info/) under the hood.

## Test All Examples

To test all examples you can run:

```
make test-examples
```

The will compile, simulate, and compare simulation output for all DAE models in
the examples directory. The output comparison uses `python` and `numpy`.

To clean-up you can do

```
make clean
```

## Generating DAEs from EOO Models

To generate DAE models from the EOO models in the `examples` folder you need to
install a fork of Modelyze.

```
git clone --recurse-submodules git@gits-15.sys.kth.se:oerikss/mbmlang.git
```

The checkout the branch `daecore`

```
git checkout daecore
```

In this root, build the Modelyze interpreter with

```
make
```

You need to setup your environment and path as

```
export MBMLANG_DIR=$(pwd)
export MODELYZE_DIR=$MBMLANG_DIR/modelyze
export PATH=$PATH:$MBMLANG_DIR/bin
```

you can then translate the EOO models in the `examples` directory as, e.g., 

```
moz examples/cauer.moz
```

which will print the translation to standard out.

> Note that for some of the models you have to manually adjust the initial
> conditions before compiling with `peadae`. There are consistent initial
> conditions for the models in the `examples` folder that needs
> adjusting.

## Difference from the Paper Evaluation

The code in this repository has changed a bit from the implementation used in
the paper evaluation. The main difference is that paper implementation used more
immutable data structures and it seems to be more sensitive to cache
effects. The paper implementation is available
[here](https://zenodo.org/records/8347712).

[^1]: Oscar Eriksson, Viktor Palmkvist, and David Broman. 2023. Partial Evaluation of Automatic Differentiation for Differential-Algebraic Equations Solvers. In Proceedings of the 22nd ACM SIGPLAN International Conference on Generative Programming: Concepts and Experiences (GPCE 2023). Association for Computing Machinery, New York, NY, USA, 57–71. https://doi.org/10.1145/3624007.3624054
