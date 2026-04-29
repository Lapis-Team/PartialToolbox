# PartialToolbox

Implementation in Lean of a toolbox for undefined terms.

## Setup

To correctly setup the project you first need to install Lean. The instructions to do so are well-documented on the [website](https://lean-lang.org/install/).
After installing Lean, you only need to open the directory on your own editor (the suggested one as per the Lean website is VS Code) and navigate the code.

If you want to build the entire project, you need to open a terminal inside the directory and run the `lake build` command.

## Repository Organisation

The library is fully contained in the `PartialToolbox` directory. We suggest the navigation of the repository in the following order.

### Unfoldable

We want to automate reasoning as much as possible with the use of typeclasses. However, Lean doesn't have any tool for automatically infer if two expressions `e1` and `e2` have the same type up to unfolding. For this reason, we encode the `Unfoldable` type class and instantiate it when necessary.

### Partial

The `PartialToolbox/Partial.lean` file contains the definition the `Partial` typeclass together with the implementation of strictness, existence conditions and directed relations.

### ForwardBackward

The `PartialToolbox/ForwardBackward.lean` file contains the definition of the typeclasses `Forward` and `Backward` with also their atomic variants.

### Grw

The `PartialToolbox/Grw.lean` file contains the implementation of the `copy` algorithm used in lambdaProlog (see Section 7.6 of "Programming with Higher-order logic"). You will find the definition of the two tactics `grw` and `respects` with the local definition of the `put` tactic that is used for handling scenarios where there are also binders.

### Partial Option

The `PartialToolbox/PartialOption.lean` file contains the implementation of lifting by instancing the `Partial` with the `Option` monad. In this file, you will find the implementation for lifting both functions and predicates, together with all the properties lifting ensures.

### Tests

The `Tests` directory contains some files with example usage of the library. 
In particular, you will find the running example presented in the paper in the `running.lean` file; as the name suggests, the `grw.lean` file contains some usage examples of the `grw`. 
Finally, the `optionNat.lean` file showcases lifting on natural numbers, and shows some final examples where also generalized rewriting (in the form of the `respects` tactic) is used.

### Playground

Finally, the `Playground.lean` file contains some sections of minimal examples that are also presented in the paper. The file is also meant to be used for playing around with the library with custom examples in the `Playground` namespace.

## Testing

To run the tests contained in the `Tests` directory, run the `lake test` command. If you want to add your own tests, add the files in the directory, and then edit the `Tests.lean` file in the root directory by importing your own tests.
