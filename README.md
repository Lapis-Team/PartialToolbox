# PartialToolbox

Implementation in Lean of the toolbox presented in _A Toolbox for Undefined Terms in Type Theory_.
## Repository Organisation
The library is fully contained in the `PartialToolbox` directory. We suggest the navigation of the repository in the following order.

### Partial
The `PartialToolbox/Partial.lean` file contains the definition the `Partial` typeclass together with the implementation of strictness, existence conditions a directed relations.

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
