# PartialToolbox

Implementation in Lean of a toolbox for undefined terms, as explained in the paper _A Toolbox for Undefined Terms in Type Theory_ written by Nicolò Pizzo and Claudio Sacerdoti Coen.

## The Toolbox

Following is a brief presentation of the ingredients composing the toolbox:
* Generalized Rewriting: generalized rewriting consists in the ability to rewrite an expression `e1` with an expression `e2` in a certain context if the expressions are related by some congruence `R` for that context. To allow generalized rewriting, we implemented the `grw` and `respects` tactics.
* Definedness Automation: the toolbox allows to extract definendess constraints and existence conditions from a given term, so that the user is able to propagate such constraints through a proof. We achieve definedness automation by means of forward and backward chains.
* Lifting: the toolbox allows to lift types and functions so that the undefined value $\bot$ is included in the domain of the terms.

## Setup

To correctly setup the project you first need to install Lean. The instructions to do so are well-documented on the [website](https://lean-lang.org/install/).
After installing Lean, you only need to open the directory on your own editor (the suggested one as per the Lean website is VS Code) and navigate the code.

If you want to build the entire project, you need to open a terminal inside the directory and run the `lake build` command.

## Repository Organisation

The repository contains some usage examples in the [`Playground.lean`](Playground.lean) file and some more specific tests in the `Tests` directory.
The implementation of the toolbox, on the other side, is fully contained in the `PartialToolbox` directory.

### Tests and Playground

The `Tests` directory contains some files with example usage of the library.
In particular, you will find the running example presented in the paper in the [`running.lean`](Tests/running.lean) file; as the name suggests, the [`grw.lean`](Tests/grw.lean) file contains some usage examples of the `grw` tactic.
Finally, the [`optionNat.lean`](Tests/optionNat.lean) file showcases lifting on natural numbers, and shows some final examples where also generalized rewriting (in the form of the `respects` tactic) is used.

The [`Playground.lean`](Playground.lean) file contains some sections of minimal examples that are also presented in the paper. The file is also meant to be used for playing around with the library with custom examples in the `Playground` namespace.

To run the tests contained in the `Tests` directory, run the `lake test` command. If you want to add your own tests, add the files in the directory, and then edit the `Tests.lean` file in the root directory by importing your own tests.

#### Usage Examples

The toolbox is designed to combine partiality, lifting, rewriting, and automated reasoning. We highlight some usage examples for the toolbox.

##### Backward Reasoning

Complex definedness goals may be reduced employing invertible rules

```lean
instance : Backward₁ (x + y)↓ (x↓ ∧ y↓) := ...

example : x↓ → y↓ → z↓ → (x + y + z)↓ := by
  intro hx hy hz
  apply Backward.intro
  exact ⟨⟨hx, hy⟩, hz⟩
```

##### Generalized Rewriting

Rewriting is allowed under arbitrary relations

```lean
def R : Nat → Nat → Prop := ...
def P : Nat → Prop := ...
theorem P' : R x y → (P x ⟶ P y) := ...

instance [Copy k] : Copy (P' k) where 

example (h : R x y) : P x → P y := by
  intro hx
  grw h
  exact hx
```

##### Lifting to partial types

Functions and predicates can easily be lifted to the partial setting

```lean
def liftedLE : Option Nat → Option Nat → Prop := liftPred₂ LE.le
```

### Implementation

You can find the implementation of the ingredients composing the toolbox in the `PartialToolbox` directory. Specifically, you will find the following files.

#### Unfoldable

Lean’s typeclass resolution does not natively identify terms that are equal *up to unfolding* (or, more generally, up to definitional or propositional equality). This limitation can hinder automation when equivalent predicates are written in syntactically different forms.

The file [`Unfoldable.lean`](PartialToolbox/Unfoldable.lean) introduces a lightweight typeclass `Unfoldable` which allows the system to treat two terms as interchangeable during instance search. 

#### ForwardBackward

The file [`ForwardBackward.lean`](PartialToolbox/ForwardBackward.lean) defines a lightweight typeclass-based framework for automating forward and backward reasoning within Lean proofs. 

The core idea is to represent reasoning steps as typeclass instances that can be chained automatically by Lean’s instance resolution mechanism. Two dual families of typeclasses are provided:

* Backward reasoning: reduces a goal to simpler subgoals.
* Forward reasoning: extracts consequences from hypotheses.

Each direction is then split into:

* an atomic layer (`Backward₁`, `Forward₁`) representing single logical steps, and
* a compositional layer (`Backward`, `Forward`) that chains these steps structurally.

#### Partial

The file [`Partial.lean`](PartialToolbox/Partial.lean) provides the core infrastructure for reasoning about partial terms, equipping types with a definedness predicate denoting that a term is defined. A default instance treats all elements as defined, enabling gradual introduction of partiality.

Strictness of functions and predicates is captured via typeclasses (`StrictFun₁/₂`, `StrictPred₁/₂`): a function is strict if defined outputs imply defined inputs, while a predicate is strict if its validity implies defined arguments. The `Existence` class complements this by expressing necessary conditions for definedness (e.g. side conditions such as nonzero denominators).

A notion of partial equality integrates equality with definedness, supporting rewriting and transitivity while tracking well-definedness.

Relations are lifted to the partial setting through directed variants:

* `◁r` (left-to-right), requiring the left-hand side to be defined,
* `r▷` (right-to-left), requiring the right-hand side to be defined,
* `◁r▷` (bidirectional), requiring both.


#### Grw

The file [`Grw.lean`](PartialToolbox/Grw.lean) implements generalized rewriting by means of the `grw` and `respects` tactics in a λProlog-inspired style using typeclass resolution. Instead of relying on equality, rewriting is driven by an arbitrary relation `R`, allowing transformations under congruent contexts (e.g. monotonicity).

The core component is the `Copy` typeclass, which encodes a relation `R lhs rhs` while leaving `lhs` to be reconstructed by instance search. This enables a "copying" mechanism where the structure of expressions is propagated during rewriting.


#### Partial Option

The [`PartialOption.lean`](PartialToolbox/PartialOption.lean) file contains the implementation of lifting by instancing the `Partial` with the `Option` monad. In this file, you will find the implementation for lifting both functions and predicates, together with all the properties lifting ensures.

The file [`PartialOption.lean`](PartialToolbox/PartialOption.lean) instantiates the `Option` type as a model of partiality, where `none` represents undefined terms and `some x` represents defined ones. 

The module defines systematic lifting of predicates (`liftPred₁`, `liftPred₂`) and functions (`liftFun₁`, `liftFun₂`): lifted predicates hold only on defined inputs and are automatically strict; they preserve standard properties such as reflexivity, symmetry, and transitivity. Simplification lemmas (`@[simp]`) expose their behavior on defined values. On the other hand, lifted functions return `none` on undefined inputs and are parameterized by an optional `dom` predicate encoding existence conditions. These conditions are automatically reflected into:

* `Existence` instances (forward reasoning),
* `Backward₁` instances (goal reduction).

As a result, definedness and side conditions are propagated transparently by the automation framework.
