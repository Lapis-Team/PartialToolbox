/-
- Since type-class resolution in Lean does not handle terms up-to unfolding, we introduce
    the `Unfoldable` type class to handle two equivalent terms likewise. Notice that this
    mechanism is logically equivalent to propositional equality.

- Example usage
    By declaring an instance `Unfoldable P Q` the user is able to handle `P` as `Q` during
    class instance search. As an example, consider the predicate `LE.le` over natural numbers:
    one may need to treat seamlessly the predicate in the form `LE.le` and `fun x y => x ≤ y`.
    To do so, the user only needs to register the proper `Unfoldable` instance.
   `instance : Unfoldable (·≥· : Nat -> Nat -> Prop) (GE.ge) := .id`
-/

@[class]
inductive Unfoldable (T : semiOutParam α) : outParam α -> Prop where
 | id: Unfoldable T T

instance {P P' : α → β → Prop} {Q Q' : β → γ → Prop} {R : α → γ → Prop} [Trans P' Q' R'] [up: Unfoldable P P'] [uq: Unfoldable Q Q'] [ur: Unfoldable R R']
 : Trans P Q R := by
 cases up ; cases uq ; cases ur  ; assumption

