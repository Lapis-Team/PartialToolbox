/-
Since Lean cannot automatically infer if two expressions `e1` and `e2` have the same type up to unfolding, we encode the `Unfoldable` type class and instantiate it when necessary. Here we simply instantiate transitivity of the class
-/

@[class]
inductive Unfoldable (T : semiOutParam α) : outParam α -> Prop where
 | id: Unfoldable T T

instance {P P' : α → β → Prop} {Q Q' : β → γ → Prop} {R : α → γ → Prop} [Trans P' Q' R'] [up: Unfoldable P P'] [uq: Unfoldable Q Q'] [ur: Unfoldable R R']
 : Trans P Q R := by
 cases up ; cases uq ; cases ur  ; assumption

