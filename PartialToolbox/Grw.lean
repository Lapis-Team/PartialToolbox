import PartialToolbox.Unfoldable
import Lean

/-
This file contains the typeclasses used for implementing generalized rewriting in
a λProlog style using the `copy` algorithm.
- The `Copy` class captures predicates that allow rewriting.
- The `put` and `take` respectively turn a proof of `R lhs rhs` into the corresponding `Copy` instance and back. 
- The `Reflexive` and `Proper` classes allow to reason about terms we don't want to rewrite, i.e. terms that
    are proper w.r.t. the relation we are rewriting. 
    For example, rewriting 0 ≤ 1 in 1 ≤ 1 + 2 yields the goal 0 ≤ 0 + 2 without needing to rewrite (in the generalized rewriting sense) 2.
- The `grw` and `respects` tactics allow to use generalized rewriting in proofs.
-/


/--
The `Copy` class captures the predicate `rel lhs rhs`.
Instancing `@Copy R lhs rhs h` where `h : R lhs rhs` allows to rewrite `lhs` instead of `rhs` in some expression.
Since both the `lhs` and the `out` parameters are output parameters, the search for an
instance will use the `rhs` parameter to determine the previous parameters.
-/
class Copy {rel: β → β → Prop} {lhs: outParam β} {rhs: β} (out: outParam (rel lhs rhs)) where

/-- 
The `put` function takes in input a parameter `k` and synthesizes an instance of `Copy k`. 
It is the dual of the `take` function.
-/
def put (k : r lhs rhs) : @Copy _ r lhs rhs k where

/--
The `take` function searches for an instance of `Copy k` where `k: r lhs rhs` and returns `k`.
It is the dual of the `put` function.
-/
def take [@Copy _ r lhs rhs k] : r lhs rhs := k

/--
`Reflexive r` means the binary relation `r` is reflexive, that is `∀ x, r x x`.
-/
class Reflexive (rel: α -> α -> Prop) where
  refl : rel x x

instance {P P' : α → α → Prop} [u: Unfoldable P P'] [Reflexive P'] : Reflexive P := by
 cases u ; assumption

/--
`Proper r x` means the element `x` is proper for the given relation `r`, that is `r x x`.
-/
class Proper (rel: α -> α -> Prop) (x: α) where
 is_proper: rel x x

instance [h: Reflexive rel] : Proper rel x where
 is_proper := h.refl

instance rr [k: Proper r z] : Copy k.is_proper where

abbrev Impl P Q := P → Q
infix : 40 " ⟶ " => Impl

/-
If `h : ∀ n, R e₁ e₂`, the `copy` algorithm searches for an instance of the class
`∀ n, @Copy α R e₁ e₂ (h n)` if `e₁ e₂ : α`. The `put` tactic handles the scenario
where `h` contains an arbitrary number of binders by deriving the required
instance `∀ n, @Copy α R e₁ e₂ (h n)`.
-/
open Lean Elab Tactic Meta in
local elab "put" h:term : tactic => withMainContext do
  let rec collectBindersAsTerms : Expr -> List (TSyntax `term)
    | .forallE n _ body _ => mkIdent n :: collectBindersAsTerms body
    | _                   => []
  let hTyp <- inferType (<- elabTerm h .none)
  let binders := (collectBindersAsTerms hTyp).toArray
  let bodyStx <- `(term| $h $binders*)
  let putBodyStx <- `(term| fun $binders* => put $bodyStx)
  evalTactic (<- `(tactic| have := $putBodyStx))

/--
`grw h` where `h : R x y` rewrites `x` in place of `y` in the goal if it is possible to
infer an instance of `Copy h`.
-/
macro "grw" h:term : tactic => `(tactic | put $h <;> apply (take : _ ⟶ _))

/--
`respects h` where `h : R e₁ e₂` rewrites `e₁` instead of `e₂` in the goal `R lhs rhs`
if `rhs` is definitionally equal to `rhs[e₁/e₂]` and solves it.
-/
macro "respects" h:term : tactic => `(tactic | put $h <;> exact take)
