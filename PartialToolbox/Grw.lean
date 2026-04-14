import Lean

class Copy {rel: β → β → Prop} {lhs: outParam β} {rhs: β} (out: outParam (rel lhs rhs)) where

def put k : @Copy _ r lhs rhs k := by constructor

def take : [@Copy _ r lhs rhs k] -> r lhs rhs := k

class Reflexive (rel: α -> α -> Prop) where
  refl : rel x x

class Proper (rel: α -> α -> Prop) (x: α) where
 is_proper: rel x x

instance [h: Reflexive rel] : Proper rel x where
 is_proper := h.refl

instance rr [k: Proper r z] : Copy k.is_proper where

/-
The copy algorithm rewrites an hypothesis `h: R x y` to prove a goal in the form
`P e₁ ⟶ P e₂` where `e₂` is `e₁[y/x]`. Since the `out` param of the `Copy` class is
an explicit binary relation, and Lean cannot put the implication → in place of `rel`
we need the following abbreviation. The infix arrow is the `\longrightarrow`, thus
it doesn't create any conflit with the → implication symbol.
-/
abbrev Impl P Q := P → Q
infix : 40 " ⟶ " => Impl

/-
If `h : ∀ n, R e₁ e₂`, the `copy` algorithm searches for an instance of the class
`∀ n, @Copy α R e₁ e₂ (h n)` if `e₁ e₂ : α`. The `put` tactic handles the scenario
where `h` contains an arbitrary number of binders by deriving the required
instance `∀ n, @Copy α R e₁ e₂ (h n)`.
-/
open Lean Elab Tactic Meta in
local elab "put" h:term : tactic => do
  let rec collectBindersAsTerms : Expr -> List (TSyntax `term)
    | .forallE n _ body _ => mkIdent n :: collectBindersAsTerms body
    | _                   => []
  let hTyp <- inferType (<- elabTerm h .none)
  let binders := (collectBindersAsTerms hTyp).toArray
  let bodyStx <- `(term| $h $binders*)
  let putBodyStx <- `(term| fun $binders* => put $bodyStx)
  evalTactic (<- `(tactic| have := $putBodyStx))

macro "grw" h:term : tactic => `(tactic | put $h <;> apply (take : _ ⟶ _))

macro "respects" h:term : tactic => `(tactic | put $h <;> exact take)
