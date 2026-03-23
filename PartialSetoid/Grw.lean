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

macro "grw" h:term : tactic => `(tactic | have := put $h <;> apply Iff.mp take)
macro "respects" h:term : tactic => `(tactic | have := put $h <;> apply take)

open Lean Elab Tactic Meta PrettyPrinter in
elab "respects'" h:term : tactic => do
  let goalType <- whnf (<- getMainTarget)

  let rec collectBindersAsTerms : Expr -> List (TSyntax `term)
    | .forallE n _ body _ => mkIdent n :: collectBindersAsTerms body
    | _                   => []

  let binders := (collectBindersAsTerms goalType).toArray
  let bodyStx <- `(term| $h $binders*)
  let putBodyStx <- `(term| fun $binders* => put $bodyStx)
  evalTactic (<- `(tactic| have := $putBodyStx <;> apply take ))

register_label_attr def_lemma
register_label_attr def_lemma_closing
macro "def_intro" : tactic =>
 let dlemma := Lean.mkIdent `def_lemma
 let dlemma_closing := Lean.mkIdent `def_lemma_closing
 `(tactic | (try apply_rules using $dlemma) <;> try solve_by_elim (maxDepth := 8) using $dlemma_closing, $dlemma)
