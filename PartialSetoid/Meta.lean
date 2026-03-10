import Lean
import PartialSetoid.Basic

open Lean Lean.Meta Lean.MonadLCtx Lean.Elab.Tactic Lean.PrettyPrinter

def hasInstance (head: Expr) : TacticM Bool := do
  let headStx <- delab (head.setPPExplicit true)
  let morphStx <- `(term| IsMorphism _ _ $headStx)
  let synthesized? <- Meta.synthInstance? (<- elabTerm morphStx .none)
  return synthesized?.isSome

mutual
  partial def grewriteAux (goal : Expr) (rhs : Expr) (h : TSyntax `term) : TacticM (TSyntax `term) := do
    if (<- isDefEq goal rhs) then return h
    else if (!Expr.occurs rhs goal) then `(term| IsProper.refl _ _)
    else grewriteAux' goal .nil rhs h

  partial def grewriteAux' (goal: Expr) (args: List Expr) (rhs: Expr) (h : TSyntax `term) : TacticM (TSyntax `term) := do
    match goal with
    | .app head arg =>
      let newArgs := arg :: args
      if (<- hasInstance head) then
        let arrows <- args.foldlM
          (fun acc _ => `(term| arrowPS _ $acc))
          (<- `(term| _))

        let grwArgs <- newArgs.toArray.mapM fun arg => grewriteAux arg rhs h
        `(term| IsMorphism.respects (psb := $arrows) _ $grwArgs*)
      else
        grewriteAux' head newArgs rhs h
    | _ =>
      throwError "TODO"
end

def extractRhs? : Expr -> Option Expr
  | .app _ rhs => rhs
  | _ => .none

def grewrite (per : Expr) : TacticM PUnit := withMainContext do
  let mvarId <- getMainGoal
  let goalType <- getMainTarget

  let some rhs := extractRhs? (<- inferType per) | throwError "Cannot extract rhs from expression"
  let h1 <- delab (per.setPPExplicit true)
  let x <- grewriteAux goalType rhs h1
  let value <- `(term| PartialSetoid.mp $x _)
  let (e, _) <- elabTermWithHoles value goalType `refined (allowNaturalHoles := true)

  let newGoals <- mvarId.apply e

  modify fun _ => { goals := newGoals }

elab "grw" h:term : tactic => withMainContext do
  let expr <- elabTerm h .none true
  grewrite expr
