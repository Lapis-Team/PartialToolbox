import Lean
import PartialSetoid.Basic

open Lean
open Lean.Meta
open Lean.MonadLCtx
open Lean.Elab.Tactic

open Lean.PrettyPrinter

def currentHyp {m: Type -> Type} [Monad m] (ctx: Lean.LocalContext) : m PUnit := do
  ctx.forM fun d => do
    let decType := d.type
    let decName := d.userName
    dbg_trace f!"+ {decName}  : {decType}"
  return

def grewriteAux (goal : Expr) (rhs : Expr) (h : TSyntax `term) : TacticM (TSyntax `term) := do
  if (<- isDefEq goal rhs) then return h
  else if (!Expr.occurs rhs goal) then `(term| IsProper.refl _ _)
  else match goal with
    | .app (.app _ arg1) arg2 =>
      let grw1 <- grewriteAux arg1 rhs h
      let grw2 <- grewriteAux arg2 rhs h
      `(term| IsMorphism2.respects _ $grw1 $grw2)
    | .app _ arg =>
      let grw <- grewriteAux arg rhs h
      `(term| IsMorphism.respects _ $grw)
    | _ => throwError "TODO"

def extractRhs : Expr -> TacticM Expr
  | Expr.app _ arg => extractRhs arg
  | e => return e

def extractLhs : Expr -> TacticM Expr
  | .app (.app _ lhs) _ => return lhs
  | e => return e
  -- | Expr.app (.app (.app (.app (.const `PartialSetoid.r _) _) _) _) y => return y
  -- | _ => throwError "Not possible"

def grewrite (per : Expr) : TacticM PUnit := withMainContext do
  let mvarId <- getMainGoal
  let goalType <- getMainTarget

  let rhs <- extractRhs (<- inferType per)
  let h1 <- delab per
  let x <- grewriteAux goalType rhs h1
  let value <- `(term| PartialSetoid.mp $x _)
  let (e, _) <- elabTermWithHoles value goalType `refined (allowNaturalHoles := true)

  let newGoals <- mvarId.apply e

  modify fun _ => { goals := newGoals }

elab "grw" h:term : tactic => withMainContext do
  let expr <- elabTerm h .none true
  grewrite expr
