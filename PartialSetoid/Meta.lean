import Lean

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
  if (¬Expr.occurs rhs goal) then (
    let hole : TSyntax `term := ⟨ mkHole (Syntax.missing) ⟩
    return Syntax.mkApp (mkIdent `IsProper.refl) #[hole, hole]
  )
  else match goal with
    | Expr.app (.app _ arg1) arg2 =>
      let hole : TSyntax `term := ⟨ mkHole (Syntax.missing) ⟩
      return Syntax.mkApp (mkIdent `IsMorphism2.respects) #[hole, (<- grewriteAux arg1 rhs h), (<- grewriteAux arg2 rhs h)]
    | Expr.app _ arg =>
      let hole : TSyntax `term := ⟨ mkHole (Syntax.missing) ⟩
      return Syntax.mkApp (mkIdent `IsMorphism.respects) #[hole,(<- grewriteAux arg rhs h)]
    | _ => throwError "TODO"

    -- delaborate h to syntax
  -- return

def grewrite (per : Expr) : TacticM PUnit := withMainContext do
  let mvarId <- getMainGoal
  let goalType <- getMainTarget
  let ctx <- getLCtx
  -- let ctx := (<- mvarId.getDecl).lctx
  let e <- inferType per

  -- dbg_trace f!"{e}"
  let Expr.app (.app (.app (.app (.const `PartialSetoid.r _) _) _) _) y := (<- inferType per) | throwError "PER is not a `PartialSetoid.r`"

  let hole : TSyntax `term := ⟨ mkHole (Syntax.missing) ⟩
  let h1 <- delab per
  let value := Syntax.mkApp (mkIdent `PartialSetoid.mp) #[
    (<- grewriteAux goalType y h1),
    hole
  ]
  let (e, gs) <- elabTermWithHoles value goalType `foo (allowNaturalHoles := true)

  let newGoals <- mvarId.apply e

  modify fun _ => { goals := newGoals }

elab "grw" h:term : tactic => withMainContext do
  let expr <- elabTerm h .none true
  grewrite expr
