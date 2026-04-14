import PartialToolbox.Partial

namespace Partial.Option

open Partial

instance partialOption : Partial (Option α) where
 isdef
  | .none => False
  | .some _ => True

-- The `[@coe]` attribute is specified so that the infoview displays `↑x` instead of `.some x`
@[coe]
abbrev inj (x : α) := (.some x : Option α)
instance : Coe α (Option α) := ⟨inj⟩

def isdef_option_elim {P: Option α -> Sort u} {h : ∀ x, P (.some x)} : x↓ -> P x :=
 match x with
  | .some _ => fun _ => h _
  | .none => False.elim

-------------------- Lifting Predicates --------------------

/-
Defining lifting on unary and binary predicates. A lifted predicates is always strict
as by definition of strictness on predicates. In the case of binary predicates, if the
term is defined, and the relation is reflexive, then also the lifted oriented predicates
are reflexive.
-/

def liftPred₁ (P: α -> Prop) : Option α -> Prop
 | .some x => P x
 | _ => False

instance strictpred₁_liftpred₁ {P: α -> Prop}: StrictPred₁ (liftPred₁ P) where
 isstrict {x} h :=
  match x with
  | .some _ => .intro
  | .none => h.elim

def liftPred₂ (P: α -> β -> Prop) : Option α -> Option β -> Prop
 | .some x, .some y => P x y
 | _,_ => False
instance strictpred₂_liftpred₂ {P: α -> β -> Prop} : StrictPred₂ (liftPred₂ P) where
 isstrict {x} {y} h :=
  match x,y with
  | .some _, .some _ => ⟨.intro,.intro⟩
  | .none ,_ => h.elim

theorem strictpred₂_reflexive_on_def {r : α → α → Prop} [Reflexive r]
 : x↓ -> liftPred₂ r x x := by
 apply isdef_option_elim ; intro x ; simp!
 apply Reflexive.refl

instance strictpred₂_reflexive_ltor {r : α → α → Prop} [Reflexive r]
 : Reflexive ◁(liftPred₂ r) := by
 constructor
 intro x
 apply strictpred₂_reflexive_on_def

instance strictpred₂_reflexive_rtol {r : α → α → Prop} [Reflexive r]
 : Reflexive (liftPred₂ r)▷ := ⟨strictpred₂_reflexive_ltor.refl⟩

-------------------- Lifting Functions --------------------

/-
Defining lifting on unary and binary functions by equipping it with a `dom` parameter
that encodes if the term belongs to the domain. This results in the fact that a lifted 
function is always strict.
Since the `dom` parameter models existence conditions for the function, we encode the
instance of the `Existence` and `Backward` typeclasses.
-/
def liftFun₁ (f: α -> β) (dom : Option α → Bool := fun _ => true) : Option α -> Option β
 | .some x => if dom (.some x) then .some (f x) else .none
 | _ => .none

instance {f: α -> β}: StrictFun₁ (liftFun₁ f) where
 isstrict {x} h :=
  match x with
  | .some _ => .intro
  | .none => h.elim

instance existence_liftfun₁ {f: α -> β} : Existence (liftFun₁ f dom x) (dom x) where
 cond h :=
  match x with
  | .some _ => by
     simp [liftFun₁] at h
     split at h <;> trivial
  | .none => h.elim

instance strictfun₁_backward {f: α → β} : Backward₁ (liftFun₁ f dom x)↓ (x↓ ∧ dom x) where
 intro := by
  simp
  apply isdef_option_elim ; intro x
  intro ec
  simp [liftFun₁]
  split
  . apply True.intro
  . contradiction

def liftFun₂ (f: α -> β → γ) (dom : Option α → Option β → Bool := fun _ _ => true) : Option α -> Option β -> Option γ
 | .some x, .some y =>
    if dom (.some x) (.some y) then .some (f x y) else .none
 | _, _ => .none

@[simp]
theorem liftFun₂_simpl : dom (some x) (some y) → liftFun₂ f dom (some x) (some y) = some (f x y) := by
 intro h
 change (if dom (some x) (some y) then some (f x y) else none) = some (f x y)
 simpa

instance strictfun₂_liftfun₂ {f: α -> β → γ} : StrictFun₂ (liftFun₂ f dom) where
 isstrict {x} {y} h :=
  match x, y with
  | .some _, .some _ => ⟨.intro,.intro⟩
  | .none, _ => h.elim
  | .some _, .none => h.elim

instance existence_liftfun₂ {f: α -> β → γ} : Existence (liftFun₂ f dom x y) (dom x y) where
 cond h :=
  match x, y with
  | .some _, .some _ => by
     simp [liftFun₂] at h
     split at h <;> trivial
  | .none, _ => h.elim
  | .some _, .none => h.elim

instance strictfun₂_backward {f: α → β → γ} : Backward₁ (liftFun₂ f dom x y)↓ (x↓ ∧ y↓ ∧ dom x y) where
 intro := by
  simp
  apply isdef_option_elim ; intro x
  apply isdef_option_elim ; intro y
  intro ec
  simp [liftFun₂]
  split
  . apply True.intro
  . contradiction

theorem lift_def_refl [Std.Refl P] : x↓ -> liftPred₂ P x x := by
 apply isdef_option_elim
 apply Std.Refl.refl

instance [Std.Symm P] : Std.Symm (liftPred₂ P) where
 symm
  | .some _, .some _ => Std.Symm.symm (r := P) _ _
  | .none, _ => False.elim
  | .some _, .none => False.elim

instance [Trans P Q R] : Trans (liftPred₂ P) (liftPred₂ Q) (liftPred₂ R) where
 trans {x y z} :=
  match x,y,z with
  | .some _, .some _, .some _ => Trans.trans (r:= P) (s:= Q) (t:= R)
  | .none, _, _ => False.elim
  | .some _, .none, _ => False.elim
  | .some _, .some _, .none => fun _ => False.elim

@[simp]
theorem liftFun₂_simpl' {f : α → β → γ} [u: Unfoldable g (liftFun₂ f dom)] : dom (some x) (some y) → g (some x) (some y) = some (f x y) := by
 cases u ; apply Partial.Option.liftFun₂_simpl

end Partial.Option


