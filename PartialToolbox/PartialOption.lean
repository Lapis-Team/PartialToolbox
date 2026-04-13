import PartialToolbox.Partial

namespace Partial.Option

open Partial

instance partialOption : Partial (Option α) where
 isdef
  | .none => False
  | .some _ => True

@[coe]
abbrev inj (x : α) := (.some x : Option α)
instance : Coe α (Option α) := ⟨inj⟩

def isdef_option_elim {P: Option α -> Sort u} {h : ∀ x, P (.some x)} : x↓ -> P x :=
 match x with
  | .some _ => fun _ => h _
  | .none => False.elim

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

end Partial.Option

@[class]
inductive Unfoldable (T : semiOutParam α) : outParam α -> Prop where
 | id: Unfoldable T T

instance {f g : α -> α -> Prop} [Partial α] [u: Unfoldable g f] : Unfoldable g▷ f▷ := by
 cases u ; exact .id

instance [u: Unfoldable g f] : Unfoldable ◁g ◁f := by
 cases u ; exact .id

instance [Partial α] [Partial β] {g f : α -> β → Prop} [u: Unfoldable g f] [StrictPred₂ f]
 : StrictPred₂ g := by
 cases u ; assumption

instance [Partial α] {g f : α -> Prop} [u: Unfoldable g f] [StrictPred₁ f]
 : StrictPred₁ g := by
 cases u ; assumption

instance [Partial α] [Partial β] {g f : α -> β} [u: Unfoldable g f] [StrictFun₁ f]
 : StrictFun₁ g := by
 cases u ; assumption

instance [Partial α] [Partial β] [Partial γ] {g f : α -> β → γ} [u: Unfoldable g f] [StrictFun₂ f]
 : StrictFun₂ g := by
 cases u ; assumption

instance [Partial α] [Partial β] {g f : α -> β} [u: Unfoldable g f] [Existence (f x) P]
 : Existence (g x) P := by
 cases u ; assumption

instance [Partial α] [Partial β] [Partial γ] {g f : α -> β → γ} [u: Unfoldable g f] [Existence (f x y) P]
 : Existence (g x y) P := by
 cases u ; assumption

instance [Partial α] [Partial β] {g f : α -> β} [u: Unfoldable g f] [Backward₁ (f x)↓ P]
 : Backward₁ (g x)↓ P := by
 cases u ; assumption

instance [Partial α] [Partial β] [Partial γ] {g f : α -> β → γ} [u: Unfoldable g f] [Backward₁ (f x y)↓ P]
 : Backward₁ (g x y)↓ P := by
 cases u ; assumption

instance {P P' : α → β → Prop} {Q Q' : β → γ → Prop} {R : α → γ → Prop} [Trans P' Q' R'] [up: Unfoldable P P'] [uq: Unfoldable Q Q'] [ur: Unfoldable R R']
 : Trans P Q R := by
 cases up ; cases uq ; cases ur  ; assumption

instance {P P' : α → α → Prop} [u: Unfoldable P P'] [Reflexive P']
 : Reflexive P := by
 cases u ; assumption

@[simp]
theorem Partial.Option.liftFun₂_simpl' {f : α → β → γ} [u: Unfoldable g (Partial.Option.liftFun₂ f dom)] : dom (some x) (some y) → g (some x) (some y) = some (f x y) := by
 cases u ; apply Partial.Option.liftFun₂_simpl

variable {x: Nat}
