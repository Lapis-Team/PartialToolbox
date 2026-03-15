-- Partial types are types equipped with a unary isdef predicate
-- Strict unary and binary functions are defined
-- Strict unary and binary predicates are defined so that they
--   hold only on defined elements
--
-- Option types are shown to be partial types and
--  functions and predicates over base types are automatically
--  lifted to strict functions and predicates
-- Lifted predicates preserve symmetry and transitivity, while
--  reflexivity is preserved only for defined elements

class Partial α where
 isdef : α -> Prop

instance default : Partial α where
 isdef _ := True

class StrictPred₁ [Partial α] (P : α -> Prop) where
 isstrict : P x -> Partial.isdef x

class StrictPred₂ [Partial α] [Partial β] (P : α -> β -> Prop) where
 isstrict : P x y -> Partial.isdef x ∧ Partial.isdef y

class StrictFun₁ [Partial α] [Partial β] (f : α -> β) where
 isstrict : Partial.isdef (f x) -> Partial.isdef x

class StrictFun₂ [Partial α] [Partial β] [Partial γ] (f : α -> β -> γ) where
 isstrict : Partial.isdef (f x y) -> Partial.isdef x ∧ Partial.isdef y

namespace Option

open Partial

instance partialOption : Partial (Option α) where
 isdef
  | .none => False
  | .some _ => True

def liftPred₁ (P: α -> Prop) : Option α -> Prop
 | .some x => P x
 | _ => False

instance {P: α -> Prop}: StrictPred₁ (liftPred₁ P) where
 isstrict {x} h :=
  match x with
  | .some _ => .intro
  | .none => h.elim

def liftPred₂ (P: α -> β -> Prop) : Option α -> Option β -> Prop
 | .some x, .some y => P x y
 | _,_ => False

instance {P: α -> β -> Prop}: StrictPred₂ (liftPred₂ P) where
 isstrict {x} {y} h :=
  match x,y with
  | .some _, .some _ => ⟨.intro,.intro⟩
  | .none ,_ => h.elim

def liftFun₁ (f: α -> β) : Option α -> Option β
 | .some x => .some (f x)
 | _ => .none

instance {f: α -> β}: StrictFun₁ (liftFun₁ f) where
 isstrict {x} h :=
  match x with
  | .some _ => .intro
  | .none => h.elim

def liftFun₂ (f: α -> β → γ) : Option α -> Option β -> Option γ
 | .some x, .some y => .some (f x y)
 | _, _ => .none

instance {f: α -> β → γ}: StrictFun₂ (liftFun₂ f) where
 isstrict {x} {y} h :=
  match x, y with
  | .some _, .some _ => ⟨.intro,.intro⟩
  | .none, _ => h.elim
  | .some _, .none => h.elim

theorem lift_def_refl [Std.Refl P] : isdef x -> liftPred₂ P x x :=
 match x with
 | .some _ => fun _ => Std.Refl.refl (r := P) _
 | .none => False.elim

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

def peq (x y: Option α) : Prop := liftPred₂ Eq x y

theorem peq_eq : peq x y -> x=y :=
 match x,y with
 | .some x, .some y => by change x = y -> _ ; simp
 | .none, _ => False.elim
 | .some _, .none => False.elim

theorem def₁_eq_peq {x y : Option α} : isdef x -> x=y -> peq x y :=
 match x,y with
 | .some x, .some y => by intro h k ; change x=y ; grind
 | .none, _ => by intro h ; apply h.elim
 | .some _, .none => by grind

theorem def₂_eq_peq {x y : Option α} : isdef y -> x=y -> peq x y := by
 grind [def₁_eq_peq]

end Option
