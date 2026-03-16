import PartialSetoid.Partial
open Partial (isdef)
open Partial.Option

instance : OfNat (Option Nat) n where ofNat := n

instance : LE (Option Nat) := ⟨liftPred₂ Nat.le⟩
instance : Add (Option Nat) := ⟨liftFun₂ Nat.add⟩
instance : Mul (Option Nat) := ⟨liftFun₂ HMul.hMul⟩
instance : Div (Option Nat) where
    div
    | .some x, .some y => if some y == 0 then .none else .some (x / y)
    | _, _ => .none

instance divstrict : StrictFun₂ (HDiv.hDiv (α := Option Nat)) where
  isstrict {x y} :=
   match x,y with
   | .some _, .some _ => fun _ => ⟨.intro, .intro⟩
   | .none, _
   | .some _, .none => False.elim

theorem div_existence{x y : Option Nat}: isdef (x / y) -> y ≠ 0 :=
 match x,y with
   | .some x, .some y => by
      intro h
      change isdef (if some y==0 then none else some (x/y)) at h
      split at h
      . apply False.elim h
      . grind
   | .none, _
   | .some _, .none => False.elim

theorem ex1 {x y : Option Nat} : isdef x -> isdef y -> y ≠ 0 -> (x / y) * y <= x := by
  apply isdef_elim ; intro x
  apply isdef_elim ; intro y
  intro h
  change (if some y == 0 then .none else .some (x / y)) * some y ≤ some x
  simp [h] ; change x / y * y ≤ x
  refine (Nat.le_div_iff_mul_le ?_).mp ?_
  . apply Nat.zero_lt_of_ne_zero
    change some y ≠ some 0 at h
    grind
  . apply Nat.le_refl

theorem ex2 {x y : Option Nat} : isdef ((x / y) * y) -> (x / y) * y <= x := by
  intro d₁
  have ⟨d₂,d₃⟩ := isstrict_liftfun₂ d₁
  have ec := div_existence d₂
  have ⟨d₄,_⟩ := StrictFun₂.isstrict d₂
  apply ex1 <;> assumption
