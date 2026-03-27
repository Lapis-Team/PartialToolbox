import PartialSetoid.PartialOption
open Partial Partial.Option

instance : OfNat (Option Nat) n where ofNat := n
instance : LE (Option Nat) := ⟨liftPred₂ LE.le⟩
instance : Add (Option Nat) := ⟨liftFun₂ Add.add⟩
instance : Mul (Option Nat) := ⟨liftFun₂ Mul.mul⟩
instance : Div (Option Nat) := ⟨liftFun₂ Div.div (dom := fun _ y => y != 0)⟩

instance : Unfoldable (.≤. : Option Nat -> Option Nat -> Prop) (liftPred₂ LE.le) := .id
instance : Unfoldable (.*. : Option Nat -> Option Nat -> Option Nat) (liftFun₂ Mul.mul) := .id
instance : Unfoldable (.+. : Option Nat -> Option Nat -> Option Nat) (liftFun₂ Add.add) := .id
instance : Unfoldable (./. : Option Nat -> Option Nat -> Option Nat) (liftFun₂ Div.div (dom := fun _ y => y != 0)) := .id

theorem ex₁ {x y : Option Nat} : isdef x -> isdef y -> y != 0 -> (x / y) * y <= x := by
  apply isdef_option_elim ; intro x
  apply isdef_option_elim ; intro y
  intro h
  change (if some y != 0 then .some (x / y) else .none) * some y ≤ some x
  simp [h] ; change x / y * y ≤ x
  refine (Nat.le_div_iff_mul_le ?_).mp ?_
  . apply Nat.zero_lt_of_ne_zero
    exact bne_iff_ne.mp h
  . apply Nat.le_refl

theorem ex₂ {x y : Option Nat} : isdef ((x / y) * y) -> (x / y) * y <= x := by
  apply elim ; simp ; intros
  apply ex₁ <;> (try simp) <;> trivial

theorem ex₃ {x y : Option Nat}: isdef ((x / y) * y) -> isdef ((y * x * 3) / y) := by
  apply elim ; simp ; intros
  apply Backward.intro ; try simp ; trivial
