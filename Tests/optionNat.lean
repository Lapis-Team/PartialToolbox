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

infix:60 " ◁≤ " => ltor LE.le
infix:60 " ≤▷ " => rtol LE.le
infix:60 " ≥▷ " => rtol GE.ge
infix:60 " ◁≥ " => ltor GE.ge

@[app_unexpander ltor]
meta def ltor.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ LE.le $a $b) => `($a ◁≤ $b)
  | `($_ GE.ge $a $b) => `($a ◁≥ $b)
  | _ => throw ()

@[app_unexpander rtol]
meta def rtol.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ LE.le $a $b) => `($a ≤▷ $b)
  | `($_ GE.ge $a $b) => `($a ≥▷ $b)
  | _ => throw ()

example {x y : Option Nat}: isdef ((x / y) * y) -> isdef ((y * x * 3) / y) := by
  apply elim ; simp ; intros
  apply Backward.intro ; try simp ; trivial

theorem ex₁ {x y : Option Nat} : isdef x -> isdef y -> y != 0 -> (x / y) * y ≤ x := by
  apply isdef_option_elim ; intro x
  apply isdef_option_elim ; intro y
  intro h
  change (if some y != 0 then .some (x / y) else .none) * some y ≤ some x
  simp [h] ; change x / y * y ≤ x
  refine (Nat.le_div_iff_mul_le ?_).mp ?_
  . apply Nat.zero_lt_of_ne_zero
    exact bne_iff_ne.mp h
  . apply Nat.le_refl

theorem ex₂ {x y : Option Nat} : (x / y) * y ◁≤ x := by
  apply elim ; simp ; intros
  apply ex₁ <;> (try simp) <;> trivial

theorem ex₃ {x₁ x₂ y₁ y₂ : Option Nat} :
 x₁ ≤▷ x₂ → y₁ ≥▷ y₂ -> x₁ / y₁ ≤▷ x₂ / y₂ := by
 intro hx hy
 apply elim ; simp ; intro dx dy ec
 specialize hx dx
 specialize hy dy
 rcases x₁ with ⟨⟩|x₁ ; apply hx.elim
 rcases x₂ with ⟨⟩|x₂ ; apply hx.elim
 rcases y₂ with ⟨⟩|y₂ ; apply hy.elim
 rcases y₁ with ⟨⟩|y₁ ; apply hy.elim
 change x₁ ≤ x₂ at hx
 change y₁ ≥ y₂ at hy
 have ec' : some y₁ != 0 := by
  have : y₂ ≠ 0 := by exact fun a => ec (congrArg some a)
  have : y₁ ≠ 0 := by grind
  have : some y₁ ≠ some 0 := by grind
  simp ; congr
 change ((if some y₁ != 0 then some (x₁/y₁) else none) ≤ (if some y₂ != 0 then some (x₂/y₂) else none))
 simp [ec, ec']
 change x₁ / y₁ ≤ x₂ / y₂
 exact Nat.div_le_div hx hy fun a => ec (congrArg some a)

theorem ex₄ {x : Option Nat}: x ◁≈ x / 1 := by
 apply isdef_option_elim ; simp ;  intro x
 constructor
 . trivial
 . congr
   change x = x / 1
   simp

theorem ex₅ {x y : Option Nat} : 1 ≤ y -> x * y ≤ x := by
 intro h
 calc
      x * y
  _ ≈ (x / 1) * y := sorry
  _ ≤▷ (x / y) * y := sorry
  _ ≈ (x /y ) * y := sorry
  _ ◁≤ x := sorry
