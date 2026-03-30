import PartialSetoid.PartialOption
open Partial Partial.Option

instance : Reflexive (.≤. : Nat -> Nat -> Prop) := ⟨Nat.le_refl _⟩

instance : OfNat (Option Nat) n where ofNat := n
instance : LE (Option Nat) := ⟨liftPred₂ LE.le⟩
instance : Add (Option Nat) := ⟨liftFun₂ Add.add⟩
instance : Mul (Option Nat) := ⟨liftFun₂ Mul.mul⟩
instance : Div (Option Nat) := ⟨liftFun₂ Div.div (dom := fun _ y => y != 0)⟩

instance : Unfoldable (.≤. : Option Nat -> Option Nat -> Prop) (liftPred₂ LE.le) := .id
instance : Unfoldable (.*. : Option Nat -> Option Nat -> Option Nat) (liftFun₂ HMul.hMul) := .id
instance : Unfoldable (.+. : Option Nat -> Option Nat -> Option Nat) (liftFun₂ HAdd.hAdd) := .id
instance : Unfoldable (./. : Option Nat -> Option Nat -> Option Nat) (liftFun₂ HDiv.hDiv (dom := fun _ y => y != 0)) := .id

infix:60 " ◁≤ " => ltor LE.le
infix:60 " ≤▷ " => rtol LE.le
infix:60 " ≥▷ " => rtol GE.ge
infix:60 " ◁≥ " => ltor GE.ge

@[app_unexpander ltor]
meta def ltor.unexpander_le : Lean.PrettyPrinter.Unexpander
  | `($_ LE.le $a $b) => `($a ◁≤ $b)
  | _ => throw ()

@[app_unexpander ltor]
meta def ltor.unexpander_ge : Lean.PrettyPrinter.Unexpander
  | `($_ GE.ge $a $b) => `($a ◁≥ $b)
  | _ => throw ()

@[app_unexpander rtol]
meta def rtol.unexpander_le : Lean.PrettyPrinter.Unexpander
  | `($_ LE.le $a $b) => `($a ≤▷ $b)
  | _ => throw ()

@[app_unexpander rtol]
meta def rtol.unexpander_ge : Lean.PrettyPrinter.Unexpander
  | `($_ GE.ge $a $b) => `($a ≥▷ $b)
  | _ => throw ()

theorem mul_le_morphism₀ {x x' y y' : Option Nat} :
 x ≤ x' -> y ≤ y' -> x*y ≤ x'*y' := by
 apply elim' ; simp
 apply isdef_option_elim ; intro x
 apply isdef_option_elim ; intro x'
 intro (h₁ : x ≤ x')
 apply elim' ; simp
 apply isdef_option_elim ; intro y
 apply isdef_option_elim ; intro y'
 intro (h₂ : y ≤ y')
 change x*y ≤ x' * y'
 apply Nat.mul_le_mul h₁ h₂

theorem mul_le_morphism {x x' y y' : Option Nat} :
 x ≤▷ x' -> y ≤▷ y' -> x*y ≤▷ x'*y' := by
 intro h₁ h₂
 apply elim ; simp ; intro d₁ d₂
 specialize h₁ d₁
 specialize h₂ d₂
 apply mul_le_morphism₀ h₁ h₂

instance [Copy h₁] [Copy h₂] : Copy (mul_le_morphism h₁ h₂) where

-----------------------------------

example {x y : Option Nat}: isdef ((x / y) * y) -> isdef ((y * x * 3) / y) := by
  apply elim ; simp ; intros
  apply Backward.intro ; try simp ; trivial

theorem ex₁' {x y : Option Nat} : isdef x -> isdef y -> y != 0 -> (x / y) * y ≤ x := by
 apply isdef_option_elim ; intro x
 apply isdef_option_elim ; intro y
 intro ec
 rw [liftFun₂_simpl' (g := (./. : Option Nat -> _ -> _)) (by exact ec)]
 apply Nat.div_mul_le_self

theorem ex₁ {x y : Option Nat} : (x / y) * y ◁≤ x := by
  apply elim ; simp ; intros
  apply ex₁' <;> (try simp) <;> trivial

theorem ex₂' {x₁ x₂ y₁ y₂ : Option Nat} :
 isdef x₁ -> isdef x₂ -> isdef y₁ -> isdef y₂ ->
  y₁ != 0 -> y₂ != 0 -> x₁ ≤ x₂ → y₁ ≥ y₂ -> x₁ / y₁ ≤ x₂ / y₂ := by
 apply isdef_option_elim ; intro x₁
 apply isdef_option_elim ; intro x₂
 apply isdef_option_elim ; intro y₁
 apply isdef_option_elim ; intro y₂
 intro ec₁ ec₂ h₁ h₂
 rw [liftFun₂_simpl' (g := (./. : Option Nat -> _ -> _)) (by exact ec₁)]
 rw [liftFun₂_simpl' (g := (./. : Option Nat -> _ -> _)) (by exact ec₂)]
 apply Nat.div_le_div h₁ h₂
 exact bne_iff_ne.mp ec₂

theorem ex₂_aux {x y : Option Nat} : x ≤ y -> x ≠ 0 → y ≠ 0 := by
 apply elim' ; simp
 apply isdef_option_elim ; intro x
 apply isdef_option_elim ; intro y
 intro (k : x ≤ y) h i
 injection i ; apply h ; congr
 grind

theorem ex₂ {x₁ x₂ y₁ y₂ : Option Nat} :
 x₁ ≤▷ x₂ → y₁ ≥▷ y₂ -> x₁ / y₁ ≤▷ x₂ / y₂ := by
 intro hx hy
 apply elim ; simp ; intro dx dy ec
 specialize hx dx ; apply elim _ hx ; simp ; intro d₁ d₂
 specialize hy dy ; have hy' : y₂ ≤ y₁ := hy ; apply elim _ hy' ; simp ; intro d₃ d₄
 apply ex₂' <;> try assumption
 . have := ex₂_aux hy ec
   grind
 . exact bne_iff_ne.mpr ec

theorem ex₄ {x : Option Nat}: x ≈▷ x / 1 := by
 apply elim ; simp ; apply isdef_option_elim ; intro x _ _
 constructor
 . trivial
 . congr
   change x = x / 1
   simp

theorem ex₅_aux {y: Option Nat} : 1 ≤ y → y != 0 := by
 apply elim' ; simp ; intro _ ; apply isdef_option_elim ; intro x h
 intro k ; rw [k] at h
 contradiction

theorem ex₅ {x y z : Option Nat} : isdef x → w ≥▷ y → z ≤▷ y -> y ≥ 1 -> (x / w) * z ≤ x := by
 intro d₁ h₁ h₂
 change 1 ≤ y → _ ; apply elim' ; simp ; intro _ d₂ h₃
 calc
       (x / w) * z
  _ ≤▷ (x / w) * y := by respects h₂
  _ ≤▷ (x / y) * y := by respects (ex₂ (Reflexive.refl : x ≤▷x) h₁)
  _ ≈  (x / y) * y := by
                       apply def_peqrfl
                       apply Backward.intro <;> and_intros <;> try trivial
                       exact ex₅_aux h₃
  _ ◁≤ x           := ex₁
