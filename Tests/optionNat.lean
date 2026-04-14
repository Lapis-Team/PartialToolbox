import PartialToolbox.PartialOption
import PartialToolbox.Unfoldable
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

infix:60 " ◁≤ " => ◁LE.le
infix:60 " ≤▷ " => LE.le▷
infix:60 " ≥▷ " => GE.ge▷
infix:60 " ◁≥ " => ◁GE.ge

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

macro "elim_p₂" x:ident y:ident h:ident  : tactic =>
 `(tactic|apply elim' <;> simp <;> apply isdef_option_elim <;> intro $x:ident <;> apply isdef_option_elim <;> intro $y:ident <;> intro $h:ident)

theorem mul_le_morphism₀ {x x' y y' : Option Nat} :
 x ≤ x' -> y ≤ y' -> x*y ≤ x'*y' := by
 elim_p₂ x x' h₁
 elim_p₂ y y' h₂
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

example {x y : Option Nat}:  ((x / y) * y)↓ -> ((y * x * 3) / y)↓ := by
  apply elim ; simp ; intros
  apply Backward.intro ; try simp ; trivial

theorem ex₁' {x y : Option Nat} : x↓ -> y↓ -> y != 0 -> (x / y) * y ≤ x := by
 apply isdef_option_elim ; intro x
 apply isdef_option_elim ; intro y
 intro ec
 rw [liftFun₂_simpl' (g := (./. : Option Nat -> _ -> _)) (by exact ec)]
 apply Nat.div_mul_le_self

theorem ex₁ {x y : Option Nat} : (x / y) * y ◁≤ x := by
  apply elim ; simp ; intros
  apply ex₁' <;> simpa

theorem ex₂' {x₁ x₂ y₁ y₂ : Option Nat} :
  x₁ ≤ x₂ → y₁ ≥ y₂ -> y₁ != 0 -> y₂ != 0 -> x₁ / y₁ ≤ x₂ / y₂ := by
 elim_p₂ x₁ x₂ h₁
 elim_p₂ y₁ y₂ h₂
 intro ec₁ ec₂
 rw [liftFun₂_simpl' (g := (./. : Option Nat -> _ -> _)) (by simpa)]
 rw [liftFun₂_simpl' (g := (./. : Option Nat -> _ -> _)) (by simpa)]
 apply Nat.div_le_div h₁ h₂
 intro a ; apply ec₂ ; congr

theorem ex₂_aux {x y : Option Nat} : x ≤ y -> x ≠ 0 → y ≠ 0 := by
 elim_p₂ x y k
 change x ≤ y at k
 intro h i
 injection i ; apply h ; congr
 grind

theorem ex₂ {x₁ x₂ y₁ y₂ : Option Nat} :
 x₁ ≤▷ x₂ → y₁ ≥▷ y₂ -> x₁ / y₁ ≤▷ x₂ / y₂ := by
 intro hx hy
 apply elim ; simp ; intro dx dy ec
 specialize hx dx
 specialize hy dy
 have := ex₂_aux hy ec
 apply ex₂' <;> simpa

theorem ex₅_aux {y: Option Nat} : 1 ≤ y → y ≠ 0 := by
 apply elim' ; simp ; intro _ ; apply isdef_option_elim ; intro y h
 intro k ; rw [k] at h
 contradiction

theorem ex₅ {x y z : Option Nat} : x↓ → w ≥▷ y → z ≤▷ y -> y ≥ 1 -> (x / w) * z ≤ x := by
 intro d₁ h₁ h₂
 change 1 ≤ y → _ ; apply elim' ; simp ; intro _ d₂ h₃
 calc
       (x / w) * z
  _ ≤▷ (x / w) * y := by respects h₂
  _ ≤▷ (x / y) * y := by respects (ex₂ (Reflexive.refl : x ≤▷x) h₁)
  _ ≈  (x / y) * y := by
                       apply def_peqrfl
                       apply Backward.intro <;> and_intros <;> try trivial
                       simp ; exact ex₅_aux h₃
  _ ◁≤ x           := ex₁

  -----------------------------------------------
/-
  @[simp]
  axiom liftPred₂_simpl {f : α → β → Prop}
   [u: Unfoldable g (Partial.Option.liftPred₂ f)] : g (some x) (some y) ↔ f x y

  example : x ≤ some 4 -> (∃ y, x = some y) -> x ≤ (x * 1) := by
   simp ; intro h y k ; subst_vars ; simp_all

  example {x y z : Option Nat}: isdef y → z ≤ x → x + y - z ≥ y := by
   calc
         x + y - z
    _ ≈▷ x - z + y := sorry
    _ ◁≥ 0 + y     := sorry
    _ ◁≈ y         := sorry
-/
