import PartialToolbox.PartialOption
import PartialToolbox.Unfoldable
open Partial -- Partial.Option

section

open Partial.Option

instance : Reflexive (.≤. : Nat -> Nat -> Prop) := ⟨Nat.le_refl _⟩

instance nat_of_option : OfNat (Option Nat) n where ofNat := n

@[simp]
theorem natlit_some (x : Nat): OfNat.ofNat x = some x := Eq.refl _

instance : LE (Option Nat) := ⟨liftPred₂ LE.le⟩
instance : Add (Option Nat) := ⟨liftFun₂ Add.add⟩
instance : Mul (Option Nat) := ⟨liftFun₂ Mul.mul⟩
instance : Div (Option Nat) := ⟨liftFun₂ Div.div (dom := fun _ y => y != 0)⟩

instance : Unfoldable (.≤. : Option Nat -> Option Nat -> Prop) (liftPred₂ LE.le) := .id
instance : Unfoldable (. ≥ . : Option Nat -> _ -> Prop) (liftPred₂ (fun x y => y≤x)) := by
 have eq : (. ≥ . : Option Nat -> _ -> Prop) = liftPred₂ (fun x y : Nat => y ≤ x) := by
  funext x y
  cases x <;> cases y <;> unfold GE.ge <;> unfold LE.le
   <;> simp [instLEOptionNat_tests, liftPred₂] <;> trivial
 rw [eq]
 exact .id
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

end

open Partial.Option in
theorem mul_le_morphism₀ {x x' y y' : Option Nat} :
 x ≤ x' -> y ≤ y' -> x*y ≤ x'*y' := by
 elim x _ x' _ h₁
 elim y _ y' _ h₂
 apply Nat.mul_le_mul h₁ h₂

theorem mul_le_morphism {x x' y y' : Option Nat} :
 x ≤▷ x' -> y ≤▷ y' -> x*y ≤▷ x'*y' := by
 intro h₁ h₂
 elim d₁ d₂ _
 specialize h₁ d₁
 specialize h₂ d₂
 apply mul_le_morphism₀ h₁ h₂

instance [Copy h₁] [Copy h₂] : Copy (mul_le_morphism h₁ h₂) where

-----------------------------------

example {x y : Option Nat}:  ((x / y) * y)↓ -> ((y * x * 3) / y)↓ := by
  elim
  apply Backward.intro ; try simp ; trivial

open Partial.Option in
theorem div_mul_le_self {x y : Option Nat} : x↓ -> y↓ -> y ≠ 0 -> (x / y) * y ≤ x := by
 elim x _ _
 elim y _ _ ec
 simp_all
 apply Nat.div_mul_le_self

theorem div_mul_le_self_dir {x y : Option Nat} : (x / y) * y ◁≤ x := by
  elim
  apply div_mul_le_self <;> simpa

open Partial.Option in
theorem ex₂' {x₁ x₂ y₁ y₂ : Option Nat} :
  x₁ ≤ x₂ → y₁ ≥ y₂ -> y₁ != 0 -> y₂ != 0 -> x₁ / y₁ ≤ x₂ / y₂ := by
 elim x₁ _ x₂ _ h₁
 elim y₁ _ y₂ _ h₂
 intro ec₁ ec₂
 simp [ec₁,ec₂]
 apply Nat.div_le_div h₁ h₂
 simp_all

open Partial.Option in
theorem ex₂_aux {x y : Option Nat} : x ≤ y -> x ≠ 0 → y ≠ 0 := by
 elim x _ y _ k
 change x ≤ y at k
 intro h i
 injection i ; apply h ; congr
 grind

theorem ex₂ {x₁ x₂ y₁ y₂ : Option Nat} :
 x₁ ≤▷ x₂ → y₁ ≥▷ y₂ -> x₁ / y₁ ≤▷ x₂ / y₂ := by
 intro hx hy
 elim dx dy ec _
 specialize hx dx
 specialize hy dy
 have := ex₂_aux hy ec
 apply ex₂' <;> simpa

open Partial.Option in
theorem ex₅_aux {y: Option Nat} : 1 ≤ y → y ≠ 0 := by
 elim y _ h
 intro k ; rw [k] at h
 contradiction

theorem ex₅ {x y z : Option Nat} : x↓ → w ≥▷ y → z ≤▷ y -> y ≥ 1 -> (x / w) * z ≤ x := by
 intro d₁ h₁ h₂
 elim d₂ _ h₃
 calc
       (x / w) * z
  _ ≤▷ (x / w) * y := by respects h₂
  _ ≤▷ (x / y) * y := by respects (ex₂ (Reflexive.refl : x ≤▷x) h₁)
  _ ≈  (x / y) * y := by
                       apply def_peqrfl
                       apply Backward.intro <;> and_intros <;> try trivial
                       simp ; exact ex₅_aux h₃
  _ ◁≤ x           := div_mul_le_self_dir

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
