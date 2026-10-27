/-
This file contains a number of minimal examples that can be found in the paper 
"A Toolbox for Undefined Terms in Type Theory" written by Pizzo and Sacerdoti Coen.

- The examples are isolated in proper namespaces, as to enusre self-containment.

- We expose an empty namespace `Playground`, so that anyone who wants to try the toolbox
    over some custom examples can easily do so.

-/
import PartialToolbox.ForwardBackward
import PartialToolbox.Partial
import PartialToolbox.PartialOption
import PartialToolbox.Unfoldable

namespace Playground
open Partial

-- Put your own code here

end Playground


-------------------- An axiomatization of arithmetic over ℕ⊥ --------------------

namespace AxiomNat

open Partial
axiom NatBot : Type
scoped notation "ℕ⊥" => NatBot
axiom zero : ℕ⊥
@[instance] axiom partialNatBot : Partial ℕ⊥
@[instance] axiom instLEOfNatBot : LE ℕ⊥
@[instance] axiom instLTOfNatBot : LT ℕ⊥

@[instance] axiom divNatBot : Div ℕ⊥
@[instance] axiom addNatBot : Add ℕ⊥
@[instance] axiom mulNatBot : Mul ℕ⊥
@[instance] axiom subNatBot : Sub ℕ⊥

@[instance] axiom divNatBotStrict : StrictFun₂ (· / · : ℕ⊥ → _ → _)
@[instance] axiom divExistence {n d : ℕ⊥} : Existence (n / d) (zero < d)
@[instance] axiom div_def_b {n m : ℕ⊥} : Backward₁ (n / m)↓ (n↓ ∧ m↓ ∧ zero < m)

@[instance] axiom add_def_b {n m : ℕ⊥} : Backward₁ (n + m)↓ (n↓ ∧ m↓)
@[instance] axiom sub_def_b {n m : ℕ⊥} : Backward₁ (n - m)↓ (n↓ ∧ m↓ ∧ n <= m)

example {x y : ℕ⊥} : (x / y)↓ → ((x + y) / y)↓ := by
 apply elim ; simp ; intros
 apply Backward.intro
 trivial

@[instance] axiom addNatBotStrict : StrictFun₂ (· + · : ℕ⊥ → _ → _)
@[instance] axiom subNatBotStrict : StrictFun₂ (· - · : ℕ⊥ → _ → _)
@[instance] axiom subExistence {n m : ℕ⊥}: Existence (n - m) (m <= n)
@[instance] axiom mul_def_b {n m : ℕ⊥} : Backward₁ (n * m)↓ (n↓ ∧ m↓)

axiom mul_gt_zero {n m : ℕ⊥} : zero < n → zero < m → zero < (n * m)
example {x y z: ℕ⊥} : ((x / y) - (y / z))↓ → ((x * y + z * z) / (y * z))↓ := by
  apply elim ; simp ; intros
  apply Backward.intro ; simp
  have ⟨hy, hz⟩ : zero < y ∧ zero < z := by trivial
  have : zero < y * z := mul_gt_zero hy hz
  trivial

axiom div_def {x y : ℕ⊥} : (x / y)↓ -> x↓ ∧ y↓ ∧ zero < y
axiom def_div {y : ℕ⊥} : zero < y -> ∀ x, x↓ -> (x / y)↓
axiom def_add {x y : ℕ⊥}: x↓ -> y↓ -> (x + y)↓
axiom sub_def {x y : ℕ⊥} : (x - y)↓ -> x↓ ∧ y↓
axiom def_mul {x y : ℕ⊥} : x↓ -> y↓ -> (x * y)↓
example {x y z: ℕ⊥} : ((x / y) - (y / z))↓ → ((x * y + z * z) / (y * z))↓ := by
  intro h
  have ⟨a₁, a₂⟩ := sub_def h
  have ⟨dx, dy, hy⟩ := div_def a₁
  have ⟨_, dz, hz⟩ := div_def a₂
  have h₁: zero < y * z := mul_gt_zero hy hz
  have h₂ := def_add (def_mul dx dy) (def_mul dz dz)
  have h₃ := def_div h₁
  specialize h₃ (x * y + z * z)
  exact h₃ h₂ 

end AxiomNat

--------------------  GRW Example -------------------- 

namespace GeneralizedRewriting

def R x y := x ≠ 0 ∧ x = y

def P (x: Nat) := ∀ y: Nat, y ≠ 0 -> x * y ≠ 0
theorem p' : R x y -> (P x ⟶ P y) := by
  intro ⟨l, r⟩
  rw [r] ; exact id
instance [Copy k] : Copy (p' k) where

theorem addR : R x₁ x₂ → R y₁ y₂ → R (x₁ + y₁) (x₂ + y₂) := by
  intro h₁ h₂
  constructor
  · have : x₁ ≠ 0 ∧ y₁ ≠ 0 := ⟨h₁.left, h₂.left⟩
    simp_all
  · have : x₁ = x₂ ∧ y₁ = y₂ := ⟨h₁.right, h₂.right⟩
    simp_all
instance [Copy k₁] [Copy k₂] : Copy (addR k₁ k₂) where

example {x y: Nat} : R x y → P (x + x) → P (y + y) := by
 intro h₁ h₂  
 grw h₁
 apply h₂

example (h : R x y) : P (x + x) → P (y + y) := by
  intro _
  grw h
  assumption

theorem proper (h : x ≠ 0) : Proper R x := ⟨⟨h, rfl⟩⟩
example (h : R x y) (hz : z ≠ 0): P (x + z) → P (y + z) := by
  intros
  have := proper hz
  grw h
  assumption

example {x y: Nat} 
  [∀ h: R x y, Copy (p' h)] 
  {h' : R (x + x) (y + y)} [Copy h'] 
  : R x y -> P (x + x) → P (y + y) := by
 intro h₁ h₂
 grw h₁
 assumption

end GeneralizedRewriting

-------------------- Lifting Example --------------------

namespace Lifting

open Partial Option

scoped notation "ℕ" => Nat
scoped notation "ℕ⊥" => Option Nat

/-
instance : Partial (Option α) where
 isdef
  | .none => False
  | .some _ => True
-/

instance : OfNat ℕ⊥ n := ⟨n⟩

-- Function lifting
instance : Mul ℕ⊥ := ⟨liftFun₂ Mul.mul⟩
instance : Div ℕ⊥ := ⟨liftFun₂ Div.div (dom := fun _ y => y != 0)⟩

-- Predicate lifting
instance : LT ℕ⊥ := ⟨liftPred₂ LT.lt⟩

instance : Unfoldable (· < · : ℕ⊥ → _ → _) (liftPred₂ LT.lt) := .id
instance : Unfoldable (./. : ℕ⊥ → ℕ⊥ → ℕ⊥) (liftFun₂ HDiv.hDiv (dom := fun _ y => y != 0)) := .id
instance : Unfoldable (.*. : ℕ⊥ → ℕ⊥ → ℕ⊥) (liftFun₂ HMul.hMul) := .id

#check Nat.mul_pos
theorem mul_pos {x y : ℕ⊥} : 0 < x → 0 < y → 0 < x * y := by 
  elim _ _ x _ h₁
  elim _ _ y _ h₂
  exact Nat.mul_pos h₁ h₂

#check Nat.div_mul_le_self
theorem div_mul_le_self {m n : ℕ⊥} : m↓ -> n↓ -> n ≠ 0 -> (m / n) * n ≤ m := by
 elim m _ _
 elim n _ _ ec
 simp_all
 apply Nat.div_mul_le_self

-- Lifting example over ℚ

scoped notation "ℚ" => Rat
scoped notation "ℚ⊥" => Option Rat
instance : OfNat ℚ⊥ n := ⟨(n : ℚ)⟩

-- Function lifting
instance : Mul ℚ⊥ := ⟨liftFun₂ Mul.mul⟩
instance : Div ℚ⊥ := ⟨liftFun₂ Div.div (dom := fun _ y => y ≠ 0)⟩

-- Predicate lifting
instance : LT ℚ⊥ := ⟨liftPred₂ LT.lt⟩

instance : Unfoldable (./. : ℚ⊥ → ℚ⊥ → ℚ⊥) (liftFun₂ HDiv.hDiv (dom := fun _ y => y ≠ 0)) := .id
instance : Unfoldable (.*. : ℚ⊥ → ℚ⊥ → ℚ⊥) (liftFun₂ HMul.hMul) := .id

-- Numerals in ℚ⊥ are the injections of numerals in ℚ
@[simp] theorem ofNat_some : (OfNat.ofNat n : ℚ⊥) = some (OfNat.ofNat n : ℚ) := rfl

example {x y : ℚ} : y ≠ 0 → (x / y) * y = x := by 
  exact Rat.div_mul_cancel

example {x y : ℚ⊥} : x↓ → y↓ → y ≠ 0 → (x / y) * y = x := by 
  elim x _ h₁
  elim y _ h₂
  elim ec
  simp_all
  apply Rat.div_mul_cancel ec


end Lifting
