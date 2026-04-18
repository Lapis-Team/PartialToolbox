import PartialToolbox.ForwardBackward
import PartialToolbox.Partial
import PartialToolbox.PartialOption
import PartialToolbox.Unfoldable

namespace Playground
open Partial

-- Put your own code here

end Playground


-------------------- Axiomatic approach for obtaining ℕ⊥ --------------------

namespace AxiomNat

open Partial
axiom NatBot : Type
notation "ℕ⊥" => NatBot
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

def proper (h : x ≠ 0) : Proper R x := ⟨⟨h, rfl⟩⟩
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

-------------------- Simple example Lifting --------------------

namespace Lifting

open Partial Option

instance : OfNat (Option Nat) n := ⟨n⟩

instance : Mul (Option Nat) := ⟨liftFun₂ Mul.mul⟩
instance : LT (Option Nat) := ⟨liftPred₂ LT.lt⟩
instance : Unfoldable (· < · : Option Nat → _ → _) (liftPred₂ LT.lt) := .id

macro "elim₁" x:ident h:ident : tactic => 
  `(tactic| apply elim' <;> simp <;> intro _ <;> apply isdef_option_elim <;> intro $x:ident $h:ident)

theorem mul_gt_zero {x y : Option Nat} : 0 < x → 0 < y → 0 < x * y := by 
  elim₁ x h₁
  elim₁ y h₂
  exact Nat.mul_pos h₁ h₂

end Lifting

----------------------------------------------------------------
