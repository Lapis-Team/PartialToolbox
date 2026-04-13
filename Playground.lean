import PartialSetoid.ForwardBackward
import PartialSetoid.Partial
import PartialSetoid.PartialOption

open Partial

#check Except

instance : Partial (Option α) := ⟨(·.isSome)⟩
instance : Partial (Except ε α) := ⟨(·.isOk)⟩
-- ⟨·.isSome⟩

-------------------- Axiomatic approach for obtaining ℕ⊥ --------------------
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
/- @[instance] axiom divExistence {n d : ℕ⊥} : Existence (n / d) (d ≠ zero) -/
@[instance] axiom divExistence {n d : ℕ⊥} : Existence (n / d) (zero < d)
/- @[instance] axiom div_def_b {n m : ℕ⊥} : Backward₁ (n / m)↓ (n↓ ∧ m↓ ∧ m ≠ zero) -/
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

/- axiom mul_ne_zero {n m : ℕ⊥} : n ≠ zero → m ≠ zero → (n * m) ≠ zero -/
/- example {x y z: ℕ⊥} : ((x / y) - (y / z))↓ → ((x * y + z * z) / (y * z))↓ := by -/
/-   apply elim ; simp ; intros -/
/-   apply Backward.intro ; simp -/
/-   have ⟨hy, hz⟩ : y ≠ zero ∧ z ≠ zero := by trivial -/
/-   have : y * z ≠ zero := mul_ne_zero hy hz -/
/-   trivial -/

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

/- example {x y z: ℕ⊥} : ((x / y) - (y / z))↓ → ((x * y + z * z) / (y * z))↓ := by -/
/-   intro h -/
/-   have ⟨a₁, a₂⟩ := sub_def h -/
/-   have ⟨dx, dy, hy⟩ := div_def a₁ -/
/-   have ⟨_, dz, hz⟩ := div_def a₂ -/
/-   have h₁: y * z ≠ zero := mul_ne_zero hy hz -/
/-   have h₂ := def_add (def_mul dx dy) (def_mul dz dz) -/
/-   have h₃ := def_div h₁ -/
/-   specialize h₃ (x * y + z * z) -/
/-   exact h₃ h₂  -/

--------------------  GRW Example -------------------- 
def R x y := x ≠ 0 ∧ x = y

def P (x: Nat) := ∀ y: Nat, y ≠ 0 -> x * y ≠ 0
theorem p' : R x y -> (P x ↔ P y) := by
  intro ⟨l, r⟩
  constructor
  · rw [← r] ; exact id
  · rw [r] ; exact id
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

set_option pp.proofs true in
example {x y: Nat} 
  [∀ h: R x y, Copy (p' h)] 
  {h' : R (x + x) (y + y)} [Copy h'] 
  : R x y -> P (x + x) → P (y + y) := by
 intro h₁ h₂
 grw h₁

-- FIXME: assioma falso
axiom le₁ {x x' y y': Nat}: x ≥ x' -> y ≤ y' -> (x ≤ y ↔ x' ≤ y')
theorem t1 {x x' y y' : Nat} : x ≥ x' → y ≤ y' -> (x ≤ y ↔ x' ≤ y') := by
  intro h₁ h₂
  constructor
  · grind
  · intros ; apply?
instance [Copy k₁] [Copy k₂]: Copy (le₁ k₁ k₂) where

instance : @Reflexive Nat LE.le where
 refl := @Nat.le_refl

example {x y z: Nat} : x - z ≥ y + z -> x - z ≤ z * z -> y + z ≤ z * z := by
  intro h₁ h₂
  have : Proper GE.ge z := ⟨Nat.le_refl z⟩
  grw h₁

-------------------- RESPECTS TEST --------------------
class Relation (α : Type) where
  rel : α -> α -> Prop

infix:90 " ~ " => Relation.rel

namespace Respect
axiom R : Nat -> Nat -> Prop
axiom P : Nat -> Prop

instance : Relation Nat := ⟨R⟩
axiom a₁ : x ~ y → (P x ↔ P y)
instance [Copy k] : Copy (a₁ k) := ⟨⟩

example : x ~ y -> P x -> P y := by
  intro h₁ h₂
  grw h₁
  assumption

end Respect
