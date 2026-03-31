import PartialSetoid.ForwardBackward
import PartialSetoid.Partial

postfix:90 "↓" => Partial.isdef

open Partial
@[instance] axiom instPartialOfNat : Partial Nat

@[instance] axiom sub_def_b {n m : Nat} : Backward₁ (isdef (n - m)) (isdef n ∧ isdef m)
@[instance] axiom sub_def_strict : StrictFun₂ (. - . : Nat -> Nat -> Nat)

@[instance] axiom div_def_b {n m : Nat} : Backward₁ (isdef (n / m)) (isdef n ∧ isdef m ∧ m ≠ 0)
@[instance] axiom div_def_strict : StrictFun₂ (. / . : Nat -> Nat -> Nat)
@[instance] axiom div_existence {n d : Nat} : Existence (n / d) (d ≠ 0)

@[instance] axiom mul_def_b {n m : Nat} : Backward₁ (isdef (n * m)) (isdef n ∧ isdef m)
@[instance] axiom mul_def_strict : StrictFun₂ (. * . : Nat -> Nat -> Nat)

@[instance] axiom add_def_b {n m : Nat} : Backward₁ (isdef (n + m)) (isdef n ∧ isdef m)
@[instance] axiom add_def_stict : StrictFun₂ (· + · : Nat -> Nat -> Nat)

example {x y : Nat} : (x / y)↓ -> ((x + y) / y)↓ := by
 apply elim ; simp ; intros
 apply Backward.intro
 trivial

example {x y : Nat} : ((x / y) - (y / z))↓ → ((y + z) / (y * z))↓ := by
  apply elim ; simp ; intro _ _ hy _ _ hz
  apply Backward.intro 
  have : y * z ≠ 0 := Nat.mul_ne_zero hy hz
  trivial

axiom div_def {x y : Nat} : (x / y)↓ → x↓ ∧ y↓ ∧ y ≠ 0
axiom def_div {y : Nat} : y ≠ 0 → ∀ x, x↓ → (x / y)↓
axiom def_add {x y : Nat}: x↓ → y↓ → (x + y)↓
axiom sub_def {x y : Nat} : (x - y)↓ → x↓ ∧ y↓
example {x y : Nat} : ((x / y) - (y / z))↓ → ((y + z) / (y * z))↓ := by
  intro h
  have ⟨a₁, a₂⟩ := sub_def h
  have ⟨_, dy, hy⟩ := div_def a₁
  have ⟨_, dz, hz⟩ := div_def a₂
  have h₁: y * z ≠ 0 := Nat.mul_ne_zero hy hz
  have h₂ := def_add dy dz
  have h₃ := def_div h₁
  specialize h₃ (y + z)
  exact h₃ h₂ 
