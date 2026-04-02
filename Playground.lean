import PartialSetoid.ForwardBackward
import PartialSetoid.Partial
import PartialSetoid.PartialOption

open Partial
axiom NatBot : Type
axiom zero : NatBot
@[instance] axiom partialNatBot : Partial NatBot

@[instance] axiom divNatBot : Div NatBot
@[instance] axiom addNatBot : Add NatBot
@[instance] axiom mulNatBot : Mul NatBot
@[instance] axiom subNatBot : Sub NatBot

@[instance] axiom divNatBotStrict : StrictFun₂ (· / · : NatBot -> _ -> _)
@[instance] axiom divExistence {n d : NatBot} : Existence (n / d) (d ≠ zero)
@[instance] axiom div_def_b {n m : NatBot} : Backward₁ (n / m)↓ (n↓ ∧ m↓ ∧ m ≠ zero)

@[instance] axiom add_def_b {n m : NatBot} : Backward₁ (n + m)↓ (n↓ ∧ m↓)

example {x y : NatBot} : (x / y)↓ -> ((x + y) / y)↓ := by
 apply elim ; simp ; intros
 apply Backward.intro
 trivial

@[instance] axiom subNatBotStrict : StrictFun₂ (· - · : NatBot -> _ -> _)
@[instance] axiom mul_def_b {n m : NatBot} : Backward₁ (n * m)↓ (n↓ ∧ m↓)
axiom mul_ne_zero {n m : NatBot} : n ≠ zero -> m ≠ zero -> (n * m) ≠ zero

example {x y z: NatBot} : ((x / y) - (y / z))↓ → ((y + z) / (y * z))↓ := by
  apply elim ; simp ; intro _ _ hy _ _ hz
  apply Backward.intro 
  have : y * z ≠ zero := mul_ne_zero hy hz
  trivial

axiom div_def {x y : NatBot} : (x / y)↓ -> x↓ ∧ y↓ ∧ y ≠ zero
axiom def_div {y : NatBot} : y ≠ zero -> ∀ x, x↓ -> (x / y)↓
axiom def_add {x y : NatBot}: x↓ -> y↓ -> (x + y)↓
axiom sub_def {x y : NatBot} : (x - y)↓ -> x↓ ∧ y↓
example {x y z: NatBot} : ((x / y) - (y / z))↓ → ((y + z) / (y * z))↓ := by
  intro h
  have ⟨a₁, a₂⟩ := sub_def h
  have ⟨_, dy, hy⟩ := div_def a₁
  have ⟨_, dz, hz⟩ := div_def a₂
  have h₁: y * z ≠ zero := mul_ne_zero hy hz
  have h₂ := def_add dy dz
  have h₃ := def_div h₁
  specialize h₃ (y + z)
  exact h₃ h₂ 
