-----------------

class Copy (what: α) (with_what: α) (rel: α -> α -> Prop) (rel': β → β → Prop) (h: rel what with_what) (lhs: outParam β) (rhs: β) (out: outParam (rel' lhs rhs)) where

def take (h: r x y): [Copy x y r r' h lhs rhs k] -> r' lhs rhs := k

instance found: Copy x y r r h x y h where

class Reflexive (rel: α -> α -> Prop) where
  refl : rel x x

class Proper (rel: α -> α -> Prop) (x: α) where
 is_proper: rel x x

instance [h: Reflexive rel] : Proper rel x where
 is_proper := h.refl

instance rr [k: Proper r' z] : Copy x y r r' rxy z z k.is_proper where

-----------------

def rNatZero x y := x ≠ 0 ∧ x = y
def rNatEven x y := x%2 = 0 ∧ x = y

axiom p : Nat -> Prop
axiom p₁ : rNatZero x y -> (p x ↔ p y)
instance pm₁ [Copy x y r rNatZero rxy lhs₂ rhs₂ k₂]: Copy x y r Iff rxy (p lhs₂) (p rhs₂) (p₁ k₂) where
axiom p₂ : rNatEven x y -> (p x ↔ p y)
instance pm₂ [Copy x y r rNatEven rxy lhs₂ rhs₂ k₂]: Copy x y r Iff rxy (p lhs₂) (p rhs₂) (p₂ k₂) where


axiom f: Nat -> Nat
axiom f₁ : rNatZero x y -> rNatZero (f x) (f y)
instance fm₁ [Copy x y r rNatZero rxy lhs₂ rhs₂ k₂]: Copy x y r rNatZero rxy (f lhs₂) (f rhs₂) (f₁ k₂) where
axiom f₂ : rNatEven x y -> rNatEven (f x) (f y)
instance fm₂ [Copy x y r rNatEven rxy lhs₂ rhs₂ k₂]: Copy x y r rNatEven rxy (f lhs₂) (f rhs₂) (f₂ k₂) where

axiom g : Nat -> Nat -> Nat
axiom g₁: rNatZero x x' -> rNatZero y y' -> rNatZero (g x y) (g x' y')
instance gm₁
 [Copy x y r rNatZero rxy lhs₂ rhs₂ k₂]
 [Copy x y r rNatZero rxy lhs₂' rhs₂' k₂']
 : Copy x y r rNatZero rxy (g lhs₂ lhs₂') (g rhs₂ rhs₂') (g₁ k₂ k₂') where

set_option trace.Meta.synthInstance true

example : ∀ x y : Nat, rNatZero x y -> p x -> p y := by
 intro x y h1 h2
 apply Iff.mp
 apply take h1
 apply h2

example : ∀ x y : Nat, rNatZero x y -> p (f x) -> p (f y) := by
 intro x y h1 h2
 apply Iff.mp
 apply take h1
 apply h2

example : ∀ x y : Nat, rNatZero x y -> p (f (f x)) -> p (f (f y)) := by
 intro x y h1 h2
 apply Iff.mp
 apply take h1
 apply h2

example : ∀ x y : Nat, rNatEven x y -> p (f (f x)) -> p (f (f y)) := by
 intro x y h1 h2
 apply Iff.mp
 apply take h1
 apply h2

example : ∀ x y : Nat, rNatEven (f x) (f y) -> p (f (f x)) -> p (f (f y)) := by
 intro x y h1 h2
 apply Iff.mp
 apply take h1
 apply h2

example : Reflexive rNatZero -> 2=2 → p z -> p z := by
 intro k h1 h2
 apply Iff.mp
 apply take h1
 apply h2

example : rNatZero z z -> 2=2 → p z -> p z := by
 intro k h1 h2
 have foo : Proper _ _:= ⟨k⟩
 apply Iff.mp
 apply take h1
 apply h2

example : ∀ x y z : Nat, rNatZero z z -> rNatZero x y -> p (g (f z) x) -> p (g (f z) y) := by
 intro x y z k h1 h2
 have foo : Proper _ _:= ⟨k⟩
 apply Iff.mp
 apply take h1
 apply h2
