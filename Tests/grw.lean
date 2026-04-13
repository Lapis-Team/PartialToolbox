import PartialToolbox.Grw

def rNatZero x y := x ≠ 0 ∧ x = y
def rNatEven x y := x%2 = 0 ∧ x = y

axiom p : Nat -> Prop
axiom p₁ : rNatZero x y → p x ⟶ p y
instance pm₁ [Copy k]: Copy (p₁ k) where
axiom p₂ : rNatEven x y → p x ⟶ p y
instance pm₂ [Copy k]: Copy (p₂ k) where


axiom f: Nat -> Nat
axiom f₁ : rNatZero x y -> rNatZero (f x) (f y)
instance fm₁ [Copy k]: Copy (f₁ k) where
axiom f₂ : rNatEven x y -> rNatEven (f x) (f y)
instance fm₂ [Copy k]: Copy (f₂ k) where

axiom g : Nat -> Nat -> Nat
axiom g₁: rNatZero x x' -> rNatZero y y' -> rNatZero (g x y) (g x' y')
instance gm₁ [Copy k₁] [Copy k₂] : Copy (g₁ k₁ k₂) where

axiom hmul₁ : rNatZero x x' -> rNatZero y y' -> rNatZero (x*y) (x'*y')
instance hmulm₁ [Copy k₁] [Copy k₂] : Copy (hmul₁ k₁ k₂) where

axiom hadd₁ : rNatZero x x' -> rNatZero y y' -> rNatZero (x+y) (x'+y')
instance haddm₁ [Copy k₁] [Copy k₂] : Copy (hadd₁ k₁ k₂) where

axiom le₁ {y': Int}: x ≥ x' -> y ≤ y' → (x ≤ y ⟶ x' ≤ y')
instance lem₁ [Copy k₁] [Copy k₂]: Copy (le₁ k₁ k₂) where
instance : @Reflexive Int LE.le where
 refl := @Int.le_refl

axiom minus₁ : x ≥ y -> -x ≤ -y
instance minusm₁ [Copy k]: Copy (minus₁ k) where
axiom minus₂ : x ≤ y -> -x ≥ -y
instance minusm₂ [Copy k]: Copy (minus₂ k) where

-- set_option trace.Meta.synthInstance true
-- set_option pp.explicit true

example : ∀ x y : Nat, rNatZero x y -> p x -> p y := by
 intro x y h1 h2
 grw h1
 apply h2

example : ∀ x y : Nat, rNatZero x y -> p (f x) -> p (f y) := by
 intro x y h1 h2
 grw h1
 apply h2

example : ∀ x y : Nat, rNatZero x y -> p (f (f x)) -> p (f (f y)) := by
 intro x y h1 h2
 grw h1
 apply h2

example : ∀ x y : Nat, rNatEven x y -> p (f (f x)) -> p (f (f y)) := by
 intro x y h1 h2
 grw h1
 apply h2

example : ∀ x y : Nat, rNatEven (f x) (f y) -> p (f (f x)) -> p (f (f y)) := by
 intro x y h1 h2
 grw h1
 apply h2

example : Reflexive rNatZero -> 2=2 → p z -> p z := by
 intro k h1 h2
 grw h1
 apply h2

example : rNatZero z z -> 2=2 → p z -> p z := by
 intro k h1 h2
 have foo : Proper _ _:= ⟨k⟩
 grw h1
 apply h2

example : ∀ x y z : Nat, rNatZero z z -> rNatZero x y -> p (g (f z) x) -> p (g (f z) y) := by
 intro x y z k h1 h2
 have foo : Proper _ _:= ⟨k⟩
 grw h1
 apply h2

example : ∀ x y z : Nat, rNatZero (f z) (f z) -> rNatZero x y -> p (g (f z) x) -> p (g (f z) y) := by
 intro x y z k h1 h2
 have foo : Proper _ _:= ⟨k⟩
 grw h1
 apply h2

theorem u : ∀ x y z : Nat, rNatZero z z -> rNatZero x y -> p ((x+z)* x) -> p ((y+z) * y) := by
 intro x y z k h1 h2
 --have foo : Proper _ _:= ⟨k⟩
 have goo: ∀r, Proper r z := ?_
 grw h1
 apply h2

#print u
CSC: ora basta cercare goo nel proof term e sostituirlo con la
rel giusta!

example (x: Int): y ≤ y' -> x ≤ y -> x ≤ y' := by
 intro h1 h2
 have foo : Proper GE.ge _:= ⟨Int.le_refl x⟩
 grw h1
 apply h2

example (x: Int): x ≥ x' -> x ≤ y -> x' ≤ y := by
 intro h1 h2
 grw h1
 apply h2

example (x: Int): -x ≥ -x' -> -x ≤ y -> -x' ≤ y := by
 intro h1 h2
 grw h1
 apply h2

example (x: Int): x ≤ x' -> -x ≤ y -> -x' ≤ y := by
 intro h1 h2
 grw h1
 apply h2
