-----------------

class Copy {rel: outParam β → β → Prop} {lhs: outParam β} {rhs: β} (out: outParam (rel lhs rhs)) where

def put k : @Copy _ r lhs rhs k := by constructor

def take : [@Copy _ r lhs rhs k] -> r lhs rhs := k

class Reflexive (rel: α -> α -> Prop) where
  refl : rel x x

class Proper (rel: α -> α -> Prop) (x: α) where
 is_proper: rel x x

instance [h: Reflexive rel] : Proper rel x where
 is_proper := h.refl

instance rr [k: Proper r z] : Copy k.is_proper where

macro "grw" h:term ("fixing")? : tactic => `(tactic | have := put $h <;> apply Iff.mp take)

-----------------

def rNatZero x y := x ≠ 0 ∧ x = y
def rNatEven x y := x%2 = 0 ∧ x = y

axiom p : Nat -> Prop
axiom p₁ : rNatZero x y -> (p x ↔ p y)
instance pm₁ [Copy k]: Copy (p₁ k) where
axiom p₂ : rNatEven x y -> (p x ↔ p y)
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

axiom le₁ {y': Int}: x ≥ x' -> y ≤ y' -> (x ≤ y ↔ x' ≤ y')
instance lem₁ [Copy k₁] [Copy k₂]: Copy (le₁ k₁ k₂) where
instance : @Reflexive Int LE.le where
 refl := @Int.le_refl

axiom minus₁ : x ≥ y -> -x ≤ -y
instance minusm₁ [Copy k]: Copy (minus₁ k) where
axiom minus₂ : x ≤ y -> -x ≥ -y
instance minusm₂ [Copy k]: Copy (minus₂ k) where

set_option trace.Meta.synthInstance true
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

-----------------------------------------

abbrev Partial := Option

def peq (x y: Partial α) : Prop :=
 x ≠ .none ∧ x=y

abbrev defined (x: Partial α) := Proper peq x

theorem defined_not_none{x: Partial α} : defined x -> x ≠ .none
 | ⟨⟨k,_⟩⟩ => k

theorem not_none_defined {x: Partial α} : x ≠ .none -> defined x := by
 intro h ; constructor ; constructor ; assumption ; eq_refl

instance : defined (.some x) where
 is_proper := by constructor <;> simp

theorem peq_symm: peq x y -> peq y x
 | ⟨h1,h2⟩ => by constructor <;> grind

theorem peq_defined₁ {x y : Partial α} (h : peq x y) : defined x where
 is_proper := by constructor <;> first | grind | apply h.left

theorem peq_defined₂ {x y : Partial α} (h : peq x y) : defined y :=
 by apply peq_defined₁ (peq_symm h)

theorem peq_eq {x y : Partial α} : peq x y -> x = y
 | ⟨_,h⟩ => h

theorem defined_eq_peq₁ {x y : Partial α} : defined x -> x=y -> peq x y := by
 intro h₁ h₂ ; constructor ; simp [defined_not_none] ; assumption

theorem defined_eq_peq₂ {x y : Partial α} : defined y -> x=y -> peq x y :=
 fun h₁ h₂ => peq_symm (defined_eq_peq₁ h₁ h₂.symm)

theorem peq_trans : peq x y -> peq y z -> peq x z
 | ⟨h₁,h₂⟩,⟨_,k⟩ => ⟨h₁, Eq.trans h₂ k⟩

---------------------------------------------

class Strict₂ (op : Partial α -> Partial β -> Partial γ) where
 is_strict₁ : defined (op x y) -> defined x
 is_strict₂ : defined (op x y) -> defined x

def plift2 (op : α -> β -> γ) : Partial α -> Partial β -> Partial γ
 | .some x, .some y => .some (op x y)
 | _, _ => .none

instance : Add (Partial Nat) := ⟨plift2 Nat.add⟩
instance : Mul (Partial Nat) := ⟨plift2 Nat.mul⟩
