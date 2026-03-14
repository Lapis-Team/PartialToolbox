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

macro "grw" h:term : tactic => `(tactic | have := put $h <;> apply Iff.mp take)

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

theorem defined_is_some {x : Partial  α} : defined x -> ∃ y, x = .some y := by
  cases x
  . intro a
    have := defined_not_none a
    grind
  . grind

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
 is_strict₂ : defined (op x y) -> defined y

def plift₂ (op : α -> β -> γ) : Partial α -> Partial β -> Partial γ
 | .some x, .some y => .some (op x y)
 | _, _ => .none

def propPlift₂ (op : α -> β -> Prop) : Partial α -> Partial β -> Prop
  | .some x, .some y => op x y
  | _, _ => False

 instance : Strict₂ (plift₂ op) where
   is_strict₁ {x y}
    | ⟨ ⟨ h₁ , h₂ ⟩ ⟩ => by
      cases x
      . cases y <;> dsimp [plift₂] at h₁ <;> grind
      . constructor ; constructor <;> grind
   is_strict₂ {x y}
    | ⟨ ⟨ h₁ , h₂ ⟩ ⟩ => by
      cases y
      . cases x <;> dsimp [plift₂] at h₁ <;> grind
      . constructor ; constructor <;> grind

instance : LE (Partial  Nat) := ⟨ propPlift₂ Nat.le ⟩

instance : Add (Partial Nat) := ⟨plift₂ Nat.add⟩
instance : Mul (Partial Nat) := ⟨plift₂ HMul.hMul⟩
instance : Div (Partial Nat) where
    div
    | .some _, .some 0 => .none
    | .some x, .some y => .some (x / y)
    | _, _ => .none

instance : Strict₂ (HDiv.hDiv (α := Partial Nat)) where
  is_strict₁ {x y}
    | ⟨ ⟨ h₁ , h₂ ⟩ ⟩ =>
      match x with
      | .some _ => by infer_instance

  is_strict₂ {x y}
    | ⟨ ⟨ h₁ , h₂ ⟩ ⟩ =>
      match y with
      | .some _ => by infer_instance
      | .none => by dsimp [HDiv.hDiv, Div.div] at h₁ <;> grind

theorem ex1 : ∀ x y : Partial Nat, defined x -> defined y -> y ≠ .some 0 -> (x / y) * y <= x := by
  intro x y d₁ d₂ h
  have ⟨ x', hx ⟩ := defined_is_some d₁ ; rw [hx]
  have ⟨ y', hy ⟩ := defined_is_some d₂ ; rw [hy]
  have ⟨ y'', hy' ⟩ : ∃ y'', y' = .succ y''  := sorry
  rw [hy'] ; change x'.div (y''.succ) * (y''.succ) ≤ x' ; rw [<- hy']
  refine (Nat.le_div_iff_mul_le ?_).mp ?_
  . grind
  . apply Nat.le_refl

theorem ex2 : ∀ x y : Partial Nat, defined ((x / y) * y) -> (x / y) * y <= x := by
  intro x y d₁
  change (defined (plift₂ _ _ _)) at d₁
  unfold HMul.hMul at d₁ ; have d₂ := Strict₂.is_strict₁ d₁
  have d₃ := Strict₂.is_strict₁ d₂
  have d₄ := Strict₂.is_strict₂ d₂
  refine ex1 x y d₃ d₄ ?_

--------- running example ------------
namespace running_example

abbrev ℕ := Nat
axiom ℝ : Type
axiom isdef : ℝ -> Prop

@[coe]
axiom inj : ℕ → ℝ
axiom inj_def: isdef (inj n)
noncomputable instance : Coe ℕ ℝ := ⟨inj⟩

noncomputable instance : OfNat ℝ n where ofNat := n

axiom sub : ℝ -> ℝ -> ℝ
axiom sub_def : isdef n -> isdef m -> isdef (sub n m)
noncomputable instance : Sub ℝ := ⟨sub⟩

axiom div : ℝ -> ℝ -> ℝ
axiom div_def : isdef n -> isdef m -> m ≠ 0 -> isdef (div n m)
noncomputable instance : Div ℝ := ⟨div⟩

axiom exp : ℝ -> ℕ -> ℝ
axiom exp_def : isdef r -> isdef (exp r n)
noncomputable instance : HPow ℝ ℕ ℝ := ⟨exp⟩

axiom lim : (ℕ -> ℝ) -> ℝ

axiom bigadd : ℕ -> ℕ -> (ℕ -> ℝ) -> ℝ

def peq (x y: ℝ) := isdef x ∧ x = y
instance : HasEquiv ℝ := ⟨peq⟩

theorem peq_def₁ : x ≈ y → isdef x := fun h => And.left h

theorem peq_def₂ : x ≈ y → isdef y
 | ⟨h,k⟩ => by rw [← k] ; assumption

def rtol (op: ℝ -> ℝ -> Prop) : ℝ -> ℝ -> Prop :=
 fun x y => isdef y -> op x y

macro l:term:50 "≈▷" r:term:50 : term => `(term|rtol peq $l $r)

theorem rtolpeq_trans: x ≈▷ y -> y ≈▷ z -> x ≈▷ z := by
 intro h1 h2 dz
 let ⟨d2,k2⟩ := h2 dz
 let ⟨d1,k1⟩ := h1 d2
 constructor <;> simp [*]

axiom ax24 {c} {f : ℕ → ℝ} : lim (fun n => c - f n) ≈▷ c - lim (fun n => f n)

example: isdef c -> isdef (lim (fun n => n)) -> isdef (lim (fun n => c - n)) := by
 intro hc h
 have k := ax24 (c:=c) (f:=(.)) ?_
 . apply peq_def₁ k
 . apply sub_def <;> assumption


end running_example
