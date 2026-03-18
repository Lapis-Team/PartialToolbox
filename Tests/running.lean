import PartialSetoid.Partial
import PartialSetoid.Grw
open Partial

abbrev ℕ := Nat
axiom ℝ : Type
-- instance : Partial ℝ := ⟨ sorry ⟩
instance : Partial ℝ := ⟨ fun _ => PEmpty ⟩

@[coe]
axiom inj : ℕ → ℝ
axiom inj_def: isdef (inj n)
noncomputable instance : Coe ℕ ℝ := ⟨inj⟩

noncomputable instance : OfNat ℝ n := ⟨ n ⟩

instance : Sub ℝ := ⟨ sorry ⟩
axiom sub_def {n m : ℝ} : isdef n -> isdef m -> isdef (n - m)
instance : StrictFun₂ (· - ·  : ℝ -> ℝ -> ℝ) := ⟨ fun a => ⟨a, a⟩ ⟩


instance : Div ℝ := ⟨ sorry ⟩
axiom div_def {n m : ℝ} : isdef n -> isdef m -> m ≠ 0 -> isdef (n / m)
instance : StrictFun₂ (· / · : ℝ -> ℝ -> ℝ) := ⟨ fun a => ⟨a, a⟩ ⟩
axiom div_existence {n m : ℝ} : isdef (n / m) → m ≠ 0 -- CSC: ??

instance : HPow ℝ ℕ ℝ := ⟨ sorry ⟩
instance : StrictFun₂ (· ^ · : ℝ -> ℕ -> ℝ) := ⟨ fun a => ⟨ a, trivial⟩  ⟩
axiom exp_def {r : ℝ} {n : ℕ} : isdef r -> isdef (r ^ n)

axiom abs : ℝ -> ℝ
axiom abs_def : isdef r -> isdef (abs r)
instance : StrictFun₁ abs := ⟨ id ⟩

axiom lim : (ℕ -> ℝ) -> ℝ
axiom lim_strict : isdef (lim xn) -> forall n, isdef (xn n) -- CSC: ??

axiom bigadd : ℕ -> ℕ -> (ℕ -> ℝ) -> ℝ
axiom bigadd_strict : isdef (bigadd n m xn) -> forall n, isdef (xn n) -- CSC: ??

noncomputable instance : LT ℝ := ⟨ sorry ⟩
instance : StrictPred₂ (LT.lt (α:=ℝ)) := ⟨ sorry ⟩

def peq (x y: ℝ) := isdef x ∧ x = y
instance : HasEquiv ℝ := ⟨peq⟩
instance : StrictPred₂ peq where
 isstrict {x y} h := by
  let ⟨d,e⟩ := h
  grind

theorem def_peq₂ {x y : ℝ}: isdef y -> x=y -> x ≈ y := by
 intro d e
 rw [e]
 constructor <;> grind

def rtol (op: ℝ -> ℝ -> Prop) : ℝ -> ℝ -> Prop :=
 fun x y => isdef y -> op x y

def rtolpeq := rtol peq
infix:60 " ≈▷ " => rtolpeq

-- macro l:term:50 "≈▷" r:term:50 : term => `(term|rtol peq $l $r)

theorem rtolpeq_trans: x ≈▷ y -> y ≈▷ z -> x ≈▷ z := by
 intro h1 h2 dz
 let ⟨d2,k2⟩ := h2 dz
 let ⟨d1,k1⟩ := h1 d2
 constructor <;> simp [*]

instance : Trans rtolpeq rtolpeq rtolpeq := ⟨rtolpeq_trans⟩

axiom step₁ (n : ℕ) : bigadd 0 (n - 1) (fun i => x^i) ≈▷ (1 - x ^ (n+1)) / (1 - x)
axiom step₁' : lim (fun n => bigadd 0 (n-1) (fun i => x ^ i)) ≈▷ lim (fun n => (1 - x ^ (n+1)) / (1 - x))
axiom step₂ (m : ℝ) (f: ℕ → ℝ) : lim (fun n => f n / m) ≈▷ lim (fun n => f n) / m
axiom step₂' : lim (fun n => (1 - x ^ (n+1)) / (1 - x)) ≈▷ lim (fun n => (1 - x ^ (n+1))) / (1 - x)
axiom step₃ (c : ℝ) (f : ℕ → ℝ) : lim (fun n => c - f n) ≈▷ c - lim (fun n => f n)
axiom step₄ : abs x < 1 -> lim (fun n => x^(n+1)) ≈▷ 0
axiom step₅ (n m : Nat) : ((n : Nat) - (m : Nat) : ℝ) ≈▷ (n - m : Nat)
axiom step₆ : abs n < m -> m - n ≠ 0

-------------------- GRW INSTANCES ---------------------

instance : Reflexive rtolpeq where
  refl {x} h := by constructor <;> trivial

theorem rtolpeq_abs : x ≈▷ x' -> (abs x) ≈▷ (abs x') := by
  sorry

theorem rtolpeq_exp {n : ℕ} : x ≈▷ x' -> x ^ n ≈▷ x' ^ n := by
  sorry

theorem rtolpeq_sub : x ≈▷ x' -> y ≈▷ y' -> (x - y) ≈▷ (x' - y') := by
  intro h₁ h₂ d₁
  have ⟨d₂,d₃⟩ := StrictFun₂.isstrict d₁
  refine ⟨d₁, ?_⟩
  have hx : x = x' := by dsimp [rtolpeq, peq, rtol] at h₁ ; grind
  have hy : y = y' := by dsimp [rtolpeq, peq, rtol] at h₂ ; grind
  rw [hx, hy]

theorem rtolpeq_div : n ≈▷ n' -> d ≈▷ d' -> (n / d) ≈▷ (n' / d') := by
  intro h₁ h₂ d₁
  have h := StrictFun₂.isstrict d₁
  refine ⟨d₁, ?_⟩
  have hn : n = n' := by dsimp [rtolpeq, peq, rtol] at h₁ ; grind
  have hd : d = d' := by dsimp [rtolpeq, peq, rtol] at h₂ ; grind
  rw [hn, hd]

instance instRtolpeqDiv [Copy r₁] [Copy r₂] : Copy (rtolpeq_div r₁ r₂) where
instance instRtolpeqSub [Copy r₁] [Copy r₂] : Copy (rtolpeq_sub r₁ r₂) where
instance instRtolpeqAbs [Copy r₁] : Copy (rtolpeq_abs r₁) where

--------------------------------------------------------

example: isdef c -> isdef (lim (fun n => n)) -> isdef (lim (fun n => c - n)) := by
 intro hc h
 have k := step₃ (c:=c) (f:=(.)) ?_
 . apply (StrictPred₂.isstrict k).left
 . apply sub_def <;> assumption

-- set_option trace.Meta.synthInstance true in
-- set_option pp.explicit true in
theorem running :
 abs x < 1 ->
  lim (fun n => bigadd 0 (n-1) (fun i => x ^ i)) ≈ 1 / (1 - x) := by
 intro h
 have ⟨d₁,d₂⟩ := StrictPred₂.isstrict h
 have d₃ := StrictFun₁.isstrict d₁
 have k :=
  calc
   lim (fun n => bigadd 0 (n-1) (fun i => x ^ i))
     ≈▷ lim (fun n => (1 - x ^ (n+1)) / (1 - x)) := by
    exact step₁'
   _ ≈▷ lim (fun n => (1 - x ^ (n+1))) / (1 - x) := by
    respects step₂ (1 - x) (fun n => 1 - x ^(n+1))
   _ ≈▷ (1 - lim (fun n => x ^ (n+1))) / (1 - x) := by
    respects step₃ 1 (fun n => x ^ (n + 1))
   _ ≈▷ (1 - 0) / (1 - x) := by
    respects step₄ h
   _ ≈▷ 1 / (1 - x) := by
    apply (_ : forall w, ((1 - 0) / (w - x)) ≈▷ 1 / (w - x)) ; intro w
    respects step₅ 1 0
 apply k
 apply div_def
 . apply inj_def
 . apply sub_def <;> assumption
 . apply step₆ h
