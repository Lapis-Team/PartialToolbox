import PartialSetoid.Partial
import PartialSetoid.Grw
import Lean
open Partial

abbrev ℕ := Nat
axiom ℝ : Type
@[instance] axiom instPartialR : Partial ℝ

@[coe] axiom inj : ℕ → ℝ
axiom inj_def: isdef (inj n)
noncomputable instance : Coe ℕ ℝ := ⟨inj⟩
instance : StrictFun₁ inj where isstrict _ := True.intro

noncomputable instance : OfNat ℝ n := ⟨ n ⟩
@[instance] axiom sub_inst : Sub ℝ
@[def_lemma] axiom sub_def {n m : ℝ} : isdef n -> isdef m -> isdef (n - m)
@[instance] axiom sub_strict : StrictFun₂ (· - ·  : ℝ -> ℝ -> ℝ)

@[instance] axiom sub_div : Div ℝ
@[def_lemma] axiom div_def {n m : ℝ} : isdef n -> isdef m -> m ≠ 0 -> isdef (n / m)
@[instance] axiom div_strict : StrictFun₂ (· / · : ℝ -> ℝ -> ℝ)
@[instance] axiom div_existence {n d : ℝ} : Existence (n / d) (d ≠ 0)

@[instance] axiom mul_inst : Mul ℝ
@[def_lemma] axiom mul_def {x y : ℝ} : isdef x -> isdef y -> isdef (x * y)
@[instance] axiom mul_strict : StrictFun₂ (· * · : ℝ -> ℝ -> ℝ)

@[instance] axiom pow_inst : HPow ℝ ℕ ℝ
@[instance] axiom pow_strict : StrictFun₂ (· ^ · : ℝ -> ℕ -> ℝ)
@[def_lemma] axiom exp_def {r : ℝ} {n : ℕ} : isdef r -> isdef (r ^ n)

axiom abs : ℝ -> ℝ
@[def_lemma] axiom abs_def : isdef r -> isdef (abs r)
@[instance] axiom abs_strict : StrictFun₁ abs

def eventually₁ (P : α -> Prop) (s: ℕ → α) : Prop :=
 ∃ N, ∀ n, n ≥ N → P (s n)

def eventually₂ (P : α -> β -> Prop) (s: ℕ → α) (s' : ℕ → β) : Prop :=
 ∃ N, ∀ n, n ≥ N → P (s n) (s' n)

axiom lim : (ℕ -> ℝ) -> ℝ
axiom lim_strict : isdef (lim xn) -> eventually₁ isdef xn
axiom lim_eventually_extensional :
 eventually₂ (.≈▷.) xn xn' -> lim xn ≈▷ lim xn'

axiom bigadd : ℕ -> ℕ -> (ℕ -> ℝ) -> ℝ
axiom bigadd_strict : isdef (bigadd n m xn) -> forall n, isdef (xn n)

@[instance] axiom lt_inst : LT ℝ
@[instance] axiom lt_strict : StrictPred₂ (LT.lt (α:=ℝ))

-------------------- isdef_elim ---------------------

instance {Qf : ℕ -> Prop} {f : ℕ → ℝ} [if' : forall n, isdef_elim (f n) (Qf n)]: isdef_elim (lim f) (∃ N, ∀ n, n ≥ N → isdef (f n) ∧ Qf n) where
 elim h k :=
  let ⟨N,u⟩ := lim_strict k
  h ⟨N, fun n ge => ⟨u n ge, (if' n).elim (.) (u n ge)⟩⟩

-------------------- GRW INSTANCES ---------------------

theorem rtolpeq_lim : (∀ n, f n ≈▷ f' n) -> lim f ≈▷ lim f' := by
 intro h
 apply lim_eventually_extensional
 apply Exists.intro 0
 grind

instance instRtolpeqLim [forall n, Copy (r n)] : Copy (rtolpeq_lim r) where

----------------- running example ---------------------------------------

axiom step₁ (x : ℝ) (n : ℕ) : bigadd 0 (n - 1) (fun i => x^i) ≈▷ (1 - x ^ (n+1)) / (1 - x)
axiom step₂ (m : ℝ) (f: ℕ → ℝ) : lim (fun n => f n / m) ≈▷ lim (fun n => f n) / m
axiom step₃ (c : ℝ) (f : ℕ → ℝ) : lim (fun n => c - f n) ≈▷ c - lim (fun n => f n)
axiom step₄ : abs x < 1 -> lim (fun n => x^(n+1)) ≈▷ 0
axiom step₅ (n m : Nat) : ((n : Nat) - (m : Nat) : ℝ) ≈▷ (n - m : Nat)
axiom step₆ : abs n < m -> m - n ≠ 0

noncomputable def geometricSeries (x: ℝ) := lim (fun n => bigadd 0 (n-1) (fun i => x ^ i))

theorem running {x : ℝ} : abs x < 1 -> geometricSeries x ≈ 1 / (1 - x) := by
  intro h
  apply isdef_elim'.elim _ h ; simp ; intro _ _ _
  calc
        geometricSeries x
   _ ≈▷ lim (fun n => (1 - x ^ (n+1)) / (1 - x)) := by respects' (step₁ x)
   _ ≈▷ lim (fun n => (1 - x ^ (n+1))) / (1 - x) := by respects step₂ (1 - x) (fun n => 1 - x ^(n+1))
   _ ≈▷ (1 - lim (fun n => x ^ (n+1))) / (1 - x) := by respects step₃ 1 (fun n => x ^ (n + 1))
   _ ≈▷ (1 - 0) / (1 - x)                        := by respects step₄ h
   _ ≈▷ 1 / (1 - x)                              := by apply (_ : forall w, ((1 - 0) / (w - x)) ≈▷ 1 / (w - x)) ; intro w
                                                       respects step₅ 1 0
   _ ≈  1 / (1 - x)                              := by
                                                     apply def_peqrfl
                                                     def_intro
                                                     exact step₆ h

axiom step₇ (x y : ℝ) : (x * (y / x)) ◁≈ y

-- running example 2
theorem running₂ { x : ℝ } : abs x < 1 -> (1 - x) * geometricSeries x ≈ 1 := by
  intro h
  apply isdef_elim'.elim _ h ; simp ; intro d₁ d₂ _
  calc
         (1 - x) * geometricSeries x
    _ ≈▷ (1 - x) * (1 / (1 - x))    := by respects (peq_rtolpeq (running h))
    _ ≈  (1 - x) * (1 / (1 - x))    := by
                                        apply def_peqrfl
                                        def_intro
                                        exact step₆ h
    _ ◁≈ 1                          := by respects step₇ (1 - x) 1
