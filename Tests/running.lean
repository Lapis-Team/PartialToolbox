import PartialToolbox.Partial
import PartialToolbox.Grw
import PartialToolbox.ForwardBackward
import Lean
open Partial

abbrev ℕ := Nat
axiom ℝ : Type
@[instance] axiom instPartialR : Partial ℝ

@[coe] axiom inj : ℕ → ℝ
@[instance] axiom inj_def_b {n} : Backward₁ (inj n)↓ n↓
noncomputable instance : Coe ℕ ℝ := ⟨inj⟩
instance : StrictFun₁ inj where isstrict _ := True.intro

noncomputable instance : OfNat ℝ n := ⟨ n ⟩
@[instance] axiom sub_inst : Sub ℝ
@[instance] axiom sub_def_b {n m : ℝ} : Backward₁ (n - m)↓ (n↓ ∧ m↓)
@[instance] axiom sub_strict : StrictFun₂ (· - ·  : ℝ -> ℝ -> ℝ)

@[instance] axiom sub_div : Div ℝ
@[instance] axiom div_def_b {n m : ℝ} : Backward₁ (n / m)↓ (n↓ ∧ m↓ ∧ m ≠ 0)
@[instance] axiom div_strict : StrictFun₂ (· / · : ℝ -> ℝ -> ℝ)
@[instance] axiom div_existence {n d : ℝ} : Existence (n / d) (d ≠ 0)

@[instance] axiom mul_inst : Mul ℝ
@[instance] axiom mul_def_b {n m : ℝ} : Backward₁ (n * m)↓ (n↓ ∧ m↓)
@[instance] axiom mul_strict : StrictFun₂ (· * · : ℝ -> ℝ -> ℝ)

@[instance] axiom pow_inst : HPow ℝ ℕ ℝ
@[instance] axiom pow_def_b {r : ℝ} {n : ℕ} : Backward₁ (r ^ n)↓ (r↓ ∧ n↓)
@[instance] axiom pow_strict : StrictFun₂ (· ^ · : ℝ -> ℕ -> ℝ)

axiom abs : ℝ -> ℝ
macro:max atomic("|" noWs) a:term noWs "|" : term => `(abs $a)
@[app_unexpander abs]
meta def abs.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) => `(|$a|)
  | _ => throw ()
@[instance] axiom abs_def_b : Backward₁ |r|↓ r↓
@[instance] axiom abs_strict : StrictFun₁ (|·|)

def eventually₁ (P : α -> Prop) (s: ℕ → α) : Prop :=
 ∃ N, ∀ n, n ≥ N → P (s n)

def eventually₂ (P : α -> β -> Prop) (s: ℕ → α) (s' : ℕ → β) : Prop :=
 ∃ N, ∀ n, n ≥ N → P (s n) (s' n)

axiom lim : (ℕ -> ℝ) -> ℝ
@[instance] axiom lim_strict : Forward₁ (lim xn)↓ (eventually₁ (·↓) xn)
axiom lim_eventually_extensional :
 eventually₂ (.≈▷.) xn xn' -> lim xn ≈▷ lim xn'

axiom bigadd : ℕ -> ℕ -> (ℕ -> ℝ) -> ℝ
notation "Σ[" s "," e "]" => bigadd s e
@[instance] axiom bigadd_strict : Forward₁ (Σ[n, m] xn)↓ (n↓ ∧ m↓ ∧ ∀ n, (xn n)↓)
@[instance] axiom bigadd_def_b : Backward₁ (Σ[n, m] xn)↓ (n↓ ∧ m↓ ∧ ∀ i, (xn i)↓)

@[instance] axiom lt_inst : LT ℝ
@[instance] axiom lt_strict : StrictPred₂ (. < . : ℝ → ℝ → Prop)

-------------------- GRW INSTANCES ---------------------

-- CSC: aggiungere riscritttura sotto bigadd

theorem rtolpeq_lim : (∀ n, f n ≈▷ f' n) -> lim f ≈▷ lim f' := by
 intro h
 apply lim_eventually_extensional
 apply Exists.intro 0
 grind

instance instRtolpeqLim [forall n, Copy (r n)] : Copy (rtolpeq_lim r) where

-------------- Backward/Forward examples -----------------------------

example {x y z : ℝ} : (x / y - y / z)↓ -> (y / y * x * z)↓ := by
 apply elim ; simp ; intro a b c d e f
 apply Backward.intro
 trivial

example {a b : ℕ} {x : ℝ} : (Σ[a, b] (fun n => x / n))↓ -> (Σ[a, b*a] (fun n => n / n))↓ := by
 apply elim ; simp ; intro a b c
 apply Backward.intro
 and_intros <;> try trivial
 intro n
 apply elim _ (c n) ; simp

example {x : ℝ} : (lim (fun n => n / x))↓ -> x ≠ 0 := by
 apply elim ; simp [eventually₁] ; intro N h
 specialize h N (by simp)
 apply elim _ h ; simp

----------------- running example ---------------------------------------

axiom step₁ (x : ℝ) (n : ℕ) : Σ[0, n-1] (fun i => x^i) ≈▷ (1 - x ^ (n+1)) / (1 - x)
axiom step₂ (x : ℝ) (f: ℕ → ℝ) : lim (fun n => f n / x) ≈▷ lim (fun n => f n) / x
axiom step₃ (c : ℝ) (f : ℕ → ℝ) : lim (fun n => c - f n) ≈▷ c - lim (fun n => f n)
axiom step₄ : |x| < 1 -> lim (fun n => x^(n+1)) ≈▷ 0
axiom step₅ (n m : Nat) : (n - m : ℝ) ≈▷ (n - m : Nat)
axiom step₆ : |x| < y -> y - x ≠ 0

noncomputable def geometricSeries (x: ℝ) := lim (fun n => Σ[0, n-1] fun i => x ^ i)

theorem running {x : ℝ} : |x| < 1 -> geometricSeries x ≈ 1 / (1 - x) := by
  intro h
  apply elim _ h ; simp ; intro _ _
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
                                                     apply Backward.intro
                                                     grind [step₆]

axiom step₇ (x y : ℝ) : (x * (y / x)) ◁≈ y

-- running example 2
theorem running₂ { x : ℝ } : |x| < 1 -> (1 - x) * geometricSeries x ≈ 1 := by
  intro h
  apply elim _ h ; simp ; intro d₁ d₂
  calc
         (1 - x) * geometricSeries x
    _ ≈▷ (1 - x) * (1 / (1 - x))    := by respects peq_rtolpeq (running h)
    _ ≈  (1 - x) * (1 / (1 - x))    := by
                                        apply def_peqrfl
                                        apply Backward.intro
                                        simp_all [step₆]
    _ ◁≈ 1                          := by respects step₇ (1 - x) 1

theorem running_full { x : ℝ } : |x| < 1 -> (1 - x) * geometricSeries x ≈ 1 := by
  intro h
  apply elim _ h ; simp ; intro d₁ d₂
  have hgs := calc
        geometricSeries x
   _ ≈▷ lim (fun n => (1 - x ^ (n+1)) / (1 - x)) := by respects' step₁ x
   _ ≈▷ lim (fun n => (1 - x ^ (n+1))) / (1 - x) := by apply step₂ (1 - x) (fun n => 1 - x ^(n+1))
   _ ≈▷ (1 - lim (fun n => x ^ (n+1))) / (1 - x) := by respects step₃ 1 (fun n => x ^ (n + 1))
   _ ≈▷ (1 - 0) / (1 - x)                        := by respects step₄ h
   _ ≈▷ 1 / (1 - x)                              := by apply (_ : ∀ w, ((1 - 0) / (w - x)) ≈▷ 1 / (w - x))
                                                       intro w
                                                       respects step₅ 1 0
   _ ≈  1 / (1 - x)                              := by apply def_peqrfl
                                                       apply Backward.intro
                                                       simp_all [step₆]
  calc
         (1 - x) * geometricSeries x
    _ ≈▷ (1 - x) * (1 / (1 - x))    := by respects peq_rtolpeq hgs
    _ ≈  (1 - x) * (1 / (1 - x))    := by apply def_peqrfl
                                          apply Backward.intro
                                          simp_all [step₆]
    _ ◁≈ 1                          := by respects step₇ (1 - x) 1
