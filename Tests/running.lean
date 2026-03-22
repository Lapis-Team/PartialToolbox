import PartialSetoid.Partial
import PartialSetoid.Grw
import Lean
open Partial

abbrev ℕ := Nat
axiom ℝ : Type
instance instPartialR : Partial ℝ := sorry

@[coe]
axiom inj : ℕ → ℝ
axiom inj_def: isdef (inj n)
noncomputable instance : Coe ℕ ℝ := ⟨inj⟩

noncomputable instance : OfNat ℝ n := ⟨ n ⟩

instance : Sub ℝ := ⟨ sorry ⟩
@[def_lemma] axiom sub_def {n m : ℝ} : isdef n -> isdef m -> isdef (n - m)
instance : StrictFun₂ (· - ·  : ℝ -> ℝ -> ℝ) := sorry


instance : Div ℝ := ⟨ sorry ⟩
@[def_lemma] axiom div_def {n m : ℝ} : isdef n -> isdef m -> m ≠ 0 -> isdef (n / m)
instance : StrictFun₂ (· / · : ℝ -> ℝ -> ℝ) := sorry
axiom div_existence {n m : ℝ} : isdef (n / m) → m ≠ 0 -- CSC: ??

instance : Mul ℝ := sorry
@[def_lemma] axiom mul_def {x y : ℝ} : isdef x -> isdef y -> isdef (x * y)
instance : StrictFun₂ (· * · : ℝ -> ℝ -> ℝ) := sorry

instance : HPow ℝ ℕ ℝ := ⟨ sorry ⟩
instance : StrictFun₂ (· ^ · : ℝ -> ℕ -> ℝ) := sorry
@[def_lemma] axiom exp_def {r : ℝ} {n : ℕ} : isdef r -> isdef (r ^ n)

axiom abs : ℝ -> ℝ
@[def_lemma] axiom abs_def : isdef r -> isdef (abs r)
instance : StrictFun₁ abs := sorry

axiom lim : (ℕ -> ℝ) -> ℝ
axiom lim_strict : isdef (lim xn) -> forall n, isdef (xn n) -- CSC: ??

axiom bigadd : ℕ -> ℕ -> (ℕ -> ℝ) -> ℝ
axiom bigadd_strict : isdef (bigadd n m xn) -> forall n, isdef (xn n) -- CSC: ??

noncomputable instance : LT ℝ := ⟨ sorry ⟩
instance : StrictPred₂ (LT.lt (α:=ℝ)) := ⟨ sorry ⟩

-------------------- isdef_elim ---------------------

class isdef_elim [Partial T] (t: T) (Q : outParam Prop) where
 elim {P : Prop} : (Q → P) -> isdef t -> P

@[default_instance]
instance  {t : ℝ} : isdef_elim t True where
 elim k _ := k ⟨⟩

instance {x y : ℝ} [ix : isdef_elim x Qx] [iy : isdef_elim y Qy] : isdef_elim (x - y) ((isdef x ∧ Qx) ∧ (isdef y ∧ Qy)) where
 elim h k :=
  let ⟨u₁,u₂⟩ := StrictFun₂.isstrict k
  ix.elim (fun qx => iy.elim (fun qy => h ⟨⟨u₁,qx⟩,⟨u₂,qy⟩⟩) u₂ ) u₁

instance {x y : ℝ} [ix : isdef_elim x Qx] [iy : isdef_elim y Qy] : isdef_elim (x * y) ((isdef x ∧ Qx) ∧ (isdef y ∧ Qy)) where
 elim h k :=
  let ⟨u₁,u₂⟩ := StrictFun₂.isstrict k
  ix.elim (fun qx => iy.elim (fun qy => h ⟨⟨u₁,qx⟩,⟨u₂,qy⟩⟩) u₂ ) u₁

instance {x : ℝ} [ix : isdef_elim x Qx] : isdef_elim (abs x) (isdef x ∧ Qx) where
 elim h k :=
  let u := StrictFun₁.isstrict k
  ix.elim (fun qx => h ⟨u,qx⟩) u

instance {x y : ℝ} [ix : isdef_elim x Qx] [iy : isdef_elim y Qy] : isdef_elim (x / y) ((isdef x ∧ Qx) ∧ (isdef y ∧ y≠0 ∧ Qy)) where
 elim h k :=
  let ⟨u₁,u₂⟩ := StrictFun₂.isstrict k
  let u₃ := div_existence k
  ix.elim (fun qx => iy.elim (fun qy => h ⟨⟨u₁,qx⟩,⟨u₂,u₃,qy⟩⟩) u₂ ) u₁

instance {x : ℝ} {y : ℕ} [ix : isdef_elim x Qx] [iy : isdef_elim y Qy] : isdef_elim (x ^ y) ((isdef x ∧ Qx) ∧ (isdef y ∧ Qy)) where
 elim h k :=
  let ⟨u₁,u₂⟩ := StrictFun₂.isstrict k
  ix.elim (fun qx => iy.elim (fun qy => h ⟨⟨u₁,qx⟩,⟨u₂,qy⟩⟩) u₂ ) u₁

instance {Qf : ℕ -> Prop} {f : ℕ → ℝ} [if' : forall n, isdef_elim (f n) (Qf n)]: isdef_elim (lim f) (forall n, isdef (f n) ∧ Qf n) where
 elim h k :=
  let u := lim_strict k
  h (fun n => ⟨u n, (if' n).elim (.) (u n)⟩)

class isdef_elim' (T: Prop) (Q : outParam Prop) where
 elim {P : Prop} : (Q -> P) -> T -> P

instance {x y : ℝ} [ix : isdef_elim x Qx] [iy: isdef_elim y Qy] : isdef_elim' (x < y) ((isdef x ∧ Qx) ∧ (isdef y ∧ Qy)) where
 elim h k :=
  let ⟨u₁,u₂⟩ := StrictPred₂.isstrict k
  ix.elim (fun qx => iy.elim (fun qy => h ⟨⟨u₁,qx⟩,⟨u₂,qy⟩⟩) u₂ ) u₁

-------------------- GRW INSTANCES ---------------------

instance : Reflexive (rtolpeq (instPartial := instPartialR)) where
  refl {x} h := by constructor <;> trivial

theorem rtolpeq_StrictFun₁ {op : α → β} [Partial α] [Partial β] [StrictFun₁ op] : x ≈▷ x' -> op x ≈▷ op x' := by
  intro h₁ d₁
  have d₂ := StrictFun₁.isstrict d₁
  apply def_peq₂ d₁
  have hx : x = x' := peq_eq (h₁ d₂)
  rw [hx]

theorem rtolpeq_StrictFun₂ {op : α → β → γ} [Partial α] [Partial β] [Partial γ] [StrictFun₂ op] : x ≈▷ x' -> y ≈▷ y' -> op x y ≈▷ op x' y' := by
  intro h₁ h₂ d₁
  have ⟨d₂,d₃⟩ := StrictFun₂.isstrict d₁
  apply def_peq₂ d₁
  have hx : x = x' := peq_eq (h₁ d₂)
  have hy : y = y' := peq_eq (h₂ d₃)
  rw [hx, hy]

theorem rtolpeq_lim : (forall n, f n ≈▷ f' n) -> lim f ≈▷ lim f' := by
 intro h d
 apply isdef_elim.elim _ d ; simp ; intro l
 have k : f=f' := by
  ext y
  apply (h y (l y)).right
 rw [k]
 constructor <;> trivial

instance instRtolpeqStrictFun₁
 [Partial α] [Partial β] {op : α → β} [StrictFun₁ op]
 {r₁ : x ≈▷ x'}
 [Copy r₁] : Copy (rtolpeq_StrictFun₁ (op := op) r₁) where

instance instRtolpeqStrictFun₂
 [Partial α] [Partial β] [Partial γ] {op : α → β → γ} [StrictFun₂ op]
 {r₁ : x ≈▷ x'} {r₂ : y ≈▷ y'}
 [Copy r₁] [Copy r₂] : Copy (rtolpeq_StrictFun₂ (op := op) r₁ r₂) where

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
