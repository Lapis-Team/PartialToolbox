import PartialSetoid.Partial
import PartialSetoid.Grw
import Lean
open Partial

abbrev ℕ := Nat
axiom ℝ : Type
instance : Partial ℝ := sorry

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

def peq (x y: ℝ) := isdef x ∧ x = y
instance : HasEquiv ℝ := ⟨peq⟩
instance : StrictPred₂ peq where
 isstrict {x y} h := by
  let ⟨d,e⟩ := h
  grind

theorem def_peq1₁ {x y : ℝ} : isdef x -> x=y -> x ≈ y := by trivial

theorem def_peq₂ {x y : ℝ} : isdef y -> x=y -> x ≈ y := by
 intro d e
 rw [e]
 constructor <;> grind

@[def_lemma_closing]
theorem peq_def₁ {x y : ℝ} : x ≈ y -> isdef x := And.left

@[def_lemma_closing]
theorem peq_def₂ {x y : ℝ}: x ≈ y -> isdef y := by
 intro h
 rw [←h.right]
 apply h.left

theorem peq_eq {x y : ℝ} : x ≈ y -> x =y := And.right

def rtol (op: ℝ -> ℝ -> Prop) : ℝ -> ℝ -> Prop :=
 fun x y => isdef y -> op x y

def rtolpeq := rtol peq
infix:60 " ≈▷ " => rtolpeq

-- macro l:term:50 "≈▷" r:term:50 : term => `(term|rtol peq $l $r)

@[def_lemma_closing]
theorem def_rtolpeq_def {x y : ℝ} : isdef y -> x≈▷ y -> isdef x := by
 intro h h'
 apply (h' h).left


theorem rtolpeq_trans: x ≈▷ y -> y ≈▷ z -> x ≈▷ z := by
 intro h1 h2 dz
 let ⟨d2,k2⟩ := h2 dz
 let ⟨d1,k1⟩ := h1 d2
 constructor <;> simp [*]

instance : Trans rtolpeq rtolpeq rtolpeq := ⟨rtolpeq_trans⟩

axiom step₁ (x : ℝ) (n : ℕ) : bigadd 0 (n - 1) (fun i => x^i) ≈▷ (1 - x ^ (n+1)) / (1 - x)
axiom step₁' : lim (fun n => bigadd 0 (n-1) (fun i => x ^ i)) ≈▷ lim (fun n => (1 - x ^ (n+1)) / (1 - x))
axiom step₂ (m : ℝ) (f: ℕ → ℝ) : lim (fun n => f n / m) ≈▷ lim (fun n => f n) / m
axiom step₃ (c : ℝ) (f : ℕ → ℝ) : lim (fun n => c - f n) ≈▷ c - lim (fun n => f n)
axiom step₄ : abs x < 1 -> lim (fun n => x^(n+1)) ≈▷ 0
axiom step₅ (n m : Nat) : ((n : Nat) - (m : Nat) : ℝ) ≈▷ (n - m : Nat)
axiom step₆ : abs n < m -> m - n ≠ 0

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

instance : Reflexive rtolpeq where
  refl {x} h := by constructor <;> trivial

theorem rtolpeq_abs : x ≈▷ x' -> (abs x) ≈▷ (abs x') := by
  sorry

theorem rtolpeq_exp {n : ℕ} : x ≈▷ x' -> x ^ n ≈▷ x' ^ n := by
  sorry

theorem rtolpeq_sub : x ≈▷ x' -> y ≈▷ y' -> (x - y) ≈▷ (x' - y') := by
  intro h₁ h₂ d₁
  apply isdef_elim.elim _ d₁ ; simp ; intro d₂ d₃
  constructor
  . def_intro
  . have hx : x = x' := peq_eq (h₁ d₂) -- dsimp [rtolpeq, peq, rtol] at h₁ ; grind
    have hy : y = y' := peq_eq (h₂ d₃)
    rw [hx, hy]

theorem rtolpeq_div : n ≈▷ n' -> d ≈▷ d' -> (n / d) ≈▷ (n' / d') := by
  intro h₁ h₂ d₁
  apply isdef_elim.elim _ d₁ ; simp ; intro d₂ d₃ d₄
  constructor
  . def_intro
    have := peq_eq (h₂ d₃)
    grind
  . have hn : n = n' := peq_eq (h₁ d₂)
    have hd : d = d' := peq_eq (h₂ d₃)
    rw [hn, hd]

theorem rtolpeq_lim : (forall n, f n ≈▷ f' n) -> lim f ≈▷ lim f' := by
 intro h d
 apply isdef_elim.elim _ d ; simp ; intro l
 have k : f=f' := by
  ext y
  apply (h y (l y)).right
 rw [k]
 constructor <;> trivial

instance instRtolpeqDiv [Copy r₁] [Copy r₂] : Copy (rtolpeq_div r₁ r₂) where
instance instRtolpeqSub [Copy r₁] [Copy r₂] : Copy (rtolpeq_sub r₁ r₂) where
instance instRtolpeqAbs [Copy r₁] : Copy (rtolpeq_abs r₁) where

instance instRtolpeqLim [forall n, Copy (r n)] : Copy (rtolpeq_lim r) where

--------------------------------------------------------

--------------------------------------------------------

example: isdef c -> isdef (lim (fun n => n)) -> isdef (lim (fun n => c - n)) := by
 intro hc h
 have k := step₃ c (.)
 def_intro

theorem running :
 abs x < 1 ->
  lim (fun n => bigadd 0 (n-1) (fun i => x ^ i)) ≈ 1 / (1 - x) := by
 intro h
 apply isdef_elim'.elim _ h ; simp ; intro d₁ d₂ _
 apply
  calc
        lim (fun n => bigadd 0 (n-1) (fun i => x ^ i))
   _ ≈▷ lim (fun n => (1 - x ^ (n+1)) / (1 - x)) := by respects' (step₁ x)
   _ ≈▷ lim (fun n => (1 - x ^ (n+1))) / (1 - x) := by respects step₂ (1 - x) (fun n => 1 - x ^(n+1))
   _ ≈▷ (1 - lim (fun n => x ^ (n+1))) / (1 - x) := by respects step₃ 1 (fun n => x ^ (n + 1))
   _ ≈▷ (1 - 0) / (1 - x)                        := by respects step₄ h
   _ ≈▷ 1 / (1 - x)                              := by apply (_ : forall w, ((1 - 0) / (w - x)) ≈▷ 1 / (w - x)) ; intro w
                                                       respects step₅ 1 0
 def_intro
 apply step₆ h
