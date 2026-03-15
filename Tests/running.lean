import PartialSetoid.Partial
open Partial

abbrev ℕ := Nat
axiom ℝ : Type
instance : Partial ℝ := sorry

@[coe]
axiom inj : ℕ → ℝ
axiom inj_def: isdef (inj n)
noncomputable instance : Coe ℕ ℝ := ⟨inj⟩

noncomputable instance : OfNat ℝ n where ofNat := n

axiom sub : ℝ -> ℝ -> ℝ
axiom sub_def : isdef n -> isdef m -> isdef (sub n m)
instance : StrictFun₂ sub := sorry
noncomputable instance : Sub ℝ := ⟨sub⟩

axiom div : ℝ -> ℝ -> ℝ
axiom div_def : isdef n -> isdef m -> m ≠ 0 -> isdef (div n m)
instance : StrictFun₂ div := sorry
axiom div_existence : isdef (div n m) → m ≠ 0 -- CSC: ??
noncomputable instance : Div ℝ := ⟨div⟩

axiom exp : ℝ -> ℕ -> ℝ
axiom exp_def : isdef r -> isdef (exp r n)
instance : StrictFun₁ (fun r => exp r n) := sorry
noncomputable instance : HPow ℝ ℕ ℝ := ⟨exp⟩

axiom lim : (ℕ -> ℝ) -> ℝ
axiom lim_strict : isdef (lim xn) -> forall n, isdef (xn n) -- CSC: ??

axiom bigadd : ℕ -> ℕ -> (ℕ -> ℝ) -> ℝ
axiom bigadd_strict : isdef (bigadd n m xn) -> forall n, isdef (xn n) -- CSC: ??

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
 . apply (StrictPred₂.isstrict k).left
 . apply sub_def <;> assumption
