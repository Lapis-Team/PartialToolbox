import PartialSetoid.Grw
import PartialSetoid.ForwardBackward
import Lean
-- Partial types are types equipped with a unary isdef predicate
-- Strict unary and binary functions are defined
-- Strict unary and binary predicates are defined so that they
--   hold only on defined elements
--
-- Option types are shown to be partial types and
--  functions and predicates over base types are automatically
--  lifted to strict functions and predicates
-- Lifted predicates preserve symmetry and transitivity, while
--  reflexivity is preserved only for defined elements

class Partial α where
 isdef : α -> Prop

@[default_instance]
instance (priority := low) default_partial : Partial α where
 isdef _ := True

class StrictPred₁ [Partial α] (P : α -> Prop) where
 isstrict : P x -> Partial.isdef x

class StrictPred₂ [Partial α] [Partial β] (P : α -> β -> Prop) where
 isstrict : P x y -> Partial.isdef x ∧ Partial.isdef y

class StrictFun₁ [Partial α] [Partial β] (f : α -> β) where
 isstrict : Partial.isdef (f x) -> Partial.isdef x

class StrictFun₂ [Partial α] [Partial β] [Partial γ] (f : α -> β -> γ) where
 isstrict : Partial.isdef (f x y) -> Partial.isdef x ∧ Partial.isdef y

-- Necessary existence condition typeclass

class Existence [Partial α] (x : α) (P: outParam Prop) where
 cond : Partial.isdef x → P

@[default_instance]
instance (priority := low) default_existence {x: α} [Partial α] : Existence x True where
 cond _ := True.intro

------------------ Defining PEQ on instances of Partial
namespace Partial

instance [Partial T] : HasEquiv T where
 Equiv (x y : T) := isdef x ∧ x = y

instance [Partial T] : StrictPred₂ (. ≈ . : T → T → Prop) where
 isstrict {x y} h := by
  let ⟨d,e⟩ := h
  grind

theorem def_peq₁ [Partial T] {x y : T} : isdef x -> x = y -> x ≈ y := by trivial

theorem def_peq₂ [Partial T] {x y : T} : isdef y -> x = y -> x ≈ y := by
 intro d e
 rw [e]
 constructor <;> grind

theorem def_peqrfl {x: T} [Partial T]: isdef x -> x ≈ x :=
 fun a => def_peq₁ a rfl

--@[def_lemma_closing]
theorem peq_def₁ [Partial T] {x y : T} : x ≈ y -> isdef x := And.left

--@[def_lemma_closing]
theorem peq_def₂ [Partial T] {x y : T}: x ≈ y -> isdef y := by
  intro ⟨hl, hr⟩
  rw [<- hr]
  apply hl

theorem peq_eq [Partial T] {x y : T} : x ≈ y -> x = y := And.right

-- PEQ Reflexivity does not hold

--- PEQ Transitivity
theorem peq_trans₁ {x y z : α} {r : α -> α -> Prop} [Partial α] : x ≈ y -> r y z -> r x z := by
  intro ⟨_, k₁⟩ h
  rw [k₁]
  exact h

instance (priority := low) { r : α -> α -> Prop } [Partial α] : Trans (.≈.) r r := ⟨peq_trans₁⟩

theorem peq_trans₂ {x y z : α} {r : α -> α -> Prop} [Partial α] : r x y -> y ≈ z -> r x z := by
  intro h ⟨_, k₁⟩
  rw [← k₁]
  exact h

instance (priority := low) { r : α -> α -> Prop } [Partial α] : Trans r (.≈.) r := ⟨peq_trans₂⟩

-- RTOL Direction ------------------------------------
def rtol [Partial T] (op: T -> T -> Prop) : T -> T -> Prop :=
 fun x y => isdef y -> op x y

infix:60 " ≈▷ " => rtol HasEquiv.Equiv
@[app_unexpander rtol]
meta def rtol.unexpander_peqq : Lean.PrettyPrinter.Unexpander
  | `($_ HasEquiv.Equiv $a $b) => `($a ≈▷ $b)
  | _ => throw ()

-- CSC: generalizzare
def peq_rtolpeq [Partial T] {x y : T} : x ≈ y -> x ≈▷ y := by
  intro h ; exact fun _ => h

-- CSC: generalizzare
theorem def_rtol_def [Partial T] {x y : T} : isdef y -> x ≈▷ y -> isdef x := by
 intro h h'
 apply (h' h).left

-- Reflexivity
-- CSC: generalizzare
instance [Partial T] : Reflexive (. ≈▷ . : T -> T -> Prop) where
  refl {x} h := by constructor <;> trivial

-- Transitivity
theorem r_trans₁ {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [StrictPred₂ r₂] [Trans r₁ r₂ r₃]  {x y z : α} :
  rtol r₁ x y -> rtol r₂ y z -> rtol r₃ x z := by
 intro h₂ h₁ d₁
 have k₁ := h₁ d₁
 have ⟨d₂,_⟩ := StrictPred₂.isstrict k₁
 have k₂ := h₂ d₂
 apply Trans.trans k₂ k₁

theorem r_trans₂ {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [Trans r₁ r₂ r₃]  {x y z : α} :
  r₁ x y -> rtol r₂ y z -> rtol r₃ x z := by
 intro k₂ h₁ d₁
 have k₁ := h₁ d₁
 apply Trans.trans k₂ k₁

theorem r_trans₃ {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [StrictPred₂ r₂] [Trans r₁ r₂ r₃]  {x y z : α} :
  rtol r₁ x y -> r₂ y z -> r₃ x z := by
 intro h₂ k₁
 have ⟨d₂,_⟩ := StrictPred₂.isstrict k₁
 have k₂ := h₂ d₂
 apply Trans.trans k₂ k₁

instance {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [StrictPred₂ r₂] [Trans r₁ r₂ r₃] : Trans (rtol r₁) (rtol r₂) (rtol r₃) := ⟨ r_trans₁ ⟩
instance {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [Trans r₁ r₂ r₃] : Trans r₁ (rtol r₂) (rtol r₃) := ⟨ r_trans₂ ⟩
instance {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [StrictPred₂ r₂] [Trans r₁ r₂ r₃] : Trans (rtol r₁) r₂ r₃ := ⟨ r_trans₃ ⟩
------------------------------------------------------

-- LTOR Direction ------------------------------------

def ltor [Partial T] (op: T -> T -> Prop) : T -> T -> Prop :=
 fun x y => isdef x -> op x y

infix:60 " ◁≈ " => ltor HasEquiv.Equiv
@[app_unexpander ltor]
meta def ltor.unexpander_peqq : Lean.PrettyPrinter.Unexpander
  | `($_ HasEquiv.Equiv $a $b) => `($a ◁≈ $b)
  | _ => throw ()

--CSC: generalizzare
theorem def_ltor_def [Partial T] {x y : T} : isdef x -> x ◁≈ y -> isdef y := by
 intro h h'
 have k := (h' h).right
 simp [<- k, h]

-- Reflexivity
-- CSC: generalizzare
instance [Partial T] : Reflexive (. ◁≈ . : T -> T -> Prop) where
  refl := by
    intro x d
    constructor <;> trivial

-- Transitivity
theorem l_trans₁ {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [StrictPred₂ r₁] [Trans r₁ r₂ r₃]  {x y z : α} :
  ltor r₁ x y -> ltor r₂ y z -> ltor r₃ x z := by
 intro h₁ h₂ d₁
 have k₁ := h₁ d₁
 have ⟨_,d₂⟩ := StrictPred₂.isstrict k₁
 have k₂ := h₂ d₂
 apply Trans.trans k₁ k₂

theorem l_trans₂ {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [StrictPred₂ r₁] [Trans r₁ r₂ r₃]  {x y z : α} :
  r₁ x y -> ltor r₂ y z -> r₃ x z := by
 intro k₁ h₂
 have ⟨_,d₂⟩ := StrictPred₂.isstrict k₁
 have k₂ := h₂ d₂
 apply Trans.trans k₁ k₂

theorem l_trans₃ {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [Trans r₁ r₂ r₃]  {x y z : α} :
  ltor r₁ x y -> r₂ y z -> ltor r₃ x z := by
 intro h₁ k₂ d₁
 have k₁ := h₁ d₁
 apply Trans.trans k₁ k₂

instance {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [StrictPred₂ r₁] [Trans r₁ r₂ r₃] : Trans (ltor r₁) (ltor r₂) (ltor r₃) := ⟨ l_trans₁ ⟩
instance {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [StrictPred₂ r₁] [Trans r₁ r₂ r₃] : Trans r₁ (ltor r₂) r₃ := ⟨ l_trans₂ ⟩
instance {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [Trans r₁ r₂ r₃] : Trans (ltor r₁) r₂ (ltor r₃) := ⟨ l_trans₃ ⟩
------------------------------------------------------

-- CSC: rimettere mano a questo paragrafo

-- Mixed transitivity
theorem rl_trans₁ [Partial T] {x y z : T} : isdef y -> x ≈▷ y -> y ◁≈ z -> x ≈ z := by
  intro dy h₁ h₂
  let ⟨d₂,k₂⟩ := h₁ dy
  let ⟨d₁,k₁⟩ := h₂ dy
  constructor <;> simp [*]
  simp [<- k₁, d₁]

theorem rl_trans₂ [Partial T] {x y z: T} : isdef x -> isdef z -> x ◁≈ y -> y ≈▷ z -> x ≈ z := by
  intro dx dz h₁ h₂
  exact r_trans₃ (fun _ => h₁ dx) (h₂ dz)

------- GRW for ≈▷ ------

theorem rtolpeq_StrictFun₁ {op : α → β} [Partial α] [Partial β] [StrictFun₁ op] : x ≈▷ x' -> op x ≈▷ op x' := by
  intro h₁ d₁
  have d₂ := StrictFun₁.isstrict d₁
  apply def_peq₂ d₁
  have hx : x = x' := peq_eq (h₁ d₂)
  rw [hx]

instance instRtolpeqStrictFun₁
 [Partial α] [Partial β] {op : α → β} [StrictFun₁ op]
 {r₁ : x ≈▷ x'}
 [Copy r₁] : Copy (rtolpeq_StrictFun₁ (op := op) r₁) where

theorem rtolpeq_StrictFun₂ {op : α → β → γ} [Partial α] [Partial β] [Partial γ] [StrictFun₂ op] : x ≈▷ x' -> y ≈▷ y' -> op x y ≈▷ op x' y' := by
  intro h₁ h₂ d₁
  have ⟨d₂,d₃⟩ := StrictFun₂.isstrict d₁
  apply def_peq₂ d₁
  have hx : x = x' := peq_eq (h₁ d₂)
  have hy : y = y' := peq_eq (h₂ d₃)
  rw [hx, hy]

instance instRtolpeqStrictFun₂
 [Partial α] [Partial β] [Partial γ] {op : α → β → γ} [StrictFun₂ op]
 {r₁ : x ≈▷ x'} {r₂ : y ≈▷ y'}
 [Copy r₁] [Copy r₂] : Copy (rtolpeq_StrictFun₂ (op := op) r₁ r₂) where

---------------------- Forward isdef ---------------------

instance isdef_elim_StrictFun₁
 [Partial α] [Partial β] {op : α → β} [s : StrictFun₁ op] [e : Existence (op x) E]
 : Forward₁ (isdef (op x)) (isdef x ∧ E) where
 elim d := ⟨s.isstrict d, e.cond d⟩

instance isdef_elim_StrictFun₂
 [Partial α] [Partial β] [Partial γ] {op : α → β → γ} [s : StrictFun₂ op] [e : Existence (op x y) E]
 : Forward₁ (isdef (op x y)) (isdef x ∧ isdef y ∧ E) where
  elim d :=
   let ⟨d₁,d₂⟩ := s.isstrict d
   ⟨d₁, d₂, e.cond d⟩

instance isdef_elim_StrictPred₁
 [Partial α] {P : α → Prop} [s : StrictPred₁ P]
 : Forward₁ (P x) (isdef x) where
 elim := s.isstrict

instance isdef_elim_StrictPred₂
 [Partial α] [Partial β] {P : α → β -> Prop} [s : StrictPred₂ P]
 : Forward₁ (P x y) (isdef x ∧ isdef y) where
 elim := s.isstrict

end Partial
