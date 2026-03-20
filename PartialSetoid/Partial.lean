import PartialSetoid.Grw
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

instance default : Partial α where
 isdef _ := True

class StrictPred₁ [Partial α] (P : α -> Prop) where
 isstrict : P x -> Partial.isdef x

class StrictPred₂ [Partial α] [Partial β] (P : α -> β -> Prop) where
 isstrict : P x y -> Partial.isdef x ∧ Partial.isdef y

class StrictFun₁ [Partial α] [Partial β] (f : α -> β) where
 isstrict : Partial.isdef (f x) -> Partial.isdef x

class StrictFun₂ [Partial α] [Partial β] [Partial γ] (f : α -> β -> γ) where
 isstrict : Partial.isdef (f x y) -> Partial.isdef x ∧ Partial.isdef y

------------------ Defining PEQ on instances of Partial
namespace Partial

def prel {op : T -> T -> Prop} [Partial T] (x y: T) : Prop := isdef x ∧ op x y

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

@[def_lemma_closing]
theorem peq_def₁ [Partial T] {x y : T} : x ≈ y -> isdef x := And.left

@[def_lemma_closing]
theorem peq_def₂ [Partial T] {x y : T}: x ≈ y -> isdef y := by
  intro ⟨hl, hr⟩
  rw [<- hr]
  apply hl

theorem peq_eq [Partial T] {x y : T} : x ≈ y -> x = y := And.right

-- PEQ Reflexivity
-- ATTENTION: THIS IS FALSE
/- instance [Partial T] : Reflexive (. ≈ . : T -> T -> Prop) where -/
/-   refl := by  -/
/-     intro x -/
/-     constructor -/
/-     . sorry -/
/-     . trivial -/

--- PEQ Transitivity
theorem peq_trans [Partial T] {x y z : T} : x ≈ y -> y ≈ z -> x ≈ z := by
  intro ⟨_, k₁⟩ ⟨dy, k₂⟩ 
  rw [k₁] 
  exact def_peq₁ dy k₂

-- RTOL Direction ------------------------------------
def rtol [Partial T] (op: T -> T -> Prop) : T -> T -> Prop :=
 fun x y => isdef y -> op x y

def rtolp [Partial T] (op : T -> T -> Prop) : T -> T -> Prop :=
 fun x y => isdef y -> prel (op := op) x y

abbrev rtolpeq [instPartial: Partial T] := rtol (. ≈ . : T → T → Prop)
infix:60 " ≈▷ " => rtolpeq

@[def_lemma_closing]
def peq_rtolpeq [Partial T] {x y : T} : x ≈ y -> x ≈▷ y := by 
  intro h ; exact fun _ => h

@[def_lemma_closing]
theorem def_rtol_def [Partial T] {x y : T} : isdef y -> x ≈▷ y -> isdef x := by
 intro h h'
 apply (h' h).left

@[def_lemma_closing]
theorem def_rtol_def₁ [Partial T] {x y : T} : isdef y -> rtolp op x y -> isdef x := by
 intro h h'
 apply (h' h).left

theorem r_trans₁ [Partial T] {x y z : T} : x ≈▷ y -> y ≈▷ z -> x ≈▷ z := by
  intro h₁ h₂ dz
  let ⟨dy, k₁⟩ := h₂ dz
  let ⟨dx, k₂⟩ := h₁ dy
  constructor <;> simp [*]

-- Reflexivity
instance [Partial T] : Reflexive (. ≈▷ . : T -> T -> Prop) where
  refl := by 
    intro x d
    constructor <;> trivial

-- Transitivity
theorem r_trans₂ [Partial T] {x y z : T} : x ≈ y -> y ≈▷ z -> x ≈▷ z := by
  intro h₁ h₂ dz
  let ⟨_, k₁⟩ := h₂ dz
  rw [<- k₁] ; assumption

theorem r_trans₃ [Partial T] {x y z : T} : x ≈▷ y -> y ≈ z -> x ≈ z := by 
  intro h₁ h₂
  have dy : isdef y := by exact peq_def₁ h₂
  have ⟨_, h₃⟩ := h₁ dy
  rw [h₃] ; assumption

instance [Partial T] : Trans (γ := T) rtolpeq rtolpeq rtolpeq := ⟨r_trans₁⟩
instance [Partial T] : Trans (γ := T) (. ≈ .) rtolpeq rtolpeq := ⟨r_trans₂⟩
instance [Partial T] : Trans (γ := T) rtolpeq (. ≈ .) (. ≈ .) := ⟨r_trans₃⟩
------------------------------------------------------

-- LTOR Direction ------------------------------------

def ltor [Partial T] (op: T -> T -> Prop) : T -> T -> Prop :=
 fun x y => isdef x -> op x y

def ltorp [Partial T] (op: T -> T -> Prop) : T -> T -> Prop :=
 fun x y => isdef x -> prel (op := op) x y

abbrev ltorpeq [instPartial: Partial T] := ltor (. ≈ . : T → T → Prop)
infix:60 " ◁≈ " => ltorpeq

@[def_lemma_closing]
theorem def_ltor_def [Partial T] {x y : T} : isdef x -> x ◁≈ y -> isdef y := by
 intro h h'
 have k := (h' h).right
 simp [<- k, h]

-- Reflexivity
instance [Partial T] : Reflexive (. ◁≈ . : T -> T -> Prop) where
  refl := by 
    intro x d
    constructor <;> trivial

-- Transitivity
theorem ltrans₁ [Partial T] {x y z : T} : x ◁≈ y -> y ◁≈ z -> x ◁≈ z := by
 intro h₁ h₂ dx
 let ⟨ _, k₂ ⟩ := h₁ dx
 have d₂ : isdef y := by rw [<- k₂] ; assumption
 let ⟨d₁,k₁⟩ := h₂ d₂
 constructor <;> simp [*]
 simp [<- k₁, d₂]

theorem ltrans₂ [Partial T] {x y z : T} : x ≈ y -> y ◁≈ z -> x ≈ z := by
  intro h₁ h₂
  have dy : isdef y := by exact peq_def₂ h₁
  have ⟨_, h₃⟩ := h₂ dy 
  rw [<- h₃] ; assumption

theorem ltrans₃ [Partial T] {x y z : T} : x ◁≈ y -> y ≈ z -> x ◁≈ z := by
  intro h₁ h₂ dx
  have ⟨_, k₁⟩ := h₁ dx
  rw [k₁] ; assumption


instance [Partial T] : Trans (γ := T) ltorpeq ltorpeq ltorpeq := ⟨ ltrans₁ ⟩
instance [Partial T] : Trans (γ := T) (. ≈ .) ltorpeq (. ≈ .) := ⟨ ltrans₂ ⟩
instance [Partial T] : Trans (γ := T) ltorpeq (. ≈ .) ltorpeq := ⟨ ltrans₃ ⟩
------------------------------------------------------

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

end Partial
