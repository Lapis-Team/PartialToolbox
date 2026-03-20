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
instance [Partial T]: HasEquiv T where
 Equiv (x y : T) := isdef x ∧ x = y
instance [Partial T] : StrictPred₂ (. ≈ . : T → T → Prop) where
 isstrict {x y} h := by
  let ⟨d,e⟩ := h
  grind

theorem def_peq1₁ [Partial T] {x y : T} : isdef x -> x=y -> x ≈ y := by trivial

theorem def_peq₂ [Partial T] {x y : T} : isdef y -> x=y -> x ≈ y := by
 intro d e
 rw [e]
 constructor <;> grind

@[def_lemma_closing]
theorem peq_def₁ [Partial T] {x y : T} : x ≈ y -> isdef x := And.left

@[def_lemma_closing]
theorem peq_def₂ [Partial T] {x y : T}: x ≈ y -> isdef y := by
 intro h
 rw [←h.right]
 apply h.left

theorem peq_eq [Partial T] {x y : T} : x ≈ y -> x = y := And.right

def rtol [Partial T] (op: T -> T -> Prop) : T -> T -> Prop :=
 fun x y => isdef y -> op x y

def ltor [Partial T] (op: T -> T -> Prop) : T -> T -> Prop :=
 fun x y => isdef x -> op x y

abbrev rtolpeq [instPartial: Partial T] := rtol (. ≈ . : T → T → Prop)
infix:60 " ≈▷ " => rtolpeq

abbrev ltorpeq [instPartial: Partial T] := ltor (. ≈ . : T → T → Prop)
infix:60 " ◁≈ " => ltorpeq

@[def_lemma_closing]
theorem def_rtolpeq_def [Partial T] {x y : T} : isdef y -> x ≈▷ y -> isdef x := by
 intro h h'
 apply (h' h).left

@[def_lemma_closing]
theorem def_ltorpeq_def [Partial T] {x y : T} : isdef x -> x ◁≈ y -> isdef y := by
 intro h h'
 have k := (h' h).right
 simp [<- k, h]

theorem rtolpeq_trans [Partial T] {x y z : T} : x ≈▷ y -> y ≈▷ z -> x ≈▷ z := by
 intro h1 h2 dz
 let ⟨d2,k2⟩ := h2 dz
 let ⟨d1,k1⟩ := h1 d2
 constructor <;> simp [*]

theorem ltorpeq_trans [Partial T] {x y z : T} : x ◁≈ y -> y ◁≈ z -> x ◁≈ z := by
 intro h₁ h₂ dx
 let k₂ := (h₁ dx).right
 have d₂ : isdef y := by rw [<- k₂] ; assumption
 let ⟨d₁,k₁⟩ := h₂ d₂
 constructor <;> simp [*]
 simp [<- k₁, d₂]

theorem rtoltopeq_trans [Partial T] {x y z : T} : isdef y -> x ≈▷ y -> y ◁≈ z -> x ≈ z := by
 intro dy h₁ h₂
 let ⟨d₂,k₂⟩ := h₁ dy
 let ⟨d₁,k₁⟩ := h₂ dy
 constructor <;> simp [*]
 simp [<- k₁, d₁]

instance [Partial T] : Trans (γ := T) rtolpeq rtolpeq rtolpeq := ⟨rtolpeq_trans⟩

end Partial
---------------------------------------
