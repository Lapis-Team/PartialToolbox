import PartialSetoid.Meta
import PartialSetoid.Relations
import Lean.Elab

class PartialSetoid (α : Sort u) where
  r : Relation α
  isPER: PartialEquiv r


instance [PartialSetoid a] : HasEquiv a := ⟨ PartialSetoid.r ⟩

namespace PartialSetoid

variable [PartialSetoid α]

theorem symm {a b : α} (hab : a ≈ b) : b ≈ a :=
  isPER.symm hab

theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  isPER.trans hab hbc

end PartialSetoid

class IsProper {α : Sort u} (r : outParam (Relation α)) (x : α) where
  _refl : r x x

theorem IsProper.refl (ps : PartialSetoid α) (x: α) {h : IsProper ps.r x} : x ≈ x :=
  h._refl

instance psprop : PartialSetoid Prop where
  r (p q) := p <-> q
  isPER := {
    symm := by grind
    trans := by grind
  }

theorem PartialSetoid.mp {α β : Prop} : α ≈ β -> α -> β := by
  intro h a
  apply Iff.mp h a

theorem PartialSetoid.mpr {α β : Prop} : α ≈ β -> β -> α := by
  intro h a
  apply Iff.mpr h a

class IsMorphism (psa : outParam (PartialSetoid α)) (psb : outParam (PartialSetoid β)) (f : α -> β) where
  _respects : ∀ {x y}, x ≈ y -> f x ≈ f y

namespace IsMorphism
  theorem respects {psa : PartialSetoid α} {psb : PartialSetoid β}
    (f : α -> β) [h : IsMorphism psa psb f] : ∀ {x y}, x ≈ y -> f x ≈ f y  := h._respects
end IsMorphism

class IsMorphism2 (psa : outParam (PartialSetoid α)) (psb : outParam (PartialSetoid β)) (psc : outParam (PartialSetoid γ)) (f : α -> β -> γ) where
  _respects : ∀ {x1 y1 x2 y2}, x1 ≈ y1 -> x2 ≈ y2 -> f x1 x2 ≈ f y1 y2

namespace IsMorphism2
  theorem respects {psa :PartialSetoid α} {psb : PartialSetoid β} {psc : PartialSetoid γ} (f: α -> β -> γ) [h : IsMorphism2 psa psb psc f] : ∀ {x1 y1 x2 y2}, x1 ≈ y1 -> x2 ≈ y2 -> f x1 x2 ≈ f y1 y2 := h._respects
end IsMorphism2

open PartialSetoid in
  instance [PartialSetoid α] [PartialSetoid β] : PartialSetoid (α -> β) where
    r (f g) := ∀ {x y}, x ≈ y -> f x ≈ g y
    isPER := {
      symm := by
        intro f1 f2 h x y k
        apply symm
        apply h
        apply symm k
      trans := by
        intro f f1 f2 h1 h2 x y k
        have d1 : y ≈ y := by apply trans (symm k) k
        apply trans (h1 k) (h2 d1)
  }

/- open PartialSetoid in  -/
/-   theorem th [PartialSetoid α] [PartialSetoid β] [PartialSetoid γ] -/
/-     (f : α -> β -> γ) : IsMorphism f <-> IsMorphism2 f := Iff.intro -/
/-       (by -/
/-         intro h -/
/-         constructor -/
/-         intro x1 y1 x2 y2 h1 h2 -/
/-         exact IsMorphism.respects f h1 h2) -/
/-       (by -/
/-         intro h -/
/-         constructor -/
/-         intro x y h1 y1 y2 h2 -/
/-         exact IsMorphism2.respects f h1 h2) -/

-- open IsMorphism in
--   theorem th2 [PartialSetoid α] [PartialSetoid β] [PartialSetoid γ]
--   (f : α -> β) (g : β -> γ) [IsMorphism f] [IsMorphism g] : IsMorphism (g ∘ f) := by
--     constructor
--     intro x y h
--     simp
--     refine respects g ?_
--     exact respects f h


instance natZero : PartialSetoid Nat where
  r x y := x ≠ 0 ∧ x = y
  isPER := {
    symm := by grind
    trans := by grind
  }

instance natZeroRefl {x: Nat} (h : x ≠ 0) : IsProper PartialSetoid.r x where
  _refl := by constructor <;> grind

-- instance natEven : PartialSetoid Nat where
--   r x y := x % 2 = 0 ∧ x = y
--   isPER := {
--     symm := by grind
--     trans := by grind
--   }


variable {p : Nat -> Prop} [IsMorphism natZero psprop p]
variable {f : Nat -> Nat} [IsMorphism natZero natZero f]
variable {g : Nat -> Nat -> Nat} [IsMorphism2 natZero natZero natZero g]

instance foo : IsMorphism2 natZero natZero natZero HAdd.hAdd where
  _respects := by
    intro x1 y1 x2 y2 ⟨x1ne, eqx1y1⟩ ⟨x2ne, eqx2y2⟩
    constructor
    · grind
    · grind

example : ∀ x y z: Nat, z ≠ 0 -> natZero.r x y -> p (x + (z + x)) -> p (y + (z + y)) := by
  intro x y z hz h hx
  apply PartialSetoid.mp
    (IsMorphism.respects _
      (IsMorphism2.respects _ h
        (IsMorphism2.respects  _ (IsProper.refl _ _) h)
      ))
  apply hx
  apply natZeroRefl hz

example : ∀ x y z: Nat, z ≠ 0 -> natZero.r x y -> p (x + (z + x)) -> p (y + (z + y)) := by
  intro x y z hz h hx
  apply PartialSetoid.mp
    (IsMorphism.respects p
      (IsMorphism2.respects HAdd.hAdd h
        (IsMorphism2.respects HAdd.hAdd (IsProper.refl natZero z) h)
      ))
  apply hx
  apply natZeroRefl hz

example : ∀ x y : Nat, natZero.r x y -> p x -> p y := by
  intro x y h1 h2
  apply PartialSetoid.mp (IsMorphism.respects p h1) _
  apply h2


-- example : ∀ x y : Nat, x ≈ y -> p x -> p y := by
--   intro x y h1
--   grw h1
--   simp
  -- apply PartialSetoid.mp (IsMorphism.respects _ _) h2
  -- apply h1
-- example := by refine

example : ∀ x y : Nat, x ≈ y -> p x -> p y := by
  intro x y h1 h2
  apply PartialSetoid.mp (IsMorphism.respects _ h1) _
  apply h2

example : ∀ x y : Nat, natZero.r x y -> p x -> p y := by
  intro x y h1 h2
  grw h1
  exact h2

theorem t1 : ∀ x y : Nat, natZero.r x y -> p (f x) -> p (f y) := by
  intro x y h1 h2
  grw h1
  exact h2

example : ∀ x y : Nat, natZero.r x y -> p (g x x) -> p (g y y) := by
  intro x y h1 h2
  grw h1
  exact h2

example : ∀ x y z : Nat, z ≠ 0 -> natZero.r x y -> p (g x z) -> p (g y z) := by
  intro x y z hz h1 h2
  grw h1
  apply natZeroRefl hz
  apply h2
