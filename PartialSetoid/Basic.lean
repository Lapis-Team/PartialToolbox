import PartialSetoid.Relations

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

theorem IsProper.refl2 (ps : PartialSetoid α) (x: α) [h : IsProper ps.r x] : x ≈ x :=
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

open PartialSetoid in
  instance arrowPS (psa: PartialSetoid α) (psb: PartialSetoid β) : PartialSetoid (α -> β) where
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
