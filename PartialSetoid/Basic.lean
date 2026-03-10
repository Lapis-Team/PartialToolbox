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

class IsMorphism2 (psa : outParam (PartialSetoid α)) (psb : outParam (PartialSetoid β)) (psc : outParam (PartialSetoid γ)) (f : α -> β -> γ) where
  _respects : ∀ {x1 y1 x2 y2}, x1 ≈ y1 -> x2 ≈ y2 -> f x1 x2 ≈ f y1 y2

namespace IsMorphism2
  theorem respects {psa :PartialSetoid α} {psb : PartialSetoid β} {psc : PartialSetoid γ} (f: α -> β -> γ) [h : IsMorphism2 psa psb psc f] : ∀ {x1 y1 x2 y2}, x1 ≈ y1 -> x2 ≈ y2 -> f x1 x2 ≈ f y1 y2 := h._respects
end IsMorphism2

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

open PartialSetoid in
   theorem morphismIsMorphism2 [psa: PartialSetoid α] [psb: PartialSetoid β] [psg: PartialSetoid γ]
     (f : α -> β -> γ) : IsMorphism psa (arrowPS psb psg) f <-> IsMorphism2 psa psb psg f := Iff.intro
       (by
         intro h
         constructor
         intro x1 y1 x2 y2 h1 h2
         exact IsMorphism.respects f h1 h2)
       (by
         intro h
         constructor
         intro x y h1 y1 y2 h2
         exact IsMorphism2.respects f h1 h2)

-- open IsMorphism in
--   theorem th2 [psa : PartialSetoid α] [PartialSetoid β] [PartialSetoid γ]
--   (f : α -> β) (g : β -> γ) [IsMorphism  f] [IsMorphism g] : IsMorphism (g ∘ f) := by
--     constructor
--     intro x y h
--     simp
--     refine respects g ?_
--     exact respects f h
