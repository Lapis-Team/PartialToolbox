import PartialSetoid.Basic
import PartialSetoid.Meta

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

-- Mettere arrowRelation al posto di arrowPS in modo da non dover usare poi (...).r

variable {p : Nat -> Prop} [IsMorphism natZero psprop p]
variable {f : Nat -> Nat} [IsMorphism natZero natZero f]
variable {g : Nat -> Nat -> Nat} [IsMorphism2 natZero natZero natZero g]
variable {g1 : Nat -> Nat -> Nat -> Nat} [IsMorphism natZero (arrowPS natZero (arrowPS natZero natZero)) g1]
variable {g2 : Nat -> Nat -> Nat -> Nat} [IsProper (arrowPS natZero (arrowPS natZero (arrowPS natZero natZero))).r g2]

instance foo : IsMorphism2 natZero natZero natZero HAdd.hAdd where
  _respects := by
    intro x1 y1 x2 y2 ⟨x1ne, eqx1y1⟩ ⟨x2ne, eqx2y2⟩
    constructor
    · grind
    · grind

instance mulIsMorphism2NatZero : IsMorphism2 natZero natZero natZero HMul.hMul where
  _respects := by
    intro x1 y1 x2 y2 ⟨x1ne, eqx1y1⟩ ⟨x2ne, eqx2y2⟩
    constructor
    · sorry
    · grind

instance mulIsMorphismNatZero : IsMorphism natZero (arrowPS natZero natZero) HMul.hMul where
  _respects := by
    intro x1 x2 ⟨x1ne, eqx1y1⟩ y1 y2 ⟨x2ne, eqx2y2⟩
    constructor
    · sorry
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
  grw h
  -- · apply natZeroRefl hz
  · sorry
  · exact hx
  -- apply PartialSetoid.mp
  --   (IsMorphism.respects _
  --     (IsMorphism2.respects _ h
  --       (IsMorphism2.respects  _ (IsProper.refl _ _) h)
  --     ))
  -- apply hx
  -- apply natZeroRefl hz

example : ∀ x y z: Nat, z ≠ 0 -> natZero.r x y -> p (x * (z * x)) -> p (y * (z * y)) := by
  intro x y z hz h hx
  apply PartialSetoid.mp
    (IsMorphism.respects (psa := natZero) _
        -- (IsMorphism.respects (psa := natZero) (HMul.hMul z) (IsMorphism.respects (psb := arrowPS natZero natZero) (HMul.hMul) (IsProper.refl _ z)) h)
        (IsMorphism.respects (psb := arrowPS _ _) _ h
        ((IsMorphism.respects (psb := arrowPS _ _) _ (IsProper.refl _ _)) h))
      )
  apply hx
  apply natZeroRefl hz


example : ∀ x y z: Nat, z ≠ 0 -> natZero.r x y -> p (g1 z x x) -> p (g1 z y y) := by
  intro x y z hz h hx
  apply PartialSetoid.mp
    (IsMorphism.respects (psa := natZero) _
        ((IsMorphism.respects (psb := arrowPS _ (arrowPS _ _)) _ (IsProper.refl _ _)) h h))
  apply hx
  apply natZeroRefl hz

example : ∀ x y z: Nat, z ≠ 0 -> natZero.r x y -> p (g2 z x x) -> p (g2 z y y) := by
  intro x y z hz h hx
  apply PartialSetoid.mp
    (IsMorphism.respects (psa := natZero) _
        ((IsProper.refl2 (arrowPS _ ( arrowPS _ (arrowPS _ _))) _ (IsProper.refl _ _)) h h))
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

def x := 1
def y := 1
