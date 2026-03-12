import PartialSetoid.Basic
import PartialSetoid.Meta

instance natZero : PartialSetoid Nat where
  r x y := x ≠ 0 ∧ x = y
  isPER := {
    symm := by grind
    trans := by grind
  }

instance natZeroRefl {x: Nat} (h : x ≠ 0) : IsProper natZero.r x  where
  _refl := by constructor <;> grind

-- Mettere arrowRelation al posto di arrowPS in modo da non dover usare poi (...).r
instance natZeroAddIsMorph : IsMorphism natZero (arrowPS natZero natZero) HAdd.hAdd where
  _respects := by
    intro x1 y1 ⟨x1ne, eqx1y1⟩ x2 y2 ⟨x2ne, eqx2y2⟩
    constructor <;> grind

instance mulIsMorphismNatZero : IsMorphism natZero (arrowPS natZero natZero) HMul.hMul where
  _respects := by
    intro x1 x2 ⟨x1ne, eqx1y1⟩ y1 y2 ⟨x2ne, eqx2y2⟩
    constructor
    · exact Nat.mul_ne_zero x1ne x2ne
    · grind


variable {p : Nat -> Prop} [IsMorphism natZero psprop p] [IsProper (arrowPS natZero psprop).r p]
variable {g : Nat -> Nat -> Nat} [IsMorphism natZero (arrowPS natZero natZero) g]
variable {g1 : Nat -> Nat -> Nat -> Nat} [IsMorphism natZero (arrowPS natZero (arrowPS natZero natZero)) g1]
variable {g2 : Nat -> Nat -> Nat -> Nat} [IsProper (arrowPS natZero (arrowPS natZero (arrowPS natZero natZero))).r g2]
-- variable {q : Nat -> Prop} [IsProper (arrowPS natZero psprop).r q]

def arrow (psa: PartialSetoid α) (psb: PartialSetoid β) (f : α -> β) (g : α -> β) : Prop :=
  ∀ x y : α, x ≈ y -> f x ≈ g y

def ArrowRelation {α} := Relation (Relation α)

-- def arrowRelation : (ps1 : PartialSetoid α) -> (ps2: PartialSetoid β) -> PartialSetoid (α -> β) :=
def arrowRelation (f : α -> β) (g : α -> β) [PartialSetoid α] [PartialSetoid β] : Prop :=
  ∀ x y : α, x ≈ y -> f x ≈ g y

-- variable {g: Nat -> Nat} [IsProper (arrowRelation) g]


-- PER over simple predicates
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

example : ∀ x y : Nat, x ≈ y -> p x -> p y := by
  intro x y h1 h2
  grw h1
  exact h2

-- PER over unary function
variable {f : Nat -> Nat} [IsMorphism natZero natZero f]
example : ∀ x y : Nat, natZero.r x y -> p (f x) -> p (f y) := by
  intro x y h1 h2
  grw h1
  exact h2

-- PER over binary function
example : ∀ x y : Nat, natZero.r x y -> p (g x x) -> p (g y y) := by
  intro x y h1 h2
  grw h1
  exact h2

example : ∀ x y z : Nat, z ≠ 0 -> natZero.r x y -> p (g x z) -> p (g y z) := by
  intro x y z hz h1 h2
  grw h1
  apply natZeroRefl hz
  apply h2

-- PER over ternary function
example : ∀ x y z: Nat, z ≠ 0 -> natZero.r x y -> p (g1 z x x) -> p (g1 z y y) := by
  intro x y z hz h hx
  apply PartialSetoid.mp
    (IsMorphism.respects _
        ((IsMorphism.respects (psb := arrowPS _ (arrowPS _ _)) _ (IsProper.refl _ _)) h h))
  apply hx
  apply natZeroRefl hz

example : ∀ x y z: Nat, z ≠ 0 -> x ≈ y -> p (g1 z x x) -> p (g1 z y y) := by
  intro x y z hz h hx
  grw h
  apply natZeroRefl hz
  apply hx

-- TODO: can move to `IsProper` instead of `IsMorphism`
example : ∀ x y z: Nat, z ≠ 0 -> natZero.r x y -> p (g2 z x x) -> p (g2 z y y) := by
  intro x y z hz h hx
  apply PartialSetoid.mp
    (IsProper.refl2 (arrowPS _ _) _
        ((IsProper.refl2 (arrowPS _ ( arrowPS _ (arrowPS _ _))) _ (IsProper.refl _ _)) h h))
  apply hx
  apply natZeroRefl hz

-- Sum
example : ∀ x y z: Nat, z ≠ 0 -> natZero.r x y -> p (x + (z + x)) -> p (y + (z + y)) := by
  intro x y z hz h hx
  apply PartialSetoid.mp
    (IsMorphism.respects _
      (IsMorphism.respects (psb := arrowPS _ _) _ h
        (IsMorphism.respects (psb := arrowPS _ _)  _ (IsProper.refl _ _) h)
      ))
  apply hx
  apply natZeroRefl hz

example : ∀ x y z: Nat, z ≠ 0 -> natZero.r x y -> p (x + (z + x)) -> p (y + (z + y)) := by
  intro x y z hz h hx
  grw h
  · apply natZeroRefl hz
  · exact hx

-- Mult
example : ∀ x y z: Nat, z ≠ 0 -> natZero.r x y -> p (x * (z * x)) -> p (y * (z * y)) := by
  intro x y z hz h hx
  apply PartialSetoid.mp
    (IsMorphism.respects _
        (IsMorphism.respects (psb := arrowPS _ _) _ h
        ((IsMorphism.respects (psb := arrowPS _ _) _ (IsProper.refl _ _)) h))
      )
  apply hx
  apply natZeroRefl hz

example : ∀ x y z: Nat, z ≠ 0 -> natZero.r x y -> p (x * (z * x)) -> p (y * (z * y)) := by
  intro x y z hz h hx
  grw h
  · apply natZeroRefl hz
  · apply hx
