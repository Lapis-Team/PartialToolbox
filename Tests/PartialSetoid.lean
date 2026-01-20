import PartialSetoid.Basic

instance ps1 : PartialSetoid Nat where 
  r := fun x y => x = y
  isPER := { 
    trans := by intro _ _ _ hxy hyz ; apply hxy.trans hyz , 
    symm := by intro _ _ h ; exact h.symm 
  }

instance ps2 : PartialSetoid Nat where 
  r := fun x y => x = y ∧ x != 0
  isPER := {
    symm := by 
      intro x y h
      have d1 : y = x := by exact h.left.symm
      have d2 : y != 0 := by simp [d1, h.right]
      exact ⟨ d1, d2 ⟩ 

    trans := by 
      intro _ _ _ h1 h2
      exact ⟨ h1.left.trans h2.left, h1.right ⟩ 
  }

example : ps1.r 0 0 := by simp [PartialSetoid.r]
example : ps1.r 1 1 := by simp [PartialSetoid.r]
example : ¬ps1.r 1 2 := by simp [PartialSetoid.r]

example : ¬ps2.r 0 0 := by simp [PartialSetoid.r]
example : ps2.r 1 1 := by simp [PartialSetoid.r]
example : ¬ps2.r 1 2 := by simp [PartialSetoid.r]
