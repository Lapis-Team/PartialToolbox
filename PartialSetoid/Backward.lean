-- [h : Backward₁ P Q] means Q -> P in an invertible way ; apply h.intro reduces P to Q
-- [h : Backward  P Q] backchains over Backward₁s to reduce P to Q without backtracking;
--   that's why all Backward₁ rules are supposed to be invertible
--   P must be made of conjunctions, universal quantifications and predicates

class Backward₁ (P: Prop) (Q : outParam Prop) where
 intro : Q -> P

class Backward (P : Prop) (Q: outParam Prop) where
 intro: Q → P

@[default_instance]
instance (priority := low) : Backward P P where
 intro h := h

instance [h₁ : Backward P₁ Q₁] [h₂ : Backward P₂ Q₂] : Backward (P₁ ∧ P₂) (Q₁ ∧ Q₂) where
 intro := fun ⟨q₁,q₂⟩ => ⟨h₁.intro q₁, h₂.intro q₂⟩

instance {P Q : α → Prop} [h : ∀ n, Backward (P n) (Q n)]  : Backward (∀ n, P n) (∀ n, Q n) where
 intro k n := (h n).intro (k n)

instance [h: Backward₁ P Q] [k : Backward Q R] : Backward P R where
 intro p := h.intro (k.intro p)
