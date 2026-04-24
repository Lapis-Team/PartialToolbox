/-
This file contains the typeclasses for defining Forward and 
  Backward reasoning, together with some instances of such typeclasses
  that can be globally used.

Backward reasoning allows to reason about the necessary and sufficient conditions 
  of an expression. This allows to replace a goal in the form `E↓`, 
  with the atomic conditions for the definedness of `E`.

Forward reasoning allows to extract the necessary conditions for the
  definedness of a term in the hypothesis.
-/

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

-- If `Q₁ → P₁` and `Q₂ → P₂`, then `(Q₁ ∧ Q₂) → (P₁ ∧ P₂)`
instance [h₁ : Backward P₁ Q₁] [h₂ : Backward P₂ Q₂] : Backward (P₁ ∧ P₂) (Q₁ ∧ Q₂) where
 intro := fun ⟨q₁,q₂⟩ => ⟨h₁.intro q₁, h₂.intro q₂⟩

-- If `∀ n Q n → P n`, then `(∀ n, Q n) → (∀ n, P n)`
instance {P Q : α → Prop} [h : ∀ n, Backward (P n) (Q n)]  : Backward (∀ n, P n) (∀ n, Q n) where
 intro k n := (h n).intro (k n)

-- Instance to build up `Backward` chains from the atomic step `Backward₁`
instance [h: Backward₁ P Q] [k : Backward Q R] : Backward P R where
 intro p := h.intro (k.intro p)

-----------------------------------------

-- [h : Forward₁ P Q] means h.elim : P -> Q
-- [h : Forward  P Q] repeatedly chains Forward₁s to obtain Q from P
--   P must be made of conjunctions, universal quantifications and predicates

class Forward₁ (P: Prop) (Q : outParam Prop) where
 elim : P -> Q

class Forward (P : Prop) (Q: outParam Prop) where
 elim: P → Q

@[default_instance]
instance (priority := low) : Forward P P where
 elim h := h

-- If `P₁ → Q₁` and `P₂ → Q₂`, then `(P₁ ∧ P₂) → (Q₁ ∧ Q₂)`
instance [h₁ : Forward P₁ Q₁] [h₂ : Forward P₂ Q₂] : Forward (P₁ ∧ P₂) (Q₁ ∧ Q₂) where
 elim := fun ⟨p₁,p₂⟩ => ⟨h₁.elim p₁, h₂.elim p₂⟩

-- If `∀ n P n → Q n`, then `(∀ n, P n) → (∀ n, Q n)`
instance {P Q : α → Prop} [h : ∀ n, Forward (P n) (Q n)] : Forward (∀ n, P n) (∀ n, Q n) where
 elim k n := (h n).elim (k n)

-- Instance to build up `Forward` chains from the atomic step `Forward₁`
instance [h: Forward₁ P Q] [k : Forward Q R] : Forward P R where
 elim p := k.elim (h.elim p)

--------------------------------------------

def elim [f : Forward P Q] : (Q -> P -> R) -> P -> R :=
 fun h p => h (f.elim p) p

syntax "elim" (ppSpace colGt (ident <|> hole))* : tactic

macro_rules
 | `(tactic|elim $l*) => `(tactic|apply elim <;> try simp <;> intros $l* <;> subst_vars)
