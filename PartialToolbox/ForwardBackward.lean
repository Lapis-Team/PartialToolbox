/-
This file contains the typeclasses for defining Forward and Backward chains during proof search,
  together with instances of such type-classes.

- Given a goal in the form `E↓`, backward reasoning allows to reason about the necessary
    and sufficient conditions for the definedness of `E`. With this mechanism we capture
    both necessary and sufficient conditions, as we do not use any form of backtracking.
    The `Backward` type-class indeed allows to model backward reasoning. We also define
    the atomic variant `Backward₁` for representing atomic steps of the chain.
    An instance of `Backward₁ P Q` means `Q → P` in an invertible way.
    An instance of `Backward P Q` chains over `Backward₁` steps to reduce `P` to `Q` without
    using backtracking. `P` must be made of conjunctions, univesal quantifications and predicates.

- Forward reasoning allows to extract the necessary conditions for the definedness of a 
    term in the hypothesis. The `Forward` type-class allows, together with its atomic
    variant `Forward₁`, extracts the necessary conditions using the `elim` function.
    An instance of `Forward₁ P Q` means `P → Q`.
    An instance of `Forward P Q` chains the atomic `Forward₁` steps, obtaining `Q` from `P`.
    Also in this case, P must be made of conjunctions, universal quantifications and predicates
    We define the `elim` macro to trigger forward reasoning during a proof.

- Example usage
  To trigger Backward reasoning one needs to register an instance for some atomic steps `Backward₁`
    and then invoke the `Backward.intro` function inside a tactic.
    As an example, consider sum over natural numbers. The sum of two numbers is defined if 
    both numbers are defined, thus we register the instance 
    `instance {x y : Nat} : Backward₁ (x+y)↓ (x↓ ∧ y↓) := ... -- complete the proof`
    We can now trigger backward reasoning inside a proof by invoking the `Backward.intro` function
    `example {x y: Nat} : x↓ → y↓ → (x + y)↓ := by intro h₁ h₂ ; apply Backward.intro ; exact ⟨h₁, h₂⟩`

  To trigger Forward reasoning one needs to register an instance for some atomic steps `Forward₁`
    and then invoke the `elim` tactic.
    As an example, consider the previous example of sum over natural numbers. We are now
    interested in the fact that if the sum of two numbers is defined, then both numbers are
    defined, thus we register the following instance
    `instance {x y : Nat} : Forward₁ (x+y)↓ (x↓ ∧ y↓) := ... -- complete the proof`
    We can now trigger forward reasoning inside a proof by invoking the `elim` tactic, thus
    extracting the necessary conditions `x↓` and `y↓` from the hypothesis `(x+y)↓`.
    `example {x y: Nat} : (x + y)↓ → x↓ ∧ y↓ := by elim h₁ h₂ h₃ ; exact ⟨h₁, h₂⟩`
    Notice that by invoking the `elim` tactic we introduce the atomic hyptheses `h₁ : x↓`,
    `h₂ : y↓` along with the hypothesis `h₃ : (x + y)↓`.

  More usage examples for Backward and Forward reasoning are shown in `Tests/running.lean`,
  `PartialToolbox/PartialOption.lean`, `PartialToolbox/Partial.lean` and the `Playground.lean` files.
-/

/-- 
  An instance `Backward₁ P Q` means `Q → P` in an invertible way. 
  Using the tactic `apply Backward₁.intro` reduces `P` to `Q`.
-/
class Backward₁ (P: Prop) (Q : outParam Prop) where
 intro : Q -> P

/--
  An instance `Backward P Q` backchains over atomic `Backward₁` steps
  to reduce `P` to `Q`. Using the tactic `apply Backward.intro` reduces `P` to `Q`.
-/
class Backward (P : Prop) (Q: outParam Prop) where
 intro: Q → P

-- Default reflexive instance `P → P` for stopping the backward chains 
@[default_instance]
instance (priority := low) : Backward P P where
 intro h := h

-- If `Q₁ → P₁` and `Q₂ → P₂`, then `(Q₁ ∧ Q₂) → (P₁ ∧ P₂)`
instance [h₁ : Backward P₁ Q₁] [h₂ : Backward P₂ Q₂] : Backward (P₁ ∧ P₂) (Q₁ ∧ Q₂) where
 intro := fun ⟨q₁,q₂⟩ => ⟨h₁.intro q₁, h₂.intro q₂⟩

-- If `∀ n, Q n → P n`, then `(∀ n, Q n) → (∀ n, P n)`
instance {P Q : α → Prop} [h : ∀ n, Backward (P n) (Q n)]  : Backward (∀ n, P n) (∀ n, Q n) where
 intro k n := (h n).intro (k n)

-- Instance to build up `Backward` chains from the atomic step `Backward₁`
instance [h: Backward₁ P Q] [k : Backward Q R] : Backward P R where
 intro p := h.intro (k.intro p)

-----------------------------------------

-- [h : Forward₁ P Q] means h.elim : P -> Q
class Forward₁ (P: Prop) (Q : outParam Prop) where
 elim : P -> Q

-- [h : Forward  P Q] repeatedly chains Forward₁s to obtain Q from P
--   P must be made of conjunctions, universal quantifications and predicates
class Forward (P : Prop) (Q: outParam Prop) where
 elim: P → Q

-- Default reflexive instance `P → P` for stopping the forward chains 
@[default_instance]
instance (priority := low) : Forward P P where
 elim h := h

-- If `P₁ → Q₁` and `P₂ → Q₂`, then `(P₁ ∧ P₂) → (Q₁ ∧ Q₂)`
instance [h₁ : Forward P₁ Q₁] [h₂ : Forward P₂ Q₂] : Forward (P₁ ∧ P₂) (Q₁ ∧ Q₂) where
 elim := fun ⟨p₁,p₂⟩ => ⟨h₁.elim p₁, h₂.elim p₂⟩

-- If `∀ n, P n → Q n`, then `(∀ n, P n) → (∀ n, Q n)`
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
