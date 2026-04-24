import PartialToolbox.Grw
import PartialToolbox.ForwardBackward
import Lean

/- 
Partial types are types equipped with a unary isdef predicate.
Strict unary and binary functions are defined.
Strict unary and binary predicates are defined so that they
  hold only on defined elements.
Left-to-right (`ltor`), right-to-left (`rtol`) and bidirectional (`bidir`)
  variants for relations are shown. The transitivities that hold 
  for combinations of such directions are also shown.
  Directed relations are shown to also preserve reflexivity and transitivity.
-/

class Partial α where
 isdef : α -> Prop

postfix:1024 "↓ " => Partial.isdef

@[default_instance]
instance (priority := low) default_partial : Partial α where
 isdef _ := True

/-- 
`StrictPred₁ P` implements strictness on unary predicates. 
If the predicate is true over some value, then the value is defined
-/
class StrictPred₁ [Partial α] (P : α -> Prop) where
 isstrict : P x -> x↓

/-- 
`StrictPred₂ P` implements strictness on binary predicates. 
If the predicate holds for some values `x`,`y`, then they are both defined.
-/
class StrictPred₂ [Partial α] [Partial β] (P : α -> β -> Prop) where
 isstrict : P x y -> x↓ ∧ y↓

/-- 
`StrictFun₁ f` implements strictness on unary functions. 
If the result of the function is defined, then also the argument is.
-/
class StrictFun₁ [Partial α] [Partial β] (f : α -> β) where
 isstrict : (f x)↓ -> x↓

/-- 
`StrictFun₂ f` implements strictness on binary functions. 
If the result of the function is defined, then also the arguments are.
-/
class StrictFun₂ [Partial α] [Partial β] [Partial γ] (f : α -> β -> γ) where
 isstrict : (f x y)↓ -> x↓ ∧ y↓

/--
`Existence x P` allows to assert that if `x` is defined, then `P` must hold.
-/
class Existence [Partial α] (x : α) (P: outParam Prop) where
 cond : x↓ → P

@[default_instance]
instance (priority := low) default_existence {x: α} [Partial α] : Existence x True where
 cond _ := True.intro

------------------ Defining PEQ on instances of Partial

instance [Partial T] : HasEquiv T where
 Equiv (x y : T) := x↓ ∧ x = y

instance [Partial T] : StrictPred₂ (. ≈ . : T → T → Prop) where
 isstrict {x y} h := by
  let ⟨d,e⟩ := h
  grind

theorem def_peq₁ [Partial T] {x y : T} : x↓ -> x = y -> x ≈ y := by trivial

theorem def_peq₂ [Partial T] {x y : T} : y↓ -> x = y -> x ≈ y := by
 intro d e
 rw [e]
 constructor <;> grind

theorem def_peqrfl {x: T} [Partial T]: x↓ -> x ≈ x :=
 fun a => def_peq₁ a rfl

theorem peq_def₁ [Partial T] {x y : T} : x ≈ y -> x↓ := And.left

theorem peq_def₂ [Partial T] {x y : T}: x ≈ y -> y↓ := by
  intro ⟨hl, hr⟩
  rw [<- hr]
  apply hl

theorem peq_eq [Partial T] {x y : T} : x ≈ y -> x = y := And.right

--- PEQ Transitivity
theorem peq_trans₁ {x y z : α} {r : α -> α -> Prop} [Partial α] : x ≈ y -> r y z -> r x z := by
  intro ⟨_, k₁⟩ h
  rw [k₁]
  exact h

instance (priority := low) { r : α -> α -> Prop } [Partial α] : Trans (.≈.) r r := ⟨peq_trans₁⟩

theorem peq_trans₂ {x y z : α} {r : α -> α -> Prop} [Partial α] : r x y -> y ≈ z -> r x z := by
  intro h ⟨_, k₁⟩
  rw [← k₁]
  exact h

instance (priority := low) { r : α -> α -> Prop } [Partial α] : Trans r (.≈.) r := ⟨peq_trans₂⟩

-- RTOL Direction ------------------------------------
def rtol [Partial T] (op: T -> T -> Prop) : T -> T -> Prop :=
 fun x y => y↓ -> op x y

postfix:1024 "▷ " => rtol

infix:60 " ≈▷ " => rtol HasEquiv.Equiv
@[app_unexpander rtol]
meta def rtol.unexpander_peqq : Lean.PrettyPrinter.Unexpander
  | `($_ HasEquiv.Equiv $a $b) => `($a ≈▷ $b)
  | _ => throw ()

def peq_rtolpeq [Partial T] {x y : T} : x ≈ y -> x ≈▷ y := by
  intro h ; exact fun _ => h

theorem def_rtol_def {r: α → α → Prop} [Partial α] [StrictPred₂ r] : y↓ -> r▷ x y -> x↓ := by
 intro h h'
 apply (StrictPred₂.isstrict (h' h)).left

-- Reflexivity
instance {r : α → α → Prop} [Partial α] [Reflexive r] : Reflexive r▷ where
  refl _ := Reflexive.refl

theorem rtol_refl {r : α → α → Prop} [Partial α] (p : ∀ {x}, x↓ -> r x x) : Reflexive r▷ := ⟨p⟩

instance rtol_peq_refl [Partial α] : Reflexive (. ≈▷ . : α -> α -> Prop) := rtol_refl def_peqrfl

-- Transitivity
theorem r_trans₁ {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [StrictPred₂ r₂]
  [Trans r₁ r₂ r₃]  {x y z : α} : r₁▷ x y -> r₂▷ y z -> r₃▷ x z := by
    intro h₂ h₁ d₁
    have k₁ := h₁ d₁
    have ⟨d₂,_⟩ := StrictPred₂.isstrict k₁
    have k₂ := h₂ d₂
    apply Trans.trans k₂ k₁

theorem r_trans₂ {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [Trans r₁ r₂ r₃]
  {x y z : α} : r₁ x y -> r₂▷ y z -> r₃▷ x z := by
    intro k₂ h₁ d₁
    have k₁ := h₁ d₁
    apply Trans.trans k₂ k₁

theorem r_trans₃ {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [StrictPred₂ r₂]
  [Trans r₁ r₂ r₃]  {x y z : α} : r₁▷ x y -> r₂ y z -> r₃ x z := by
     intro h₂ k₁
     have ⟨d₂,_⟩ := StrictPred₂.isstrict k₁
     have k₂ := h₂ d₂
     apply Trans.trans k₂ k₁

instance (priority := high) {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [StrictPred₂ r₂]
  [Trans r₁ r₂ r₃] : Trans r₁▷ r₂▷ r₃▷ := ⟨ r_trans₁ ⟩
instance {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [Trans r₁ r₂ r₃] : Trans r₁ r₂▷ r₃▷ := ⟨ r_trans₂ ⟩
instance {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [StrictPred₂ r₂]
  [Trans r₁ r₂ r₃] : Trans r₁▷ r₂ r₃ := ⟨ r_trans₃ ⟩
------------------------------------------------------

-- LTOR Direction ------------------------------------

def ltor [Partial T] (op: T -> T -> Prop) : T -> T -> Prop :=
 fun x y => x↓ -> op x y

infix:60 " ◁≈ " => ltor HasEquiv.Equiv
@[app_unexpander ltor]
meta def ltor.unexpander_peqq : Lean.PrettyPrinter.Unexpander
  | `($_ HasEquiv.Equiv $a $b) => `($a ◁≈ $b)
  | _ => throw ()

prefix:1024 " ◁" => ltor

theorem def_ltor_def {r: α → α → Prop} [Partial α] [StrictPred₂ r] : x↓ → ◁r x y → y↓ := by
 intro h h'
 apply (StrictPred₂.isstrict (h' h)).right

-- Reflexivity
instance {r : α → α → Prop} [Partial α] [Reflexive r] : Reflexive ◁r where
  refl _ := Reflexive.refl

theorem ltor_refl {r : α → α → Prop} [Partial α] (p : ∀ {x}, x↓ -> r x x) : Reflexive ◁r := ⟨p⟩

instance ltor_peq_refl [Partial α] : Reflexive (· ◁≈ · : α -> α -> Prop) := ltor_refl def_peqrfl

-- Transitivity
theorem l_trans₁ {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [StrictPred₂ r₁] [Trans r₁ r₂ r₃]  {x y z : α}
  : ◁r₁ x y -> ◁r₂ y z -> ◁r₃ x z := by
    intro h₁ h₂ d₁
    have k₁ := h₁ d₁
    have ⟨_,d₂⟩ := StrictPred₂.isstrict k₁
    have k₂ := h₂ d₂
    apply Trans.trans k₁ k₂

theorem l_trans₂ {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [StrictPred₂ r₁] [Trans r₁ r₂ r₃]  {x y z : α}
  : r₁ x y -> ◁r₂ y z -> r₃ x z := by
    intro k₁ h₂
    have ⟨_,d₂⟩ := StrictPred₂.isstrict k₁
    have k₂ := h₂ d₂
    apply Trans.trans k₁ k₂

theorem l_trans₃ {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [Trans r₁ r₂ r₃]  {x y z : α}
  : ◁r₁ x y -> r₂ y z -> ◁r₃ x z := by
    intro h₁ k₂ d₁
    have k₁ := h₁ d₁
    apply Trans.trans k₁ k₂

instance {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [StrictPred₂ r₁] [Trans r₁ r₂ r₃] : Trans ◁r₁ ◁r₂ ◁r₃ := ⟨ l_trans₁ ⟩
instance (priority := high) {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [StrictPred₂ r₁] [Trans r₁ r₂ r₃] : Trans r₁ ◁r₂ r₃ := ⟨ l_trans₂ ⟩
instance (priority := high + 1) {r₁ r₂ r₃ : α -> α -> Prop} [Partial α] [Trans r₁ r₂ r₃] : Trans ◁r₁ r₂ ◁r₃ := ⟨ l_trans₃ ⟩
------------------------------------------------------

-- Bidirectional relation
infix:60 " ◁≈▷ " => ltor (rtol HasEquiv.Equiv)

-- Reflexivity
instance [Partial α] : Reflexive (· ◁≈▷ · : α -> α -> Prop) := ltor_refl fun _ => def_peqrfl

-- Transitivity
theorem bidir_trans₁ [Partial α] {r₁ r₂ r₃ : α -> α -> Prop}
  [StrictPred₂ r₂] [Trans r₁ r₂ r₃] : ◁r₁▷ x y -> r₂▷ y z -> ◁r₃▷ x z := by
  intro h₁ h₂ dx dz
  specialize h₂ dz
  have ⟨dy, _⟩ := StrictPred₂.isstrict h₂
  specialize h₁ dx dy
  exact Trans.trans h₁ h₂

theorem bidir_trans₂ [Partial α] {r₁ r₂ r₃ : α -> α -> Prop}
  [StrictPred₂ r₁] [Trans r₁ r₂ r₃] : ◁r₁ x y -> ◁r₂▷ y z -> ◁r₃▷ x z := by
  intro h₁ h₂ dx dz
  specialize h₁ dx
  have ⟨_, dy⟩ := StrictPred₂.isstrict h₁
  specialize h₂ dy dz
  exact Trans.trans h₁ h₂

instance (priority := high + 2) [Partial α] {r₁ r₂ r₃ : α -> α -> Prop}
  [StrictPred₂ r₂] [Trans r₁ r₂ r₃] : Trans ◁r₁▷ r₂▷ ◁r₃▷ := ⟨bidir_trans₁⟩
instance (priority := high + 2) [Partial α] {r₁ r₂ r₃ : α -> α -> Prop}
  [StrictPred₂ r₁] [Trans r₁ r₂ r₃] : Trans ◁r₁ ◁r₂▷ ◁r₃▷ := ⟨bidir_trans₂⟩

------------------------------------------------------

theorem ltorpeq_StrictPred₁ {P : α → Prop} [Partial α] [StrictPred₁ P]
  : x ◁≈ x' -> P x ⟶ P x' := by
    intro h₁ k
    have d₁ := StrictPred₁.isstrict k
    have hx : x = x' := peq_eq (h₁ d₁)
    simpa [←hx]

instance instLtorpeqStrictPred₁
  [Partial α] {P : α → Prop} [StrictPred₁ P]
  {r₁ : x ◁≈ x'}
  [Copy r₁] : Copy (ltorpeq_StrictPred₁ (P := P) r₁) where

theorem ltorpeq_StrictPred₂ {P : α → β → Prop} [Partial α] [Partial β] [StrictPred₂ P]
  : x ◁≈ x' -> y ◁≈ y' -> P x y ⟶ P x' y' := by
    intro h₁ h₂ k
    have d₁ := StrictPred₂.isstrict k
    have hx : x = x' := peq_eq (h₁ d₁.left)
    have hy : y = y' := peq_eq (h₂ d₁.right)
    simpa [←hx, ←hy]

instance instLtorpeqStrictPred₂
  [Partial α] [Partial β] {P : α → β → Prop} [StrictPred₂ P]
  {r₁ : x ◁≈ x'} {r₂ : y ◁≈ y'}
  [Copy r₁] [Copy r₂] : Copy (ltorpeq_StrictPred₂ (P := P) r₁ r₂) where

theorem rtolpeq_StrictFun₁ {f : α → β} [Partial α] [Partial β] [StrictFun₁ f]
  : x ≈▷ x' -> f x ≈▷ f x' := by
    intro h₁ d₁
    have d₂ := StrictFun₁.isstrict d₁
    apply def_peq₂ d₁
    have hx : x = x' := peq_eq (h₁ d₂)
    rw [hx]

instance instRtolpeqStrictFun₁
  [Partial α] [Partial β] {f : α → β} [StrictFun₁ f]
  {r₁ : x ≈▷ x'}
  [Copy r₁] : Copy (rtolpeq_StrictFun₁ (f := f) r₁) where

theorem rtolpeq_StrictFun₂ {f : α → β → γ} [Partial α] [Partial β] [Partial γ] [StrictFun₂ f]
  : x ≈▷ x' -> y ≈▷ y' -> f x y ≈▷ f x' y' := by
    intro h₁ h₂ d₁
    have ⟨d₂,d₃⟩ := StrictFun₂.isstrict d₁
    apply def_peq₂ d₁
    have hx : x = x' := peq_eq (h₁ d₂)
    have hy : y = y' := peq_eq (h₂ d₃)
    rw [hx, hy]

instance instRtolpeqStrictFun₂
  [Partial α] [Partial β] [Partial γ] {f : α → β → γ} [StrictFun₂ f]
  {r₁ : x ≈▷ x'} {r₂ : y ≈▷ y'}
  [Copy r₁] [Copy r₂] : Copy (rtolpeq_StrictFun₂ (f := f) r₁ r₂) where

---------------------- Forward isdef ---------------------

/-
The following instances allow to hide from the API the explicit use of `Forward₁`, so that
the user may model naturally strictness on functions/predicates and existence conditions
respectively with the `Strict(Fun|Pred)` and `Existence` typeclasses.
The `elim` function will then automatically search for these instances when necessary.
-/

instance [Partial α] [Partial β] {op : α → β} [s : StrictFun₁ op] [e : Existence (op x) E]
 : Forward₁ (op x)↓ (x↓ ∧ E) where
 elim d := ⟨s.isstrict d, e.cond d⟩

instance [Partial α] [Partial β] [Partial γ] {op : α → β → γ} [s : StrictFun₂ op] [e : Existence (op x y) E]
 : Forward₁ (op x y)↓ (x↓ ∧ y↓ ∧ E) where
  elim d :=
   let ⟨d₁,d₂⟩ := s.isstrict d
   ⟨d₁, d₂, e.cond d⟩

instance [Partial α] {P : α → Prop} [s : StrictPred₁ P] : Forward₁ (P x) x↓ where
 elim := s.isstrict

instance [Partial α] [Partial β] {P : α → β -> Prop} [s : StrictPred₂ P]
 : Forward₁ (P x y) (x↓ ∧ y↓) where
 elim := s.isstrict

-------------------- Unfoldable instances --------------------

/-- 
If it is possible to unfold two relations `g` and `f`, then also their `rtol` variants 
can be unfolded.
-/
instance {f g : α -> α -> Prop} [Partial α] [u: Unfoldable g f] : Unfoldable g▷ f▷ := by
 cases u ; exact .id

/-- 
If it is possible to unfold two relations `g` and `f`, then also their `ltor` variants 
can be unfolded.
-/
instance [u: Unfoldable g f] : Unfoldable ◁g ◁f := by
 cases u ; exact .id

/-- 
If it is possible to unfold two binary relations `g` and `f` and `f` is strict, then also `g`
is strict.
-/
instance [Partial α] [Partial β] {g f : α -> β → Prop} [u: Unfoldable g f] [StrictPred₂ f]
 : StrictPred₂ g := by
 cases u ; assumption

/-- 
If it is possible to unfold two unary relations `g` and `f` and `f` is strict, then also `g`
is strict.
-/
instance [Partial α] {g f : α -> Prop} [u: Unfoldable g f] [StrictPred₁ f]
 : StrictPred₁ g := by
 cases u ; assumption

/-- 
If it is possible to unfold two unary functions `g` and `f` and `f` is strict, then also `g`
is strict.
-/
instance [Partial α] [Partial β] {g f : α -> β} [u: Unfoldable g f] [StrictFun₁ f]
 : StrictFun₁ g := by
 cases u ; assumption

/-- 
If it is possible to unfold two binary functions `g` and `f` and `f` is strict, then also `g`
is strict.
-/
instance [Partial α] [Partial β] [Partial γ] {g f : α -> β → γ} [u: Unfoldable g f] [StrictFun₂ f]
 : StrictFun₂ g := by
 cases u ; assumption

/-- 
If it is possible to unfold two unary functions `g` and `f` and `f` has some existence conditions,
then `g` is subject to the same conditions.
-/
instance [Partial α] [Partial β] {g f : α -> β} [u: Unfoldable g f] [Existence (f x) P]
 : Existence (g x) P := by
 cases u ; assumption

/-- 
If it is possible to unfold two binary functions `g` and `f` and `f` has some existence conditions,
then `g` is subject to the same conditions.
-/
instance [Partial α] [Partial β] [Partial γ] {g f : α -> β → γ} [u: Unfoldable g f] [Existence (f x y) P]
 : Existence (g x y) P := by
 cases u ; assumption

/-- 
If it is possible to unfold two unary functions `g` and `f` and `f` is subject to some backward
implication, the also `g` is.
-/
instance [Partial α] [Partial β] {g f : α -> β} [u: Unfoldable g f] [Backward₁ (f x)↓ P]
 : Backward₁ (g x)↓ P := by
 cases u ; assumption

/-- 
If it is possible to unfold two binary functions `g` and `f` and `f` is subject to some backward
implication, the also `g` is.
-/
instance [Partial α] [Partial β] [Partial γ] {g f : α -> β → γ} [u: Unfoldable g f] [Backward₁ (f x y)↓ P]
 : Backward₁ (g x y)↓ P := by
 cases u ; assumption
