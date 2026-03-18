-- set_option pp.explicit true

class C (eq: T -> T -> Prop) (t: T) where
 r : eq t t

def rr (t: T) (eq:_) [h: C eq t] : eq t t := C.r

axiom t: Type
axiom eqt: t -> t -> Prop
axiom s: Type
axiom eqs: s -> s -> Prop
axiom c: t
axiom f: t -> t
axiom g: s -> t
def eqfun (eqα: α -> α -> Prop) (eqβ: β -> β -> Prop) (f g: α -> β) : Prop :=
 ∀x, eqα x x -> eqβ (f x) (g x)

-- instance sC {x: s} : C eqs x := sorry

instance cC : C eqt c := sorry

instance : C (eqfun eqt eqt) f := sorry
instance : C (eqfun eqs eqt) g := sorry

instance fC [C eqt x] [fi : C (eqfun eqt eqt) f]: C eqt (f x) where
 r := by
  apply fi.r
  apply rr

instance gC [C eqs x] [fi : C (eqfun eqs eqt) g]: C eqt (g x) where
 r := by
  apply fi.r
  apply rr

instance lamC {P : α -> β} [h : forall x, [C eqα x] -> C eqβ (P x)]: C (eqfun eqα eqβ) (λ x => P x) where
 r := by
  intro x e
  have : C eqα x := ⟨e⟩
  simp
  apply (h x).r

#print lamC

set_option pp.explicit true
set_option trace.Meta.synthInstance true
#check rr (f (f c)) eqt
#check rr (λ (_ : s) => c) (eqfun eqs eqt)
#check rr (λ x => λ (_: s) => f (g x)) (eqfun eqs (eqfun eqs eqt))


----------------------------
/-

class C (t: T) where
 r : t = t

def rr (t: T) [h: C t]  : t = t := C.r

axiom t: Type
axiom s: Type
axiom c: t
axiom f: t -> t
axiom g: s -> t

instance sC {x: s} : C x := sorry

instance cC : C c where
 r := Eq.refl _

instance fC [C x]: C (f x) where
 r := congr (Eq.refl _) C.r

instance gC [C x]: C (g x) where
 r := congr (Eq.refl _) C.r

instance lamC {P : α -> β} [forall (x : α), C x] [h : forall x, [C x] -> C (P x)]: C (λ x => P x) where
 r := by ext y ; apply rr

#print lamC

#check rr (f (f c))
#check rr (λ (_ : s) => c)
#check rr (λ x => λ (_: s) => f (g x))

-/
