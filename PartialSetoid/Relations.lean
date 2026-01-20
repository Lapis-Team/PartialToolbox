def Relation (α : Sort u) := α -> α -> Prop

class Transitive (r : Relation α) where 
  trans: ∀ {x y z}, r x y -> r y z -> r x z

class Symmetric (r : Relation α) where
  symm: ∀ {x y}, r x y -> r y x

class abbrev PartialEquiv (r : Relation α) := Transitive r, Symmetric r
/- class abbrev PartialEquiv (r : Relation α) := Transitive r, Std.Symm r -/
