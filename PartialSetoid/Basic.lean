import PartialSetoid.Relations

class PartialSetoid (α : Sort u) where
  r : Relation α 
  isPER: PartialEquiv r

namespace PartialSetoid

variable [PartialSetoid α]

theorem symm {a b : α} (hab : r a b) : r b a := 
  isPER.symm hab

theorem trans {a b c : α} (hab : r a b) (hbc : r b c) : r a c :=
  isPER.trans hab hbc

end PartialSetoid
