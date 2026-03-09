import PartialSetoid
import Init.Data.Vector

inductive Vec (α : Type) : Nat -> Type u where
  | zero : Vec α 0
  | cons : α -> (Vec α n) -> Vec α (n.succ)

def append (xs : Vec α n) (ys : Vec α m) : Vec α (m + n) :=
  match xs with
    | Vec.zero => ys
    | Vec.cons x xs => Vec.cons x (append xs ys)
