import «Subsets».SubsetDef

-- instance : Functor BinTree where
--   map {α β : Type} (f : α → β) (b : BinTree α) :=
--     let rec help : BinTree α → BinTree β
--     | BinTree.leaf => BinTree.leaf
--     | BinTree.branch l x r => BinTree.branch (help l) (f x) (help r)
--     help b

def sMap (f : Bool → Bool) : Subset n → Subset n
  | Subset.nil => Subset.nil
  | Subset.cons b bs => Subset.cons (f b) (sMap f bs)

-- def map (f : Bool → Bool) : {n : Nat} → Subset n → Subset n
--   | 0, Subset.nil => Subset.nil
--   | _+1, Subset.cons b bs => Subset.cons (f b) (map f bs)

-- def subToString {n : Nat} (s : Subset n) : String := toString (Subset.toListBit s)

-- instance : ToString (Subset n) where toString := subToString

def subsetMap {n : Nat} (s : Subset n) (f : Bool → Bool) : Subset n :=
    let rec help {k : Nat} : Subset k → Subset k
    | Subset.nil => Subset.nil
    | Subset.cons b bs => Subset.cons (f b) (help bs)
    help s

instance : Functor (Subset n) where map := subsetMap
