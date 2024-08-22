import «Subsets».SubsetDef

-- type definitions

-- copied from "Functional Programming in Lean"
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)

abbrev VecB : Nat → Type := Vect Bool

def VecB.toListBit {n : Nat} (v : VecB n) : List (Fin 2) :=
  match v with
  | Vect.nil => []
  | Vect.cons b bs =>
    if b then (1::VecB.toListBit bs) else (0::VecB.toListBit bs)

def Vect.toArray {n : Nat} : Vect α n → Array α
  | Vect.nil => #[]
  | Vect.cons b bs => (Vect.toArray bs).push b

def vecBToString {n : Nat} (v : VecB n) : String := toString (VecB.toListBit v)

instance : ToString (VecB n) where toString := vecBToString

@[reducible] def Vect.length {n : Nat} (_ : Vect α n) : Nat := n

-- def VecB.length {n : Nat} : VecB n → Nat
--   | Vect.nil => 0
--   | Vect.cons _ bs => 1 + (VecB.length bs)

-- `TODO` why doesn't this work?
-- inductive VecB2 :  Nat → Type where
--   | nil => VecB2 0
--   | cons => VecB2 n → VecB2 (n+1)

-- conversion functions

def Subset.toVecB {n : Nat} (s : Subset n) : VecB n :=
  match n, s with
  | 0, Subset.nil => Vect.nil
  | _+1, Subset.cons b bs => Vect.cons b (Subset.toVecB bs)

def VecB.toSubset {n : Nat} (v : VecB n) : Subset n :=
  match n, v with
  | 0, Vect.nil => Subset.nil
  | _+1, Vect.cons b bs => Subset.cons b (VecB.toSubset bs)

-- composition is id theorems

theorem sTV_vTS_id {n : Nat} (v : VecB n) : Subset.toVecB (VecB.toSubset v) = v := by
  induction v with
  | nil => rfl
  | cons b bs ih =>
    calc Subset.toVecB (VecB.toSubset (Vect.cons b bs))
      _ = Subset.toVecB (Subset.cons b (VecB.toSubset bs)) := by rfl
      _ = Vect.cons b (Subset.toVecB (VecB.toSubset bs)) := by rfl
      _ = Vect.cons b bs := by rw [ih]

theorem vTS_sTV_id {n : Nat} (s : Subset n) : VecB.toSubset (Subset.toVecB s) = s := by
  induction s with
  | nil => rfl
  | cons b bs ih =>
    calc VecB.toSubset (Subset.toVecB (Subset.cons b bs))
      _ = VecB.toSubset (Vect.cons b (Subset.toVecB bs)) := by rfl
      _ = Subset.cons b (VecB.toSubset (Subset.toVecB bs)) := by rfl
      _ = Subset.cons b bs := by rw [ih]
