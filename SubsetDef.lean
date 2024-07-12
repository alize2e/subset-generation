inductive Subset : Nat → Type
  | nil  : Subset 0
  | cons : Bool → Subset n → Subset (n+1)

def Subset.beq {n m : Nat} : Subset n → Subset m → Bool
  | nil, nil    => true
  | cons a as, cons b bs => a == b && Subset.beq as bs
  | _,     _     => false

def Subset.append {n m : Nat} : Subset n → Subset m → Subset (m+n)
  | nil, bs => bs
  | cons a as, bs => cons a (append as bs)

@[reducible] def Subset.card {n : Nat} (_ : Subset n) : Nat := n

def Subset.toListBit {n : Nat} (s : Subset n) : List (Fin 2) :=
  match s with
  | Subset.nil => []
  | Subset.cons b bs =>
    if b then (1::Subset.toListBit bs) else (0::Subset.toListBit bs)

def Subset.toListBool {n : Nat} (s : Subset n) : List Bool :=
  match s with
  | Subset.nil => []
  | Subset.cons b bs => b :: Subset.toListBool bs

def subToString {n : Nat} (s : Subset n) : String := toString (Subset.toListBit s)

instance : ToString (Subset n) where toString := subToString

@[reducible] def Subset.cast (eq : n = m) (xs : Subset m) : Subset n := eq ▸ xs --idk if reducible changes anything here

def Subset.helpGR {n : Nat} : List (Subset n) → List (Subset (n+1))
  | [] => []
  | x :: xs => (Subset.cons false x) :: (Subset.cons true x) :: helpGR xs

def Subset.genRec (n : Nat) : List (Subset n) :=
  match n with
  | 0 => [Subset.nil]
  | n'+1 => helpGR (Subset.genRec n')

def Fin.toNat (f : Fin n) : Nat := f.val

def Nat.toFin (k n : Nat) (lt : k<n) : Fin n := ⟨k, lt⟩

def initFalse (k : Nat) : Subset k :=
  match k with
  | 0 => Subset.nil
  | k'+1 => Subset.cons false (initFalse k')

def initTrue (k : Nat) : Subset k :=
  match k with
  | 0 => Subset.nil
  | k'+1 => Subset.cons true (initTrue k')

theorem append_card {n m : Nat} (as : Subset n) (bs : Subset m) : (Subset.append as bs).card = as.card + bs.card := by
  induction as with
  | nil =>
    calc (Subset.append Subset.nil bs).card
      _ = bs.card := by rfl
      _ = Subset.nil.card + bs.card := by simp
  | cons a as' ih =>
    calc (Subset.append (Subset.cons a as') bs).card
      _ = (Subset.cons a (Subset.append as' bs)).card := by rfl
      _ = (Subset.append as' bs).card + 1 := by rfl
      _ = as'.card + bs.card + 1 := by rw [ih]
      _ = as'.card + 1 + bs.card := by simp_arith

example {n : Nat} (s : Subset n) (b : Bool) : (Subset.cons b s).card = s.card + 1 := by simp
example (n m : Nat) (as : Subset n) (bs : Subset m) : as.card = bs.card → n = m := by simp
example (n m : Nat) (s : Subset n) : s.card = m → n = m := by simp

inductive SubsetXS (α : Type u) : List α → Type u where
 | nil : SubsetXS α []
 | cons : Bool → SubsetXS α xs → SubsetXS α (x::xs)
