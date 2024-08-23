import Subsets.GrayRecSlides

def Subset.genRec' (n : Nat) : List (Subset n) :=
  match n with
  | 0 => [nil]
  | n'+1 => ((genRec' n').map (cons false)) ++ ((genRec' n').map (cons true))

def Subset.start' {n : Nat} (g : Subset n) : Bool :=
  match g with
  | nil => false
  | cons b _ => b

def Subset.ψ'' {n : Nat} (parity : Bool) : Subset n → Subset n
  | nil => nil
  | cons curr rest => cons (xor parity curr) (ψ'' (xor parity curr) rest)

def Subset.ψ' {n : Nat} (s : Subset n) : Subset n := ψ'' false s

def Subset.φ'' {n : Nat} (last : Bool) : Subset n → Subset n
  | nil => nil
  | cons curr rest => cons (xor last curr) (φ'' curr rest)

def Subset.φ' {n : Nat} (s : Subset n) : Subset n := φ'' false s

#eval (Subset.genRec' 4).map Subset.φ' == (Subset.grayRecSlides 4)
#eval (Subset.genRec' 3) == (Subset.grayRecSlides 3).map Subset.ψ'
