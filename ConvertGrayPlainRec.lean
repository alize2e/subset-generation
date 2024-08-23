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

theorem Subset.φ'_p_eq_g {n : Nat} : (genRec' n).map φ' = (grayRecSlides n) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    calc (genRec' n'.succ).map φ'
      _ = (((genRec' n').map (cons false)) ++ ((genRec' n').map (cons true))).map φ' := by rfl
      _ = ((genRec' n').map (cons false)).map φ' ++ ((genRec' n').map (cons true)).map φ' := List.map_append φ' ((genRec' n').map (cons false)) ((genRec' n').map (cons true))
      _ = (genRec' n').map (φ'∘(cons false)) ++ (genRec' n').map (φ'∘(cons true)) := by simp only [List.map_map]
      _ = (genRec' n').map ((φ'' false)∘(cons false)) ++ (genRec' n').map ((φ'' false)∘(cons true)) := by rfl
      _ = (genRec' n').map (fun s : Subset n' => cons (xor false false) (φ'' false s)) ++ (genRec' n').map (fun s : Subset n' => cons (xor false true) (φ'' true s)) := by rfl
      _ = (genRec' n').map (fun s : Subset n' => cons false (φ'' false s)) ++ (genRec' n').map (fun s : Subset n' => cons true (φ'' true s)) := by rfl
      _ = (genRec' n').map ((cons false)∘(φ'' false)) ++ (genRec' n').map ((cons true)∘(φ'' true)) := by rfl
      _ = (((genRec' n').map (φ'' false)).map (cons false)) ++ (((genRec' n').map (φ'' true)).map (cons true)) := by simp [List.map_map]
      _ = (((genRec' n').map φ').map (cons false)) ++ (((genRec' n').map (φ'' true)).map (cons true)) := by rfl
      _ = ((grayRecSlides n').map (cons false)) ++ (((genRec' n').map (φ'' true)).map (cons true)) := by rw [ih]

theorem Subset.ψ'_g_eq_p {n : Nat} : (grayRecSlides n).map ψ' = (genRec' n) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    if h : n'=0 then
      have : n'.succ = 1 := by simp [h]
      rw [this]
      rfl
    else
      match n' with
      | Nat.zero => contradiction
      | Nat.succ n'' =>
        -- simp [←grayRecSlides_xor11]
        calc (grayRecSlides n''.succ.succ).map ψ'
          _ = (((grayRecSlides n''.succ).map (cons false)) ++ ((grayRecSlides n''.succ).map (cons false)).map xor_11).map ψ' := by simp [←grayRecSlides_xor11]
          _ = (((grayRecSlides n''.succ).map (cons false)) ++ ((grayRecSlides n''.succ).map (cons false)).map xor_11).map ψ' := by simp [←grayRecSlides_xor11]
          _ = (grayRecSlides n''.succ).map (ψ' ∘ (cons false)) ++ ((grayRecSlides n''.succ).map (ψ' ∘ xor_11 ∘ cons false)) := by simp only [List.map_map, List.map_append]
          -- _ = (((helpGRS n''.succ false).map (cons false)) ++ ((helpGRS n''.succ true).map (cons true))).map ψ' := by rfl
        -- simp only [genRec', ←grayRecSlides_xor11, grayRecSlides_IS, ih]
