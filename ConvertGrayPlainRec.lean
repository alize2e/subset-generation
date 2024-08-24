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
#eval (Subset.genRec' 3)
#eval (Subset.genRec' 3)

theorem Subset.ψ'_cons_false_comm {n : Nat} : ψ' ∘ (cons false : Subset n → Subset (n+1)) = (cons false) ∘ ψ' := by rfl

theorem Subset.map_map (f g : Bool → Bool) (s : Subset n) : map g (map f s) = map (g ∘ f) s := by
  induction s with
  | nil => rfl
  | cons b bs ih =>
    calc map g (map f (cons b bs))
      _ = cons ((g∘f) b) (map g (map f bs)) := by rfl
      _ = cons ((g∘f) b) (map (g∘f) bs) := by rw [ih]

theorem Subset.map_id (s : Subset n) : map (fun x => x) s = s := by
  induction s with
  | nil => rfl
  | cons b bs ih => simp [map, ih]

theorem Subset.ψ''_true {n : Nat} {s : Subset n} : ∀ b : Bool, ψ'' b s = (ψ' s).map (xor b) := by
  induction s with
  | nil =>
    intro b
    match b with
    | false => rfl
    | true => rfl
  | cons x xs ih =>
    intro b
    calc ψ'' b (cons x xs)
      _ = cons (xor b x) (ψ'' (xor b x) xs) := by rfl
      _ = cons (xor b x) ((ψ' xs).map (xor (xor b x))) := by rw [ih]
      _ = map (fun x => x) (cons (xor b x) ((ψ' xs).map (xor (xor b x)))) := by rw [map_id]
      _ = map (fun x => xor x false) (cons (xor b x) ((ψ' xs).map (xor (xor b x)))) := by simp only [Bool.xor_false]
      _ = map (fun x => xor false x) (cons (xor b x) ((ψ' xs).map (xor (xor b x)))) := by simp only [Bool.xor_comm]
      _ = map (fun x => xor (xor b b) x) (cons (xor b x) ((ψ' xs).map (xor (xor b x)))) := by rw [Bool.xor_self]
      _ = map (fun x => xor b (xor b x)) (cons (xor b x) ((ψ' xs).map (xor (xor b x)))) := by simp only [Bool.xor_assoc]
      _ = map (xor b ∘ xor b) (cons (xor b x) ((ψ' xs).map (xor (xor b x)))) := by rfl
      _ = map (xor b) (map (xor b) (cons (xor b x) ((ψ' xs).map (xor (xor b x))))) := by rw [map_map]
      _ = map (xor b) (cons (xor b (xor b x)) ((((ψ' xs).map (xor (xor b x)))).map (xor b))) := by rfl
      _ = map (xor b) (cons (xor b (xor b x)) ((ψ' xs).map ((xor b) ∘ (xor (xor b x))))) := by rw [map_map]
      _ = map (xor b) (cons (xor b (xor b x)) ((ψ' xs).map (fun y => xor b (xor (xor b x) y)))) := by rfl
      _ = map (xor b) (cons (xor (xor b b) x) ((ψ' xs).map (fun y => xor (xor b b) (xor x y)))) := by simp only [Bool.xor_assoc]
      _ = map (xor b) (cons (xor false x) ((ψ' xs).map (fun y => xor false (xor x y)))) := by simp only [Bool.xor_self]
      _ = map (xor b) (cons (xor false x) ((ψ' xs).map (fun y => xor (xor false x) y))) := by simp only [Bool.xor_assoc]
      _ = map (xor b) (cons (xor false x) ((ψ' xs).map (xor (xor false x)))) := by rfl
      _ = map (xor b) (cons (xor false x) (ψ''  (xor false x) xs)) := by rw [ih]
      _ = map (xor b) (ψ'' false (cons x xs)) := by rfl
      _ = map (xor b) (ψ' (cons x xs)) := by rfl

theorem Subset.φ'_cons_false_comm {n : Nat} : φ' ∘ (cons false : Subset n → Subset (n+1)) = (cons false) ∘ φ' := by rfl

theorem Subset.φ'_cons_true' {n : Nat} {p : Subset n} : φ' (cons true p) = xor_11 (cons false (φ' p)) :=
  match p with
  | nil => rfl
  | cons b bs => by simp [φ', φ'', xor_11]

theorem Subset.φ'_cons_true {n : Nat} : φ' ∘ (cons true : Subset n → Subset (n+1)) = xor_11 ∘ cons false ∘ φ' := by funext; simp [φ'_cons_true']

theorem Subset.φ'_cons_true'' {n : Nat} : φ' ∘ (cons true : Subset n → Subset (n+1)) = (xor_11 ∘ cons false) ∘ φ' := by funext; simp [φ'_cons_true']

theorem Subset.φ'_p_eq_g {n : Nat} : (genRec' n).map φ' = (grayRecSlides n) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    calc (genRec' n'.succ).map φ'
      _ = (((genRec' n').map (cons false)) ++ ((genRec' n').map (cons true))).map φ' := by rfl
      _ = ((genRec' n').map (cons false)).map φ' ++ ((genRec' n').map (cons true)).map φ' := List.map_append φ' ((genRec' n').map (cons false)) ((genRec' n').map (cons true))
      _ = (genRec' n').map (φ'∘(cons false)) ++ (genRec' n').map (φ'∘(cons true)) := by simp only [List.map_map]
      _ = (genRec' n').map ((cons false) ∘ φ') ++ (genRec' n').map (φ'∘(cons true)) := by rw [φ'_cons_false_comm]
      _ = (genRec' n').map ((cons false) ∘ φ') ++ (genRec' n').map (xor_11 ∘ cons false ∘ φ') := by rw [φ'_cons_true]
      _ = ((genRec' n').map φ').map (cons false) ++ (((genRec' n').map φ').map (cons false)).map xor_11 := by simp only [List.map_map]
      _ = (grayRecSlides n').map (cons false) ++ ((grayRecSlides n').map (cons false)).map xor_11 := by rw [ih]
      _ = grayRecSlides n'.succ := by rw [grayRecSlides_xor11]

theorem Subset.ψ'_g_eq_p {n : Nat} : ∀ nl ≤ n, (grayRecSlides nl).map ψ' = (genRec' nl) := by
  induction n with
  | zero =>
    intro nl
    intro h0
    have : ¬ 0<nl := by simp [h0]
    match nl with
    | Nat.zero => rfl
    | Nat.succ nl' => contradiction
  | succ n' ih =>
    if h : n'=0 then
      have : n'.succ = 1 := by simp only [h]
      intro nl
      intro h0
      rw [this] at *
      if h' : nl = 1 then
        rw [h']
        rfl
      else
        have : nl<1 := Nat.lt_of_le_of_ne h0 h'
        rw [ih]
        rw [h]
        simp_arith only [Nat.le_of_lt_succ, this]
    else
      match n' with
      | Nat.zero => contradiction
      | Nat.succ n'' =>
        intro nl
        intro h0
        if h' : nl = n''.succ.succ then
          rw [h']
          simp [←grayRecSlides_xor11]
          simp [genRec']
          have : List.map (ψ' ∘ cons false ∘ cons false) (grayRecSlides n'') = List.map ((ψ' ∘ cons false) ∘ cons false) (grayRecSlides n'') := by simp [ψ'_cons_false_comm']
      --     calc List.map (ψ' ∘ cons false ∘ cons false) (grayRecSlides n'') ++
      -- (List.map (ψ' ∘ cons false ∘ xor_11 ∘ cons false) (grayRecSlides n'') ++
      --   (List.map (ψ' ∘ xor_11 ∘ cons false ∘ cons false) (grayRecSlides n'') ++
      --     List.map (ψ' ∘ xor_11 ∘ cons false ∘ xor_11 ∘ cons false) (grayRecSlides n'')))
          -- calc (grayRecSlides n''.succ.succ).map ψ'
          --   _ = (((grayRecSlides n''.succ).map (cons false)) ++ ((grayRecSlides n''.succ).map (cons false)).map xor_11).map ψ' := by simp [←grayRecSlides_xor11]
          --   _ = (((grayRecSlides n''.succ).map (cons false)) ++ ((grayRecSlides n''.succ).map (cons false)).map xor_11).map ψ' := by simp [←grayRecSlides_xor11]
          --   _ = (grayRecSlides n''.succ).map (ψ' ∘ (cons false)) ++ ((grayRecSlides n''.succ).map (ψ' ∘ xor_11 ∘ cons false)) := by simp only [List.map_map, List.map_append]
            -- _ = (((helpGRS n''.succ false).map (cons false)) ++ ((helpGRS n''.succ true).map (cons true))).map ψ' := by rfl
        else
          have : nl < n''.succ.succ := Nat.lt_of_le_of_ne h0 h'
          rw [ih]
          apply (Nat.le_of_lt_succ this)
