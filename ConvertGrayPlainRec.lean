import Subsets.GrayRecSlides

def Subset.genRec' (n : Nat) : List (Subset n) :=
  match n with
  | 0 => [nil]
  | n'+1 => ((genRec' n').map (cons false)) ++ ((genRec' n').map (cons true))

-- conversion functions
def Subset.ψ'' {n : Nat} (parity : Bool) : Subset n → Subset n
  | nil => nil
  | cons curr rest => cons (xor parity curr) (ψ'' (xor parity curr) rest)

def Subset.ψ' {n : Nat} (s : Subset n) : Subset n := ψ'' false s

def Subset.φ'' {n : Nat} (last : Bool) : Subset n → Subset n
  | nil => nil
  | cons curr rest => cons (xor last curr) (φ'' curr rest)

def Subset.φ' {n : Nat} (s : Subset n) : Subset n := φ'' false s

-- Subset.map lemmas
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

-- cons lemmas
theorem Subset.ψ''_b {n : Nat} {s : Subset n} : ∀ b : Bool, ψ'' b s = (ψ' s).map (xor b) := by
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

-- composition is id lemmas
theorem Subset.ψ''_b_φ''_b_id {n : Nat} {gray : Subset n} : ∀ b : Bool, (ψ'' b ∘ φ'' b) gray = gray := by
  induction gray with
  | nil => intro b; rfl
  | cons g gs ih =>
    intro b
    calc (ψ'' b ∘ φ'' b) (cons g gs)
      _ = ψ'' b (φ'' b (cons g gs)) := by rfl
      _ = ψ'' b (cons (xor b g) (φ'' g gs)) := by rfl
      _ = cons (xor b (xor b g)) (ψ'' (xor b (xor b g)) (φ'' g gs)) := by rfl
      _ = cons (xor (xor b b) g) (ψ'' (xor (xor b b) g) (φ'' g gs)) := by simp only [Bool.xor_assoc]
      _ = cons (xor false g) (ψ'' (xor false g) (φ'' g gs)) := by simp only [Bool.xor_self]
      _ = cons g (ψ'' g (φ'' g gs)) := by simp only [Bool.false_xor]
      _ = cons g (((ψ'' g) ∘ (φ'' g)) gs) := by rfl
      _ = cons g gs := by rw [ih]

theorem Subset.ψ'_φ'_id : ∀ n : Nat, ψ' ∘ φ' = fun (s : Subset n) => s := by
  intro n
  funext gray
  calc (ψ' ∘ φ') gray
    _ = (ψ'' false ∘ φ'' false) gray := by rfl
    _ = gray := ψ''_b_φ''_b_id false

theorem Subset.φ''_b_ψ''_b_id {n : Nat} {plain : Subset n} : ∀ b : Bool, (φ'' b ∘ ψ'' b) plain = plain := by
  induction plain with
  | nil => intro b; rfl
  | cons p ps ih =>
    intro b
    calc (φ'' b ∘ ψ'' b) (cons p ps)
      _ = φ'' b (cons (xor b p) (ψ'' (xor b p) ps)) := by rfl
      _ = cons (xor b (xor b p)) (φ'' (xor b p) (ψ'' (xor b p) ps)) := by rfl
      _ = cons (xor (xor b b) p) (φ'' (xor b p) (ψ'' (xor b p) ps)) := by simp only [Bool.xor_assoc]
      _ = cons (xor false p) (φ'' (xor b p) (ψ'' (xor b p) ps)) := by simp only [Bool.xor_self]
      _ = cons p (φ'' (xor b p) (ψ'' (xor b p) ps)) := by simp only [Bool.false_xor]
      _ = cons p (((φ'' (xor b p)) ∘ (ψ'' (xor b p))) ps) := by rfl
      _ = cons p ps := by rw [ih]

theorem Subset.φ'_ψ'_id : ∀ n : Nat, φ' ∘ ψ' = fun (s : Subset n) => s := by
  intro n
  funext plain
  calc (φ' ∘ ψ') plain
    _ = (φ'' false ∘ ψ'' false) plain := by rfl
    _ = plain := φ''_b_ψ''_b_id false

-- conversion theorems
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

theorem Subset.ψ'_g_eq_p {n : Nat} : (grayRecSlides n).map ψ' = (genRec' n) := by
  rw [←φ'_p_eq_g]
  calc List.map ψ' (List.map φ' (genRec' n))
    _ = List.map (ψ' ∘ φ') (genRec' n) := by rw [List.map_map]
    _ = (genRec' n).map (fun s => s) := by rw [ψ'_φ'_id]
    _ = (genRec' n) := List.map_id' (genRec' n)
