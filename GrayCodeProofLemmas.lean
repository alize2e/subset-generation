import Subsets.GrayRecComp

def Subset.num_changes {n : Nat} : Subset n → Subset n → Nat
  | nil, nil => 0
  | cons true as, cons true bs => num_changes as bs
  | cons false as, cons false bs => num_changes as bs
  | cons _ as, cons _ bs => 1 + num_changes as bs

theorem Subset.symm_num_changes {n : Nat} {as bs : Subset n} : num_changes as bs = num_changes bs as := by
  induction n with
  | zero =>
    match as, bs with
    | nil, nil => rfl
  | succ n' ih =>
    match as, bs with
    | cons true xs, cons true ys =>
      calc num_changes (cons true xs) (cons true ys)
        _ = num_changes xs ys := by rfl
        _ = num_changes ys xs := by rw [ih]
        _ = num_changes (cons true ys) (cons true xs) := by rfl
    | cons false xs, cons false ys =>
      calc num_changes (cons false xs) (cons false ys)
        _ = num_changes xs ys := by rfl
        _ = num_changes ys xs := by rw [ih]
        _ = num_changes (cons false ys) (cons false xs) := by rfl
    | cons true xs, cons false ys =>
      calc num_changes (cons true xs) (cons false ys)
        _ = 1 + num_changes xs ys := by rfl
        _ = 1 + num_changes ys xs := by rw [ih]
        _ = num_changes (cons false ys) (cons true xs) := by rfl
    | cons false xs, cons true ys =>
      calc num_changes (cons false xs) (cons true ys)
        _ = 1 + num_changes xs ys := by rfl
        _ = 1 + num_changes ys xs := by rw [ih]
        _ = num_changes (cons true ys) (cons false xs) := by rfl

theorem Subset.cons_same_num_changes {n : Nat} {as bs : Subset n} {x : Bool} : num_changes (cons x as) (cons x bs) = num_changes as bs := by
  cases x
  repeat rfl

theorem Subset.eq_num_changes_eq_zero {n : Nat} {as : Subset n} : num_changes as as = 0 := by
  induction as with
  | nil => rfl
  | cons b bs ih =>
    have : num_changes (cons b bs) (cons b bs) = num_changes bs bs := by cases b <;> repeat rfl
    rw [this]
    rw [ih]

-- List.get_map not imported, and not working ://///
theorem List.diy_get_map (α β : Type) (f : α → β) (l : List α) (i : Nat) {h : i<l.length} : (l.map f)[i]'(by simp[h]) = f l[i] := by
  induction i generalizing l with
  | zero =>
    match l with
    | x::xs => rfl
  | succ i' ih =>
    have : i'.succ<(l.map f).length := by simp [h]
    match l with
    | x::xs =>
      have : (xs.map f).length.succ = ((x::xs).map f).length := by rfl
      have : (xs.map f).length = xs.length := by simp
      calc ((x::xs).map f)[i'.succ]
        _ = (xs.map f)[i'] := by simp
        _ = f xs[i'] := by rw [ih]

theorem List.diy_reverse_zero_last {α : Type} {l : List α} {h : 0<l.length} {h' : l.reverse.length-1<l.reverse.length} : l.reverse[l.reverse.length-1] = l[0] := by
  match l with
  | x::xs =>
    have : (x::xs).reverse = xs.reverse++[x] := List.reverse_cons x xs
    have : ¬ (xs.reverse++[x]).length-1 < xs.reverse.length := by simp
    calc (x::xs).reverse[(x::xs).reverse.length-1]
      _ = (xs.reverse++[x])[(xs.reverse++[x]).length-1] := by simp
      _ = x := List.get_last this
      _ = (x::xs)[0] := by simp

-- copied from documentation, idk why not imported
theorem Nat.sub_one_add_one_eq_of_pos : ∀ {n}, 0 < n → (n - 1) + 1 = n
  | _+1, _ => rfl

-- idk why not imported from documentation
theorem Nat.sub_lt_sub_right : ∀ {a b c : Nat}, c ≤ a → a < b → a - c < b - c
  | 0, _, _, hle, h => by
    rw [Nat.eq_zero_of_le_zero hle, Nat.sub_zero, Nat.sub_zero]
    exact h
  | _, _, 0, _, h => by
    rw [Nat.sub_zero, Nat.sub_zero]
    exact h
  | _+1, _+1, _+1, hle, h => by
    rw [Nat.add_sub_add_right, Nat.add_sub_add_right]
    exact Nat.sub_lt_sub_right (le_of_succ_le_succ hle) (lt_of_succ_lt_succ h)
