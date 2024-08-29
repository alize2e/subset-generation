import Subsets.GrayItValProof

def initPointers {m : Nat} (soFar : List (Fin m.succ)) (n : Nat) (h : n<m.succ) : List (Fin m.succ) :=
  match n with
  | .zero => (Nat.zero.toFin m.succ h) :: soFar
  | .succ n' =>
    have : n' < m.succ :=
      calc n'
        _ < n'.succ := by simp only [Nat.succ_eq_add_one, Nat.lt_add_one]
        _ < m.succ := h
    initPointers ((n'.succ.toFin m.succ h) :: soFar) n' this

theorem initPointers_len {m : Nat} {soFar : List (Fin m.succ)} {n : Nat} {h : n<m.succ} :
  (initPointers soFar n h).length = soFar.length + n.succ := by
    induction n generalizing soFar with
    | zero => rfl
    | succ n' ih =>
      have : n' < m.succ :=
        calc n'
          _ < n'.succ := by simp only [Nat.succ_eq_add_one, Nat.lt_add_one]
          _ < m.succ := h
      calc (initPointers soFar n'.succ h).length
        _ = (initPointers ((n'.succ.toFin m.succ h) :: soFar) n' this).length := by rfl
        _ = ((n'.succ.toFin m.succ h) :: soFar).length + n'.succ := by rw [ih]
        _ = soFar.length + 1 + n'.succ := by rfl
        _ = soFar.length + n'.succ.succ := by simp_arith

def Subset.helpGrayL {n : Nat} (curr : Subset n) (soFar : List (Subset n)) (f : List (Fin n.succ))
  (f_len : f.length = n.succ) : List (Subset n) :=
    let soFar' := curr :: soFar
    let j := f[0]
    let f' : List (Fin n.succ) := f.set 0 (0 : Fin n.succ)
    have f'_len : f'.length = n.succ := by simp only [Nat.succ_eq_add_one, List.length_set f, f_len]
    if h_end : j = n then
      soFar'
    else
      have j_lt_n : j < n := by
        have : j < n.succ := f[0].2
        have : j ≤ n := by simp [Nat.le_of_lt_succ]
        simp [Nat.lt_iff_le_and_ne, this, h_end]
      have : j.succ.val < f'.length :=
        calc j.succ.val
          _ < n.succ := by simp [j_lt_n]
          _ = f'.length := by rw [f'_len]
      let f'' : List (Fin n.succ) := f'.set j f'[j.succ]
      have f''_len : f''.length = n.succ := by simp only [Nat.succ_eq_add_one, List.length_set f', f'_len]
      let f''' : List (Fin n.succ) := f''.set j.succ (j.succ.val.toFin n.succ (by simp only [Nat.succ_eq_add_one, Fin.val_succ, Nat.add_lt_add_iff_right, j_lt_n]))
      have f'''_len : f'''.length = n.succ := by simp only [Nat.succ_eq_add_one, List.length_set f'', f''_len]
      let curr' := curr.change1 j j_lt_n
      have : curr'.grayVal.fst+1 = curr.grayVal.fst := sorry
      have : curr'.grayVal.fst+1 ≤ curr.grayVal.fst := by simp only [this, Nat.le_refl]
      helpGrayL curr' soFar' f''' f'''_len
    termination_by curr.grayVal.fst

def Subset.grayLoopless (n : Nat) : List (Subset n) :=
  match n with
  | .zero => [nil]
  | .succ n' =>
    helpGrayL (initFalse n'.succ) ([] : List (Subset n'.succ)) (initPointers ([] : List (Fin n'.succ.succ)) n'.succ (Nat.lt_add_one n'.succ)) (by simp only [Nat.succ_eq_add_one, initPointers_len, List.length_nil, Nat.zero_add])
