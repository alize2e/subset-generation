import «Subsets».SubsetDef

theorem Subset.in_genRec_IS {n : Nat} {b : Bool} {bs : Subset n} {l : List (Subset n)} :
  bs ∈ l → (cons b bs) ∈ (helpGR l) := by
    induction l with
    | nil => nofun
    | cons x xs ih =>
      intro h1
      cases h1
      . have : helpGR (bs::xs) = ((cons false bs) :: (cons true bs) :: helpGR xs) :=
          calc helpGR (bs::xs)
            _ = ((cons false bs) :: (cons true bs) :: helpGR xs) := by rfl
        cases b with
        | true => simp [List.any_cons, this]
        | false => simp [List.any_cons, this]
      . have : bs ∈ xs := by assumption
        have h2 : (cons b bs) ∈ helpGR xs := by simp [ih, this]
        have h3 : helpGR (x::xs) = (cons false x) :: [cons true x] ++ helpGR xs := by rfl
        simp [h2,h3]

theorem Subset.in_genRec {n : Nat} {s : Subset n} : s ∈ genRec n := by
  induction s with
  | nil =>
    have : genRec 0 = [nil] := by rfl
    simp [this]
  | cons b bs ih =>
    have h1 : genRec (cons b bs).card = helpGR (genRec bs.card) := by rfl
    have h2 : bs ∈ genRec bs.card := by simp [ih]
    simp [in_genRec_IS, h1, h2]

theorem Subset.helpGR_num {n : Nat} {l : List (Subset n)} : (helpGR l).length = 2*l.length := by
  induction l with
  | nil =>
    calc (helpGR List.nil).length
      _ = List.nil.length := by rfl
  | cons x xs ih =>
    calc (helpGR (x::xs)).length
      _ = ((cons false x) :: (cons true x) :: (helpGR xs)).length := by rfl
      _ = 2 + (helpGR xs).length := by simp_arith
      _ = 2 + 2*xs.length := by rw [ih]
      _ = 2*(xs.length+1) := by simp_arith
      _ = 2*(x::xs).length := by rfl

theorem Subset.genRec_num {n : Nat} : (genRec n).length = 2^n :=
  by induction n with
  | zero => rfl
  | succ n' ih =>
    calc (genRec n'.succ).length
      _ = (helpGR (genRec n')).length := by rfl
      _ = 2*(genRec n').length := by rw [helpGR_num]
      _ = 2*(2^n') := by rw [ih]
      _ = 2^n'.succ := by rw [Nat.pow_succ']

theorem Subset.ne_imp_helpGR_ne {n : Nat} {bs : Subset n} {l : List (Subset n)} (h : bs ∉ l) (b : Bool) :
  (cons b bs) ∉ (helpGR l) := by
    induction l with
    | nil => nofun
    | cons x xs ih =>
      simp_all only [ne_eq, List.forall_mem_ne, List.mem_cons, not_or, helpGR, forall_eq_or_imp, cons.injEq, and_false, not_false_eq_true, and_self]

theorem Subset.nodup_eq_helpGR_nodup {n : Nat} {l : List (Subset n)} (h : l.Nodup) : (helpGR l).Nodup := by
  induction l with
  | nil => simp only [List.nodup_nil, helpGR]
  | cons x xs ih =>
    simp only [List.nodup_cons] at h
    simp only [h] at ih
    simp [helpGR]
    have : x ∉ xs := by simp only [h, not_false_eq_true]
    have h1 : ¬cons false x ∈ helpGR xs := ne_imp_helpGR_ne this false
    have h2 : ¬cons true x ∈ helpGR xs := ne_imp_helpGR_ne this true
    simp only [h1, not_false_eq_true, h2, ih, and_self]

theorem Subset.genRec_nodup {n : Nat} : (genRec n).Nodup := by
  induction n with
  | zero => simp only [genRec, List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self]
  | succ n' ih =>
    simp only [genRec]
    exact nodup_eq_helpGR_nodup ih
