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

-- def distinct {α : Type} [BEq α] : List α → Bool
--   | [] => true
--   | x::xs => distinct xs && !xs.contains x

-- theorem Subset.t {n : Nat} {b : Bool} {x : Subset n} {l : List (Subset n)} {h : !l.contains x} :
--   !(helpGR l).contains (cons b x) := by
--     induction l with
--     | nil => rfl
--     | cons x xs ih =>
--       have : !(helpGR (x::xs)).contains (cons b x) = !((cons false x) :: (cons true x) :: helpGR xs).contains (cons b x) := by simp
--       rw [this]

-- theorem Subset.helpGR_distinct_IS {n : Nat} (l : List (Subset n)) (h : distinct l) : distinct (helpGR l) := by
--   induction l with
--   | nil => rfl
--   | cons x xs ih =>
--     calc distinct (helpGR (x::xs))
--       _ = distinct ((cons false x) :: (cons true x) :: helpGR xs) := by rfl
--       _ = distinct ((cons true x) :: helpGR xs) && !((cons true x) :: helpGR xs).contains (cons false x) := by rfl

-- theorem Subset.genRec_distinct {n : Nat} : distinct (genRec n) := by
--   induction n with
--   | zero => rfl
--   | succ n' ih =>
--     calc distinct (genRec n'.succ)
--       _ = distinct (helpGR (genRec n')) := by rfl

-- theorem Subset.genRec_no_dup {n : Nat} : Nodup (genRec n) := by
--   induction n with
--   | zero =>
--     calc Nodup (genRec 0)
--       _ = Nodup [Subset.nil] := by rfl
--       -- _ = Nodup [] := by simp [pairwise_cons]
--       -- _ = true := by simp [Pairwise.nil]
--   | succ n' ih =>


--Nodup, Pairwise?
-- theorem nodup_cons {a : α} {l : List α} : Nodup (a :: l) ↔ a ∉ l ∧ Nodup l := by
-- theorem pairwise_map {l : List α} :
    -- (l.map f).Pairwise R ↔ l.Pairwise fun a b => R (f a) (f b) := by

-- List.any_cons

-- theorem any_eq {l : List α} : l.any p = decide (∃ x, x ∈ l ∧ p x) := by induction l <;> simp [*]

-- @[simp] theorem any_eq_true {l : List α} : l.any p ↔ ∃ x, x ∈ l ∧ p x := by simp [any_eq]

-- theorem contains_eq_any_beq [BEq α] (l : List α) (a : α) : l.contains a = l.any (a == ·) := by
--   induction l with simp | cons b l => cases b == a <;> simp [*]

-- example {n : Nat} {b : Bool} {bs : Subset n} {l : List (Subset n)} : (helpGR l).contains (cons b bs) → l.contains bs :=
--   calc (helpGR l).contains (cons b bs)
--     _ = decide (∃ x, x ∈ l ∧ (cons b bs) == (cons b x)) := by simp [List.contains_eq_any_beq, ]

-- example {n : Nat} {b : Bool} {bs : Subset n} {l : List (Subset n)} : l.contains bs → (helpGR l).contains (cons b bs) := by
--   intro h
--   -- have : l.any (bs == ⬝ ) := by simp[List.contains_eq_any_beq]
--   have : ∃ x, x ∈ l ∧ bs == x := by simp [List.contains_eq_any_beq, List.any_eq_true]
--   induction l with simp [List.beq] | cons b l => cases b == a <;> simp [*]
