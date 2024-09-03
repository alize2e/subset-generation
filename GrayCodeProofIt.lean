import Subsets.GrayItValProof

theorem Subset.num_changes_change1_eq_1 {n : Nat} {s : Subset n} {m : Nat} {h : m<n} : num_changes (s.change1 m h) s = 1 := by
  induction s generalizing m with
  | nil => nofun
  | cons b bs ih =>
    match m with
    | Nat.zero =>
      calc num_changes ((cons b bs).change1 0 h) (cons b bs)
        _ = num_changes (cons (!b) bs) (cons b bs) := by rfl
        _ = 1 + num_changes bs bs := cons_diff_num_changes
        _ = 1 := by simp_arith [eq_num_changes_eq_zero]
    | Nat.succ m' =>
      have : 1 ≤ m'.succ := by simp_arith [Nat.succ_pos]
      have : m' < bs.card :=
        calc m'
          _ = m'.succ - 1 := by simp_arith
          _ < (cons b bs).card - 1 := Nat.sub_lt_sub_right this h
      calc num_changes ((cons b bs).change1 m'.succ h) (cons b bs)
        _ = num_changes (cons b (bs.change1 m' this)) (cons b bs) := by rfl
        _ = num_changes (bs.change1 m' this) bs := cons_same_num_changes
        _ = 1 := ih

def Subset.helpGrayIt_proof {m : Nat} (soFar : List (Subset (m+1))) (_ : soFar.length>0)
  (proof : isGray soFar) : {l : (List (Subset m.succ)) // isGray l} :=
    match soFar with
    | a :: xs =>
      match a with
      | Subset.cons a₀ as =>
        match h : (cons a₀ as).grayVal.snd with -- (cons a₀ as).grayVal.snd = !a∞ from Knuth book
        | false =>
          have : (grayVal (cons (!a₀) as)).fst+1 = (grayVal (cons a₀ as)).fst := dec_case_1 a₀ as h
          have : (grayVal (cons (!a₀) as)).fst+1 ≤ (grayVal (cons a₀ as)).fst := by simp only [this, Nat.le_refl]
          have proof_new : num_changes (cons (!a₀) as) (cons a₀ as) = 1 := by simp_arith [cons_diff_num_changes, eq_num_changes_eq_zero]
          have proof' : isGray ((cons (!a₀) as) :: (cons a₀ as) :: xs) := by simp only [isGray, proof_new, proof, and_self, decide_True]
          helpGrayIt_proof ((cons (!a₀) as) :: (cons a₀ as) :: xs) (by simp only [List.length_cons, gt_iff_lt, Nat.zero_lt_succ]) proof'
        | true =>
          match h2 : (cons a₀ as).findMinLeft1?.isSome with
          | false =>
            ⟨(cons a₀ as :: xs), proof⟩
          | true =>
            let next := (cons a₀ as).change1 ((cons a₀ as).findMinLeft1?.get h2) (by simp)
            have : (grayVal next).fst+1 = (grayVal (cons a₀ as)).fst := dec_case_2 h h2
            have : (grayVal next).fst+1 ≤ (grayVal (cons a₀ as)).fst := by simp only [this, Nat.le_refl]
            have proof_new : num_changes ((cons a₀ as).change1 ((cons a₀ as).findMinLeft1?.get h2) (by simp)) (cons a₀ as) = 1 := num_changes_change1_eq_1
            have proof' : isGray (next :: (cons a₀ as) :: xs) := by simp [proof_new, proof, isGray]
            helpGrayIt_proof (next :: (cons a₀ as) :: xs) (by simp only [List.length_cons, gt_iff_lt, Nat.zero_lt_succ]) proof'
      termination_by (soFar[0].grayVal).fst

def Subset.grayIt_proof (n : Nat) : {l : (List (Subset n)) // isGray l} :=
  match n with
  | 0 => ⟨[nil], rfl⟩
  | m+1 =>
    let init := initFalse m.succ
    have : !(grayVal init).snd :=
      calc !(grayVal init).snd
        _ = !(grayVal (initFalse m.succ)).snd := by rfl
        _ = !(false) := by simp [false_grayVal_false]
        _ = true := by simp
    helpGrayIt_proof [init] (by simp [this]) rfl

theorem Subset.grayItProof {n : Nat} : isGray (grayIt_proof n).1 := (grayIt_proof n).2
