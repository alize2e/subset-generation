import «Subsets».GrayItValProof

def Subset.helpGrayIt {m : Nat} (soFar : List (Subset (m+1))) (_ : soFar.length>0) : List (Subset m.succ) :=
    match soFar with
    | a :: xs =>
      match a with
      | Subset.cons a₀ as =>
        match h : (cons a₀ as).grayVal.snd with -- (cons a₀ as).grayVal.snd = !a∞ from Knuth book
        | false =>
          have : (grayVal (cons (!a₀) as)).fst+1 = (grayVal (cons a₀ as)).fst := dec_case_1 a₀ as h
          have : (grayVal (cons (!a₀) as)).fst+1 ≤ (grayVal (cons a₀ as)).fst := by simp only [this, Nat.le_refl]
          helpGrayIt ((cons (!a₀) as) :: (cons a₀ as) :: xs) (by simp only [List.length_cons, gt_iff_lt, Nat.zero_lt_succ])
        | true =>
          match h2 : (cons a₀ as).findMinLeft1?.isSome with
          | false => soFar
          | true =>
            let next := (cons a₀ as).change1 ((cons a₀ as).findMinLeft1?.get h2) (by simp)
            have : (grayVal next).fst+1 = (grayVal (cons a₀ as)).fst := dec_case_2 h h2
            have : (grayVal next).fst+1 ≤ (grayVal (cons a₀ as)).fst := by simp only [this, Nat.le_refl]
            helpGrayIt (next :: (cons a₀ as) :: xs) (by simp only [List.length_cons, gt_iff_lt, Nat.zero_lt_succ])
      termination_by (soFar[0].grayVal).fst

def Subset.grayIt (n : Nat) : List (Subset n) :=
  match n with
  | 0 => [nil]
  | m+1 =>
    let init := initFalse m.succ
    have : !(grayVal init).snd :=
      calc !(grayVal init).snd
        _ = !(grayVal (initFalse m.succ)).snd := by rfl
        _ = !(false) := by simp [false_grayVal_false]
        _ = true := by simp
    helpGrayIt [init] (by simp [this])

#eval! Subset.grayIt 3
#eval! List.map (Subset.grayVal) (Subset.grayIt 3)
#eval! List.map (Subset.grayVal) (Subset.grayIt 3)
