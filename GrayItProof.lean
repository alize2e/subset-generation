import «Subsets».GrayItValProof

def Subset.helpGrayIt {m : Nat} (parity : Bool) (soFar : List (Subset (m+1)))
  (soFar_len : soFar.length>0) (parity_def : parity = !(soFar[0].grayVal).snd) : List (Subset m.succ) :=
    match soFar with
    | a :: xs =>
      match a with
      | Subset.cons a₀ as =>
        match h : parity with
        | true =>
          let a' := cons (!a₀) as
          have parity_def' : (grayVal a').snd = true :=
            calc (grayVal a').snd
              _ = xor (!a₀) (grayVal as).snd := by rfl
              _ = !(xor a₀ (grayVal as).snd) := by simp only [Bool.not_xor]
              _ = !(grayVal (cons a₀ as)).snd := by rfl
              _ = true := by simp only [parity_def, List.cons_getElem_zero]
          have : (grayVal (cons a₀ as)).snd = false :=
            calc (grayVal (cons a₀ as)).snd
              _ = !!(grayVal (cons a₀ as :: xs)[0]).snd := by simp only [List.cons_getElem_zero, Bool.not_not]
              _ = !true := by rw [parity_def]
          have : (grayVal (cons (!a₀) as)).fst+1 = (grayVal (cons a₀ as)).fst := dec_case_1 a₀ as this
          have : (grayVal (cons (!a₀) as)).fst+1 ≤ (grayVal (cons a₀ as)).fst := by simp only [this, Nat.le_refl]
          helpGrayIt (!parity) (a' :: soFar) (by simp only [List.length_cons, gt_iff_lt, Nat.zero_lt_succ]) (by simp only [h, Bool.not_true, List.cons_getElem_zero, parity_def'])
        | false =>
          let out := minLeft1? (cons a₀ as)
          match h2 : out with
          | none => soFar
          | some next =>
            have : (grayVal next).fst+1 = (grayVal (cons a₀ as)).fst := sorry
            have : (grayVal next).fst+1 ≤ (grayVal (cons a₀ as)).fst := by simp only [this, Nat.le_refl]
            have parity_def' : (grayVal next).snd = false := sorry
            helpGrayIt (!parity) (next :: soFar) (by simp only [List.length_cons, gt_iff_lt, Nat.zero_lt_succ]) (by simp only [h, Bool.not_false, List.cons_getElem_zero, parity_def'])
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
    helpGrayIt true [init] (by simp) (by simp [this])

#eval Subset.grayIt 3
#eval List.map (Subset.grayVal) (Subset.grayIt 3)
#eval List.map (Subset.grayVal) (Subset.grayIt 3)
