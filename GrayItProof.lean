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
              _ = true := by simp only [parity_def, List.getElem_cons_zero]
          have : (grayVal (cons a₀ as)).snd = false :=
            calc (grayVal (cons a₀ as)).snd
              _ = !!(grayVal (cons a₀ as :: xs)[0]).snd := by simp only [List.getElem_cons_zero, Bool.not_not]
              _ = !true := by rw [parity_def]
          have : (grayVal (cons (!a₀) as)).fst+1 = (grayVal (cons a₀ as)).fst := dec_case_1 a₀ as this
          have : (grayVal (cons (!a₀) as)).fst+1 ≤ (grayVal (cons a₀ as)).fst := by simp only [this, Nat.le_refl]
          helpGrayIt (!parity) (a' :: soFar) (by simp only [List.length_cons, gt_iff_lt, Nat.zero_lt_succ]) (by simp only [h, Bool.not_true, List.getElem_cons_zero, parity_def'])
        | false =>
          match h2 : minLeft1? (cons a₀ as) with
          | none => soFar
          | some next =>
            have parity_def' : (grayVal next).snd = false :=
              have : (cons a₀ as).ml1?XorGv := ml1?_gV_ne_gV (cons a₀ as)
              have : (cons a₀ as).ml1?XorGv = xor (grayVal next).snd (grayVal (cons a₀ as)).snd := by simp [ml1?XorGv, h2]
              by simp_all only [List.getElem_cons_zero, Bool.false_eq, Bool.not_eq_false', Nat.le_refl, Bool.bne_true, Bool.not_eq_true', Bool.not_false]
            have : (grayVal next).fst+1 = (grayVal (cons a₀ as)).fst := sorry
            have : (grayVal next).fst+1 ≤ (grayVal (cons a₀ as)).fst := by simp only [this, Nat.le_refl]
            helpGrayIt (!parity) (next :: soFar) (by simp only [List.length_cons, gt_iff_lt, Nat.zero_lt_succ]) (by simp only [h, Bool.not_false, List.getElem_cons_zero, parity_def'])
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

#eval! Subset.grayIt 3
#eval! List.map (Subset.grayVal) (Subset.grayIt 3)
#eval! List.map (Subset.grayVal) (Subset.grayIt 3)
