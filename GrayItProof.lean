import «Subsets».GrayItValProof

def Subset.helpGrayIt {m : Nat} (parity : Bool) (soFar : List (Subset (m+1)))
  (soFar_len : soFar.length>0) (parity_def : parity = !(soFar[0].grayVal 1).snd) : List (Subset m.succ) :=
    match soFar with
    | a :: xs =>
      match h : parity with
      | true =>
        match a with
        | cons a₀ as =>
          let a' := cons (!a₀) as
          have parity_def' : (grayVal 1 a').snd = true :=
            calc (grayVal 1 a').snd
              _ = (grayVal 1 (cons (!a₀) as)).snd := by rfl
              _ = xor (!a₀) (grayVal 2 as).snd := by rfl
              _ = !(xor a₀ (grayVal 2 as).snd) := by simp [Bool.not_xor]
              _ = !(grayVal 1 (cons a₀ as)).snd := by rfl
              _ = true := by simp [parity_def]
          have : (grayVal 1 (cons a₀ as)).snd = false :=
            calc (grayVal 1 (cons a₀ as)).snd
              _ = !!(grayVal 1 (cons a₀ as :: xs)[0]).snd := by simp
              _ = !true := by rw [parity_def]
          have : (grayVal 1 (cons (!a₀) as)).fst+1 = (grayVal 1 (cons a₀ as)).fst := dec_case_1 a₀ as this
          have : (grayVal 1 (cons (!a₀) as)).fst+1 ≤ (grayVal 1 (cons a₀ as)).fst := by simp [this]
          -- why does it want a and not (cons a₀ as)? how does a even exist?
          have : (grayVal 1 (cons (!a₀) as)).fst+1 = (grayVal 1 a).fst := sorry
          have : (grayVal 1 (cons (!a₀) as)).fst+1 ≤ (grayVal 1 a).fst := by simp [this]
          helpGrayIt (!parity) (a' :: soFar) (by simp [soFar_len]) (by simp [parity_def', h])
      | false =>
        let out := minLeft1? a
        match h2 : out with
        | none => soFar
        | some next =>
          have : (grayVal 1 next).fst+1 = (grayVal 1 a).fst := sorry
          have : (grayVal 1 next).fst+1 ≤ (grayVal 1 a).fst := by simp [this]
          have parity_def' : (grayVal 1 next).snd = false := sorry
          helpGrayIt (!parity) (next :: soFar) (by simp [soFar_len]) (by simp [parity_def', h])
      termination_by (soFar[0].grayVal 1).fst

def Subset.grayIt (n : Nat) : List (Subset n) :=
  match n with
  | 0 => [nil]
  | m+1 =>
    let init := initFalse m.succ
    have : !(grayVal 1 init).snd :=
      calc !(grayVal 1 init).snd
        _ = !(grayVal 1 (initFalse m.succ)).snd := by rfl
        _ = !(false) := by simp [false_grayVal_false]
        _ = true := by simp
    helpGrayIt true [init] (by simp) (by simp [this])

#eval Subset.grayIt 3
#eval List.map (Subset.grayVal 1) (Subset.grayIt 3)
