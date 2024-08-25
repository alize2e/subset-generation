import «Subsets».GrayItValProof

def s1 := (Subset.cons true (Subset.cons false (Subset.cons false Subset.nil)))
def s0 := (Subset.cons false (Subset.cons false (Subset.cons false Subset.nil)))
#eval s1.grayVal
#eval s0.grayVal
def s2 := (Subset.cons true (Subset.cons true (Subset.cons false Subset.nil)))
#eval s2.grayVal --yay!

def Subset.helpGrayIt {m : Nat} (parity : Bool) (soFar : List (Subset m.succ))
  (ok : soFar.length>0) : List (Subset m.succ) :=
    match soFar with
    | a :: xs =>
      match parity with
      | true =>
        match a with
        | cons a₀ as =>
          let a' := cons (¬ a₀) as
          have : (grayVal (cons (!a₀) as)).fst < (grayVal (cons a₀ as)).fst := sorry
          helpGrayIt (¬ parity) (a' :: soFar) (by simp [ok])
      | false =>
        let out := minLeft1? a
        match out with
        | none => soFar
        | some next =>
          have : (grayVal next).fst < (grayVal a).fst := sorry
          helpGrayIt (¬ parity) (next :: soFar) (by simp [ok])
      termination_by (soFar[0].grayVal).fst

def Subset.grayIt (n : Nat) : List (Subset n) :=
  match n with
  | 0 => [nil]
  | m+1 =>
    let init := initFalse m.succ
    helpGrayIt true [init] (by simp)

#eval Subset.grayIt 3
#eval List.map (Subset.grayVal) (Subset.grayIt 3)
