import «Subsets».SubsetIsoFun

def Subset.grayVal {m : Nat} (times : Nat) : Subset m → Nat × Bool
  | nil => (0, false)
  | cons b bs =>
    match grayVal (2*times) bs with
    | (val, parity) =>
      let delta := if b.xor parity then 0 else 1
      (val + times*delta, b.xor parity)

#eval s
#eval (s.append s).grayVal 1
def s1 := (Subset.cons true (Subset.cons false (Subset.cons false Subset.nil)))
def s0 := (Subset.cons false (Subset.cons false (Subset.cons false Subset.nil)))
#eval s1.grayVal 1
#eval s0.grayVal 1
def s2 := (Subset.cons true (Subset.cons true (Subset.cons false Subset.nil)))
#eval s2.grayVal 1 --yay!

def Subset.minLeft1? {n : Nat} : Subset n → Option (Subset n)
  | nil => none
  | cons true (cons b bs) => some (cons true (cons (¬b) bs))
  | cons b bs =>
    let out := minLeft1? bs
    match out with
    | none => none
    | some next => some (cons b next)

def Subset.helpGrayIt {m : Nat} (parity : Bool) (soFar : List (Subset m.succ))
  (ok : soFar.length>0) : List (Subset m.succ) :=
    match soFar with
    | a :: xs =>
      match parity with
      | true =>
        match a with
        | cons a₀ as =>
          let a' := cons (¬ a₀) as
          have : (grayVal 1 (cons (!a₀) as)).fst < (grayVal 1 (cons a₀ as)).fst := sorry
          helpGrayIt (¬ parity) (a' :: soFar) (by simp [ok])
      | false =>
        let out := minLeft1? a
        match out with
        | none => soFar
        | some next =>
          have : (grayVal 1 next).fst < (grayVal 1 a).fst := sorry
          helpGrayIt (¬ parity) (next :: soFar) (by simp [ok])
      termination_by (soFar[0].grayVal 1).fst

def Subset.grayIt (n : Nat) : List (Subset n) :=
  match n with
  | 0 => [nil]
  | m+1 =>
    let init := initFalse m.succ
    helpGrayIt true [init] (by simp)

#eval Subset.grayIt 3
#eval List.map (Subset.grayVal 1) (Subset.grayIt 3)
