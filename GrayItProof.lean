import «Subsets».SubsetIsoFun

def Subset.grayVal {m : Nat} (times : Nat) : Subset m → Nat × Bool
  | nil => (0, false)
  | cons b bs =>
    match grayVal (2*times) bs with
    | (val, parity) => (val + times*(if b.xor parity then 0 else 1), b.xor parity)

def Subset.minLeft1? {n : Nat} : Subset n → Option (Subset n)
  | nil => none
  | cons true (cons b bs) => some (cons true (cons (!b) bs))
  | cons b bs =>
    let out := minLeft1? bs
    match out with
    | none => none
    | some next => some (cons b next)

def Subset.helpGrayIt {m : Nat} (parity : Bool) (soFar : List (Subset m.succ))
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
          have : (grayVal 1 (cons (!a₀) as)).fst < (grayVal 1 a).fst := sorry
          helpGrayIt (!parity) (a' :: soFar) (by simp [soFar_len]) (by simp [parity_def', h])
      | false =>
        let out := minLeft1? a
        match h2 : out with
        | none => soFar
        | some next =>
          have : (grayVal 1 next).fst < (grayVal 1 a).fst := sorry
          have parity_def' : (grayVal 1 next).snd = false := sorry
          helpGrayIt (!parity) (next :: soFar) (by simp [soFar_len]) (by simp [parity_def', h])
      termination_by (soFar[0].grayVal 1).fst

theorem Subset.false_grayVal_false {m : Nat} : ∀ times : Nat, ((initFalse m.succ).grayVal times).snd = false := by
  induction m with
  | zero => intro times; rfl
  | succ m' ih =>
    intro times
    calc (grayVal times (initFalse m'.succ.succ)).snd
      _ = (grayVal times (cons (false) (initFalse m'.succ))).snd := by rfl
      _ = xor false (grayVal (2*times) (initFalse m'.succ)).snd := by rfl
      _ = (grayVal (2*times) (initFalse m'.succ)).snd := by simp
      _ = false := by simp [ih]

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
