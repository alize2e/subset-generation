import «Subsets».SubsetDef

def Subset.grayVal {m : Nat} (times : Nat) : Subset m → Nat × Bool
  | nil => (0, false)
  | cons b bs =>
    match grayVal (2*times) bs with
    | (val, parity) => (val + times*(if b.xor parity then 0 else 1), b.xor parity)

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

theorem Subset.dec_case_1 {m : Nat} (a₀ : Bool) (as : Subset m) (h : (grayVal 1 (cons a₀ as)).snd = false) :
  (grayVal 1 (cons (!a₀) as)).fst+1 = (grayVal 1 (cons a₀ as)).fst :=
    match a₀ with
    | true =>
      if h' : (grayVal 2 as).snd then
        by simp [grayVal, h', Bool.xor_false]
      else
        have : (grayVal 1 (cons true as)).snd = true := by simp [grayVal, h']
        absurd this (by simp [h])
    | false =>
      if h' : (grayVal 2 as).snd then
        have : (grayVal 1 (cons false as)).snd = true := by simp [grayVal, h', Bool.xor_false]
        absurd this (by simp [h])
      else
        by simp [grayVal, h', Bool.xor_false]

def Subset.minLeft1? {n : Nat} : Subset n → Option (Subset n)
  | nil => none
  | cons true (cons b bs) => some (cons true (cons (!b) bs))
  | cons b bs =>
    let out := minLeft1? bs
    match out with
    | none => none
    | some next => some (cons b next)

-- theorem Subset.dec_case_2 {m : Nat} {a₀ : Bool} {as : Subset m} {h : (grayVal 1 (cons a₀ as)).snd = false} :
