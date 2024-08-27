-- look at page 14!

import «Subsets».SubsetDef

def Subset.grayVal {m : Nat} : Subset m → Nat × Bool
  | nil => (0, false)
  | cons b bs =>
    match grayVal bs with
    | (val, parity) => (2*val + (if b.xor parity then 0 else 1), b.xor parity)

theorem Subset.false_grayVal_false {m : Nat} : ((initFalse m.succ).grayVal).snd = false := by
  induction m with
  | zero => rfl
  | succ m' ih =>
    calc (grayVal (initFalse m'.succ.succ)).snd
      _ = (grayVal (cons (false) (initFalse m'.succ))).snd := by rfl
      _ = xor false (grayVal (initFalse m'.succ)).snd := by rfl
      _ = (grayVal (initFalse m'.succ)).snd := by simp
      _ = false := by simp [ih]

theorem Subset.dec_case_1 {m : Nat} (a₀ : Bool) (as : Subset m) (h : (grayVal (cons a₀ as)).snd = false) :
  (grayVal (cons (!a₀) as)).fst+1 = (grayVal (cons a₀ as)).fst :=
    match a₀ with
    | true =>
      if h' : (grayVal as).snd then
        by simp [grayVal, h', Bool.xor_false]
      else
        have : (grayVal (cons true as)).snd = true := by simp [grayVal, h']
        absurd this (by simp [h])
    | false =>
      if h' : (grayVal as).snd then
        have : (grayVal (cons false as)).snd = true := by simp [grayVal, h', Bool.xor_false]
        absurd this (by simp [h])
      else
        by simp [grayVal, h', Bool.xor_false]

def Subset.minLeft1? {n : Nat} : Subset n → Option (Subset n)
  | nil => none
  | cons true (cons b bs) => some (cons true (cons (!b) bs))
  | cons b bs => minLeft1? bs >>= fun out => pure (cons b out)

-- theorem Subset.dec_case_2 {m : Nat} {a₀ : Bool} {as : Subset m} {h : (grayVal 1 (cons a₀ as)).snd = false} :
  -- (grayVal next).fst+1 = (grayVal (cons a₀ as)).fst\

def Subset.ml1?_prop {n : Nat} (s : Subset n) : Bool :=
  match minLeft1? s with
  | none => true
  | some out => xor (grayVal out).snd (grayVal s).snd

-- theorem Subset.minLeft1?_change {n : Nat} {s : Subset n} : ml1?_prop s :=
--   match (minLeft1? s) with
--   | none => by skip
--   | some out =>

#eval (Subset.genRec 3)
#eval (Subset.genRec 3).map Subset.minLeft1?

def s := Subset.cons false (Subset.cons true (Subset.cons true Subset.nil))
#eval s
#eval Subset.minLeft1? s
