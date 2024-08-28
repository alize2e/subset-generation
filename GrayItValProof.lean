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
  | cons b bs =>
    let out := minLeft1? bs
    match out with
    | none => none
    | some next => some (cons b next)

def Subset.ml1?XorGv {n : Nat} (s : Subset n) : Bool :=
  match s.minLeft1? with
  | none => true
  | some out => xor (grayVal out).snd (grayVal s).snd

-- theorem Subset.ml1?_gV_ne_gV {n : Nat} {s : Subset n} : s.ml1?XorGv := by
--   simp [ml1?XorGv]
--   match s.minLeft1? with
--   | none => rfl
--   | some out =>
--     calc xor out.grayVal.snd s.grayVal.snd
  -- simp [minLeft1?]
  -- match s.findMinLeft1? with
  -- | none => rfl
  -- | some out => simp only [gV_ne_change1_gV, Bool.not_bne_self]

-- theorem Subset.dec_case_2 {m : Nat} {a₀ : Bool} {as : Subset m} {h : (grayVal 1 (cons a₀ as)).snd = false} :
  -- (grayVal next).fst+1 = (grayVal (cons a₀ as)).fst\

-- def Subset.split {n : Nat} (s : Subset n) (m : Fin n) : Prod Bool (Prod (Subset (m-1)) (Subset (n-m))) :=

def Subset.change1 {n : Nat} (s : Subset n) (m : Nat) (h : m<n) : Subset n :=
  match m with
  | Nat.zero =>
    match s with
    | cons b bs => cons (!b) bs
  | Nat.succ m' =>
    match s with
    | cons b bs => cons b (change1 bs m' (Nat.lt_of_succ_lt_succ h))

def Subset.change1'' {n : Nat} (m : Nat) (h : m<n) (s : Subset n) : Subset n :=
  match m with
  | Nat.zero =>
    match s with
    | cons b bs => cons (!b) bs
  | Nat.succ m' =>
    match s with
    | cons b bs => cons b (change1 bs m' (Nat.lt_of_succ_lt_succ h))

def Subset.findMinLeft1? {n : Nat} : Subset n → Option (Fin n)
  | nil => none
  | cons true (cons _ _) => some 1
  | cons _ bs =>
    match findMinLeft1? bs with
    | none => none
    | some out => some out.succ

theorem Subset.gV_ne_change1_gV {n : Nat} {s : Subset n} {m : Nat} {h : m<n} : (s.change1 m h).grayVal.snd = !s.grayVal.snd := by
  induction s generalizing m with
  | nil => nofun
  | cons b bs ih =>
    match m with
    | .zero =>
      calc ((cons b bs).change1 Nat.zero h).grayVal.snd
        _ = (cons (!b) bs).grayVal.snd := by rfl
        _ = (!b).xor bs.grayVal.snd := by rfl
        _ = !((b).xor bs.grayVal.snd) := Bool.not_xor b bs.grayVal.snd
    | .succ m' =>
      calc ((cons b bs).change1 m'.succ h).grayVal.snd
        _ = (cons b (bs.change1 m' (Nat.lt_of_succ_lt_succ h))).grayVal.snd := by rfl
        _ = b.xor (bs.change1 m' (Nat.lt_of_succ_lt_succ h)).grayVal.snd := by rfl
        _ = b.xor !bs.grayVal.snd := by rw [ih]
        _ = !(b.xor bs.grayVal.snd) := Bool.xor_not b bs.grayVal.snd

-- doesn't terminate??? compilation problem with grayitproof
def Subset.minLeft1?' {n : Nat} (s : Subset n) : Option (Subset n) :=
  match s.findMinLeft1? with
  | none => none
  | some out => s.change1 out (Fin.is_lt out)

#eval (Subset.genRec 3)
#eval (Subset.genRec 3).map (Subset.change1'' 2 (by simp))
#eval (Subset.genRec 3).map Subset.minLeft1?' == (Subset.genRec 3).map Subset.minLeft1?

def Subset.ml1?XorGv' {n : Nat} (s : Subset n) : Bool :=
  match s.minLeft1?' with
  | none => true
  | some out => xor (grayVal out).snd (grayVal s).snd

theorem Subset.ml1?_gV_ne_gV' {n : Nat} {s : Subset n} : s.ml1?XorGv' := by
  simp [ml1?XorGv']
  simp [minLeft1?']
  match s.findMinLeft1? with
  | none => rfl
  | some out => simp only [gV_ne_change1_gV, Bool.not_bne_self]

#eval (Subset.genRec 3)
#eval (Subset.genRec 3).map Subset.minLeft1?

def s := Subset.cons false (Subset.cons true (Subset.cons true Subset.nil))
#eval s
#eval Subset.minLeft1? s
