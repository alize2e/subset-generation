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

def Subset.minLeft1?_pair {n : Nat} : Subset n → Option (Prod (Subset n) (Fin n))
  | nil => none
  | cons true (cons b bs) => some ((cons true (cons (!b) bs)), 0)
  | cons b bs =>
    let out := minLeft1?_pair bs
    match out with
    | none => none
    | some (next, num) => some (cons b next, num.succ)

def Subset.minLeft1?_monadic {n : Nat} : Subset n → Option (Subset n)
  | nil => none
  | cons true (cons b bs) => pure (cons true (cons (!b) bs))
  | cons b bs => minLeft1? bs >>= fun out => pure (cons b out)

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

-- def Subset.change1_or_eq {n : Nat} (s : Subset n) (m : Nat) : Subset n :=
--   match m with
--   | Nat.zero =>
--     match s with
--     | nil => nil
--     | cons b bs => cons (!b) bs
--   | Nat.succ m' =>
--     match s with
--     | nil => nil
--     | cons b bs => cons b (change1_or_eq bs m')

def Subset.findMinLeft1? {n : Nat} : Subset n → Option (Fin n)
  | nil => none
  | cons true (cons _ _) => pure 0
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

def Subset.minLeft1?' {n : Nat} (s : Subset n) : Option (Subset n) :=
  match s.findMinLeft1? with
  | none => none
  | some out => s.change1 out (by simp only [Fin.is_lt])

def Subset.ml1?XorGv {n : Nat} (s : Subset n) : Bool :=
  match s.minLeft1?' with
  | none => true
  | some out => xor (grayVal out).snd (grayVal s).snd

theorem Subset.ml1?_gV_ne_gV {n : Nat} {s : Subset n} : s.ml1?XorGv := by
  simp [ml1?XorGv]
  simp [minLeft1?']
  -- by_cases s.minLeft1?' = none
  -- . simp [ml1?XorGv, *]
  -- . match s.findMinLeft1? with
  --   | none => skip
  --   | some out =>
  --     calc s.ml1?XorGv
  --       _ = xor (s.change1 out (by simp only [Fin.is_lt])).grayVal.snd (grayVal s).snd := by simp [ml1?XorGv, minLeft1?', *]


  -- match s.minLeft1?' with
  -- | none =>
  --   have : s.minLeft1? = none := by assumption
  --   calc s.ml1?XorGv
  --     _ = true := by rfl --simp_all? [minLeft1?', *]
  -- | some out =>
  --   skip

-- theorem Subset.change1_square_id {n : Nat} {s : Subset n} {m : Nat} {h : m<n} : change1 (change1 s m h) m h = s := by
--   let d := n-m
--   induction d generalizing n m s with
--   | zero => skip
--     -- have : d = 0 := by assumption
--     -- have : n-m = 0 := by assumption
--   | succ diff => skip


theorem Subset.ml1?_gV_neq_gV' {n : Nat} {s : Subset n} : ml1?_gV_beq?_gV s := by
  induction s with
  | nil => rfl
  | cons b bs ih =>
    match b with
    | true =>
      match bs with
      | nil => rfl
      | cons b' bs' =>
        match minLeft1? (cons true (cons b bs)) with
        | none => skip
        | some out =>
          calc (cons true (cons b' bs')).ml1?_gV_beq?_gV
            _ = xor (grayVal out)

#eval (Subset.genRec 3)
#eval (Subset.genRec 3).map Subset.minLeft1?

def s := Subset.cons false (Subset.cons true (Subset.cons true Subset.nil))
#eval s
#eval Subset.minLeft1? s
