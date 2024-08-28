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

def Subset.change1 {n : Nat} (s : Subset n) (m : Nat) (h : m<n) : Subset n :=
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

def Subset.minLeft1? {n : Nat} (s : Subset n) : Option (Subset n) :=
  match s.findMinLeft1? with
  | none => none
  | some out => s.change1 out (Fin.is_lt out)

def Subset.ml1?XorGv {n : Nat} (s : Subset n) : Bool :=
  match s.minLeft1? with
  | none => true
  | some out => xor (grayVal out).snd (grayVal s).snd

theorem Subset.ml1?_gV_ne_gV {n : Nat} (s : Subset n) : s.ml1?XorGv := by
  simp [ml1?XorGv]
  simp [minLeft1?]
  match s.findMinLeft1? with
  | none => rfl
  | some out => simp only [gV_ne_change1_gV, Bool.not_bne_self]

#eval (Subset.genRec 3)
#eval (Subset.genRec 3).map Subset.minLeft1?

theorem Subset.ml1?_cons_idk {n : Nat} {b : Bool} {bs : Subset n} {h : (cons true (cons b bs)).grayVal.snd} :
  ((cons true (cons b bs)).change1 1 (by simp only [Nat.lt_add_left_iff_pos, Nat.zero_lt_succ])).grayVal.fst+1 = (cons true (cons b bs)).grayVal.fst := by
    have h1 : bs.grayVal.snd = b :=
      calc bs.grayVal.snd
        _ = xor false bs.grayVal.snd := by rw [Bool.false_xor bs.grayVal.snd]
        _ = xor (xor b b) bs.grayVal.snd := by rw [Bool.xor_self]
        _ = xor b (xor b bs.grayVal.snd) := by rw [Bool.xor_assoc]
        _ = xor (xor b bs.grayVal.snd) b := by rw [Bool.xor_comm]
        _ = xor (cons b bs).grayVal.snd b := by rfl
        _ = xor false (xor (cons b bs).grayVal.snd b) := by rw [Bool.false_xor (xor (cons b bs).grayVal.snd b)]
        _ = xor (xor true true) (xor (cons b bs).grayVal.snd b) := by rw [Bool.xor_self]
        _ = xor true (xor true (xor (cons b bs).grayVal.snd b)) := by rw [Bool.xor_assoc]
        _ = xor true (xor (xor true (cons b bs).grayVal.snd) b) := by rw [Bool.xor_assoc]
        _ = xor true (xor ((cons true (cons b bs)).grayVal.snd) b) := by rfl
        _ = xor true (xor true b) := by rw [h]
        _ = xor (xor true true) b := by rw [Bool.xor_assoc]
        _ = xor false b := by rw [Bool.xor_self]
        _ = b := Bool.false_xor b
    have : (cons true (cons b bs)).change1 1 (by simp only [Nat.lt_add_left_iff_pos, Nat.zero_lt_succ]) = cons true (cons (!b) bs) := by rfl
    rw [this]
    simp [grayVal]
    calc (2 * (2 * bs.grayVal.fst + if b = bs.grayVal.snd then 0 else 1) + if (!b) = bs.grayVal.snd then 0 else 1) + 1
      _ = (2 * (2 * bs.grayVal.fst + if true then 0 else 1) + if false then 0 else 1) + 1 := by simp only [h1, ↓reduceIte, Nat.add_zero, Bool.not_eq_self, Bool.false_eq_true]
      _ = (2 * (2 * bs.grayVal.fst) + 1) + 1 := by simp only [↓reduceIte, Nat.add_zero, Bool.false_eq_true]
      _ = 2 * (2 * bs.grayVal.fst) + 2 := by simp_arith
      _ = 2 * (2 * bs.grayVal.fst + 1) := by simp_arith
      _ = 2 * (2 * bs.grayVal.fst + if true then 1 else 0) + if true then 0 else 1 := by simp
      _ = 2 * (2 * bs.grayVal.fst + if b = bs.grayVal.snd then 1 else 0) + if b = bs.grayVal.snd then 0 else 1 := by simp only [↓reduceIte, Nat.add_zero, h1]
