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

theorem Subset.fML1?_isSome_gV_pos {n : Nat} {s : Subset n} : s.findMinLeft1?.isSome → 1 ≤ s.grayVal.fst := by
  induction n with
  | zero =>
    match s with
    | nil => nofun
  | succ n' ih =>
    match n' with
    | .zero =>
      match s with
      | cons false nil => nofun
      | cons true nil => nofun
    | .succ n'' =>
      match s with
      | cons true (cons b bs) =>
        intro _
        match h1 : (cons b bs).grayVal.snd with
        | true =>
          calc (cons true (cons b bs)).grayVal.fst
            _ = 2*(cons b bs).grayVal.fst + (if (xor true (cons b bs).grayVal.snd) then 0 else 1) := by rfl
            _ = 2*(cons b bs).grayVal.fst + (if !(cons b bs).grayVal.snd then 0 else 1) := by rw [Bool.true_xor (cons b bs).grayVal.snd]
            _ = 2*(cons b bs).grayVal.fst + (if !true then 0 else 1) := by rw [h1]
            _ = 2*(cons b bs).grayVal.fst + 1 := by rfl
            _ ≥ 1 := by simp only [ge_iff_le, Nat.le_add_left]
        | false =>
          calc 1
            _ ≤ 2 := by simp
            _ ≤ 4*bs.grayVal.fst + 2 := by simp_arith
            _ = 2*(2*bs.grayVal.fst + 1) := by simp_arith
            _ = 2*(2*bs.grayVal.fst + (if false then 0 else 1)) := by simp only [Bool.false_eq_true, ↓reduceIte]
            _ = 2*(2*bs.grayVal.fst + (if (cons b bs).grayVal.snd then 0 else 1)) := by rw [h1]
            _ = 2*(2*bs.grayVal.fst + (if b.xor bs.grayVal.snd then 0 else 1)) := by rfl
            _ = 2*(cons b bs).grayVal.fst := by rfl
            _ ≤ 2*(cons b bs).grayVal.fst + (if (xor true (cons b bs).grayVal.snd) then 0 else 1) := by simp only [Bool.true_bne, Bool.not_eq_true', ge_iff_le, Nat.le_add_right]
            _ = (cons true (cons b bs)).grayVal.fst := by rfl
      | cons false (cons b bs) =>
        simp only [findMinLeft1?]
        match h2 : (cons b bs).findMinLeft1? with
        | none => nofun
        | some out =>
          intro _
          calc 1
            _ ≤ (cons b bs).grayVal.fst := ih (by simp only [Nat.succ_eq_add_one, h2, Option.isSome_some])
            _ = 1*(cons b bs).grayVal.fst := by simp_arith
            _ ≤ 2*(cons b bs).grayVal.fst := Nat.mul_le_mul_right (cons b bs).grayVal.fst (by simp only [Nat.reduceLeDiff])
            _ ≤ 2*(cons b bs).grayVal.fst + (if false.xor (cons b bs).grayVal.snd then 0 else 1) := by simp only [Bool.false_bne, Nat.le_add_right]
            _ = (cons false (cons b bs)).grayVal.fst := by rfl

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

theorem Subset.cons_true_ml1?ish_gV_IS {n : Nat} {b : Bool} {bs : Subset n} (h : (cons true (cons b bs)).grayVal.snd) :
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

theorem Subset.change1_cons_false_IS {n : Nat} {b : Bool} {bs : Subset n}
  (h2 : (cons false (cons b bs)).findMinLeft1?.isSome) (h2' : (cons b bs).findMinLeft1?.isSome) :
  (cons false (cons b bs)).change1 ((cons false (cons b bs)).findMinLeft1?.get h2) (by simp) = cons false ((cons b bs).change1 ((cons b bs).findMinLeft1?.get h2') (by simp)) := by
    have : ∃ out, (cons b bs).findMinLeft1? = some out := by
      match h3 : (cons b bs).findMinLeft1? with
      | none =>
        have : (cons b bs).findMinLeft1?.isSome = false := by simp [h3]
        have : true = false :=
          calc true
            _ = (cons b bs).findMinLeft1?.isSome := by rw [h2']
            _ = false := this
        contradiction
      | some out => simp [h3]
    apply Exists.elim this
    intro out
    intro h4
    have : (cons false (cons b bs)).findMinLeft1? = some out.succ := by simp only [findMinLeft1?, Nat.succ_eq_add_one, h4]
    simp only [this, Option.get_some, change1, h4]

theorem Subset.gV2_false_ne_nil_gV_pos {n : Nat} {s : Subset n} {h : s.grayVal.snd = false} : n ≠ 0 → s.grayVal.fst ≥ 1 :=
  match n with
  | .zero => nofun
  | .succ n' => by
    match s with
    | cons b bs =>
      simp [grayVal]
      have : b = bs.grayVal.snd :=
        calc b
          _ = xor b false := by rw [Bool.xor_false b]
          _ = xor b (xor bs.grayVal.snd bs.grayVal.snd) := by rw [Bool.xor_self bs.grayVal.snd]
          _ = xor (xor b bs.grayVal.snd) bs.grayVal.snd := by rw [Bool.xor_assoc]
          _ = xor ((cons b bs).grayVal.snd) bs.grayVal.snd := by rfl
          _ = xor false bs.grayVal.snd := by rw [h]
          _ = bs.grayVal.snd := Bool.false_xor bs.grayVal.snd
      simp [this]

theorem Subset.bs_gV_pos_help {n''' : Nat} {b : Bool} {bs : Subset n'''} (h2' : (cons b bs).findMinLeft1?.isSome = true)
  (h5 : bs.grayVal.snd = !b) : bs.grayVal.fst ≥ 1 :=
    match n''' with
    | .zero => by
      match bs with
      | nil =>
        have : nil.grayVal.fst = 0 := by rfl
        simp only [this, ge_iff_le, Nat.le_zero_eq, Nat.add_one_ne_zero]
        match b with
        | true =>
          have : (cons true nil).findMinLeft1?.isSome = false := by rfl
          contradiction
        | false =>
          have : (cons false nil).grayVal.snd = false := by rfl
          contradiction
    | .succ niv => by
      match b with
      | false =>
        match h2'' : bs.findMinLeft1?.isSome with
        | true => simp only [ge_iff_le, h2'', fML1?_isSome_gV_pos]
        | false =>
          match h3 : bs.findMinLeft1? with
          | none =>
            have : (cons false bs).findMinLeft1?.isSome = false := by simp only [findMinLeft1?, Option.isSome, h3]
            have : true = false :=
              calc true
                _ = (cons false bs).findMinLeft1?.isSome := by rw [h2']
                _ = false := this
            contradiction
          | some out =>
            have : bs.findMinLeft1?.isSome := by simp only [h3, Option.isSome]
            have : true = false :=
              calc true
                _ = bs.findMinLeft1?.isSome := by rw [this]
                _ = false := h2''
            contradiction
      | true =>
        match bs with
        | cons b' bs' => simp only [ge_iff_le, h5, Bool.not_true, ne_eq, Nat.add_one_ne_zero, not_false_eq_true, gV2_false_ne_nil_gV_pos]

theorem Subset.dec_case_2 {n : Nat} {s : Subset n} (h : s.grayVal.snd) (h2 : s.findMinLeft1?.isSome) : (s.change1 (s.findMinLeft1?.get h2) (by simp)).grayVal.fst+1 = s.grayVal.fst := by
  induction n with
  | zero =>
    match s with
    | nil => nofun
  | succ n' ih =>
    match n' with
    | Nat.zero =>
      match s with
      | cons true nil => nofun
      | cons false nil => nofun
    | Nat.succ n'' =>
      match s with
      | cons true (cons _ _) => apply cons_true_ml1?ish_gV_IS h
      | cons false (cons b bs) =>
        have h' : (cons b bs).grayVal.snd :=
          calc (cons b bs).grayVal.snd
            _ = xor false (cons b bs).grayVal.snd := by rw [Bool.false_xor (cons b bs).grayVal.snd]
            _ = (cons false (cons b bs)).grayVal.snd := by rfl
            _ = true := h
        match h2' : (cons b bs).findMinLeft1?.isSome with
        | true =>
          rw [change1_cons_false_IS h2 h2']
          simp only [grayVal]
          simp only [Bool.false_xor]
          have h3 : ((cons b bs).change1 ((cons b bs).findMinLeft1?.get h2') (by simp)).grayVal.fst = (cons b bs).grayVal.fst - 1 :=
            calc ((cons b bs).change1 ((cons b bs).findMinLeft1?.get h2') (by simp)).grayVal.fst
              _ = ((cons b bs).change1 ((cons b bs).findMinLeft1?.get h2') (by simp)).grayVal.fst + 1 - 1 := by simp_arith
              _ = (cons b bs).grayVal.fst - 1 := by rw [ih h' h2']
          simp only [h3]
          have h5 : bs.grayVal.snd = !b :=
            calc bs.grayVal.snd
              _ = xor false bs.grayVal.snd := by rw [Bool.false_xor bs.grayVal.snd]
              _ = xor (xor b b) bs.grayVal.snd := by rw [Bool.xor_self]
              _ = xor b (xor b bs.grayVal.snd) := by rw [Bool.xor_assoc]
              _ = xor b (cons b bs).grayVal.snd := by rfl
              _ = xor b true := by rw [h']
              _ = !b := Bool.xor_true b
          simp only [h5, Bool.eq_not_self, ↓reduceIte, Nat.add_zero]
          simp only [Bool.xor_not b b, bne_self_eq_false, Bool.not_false, ↓reduceIte, Nat.add_zero]
          simp_arith
          simp only [grayVal]
          simp only [h5, Bool.bne_not_self, ↓reduceIte, Nat.add_zero]
          simp only [gV_ne_change1_gV, h', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          simp_arith
          have : 1 ≤ 2*bs.grayVal.fst := by
            match h4 : bs.findMinLeft1? with
            | none =>
              match n'' with
              | .zero =>
                match bs with
                | nil =>
                  have h2'f : (cons b nil).findMinLeft1?.isSome = false := by simp [findMinLeft1?]
                  have : true = false :=
                    calc true
                      _ = (cons b nil).findMinLeft1?.isSome := by rw [h2']
                      _ = false := h2'f
                  contradiction
              | .succ n''' =>
                calc 1
                  _ ≤ bs.grayVal.fst := by simp only [bs_gV_pos_help h2' h5]
                  _ = 1*bs.grayVal.fst := by simp_arith
                  _ ≤ 2*bs.grayVal.fst := Nat.mul_le_mul_right bs.grayVal.fst (by simp only [Nat.reduceLeDiff])
            | some out' =>
              calc 1
              _ ≤ bs.grayVal.fst := fML1?_isSome_gV_pos (by simp [h4])
              _ ≤ 2*bs.grayVal.fst := by simp_arith
          calc 2 * (2 * bs.grayVal.fst - 1) + 2
            _ = 2 * (2 * bs.grayVal.fst - 1 + 1) := Nat.mul_add 2 (2*bs.grayVal.fst-1) 1
            _ = 2 * (2 * bs.grayVal.fst) := by rw [Nat.sub_add_cancel this]
            _ = 4 * bs.grayVal.fst := by simp_arith
        | false =>
          have : (cons false (cons b bs)).findMinLeft1?.isSome = false := by
            simp [findMinLeft1?]
            match h3 : (cons b bs).findMinLeft1? with
            | none => rfl
            | some out =>
              have ht : (cons b bs).findMinLeft1?.isSome = true := by simp [h3]
              have hf : (cons b bs).findMinLeft1?.isSome = false := h2'
              have : true = false :=
                calc true
                  _ = (cons b bs).findMinLeft1?.isSome := by rw [ht]
                  _ = false := hf
              contradiction
          have : true = false :=
            calc true
              _ = (cons false (cons b bs)).findMinLeft1?.isSome := by rw [h2]
              _ = false := by rw [this]
          contradiction



-- def Subset.minLeft1? {n : Nat} (s : Subset n) : Option (Subset n) :=
--   match s.findMinLeft1? with
--   | none => none
--   | some out => s.change1 out (Fin.is_lt out)

-- def Subset.ml1?XorGv {n : Nat} (s : Subset n) : Bool :=
--   match s.minLeft1? with
--   | none => true
--   | some out => xor (grayVal out).snd (grayVal s).snd

-- theorem Subset.ml1?_gV_ne_gV {n : Nat} (s : Subset n) : s.ml1?XorGv := by
--   simp [ml1?XorGv]
--   simp [minLeft1?]
--   match s.findMinLeft1? with
--   | none => rfl
--   | some out => simp only [gV_ne_change1_gV, Bool.not_bne_self]

-- #eval (Subset.genRec 3)
-- #eval (Subset.genRec 3).map Subset.minLeft1?

-- theorem Subset.cons_gV_ge_gV {n : Nat} {b : Bool} {bs : Subset n} : (cons b bs).grayVal.fst ≥ bs.grayVal.fst := by
--   simp [grayVal]
--   simp_arith

-- theorem Subset.cons_true_cons_gV_pos {n : Nat} (b : Bool) (bs : Subset n) : (cons true (cons b bs)).grayVal.fst ≥ 1 := by
--   induction bs generalizing b with
--   | nil =>
--     match b with
--     | true => simp only [grayVal, Nat.mul_zero, Bool.bne_false, ↓reduceIte, Nat.add_zero, bne_self_eq_false, Bool.false_eq_true, Nat.zero_add, ge_iff_le, Nat.le_refl]
--     | false => simp only [grayVal, Nat.mul_zero, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.mul_one, Bool.bne_false, Nat.add_zero, ge_iff_le, Nat.reduceLeDiff]
--   | cons b' bs' ih =>
--     match b' with
--     | true =>
--       simp [grayVal]
--       match bs'.grayVal.snd with
--       | true => simp_arith
--       | false =>
--         match b with
--         | true => simp_arith
--         | false => simp_arith
--     | false =>
--       match b with
--       | true =>
--         calc 1
--           _ ≤ (cons true (cons false bs')).grayVal.fst := ih false
--           _ ≤ (cons true (cons true (cons false bs'))).grayVal.fst := cons_gV_ge_gV
--       | false =>
--         simp [grayVal]
--         match bs'.grayVal.snd with
--         | true => simp_arith
--         | false => simp_arith
