import Subsets.working.GrayCodeProofLemmas

-- theorem sub_of_sub {a b : Nat} {h1 : b<2*a} {h2 : a≤b} {h3 : a≥1} : a-(b-a) = a-b+a := by
--   induction a generalizing b with
--   | zero => contradiction
--   | succ a' ih =>
--     calc a'.succ-(b-a'.succ)
--       _ = a'+1-(b-(a'+1)) := by simp_arith
--       _ = 1+a'-((b-a')-1) := by simp_arith [Nat.sub_add_eq]

theorem t16 (a : Nat) (_ : 0 < a) : a-1+1=a := by
  match a with
  | a'+1 => simp_arith

theorem t17 (a b : Nat) (h1 : b<a) : a-(1+b)+1 = a-b := by
  induction b generalizing a with
  | zero => simp [t16 a (by simp [h1])]
  | succ b' ih =>
    have : b'.succ ≠ 0 := by simp_arith
    have h1' : b' < a-1 :=
      calc b'
        _ = b'.succ-1 := by simp_arith
        _ < a-1 := Nat.pred_lt_pred this h1
    calc a-(1+b'.succ)+1
      _ = a-(1+b'+1)+1 := by simp_arith
      _ = a-(1+b')-1+1 := by simp_arith [Nat.sub_add_eq]
      _ = a-1-(1+b')+1 := by simp_arith [Nat.sub_right_comm]
      _ = a-1-b' := by simp [ih, h1']
      _ = a-(1+b') := by simp_arith [Nat.sub_add_eq]
      _ = a-b'.succ := by simp_arith [Nat.add_comm]

-- theorem t18 (a b : Nat) (h : b<a) : 1+a-b=1+(a-b) := by
--   induction b generalizing a with
--   | zero => rfl
--   | succ b' ih =>
--     calc 1+a-b'.succ
--       _ = 1+a-(b'+1) := by simp_arith
--       _ = 1+a-b'-1 := by simp_arith [Nat.sub_add_eq]
--       _ = 1+(a-b')-1 := by simp_arith [ih a (Nat.lt_of_succ_lt h)]
--       _ = (a-b')+1-1 := by simp_arith [Nat.add_comm]
--       _ = (a-b') := by simp_arith
--       _ = 1-1+(a-b') := by simp_arith

theorem t18 (a b c : Nat) (h : c<b) : ∀ al : Nat, al ≤ a → al+b-c=al+(b-c) := by
  induction a generalizing b c with
  | zero => simp_arith
  | succ a' ih =>
    intro al
    intro h2
    induction al with
    | zero => simp_arith
    | succ al' ih2 =>
      have : al'.succ<a'.succ ∨ al'.succ=a'.succ := Nat.lt_or_eq_of_le h2
      cases this
      . have : al'.succ<a'.succ := by assumption
        have : al'.succ≤a' := Nat.le_of_lt_succ this
        apply ih b c h al'.succ this
      . have : c < a'+b :=
          calc c
            _ < b := h
            _ ≤ b+a' := by simp_arith
            _ = a'+b := by simp [Nat.add_comm]
        calc al'.succ+b-c
          _ = al'+1+b-c := by simp_arith
          _ = 1+al'+b-c := by simp_arith [Nat.add_comm]
          _ = 1+(al'+b)-c := by simp_arith [Nat.add_assoc]
          _ = 1+(al'+b-c) := ih (a'+b) c this 1 -- have : 1 ≤ a'
          -- -- _ = a'.succ+b-c := by simp only [*]
          -- -- _ = a'+1+b-c := by simp_arith
          -- -- _ = 1+a'+b-c := by simp_arith [Nat.add_comm]
          -- -- _ = 1+(a'+b-c) := ih 1 (a'+b) c (by simp [h]) le_or_eq_of_le_succ

example {l i : Nat} {h1 : i<2*l} {h2 : l≤i} {h3 : l≥1} : (l-1-(i.succ-l)).succ = l-1-(i-l) :=
  have h4 : i≥l := by assumption
  calc (l-1-(i.succ-l)).succ
    _ = (l-1-(i+1-l))+1 := by simp_arith
    _ = l-1-(i+1-l)+1 := by simp_arith
    _ = l-1-(1+i-l)+1 := by simp_arith [Nat.add_comm]
    _ = l-1-(i-l) := t17 (l-1) (i-l) sorry
    -- _ = l-1-(i-(l-1))+1 := by simp_arith [*]
    -- _ = l-1-(1+(i-l))+1 := by simp_arith [this]

-- ((grayRecSlides n').length-1-(i.succ-(grayRecSlides n').length)).succ
-- example {l i : Nat} : i<2*l → l≤i → l-(i-l) = 2*l - i := by
--   induction l with
--   | zero => nofun
--   | succ l' ih =>
--     intro h1 h2
--     calc Nat.succ l' - (i - Nat.succ l')
--       _ =

-- example {l i : Nat} {_ : i<2*l} {_ : l≤i} : l-1-(i-l) = 2*l-i-1 := by
--   simp [Nat.sub, Nat.add, Nat.sub_add_eq, Nat.sub_right_comm, *]
--   calc l-1-(i-l)
--     _ = (0+l)-1-(i-l) := by simp_arith
--     _ = (0+l)-1-(i+l-l-l) := by simp_arith
--     _ = (0+l)-1-(i+l-(l+l)) := by simp_arith [Nat.sub_add_eq]
--     _ = (0+l)-1-(i+l-2*l) := by simp_arith [Nat.two_mul]
--     _ = (0+l)-1-(i+l-2*l) := by simp_arith [Nat.sub_add_eq]
--     _ = (0+l)-(i+l-2*l)-1 := by simp_arith [Nat.sub_right_comm]
--     -- _ = (0+l)-1-(i-2*l+l) := by simp_arith [Nat.add_sub_comm]
--     -- _ = l-(i-l)-1 := Nat.sub_right_comm l 1 (i-l)
--     -- _ = l-(i-2*l+l)-1 := by simp_arith

-- theorem Subset.GRS_1_change_next_right {n' : Nat} {i : Nat} {h : i.succ<(grayRecSlides n'.succ).length}
--   {_ : ¬ i.succ<((grayRecSlides n').map (cons false)).length} {_ : ¬ i.succ = ((grayRecSlides n').map (cons false)).length}
--   {ih : ∀ {i' : Nat} {h' : Nat.succ i' < List.length (grayRecSlides n')}, num_changes (grayRecSlides n')[i'] (grayRecSlides n')[i' + 1] = 1} :
--   num_changes (grayRecSlides n'.succ)[i] (grayRecSlides n'.succ)[i+1] = 1 := by
--     simp [grayRecSlides, helpGRS, ←helpGRS_parity_reverse]
--     have : helpGRS n' false = grayRecSlides n' := by simp [grayRecSlides]
--     simp [this]
--     have : i + 1 < List.length (List.map (cons false) (grayRecSlides n') ++ List.map (cons true) (List.reverse (grayRecSlides n'))) := by simp [←grayRecSlides_IS, ]
--     have succ_i_in_right : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i+1] = ((grayRecSlides n').reverse.map (cons true))[i.succ-((grayRecSlides n').map (cons false)).length] := List.get_append_right ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) (by assumption)
--     -- rw [List.get_append_right (List.map (cons false) (grayRecSlides n')) (List.map (cons true) (List.reverse (grayRecSlides n'))) (by assumption : ¬ (i + 1)<((grayRecSlides n').map (cons false)).length)]
