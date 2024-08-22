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

example {a b c : Nat} (h : c≤b) : a+b-c = a+(b-c) := Nat.add_sub_assoc h a

-- theorem t19 {l i : Nat} {h1 : i<2*l} {h2 : l≤i} {h3 : l≥1} : (l-1-(i.succ-l)).succ = l-1-(i-l) :=
--   have h4 : i≥l := by assumption
--   have h5 : i-l < l-1 := by skip -- currently false because could have i = 2l-1
--   calc (l-1-(i.succ-l)).succ
--     _ = (l-1-(i+1-l))+1 := by simp_arith
--     _ = l-1-(i+1-l)+1 := by simp_arith
--     _ = l-1-(1+i-l)+1 := by simp_arith [Nat.add_comm]
--     _ = l-1-(1+(i-l))+1 := by rw [Nat.add_sub_assoc h2 1]
--     _ = l-1-(i-l) := t17 (l-1) (i-l) h5

theorem t19' {l i : Nat} {h1 : i<2*l-1} {h2 : l≤i} {h3 : l≥1} : (l-1-(i.succ-l)).succ = l-1-(i-l) :=
  have h4 : i≥l := by assumption
  have h5 : i-l < l-1 := by skip -- now cannot have i = 2l-1
  calc (l-1-(i.succ-l)).succ
    _ = l-1-(1+i-l)+1 := by simp_arith [Nat.add_comm]
    _ = l-1-(1+(i-l))+1 := by rw [Nat.add_sub_assoc h2 1]
    _ = l-1-(i-l) := t17 (l-1) (i-l) h5

-- theorem FALSE_t19'' {l i : Nat} {h1 : i=2*l-1} {h2 : l≥1} : (l-1-(i.succ-l)).succ = l-1-(i-l) := -- !!!!!FALSE!!!!!!
--   calc (l-1-(i.succ-l)).succ
--     _ = l-1-(2*l-1+1-l)+1 := by rw [h1]
--     _ = l-1-(2*l-l)+1 := by simp [t17 (2*l) 0 (by simp_arith [h2])]
--     _ = l-1-(l+l-l)+1 := by rw [Nat.two_mul]
--     _ = l-1-l+1 := by simp_arith
--     _ = 1 := sorry

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
