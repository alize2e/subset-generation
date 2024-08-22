import Subsets.GrayCodeProofLemmas

theorem Subset.c1 (n' i : Nat)
  (ih : ∀ {i : Nat} {h : Nat.succ i < List.length (grayRecSlides n')}, num_changes (grayRecSlides n')[i] (grayRecSlides n')[i + 1] = 1)
  (_ : Nat.succ i < List.length (grayRecSlides (Nat.succ n')))
  (h : Nat.succ i < List.length (List.map (cons false) (grayRecSlides n') ++ List.map (cons true) (List.reverse (grayRecSlides n'))))
  (succ_i_in_bounds : Nat.succ i < List.length (List.map (cons false) (grayRecSlides n'))) :
  num_changes (grayRecSlides n'.succ)[i] (grayRecSlides n'.succ)[i.succ] = 1 :=
    have : ((grayRecSlides n').map (cons false)).length = (grayRecSlides n').length := List.length_map (grayRecSlides n') (cons false)
    have i_in_bounds : i<((grayRecSlides n').map (cons false)).length := Nat.lt_of_succ_lt succ_i_in_bounds
    have i_in_left : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] = ((grayRecSlides n').map (cons false))[i] := List.get_append_left ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) i_in_bounds
    have succ_i_in_left : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] = ((grayRecSlides n').map (cons false))[i.succ] := List.get_append_left ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) succ_i_in_bounds
    calc num_changes (grayRecSlides n'.succ)[i] (grayRecSlides n'.succ)[i.succ]
      _ = num_changes (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by simp only [succ_i_in_bounds, grayRecSlides_IS n']
      _ = num_changes ((grayRecSlides n').map (cons false))[i] ((grayRecSlides n').map (cons false))[i.succ] := by simp only [i_in_left, succ_i_in_left]
      _ = num_changes (cons false (grayRecSlides n')[i]) ((grayRecSlides n').map (cons false))[i.succ] := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons false) (grayRecSlides n') i]
      _ = num_changes (cons false (grayRecSlides n')[i]) (cons false (grayRecSlides n')[i.succ]) := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons false) (grayRecSlides n') i.succ]
      _ = num_changes (grayRecSlides n')[i] (grayRecSlides n')[i.succ] := by rw [cons_same_num_changes]
      _ = 1 := by rw [ih]

theorem Subset.c2 (n' i : Nat)
  (_ : Nat.succ i < List.length (grayRecSlides (Nat.succ n')))
  (h : Nat.succ i < List.length (List.map (cons false) (grayRecSlides n') ++ List.map (cons true) (List.reverse (grayRecSlides n'))))
  (succ_i_eq_map_len : Nat.succ i = List.length (List.map (cons false) (grayRecSlides n'))) :
  num_changes (grayRecSlides n'.succ)[i] (grayRecSlides n'.succ)[i.succ] = 1 := by
    have succ_i_eq_len : i.succ = (grayRecSlides n').length := by simp only [succ_i_eq_map_len, List.length_map]
    have i_in_bounds : i < i.succ := Nat.lt_succ_self i
    rw [succ_i_eq_map_len] at i_in_bounds
    have : ((grayRecSlides n').reverse.map (cons true)).length = ((grayRecSlides n').map (cons false)).length := by simp only [List.length_map, List.length_reverse]
    have : ((grayRecSlides n').reverse).length = ((grayRecSlides n').map (cons false)).length := by simp only [List.length_reverse, List.length_map]
    have i_in_left : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] = ((grayRecSlides n').map (cons false))[i] := List.get_append_left ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) i_in_bounds
    have i_succ_in_right : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[((grayRecSlides n').map (cons false)).length] = ((grayRecSlides n').reverse.map (cons true))[((grayRecSlides n').map (cons false)).length-((grayRecSlides n').map (cons false)).length] := List.get_append_right ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) (by simp only [List.length_map, Nat.lt_irrefl, not_false_eq_true])
    have rev_rev_len_pos : 0 < (grayRecSlides n').reverse.reverse.length := by
      calc 0
        _ < 2^n' := Nat.two_pow_pos n'
        _ = (grayRecSlides n').length := by rw [grayRecSlides_num]
        _ = (grayRecSlides n').reverse.reverse.length := by rw [List.reverse_reverse (grayRecSlides n')]
    have : (grayRecSlides n').reverse.reverse.length - 1 < (grayRecSlides n').reverse.reverse.length :=
      calc (grayRecSlides n').reverse.reverse.length - 1
        _ < (grayRecSlides n').reverse.reverse.length - 1 + 1 := by simp only [List.reverse_reverse, Nat.lt_succ_self]
        _ = (grayRecSlides n').reverse.reverse.length := by rw [Nat.sub_one_add_one_eq_of_pos rev_rev_len_pos]
    calc num_changes (grayRecSlides n'.succ)[i] (grayRecSlides n'.succ)[i.succ]
      _ = num_changes (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by simp only [grayRecSlides_IS n', succ_i_eq_map_len, List.length_map]
      _ = num_changes ((grayRecSlides n').map (cons false))[i] (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by rw [i_in_left]
      _ = num_changes (cons false (grayRecSlides n')[i]) (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons false) (grayRecSlides n') i]
      _ = num_changes (cons false (grayRecSlides n')[i]) (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[((grayRecSlides n').map (cons false)).length] := by simp only [succ_i_eq_len, List.length_map]
      _ = num_changes (cons false (grayRecSlides n')[i]) ((grayRecSlides n').reverse.map (cons true))[((grayRecSlides n').map (cons false)).length-((grayRecSlides n').map (cons false)).length] := by rw [i_succ_in_right]
      _ = num_changes (cons false (grayRecSlides n')[i]) ((grayRecSlides n').reverse.map (cons true))[0] := by simp only [List.length_map, Nat.sub_self]
      _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n').reverse[0]) := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons true) (grayRecSlides n').reverse 0]
      _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n').reverse.reverse[(grayRecSlides n').reverse.reverse.length-1]) := by rw [List.diy_reverse_zero_last]
      _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n')[(grayRecSlides n').length-1]) := by simp only [List.reverse_reverse]
      _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n')[i.succ-1]) := by simp only [succ_i_eq_map_len, List.length_map]
      _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n')[i]) := by simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      _ = 1 + num_changes (grayRecSlides n')[i] (grayRecSlides n')[i] := by rfl
      _ = 1 + 0 := by simp only [eq_num_changes_eq_zero, Nat.add_zero]
      _ = 1 := Nat.add_zero 1

theorem Subset.c3 (n' i : Nat)
  (ih : ∀ {i : Nat} {h : Nat.succ i < List.length (grayRecSlides n')}, num_changes (grayRecSlides n')[i] (grayRecSlides n')[i + 1] = 1)
  (_ : Nat.succ i < List.length (grayRecSlides (Nat.succ n')))
  (h : Nat.succ i < List.length (List.map (cons false) (grayRecSlides n') ++ List.map (cons true) (List.reverse (grayRecSlides n'))))
  (h1 : ¬Nat.succ i < List.length (List.map (cons false) (grayRecSlides n')))
  (h2 : ¬Nat.succ i = List.length (List.map (cons false) (grayRecSlides n'))) :
  num_changes (grayRecSlides n'.succ)[i] (grayRecSlides n'.succ)[i.succ] = 1 := by
    have h1' : ¬ (i.succ<((grayRecSlides n').map (cons false)).length) := h1
    rw [Nat.not_lt_eq i.succ ((grayRecSlides n').map (cons false)).length] at h1
    have h3 : ¬ ((grayRecSlides n').map (cons false)).length = i.succ := Ne.symm h2
    have h4 : ((grayRecSlides n').map (cons false)).length < i.succ := Nat.lt_of_le_of_ne h1 h3
    have : ((grayRecSlides n').map (cons false)).length ≤ i → ¬ (i<((grayRecSlides n').map (cons false)).length) := by simp only [List.length_map, Nat.not_lt, imp_self]
    have h10 : ¬ (i<((grayRecSlides n').map (cons false)).length) := this (Nat.le_of_lt_succ h4 : ((grayRecSlides n').map (cons false)).length ≤ i)
    have h11 : i.succ-((grayRecSlides n').map (cons false)).length < ((grayRecSlides n').reverse.map (cons true)).length :=
      calc i.succ-((grayRecSlides n').map (cons false)).length
        _ < (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true))).length - ((grayRecSlides n').map (cons false)).length := Nat.sub_lt_sub_right h1 h
        _ = ((grayRecSlides n').map (cons false)).length + ((grayRecSlides n').reverse.map (cons true)).length - ((grayRecSlides n').map (cons false)).length := by simp only [List.length_append, List.length_map, List.length_reverse, Nat.add_sub_cancel]
        _ = ((grayRecSlides n').reverse.map (cons true)).length := by simp only [List.length_map, List.length_reverse, Nat.add_sub_cancel]
    have : (grayRecSlides n').reverse.length = ((grayRecSlides n').reverse.map (cons true)).length := by simp only [List.length_reverse, List.length_map]
    have : ((grayRecSlides n').map (cons false)).length = (grayRecSlides n').length := by simp only [List.length_map]
    have : i.succ-((grayRecSlides n').map (cons false)).length < (grayRecSlides n').reverse.length := by
      calc i.succ-((grayRecSlides n').map (cons false)).length
        _ < ((grayRecSlides n').reverse.map (cons true)).length := h11
        _ = (grayRecSlides n').reverse.length := by simp only [List.length_map, List.length_reverse]
    have succ_i_in_right : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] = ((grayRecSlides n').reverse.map (cons true))[i.succ-((grayRecSlides n').map (cons false)).length] := List.get_append_right ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) h1'
    have i_in_right : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] = ((grayRecSlides n').reverse.map (cons true))[i-((grayRecSlides n').map (cons false)).length] := List.get_append_right ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) h10
    have : List.length (grayRecSlides n') - 1 - (i - List.length (grayRecSlides n')) < List.length (grayRecSlides n') := s1 (s0 n')
    have h15 : (grayRecSlides n').length < i.succ :=
      calc (grayRecSlides n').length
        _ = ((grayRecSlides n').map (cons false)).length := by simp only [List.length_map]
        _ < i.succ := h4
    have h16 : i.succ < 2*(grayRecSlides n').length :=
      calc i.succ
        _ < (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true))).length := h
        _ = ((grayRecSlides n').map (cons false)).length + ((grayRecSlides n').reverse.map (cons true)).length := by simp only [List.length_append, List.length_map, List.length_reverse]
        _ = (grayRecSlides n').length + (grayRecSlides n').length := by simp only [List.length_map, List.length_reverse]
        _ = 2*(grayRecSlides n').length := by rw [←Nat.two_mul (grayRecSlides n').length]
    have : Nat.succ (List.length (grayRecSlides n') - 1 - (Nat.succ i - List.length (grayRecSlides n'))) < List.length (grayRecSlides n') :=
      calc Nat.succ (List.length (grayRecSlides n') - 1 - (Nat.succ i - List.length (grayRecSlides n')))
        _ < Nat.succ (List.length (grayRecSlides n') - 1) := Nat.succ_lt_succ (s2 h15 (s2' h16 h15))
        _ = Nat.succ (Nat.pred (List.length (grayRecSlides n'))) := by rfl
        _ = List.length (grayRecSlides n') := Nat.succ_pred_eq_of_ne_zero (Nat.ne_of_lt' (s0 n'))
    calc num_changes (grayRecSlides n'.succ)[i] (grayRecSlides n'.succ)[i.succ]
      _ = num_changes (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by simp only [grayRecSlides_IS n']
      _ = num_changes ((grayRecSlides n').reverse.map (cons true))[i-((grayRecSlides n').map (cons false)).length] ((grayRecSlides n').reverse.map (cons true))[i.succ-((grayRecSlides n').map (cons false)).length] := by simp only [i_in_right, List.length_map, succ_i_in_right]
      _ = num_changes (cons true (grayRecSlides n').reverse[i-((grayRecSlides n').map (cons false)).length]) ((grayRecSlides n').reverse.map (cons true))[i.succ-((grayRecSlides n').map (cons false)).length] := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons true) (grayRecSlides n').reverse (i-((grayRecSlides n').map (cons false)).length)]
      _ = num_changes (cons true (grayRecSlides n').reverse[i-((grayRecSlides n').map (cons false)).length]) (cons true (grayRecSlides n').reverse[i.succ-((grayRecSlides n').map (cons false)).length]) := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons true) (grayRecSlides n').reverse (i.succ-((grayRecSlides n').map (cons false)).length)]
      _ = num_changes (grayRecSlides n').reverse[i-((grayRecSlides n').map (cons false)).length] (grayRecSlides n').reverse[i.succ-((grayRecSlides n').map (cons false)).length] := by rw [cons_same_num_changes]
      _ = num_changes (grayRecSlides n').reverse[i-(grayRecSlides n').length] (grayRecSlides n').reverse[i.succ-(grayRecSlides n').length] := by simp only [List.length_map]
      _ = num_changes (grayRecSlides n')[(grayRecSlides n').length-1-(i-(grayRecSlides n').length)] (grayRecSlides n')[(grayRecSlides n').length-1-(i.succ-(grayRecSlides n').length)] := by simp only [List.sorry_getElem_reverse] -- FIX!!!!!
      _ = num_changes (grayRecSlides n')[((grayRecSlides n').length-1-(i.succ-(grayRecSlides n').length)).succ] (grayRecSlides n')[(grayRecSlides n').length-1-(i.succ-(grayRecSlides n').length)] := by simp only [(s3 h16 h15)]
      _ = num_changes (grayRecSlides n')[(grayRecSlides n').length-1-(i.succ-(grayRecSlides n').length)] (grayRecSlides n')[((grayRecSlides n').length-1-(i.succ-(grayRecSlides n').length)).succ] := by rw [symm_num_changes]
      _ = 1 := by rw [ih]

-- edit so that i show it's also a gray cycle by changing h to ≤ not <, but a pain for indices
theorem Subset.grayRecSlides_one_change_next {n : Nat} {i : Nat} {h : i.succ<(grayRecSlides n).length} :
  num_changes (grayRecSlides n)[i] (grayRecSlides n)[i+1] = 1 := by
    induction n generalizing i with
    | zero => nofun
    | succ n' ih =>
      rw [grayRecSlides_IS n'] at h
      if i.succ<((grayRecSlides n').map (cons false)).length then
        exact (c1 n' i ih (by assumption) h (by assumption))
      else
        if i.succ = ((grayRecSlides n').map (cons false)).length then
          exact (c2 n' i (by assumption) h (by assumption))
        else
          exact (c3 n' i ih (by assumption) h (by assumption) (by assumption))

theorem Subset.genGray_one_change_next {n : Nat} {i : Nat} {h : i.succ<(genGray n).length} :
  num_changes (genGray n)[i] (genGray n)[i+1] = 1 := by
    have : i.succ<(grayRecSlides n).length :=
      calc i.succ
        _ < (genGray n).length := h
        _ = (grayRecSlides n).length := by rw [gray_rec_eq]
    have h1 : (genGray n)[i] = (grayRecSlides n)[i] := by simp only [gray_rec_eq n]
    have h2 : (genGray n)[i+1] = (grayRecSlides n)[i+1] := by simp only [gray_rec_eq n]
    calc num_changes (genGray n)[i] (genGray n)[i+1]
      _ = num_changes (grayRecSlides n)[i] (grayRecSlides n)[i+1] := by simp only [h1,h2]
      _ = 1 := grayRecSlides_one_change_next
