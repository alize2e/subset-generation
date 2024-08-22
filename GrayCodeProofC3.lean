import Subsets.working.GrayCodeProofLemmas

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
    -- have h8 : i.succ<(((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true))).length := by assumption
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
