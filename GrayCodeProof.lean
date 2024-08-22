import Subsets.working.GrayCodeProofLemmas

axiom List.sorry_getElem_reverse {α : Type} {l : List α} {i} (h : i < l.reverse.length) :
    l.reverse[i] = l[l.length - 1 - i]'(Nat.sub_one_sub_lt_of_lt (by simpa using h)) -- List.getElem_reverse

-- edit so that i show it's also a gray cycle by changing h to ≤ not <, but a pain for indices
theorem Subset.grayRecSlides_one_change_next {n : Nat} {i : Nat} {h : i.succ<(grayRecSlides n).length} :
  num_changes (grayRecSlides n)[i] (grayRecSlides n)[i+1] = 1 := by
    induction n generalizing i with
    | zero => nofun
    | succ n' ih =>
      rw [grayRecSlides_IS n'] at h
      if i.succ<((grayRecSlides n').map (cons false)).length then
        sorry
      else
        if i.succ = ((grayRecSlides n').map (cons false)).length then
          sorry
        else
          have h1 : ¬ (i.succ<((grayRecSlides n').map (cons false)).length) := by assumption
          rw [Nat.not_lt_eq i.succ ((grayRecSlides n').map (cons false)).length] at h1
          have h2 : ¬ i.succ = ((grayRecSlides n').map (cons false)).length := by assumption
          have h3 : ¬ ((grayRecSlides n').map (cons false)).length = i.succ := Ne.symm h2
          have h4 : ((grayRecSlides n').map (cons false)).length < i.succ := Nat.lt_of_le_of_ne h1 h3
          have h5 : ((grayRecSlides n').map (cons false)).length ≤ i := Nat.le_of_lt_succ h4
          have h6 : ((grayRecSlides n').map (cons false)).length ≤ i → ¬ (i<((grayRecSlides n').map (cons false)).length) := by simp [Nat.not_lt]
          have h7 : ¬ (i<((grayRecSlides n').map (cons false)).length) := h6 h5
          have h11 : i.succ-((grayRecSlides n').map (cons false)).length < ((grayRecSlides n').reverse.map (cons true)).length :=
            calc i.succ-((grayRecSlides n').map (cons false)).length
              _ < (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true))).length - ((grayRecSlides n').map (cons false)).length := Nat.sub_lt_sub_right h1 (by assumption)
              _ = ((grayRecSlides n').map (cons false)).length + ((grayRecSlides n').reverse.map (cons true)).length - ((grayRecSlides n').map (cons false)).length := by simp
              _ = ((grayRecSlides n').reverse.map (cons true)).length := by simp
          -- have h12 : i.succ < (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true))).length := by assumption
          -- have h13 : i.succ - ((grayRecSlides n').map (cons false)).length < (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true))).length - ((grayRecSlides n').map (cons false)).length := by simp [h12]
          have h8 : i.succ<(((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true))).length := by assumption
          have h9 : (grayRecSlides n').reverse.length = ((grayRecSlides n').reverse.map (cons true)).length := by repeat simp
          have h9 : ((grayRecSlides n').map (cons false)).length = (grayRecSlides n').length := by repeat simp
          have h10 : i.succ-((grayRecSlides n').map (cons false)).length < (grayRecSlides n').reverse.length := by
            calc i.succ-((grayRecSlides n').map (cons false)).length
              _ < ((grayRecSlides n').reverse.map (cons true)).length := h11
              _ = (grayRecSlides n').reverse.length := by simp
          have succ_i_in_right : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] = ((grayRecSlides n').reverse.map (cons true))[i.succ-((grayRecSlides n').map (cons false)).length] := List.get_append_right ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) (by assumption)
          have i_in_right : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] = ((grayRecSlides n').reverse.map (cons true))[i-((grayRecSlides n').map (cons false)).length] := List.get_append_right ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) (by assumption)
          have : List.length (grayRecSlides n') - 1 - (i - List.length (grayRecSlides n')) < List.length (grayRecSlides n') := s1 (s0 n')
          have h15 : (grayRecSlides n').length < i.succ :=
            calc (grayRecSlides n').length
              _ = ((grayRecSlides n').map (cons false)).length := by repeat simp
              _ < i.succ := h4
          have h16 : i.succ < 2*(grayRecSlides n').length :=
            calc i.succ
              _ < (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true))).length := by assumption
              _ = ((grayRecSlides n').map (cons false)).length + ((grayRecSlides n').reverse.map (cons true)).length := by simp
              _ = (grayRecSlides n').length + (grayRecSlides n').length := by simp
              _ = 2*(grayRecSlides n').length := by rw [←Nat.two_mul (grayRecSlides n').length]
          have : Nat.succ (List.length (grayRecSlides n') - 1 - (Nat.succ i - List.length (grayRecSlides n'))) < List.length (grayRecSlides n') :=
            calc Nat.succ (List.length (grayRecSlides n') - 1 - (Nat.succ i - List.length (grayRecSlides n')))
              _ < Nat.succ (List.length (grayRecSlides n') - 1) := Nat.succ_lt_succ (s2 h15 (s2' h16 h15))
              _ = Nat.succ (Nat.pred (List.length (grayRecSlides n'))) := by rfl
              _ = List.length (grayRecSlides n') := Nat.succ_pred_eq_of_ne_zero (Nat.ne_of_lt' (s0 n'))
          calc num_changes (grayRecSlides n'.succ)[i] (grayRecSlides n'.succ)[i.succ]
            _ = num_changes (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by simp [grayRecSlides_IS n']
            _ = num_changes ((grayRecSlides n').reverse.map (cons true))[i-((grayRecSlides n').map (cons false)).length] ((grayRecSlides n').reverse.map (cons true))[i.succ-((grayRecSlides n').map (cons false)).length] := by simp [i_in_right, succ_i_in_right]
            _ = num_changes (cons true (grayRecSlides n').reverse[i-((grayRecSlides n').map (cons false)).length]) ((grayRecSlides n').reverse.map (cons true))[i.succ-((grayRecSlides n').map (cons false)).length] := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons true) (grayRecSlides n').reverse (i-((grayRecSlides n').map (cons false)).length)]
            _ = num_changes (cons true (grayRecSlides n').reverse[i-((grayRecSlides n').map (cons false)).length]) (cons true (grayRecSlides n').reverse[i.succ-((grayRecSlides n').map (cons false)).length]) := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons true) (grayRecSlides n').reverse (i.succ-((grayRecSlides n').map (cons false)).length)]
            _ = num_changes (grayRecSlides n').reverse[i-((grayRecSlides n').map (cons false)).length] (grayRecSlides n').reverse[i.succ-((grayRecSlides n').map (cons false)).length] := by rw [cons_same_num_changes]
            _ = num_changes (grayRecSlides n').reverse[i-(grayRecSlides n').length] (grayRecSlides n').reverse[i.succ-(grayRecSlides n').length] := by simp
            _ = num_changes (grayRecSlides n')[(grayRecSlides n').length-1-(i-(grayRecSlides n').length)] (grayRecSlides n')[(grayRecSlides n').length-1-(i.succ-(grayRecSlides n').length)] := by simp [List.sorry_getElem_reverse] -- FIX!!!!!
            _ = num_changes (grayRecSlides n')[((grayRecSlides n').length-1-(i.succ-(grayRecSlides n').length)).succ] (grayRecSlides n')[(grayRecSlides n').length-1-(i.succ-(grayRecSlides n').length)] := sorry
            _ = num_changes (grayRecSlides n')[(grayRecSlides n').length-1-(i.succ-(grayRecSlides n').length)] (grayRecSlides n')[((grayRecSlides n').length-1-(i.succ-(grayRecSlides n').length)).succ] := by rw [symm_num_changes]
            _ = 1 := by rw [ih]
