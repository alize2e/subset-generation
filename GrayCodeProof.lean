import Subsets.working.GrayCodeProofLemmas

-- edit so that i show it's also a gray cycle by changing h to ≤ not <, but a pain for indices
theorem Subset.grayRecSlides_one_change_next {n : Nat} {parity : Bool} {i : Nat} {h : i.succ<(grayRecSlides n).length} :
  num_changes (grayRecSlides n)[i] (grayRecSlides n)[i+1] = 1 := by
    induction n generalizing i with
    | zero => nofun
    | succ n' ih =>
      rw [grayRecSlides_IS n'] at h
      if i.succ<((grayRecSlides n').map (cons false)).length then
        have succ_i_in_bounds : i.succ<((grayRecSlides n').map (cons false)).length := by assumption
        have : ((grayRecSlides n').map (cons false)).length = (grayRecSlides n').length := by simp
        have i_in_bounds : i<((grayRecSlides n').map (cons false)).length := Nat.lt_of_succ_lt succ_i_in_bounds
        have : i.succ<(((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true))).length := by assumption
        have i_in_left : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] = ((grayRecSlides n').map (cons false))[i] := List.get_append_left ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) i_in_bounds
        have succ_i_in_left : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] = ((grayRecSlides n').map (cons false))[i.succ] := List.get_append_left ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) succ_i_in_bounds
        calc num_changes (grayRecSlides n'.succ)[i] (grayRecSlides n'.succ)[i.succ]
          _ = num_changes (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by simp [succ_i_in_bounds, grayRecSlides_IS n']
          _ = num_changes ((grayRecSlides n').map (cons false))[i] ((grayRecSlides n').map (cons false))[i.succ] := by simp [i_in_left, succ_i_in_left]
          _ = num_changes (cons false (grayRecSlides n')[i]) ((grayRecSlides n').map (cons false))[i.succ] := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons false) (grayRecSlides n') i]
          _ = num_changes (cons false (grayRecSlides n')[i]) (cons false (grayRecSlides n')[i.succ]) := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons false) (grayRecSlides n') i.succ]
          _ = num_changes (grayRecSlides n')[i] (grayRecSlides n')[i.succ] := by rw [cons_same_num_changes]
          _ = 1 := by rw [ih]
      else
        if i.succ = ((grayRecSlides n').map (cons false)).length then
          have succ_i_eq_map_len : i.succ = ((grayRecSlides n').map (cons false)).length := by assumption
          have succ_i_eq_len : i.succ = (grayRecSlides n').length := by simp [succ_i_eq_map_len]
          have i_in_bounds : i < i.succ := by simp
          rw [succ_i_eq_map_len] at i_in_bounds
          have : ((grayRecSlides n').reverse.map (cons true)).length = ((grayRecSlides n').map (cons false)).length := by simp
          have : i.succ<(((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true))).length := by assumption
          have : ((grayRecSlides n').reverse).length = ((grayRecSlides n').map (cons false)).length := by simp
          have i_in_left : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] = ((grayRecSlides n').map (cons false))[i] := List.get_append_left ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) i_in_bounds
          have i_succ_in_right : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[((grayRecSlides n').map (cons false)).length] = ((grayRecSlides n').reverse.map (cons true))[((grayRecSlides n').map (cons false)).length-((grayRecSlides n').map (cons false)).length] := List.get_append_right ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) (by simp [succ_i_eq_map_len])
          have rev_rev_len_pos : 0 < (grayRecSlides n').reverse.reverse.length := by
            calc 0
              _ < 2^n' := by simp [Nat.two_pow_pos]
              _ = (grayRecSlides n').length := by rw [grayRecSlides_num]
              _ = (grayRecSlides n').reverse.reverse.length := by simp
          have : (grayRecSlides n').reverse.reverse.length - 1 < (grayRecSlides n').reverse.reverse.length := by
            calc (grayRecSlides n').reverse.reverse.length - 1
              _ < ((grayRecSlides n').reverse.reverse.length - 1).succ := by simp
              _ = (grayRecSlides n').reverse.reverse.length - 1 + 1 := by simp
              _ = (grayRecSlides n').reverse.reverse.length := by rw [Nat.sub_one_add_one_eq_of_pos rev_rev_len_pos]
          calc num_changes (grayRecSlides n'.succ)[i] (grayRecSlides n'.succ)[i.succ]
            _ = num_changes (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by simp [succ_i_eq_map_len, grayRecSlides_IS n']
            _ = num_changes ((grayRecSlides n').map (cons false))[i] (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by rw [i_in_left]
            _ = num_changes (cons false (grayRecSlides n')[i]) (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons false) (grayRecSlides n') i]
            _ = num_changes (cons false (grayRecSlides n')[i]) (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[((grayRecSlides n').map (cons false)).length] := by simp [succ_i_eq_len]
            _ = num_changes (cons false (grayRecSlides n')[i]) ((grayRecSlides n').reverse.map (cons true))[((grayRecSlides n').map (cons false)).length-((grayRecSlides n').map (cons false)).length] := by rw [i_succ_in_right]
            _ = num_changes (cons false (grayRecSlides n')[i]) ((grayRecSlides n').reverse.map (cons true))[0] := by simp
            _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n').reverse[0]) := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons true) (grayRecSlides n').reverse 0]
            _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n').reverse.reverse[(grayRecSlides n').reverse.reverse.length-1]) := by rw [List.diy_reverse_zero_last]
            _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n')[(grayRecSlides n').length-1]) := by simp
            _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n')[i.succ-1]) := by simp [succ_i_eq_map_len]
            _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n')[i]) := by simp
            _ = 1 + num_changes (grayRecSlides n')[i] (grayRecSlides n')[i] := by rfl
            _ = 1 + 0 := by simp [eq_num_changes_eq_zero]
            _ = 1 := by simp
        else
          sorry
