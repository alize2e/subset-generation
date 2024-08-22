import Subsets.working.GrayCodeProofC3

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
          sorry
        else
          exact (c3 n' i ih (by assumption) h (by assumption) (by assumption))
