import Subsets.working.GrayCodeProofLemmas

example {l i : Nat} {_ : i<2*l} {_ : l≤i} : (l-1-(i.succ-l)).succ = l-1-(i-l) :=
  have : i≥l := by assumption
  calc (l-1-(i.succ-l)).succ
    _ = (l-1-(i+1-l))+1 := by simp_arith
    _ = l-1-(i+1-l)+1 := by simp_arith
    _ = l-1-(1+i-l)+1 := by simp_arith [Nat.add_comm]
    _ = l-1-(1+(i-l))+1 := by simp_arith [this]

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
