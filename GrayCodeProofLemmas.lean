import Subsets.GrayRecComp

def Subset.num_changes {n : Nat} : Subset n → Subset n → Nat
  | nil, nil => 0
  | cons true as, cons true bs => num_changes as bs
  | cons false as, cons false bs => num_changes as bs
  | cons _ as, cons _ bs => 1 + num_changes as bs

theorem Subset.symm_num_changes {n : Nat} {as bs : Subset n} : num_changes as bs = num_changes bs as := by
  induction n with
  | zero =>
    match as, bs with
    | nil, nil => rfl
  | succ n' ih =>
    match as, bs with
    | cons true xs, cons true ys =>
      calc num_changes (cons true xs) (cons true ys)
        _ = num_changes xs ys := by rfl
        _ = num_changes ys xs := by rw [ih]
        _ = num_changes (cons true ys) (cons true xs) := by rfl
    | cons false xs, cons false ys =>
      calc num_changes (cons false xs) (cons false ys)
        _ = num_changes xs ys := by rfl
        _ = num_changes ys xs := by rw [ih]
        _ = num_changes (cons false ys) (cons false xs) := by rfl
    | cons true xs, cons false ys =>
      calc num_changes (cons true xs) (cons false ys)
        _ = 1 + num_changes xs ys := by rfl
        _ = 1 + num_changes ys xs := by rw [ih]
        _ = num_changes (cons false ys) (cons true xs) := by rfl
    | cons false xs, cons true ys =>
      calc num_changes (cons false xs) (cons true ys)
        _ = 1 + num_changes xs ys := by rfl
        _ = 1 + num_changes ys xs := by rw [ih]
        _ = num_changes (cons true ys) (cons false xs) := by rfl

theorem Subset.cons_same_num_changes {n : Nat} {as bs : Subset n} {x : Bool} : num_changes (cons x as) (cons x bs) = num_changes as bs := by
  cases x
  repeat rfl

theorem Subset.eq_num_changes_eq_zero {n : Nat} {as : Subset n} : num_changes as as = 0 := by
  induction as with
  | nil => rfl
  | cons b bs ih =>
    have : num_changes (cons b bs) (cons b bs) = num_changes bs bs := by cases b <;> repeat rfl
    rw [this]
    rw [ih]

-- List.get_map not imported, and not working ://///
theorem List.diy_get_map (α β : Type) (f : α → β) (l : List α) (i : Nat) {h : i<l.length} : (l.map f)[i]'(by simp[h]) = f l[i] := by
  induction i generalizing l with
  | zero =>
    match l with
    | x::xs => rfl
  | succ i' ih =>
    have : i'.succ<(l.map f).length := by simp [h]
    match l with
    | x::xs =>
      have : (xs.map f).length.succ = ((x::xs).map f).length := by rfl
      have : (xs.map f).length = xs.length := by simp
      calc ((x::xs).map f)[i'.succ]
        _ = (xs.map f)[i'] := by simp
        _ = f xs[i'] := by rw [ih]

theorem List.diy_reverse_zero_last {α : Type} {l : List α} {h : 0<l.length} {h' : l.reverse.length-1<l.reverse.length} : l.reverse[l.reverse.length-1] = l[0] := by
  match l with
  | x::xs =>
    have : (x::xs).reverse = xs.reverse++[x] := List.reverse_cons x xs
    have : ¬ (xs.reverse++[x]).length-1 < xs.reverse.length := by simp
    calc (x::xs).reverse[(x::xs).reverse.length-1]
      _ = (xs.reverse++[x])[(xs.reverse++[x]).length-1] := by simp
      _ = x := List.get_last this
      _ = (x::xs)[0] := by simp

-- copied from documentation, idk why not imported for everything below
theorem Nat.sub_one_add_one_eq_of_pos : ∀ {n}, 0 < n → (n - 1) + 1 = n
  | _+1, _ => rfl

theorem Nat.sub_lt_sub_right : ∀ {a b c : Nat}, c ≤ a → a < b → a - c < b - c
  | 0, _, _, hle, h => by
    rw [Nat.eq_zero_of_le_zero hle, Nat.sub_zero, Nat.sub_zero]
    exact h
  | _, _, 0, _, h => by
    rw [Nat.sub_zero, Nat.sub_zero]
    exact h
  | _+1, _+1, _+1, hle, h => by
    rw [Nat.add_sub_add_right, Nat.add_sub_add_right]
    exact Nat.sub_lt_sub_right (le_of_succ_le_succ hle) (lt_of_succ_lt_succ h)

theorem Nat.sub_one_sub_lt_of_lt (h : a < b) : b - 1 - a < b := by
  rw [← Nat.sub_add_eq]
  exact sub_lt (zero_lt_of_lt h) (Nat.lt_add_right a Nat.one_pos)

-- @[simp] theorem List.get?_eq_getElem? (l : List α) (i : Nat) : l.get? i = l[i]? := by
--   simp only [getElem?, decidableGetElem?]; split
--   · exact (get?_eq_get ‹_›)
--   · exact (get?_eq_none.2 <| Nat.not_lt.1 ‹_›)

-- @[simp] theorem List.getElem?_eq_getElem {l : List α} {n} (h : n < l.length) : l[n]? = some l[n] := by
--   simp only [← get?_eq_getElem?, get?_eq_get, h, get_eq_getElem]

-- @[simp] theorem List.getElem_reverse {l : List α} {i} (h : i < l.reverse.length) :
--     l.reverse[i] = l[l.length - 1 - i]'(Nat.sub_one_sub_lt_of_lt (by simpa using h)) := by
--       apply Option.some.inj
--       rw [← getElem?_eq_getElem, ← getElem?_eq_getElem]
--       rw [getElem?_reverse (by simpa using h)]

-- theorem Subset.GRS_1_change_mid (n' : Nat) (i : Nat) (h : i.succ < (grayRecSlides n'.succ).length) (succ_i_eq_map_len : i.succ = ((grayRecSlides n').map (cons false)).length) :
--   num_changes (grayRecSlides n'.succ)[i] (grayRecSlides n'.succ)[i+1] = 1 := by
--     have succ_i_eq_len : i.succ = (grayRecSlides n').length := by simp [succ_i_eq_map_len]
--     have i_in_bounds : i < i.succ := by simp
--     rw [succ_i_eq_map_len] at i_in_bounds
--     have : ((grayRecSlides n').reverse.map (cons true)).length = ((grayRecSlides n').map (cons false)).length := by simp
--     have : (grayRecSlides n'.succ).length = (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true))).length := by rw [grayRecSlides_IS n']
--     have : i.succ<(((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true))).length := by simp [this, h]
--     have : ((grayRecSlides n').reverse).length = ((grayRecSlides n').map (cons false)).length := by simp
--     have i_in_left : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] = ((grayRecSlides n').map (cons false))[i] := List.get_append_left ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) i_in_bounds
--     have i_succ_in_right : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[((grayRecSlides n').map (cons false)).length] = ((grayRecSlides n').reverse.map (cons true))[((grayRecSlides n').map (cons false)).length-((grayRecSlides n').map (cons false)).length] := List.get_append_right ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) (by simp [succ_i_eq_map_len])
--     have rev_rev_len_pos : 0 < (grayRecSlides n').reverse.reverse.length := by
--       calc 0
--         _ < 2^n' := by simp [Nat.two_pow_pos]
--         _ = (grayRecSlides n').length := by rw [grayRecSlides_num]
--         _ = (grayRecSlides n').reverse.reverse.length := by simp
--     have : (grayRecSlides n').reverse.reverse.length - 1 < (grayRecSlides n').reverse.reverse.length := by
--       calc (grayRecSlides n').reverse.reverse.length - 1
--         _ < ((grayRecSlides n').reverse.reverse.length - 1).succ := by simp
--         _ = (grayRecSlides n').reverse.reverse.length - 1 + 1 := by simp
--         _ = (grayRecSlides n').reverse.reverse.length := by rw [Nat.sub_one_add_one_eq_of_pos rev_rev_len_pos]
--     calc num_changes (grayRecSlides n'.succ)[i] (grayRecSlides n'.succ)[i.succ]
--       _ = num_changes (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by simp [succ_i_eq_map_len, grayRecSlides_IS n']
--       _ = num_changes ((grayRecSlides n').map (cons false))[i] (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by rw [i_in_left]
--       _ = num_changes (cons false (grayRecSlides n')[i]) (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons false) (grayRecSlides n') i]
--       _ = num_changes (cons false (grayRecSlides n')[i]) (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[((grayRecSlides n').map (cons false)).length] := by simp [succ_i_eq_len]
--       _ = num_changes (cons false (grayRecSlides n')[i]) ((grayRecSlides n').reverse.map (cons true))[((grayRecSlides n').map (cons false)).length-((grayRecSlides n').map (cons false)).length] := by rw [i_succ_in_right]
--       _ = num_changes (cons false (grayRecSlides n')[i]) ((grayRecSlides n').reverse.map (cons true))[0] := by simp
--       _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n').reverse[0]) := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons true) (grayRecSlides n').reverse 0]
--       _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n').reverse.reverse[(grayRecSlides n').reverse.reverse.length-1]) := by rw [List.diy_reverse_zero_last]
--       _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n')[(grayRecSlides n').length-1]) := by simp
--       _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n')[i.succ-1]) := by simp [succ_i_eq_map_len]
--       _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n')[i]) := by simp
--       _ = 1 + num_changes (grayRecSlides n')[i] (grayRecSlides n')[i] := by rfl
--       _ = 1 + 0 := by simp [eq_num_changes_eq_zero]
--       _ = 1 := by simp

-- import Subsets.working.GrayCodeProofLemmas

-- -- edit so that i show it's also a gray cycle by changing h to ≤ not <, but a pain for indices
-- theorem Subset.grayRecSlides_one_change_next {n : Nat} {i : Nat} {h : i.succ<(grayRecSlides n).length} :
--   num_changes (grayRecSlides n)[i] (grayRecSlides n)[i+1] = 1 := by
--     induction n generalizing i with
--     | zero => nofun
--     | succ n' ih =>
--       rw [grayRecSlides_IS n'] at h
--       if i.succ<((grayRecSlides n').map (cons false)).length then
--         sorry
--       --   have succ_i_in_bounds : i.succ<((grayRecSlides n').map (cons false)).length := by assumption
--       --   have : ((grayRecSlides n').map (cons false)).length = (grayRecSlides n').length := by simp
--       --   have i_in_bounds : i<((grayRecSlides n').map (cons false)).length := Nat.lt_of_succ_lt succ_i_in_bounds
--       --   have : i.succ<(((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true))).length := by assumption
--       --   have i_in_left : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] = ((grayRecSlides n').map (cons false))[i] := List.get_append_left ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) i_in_bounds
--       --   have succ_i_in_left : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] = ((grayRecSlides n').map (cons false))[i.succ] := List.get_append_left ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) succ_i_in_bounds
--       --   calc num_changes (grayRecSlides n'.succ)[i] (grayRecSlides n'.succ)[i.succ]
--       --     _ = num_changes (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by simp [succ_i_in_bounds, grayRecSlides_IS n']
--       --     _ = num_changes ((grayRecSlides n').map (cons false))[i] ((grayRecSlides n').map (cons false))[i.succ] := by simp [i_in_left, succ_i_in_left]
--       --     _ = num_changes (cons false (grayRecSlides n')[i]) ((grayRecSlides n').map (cons false))[i.succ] := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons false) (grayRecSlides n') i]
--       --     _ = num_changes (cons false (grayRecSlides n')[i]) (cons false (grayRecSlides n')[i.succ]) := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons false) (grayRecSlides n') i.succ]
--       --     _ = num_changes (grayRecSlides n')[i] (grayRecSlides n')[i.succ] := by rw [cons_same_num_changes]
--       --     _ = 1 := by rw [ih]
--       else
--         if i.succ = ((grayRecSlides n').map (cons false)).length then
--           sorry
--         --   have succ_i_eq_map_len : i.succ = ((grayRecSlides n').map (cons false)).length := by assumption
--         --   have succ_i_eq_len : i.succ = (grayRecSlides n').length := by simp [succ_i_eq_map_len]
--         --   have i_in_bounds : i < i.succ := by simp
--         --   rw [succ_i_eq_map_len] at i_in_bounds
--         --   have : ((grayRecSlides n').reverse.map (cons true)).length = ((grayRecSlides n').map (cons false)).length := by simp
--         --   have : i.succ<(((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true))).length := by assumption
--         --   have : ((grayRecSlides n').reverse).length = ((grayRecSlides n').map (cons false)).length := by simp
--         --   have i_in_left : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] = ((grayRecSlides n').map (cons false))[i] := List.get_append_left ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) i_in_bounds
--         --   have i_succ_in_right : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[((grayRecSlides n').map (cons false)).length] = ((grayRecSlides n').reverse.map (cons true))[((grayRecSlides n').map (cons false)).length-((grayRecSlides n').map (cons false)).length] := List.get_append_right ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) (by simp [succ_i_eq_map_len])
--         --   have rev_rev_len_pos : 0 < (grayRecSlides n').reverse.reverse.length := by
--         --     calc 0
--         --       _ < 2^n' := by simp [Nat.two_pow_pos]
--         --       _ = (grayRecSlides n').length := by rw [grayRecSlides_num]
--         --       _ = (grayRecSlides n').reverse.reverse.length := by simp
--         --   have : (grayRecSlides n').reverse.reverse.length - 1 < (grayRecSlides n').reverse.reverse.length := by
--         --     calc (grayRecSlides n').reverse.reverse.length - 1
--         --       _ < ((grayRecSlides n').reverse.reverse.length - 1).succ := by simp
--         --       _ = (grayRecSlides n').reverse.reverse.length - 1 + 1 := by simp
--         --       _ = (grayRecSlides n').reverse.reverse.length := by rw [Nat.sub_one_add_one_eq_of_pos rev_rev_len_pos]
--         --   calc num_changes (grayRecSlides n'.succ)[i] (grayRecSlides n'.succ)[i.succ]
--         --     _ = num_changes (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by simp [succ_i_eq_map_len, grayRecSlides_IS n']
--         --     _ = num_changes ((grayRecSlides n').map (cons false))[i] (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by rw [i_in_left]
--         --     _ = num_changes (cons false (grayRecSlides n')[i]) (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons false) (grayRecSlides n') i]
--         --     _ = num_changes (cons false (grayRecSlides n')[i]) (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[((grayRecSlides n').map (cons false)).length] := by simp [succ_i_eq_len]
--         --     _ = num_changes (cons false (grayRecSlides n')[i]) ((grayRecSlides n').reverse.map (cons true))[((grayRecSlides n').map (cons false)).length-((grayRecSlides n').map (cons false)).length] := by rw [i_succ_in_right]
--         --     _ = num_changes (cons false (grayRecSlides n')[i]) ((grayRecSlides n').reverse.map (cons true))[0] := by simp
--         --     _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n').reverse[0]) := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons true) (grayRecSlides n').reverse 0]
--         --     _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n').reverse.reverse[(grayRecSlides n').reverse.reverse.length-1]) := by rw [List.diy_reverse_zero_last]
--         --     _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n')[(grayRecSlides n').length-1]) := by simp
--         --     _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n')[i.succ-1]) := by simp [succ_i_eq_map_len]
--         --     _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n')[i]) := by simp
--         --     _ = 1 + num_changes (grayRecSlides n')[i] (grayRecSlides n')[i] := by rfl
--         --     _ = 1 + 0 := by simp [eq_num_changes_eq_zero]
--         --     _ = 1 := by simp
--         else
--           have h1 : ¬ (i.succ<((grayRecSlides n').map (cons false)).length) := by assumption
--           rw [Nat.not_lt_eq i.succ ((grayRecSlides n').map (cons false)).length] at h1
--           have h2 : ¬ i.succ = ((grayRecSlides n').map (cons false)).length := by assumption
--           have h3 : ¬ ((grayRecSlides n').map (cons false)).length = i.succ := Ne.symm h2
--           have h4 : ((grayRecSlides n').map (cons false)).length < i.succ := Nat.lt_of_le_of_ne h1 h3
--           have h5 : ((grayRecSlides n').map (cons false)).length ≤ i := Nat.le_of_lt_succ h4
--           have h6 : ((grayRecSlides n').map (cons false)).length ≤ i → ¬ (i<((grayRecSlides n').map (cons false)).length) := by simp [Nat.not_lt]
--           have h7 : ¬ (i<((grayRecSlides n').map (cons false)).length) := h6 h5
--           have : i-((grayRecSlides n').reverse.map (cons true)).length < ((grayRecSlides n').reverse.map (cons true)).length := by
--             calc i-((grayRecSlides n').reverse.map (cons true)).length
--               < (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true))).length - ((grayRecSlides n').reverse.map (cons true)).length := by assumption
--           have : i.succ<(((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true))).length := by assumption
--           have i_in_right : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] = ((grayRecSlides n').reverse.map (cons true))[i-((grayRecSlides n').reverse.map (cons true)).length] := List.get_append_right ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true))
--           have i_in_right : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] = ((grayRecSlides n').reverse.map (cons true))[i.succ-((grayRecSlides n').reverse.map (cons true)).length] := List.get_append_right ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true))
--           sorry