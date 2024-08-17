import Subsets.GrayRecComp

def Subset.num_changes {n : Nat} : Subset n → Subset n → Nat
  | nil, nil => 0
  | cons true as, cons true bs => num_changes as bs
  | cons false as, cons false bs => num_changes as bs
  | cons _ as, cons _ bs => 1 + num_changes as bs

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
    have h1 : i'.succ<(l.map f).length := by simp [h]
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

-- copied from documentation, idk why not imported
theorem Nat.sub_one_add_one_eq_of_pos : ∀ {n}, 0 < n → (n - 1) + 1 = n
  | _+1, _ => rfl

-- edit so that i show it's also a gray cycle by changing h to ≤ not <, but a pain for indices
theorem Subset.grayRecSlides_one_change_next {n : Nat} {parity : Bool} {i : Nat} {h : i.succ<(grayRecSlides n).length} :
  num_changes (grayRecSlides n)[i] (grayRecSlides n)[i+1] = 1 := by
    induction n generalizing i with
    | zero => nofun
    | succ n' ih =>
      rw [grayRecSlides_IS n'] at h
      if i.succ<((grayRecSlides n').map (cons false)).length then
        have hi : i.succ<((grayRecSlides n').map (cons false)).length := by assumption
        have hi' : i<((grayRecSlides n').map (cons false)).length := Nat.lt_of_succ_lt hi
        have : ((grayRecSlides n').map (cons false)).length = (grayRecSlides n').length := by simp
        rw [this] at hi'
        have hi'' : i<((grayRecSlides n').map (cons false)).length := Nat.lt_of_succ_lt hi
        have : i.succ<(((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true))).length := by assumption
        have h1 : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] = ((grayRecSlides n').map (cons false))[i] := List.get_append_left ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) hi''
        have h2 : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] = ((grayRecSlides n').map (cons false))[i.succ] := List.get_append_left ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) hi
        calc num_changes (grayRecSlides n'.succ)[i] (grayRecSlides n'.succ)[i.succ]
          _ = num_changes (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by simp [hi, grayRecSlides_IS n']
          _ = num_changes ((grayRecSlides n').map (cons false))[i] ((grayRecSlides n').map (cons false))[i.succ] := by simp [h1, h2]
          _ = num_changes (cons false (grayRecSlides n')[i]) ((grayRecSlides n').map (cons false))[i.succ] := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons false) (grayRecSlides n') i]
          _ = num_changes (cons false (grayRecSlides n')[i]) (cons false (grayRecSlides n')[i.succ]) := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons false) (grayRecSlides n') i.succ]
          _ = num_changes (grayRecSlides n')[i] (grayRecSlides n')[i.succ] := by rw [cons_same_num_changes]
          _ = 1 := by rw [ih]
      else
        if i.succ = ((grayRecSlides n').map (cons false)).length then
          have hi : i.succ = ((grayRecSlides n').map (cons false)).length := by assumption
          have hi' : i.succ = (grayRecSlides n').length := by simp [hi]
          have h3 : i < i.succ := by simp
          have h4 : i < i.succ := by simp
          rw [hi] at h3
          rw [hi'] at h4
          have : ((grayRecSlides n').reverse.map (cons true)).length = ((grayRecSlides n').map (cons false)).length := by simp
          have : i.succ<(((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true))).length := by assumption
          have : ((grayRecSlides n').reverse).length = ((grayRecSlides n').map (cons false)).length := by simp
          have h1 : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] = ((grayRecSlides n').map (cons false))[i] := List.get_append_left ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) h3
          have h5 : (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[((grayRecSlides n').map (cons false)).length] = ((grayRecSlides n').reverse.map (cons true))[((grayRecSlides n').map (cons false)).length-((grayRecSlides n').map (cons false)).length] := List.get_append_right ((grayRecSlides n').map (cons false)) ((grayRecSlides n').reverse.map (cons true)) (by simp [hi])
          have h7 : 0 < (grayRecSlides n').reverse.reverse.length := by
            calc 0
              _ < 2^n' := by simp [Nat.two_pow_pos]
              _ = (grayRecSlides n').length := by rw [grayRecSlides_num]
              _ = (grayRecSlides n').reverse.reverse.length := by simp
          have h6 : (grayRecSlides n').reverse.reverse.length - 1 < (grayRecSlides n').reverse.reverse.length := by
            calc (grayRecSlides n').reverse.reverse.length - 1
              _ < ((grayRecSlides n').reverse.reverse.length - 1).succ := by simp
              _ = (grayRecSlides n').reverse.reverse.length - 1 + 1 := by simp
              _ = (grayRecSlides n').reverse.reverse.length := by rw [Nat.sub_one_add_one_eq_of_pos h7]
          calc num_changes (grayRecSlides n'.succ)[i] (grayRecSlides n'.succ)[i.succ]
            _ = num_changes (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by simp [hi, grayRecSlides_IS n']
            _ = num_changes ((grayRecSlides n').map (cons false))[i] (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by rw [h1]
            _ = num_changes (cons false (grayRecSlides n')[i]) (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons false) (grayRecSlides n') i]
            _ = num_changes (cons false (grayRecSlides n')[i]) (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[((grayRecSlides n').map (cons false)).length] := by simp [hi']
            _ = num_changes (cons false (grayRecSlides n')[i]) ((grayRecSlides n').reverse.map (cons true))[((grayRecSlides n').map (cons false)).length-((grayRecSlides n').map (cons false)).length] := by rw [h5]
            _ = num_changes (cons false (grayRecSlides n')[i]) ((grayRecSlides n').reverse.map (cons true))[0] := by simp
            _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n').reverse[0]) := by rw [List.diy_get_map (Subset n') (Subset n'.succ) (cons true) (grayRecSlides n').reverse 0]
            _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n').reverse.reverse[(grayRecSlides n').reverse.reverse.length-1]) := by rw [List.diy_reverse_zero_last]
            _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n')[(grayRecSlides n').length-1]) := by simp
            _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n')[i.succ-1]) := by simp [hi]
            _ = num_changes (cons false (grayRecSlides n')[i]) (cons true (grayRecSlides n')[i]) := by simp
            _ = 1 + num_changes (grayRecSlides n')[i] (grayRecSlides n')[i] := by rfl
            _ = 1 + 0 := by simp [eq_num_changes_eq_zero]
            _ = 1 := by simp
        else
          sorry
