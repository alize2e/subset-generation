import Subsets.GrayRecComp

def Subset.num_changes {n : Nat} : Subset n → Subset n → Nat
  | nil, nil => 0
  | cons true as, cons true bs => num_changes as bs
  | cons false as, cons false bs => num_changes as bs
  | cons _ as, cons _ bs => 1 + num_changes as bs

theorem Subset.cons_same_num_changes {n : Nat} {as bs : Subset n} {x : Bool} : num_changes (cons x as) (cons x bs) = num_changes as bs := by
  cases x
  repeat rfl

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
          have h3 : i < i.succ := by simp
          simp only [hi] at h3
          -- have hi' : i<((grayRecSlides n').map (cons false)).length := by simp [hi, this]
          calc num_changes (grayRecSlides n'.succ)[i] (grayRecSlides n'.succ)[i.succ]
           _ = num_changes (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i] (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)))[i.succ] := by simp [hi, grayRecSlides_IS n']

        else
          sorry
