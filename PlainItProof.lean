import «Subsets».BinVal

def Subset.incr {n : Nat} : Subset n → Option (Subset n)
  | nil => none
  | cons false bs => some (cons true bs)
  | cons true bs =>
    match bs.incr with
    | none => none
    | some out => some (cons false out)

theorem Subset.incr_bV {n : Nat} (s : Subset n) {h : s.incr.isSome} : (binValOne (s.incr.get h) 1) + 1 = binValOne s 1 := by
  induction n with
  | zero =>
    match s with
    | nil => nofun
  | succ n' ih =>
    match s with
    | cons false bs => simp only [binValOne, ↓reduceIte, Fin.isValue, Fin.reduceSub, Fin.val_zero, Nat.zero_add, Nat.add_comm,
  Bool.false_eq_true, Fin.val_one]
    | cons true bs =>
      match h' : bs.incr with
      | none =>
        have : (cons true bs).incr.isSome = false := by simp [incr, h']
        have : true = false :=
          calc true
            _ = (cons true bs).incr.isSome := by rw [h]
            _ = false := this
        contradiction
      | some out =>
        calc (binValOne ((cons true bs).incr.get h) 1) + 1
          _ = (binValOne (cons false out) 1) + 1 := by simp only [incr, h', Option.get_some, Fin.isValue]
          _ = 2 * (binValOne out 1) + 1 + 1 := by simp only [binValOne, Bool.false_eq_true, ↓reduceIte, Fin.isValue, Fin.val_one, Nat.add_comm]
          _ = 2 * (binValOne (bs.incr.get (by simp only [h', Option.isSome_some])) 1) + 1 + 1 := by simp only [Fin.isValue, h', Option.get_some]
          _ = 2 * ((binValOne (bs.incr.get (by simp only [h', Option.isSome_some])) 1) + 1) := by simp_arith
          _ = 2 * (binValOne bs 1) := by rw [ih]
          _ = binValOne (cons true bs) 1 := by simp only [Fin.isValue, binValOne, ↓reduceIte, Fin.reduceSub, Fin.val_zero, Nat.zero_add]

def Subset.helpGenIt {n : Nat} (soFar : List (Subset n)) (_ : soFar.length>0) : List (Subset n) :=
  match h : soFar[0].incr with
  | none => soFar
  | some next =>
    have : (binValOne next 1) + 1 = (binValOne soFar[0] 1) :=
      calc (binValOne next 1) + 1
        _ = (binValOne (soFar[0].incr.get (by simp only [h, Option.isSome_some])) 1) + 1 := by simp only [Fin.isValue, h, Option.get_some]
        _ = binValOne soFar[0] 1 := incr_bV soFar[0]
    helpGenIt (next :: soFar) (by simp only [List.length_cons, gt_iff_lt, Nat.zero_lt_succ])
  termination_by (binValOne soFar[0] 1)

def Subset.genIt (n : Nat) : List (Subset n) := helpGenIt [initFalse n] (by simp only [List.length_singleton, gt_iff_lt, Nat.lt_add_one])

#eval (Subset.genIt 3)
