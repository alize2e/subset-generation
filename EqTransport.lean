import «Subsets».BinVal

def Subset.eqTransport {n m : Nat} : Subset n → Subset m → Bool -- Bool or Prop?
  | nil, nil => true
  | cons true as, cons true bs => eqTransport as bs
  | cons false as, cons false bs => eqTransport as bs
  | _, _ => false

theorem Subset.eqT_eqBV {n m : Nat} {s1 : Subset n} {s2 : Subset m} (eqT : eqTransport s1 s2) {opp : Fin 2} :
  binValOne s1 opp = binValOne s2 opp := by
  induction n generalizing m with
  | zero =>
    match s1, s2 with
    | nil, nil => rfl
  | succ n' ih =>
    match s1, s2 with
    | cons true as, cons true bs =>
      simp [binValOne, eqTransport]
      rw [ih]
      if h : eqTransport as bs then
        exact h
      else
        contradiction
    | cons false as, cons false bs =>
      simp [binValOne, eqTransport]
      rw [ih]
      if h : eqTransport as bs then
        exact h
      else
        contradiction
    | cons true as, cons false bs =>
      have : eqTransport (cons true as) (cons false bs) = false := by simp [eqTransport]
      contradiction
    | cons false as, cons true bs =>
      have : eqTransport (cons false as) (cons true bs) = false := by simp [eqTransport]
      contradiction

theorem Subset.eqT_append_IS {n m l : Nat} {as : Subset n} {b : Bool} {bs : Subset m} {s : Subset l} :
  eqTransport s (append as (cons b bs)) = eqTransport s (append (append as (cons b nil)) bs) := by
    induction as generalizing l with
    | nil => rfl
    | cons a as' ih =>
      match s with
      | nil => rfl
      | cons x xs =>
        match x, a with
        | true, true => simp [eqTransport, ih]
        | false, false => simp [eqTransport, ih]
        | true, false => rfl
        | false, true => rfl

theorem Subset.eqT_self {n : Nat} (s : Subset n) : eqTransport s s = true := by
  induction s with
  | nil => rfl
  | cons b bs ih =>
    match b with
      | true => simp [eqTransport, ih]
      | false => simp [eqTransport, ih]
