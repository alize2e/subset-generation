import «Subsets».SubsetDef

def funToSubset {n : Nat} (f : (Fin n) → Bool) : Subset n :=
  match n with
  | 0 => Subset.nil
  | n'+1 =>
    let f' (i : Fin n') : Bool := f (Fin.succ i)
    Subset.cons (f 0) (funToSubset f')

def Subset.toFun : {n : Nat} → Subset n → (Fin n → Bool)
  | 0, Subset.nil =>
    λ (x : Fin 0) => Fin.elim0 x
  | n'+1, Subset.cons b s =>
    λ (i : Fin (n'+1)) => if h : ¬ i = 0 then s.toFun (i.pred (h)) else b

theorem fts_stf_id {n : Nat} {s : Subset n} : funToSubset s.toFun = s := by
  induction s with
  | nil => rfl
  | cons b s' ih =>
    calc funToSubset (Subset.cons b s').toFun
      _ = funToSubset (λ (i : Fin (s'.card+1)) => if h : i ≠ 0 then s'.toFun (i.pred (h)) else b) := by rfl
      _ = Subset.cons b (funToSubset s'.toFun) := by rfl
      _ = Subset.cons b s' := by rw [ih]

theorem stf_fts_id_first {n : Nat} {f : Fin (n+1) → Bool} : (funToSubset f).toFun 0 = f 0 := by rfl
  -- calc (funToSubset f).toFun 0
  --   _ = (Subset.cons (f 0) (funToSubset (λ (i : Fin n) => f (Fin.succ i)))).toFun 0 := by rfl
  --   _ = f 0 := by rfl

theorem stf_fts_id_nil {f : Fin 0 → Bool} : (funToSubset f).toFun = f := by
  funext i
  have : (funToSubset f).toFun i = f i := Fin.elim0 i
  simp [this]

theorem stf_fts_id {n : Nat} {f : Fin n → Bool} : (funToSubset f).toFun = f := by
  induction n with
  | zero => simp [stf_fts_id_nil]
  | succ n' ih =>
    funext i
    if h : i=0 then
      simp [stf_fts_id_first, h]
    else
      calc (funToSubset f).toFun i
        _ = (Subset.cons (f 0) (funToSubset (λ (x : Fin n') => f (Fin.succ x)))).toFun i := by rfl
        _ = (λ (x : Fin (n'+1)) => if h : ¬ x = 0 then (funToSubset (λ (x : Fin n') => f (Fin.succ x))).toFun (x.pred (h)) else (f 0)) i := by rfl
        _ = (funToSubset (λ (x : Fin n') => f (Fin.succ x))).toFun (i.pred h) := by simp [h]
        _ = (λ (x : Fin n') => f (Fin.succ x)) (i.pred h) := by rw [ih]
        _ = f (Fin.succ (i.pred h)) := by rfl
        _ = f i := by simp_arith

def s := Subset.cons false (Subset.cons true (Subset.cons true Subset.nil))

def f (i : Fin 3) : Bool := i≠0

#eval s
#eval funToSubset s.toFun

#eval f 0
#eval (funToSubset f).toFun 0
