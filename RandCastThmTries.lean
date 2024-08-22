-- random theorems i tried to prove, mostly involving casting, plus one about binval where idk why it doesn't allow rfl

import «Subsets».BinVal

def s' := Subset.cons true (Subset.cons true (Subset.cons false Subset.nil))
#eval s'
#eval s' == Subset.cons true (Subset.cons true (Subset.cons false Subset.nil))
#eval s'.append s' == Subset.cons true (Subset.cons true (Subset.cons false (Subset.cons true (Subset.cons true (Subset.cons false Subset.nil)))))

def Subset.eq2 {n m : Nat} (a : Subset n) (b : Subset m) {eq : n=m} : Bool := a == b.cast eq

-- def Subset.eqTransportOld {n m : Nat} (eq : n=m) : Subset n → Subset m → Bool
--   | nil, nil => true
--   | cons a as, cons b bs =>
--     have eq' : as.card = bs.card :=
--       calc as.card
--         _ = as.card+1-1 := by rfl
--         _ = bs.card+1-1 := by rw [eq]
--     a==b ∧ (eqTransportOld eq' as bs)

-- theorem Subset.t {n l r : Nat} {eq_len : l+r=n} (lastStart : Subset l) (xsr : Subset r)
--   (soFar0 : Subset n) (h : ∀ i : Fin n, (lastStart.append xsr).toFun i = soFar0.toFun i) :
--   funToSubset (lastStart.append xsr).toFun = funToSubset soFar0.toFun :=
--     calc funToSubset (lastStart.append xsr).toFun

-- theorem Subset.binVal_eqTransport_IS {n m : Nat} {eq : n.succ=m.succ} {as : Subset n} {bs : Subset m} {opp : Fin 2}
--   {a b : Bool} {h : (cons a as).eqTransport eq (cons b bs)} {ih : as.binValOne opp = bs.binValOne opp} :
--   (cons a as).binValOne opp = (cons b bs).binValOne opp :=
--     calc (cons a as).binValOne opp
--       _ = (if a then 1-opp else opp) + 2*(as.binValOne opp) := by rfl
--       _ = (if b then 1-opp else opp) + 2*(as.binValOne opp) := by simp [h, eqTransport]

-- theorem Subset.binVal_eqTransport {n m : Nat} {a : Subset n} {opp : Fin 2} :
--   ∀ m : Nat, ∀ eq : n=m, ∀ b : Subset m, ∀ h : a.eqTransport b eq, a.binValOne opp = b.binValOne opp := by
--     induction n with
--     | zero =>
--       match a with
--       | nil =>
--         intro m eq b h
--         match b with
--         | nil => rfl
--     | succ n' ih =>
--       match a with
--       | cons x xs =>
--         intro m eq b h



-- theorem Subset.binVal_eqTransport {n m : Nat} {eq : n=m} {a : Subset n} {b : Subset m} {opp : Fin 2} {h : a.eqTransport eq b} :
--   a.binValOne opp = b.binValOne opp := by
--     induction n with
--     | zero =>
--       match a with
--       | nil =>
--         match b with
--         | nil => rfl
--     | succ n' ih =>
--       match a with
--       | cons x xs =>
--         match b

-- theorem Subset.binVal_eq2_eq {n : Nat} {a : Subset n} {b : Subset m} {opp : Fin 2} {eq : n=m} {h : a.eq2 b} :
--   binValOne a opp = binValOne b opp := congrArg binValOne h opp

-- theorem Subset.binVal_eq2_eq {n : Nat} {s : Subset n} {opp : Fin 2} :
--   ∀ m : Nat, ∀ eq : m=n, (s.cast eq).binValOne opp = s.binValOne opp := by
--     induction s with
--     | nil =>
--       intro m eq
--       match (nil.cast eq) with
--       | nil => rfl
--     | cons b bs =>
--       intro m eq
--       match (cons b bs).cast eq with
--       | cons b (bs.cast (by simp_arith [eq])) => rfl

-- theorem Subset.binVal_eq2_eq {n : Nat} {a : Subset n} {b : Subset m} {opp : Fin 2} {eq : n=m} {h : a.eq2 b} :
--   a.binValOne opp = b.binValOne opp := by
--     induction n with
--     | zero =>
--       have : a.card = 0 := by rfl
--       have : Nat.zero = m := by rw [eq]
--       have : b.card = Nat.zero := by rw [eq]
--       match a with
--       | nil => rfl
--     | succ n' ih =>



-- theorem Subset.binVal1_min {n : Nat} {s : Subset n} : (initTrue n).binValOne 1 ≤ s.binValOne 1 := by
--   induction s with
--   | nil =>
--     calc (initTrue 0).binValOne 1
--       _ ≤ (initTrue 0).binValOne 1 := by simp
--       _ = nil.binValOne 1 := by rfl
--   | cons b bs ih =>
--     have h : (if b then 1-1 else 1) ≤ 1 :=
--       match b with
--       | true => by simp_arith
--       | false => by simp_arith
--     calc (initTrue (cons b bs).card).binValOne 1
--       _ = (cons true (initTrue bs.card)).binValOne 1 := by rfl
--       _ = (if true then 1-1 else 1) + 2*(binValOne (initTrue bs.card) 1) := by rfl


  -- (xs.append (cons false nil)).binValOne 1 > ((initFalse n).append (cons true nil)).binValOne 1 := by
  --   induction xs with
  --   | nil => by simp [binVal_msb]
  --   | cons b bs ih =>
  --     calc (nil.append (cons false nil)).binValOne 1
  --       _ = (cons false nil).binValOne 1 := by rfl
  --       _ = (if false then 1-1 else 1) + 2*(Subset.binValOne nil 1) := by rfl
  --       _ = 1 + 2*(Subset.binValOne nil 1) := by simp
  --       _ > 0 + 2*(Subset.binValOne nil 1) := by simp_arith
