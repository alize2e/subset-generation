import «Subsets».SubsetIsoFun

def Subset.binVal {l r : Nat} (xsl : Subset l) (xsr : Subset r) (opp : Fin 2) : Nat :=
  match xsl, xsr with
  | cons l xsl', xsr => (if l then 1-opp else opp) + 2*(Subset.binVal xsl' xsr opp)
  | nil, cons r xsr' => (if r then 1-opp else opp) + 2*(Subset.binVal nil xsr' opp)
  | nil, nil => 0

def Subset.binValOne {n : Nat} (s : Subset n) (opp : Fin 2) : Nat :=
  match s with
  | nil => 0
  | cons b s' => (if b then 1-opp else opp) + 2*(Subset.binValOne s' opp)

theorem Subset.binVal_append {l r : Nat} {sl : Subset l} {sr : Subset r} {opp : Fin 2} :
  Subset.binVal sl sr opp = (Subset.append sl sr).binValOne opp := by
    induction sl with
    | nil =>
      induction sr with
      | nil => rfl
      | cons r sr' ihr =>
        calc Subset.binVal Subset.nil (Subset.cons r sr') opp
          _ = (if r then 1-opp else opp) + 2*(Subset.binVal Subset.nil sr' opp) := by rfl
          _ = (if r then 1-opp else opp) + (2*(Subset.append Subset.nil sr').binValOne opp) := by rw [ihr]
    | cons l sl' ihl =>
      calc Subset.binVal (Subset.cons l sl') sr opp
        _ = (if l then 1-opp else opp) + 2*(Subset.binVal sl' sr opp) := by simp [Subset.binVal]
        _ = (if l then 1-opp else opp) + 2*(Subset.append sl' sr).binValOne opp := by rw [ihl]

theorem Subset.binVal_power {l r : Nat} {xsl : Subset l} {xsr : Subset r} {opp : Fin 2} :
  Subset.binVal xsl xsr opp = (xsl.binValOne opp) + 2^xsl.card*(xsr.binValOne opp) := by
    induction xsl with
    | nil =>
      calc Subset.binVal Subset.nil xsr opp
        _ = (Subset.append Subset.nil xsr).binValOne opp := by rw [binVal_append]
        _ = xsr.binValOne opp := by rfl
        _ = 0 + 2^0*(xsr.binValOne opp) := by simp_arith
        _ = (Subset.nil.binValOne opp) + 2^0*(xsr.binValOne opp) := by rfl
    | cons l xsl' ih =>
      calc Subset.binVal (Subset.cons l xsl') xsr opp
        _ = (if l then 1-opp else opp) + 2*(Subset.binVal xsl' xsr opp) := by simp [Subset.binVal]
        _ = (if l then 1-opp else opp) + 2*(xsl'.binValOne opp + 2^(xsl'.card)*(xsr.binValOne opp)) := by rw [ih]
        _ = (if l then 1-opp else opp) + 2*xsl'.binValOne opp + 2*(2^(xsl'.card)*(xsr.binValOne opp)) := by simp_arith [Nat.left_distrib]
        _ = (if l then 1-opp else opp) + 2*xsl'.binValOne opp + (2^(xsl'.card)*2)*(xsr.binValOne opp) := by simp_arith [Nat.mul_assoc, Nat.mul_comm]
        _ = (if l then 1-opp else opp) + 2*xsl'.binValOne opp + 2^(xsl'.card+1)*(xsr.binValOne opp) := by simp_arith [Nat.pow_succ]
        _ = (Subset.cons l xsl').binValOne opp + 2^(xsl'.card+1)*xsr.binValOne opp := by rfl

theorem Subset.dec1 {l r' : Nat} (xsl : Subset l) (x : Bool) (xsr' : Subset r')
  (zeros : xsl.binValOne 0 = 0) (h : x=true) (xsl' : Subset (l+1)) (xsl'_def : xsl' = cons false xsl):
    binVal xsl' xsr' 0 < binVal xsl (cons x xsr') 0 :=
      calc binVal xsl' xsr' 0
        _ = binVal (cons false xsl) xsr' 0 := by rw [xsl'_def]
        _ = (if false then 1-0 else 0) + 2*(binVal xsl xsr' 0) := by simp [binVal]
        _ = 2*(binVal xsl xsr' 0) := by simp
        _ = 2*((xsl.binValOne 0) + 2^xsl.card*(xsr'.binValOne 0)) := by rw [binVal_power]
        _ = 2*(2^xsl.card*(xsr'.binValOne 0)) + 0 := by simp_arith [zeros]
        _ = (2^xsl.card*2)*(xsr'.binValOne 0) := by simp_arith [Nat.mul_assoc, Nat.mul_comm]
        _ = (2^xsl.card)*(2*(xsr'.binValOne 0)) + 0 := by simp_arith [Nat.mul_assoc]
        _ < (2^xsl.card)*(2*(xsr'.binValOne 0)) + 1 := by simp_arith
        _ ≤ (2^xsl.card)*(2*(xsr'.binValOne 0)) + 2^xsl.card := by simp_arith [Nat.one_le_two_pow]
        _ = 2^xsl.card*((2*xsr'.binValOne 0) + 1) := by rw [Nat.mul_succ]
        _ = 2^xsl.card*((2*xsr'.binValOne 0) + (if true then 1-0 else 0 : Fin 2)) := by rfl
        _ = 2^xsl.card*((2*xsr'.binValOne 0) + (if x then 1-0 else 0 : Fin 2)) := by rw [h]
        _ = 2^xsl.card*((if x then 1-0 else 0 : Fin 2) + 2*(xsr'.binValOne 0)) := by simp_arith [Nat.add_comm]
        _ = 2^xsl.card*((cons x xsr').binValOne 0) := by simp [binValOne]
        _ = (xsl.binValOne 0) + 2^xsl.card*((cons x xsr').binValOne 0) := by simp_arith [zeros]
        _ = binVal xsl (cons x xsr') 0 := by simp [binVal_power]

theorem Subset.binVal_msb {n : Nat} :
  ((initTrue n).append (cons false nil)).binValOne 1 = 1 + ((initFalse n).append (cons true nil)).binValOne 1 := by
    induction n with
    | zero =>
      calc ((initTrue 0).append (cons false nil)).binValOne 1
        _ = (nil.append (cons false nil)).binValOne 1 := by rfl
        _ = (cons false nil).binValOne 1 := by rfl
        _ = (if false then 1-1 else 1) + 2*(binValOne nil 1) := by rfl
        _ = 1 + 2*(Subset.binValOne nil 1) := by simp
        _ = 1 + 2*(Subset.binValOne nil 1) := by simp_arith
        _ = 1 + (if true then 1-1 else 1) + 2*(binValOne nil 1) := by rfl
        _ = 1 + (cons true nil).binValOne 1 := by rfl
        _ = 1 + (nil.append (cons true nil)).binValOne 1 := by rfl
    | succ n' ih =>
      calc ((initTrue n'.succ).append (cons false nil)).binValOne 1
        _ = ((cons true (initTrue n')).append (cons false nil)).binValOne 1 := by rfl
        _ = (cons true ((initTrue n').append (cons false nil))).binValOne 1 := by rfl
        _ = (if true then 1-1 else 1) + 2*(((initTrue n').append (cons false nil)).binValOne 1) := by rfl
        _ = 2*(((initTrue n').append (cons false nil)).binValOne 1) := by simp
        _ = 2*(1 + ((initFalse n').append (cons true nil)).binValOne 1) := by simp [ih]
        _ = 2 + 2*((initFalse n').append (cons true nil)).binValOne 1 := by simp_arith
        _ = 1 + ((if false then 1-1 else 1) + 2*((initFalse n').append (cons true nil)).binValOne 1) := by simp_arith
        _ = 1 + (cons false ((initFalse n').append (cons true nil))).binValOne 1 := by rfl

theorem Subset.binVal1_max {n : Nat} {s : Subset n} : s.binValOne 1 ≤ (initFalse n).binValOne 1 := by
  induction s with
  | nil =>
    calc nil.binValOne 1
      _ = (initFalse 0).binValOne 1 := by rfl
      _ ≤ (initFalse 0).binValOne 1 := by simp
  | cons b bs ih =>
    have h : (if b then 1-1 else 1) ≤ 1 :=
      match b with
      | true => by simp_arith
      | false => by simp_arith
    match b with
    | true =>
      calc Subset.binValOne (Subset.cons true bs) 1
        _ = (if true then 1-1 else 1) + 2*(Subset.binValOne bs 1) := by rfl -- WHY NO RFL
        _ ≤ 1 + 2*(Subset.binValOne bs 1) := by simp_arith [h, Nat.add_le_add_left]
        _ ≤ 1 + 2*(binValOne bs 1) := by simp [h, Nat.add_le_add_right]
        _ ≤ 1 + 2*(binValOne (initFalse bs.card) 1) := by simp [ih, Nat.mul_le_mul_left, Nat.add_le_add_left]
    | false =>
      calc Subset.binValOne (Subset.cons false bs) 1
        _ = (if false then 1-1 else 1) + 2*(Subset.binValOne bs 1) := by rfl -- WHY NO RFL
        _ ≤ 1 + 2*(binValOne bs 1) := by simp [h, Nat.add_le_add_right]
        _ ≤ 1 + 2*(binValOne (initFalse bs.card) 1) := by simp [ih, Nat.mul_le_mul_left, Nat.add_le_add_left]
