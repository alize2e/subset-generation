import Subsets.GrayIt

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
      | nil => simp only [binVal, binValOne]
      | cons r sr' ihr =>
        calc Subset.binVal Subset.nil (Subset.cons r sr') opp
          _ = (if r then 1-opp else opp) + 2*(Subset.binVal Subset.nil sr' opp) := by simp only [binVal]
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

def Subset.genIt (n : Nat) : List (Subset n) :=
  let rec help {l r : Nat} (xsl : Subset l) (xsr : Subset r) (soFar : List (Subset n))
    (sum_l_r_n : l+r=n) (zeros : xsl.binValOne 0 = 0) (nel : soFar.length>0) : List (Subset n) :=
      match xsr with
      | Subset.nil => soFar
      | Subset.cons x xsr' =>
          if h:x then -- xsl is all 0s
            let xsl' := Subset.cons false xsl
            have sum_l'_r'_n : xsl'.card + xsr'.card = n := by
              calc xsl'.card + xsr'.card
                _ = xsl.card + 1 + xsr'.card := by rfl
                _ = xsl.card + xsr'.card + 1 := by simp_arith
                _ = xsl.card + (Subset.cons x xsr').card := by rfl
                _ = n := by rw [sum_l_r_n]
            have d1 : binVal xsl' xsr' 0 < binVal xsl (cons x xsr') 0 :=
              by simp [dec1 xsl x xsr' zeros h xsl']
            have zeros' : xsl'.binValOne 0 = 0 :=
              calc xsl'.binValOne 0
                _ = (cons false xsl).binValOne 0 := rfl
                _ = (if false then 1 else 0) + 2*xsl.binValOne 0 := by simp [binValOne]
                _ = 0 := by simp [zeros]
            help xsl' xsr' soFar sum_l'_r'_n zeros' nel
          else
            let xs := Subset.append xsl (Subset.cons true xsr')
            have xs_len_eq_n : xs.card = n :=
              calc xs.card
                _ = (Subset.append xsl (Subset.cons true xsr')).card := by rfl
                _ = xsl.card + (Subset.cons true xsr').card := by rw [append_card]
                _ = n := by rw [sum_l_r_n]
            have sum_l'_r'_n :  Subset.nil.card + xs.card = n := by simp_arith [xs_len_eq_n]
            -- have : xs.binValOne 1 < soFar[0].binValOne 1 := sorry
            have d2 : (Subset.cast (by simp[xs_len_eq_n]) xs : Subset n).binValOne 1 < soFar[0].binValOne 1 := sorry
            help Subset.nil (xs) ((Subset.cast (by simp [xs_len_eq_n]) xs) :: soFar) sum_l'_r'_n rfl (by simp [nel])
      termination_by (soFar[0].binValOne 1, binVal xsl xsr 0)
      -- xsl'++xsr' = incr xsl++xsn (where lsb is left)

  let init := initFalse n
  help Subset.nil init ([init]) (by simp_arith) rfl (by simp)

def Subset.start' {n : Nat} (g : Subset n) : Bool :=
  match g with
  | nil => false
  | cons b _ => b

def Subset.ψ {n : Nat} : Subset n → Subset n
  | nil => nil
  | cons curr rest => cons (xor curr rest.start') (ψ rest)

def Subset.φ {n : Nat} : Subset n → Subset n
  | nil => nil
  | cons curr rest => cons (xor curr (φ rest).start') (φ rest)

#eval! (Subset.genIt 4).map Subset.ψ == Subset.grayIt 4
#eval! (Subset.grayIt 3).map Subset.φ == Subset.genIt 3

theorem Subset.ψ_φ_id {n : Nat} {gray : Subset n} : (ψ∘φ) gray = gray := by
  induction gray with
  | nil => rfl
  | cons b g' ih =>
    calc (ψ ∘ φ) (cons b g')
      _ = ψ (φ (cons b g')) := by rfl
      _ = ψ (cons (xor b (φ g').start') (φ g')) := by rfl
      _ = cons (xor (xor b (φ g').start') (φ g').start') (ψ (φ g')) := by rfl
      _ = cons (xor b (xor (φ g').start' (φ g').start')) (ψ (φ g')) := by rw [Bool.xor_assoc]
      _ = cons (xor b false) (ψ (φ g')) := by rw [Bool.xor_self]
      _ = cons b (ψ (φ g')) := by rw [Bool.xor_false]
      _ = cons b ((ψ∘φ) g') := by rfl
      _ = cons b g' := by rw [ih]

theorem Subset.φ_ψ_id {n : Nat} {plain : Subset n} : (φ∘ψ) plain = plain := by
  induction plain with
  | nil => rfl
  | cons b p' ih =>
    calc (φ∘ψ) (cons b p')
      _ = φ (ψ (cons b p')) := by rfl
      _ = φ (cons (xor b p'.start') (ψ p')) := by rfl
      _ = cons (xor (xor b p'.start') (φ (ψ p')).start') (φ (ψ p')) := by rfl
      _ = cons (xor (xor b p'.start') (((φ∘ψ) p')).start') (((φ∘ψ) p')) := by rfl
      _ = cons (xor (xor b p'.start') p'.start') p' := by rw [ih]
      _ = cons (xor b (xor p'.start' p'.start')) p' := by rw [Bool.xor_assoc]
      _ = cons (xor b false) p' := by rw [Bool.xor_self]
      _ = cons b p' := by rw [Bool.xor_false]
