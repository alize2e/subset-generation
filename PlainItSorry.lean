-- usable with sorry for d2

import «Subsets».SubsetBinVal

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

#eval Subset.genIt 3

#eval 2^s.card
#eval Subset.binVal s s 0
#eval Subset.append s s
#eval Subset.binVal s s 1

#eval List.map (λ s : Subset 3 => Subset.binValOne s 1) (Subset.genIt 3)
example {n : Nat} {s : Subset n} : 0<2^s.card := by simp_arith [Nat.two_pow_pos]
