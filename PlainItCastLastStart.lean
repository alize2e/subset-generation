-- soFar is (cast of) lastStart ++

import «Subsets».SubsetBinVal

def Subset.genIt (n : Nat) : List (Subset n) :=
  let rec help {l r : Nat} (xsl : Subset l) (xsr : Subset r) (soFar : List (Subset n))
    (sum_l_r_n : l+r=n) (zeros : xsl.binValOne 0 = 0) (nel : soFar.length>0) (lastStart : Subset l)
    (last_eq : soFar[0] = lastStart.append xsr) : List (Subset n) :=
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
            have l_lt_n : l<n :=
              calc l
                _ < l+1 := by simp
                _ = l+(cons x nil).card := by simp
                _ ≤ l+((cons x nil).card + xsr'.card) := by simp_arith
                _ = l+((cons x nil).append xsr').card := by simp [append_card]
                _ = n := by simp [sum_l_r_n]
            let lastStart' := lastStart.append (cons (soFar[0].toFun (l.toFin n l_lt_n)) nil)
            have card_last' : (lastStart'.append xsr').card = n :=
              calc (lastStart'.append xsr').card
                _ = lastStart'.card + xsr'.card := by simp [append_card]
                _ = (lastStart.append (cons (soFar[0].toFun (l.toFin n l_lt_n)) nil)).card + xsr'.card := by rfl
                _ = lastStart.card + 1 + xsr'.card := by simp [append_card]
                _ = xsl.card + 1 + xsr'.card := by simp
                _ = xsl'.card + xsr'.card := by simp
                _ = n := by simp [sum_l'_r'_n]
            have card_last : n = (lastStart.append (cons x xsr')).card := by simp_arith [sum_l_r_n, Nat.add_comm]
            have card_int : ((lastStart.append (cons x nil)).append xsr').card = n :=
            have last_eq' : soFar[0] = lastStart'.append xsr' := sorry
              -- calc soFar[0]
              --   _ = lastStart.append (cons x xsr') := by rw [last_eq]
              --   _ = (lastStart.append (cons x nil)).append xsr' := by rfl
            help xsl' xsr' soFar sum_l'_r'_n zeros' nel lastStart last_eq'
          else
            let xs := Subset.append xsl (Subset.cons true xsr')
            have xs_len_eq_n : xs.card = n :=
              calc xs.card
                _ = (Subset.append xsl (Subset.cons true xsr')).card := by rfl
                _ = xsl.card + (Subset.cons true xsr').card := by rw [append_card]
                _ = n := by rw [sum_l_r_n]
            have sum_l'_r'_n :  Subset.nil.card + xs.card = n := by simp_arith [xs_len_eq_n]
            have d2 : (Subset.cast (by simp[xs_len_eq_n]) xs : Subset n).binValOne 1 < soFar[0].binValOne 1 := sorry
            help Subset.nil xs ((Subset.cast (by simp [xs_len_eq_n]) xs) :: soFar) sum_l'_r'_n rfl (by simp [nel]) Subset.nil rfl
      termination_by (soFar[0].binValOne 1, binVal xsl xsr 0)
      -- xsl'++xsr' = incr xsl++xsn (where lsb is left)

  let init := initFalse n
  help Subset.nil init ([init]) (by simp_arith) rfl (by simp) Subset.nil rfl

#eval Subset.genIt 3

-- def s := Subset.cons false (Subset.cons true (Subset.cons true Subset.nil))
#eval s.append (Subset.cons false Subset.nil)
#eval 2^s.card
#eval Subset.binVal s s 0
#eval Subset.append s s
#eval Subset.binVal s s 1


-- #eval Functor.map (Subset.binVal Subset.nil 1) (Subset.genIt 3)
example {n : Nat} {s : Subset n} : 0<2^s.card := by simp_arith [Nat.two_pow_pos]
