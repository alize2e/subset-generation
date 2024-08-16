import Subsets.PlainItSorry

def Subset.grayVal {m : Nat} (times : Nat) : Subset m → Nat × Bool
  | nil => (0, false)
  | cons b bs =>
    match grayVal (2*times) bs with
    | (val, parity) =>
      let delta := if b.xor parity then 0 else 1
      (val + times*delta, b.xor parity)

def Subset.minLeft1? {n : Nat} : Subset n → Option (Subset n)
  | nil => none
  | cons true (cons b bs) => some (cons true (cons (¬b) bs))
  | cons b bs =>
    let out := minLeft1? bs
    match out with
    | none => none
    | some next => some (cons b next)

def Subset.helpGrayIt {m : Nat} (parity : Bool) (soFar : List (Subset m.succ))
  (ok : soFar.length>0) : List (Subset m.succ) :=
    match soFar with
    | a :: xs =>
      match parity with
      | true =>
        match a with
        | cons a₀ as =>
          let a' := cons (¬ a₀) as
          have : (grayVal 1 (cons (!a₀) as)).fst < (grayVal 1 (cons a₀ as)).fst := sorry
          helpGrayIt (¬ parity) (a' :: soFar) (by simp [ok])
      | false =>
        let out := minLeft1? a
        match out with
        | none => soFar
        | some next =>
          have : (grayVal 1 next).fst < (grayVal 1 a).fst := sorry
          helpGrayIt (¬ parity) (next :: soFar) (by simp [ok])
      termination_by (soFar[0].grayVal 1).fst

def Subset.grayIt (n : Nat) : List (Subset n) :=
  match n with
  | 0 => [nil]
  | m+1 =>
    let init := initFalse m.succ
    helpGrayIt true [init] (by simp)

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

#eval (Subset.genIt 4).map Subset.ψ == Subset.grayIt 4
#eval (Subset.grayIt 3).map Subset.φ == Subset.genIt 3

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

theorem Subset.φ_ψ_id {n : Nat} {gray : Subset n} : (φ∘ψ) plain = plain := by
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
