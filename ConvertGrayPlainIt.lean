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

--  -- wrong order of traversal -- correction below
-- def Subset.ψ' {n : Nat} (last : Bool) : Subset n → Subset n
--   | nil => nil
--   | cons b p' => cons (xor b last) (ψ' b p')
-- def Subset.ψ {n : Nat} (p : Subset n) : Subset n := ψ' false p
-- def Subset.φ' {n : Nat} (parity : Bool) : Subset n → Subset n
--   | nil => nil
--   | cons b g' => cons (xor b parity) (φ' (xor b parity) g')
-- def Subset.φ {n : Nat} (g : Subset n) : Subset n := φ' false g

def Subset.ψ {n : Nat} : Subset n → Subset n
  | nil => nil
  | cons b nil => cons b nil
  | cons curr (cons prev rest) => cons (xor curr prev) (ψ (cons prev rest))

def Subset.φ' {n : Nat} : Subset n → Bool × Subset n
  | nil => (false, nil)
  | cons b g' => (xor b (φ' g').fst, cons (xor b (φ' g').fst) (φ' g').snd)

def Subset.φ {n : Nat} (g : Subset n) : Subset n := (φ' g).snd

def Subset.prev {n : Nat} (g : Subset n.succ) : Bool :=
  match g with
  | cons b _ => b

theorem Subset.t1 {n : Nat} {b : Bool} {g : Subset n} : (φ' (cons b g)).fst = (φ' (cons b g)).snd.prev := by rfl

-- theorem Subset.t2 {n : Nat} {b : Bool} {ph : Bool} {p : Subset n} {ih : (φ∘ψ) (cons ph p) = cons ph p} :
--   (xor (xor b ph) (φ' (ψ (cons ph p))).fst) = b := by
--     match p with
--     | nil =>
--       calc (xor (xor b ph) (φ' (ψ (cons ph nil))).fst)
--         _ = xor (xor b ph) (φ' (cons ph nil)).fst := by rfl
--         _ = xor (xor b ph) (xor ph (φ' nil).fst, cons (xor ph (φ' nil).fst) (φ' nil).snd).fst := by rfl
--         _ = xor (xor b ph) (xor ph (φ' nil).fst) := by rfl
--         _ = xor (xor b ph) (xor ph (false, nil).fst) := by rfl
--         _ = xor (xor b ph) (xor ph false) := by rfl
--         _ = xor (xor b ph) ph := by rw [Bool.xor_false]
--         _ = xor b (xor ph ph) := by rw [Bool.xor_assoc]
--         _ = xor b false := by rw [Bool.xor_self]
--         _ = b := by rw [Bool.xor_false]
--     | cons ph' p' =>
--       calc xor (xor b ph) (φ' (ψ (cons ph (cons ph' p')))).fst
--         _ = xor (xor b ph) (φ' (cons (xor ph ph') (ψ (cons ph' p')))).fst := by rfl
--         _ = xor (xor b ph) (xor (xor ph ph') (φ' (ψ (cons ph' p'))).fst, cons (xor (xor ph ph') (φ' (ψ (cons ph' p'))).fst) (φ' (ψ (cons ph' p'))).snd).fst := by rfl
--         _ = xor (xor b ph) (xor (xor ph ph') (φ' (ψ (cons ph' p'))).fst) := by rfl
--         -- NEED INDUCTION? BUT THEN WOULD NEED TO RESTRUCTURE
--         -- _ = xor (xor b ph) (xor (xor ph ph') (φ (ψ (cons ph' p'))).snd.prev) := by rfl

-- theorem Subset.ISp {n : Nat} {b : Bool} {ph : Bool} {p : Subset n} {ih : (φ∘ψ) (cons ph p) = cons ph p} :
--   (φ∘ψ) (cons b (cons ph p)) = cons b (cons ph p) := by
--     calc (φ∘ψ) (cons b (cons ph p))
--       _ = φ (ψ (cons b (cons ph p))) := by rfl
--       _ = φ (cons (xor b ph) (ψ (cons ph p))) := by rfl
--       _ = (φ' (cons (xor b ph) (ψ (cons ph p)))).snd := by rfl
--       _ = ((xor (xor b ph) (φ' (ψ (cons ph p))).fst, cons (xor (xor b ph) (φ' (ψ (cons ph p))).fst) (φ' (ψ (cons ph p))).snd)).snd := by rfl
--       _ = cons (xor (xor b ph) (φ' (ψ (cons ph p))).fst) (φ' (ψ (cons ph p))).snd := by rfl
--       _ = cons (xor (xor b ph) (φ' (ψ (cons ph p))).fst) (φ' (ψ (cons ph p))).snd := by rfl
--       _ = cons (xor (xor b ph) (φ' (ψ (cons ph p))).fst) ((φ∘ψ) (cons ph p)) := by rfl
--       _ = cons (xor (xor b ph) (φ' (ψ (cons ph p))).fst) (cons ph p) := by rw [ih]
--       -- but how to finish? WTS (xor (xor b ph) (φ' (ψ (cons ph p))).fst) = b

#eval Subset.genIt 3
#eval Subset.grayIt 3

#eval (Subset.genIt 4).map Subset.ψ == Subset.grayIt 4
#eval (Subset.grayIt 3).map Subset.φ == Subset.genIt 3

#eval Subset.cons false (Subset.cons true (Subset.cons true Subset.nil))

theorem Subset.BC0p : (φ∘ψ) nil = nil := rfl
theorem Subset.BC1p {b : Bool} : (φ∘ψ) (cons b nil) = (cons b nil) := by
  calc (φ∘ψ) (cons b nil)
    _ = φ (ψ (cons b nil)) := by rfl
    _ = φ (cons b nil) := by rfl
    _ = (φ' (cons b nil)).snd := by rfl
    _ = (xor b (φ' nil).fst, cons (xor b (φ' nil).fst) (φ' nil).snd).snd := by rfl
    _ = (xor b false, cons (xor b false) nil).snd := by rfl
    _ = (b, cons b nil).snd := by simp
    _ = cons b nil := by rfl

theorem Subset.BC0g : (ψ∘φ) nil = nil := rfl
theorem Subset.BC1g {b : Bool} : (ψ∘φ) (cons b nil) = (cons b nil) := by
  calc (ψ∘φ) (cons b nil)
    _ = ψ (φ (cons b nil)) := by rfl
    _ = ψ (φ' (cons b nil)).snd := by rfl
    _ = ψ (xor b (φ' nil).fst, cons (xor b (φ' nil).fst) (φ' nil).snd).snd := by rfl
    _ = ψ (xor b false, cons (xor b false) nil).snd := by rfl
    _ = ψ (b, cons b nil).snd := by simp
    _ = ψ (cons b nil) := by rfl
    _ = cons b nil := by rfl
theorem Subset.ISg {n : Nat} {b : Bool} {gh : Bool} {g : Subset n} {ih : (ψ∘φ) (cons gh g) = cons gh g} :
  (ψ∘φ) (cons b (cons gh g)) = cons b (cons gh g) := by
    calc (ψ ∘ φ) (cons b (cons gh g))
      _ = ψ (φ (cons b (cons gh g))) := by rfl
      _ = ψ (φ' (cons b (cons gh g))).snd := by rfl
      _ = ψ (xor b (φ' (cons gh g)).fst, cons (xor b (φ' (cons gh g)).fst) (φ' (cons gh g)).snd).snd := by rfl
      _ = ψ (cons (xor b (φ' (cons gh g)).fst) (φ' (cons gh g)).snd) := by rfl
      _ = ψ (cons (xor b (φ' (cons gh g)).snd.prev) (φ' (cons gh g)).snd) := by rfl
      _ = ψ (cons (xor b ((xor gh (φ' g).fst, cons (xor gh (φ' g).fst) (φ' g).snd)).snd.prev) ((xor gh (φ' g).fst, cons (xor gh (φ' g).fst) (φ' g).snd)).snd) := by rfl
      _ = ψ (cons (xor b (cons (xor gh (φ' g).fst) (φ' g).snd).prev) (cons (xor gh (φ' g).fst) (φ' g).snd)) := by rfl
      _ = ψ (cons (xor b (xor gh (φ' g).fst)) (cons (xor gh (φ' g).fst) (φ' g).snd)) := by rfl
      _ = cons (xor (xor b (xor gh (φ' g).fst)) (xor gh (φ' g).fst)) (ψ (cons (xor gh (φ' g).fst) (φ' g).snd)) := by rfl
      _ = cons (xor b (xor (xor gh (φ' g).fst) (xor gh (φ' g).fst))) (ψ (cons (xor gh (φ' g).fst) (φ' g).snd)) := by rw [Bool.xor_assoc]
      _ = cons (xor b false) (ψ (cons (xor gh (φ' g).fst) (φ' g).snd)) := by rw [Bool.xor_self]
      _ = cons b (ψ (cons (xor gh (φ' g).fst) (φ' g).snd)) := by rw [Bool.xor_false]
      _ = cons b (ψ (((xor gh (φ' g).fst, cons (xor gh (φ' g).fst) (φ' g).snd)).snd)) := by rfl
      _ = cons b (ψ (φ' (cons gh g)).snd) := by rfl
      _ = cons b (ψ (φ (cons gh g))) := by rfl
      _ = cons b ((ψ∘φ) (cons gh g)) := by rfl
      _ = cons b (cons gh g) := by rw [ih]

-- theorem Subset.ψ_φ_id {n : Nat} (g : Subset n) : (ψ∘φ) g = g := by
  -- induction g with
  -- | nil => rfl
  -- | cons b nil ih =>
  --   calc (ψ∘φ) (cons b nil)
  --     _ = cons b nil := by rw [BC1g]
  -- | cons b g' ih' =>
  --   simp

-- theorem ψ_φ_id {n : Nat} (g : Subset n) : (Subset.ψ∘Subset.φ) g = g := by
--   induction g with
--   | nil => rfl
--   | cons b Subset.nil ih =>
--     calc (Subset.ψ∘Subset.φ) (Subset.cons b Subset.nil)
--       _ = (Subset.cons b Subset.nil) := by simp [Subset.BC1g b]
--   | cons b g' ih' =>
--     simp
