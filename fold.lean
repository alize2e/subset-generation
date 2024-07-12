def foldNat (i : Nat → Nat) (f : Nat → (Nat → Nat) → (Nat → Nat)) (m : Nat) (n : Nat) : Nat :=
  match m with
  | Nat.zero => i n
  | Nat.succ m' => f n (foldNat i f m') n

def iₐ (n : Nat) : Nat := n
def fₐ (_ : Nat) (g : Nat → Nat) : Nat → Nat := Nat.succ∘g
def add (m : Nat) : Nat → Nat := foldNat iₐ fₐ m

theorem approx_add_correct {n m : Nat} : add m n = m + n := by
  induction m with
  | zero =>
    calc add 0 n
      _ = foldNat iₐ fₐ 0 n := by rfl
      _ = iₐ n := by rfl
      _ = n := by rfl
      _ = 0 + n := by simp_arith
  | succ m' ih =>
    calc add m'.succ n
      _ = fₐ m' (foldNat iₐ fₐ m') n := by rfl
      _ = fₐ m' (add m') n := by rfl
      _ = (Nat.succ∘(add m')) n := by rfl
      _ = Nat.succ (add m' n) := by rfl
      _ = Nat.succ (m' + n) := by rw [ih]
      _ = m' + n + 1 := by rfl
      _ = (m'+1) + n := by simp_arith

theorem add_correct : add = HAdd.hAdd := by
  funext m
  funext n
  simp [approx_add_correct]

def iₘ (_ : Nat) : Nat := Nat.zero
def fₘ (m : Nat) (g : Nat → Nat) (n : Nat) : Nat := add m (g n)
def mul (m : Nat) : Nat → Nat := foldNat iₘ fₘ m

theorem approx_mul_correct {n m : Nat} : mul m n = m * n := by
  induction m with
  | zero =>
    calc mul 0 n
      _ = foldNat iₘ fₘ 0 n := by rfl
      _ = iₘ n := by rfl
      _ = 0 := by rfl
      _ = 0 * n := by simp_arith
  | succ m' ih =>
    calc mul m'.succ n
      _ = fₘ n (foldNat iₘ fₘ m') n := by rfl
      _ = fₘ n (mul m') n := by rfl
      _ = add n (mul m' n) := by rfl
      _ = add n (m'*n) := by rw [ih]
      _ = n + (m'*n) := by rw [approx_add_correct]
      _ = m'.succ * n := by simp_arith [Nat.succ_mul]

theorem mul_correct : mul = HMul.hMul := by
  funext m
  funext n
  simp [approx_mul_correct]

#eval mul 3 7
