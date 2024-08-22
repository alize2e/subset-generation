import «Subsets».SubsetDef

def Subset.helpGG {n : Nat} (Γₙ : List (Subset n)) (soFar : List (Subset (n+1))) : List (Subset (n+1)) :=
  match Γₙ with
  | [] => soFar
  | x :: xs => (cons false x) :: helpGG xs ((cons true x) :: soFar)

def Subset.genGray (n : Nat) : List (Subset n) :=
  match n with
  | 0 => [nil]
  | n'+1 => helpGG (genGray n') []

theorem Subset.in_helpGG_false {n : Nat} {bs : Subset n} {l : List (Subset n)} :
  bs ∈ l → ∀ soFar : List (Subset (n+1)), (Subset.cons false bs) ∈ (Subset.helpGG l soFar) := by
    induction l with
    | nil => nofun
    | cons x xs ih =>
      intro h1
      cases h1
      . intro soFar
        have h2 : helpGG (bs::xs) soFar = (cons false bs) :: helpGG xs ((cons true bs) :: soFar) := by rfl
        simp [List.any_cons, h2]
      . have : bs ∈ xs := by assumption
        intro soFar
        have h3 : (cons false bs) ∈ cons false x :: helpGG xs (cons true x :: soFar) := by simp [ih, this]
        have h4 : helpGG (x::xs) soFar = cons false x :: helpGG xs (cons true x :: soFar) := by rfl
        rw [h4]
        apply h3

theorem Subset.in_helpGG_true_IS {n : Nat} {bs : Subset n} {l : List (Subset n)} :
  ∀ soFar : List (Subset (n+1)), (cons true bs) ∈ soFar → ∀ soFar' : List (Subset (n+1)), (cons true bs) ∈ helpGG l (soFar'++soFar) := by
    induction l with
    | nil =>
      intro soFar
      intro h
      intro soFar'
      have : helpGG [] (soFar' ++ soFar) = soFar' ++ soFar := by rfl
      rw [this]
      have : cons true bs ∈ soFar' ++ soFar := by simp [List.mem_append_of_mem_right, h]
      simp [this]
    | cons x xs ih =>
      intro soFar
      intro h
      intro soFar'
      have : helpGG (x::xs) (soFar' ++ soFar) = (cons false x) :: helpGG xs (cons true x :: soFar' ++ soFar) := by rfl
      simp [this]
      have : cons true x :: (soFar' ++ soFar) = (cons true x :: soFar') ++ soFar := by simp
      rw [this]
      have h2 : ∀ soFar'' : List (Subset (n+1)), cons true bs ∈ helpGG xs (soFar'' ++ soFar) := by simp [ih, h]
      let soFar'' : List (Subset (n+1)) := (cons true x) :: soFar'
      have : (cons true x :: soFar') ++ soFar = soFar'' ++ soFar := by rfl
      rw [this]
      simp [h2]

theorem Subset.in_helpGG_true {n : Nat} {bs : Subset n} {l : List (Subset n)} :
  bs ∈ l → ∀ soFar : List (Subset (n+1)), (Subset.cons true bs) ∈ (Subset.helpGG l soFar) := by
    induction l with
    | nil => nofun
    | cons x xs ih =>
      intro h1
      cases h1
      . intro soFar
        have : helpGG (bs::xs) soFar = (cons false bs) :: helpGG xs ((cons true bs) :: soFar) := by rfl
        have : cons true bs ∈ cons true bs :: soFar := by simp
        let soFar' : List (Subset (n+1)) := []
        have h2 : cons true bs ∈ helpGG xs (soFar' ++ cons true bs::soFar) := by simp [in_helpGG_true_IS, this]
        have : helpGG xs (soFar' ++ cons true bs::soFar) = helpGG xs (cons true bs::soFar) := by rfl
        rw [this] at h2
        have h3 : cons true bs ∈ cons false bs :: helpGG xs (cons true bs::soFar) := by simp [h2]
        have : cons false bs :: helpGG xs (cons true bs::soFar) = helpGG (bs :: xs) soFar := by rfl
        rw [this] at h3
        simp [h3]
      . intro soFar
        have : helpGG (x::xs) soFar = (cons false x) :: helpGG xs ((cons true x) :: soFar) := by rfl
        rw [this]
        simp
        have : bs ∈ xs := by assumption
        have : (cons true bs) ∈ helpGG xs (cons true x :: soFar) := by simp [ih, this]
        simp [this]

theorem Subset.in_genGray {n : Nat} {s : Subset n} : s ∈ genGray n := by
  induction s with
  | nil =>
    have : genGray 0 = [nil] := by rfl
    simp [this]
  | cons b bs ih =>
    have : genGray (cons b bs).card = helpGG (genGray bs.card) [] := by rfl
    rw [this]
    cases b with
    | false => simp [in_helpGG_false, ih]
    | true => simp [in_helpGG_true, ih]

theorem Subset.helpGG_num {n : Nat} : ∀ l : List (Subset n),
  ∀ soFar : List (Subset (n+1)), (helpGG l soFar).length = 2*l.length + soFar.length := by
    intro l
    induction l with
    | nil =>
      intro soFar
      calc (helpGG List.nil soFar).length
        _ = soFar.length := by rfl
        _ = 2*List.nil.length + soFar.length := by simp_arith
    | cons x xs ih =>
      intro soFar
      calc (helpGG (x::xs) soFar).length
        _ = ((cons false x) :: (helpGG xs (cons true x :: soFar))).length := by rfl
        _ = 1 + (helpGG xs (cons true x :: soFar)).length := by simp_arith
        _ = 1 + 2*(xs.length) + ((cons true x) :: soFar).length := by simp_arith [ih]
        _ = 2 + 2*(xs.length) + soFar.length := by simp_arith
        _ = 2*(x::xs).length + soFar.length := by simp_arith

theorem Subset.genGray_num {n : Nat} : (genGray n).length = 2^n :=
  by induction n with
  | zero => rfl
  | succ n' ih =>
    calc (genGray n'.succ).length
      _ = (helpGG (genGray n') []).length := by rfl
      _ = 2*(genGray n').length + [].length := by rw [helpGG_num]
      _ = 2*(genGray n').length := by rfl
      _ = 2*(2^n') := by rw [ih]
      _ = 2^n'.succ := by rw [Nat.pow_succ']

theorem Subset.helpGG_symmetry {n : Nat} {l : List (Subset n)} {soFar : List (Subset (n+1))} :
  helpGG l soFar = (l.map (cons false)) ++ List.reverseAux (l.map (cons true)) soFar := by
    induction l generalizing soFar with
    | nil => rfl
    | cons x xs ih =>
      calc helpGG (x::xs) soFar
        _ = (cons false x) :: helpGG xs ((cons true x) :: soFar) := by rfl
        _ = (cons false x) :: (xs.map (cons false)) ++ List.reverseAux (xs.map (cons true)) ((cons true x) :: soFar) := by simp [ih]
        _ = ((x::xs).map (cons false)) ++ List.reverseAux (xs.map (cons true)) ((cons true x) :: soFar) := by rfl
        _ = ((x::xs).map (cons false)) ++ List.reverseAux ((cons true x)::xs.map (cons true)) soFar := by rfl
        _ = ((x::xs).map (cons false)) ++ List.reverseAux ((x::xs).map (cons true)) soFar := by rfl

#eval Subset.genGray 3
