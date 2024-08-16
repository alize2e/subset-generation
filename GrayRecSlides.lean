import «Subsets».SubsetDef

def Subset.helpGRS {n : Nat} (l : List (Subset n)) (parity : Bool) : List (Subset (n+1)) :=
  match l with
  | [] => []
  | x :: xs => (cons parity x) :: helpGRS xs parity

def Subset.grayRecSlides' (n : Nat) (parity : Bool) : List (Subset n) :=
  match n with
  | 0 => [nil]
  | n'+1 =>
    (helpGRS (grayRecSlides' n' false) parity) ++ (helpGRS (grayRecSlides' n' true) ¬parity)

def Subset.grayRecSlides (n : Nat) : List (Subset n) := grayRecSlides' n false

theorem Subset.in_helpGRS_b {n : Nat} {bs : Subset n} {l : List (Subset n)} : bs ∈ l → (Subset.cons b bs) ∈ helpGRS l b := by
  induction l with
  | nil => nofun
  | cons x xs ih =>
    intro h
    cases h with
    | head =>
      have : helpGRS (bs :: xs) b = (cons b bs) :: helpGRS xs b := by rfl
      simp [this]
    | tail =>
      have h1 : bs ∈ xs := by assumption
      have h2 : cons b bs ∈ helpGRS xs b := by simp [ih, h1]
      have h3 : helpGRS (x :: xs) b = (cons b x) :: helpGRS xs b := by rfl
      simp [h2, h3]

theorem Subset.in_grayRecSlides' {n : Nat} {s : Subset n} : ∀ parity : Bool, s ∈ grayRecSlides' n parity := by
  induction s with
  | nil =>
    intro parity
    have : grayRecSlides' 0 parity = [nil] := by rfl
    simp [this]
  | cons b bs ih =>
    intro parity
    have : grayRecSlides' (cons b bs).card parity = (helpGRS (grayRecSlides' bs.card false) parity) ++ (helpGRS (grayRecSlides' bs.card true) ¬parity) := by rfl
    rw [this]
    have hor : (cons b bs ∈ helpGRS (grayRecSlides' (card bs) false) parity) ∨ (cons b bs ∈ helpGRS (grayRecSlides' (card bs) true) (decide ¬parity = true)) := by
      match b with
      | false =>
        match parity with
        | false => simp [in_helpGRS_b, ih]
        | true => simp [in_helpGRS_b, ih]
      | true =>
        match parity with
        | false => simp [in_helpGRS_b, ih]
        | true => simp [in_helpGRS_b, ih]
    cases hor
    . have hleft : cons b bs ∈ helpGRS (grayRecSlides' (card bs) false) parity := by assumption
      simp [List.mem_append_of_mem_left, hleft]
    . have hright : cons b bs ∈ helpGRS (grayRecSlides' (card bs) true) (decide ¬parity = true) := by assumption
      simp at hright
      simp [List.mem_append_of_mem_right, hright]

theorem Subset.in_grayRecSlides {n : Nat} {s : Subset n} : s ∈ grayRecSlides n :=
  have : grayRecSlides n = grayRecSlides' n false := by rfl
  by simp [this, in_grayRecSlides']
