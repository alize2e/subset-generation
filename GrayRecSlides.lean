import «Subsets».SubsetDef

def Subset.helpGRS (n : Nat) (parity : Bool) : List (Subset n) :=
  match n with
  | 0 => [nil]
  | n'+1 => ((helpGRS n' false).map (cons parity)) ++ ((helpGRS n' true).map (cons ¬parity))

def Subset.grayRecSlides (n : Nat) : List (Subset n) := helpGRS n false

#eval Subset.grayRecSlides 3

theorem Subset.in_helpGRS {n : Nat} {s : Subset n} : ∀ parity : Bool, s ∈ helpGRS n parity := by
  induction s with
  | nil =>
    intro parity
    have : helpGRS 0 parity = [nil] := by rfl
    simp [this]
  | cons b bs ih =>
    intro parity
    have : helpGRS (cons b bs).card parity = ((helpGRS bs.card false).map (cons parity)) ++ ((helpGRS bs.card true).map (cons ¬parity)) := by rfl
    rw [this]
    have hor : (cons b bs ∈ (helpGRS (card bs) false).map (cons parity)) ∨ (cons b bs ∈ (helpGRS (card bs) true).map (cons (decide ¬parity = true))) := by
      cases b <;> cases parity <;> simp [ih]
    cases hor
    . have hleft : cons b bs ∈ (helpGRS (card bs) false).map (cons parity) := by assumption
      simp [List.mem_append_of_mem_left, hleft]
    . have hright : cons b bs ∈ (helpGRS (card bs) true).map (cons (decide ¬parity = true)) := by assumption
      simp at hright
      simp [List.mem_append_of_mem_right, hright]

theorem Subset.in_grayRecSlides {n : Nat} {s : Subset n} : s ∈ grayRecSlides n :=
  have : grayRecSlides n = helpGRS n false := by rfl
  by simp [this, in_helpGRS]
