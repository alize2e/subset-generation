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

theorem Subset.helpGRS_parity_reverse {n : Nat} : (helpGRS n false).reverse = helpGRS n true := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    calc (helpGRS n'.succ false).reverse
      _ = (((helpGRS n' false).map (cons false)) ++ ((helpGRS n' true).map (cons true))).reverse := by rfl
      _ = ((helpGRS n' true).map (cons true)).reverse ++ ((helpGRS n' false).map (cons false)).reverse := by simp
      _ = ((helpGRS n' true).reverse.map (cons true)) ++ ((helpGRS n' false).reverse.map (cons false)) := by simp [List.map_reverse]
      _ = ((helpGRS n' false).reverse.reverse.map (cons true)) ++ ((helpGRS n' true).map (cons false)) := by rw [ih]
      _ = ((helpGRS n' false).map (cons true)) ++ ((helpGRS n' true).map (cons false)) := by simp
      _ = helpGRS n'.succ true := by rfl

theorem Subset.grayRecSlides_IS (n' : Nat) : grayRecSlides n'.succ = ((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)) :=
  calc grayRecSlides n'.succ
    _ = helpGRS n'.succ false := by rfl
    _ = ((helpGRS n' false).map (cons false)) ++ ((helpGRS n' true).map (cons ¬false)) := by rfl
    _ = ((helpGRS n' false).map (cons false)) ++ ((helpGRS n' false).reverse.map (cons ¬false)) := by rw [helpGRS_parity_reverse]
    _ = ((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true)) := by rfl

theorem Subset.grayRecSlides_num {n : Nat} : (grayRecSlides n).length = 2^n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    calc (grayRecSlides n'.succ).length
      _ = (((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons true))).length := by rw [grayRecSlides_IS n']
      _ = ((grayRecSlides n').map (cons false)).length + ((grayRecSlides n').reverse.map (cons true)).length := by simp
      _ = (grayRecSlides n').length + (grayRecSlides n').reverse.length := by simp
      _ = (grayRecSlides n').length + (grayRecSlides n').length := by simp
      _ = 2*(grayRecSlides n').length := by simp_arith
      _ = 2*2^n' := by rw [ih]
      _ = 2^n'.succ := by rw [Nat.pow_succ']

def Subset.xor_11 {n : Nat} : Subset n → Subset n
  | nil => nil
  | cons b nil => cons (!b) nil
  | cons b (cons b' bs) => cons (!b) (cons (!b') bs)

theorem Subset.grayRecSlides_xor11 {n : Nat} : ((grayRecSlides n).map (cons false)) ++ ((grayRecSlides n).map (cons false)).map xor_11 = grayRecSlides n.succ := by
  induction n with
  | zero => rfl
  | succ n' _ =>
    calc ((grayRecSlides n'.succ).map (cons false)) ++ ((grayRecSlides n'.succ).map (cons false)).map xor_11
      _ = ((helpGRS n'.succ false).map (cons false)) ++ ((((helpGRS n' false).map (cons false)) ++ ((helpGRS n' true).map (cons true))).map (cons false)).map xor_11 := by rfl
      _ = ((helpGRS n'.succ false).map (cons false)) ++ ((((helpGRS n' false).map (xor_11 ∘ cons false ∘ cons false)) ++ ((helpGRS n' true).map (xor_11 ∘ cons false ∘ cons true)))) := by simp only [List.map_map, List.map_append]
      _ = ((helpGRS n'.succ false).map (cons false)) ++ ((((helpGRS n' false).map (cons true ∘ cons true)) ++ ((helpGRS n' true).map (cons true ∘ cons false)))) := by rfl
      _ = ((helpGRS n'.succ false).map (cons false)) ++ ((((helpGRS n' false).map (cons true)) ++ ((helpGRS n' true).map (cons false))).map (cons true)) := by simp only [List.map_map, List.map_append]
      _ = grayRecSlides n'.succ.succ := by rfl

theorem Subset.append_map_cons_diff_rev_ne {n : Nat} {as bs : List (Subset n)} :
  ∀ a ∈ as.map (cons false), ∀ b ∈ (bs.map (cons true)).reverse, a ≠ b := by
    intro a ha
    intro b hb
    match a with
    | cons true _ =>
      contradiction

-- pairwise_reverse, pairwise_map
theorem Subset.cons_diff_rev_nodup {n : Nat} {l : List (Subset n)} (h : l.Nodup) :
  ((l.map (cons false)) ++ (l.map (cons true)).reverse).Nodup := by
    induction l with
    | nil => simp only [List.map_nil, List.reverse_nil, List.append_nil, List.nodup_nil]
    | cons x xs ih =>
      simp_all [List.Nodup, List.pairwise_reverse, List.pairwise_append, List.pairwise_map]

theorem Subset.grayRecSlides_nodup {n : Nat} : (grayRecSlides n).Nodup := by
  induction n with
  | zero => simp only [grayRecSlides, helpGRS, List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self]
  | succ n' ih =>
    simp [grayRecSlides_IS]
