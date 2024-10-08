-- very much a draft, now unnecessary

import «Subsets».SubsetDef

inductive List.UniqMem (x : α) : List α → Prop
  /-- The head of a list is a member if it is not in the rest of the list: `x ∉ as → x ∈! x :: as`. -/
  | head (as : List α) : x ∉ as → UniqMem x (x::as)
  /-- A "unique member" of the tail of a list is a member of the list if it is not equal to the head
  of the list: `x ≠ a ∧ x ∈! as → x ∈! a :: as`. -/
  | tail (a : α) {as : List α} : x ≠ a → UniqMem x as → UniqMem x (a::as)

-- instance {n : Nat} : LawfulBEq (Subset n) where
--   eq_of_beq {as bs} := by
--     induction as with
--     | nil => intro h; cases bs <;> first | rfl | contradiction
--     | cons a as ih =>
--       cases bs with
--       | cons b bs =>
--         simp [show (Subset.cons a as == Subset.cons b bs) = (a == b && as == bs) from rfl, -and_imp]
--         intro ⟨h₁, h₂⟩
--         exact ⟨h₁, ih h₂⟩
--   rfl {as} := by
--     induction as with
--     | nil => rfl
--     | cons a as ih => simp [BEq.beq, Subset.beq, LawfulBEq.rfl]; exact ih

def List.uElem [BEq α] (a : α) : List α → Bool
  | []    => false
  | b::bs => match a == b with
    | true  => !bs.elem a
    | false => bs.uElem a

@[simp] theorem List.uElem_nil [BEq α] : ([] : List α).uElem a = false := by rfl

theorem List.uElem_cons [BEq α] {a : α} :
    (b::bs).uElem a = match a == b with | true => !bs.elem a | false => bs.uElem a := by rfl

-- theorem List.uMem_of_uElem_eq_true [BEq α] [LawfulBEq α] {x : α} {l : List α} : List.uElem a as = true → List.UniqMem a as := by
--   induction l with
--   | nil => simp [uElem]
--   | cons a as ih =>
--     rfl

-- theorem List.uMem_of_uElem_eq_true [BEq α] [LawfulBEq α] {a : α} {as : List α} : elem a as = true → UniqMem a as := by
--   match as with
--   | [] => simp [elem]
--   | a'::as =>
--     simp [elem]
--     split
--     next h => intros; simp [BEq.beq] at h; subst h; apply Mem.head
--     next _ => intro h; exact Mem.tail _ (mem_of_elem_eq_true h)

-- theorem elem_eq_true_of_mem [BEq α] [LawfulBEq α] {a : α} {as : List α} (h : a ∈ as) : elem a as = true := by
--   induction h with
--   | head _ => simp [elem]
--   | tail _ _ ih => simp [elem]; split; rfl; assumption

-- instance [BEq α] [LawfulBEq α] (a : α) (as : List α) : Decidable (a ∈ as) :=
--   decidable_of_decidable_of_iff (Iff.intro mem_of_elem_eq_true elem_eq_true_of_mem)

-- theorem Subset.uElem_genRec_IS {n : Nat} {b : Bool} {bs : Subset n} {l : List (Subset n)} :
--   l.UniqMem bs → (helpGR l).uElem (cons b bs) := by
--     induction l with
--     | nil => nofun
--     | cons x xs ih =>
--       intro h1
--       cases h1
--       . have : helpGR (bs::xs) = ((cons false bs) :: (cons true bs) :: helpGR xs) :=
--           calc helpGR (bs::xs)
--             _ = ((cons false bs) :: (cons true bs) :: helpGR xs) := by rfl
--         rw [this]
--         cases b with
--         | true =>
--           calc List.uElem (cons true bs) (cons false bs :: cons true bs :: helpGR xs)
--             _ = ((cons true bs) :: helpGR xs).uElem (cons true bs) := by rfl
--             _ = match (cons true bs) == (cons true bs) with | true => !(helpGR xs).elem (cons true bs) | false => (helpGR xs).uElem (cons true bs) := by rfl
--             _ = !(helpGR xs).elem (cons true bs) := by simp
--         | false => simp [List.any_cons, this]
--       . have : bs ∈ xs := by assumption
--         have h2 : (cons b bs) ∈ helpGR xs := by simp [ih, this]
--         have h3 : helpGR (x::xs) = (cons false x) :: [cons true x] ++ helpGR xs := by rfl
--         simp [h2,h3]

-- theorem Subset.t5 {n : Nat} {b : Bool} {bs : Subset n} {l : List (Subset n)} {h : bs ∉ l} :
--   cons b bs ∉ helpGR l := by
--     induction l with
--     | nil => nofun
--     | cons x xs ih =>
      -- have : bs ≠ x := by
      --   calc bs ≠ x
      --     _ = ¬ (bs = x) := by rfl
      --     _ = ¬
theorem Subset.t6 {n : Nat} {b : Bool} {bs : Subset n} {l : List (Subset n)} :
  cons b bs ∈ helpGR l → bs ∈ l := by
    induction l with
    | nil =>
      have h1 : (cons b bs) ∉ ([] : List (Subset (n+1))) := by simp
      have h2 : ((cons b bs) ∉ helpGR ([] : List (Subset n))) → False := by simp [h]
      simp
      have h3 : helpGR ([] : List (Subset n)) = ([] : List (Subset (n+1))) := by rfl
      have h4 : (cons b bs) ∉ helpGR ([] : List (Subset n)) := by simp [h1, h3]
      simp [h2, h4]
    | cons x xs ih =>
      intro h
      cases h
      . simp
      . simp
        have h2 : List.Mem (cons b bs) (cons true x :: helpGR xs) := by assumption
        cases h2
        . simp
        . have h3 : List.Mem (cons b bs) (helpGR xs) := by assumption
          apply Or.inr
          apply ih h3

theorem Subset.t7 {n : Nat} {b : Bool} {bs : Subset n} {l : List (Subset n)} {h : bs ∉ l} :
  cons b bs ∉ helpGR l := sorry -- doesn't work unless have LawfulBEq for Subsets or Decidable mem
    -- let xs : List (Subset (n+1)) := helpGR l
    -- if h1 : List.elem (cons b bs) xs then
    --   have h2 : (cons b bs) ∈ xs := List.mem_of_elem_eq_true h1
    --   have : bs ∈ l := t6 h2
    --   by contradiction
    -- else
    --   sorry --have h2 : (cons b bs) ∉ xs := List.mem_of_elem_eq_true h1

theorem Subset.temp {n : Nat} {b : Bool} {bs : Subset n} {l : List (Subset n)} :
  l.UniqMem bs → (helpGR l).UniqMem (cons b bs) := by
    induction l with
    | nil => nofun
    | cons x xs ih =>
      intro h1
      cases h1
      . have h2 : bs ∉ xs := by assumption
        match b with
        | true =>
          have : List.UniqMem (cons true bs) (helpGR (bs::xs)) = List.UniqMem (cons true bs) (cons false bs :: cons true bs :: helpGR xs) := by rfl
          have : (cons true bs) ∉ helpGR xs := by
            induction xs with
            | nil => nofun
            | cons y ys ih' => sorry
              -- have : helpGR (y::ys) = (cons false y :: cons true y :: helpGR ys) := by rfl
              -- have : bs ≠ y := by assumption
              -- match b with
              -- | false =>
              --   rw [h2]
          sorry
          -- have : List.UniqMem (cons true bs) (cons true bs :: helpGR xs) := by simp [List.UniqMem]
        | false => sorry
          --   _ = List.UniqMem (cons true bs) (cons true bs :: helpGR xs) := by rfl
          --   _ = ((cons true bs) :: helpGR xs).uElem (cons true bs) := by rfl
          --   _ = match (cons true bs) == (cons true bs) with | true => !(helpGR xs).elem (cons true bs) | false => (helpGR xs).uElem (cons true bs) := by rfl
          --   _ = !(helpGR xs).elem (cons true bs) := by simp
      . have h3 : bs ≠ x := by assumption
        have h4 : xs.UniqMem bs := by assumption
        sorry
