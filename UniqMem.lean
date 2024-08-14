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

theorem List.uMem_of_uElem_eq_true [BEq α] [LawfulBEq α] {x : α} {l : List α} : List.uElem a as = true → List.UniqMem a as := by
  induction l with
  | nil => simp [uElem]
  | cons a as ih =>
    rfl

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
            | cons a as ih' =>

          have : List.UniqMem (cons true bs) (cons true bs :: helpGR xs) := by simp [List.UniqMem]
          --   _ = List.UniqMem (cons true bs) (cons true bs :: helpGR xs) := by rfl
          --   _ = ((cons true bs) :: helpGR xs).uElem (cons true bs) := by rfl
          --   _ = match (cons true bs) == (cons true bs) with | true => !(helpGR xs).elem (cons true bs) | false => (helpGR xs).uElem (cons true bs) := by rfl
          --   _ = !(helpGR xs).elem (cons true bs) := by simp
