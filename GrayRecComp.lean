import «Subsets».SubsetDef

def Subset.helpGRS (n : Nat) (parity : Bool) : List (Subset n) :=
  match n with
  | 0 => [nil]
  | n'+1 => ((helpGRS n' false).map (cons parity)) ++ ((helpGRS n' true).map (cons ¬parity))

def Subset.grayRecSlides (n : Nat) : List (Subset n) := helpGRS n false

def Subset.helpGG {n : Nat} (Γₙ : List (Subset n)) (soFar : List (Subset (n+1))) : List (Subset (n+1)) :=
  match Γₙ with
  | [] => soFar
  | x :: xs => (cons false x) :: helpGG xs ((cons true x) :: soFar)

def Subset.genGray (n : Nat) : List (Subset n) :=
  match n with
  | 0 => [nil]
  | n'+1 => helpGG (genGray n') []

#eval (Subset.genGray 3) == (Subset.grayRecSlides 3)

theorem Subset.helpGRS_parity_reverse {n : Nat} : (helpGRS n false).reverse = helpGRS n true := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    calc (helpGRS n'.succ false).reverse
      _ = (((helpGRS n' false).map (cons false)) ++ ((helpGRS n' true).map (cons true))).reverse := by rfl
      _ = ((helpGRS n' true).map (cons true)).reverse ++ ((helpGRS n' false).map (cons false)).reverse := by simp
      _ = ((helpGRS n' true).reverse.map (cons true)) ++ ((helpGRS n' false).reverse.map (cons false)) := by simp [List.reverse_map]
      _ = ((helpGRS n' false).reverse.reverse.map (cons true)) ++ ((helpGRS n' true).map (cons false)) := by rw [ih]
      _ = ((helpGRS n' false).map (cons true)) ++ ((helpGRS n' true).map (cons false)) := by simp
      _ = helpGRS n'.succ true := by rfl

theorem Subset.helpGG_symmetry {n : Nat} :

-- theorem Subset.genGray_IS {n : Nat} :
--   ((genGray n).map (cons false)) ++ ((genGray n).map (cons true)).reverse = genGray n.succ := by
--     induction n with
--     | zero => rfl
--     | succ n' ih =>
--       calc ((genGray n'.succ).map (cons false)) ++ ((genGray n'.succ).map (cons true)).reverse
--         _ = ((((genGray n').map (cons false)) ++ ((genGray n').map (cons true)).reverse).map (cons false)) ++ ((((genGray n').map (cons false)) ++ ((genGray n').map (cons true)).reverse).map (cons true)).reverse := by simp [ih]

-- theorem Subset.gray_rec_eq {n : Nat} : grayRecSlides n = genGray n := by
--   induction n with
--   | zero => rfl
--   | succ n' ih =>
--     calc grayRecSlides n'.succ
--       _ = helpGRS n'.succ false := by rfl
--       _ = ((helpGRS n' false).map (cons false)) ++ ((helpGRS n' true).map (cons ¬false)) := by rfl
--       _ = ((helpGRS n' false).map (cons false)) ++ ((helpGRS n' false).reverse.map (cons ¬false)) := by rw [helpGRS_parity_reverse]
--       _ = ((grayRecSlides n').map (cons false)) ++ ((grayRecSlides n').reverse.map (cons ¬false)) := by rfl
--       _ = ((genGray n').map (cons false)) ++ ((genGray n').reverse.map (cons ¬false)) := by rw [ih]
--       _ = ((genGray n').map (cons false)) ++ ((genGray n').reverse.map (cons true)) := by simp
--       _ = ((genGray n').map (cons false)) ++ ((genGray n').map (cons true)).reverse := by simp [List.reverse_map]
