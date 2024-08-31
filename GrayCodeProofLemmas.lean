import Subsets.GrayRecComp

-- copied from documentation
theorem List.copied_getElem_reverse {l : List α} {i} (h : i < l.reverse.length) :
    l.reverse[i] = l[l.length - 1 - i]'(Nat.sub_one_sub_lt (by simpa using h)) := by
  apply Option.some.inj
  rw [← getElem?_eq_getElem, ← getElem?_eq_getElem]
  rw [getElem?_reverse (by simpa using h)]



-- num_changes and related lemmas
def Subset.num_changes {n : Nat} : Subset n → Subset n → Nat
  | nil, nil => 0
  | cons true as, cons true bs => num_changes as bs
  | cons false as, cons false bs => num_changes as bs
  | cons _ as, cons _ bs => 1 + num_changes as bs

theorem Subset.symm_num_changes {n : Nat} {as bs : Subset n} : num_changes as bs = num_changes bs as := by
  induction n with
  | zero =>
    match as, bs with
    | nil, nil => rfl
  | succ n' ih =>
    match as, bs with
    | cons true xs, cons true ys =>
      calc num_changes (cons true xs) (cons true ys)
        _ = num_changes xs ys := by rfl
        _ = num_changes ys xs := by rw [ih]
        _ = num_changes (cons true ys) (cons true xs) := by rfl
    | cons false xs, cons false ys =>
      calc num_changes (cons false xs) (cons false ys)
        _ = num_changes xs ys := by rfl
        _ = num_changes ys xs := by rw [ih]
        _ = num_changes (cons false ys) (cons false xs) := by rfl
    | cons true xs, cons false ys =>
      calc num_changes (cons true xs) (cons false ys)
        _ = 1 + num_changes xs ys := by rfl
        _ = 1 + num_changes ys xs := by rw [ih]
        _ = num_changes (cons false ys) (cons true xs) := by rfl
    | cons false xs, cons true ys =>
      calc num_changes (cons false xs) (cons true ys)
        _ = 1 + num_changes xs ys := by rfl
        _ = 1 + num_changes ys xs := by rw [ih]
        _ = num_changes (cons true ys) (cons false xs) := by rfl

theorem Subset.cons_same_num_changes {n : Nat} {as bs : Subset n} {x : Bool} : num_changes (cons x as) (cons x bs) = num_changes as bs := by
  cases x
  repeat rfl

theorem Subset.eq_num_changes_eq_zero {n : Nat} {as : Subset n} : num_changes as as = 0 := by
  induction as with
  | nil => rfl
  | cons b bs ih =>
    have : num_changes (cons b bs) (cons b bs) = num_changes bs bs := by cases b <;> repeat rfl
    rw [this]
    rw [ih]

def Subset.isGray {n : Nat} : List (Subset n) → Bool
  | [] => true
  | _::[] => true
  | x :: y :: zs => (num_changes x y = 1) ∧ isGray (y::zs)



-- copied from GrayRec
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

theorem Subset.genGray_num (n : Nat) : (genGray n).length = 2^n :=
  by induction n with
  | zero => rfl
  | succ n' ih =>
    calc (genGray n'.succ).length
      _ = (helpGG (genGray n') []).length := by rfl
      _ = 2*(genGray n').length + [].length := by rw [helpGG_num]
      _ = 2*(genGray n').length := by rfl
      _ = 2*(2^n') := by rw [ih]
      _ = 2^n'.succ := by rw [Nat.pow_succ']



-- copied from GrayRecSlides
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



-- GrayCodeProof–specific lemmas
theorem Subset.s0 (n' : Nat) : 0<(grayRecSlides n').length :=
  calc 0
    _ < 2^n' := Nat.two_pow_pos n'
    _ = (genGray n').length := by simp [genGray_num n']
    _ = (grayRecSlides n').length := by rw [gray_rec_eq]

theorem s1 {l i : Nat} (h : 0<l) : l-1-(i-l)<l := -- h is (s0 n'), so s1 (s0 n')
  calc l-1-(i-l)
    _ ≤ l-1 := Nat.sub_le (l-1) (i-l)
    _ < l := Nat.pred_lt_self h

theorem s2' {l i : Nat} (h1 : i.succ<2*l) (h2 : l<i.succ) : 1<l :=
  match l with
  | Nat.zero =>
    have : i.succ < 0 := by simp_arith [h1]
    by contradiction
  | Nat.succ l' =>
    if h' : l' = 0 then
      have : 1<i.succ :=
        calc 1
          _ ≤ l'.succ := by simp_arith
          _ < i.succ := h2
      have : 2≤i.succ := by simp_arith [this, Nat.succ_le_of_lt]
      have : i.succ<2 :=
        calc i.succ
          _ < 2*l'.succ := h1
          _ = 2 := by simp_arith [h']
      have : 2<2 :=
        calc 2
          _ ≤ i.succ := by assumption
          _ < 2 := by assumption
      by contradiction
    else
      have : l'>0 := Nat.pos_of_ne_zero h'
      calc 1
        _ < 1+l' := Nat.lt_add_of_pos_right this
        _ = l'.succ := by simp_arith

theorem s2 {l i : Nat} (h1 : l<i.succ) (h2 : 1<l) : l-1-(i.succ-l)<l-1 := -- h1 is h15, h2 is (s2' h16 h15), so s2 h15 (s2' h16 h15)
  have : 0<i.succ-l ↔ l<i.succ := by simp [Nat.sub_pos_iff_lt]
  have h1' : i.succ-l > 0 := by simp [this, h1]
  have : 0<l-1 ↔ 1<l := by simp [Nat.sub_pos_iff_lt]
  have h2' : l-1 > 0 := by simp [this, h2]
  Nat.sub_lt h2' h1'

theorem t16 (a : Nat) (_ : 0 < a) : a-1+1=a := by
  match a with
  | a'+1 => simp_arith

theorem t17 (a b : Nat) (h1 : b<a) : a-(1+b)+1 = a-b := by
  induction b generalizing a with
  | zero => simp [t16 a (by simp [h1])]
  | succ b' ih =>
    have : b'.succ ≠ 0 := by simp_arith
    have h1' : b' < a-1 :=
      calc b'
        _ = b'.succ-1 := by simp_arith
        _ < a-1 := Nat.pred_lt_pred this h1
    calc a-(1+b'.succ)+1
      _ = a-(1+b'+1)+1 := by rfl
      _ = a-(1+b')-1+1 := by simp_arith [Nat.sub_add_eq]
      _ = a-1-(1+b')+1 := by simp_arith [Nat.sub_right_comm]
      _ = a-1-b' := by simp [ih, h1']
      _ = a-(1+b') := by simp_arith [Nat.sub_add_eq]
      _ = a-b'.succ := by simp_arith [Nat.add_comm]

theorem s3 {l i : Nat} (h1 : i.succ<2*l) (h2 : l<i.succ) : (l-1-(i.succ-l)).succ = l-1-(i-l) := -- h1 is h16, h2 is h15, so s3 h16 h15
  have : l+1<i.succ+1 := Nat.add_lt_add_right h2 1
  have : l+1≤Nat.succ i := Nat.le_of_lt_add_one this
  have : i-l<l-1 :=
    calc i-l
      _ = i.succ-1-l := by simp_arith
      _ = i.succ-l-1 := Nat.sub_right_comm i.succ 1 l
      _ = i.succ-(l+1) := Nat.sub_add_eq i.succ l 1
      _ < 2*l-(l+1) := Nat.sub_lt_sub_right this h1
      _ = l+l-(l+1) := by rw [Nat.two_mul l]
      _ = l+l-l-1 := Nat.sub_add_eq (l+l) l 1
      _ = l-1 := by simp
  calc Nat.succ (l - 1 - (Nat.succ i - l))
    _ = l - 1 - (i + 1 - l) + 1 := by simp_arith
    _ = l - 1 - (1 + i - l) + 1 := by rw [Nat.add_comm i 1]
    _ = l - 1 - (1 + (i - l)) + 1 := by rw [Nat.add_sub_assoc (Nat.le_of_lt_add_one h2 : l≤i) 1]
    _ = l - 1 - (i - l) := t17 (l-1) (i-l) this
