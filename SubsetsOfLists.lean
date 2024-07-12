import «Subsets».SubsetDef

def Subset.ofList {α : Type} {n : Nat} (soFar : List α) (s : Subset n) (l : List α) (ok : s.card = l.length): List α :=
  match s, l with
  | Subset.nil, [] => soFar
  | Subset.cons false bs, x :: xs =>
    have ok' : bs.card = xs.length := by
      calc bs.card
        _ = bs.card + 1 - 1 := rfl
        _ = (Subset.cons false bs).card - 1 := rfl
        _ = (x::xs).length - 1 := by rw [ok]
    Subset.ofList soFar bs xs ok'
  | Subset.cons true bs, x :: xs =>
    have ok' : bs.card = xs.length := by
      calc bs.card
        _ = bs.card + 1 - 1 := rfl
        _ = (Subset.cons false bs).card - 1 := rfl
        _ = (x::xs).length - 1 := by rw [ok]
    Subset.ofList (x :: soFar) bs xs ok'

def Subset.genAllList {α : Type} (l : List α) :=
  let (s : List (Subset l.length)) := Subset.genRec l.length
  let rec help (soFar : List (List α)) : List (Subset l.length) → List (List α)
  | [] => soFar
  | x :: xs => help ((Subset.ofList [] x l rfl) :: soFar) xs
  help [] s

#eval (Subset.genAllList [1,2,3,4,8,9]).length
