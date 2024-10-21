variable {n : Nat}

/-! A vector is a list with extra length information enforced -/
structure Vect (A : Type) where
  lst : List A
  len : lst.length = n

def Vect.map {A B : Type} (f : A -> B) (V : @Vect n A) : @Vect n B :=
  { lst := List.map f V.lst,
    len := Eq.subst V.len (List.length_map V.lst f) }

def Vect.mem {A : Type} (V : @Vect n A) (a : A) : Prop :=
  List.Mem a V.lst

theorem len_transport {A : Type} {n m : Nat} (nm : n = m) : @Vect n A = @Vect m A := by rw [nm]
