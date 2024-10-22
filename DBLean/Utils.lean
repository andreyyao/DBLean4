import Mathlib.Data.Finite.Basic
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Data.Set.Finite
variable {n : Nat}

/-- A vector is a list with extra length information enforced -/
structure Vect (A : Type) where
  lst : List A
  len : lst.length = n

/-- An empty vector of length 0 -/
def Vect.empty {A : Type} : @Vect 0 A :=
  { lst := [], len := List.length_nil }

/-- Like List.map, but respects length in dependent type -/
def Vect.map {A B : Type} (f : A -> B) (V : @Vect n A) : @Vect n B :=
  { lst := List.map f V.lst,
    len := Eq.subst V.len (List.length_map V.lst f) }

def Vect.mem {A : Type} (V : @Vect n A) (a : A) : Prop :=
  List.Mem a V.lst

theorem Vect.len_transport {A : Type} {n m : Nat} (nm : n = m) : @Vect n A = @Vect m A := by rw [nm]

lemma Vect.empty_unique : ∀ (v : @Vect 0 A), v = Vect.empty := by
  intros v
  have list_zero_nil : ∀ l : List A, l.length = 0 -> l = [] := by
    intro l
    cases l with
    | nil => intro; rfl
    | cons a t =>
      rw [List.length_cons]; intro H; contradiction
  match v with
  | Vect.mk lst len =>
    have lst_nil := list_zero_nil lst len
    subst lst; rfl

theorem Vect.finite_finite {A : Type} : Finite A -> Finite (@Vect n A) := by
  intro H
  induction n with
  | zero =>
    let toFun := fun (v : @Vect 0 A) => { val := 0, isLt := Nat.zero_lt_one : Fin 1}
    let invFun := fun (m : Fin 1) => @Vect.empty A
    have left_inverse : Function.LeftInverse invFun toFun := by
      unfold Function.LeftInverse; intro v
      rw [empty_unique (invFun (toFun v)), empty_unique v]
    have right_inverse : Function.RightInverse invFun toFun := by
      unfold Function.RightInverse
      intro fin; cases fin with
      | mk m lt => apply ((@Nat.lt_one_iff m).1) at lt; subst m; rfl
    have equiv := Equiv.mk toFun invFun left_inverse right_inverse
    exact (Finite.intro equiv)
  | succ n' IH => cases IH with | @intro b IHEq => cases H with | @intro c Eq =>
    let N := b * c
    let toFun := fun (v : @Vect n A) => 0
    sorry

lemma function_finite {A B : Type} : Finite A -> Finite B -> Finite (A -> B) := by intros; exact Pi.finite
