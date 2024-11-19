import Mathlib.Order.BooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Algebra.BigOperators.Finprod
import DBLean.Semirings

lemma entry_true_impl_bool_summation_true {D : Type}: ∀ (S : Finset D) (f : D -> Bool),
  (∃ s ∈ S, f s = true) → (S.sum f = true) := by
  intros S f ex
  apply Finset.sup_eq_top_iff.mpr at ex
  exact ex

lemma bool_summation_true_impl_entry_true {D : Type}: ∀ (S : Finset D) (f : D -> Bool),
  (S.sum f = true) → (∃ s ∈ S, f s = true) := by
  intros S f eq;
  rw [Finset.sum_eq_fold] at eq
  exact Finset.sup_eq_top_iff.mp eq /-Huh, nice find-/

lemma list_fold_lattice_top {α β : Type} [DistribLattice α] [OrderTop α] :
  ∀ (f : β -> α) (l : List β), List.foldl (fun acc e => acc ⊔ f e) ⊤ l = ⊤ := by
  intros f l
  induction l with
  | nil => rfl
  | cons hd tl IH => simp; exact IH

lemma list_fold_lattice_bot {α β : Type} [DistribLattice α] [OrderBot α] :
  ∀ (f : β -> α) (l : List β), List.foldl (fun acc e => acc ⊓ f e) ⊥ l = ⊥ := by
  intros f l
  induction l with
  | nil => rfl
  | cons hd tl IH => simp; exact IH

lemma list_fold_true_impl_exists_top {β : Type} : ∀ (f : β -> Bool) (l : List β),
  List.foldl (fun acc e => acc + f e) 0 l = 1 →
  ∃ e ∈ l, f e = 1 := by
  intros f l eq; induction l with
  | nil => contradiction
  | cons hd tl IHtl => simp; cases val : (f hd) with
    | true => aesop
    | false => right; aesop

lemma list_fold_init_lt_top_impl_lt_top {α β : Type} [DistribLattice β] [OrderTop β] :
  ∀ (f : α -> β) (l : List α) (i : β), i < ⊤ →
  List.foldl (fun acc e => acc ⊓ f e) i l < ⊤ := by
  intros f l i lt; induction l with
  | nil => simp; exact lt
  | cons hd tl IH =>
    rw [<- List.foldl_map] at *; simp; rw [inf_comm, List.foldl_assoc] at *
    generalize List.foldl Inf.inf i (List.map f tl) = x at *
    have _ : f hd ⊓ x ≤ x := by apply inf_le_right
    have _ : x ≤ ⊤ := (le_of_lt IH)
    apply lt_of_le_of_ne
    . aesop
    . aesop

lemma list_fold_top_impl_forall_top {α β : Type} [DistribLattice β] [OrderTop β] [Dec: DecidableEq β]:
  ∀ (f : α -> β) (l : List α),
  List.foldl (fun acc e => acc ⊓ f e) ⊤ l = ⊤ →
  (∀ e ∈ l, f e = ⊤) := by
  intros f l eq; induction l with
  | nil => simp
  | cons hd tl IHtl => simp; simp at eq; cases (Dec (f hd) ⊤) with
    | isTrue h => aesop
    | isFalse h =>
      apply lt_top_iff_ne_top.mpr at h
      have fold_lt := list_fold_init_lt_top_impl_lt_top f tl (f hd) h
      aesop

lemma forall_top_impl_list_fold_top {α β : Type} [DistribLattice β] [OrderTop β] :
  ∀ (f : α -> β) (l : List α),
  (∀ e ∈ l, f e = ⊤) →
  List.foldl (fun acc e => acc ⊓ f e) ⊤ l = ⊤ := by
  intros f l H; induction l with
  | nil => rfl
  | cons hd tl IHtl =>
    simp; simp at H; rcases H with ⟨eq, alltl⟩; rw [eq]; apply IHtl alltl
