import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Ring.Hom.Defs

/-- Why(X) provenance is the double power set of X -/
def Why (X : Type) := Set (Set X)

instance Why.instCommSemiring {X : Type} : CommSemiring (Why X) where
  add := Set.union
  add_assoc := Set.union_assoc
  zero := (∅ : Set (Set X))
  zero_add := Set.empty_union
  add_zero := Set.union_empty
  add_comm := Set.union_comm
  mul := fun (S1 S2 : Set (Set X)) => { s | ∃ s1 ∈ S1, ∃ s2 ∈ S2, s = s1 ∪ s2}
  mul_comm := by
    intros A B; unfold HMul.hMul; unfold instHMul; unfold Mul.mul; simp
    apply Set.ext; intro x; rw [Set.mem_setOf_eq]; rw [Set.mem_setOf_eq]
    apply Iff.intro
    . rintro ⟨a1, ⟨a1_mem, ⟨b1, ⟨b1_mem, eq1⟩⟩⟩⟩; aesop
    . rintro ⟨b1, ⟨b1_mem, ⟨a1, ⟨a1_mem, eq1⟩⟩⟩⟩; aesop
  mul_assoc := by
    intros A B C; unfold HMul.hMul; unfold instHMul; unfold Mul.mul; simp
    apply Set.ext; intro x; rw [Set.mem_setOf_eq]; rw [Set.mem_setOf_eq]
    apply Iff.intro
    . rintro ⟨y, ⟨⟨a1, ⟨a1_mem, ⟨b1, ⟨b1_mem, eq1⟩⟩⟩⟩, ⟨c1, ⟨c1_mem, eq2⟩⟩⟩⟩
      exists a1; split_ands; exact a1_mem; exists (b1 ∪ c1)
      split_ands
      . exists b1; split_ands; exact b1_mem; exists c1
      . aesop
    . rintro ⟨a1, ⟨a1_mem, ⟨y, ⟨⟨b1, ⟨b1_mem, ⟨c1, ⟨c1_mem, eq1⟩⟩⟩⟩, eq2⟩⟩⟩⟩
      exists (a1 ∪ b1)
      split_ands
      . exists a1; split_ands; exact a1_mem
        exists b1
      . exists c1; split_ands; exact c1_mem; aesop
  zero_mul := by
    intro S; unfold HMul.hMul; unfold instHMul; unfold Mul.mul; simp
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro T; simp; aesop
  mul_zero := by
    intro S; unfold HMul.hMul; unfold instHMul; unfold Mul.mul; simp
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro T; simp; aesop
  one := Set.singleton ∅
  mul_one := by
    intros A; unfold HMul.hMul; unfold instHMul; unfold Mul.mul; simp
    apply Set.ext; intro x; rw [Set.mem_setOf_eq]; apply Iff.intro
    . rintro ⟨a, ⟨a_mem, ⟨e, ⟨e_mem, eq⟩⟩⟩⟩
      rw [Set.mem_singleton_iff.mp e_mem] at eq; aesop
    . intro x_mem; exists x; split_ands; exact x_mem; exists ∅; aesop
  one_mul := by
    intros A; rw [mul_comm] -- Why doesn't this work?
