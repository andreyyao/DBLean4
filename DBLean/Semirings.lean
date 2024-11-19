import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Semirings

This file provides definitions for semirings and related concepts like the
natural order. It also concretely defines various semirings like `bool`, `nat`,
polynomial semirings, etc.

It defines a `NatOrdSemiring` typeclass for naturally ordered semirings and
instantiates several semirings as its instance.

Note that this file is only about semirings, and does not reference any
databases concepts.

## Tags

semirings
-/

def natural_order (K : Type) [Semiring K] : K -> K -> Prop :=
  fun (a b : K) => ∃ (c : K), a + c = b

@[default_instance]
instance instPreOrder {K : Type} [Semiring K] : Preorder K where
  le := natural_order K
  le_refl := by intro a; exists 0; simp
  le_trans := by
    intros a b c le1 le2
    let ⟨k1, E1⟩ := le1
    let ⟨k2, E2⟩ := le2
    exists (k1 + k2); rw [<- add_assoc, E1]; exact E2

class NatOrdSemiring (K : Type) extends Semiring K where
  naturally_ordered : IsPartialOrder K (natural_order K)

instance instPartialOrder {K : Type} [no : NatOrdSemiring K] : PartialOrder K where
  le_antisymm := by
    intros a b le_ab le_ba
    exact (no.naturally_ordered.antisymm a b le_ab le_ba)

/-- Prop. A.2 from "Containment of conjunctive queries on annotated relations" -/
lemma homomorphism_monotone (K1 K2 : Type) [NatOrdSemiring K1] [NatOrdSemiring K2]
  (hom : RingHom K1 K2) : Monotone hom.toFun := by
  intros a b le; obtain ⟨c, eq⟩ := le; exists (hom c); aesop


@[simp]
def Bool.nsmul : Nat -> Bool -> Bool
| .zero => fun _ => false
| .succ n => fun b => b || (Bool.nsmul n b)

instance Bool.instSemiring : Semiring Bool where
  add := or
  add_assoc := by intros; exact Bool.or_assoc _ _ _
  zero := false
  zero_add := by intros; exact Bool.false_or _
  add_zero := by intros; exact Bool.or_false _
  add_comm := by intros; exact Bool.or_comm _ _
  mul := and
  mul_assoc := by intros; exact Bool.and_assoc _ _ _
  one := true
  one_mul := by intros; exact Bool.true_and _
  mul_one := by intros; exact Bool.and_true _
  left_distrib := by intros; exact Bool.and_or_distrib_left _ _ _
  right_distrib := by intros; exact Bool.and_or_distrib_right _ _ _
  zero_mul := by intros; exact Bool.false_and _
  mul_zero := by intros; exact Bool.and_false _
  nsmul := Bool.nsmul
  nsmul_zero := by intro b; rfl
  nsmul_succ := by intros n b; simp; rw [Bool.or_comm]; rfl
