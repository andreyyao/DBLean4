import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Semirings

This file provides definitions for semirings and related concepts like the
natural order. It also concretely defines various semirings like `Bool`, `Nat`,
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

instance NatOrdInstPreOrder {K : Type} [Semiring K] : IsPreorder K (natural_order K) where
  refl := by intro a; exists 0; rw [add_zero]
  trans := by
    rintro a b c ⟨k1, eq1⟩ ⟨k2, eq2⟩; exists (k1 + k2)
    rw [<- add_assoc, eq1, eq2]

@[default_instance]
instance {K : Type} [Semiring K] : Preorder K where
  le := natural_order K
  le_refl := NatOrdInstPreOrder.refl
  le_trans := NatOrdInstPreOrder.trans

class NatOrdSemiring (K : Type) extends Semiring K where
  naturally_ordered : IsPartialOrder K (natural_order K)

instance instPartialOrder {K : Type} [no : NatOrdSemiring K] : PartialOrder K where
  le_antisymm := no.naturally_ordered.antisymm

/-- Prop. A.2 from "Containment of conjunctive queries on annotated relations" -/
lemma homomorphism_monotone (K1 K2 : Type) [NatOrdSemiring K1] [NatOrdSemiring K2]
  (hom : RingHom K1 K2) : Monotone hom.toFun := by
  intros a b le; obtain ⟨c, eq⟩ := le; exists (hom c); aesop


@[simp]
def Bool.nsmul : Nat -> Bool -> Bool
| .zero => fun _ => false
| .succ n => fun b => b || (Bool.nsmul n b)

instance Bool.instSemiring : CommSemiring Bool where
  add := or
  add_assoc := by intros; exact Bool.or_assoc _ _ _
  zero := false
  zero_add := by intros; exact Bool.false_or _
  add_zero := by intros; exact Bool.or_false _
  add_comm := by intros; exact Bool.or_comm _ _
  mul := and
  mul_assoc := by intros; exact Bool.and_assoc _ _ _
  mul_comm := by intros; exact Bool.and_comm _ _
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

instance Bool.instIsPartialOrderNatOrd : IsPartialOrder Bool (natural_order Bool) where
  refl := by intro b; unfold natural_order; exists false; cases b <;> aesop
  trans := by
    rintro a b c ⟨x1, eq1⟩ ⟨x2, eq2⟩; exists (x1 + x2)
    rw [<- add_assoc, <- eq2, <- eq1]
  antisymm := by
    rintro a b ⟨x1, eq1⟩ ⟨x2, eq2⟩
    cases a <;> cases b <;> cases x1 <;> cases x2 <;> ((try rfl); (try contradiction))

/- Bool is a naturally ordered semiring -/
instance Bool.instNatOrdSemiring : NatOrdSemiring Bool where
  naturally_ordered := Bool.instIsPartialOrderNatOrd

instance Nat.instIsPartialOrderNatOrd : IsPartialOrder ℕ (natural_order ℕ) where
  antisymm := by
    rintro a b ⟨x1, eq1⟩ ⟨x2, eq2⟩; rw [<- eq1, add_assoc] at eq2; aesop

/- Bool is a naturally ordered semiring -/
instance Nat.instNatOrdSemiring : NatOrdSemiring ℕ where
  naturally_ordered := Nat.instIsPartialOrderNatOrd

/-- Additive analog of the `NoZeroDivisors` class in Mathlib4 -/
class NoZeroSubtractors (M₀ : Type u_2) [Add M₀] [Zero M₀] where
  eq_zero_or_eq_zero_of_add_eq_zero : ∀ {a b : M₀}, a + b = 0 → a = 0 ∨ b = 0

/-- The type of positive semirings -/
class PosSemiring (K : Type) extends Semiring K, NoZeroDivisors K, NoZeroSubtractors K where
  zero_ne_one : 0 ≠ 1

/- This section establishes various provenance polynomials -/
section provenance
  variable (X : Type) /- X is a countable set of variables -/

  /-- ℕ[X]. A provenance polynomial is a countably multivariate polynomial with
  coefficients from the natural numbers -/
  def ProvPolynomial := MvPolynomial X ℕ

  noncomputable
  instance : CommSemiring (ProvPolynomial X) := AddMonoidAlgebra.commSemiring

  /-- B[X]. A boolean provenance polynomial is a countably multivariate
  polynomial with boolean coefficients -/
  def BoolProvPolynomial := MvPolynomial X Bool

  noncomputable
  instance : CommSemiring (BoolProvPolynomial X) := AddMonoidAlgebra.commSemiring

end provenance
