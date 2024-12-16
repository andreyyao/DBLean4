import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Quotient
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Polynomial.Basic

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

/-- Additive monoid analog of the `NoZeroDivisors` class from Mathlib4 -/
class NoZeroSubtractors (M₀ : Type u_2) [Add M₀] [Zero M₀] : Prop where
  eq_zero_or_eq_zero_of_add_eq_zero : ∀ {a b : M₀}, a + b = 0 → a = 0 ∨ b = 0

/-- The type of positive semirings -/
class PosSemiring (K : Type) [Semiring K] extends NoZeroDivisors K, NoZeroSubtractors K : Prop where
  zero_ne_one : (1 : K) ≠ (0 : K)

/-- Prop. A.2 from "Containment of conjunctive queries on annotated relations" -/
lemma homomorphism_monotone (K1 K2 : Type) [NatOrdSemiring K1] [NatOrdSemiring K2]
  (hom : K1 →+* K2) : Monotone hom.toFun := by
  intros a b le; obtain ⟨c, eq⟩ := le; exists (hom c); aesop

@[simp]
def Bool.nsmul : Nat -> Bool -> Bool
| .zero => fun _ => false
| .succ n => fun b => b || (Bool.nsmul n b)

@[default_instance]
instance Bool.instSemiring : CommSemiring Bool where
  add := or
  add_assoc := Bool.or_assoc
  zero := false
  zero_add := Bool.false_or
  add_zero := Bool.or_false
  add_comm := Bool.or_comm
  mul := and
  mul_assoc := Bool.and_assoc
  mul_comm := Bool.and_comm
  one := true
  one_mul := Bool.true_and
  mul_one := Bool.and_true
  left_distrib := Bool.and_or_distrib_left
  right_distrib := Bool.and_or_distrib_right
  zero_mul := Bool.false_and
  mul_zero := Bool.and_false
  nsmul := Bool.nsmul
  nsmul_zero := by intro b; rfl
  nsmul_succ := by intros n b; simp; rw [Bool.or_comm]; rfl

instance Bool.instIsPartialOrderNatOrd : IsPartialOrder Bool (natural_order Bool) where
  antisymm := by
    rintro a b ⟨x1, eq1⟩ ⟨x2, eq2⟩
    cases a <;> cases b <;> cases x1 <;> cases x2 <;> ((try rfl); (try contradiction))

/- Bool is a naturally ordered semiring -/
instance Bool.instNatOrdSemiring : NatOrdSemiring Bool where
  naturally_ordered := Bool.instIsPartialOrderNatOrd

/- Bool is a positive semiring -/
instance Bool.instPosSemiring : PosSemiring Bool where
  eq_zero_or_eq_zero_of_add_eq_zero := by
    rintro a b eq; cases a <;> cases b <;> try contradiction
    left; rfl
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    rintro a b eq; cases a <;> cases b <;> ((try contradiction); try aesop)
  zero_ne_one := by rintro h; injection h

instance Nat.instIsPartialOrderNatOrd : IsPartialOrder ℕ (natural_order ℕ) where
  antisymm := by
    rintro a b ⟨x1, eq1⟩ ⟨x2, eq2⟩; rw [<- eq1, add_assoc] at eq2; aesop

/- ℕ is a naturally ordered semiring -/
instance Nat.instNatOrdSemiring : NatOrdSemiring ℕ where
  naturally_ordered := Nat.instIsPartialOrderNatOrd

/- ℕ is a positive semiring -/
instance Nat.instPosSemiring : PosSemiring ℕ where
  eq_zero_or_eq_zero_of_add_eq_zero := by
    rintro a b eq; apply add_eq_zero.mp at eq; aesop
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    rintro a b; exact mul_eq_zero.mp
  zero_ne_one := by rintro h; injection h

/- This section establishes various provenance polynomials -/
section provenance
  variable (X : Type) /- X is a countable set of variables -/
  variable [DecidableEq X]

  /-- Additive analog of Function.Injective.NoZeroDivisors from Mathlib4 -/
  protected theorem Function.Injective.noZeroSubtractors
  {M₀ : Type u_1} {M₀' : Type u_3} [Add M₀] [Zero M₀] [Add M₀'] [Zero M₀']
  (f : M₀ → M₀') (hf : Function.Injective f) (zero : f 0 = 0)
  (add : ∀ (x y : M₀), f (x + y) = f x + f y) [noZeroSub : NoZeroSubtractors M₀'] :
   NoZeroSubtractors M₀ where
     eq_zero_or_eq_zero_of_add_eq_zero := by
       intros a b eq; specialize add a b; rw [eq, zero] at add; symm at add
       apply noZeroSub.eq_zero_or_eq_zero_of_add_eq_zero at add; cases add with
       | inl h => left; nth_rw 1 [<- zero] at h; apply (hf h)
       | inr h => right; nth_rw 1 [<- zero] at h; apply (hf h)

  /-- Additive analog of Polynomial.instNoZeroDivisors from Mathlib4 -/
  instance Polynomial.instNoZeroSubtractors {K : Type} [CommSemiring K] [nzsb : NoZeroSubtractors K] :
    NoZeroSubtractors (Polynomial K) where
    eq_zero_or_eq_zero_of_add_eq_zero := by
      intros p q eq
      rcases (lt_trichotomy p.degree q.degree) with dg_lt | (dg_eq | dg_gt)
      . have h := leadingCoeff_add_of_degree_lt dg_lt
        rw [eq] at h; simp at h; right; apply leadingCoeff_eq_zero.mp; rw [h]
      . rcases deg_case : p.degree with ( _ | ( _ | n ))
        . apply degree_eq_bot.mp at deg_case; left; exact deg_case
        . rw [deg_case] at dg_eq; symm at dg_eq
          rw [eq_C_of_degree_eq_zero deg_case, eq_C_of_degree_eq_zero dg_eq] at eq
          rw [<- C_add] at eq; apply C_eq_zero.mp at eq
          cases (nzsb.eq_zero_or_eq_zero_of_add_eq_zero eq) with
          | inl p_zero => left; rw [<- C_0]; rw [eq_C_of_degree_eq_zero deg_case, <-p_zero]
          | inr q_zero => right; rw [<- C_0]; rw [eq_C_of_degree_eq_zero dg_eq, <-q_zero]
        . cases (Classical.em (p.leadingCoeff + q.leadingCoeff = 0)) with
          | inl coeff_sum_eq_zero =>
            cases (nzsb.eq_zero_or_eq_zero_of_add_eq_zero coeff_sum_eq_zero) with
            | inl p_lcz => left; apply leadingCoeff_eq_zero.mp p_lcz
            | inr q_lcz => right; apply leadingCoeff_eq_zero.mp q_lcz
          | inr coeff_sum_ne_zero =>
            have h := leadingCoeff_add_of_degree_eq dg_eq coeff_sum_ne_zero
            rw [eq] at h; simp at h; symm at h
            cases (nzsb.eq_zero_or_eq_zero_of_add_eq_zero h) with
            | inl p_lcz => left; rw [leadingCoeff_eq_zero.mp p_lcz]
            | inr q_lcz => right; rw [leadingCoeff_eq_zero.mp q_lcz]
      . have h := leadingCoeff_add_of_degree_lt dg_gt
        rw [add_comm, eq] at h; simp at h; left; apply leadingCoeff_eq_zero.mp; rw [h]

  /-- Additive analog of Mathlib.RingTheory.Polynomial.noZeroDivisors_fin -/
  theorem noZeroSubtractors_fin (K : Type) [CommSemiring K] [NoZeroSubtractors K] :
    ∀ n : ℕ, NoZeroSubtractors (MvPolynomial (Fin n) K) := by
    intro n; induction n with
    | zero => exact ((MvPolynomial.isEmptyAlgEquiv K _).injective.noZeroSubtractors _ (map_zero _) (map_add _))
    | succ n IH =>
      exact ((MvPolynomial.finSuccEquiv K n).injective.noZeroSubtractors _ (map_zero _) (map_add _) )

  /- Additive analog of Mathlib.RingTheory.Polynomial.noZeroDivisors_of_finite -/
  theorem noZeroSubtractors_of_finite (K : Type) (σ : Type v) [CommSemiring K] [Finite σ]
      [NoZeroSubtractors K] : NoZeroSubtractors (MvPolynomial σ K) := by
    cases nonempty_fintype σ
    haveI := noZeroSubtractors_fin K (Fintype.card σ)
    exact (MvPolynomial.renameEquiv K (Fintype.equivFin σ)).injective.noZeroSubtractors _ (map_zero _) (map_add _)

  instance (K : Type) (σ : Type v) [CommSemiring K] [NoZeroSubtractors K] [Finite σ] :
    Subsingleton (AddUnits (MvPolynomial σ K)) where
    allEq := by
      intro p q
      have _nzsb := noZeroSubtractors_of_finite K σ
      have p_zero : p.val = 0 := by {
        cases (_nzsb.eq_zero_or_eq_zero_of_add_eq_zero p.add_neg) with
        | inl p_zero => exact p_zero
        | inr p_neg_zero => rw [<- (add_zero p.val)]; nth_rw 1 [<- p_neg_zero]; exact p.val_neg
      }
      have q_zero : q.val = 0 := by {
        cases (_nzsb.eq_zero_or_eq_zero_of_add_eq_zero q.add_neg) with
        | inl q_zero => exact q_zero
        | inr q_neg_zero => rw [<- (add_zero q.val)]; nth_rw 1 [<- q_neg_zero]; exact q.val_neg
      }
      exact (AddUnits.eq_iff.mp (Eq.trans p_zero (Eq.symm q_zero)))

  /-- Multivariate polynomials over semiring without zero subtractors also has that property -/
  instance MvPolynomial.instNoZeroSubtractors {X K : Type} [CommSemiring K] [NoZeroSubtractors K] : NoZeroSubtractors (MvPolynomial X K) where
    eq_zero_or_eq_zero_of_add_eq_zero {p q} h := by
      obtain ⟨s, p, q, rfl, rfl⟩ := MvPolynomial.exists_finset_rename₂ p q
      let _nzsb := noZeroSubtractors_of_finite K s
      have : p + q = 0 := by
        apply MvPolynomial.rename_injective _ Subtype.val_injective
        simpa using h
      rw [add_eq_zero] at this; aesop

  /-- Multivariate polynomials over a positive semiring is again a positive semring -/
  noncomputable instance {K : Type} [CommSemiring K] [pos : PosSemiring K] :
    PosSemiring (MvPolynomial X K) where
    zero_ne_one := by
      rintro triv
      let p0 := MvPolynomial.eval (λ _ => 0) (0 : MvPolynomial X K)
      let p1 := MvPolynomial.eval (λ _ => 0) (1 : MvPolynomial X K)
      have p0_eq_0 : p0 = 0 := by unfold p0; rw [<- MvPolynomial.C_0, MvPolynomial.eval_C]
      have p1_eq_1 : p1 = 1 := by unfold p1; rw [<- MvPolynomial.C_1, MvPolynomial.eval_C]
      unfold p0 p1 at *; rw [triv] at p1_eq_1; rw [p1_eq_1] at p0_eq_0
      exact (pos.zero_ne_one p0_eq_0)

  /-- ℕ[X]. A provenance polynomial is a countably multivariate polynomial with
  coefficients from the natural numbers -/
  @[simp]
  def NatProvPolynomial := MvPolynomial X ℕ

  noncomputable instance : CommSemiring (NatProvPolynomial X) := AddMonoidAlgebra.commSemiring

  /-- B[X]. A boolean provenance polynomial is a countably multivariate
  polynomial with boolean coefficients -/
  def BoolProvPolynomial := MvPolynomial X Bool

  noncomputable instance : CommSemiring (BoolProvPolynomial X) := AddMonoidAlgebra.commSemiring


  /- Given a monomial n*X1^{e1}*X2^{e2}*..., return n*X1*X2*... -/
  noncomputable
  def drop_exponents_monomial {X : Type} (s : X →₀ ℕ) (c : ℕ) : NatProvPolynomial X :=
    let drop_exponents_power (s : X →₀ ℕ) : X →₀ ℕ :=
    { support := s.support
      toFun := fun x => min (s x) 1
      mem_support_toFun := by intro x; apply Iff.intro <;> simp }
    MvPolynomial.monomial (drop_exponents_power s) c

  /-- Extends the exponent-dropping to MvPolynomials -/
  noncomputable
  def drop_exponents {X : Type} (p : NatProvPolynomial X) : NatProvPolynomial X :=
    p.sum (drop_exponents_monomial)

  -- The congruence relation on ℕ[X] used to construct Trio[X]
  noncomputable
  def NatPolyCongruence : RingCon (NatProvPolynomial X) where
    r := fun p q => drop_exponents p = drop_exponents q
    iseqv := { refl := by aesop, symm := by aesop, trans := by aesop }
    add' := by
      intros w x y z wRx yRz; simp at *
      sorry
    mul' := by
      intros w x y z wRx yRz; simp at *
      sorry

  /-- Trio[X] is the quotient of ℕ[X] by the "same exponent
  after drop" congruence relation -/
  def Trio := RingCon.Quotient (NatPolyCongruence X)

end provenance

/-- All positive semirings have an epimorphism onto Bool -/
def positive_imp_surj_Bool {K : Type} [Semiring K] [pos : PosSemiring K] [dec : DecidableEq K] : K →+* Bool := by
  let f (k : K) : Bool := decide (k ≠ 0)
  have zero_of_f_false (k : K) (eq : f k = false) : k = 0 := by {
    unfold f at eq; rw [decide_not, Bool.not_eq_false'] at eq
    apply of_decide_eq_true eq
  }
  have add_eq_or {b1 b2 : Bool} : b1 + b2 = or b1 b2 := by rfl
  have mul_eq_and {b1 b2 : Bool} : b1 * b2 = and b1 b2 := by rfl
  have map_one : f 1 = true :=
    by unfold f; rw [decide_eq_true_eq]; exact pos.zero_ne_one
  have map_zero : f 0 = false :=
    by unfold f; apply decide_eq_false; aesop
  have map_add (a b : K) : f (a + b) = f a + f b := by {
    rcases (Decidable.em (f a = true)) with fa_t | fa_f
    . rcases (Decidable.em (f b = true)) with fb_t | fb_f
      . rw [fa_t, fb_t]; unfold f at *; simp
        rw [decide_eq_true_eq] at *
        rw [add_eq_or]; simp; intro H
        cases (pos.eq_zero_or_eq_zero_of_add_eq_zero H) with
        | inl l => contradiction
        | inr r => contradiction
      . rw [fa_t]; unfold f at *;
        rw [Bool.not_eq_true] at fb_f
        apply zero_of_f_false at fb_f; subst b; rw [add_zero, fa_t]
        simp; change ((true || false) = true); simp
    . rcases (Decidable.em (f b = true)) with fb_t | fb_f
      . rw [Bool.not_eq_true] at fa_f; apply zero_of_f_false at fa_f;
        subst fa_f; rw [zero_add, map_zero, fb_t]; rfl
      . rw [Bool.not_eq_true] at *
        apply zero_of_f_false at fa_f; apply zero_of_f_false at fb_f
        subst a b; rw [add_zero, map_zero]; rfl
  }
  have map_mul (a b : K) : f (a * b) = f a * f b := by {
    rcases (Decidable.em (f a = true)) with fa_t | fa_f
    . rcases (Decidable.em (f b = true)) with fb_t | fb_f
      . rw [fa_t, fb_t]; unfold f at *; simp
        rw [decide_eq_true_eq] at *
        rw [mul_eq_and]; simp; aesop
      . rw [fa_t]; unfold f at *;
        rw [Bool.not_eq_true] at fb_f
        apply zero_of_f_false at fb_f; subst b; rw [mul_zero]; rfl
    . rcases (Decidable.em (f b = true)) with fb_t | fb_f
      . rw [Bool.not_eq_true] at fa_f; apply zero_of_f_false at fa_f;
        subst fa_f; rw [zero_mul, map_zero, fb_t]; rfl
      . rw [Bool.not_eq_true] at *
        apply zero_of_f_false at fa_f; apply zero_of_f_false at fb_f
        subst a b; rw [mul_zero, map_zero]; rfl
  }
  exact {
    toFun := f,
    map_one' := map_one,
    map_zero' := map_zero,
    map_add' := map_add,
    map_mul' := map_mul
  }


variable {X : Type}

@[simp]
abbrev Why (X : Type) := Set (Set X)

instance Why.instZero : Zero (Why X) where
  zero := (∅ : Set (Set X))

instance Why.instAdd : Add (Why X) where
  add := Set.union

lemma Why.add_def {A B : Why X} : A + B = A ∪ B := by rfl

instance Why.instAddCommMonoid : AddCommMonoid (Why X) where
  add := Set.union
  add_assoc := Set.union_assoc
  zero := (∅ : Set (Set X))
  zero_add := Set.empty_union
  add_zero := Set.union_empty
  nsmul := nsmulRec
  add_comm := Set.union_comm

instance Why.instOne : One (Why X) where
  one := Set.singleton ∅

instance Why.instMul : Mul (Why X) where
  mul := fun (A B : Set (Set X)) => { s | ∃ a ∈ A, ∃ b ∈ B, s = a ∪ b}

lemma Why.mul_def {A B : Why X} : A * B = { s | ∃ a ∈ A, ∃ b ∈ B, s = a ∪ b} := by rfl

instance Why.instCommMonoid : CommMonoid (Why X) where
  mul_comm := by
    intros A B; repeat rw [Why.mul_def]
    apply Set.ext; intro x; rw [Set.mem_setOf_eq]; rw [Set.mem_setOf_eq]
    apply Iff.intro
    . rintro ⟨a1, a1_mem, b1, b1_mem, eq1⟩; aesop
    . rintro ⟨b1, b1_mem, a1, a1_mem, eq1⟩; aesop
  mul_assoc := by
    intros A B C; repeat rw [Why.mul_def]
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
  mul_one := by
    intros A; apply Set.ext; intro x; apply Iff.intro
    . rintro ⟨a, a_mem, e, e_mem, eq⟩
      rw [Set.mem_singleton_iff.mp e_mem] at eq; aesop
    . intro x_mem; exists x; split_ands; exact x_mem; exists ∅; aesop
  one_mul := by
    intros A; apply Set.ext; intro x; apply Iff.intro
    . rintro ⟨a, a_mem, e, e_mem, eq⟩
      rw [Set.mem_singleton_iff.mp a_mem] at eq; aesop
    . intro x_mem; exists ∅; split_ands; rfl; exists x; aesop

instance Why.instCommSemiring : CommSemiring (Why X) where
  zero_mul := by
    intros A; rw [Why.mul_def]
    apply Set.ext; intro x; rw [Set.mem_setOf_eq]
    apply Iff.intro <;> rintro ⟨z, ⟨z_mem, _⟩⟩; contradiction
  mul_zero := by
    intros A; rw [Why.mul_def]
    apply Set.ext; intro x; rw [Set.mem_setOf_eq]
    apply Iff.intro <;> rintro ⟨_, ⟨_, ⟨z, ⟨z_mem,  _⟩ ⟩⟩⟩; contradiction
  left_distrib := by
    intros A B C; repeat rw [Why.mul_def]; repeat rw [Why.add_def]
    apply Set.ext; intro x; apply Iff.intro
    . rw [Set.mem_setOf_eq]
      rintro ⟨a, a_mem, bc, bc_mem, eq⟩
      cases bc_mem with
      | inl bc_b => left; rw [Set.mem_setOf_eq]; aesop
      | inr bc_c => right; rw [Set.mem_setOf_eq]; aesop
    . intro x_mem; cases x_mem with
      | inl bc_b => rw [Set.mem_setOf_eq] at *; aesop
      | inr bc_c => rw [Set.mem_setOf_eq] at *; aesop
  right_distrib := by
    intros A B C; repeat rw [Why.mul_def]; repeat rw [Why.add_def]
    apply Set.ext; intro x; apply Iff.intro
    . rw [Set.mem_setOf_eq]
      rintro ⟨ab, ab_mem, c, c_mem, eq⟩
      cases ab_mem with
      | inl ab_a => left; rw [Set.mem_setOf_eq]; aesop
      | inr ab_b => right; rw [Set.mem_setOf_eq]; aesop
    . intro x_mem; cases x_mem with
      | inl ab_a => rw [Set.mem_setOf_eq] at *; aesop
      | inr ab_b => rw [Set.mem_setOf_eq] at *; aesop
  mul_comm := mul_comm
  mul_assoc := mul_assoc
  mul_one := mul_one
  one_mul := one_mul
