import DBLean.CQ
import DBLean.Utils
import Mathlib.Order.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.BigOperators.Finprod

variable {S : Schema}
/- The output arity -/
variable {V : Type}
variable {outs : Nat}

open CQ_syntax

/-- A UCQ is a list of CQ's with the same variable set and output arity -/
@[reducible] /- Makes the definition transparent -/
def UCQ := List (@CQ S V outs)

namespace UCQ_set_semantics

  variable {D : Type}
  variable {adom : Set D}

  def Instance := @CQ_semantics.Instance

  open Set
  def set_semantics (qs : @UCQ S V outs) (I : @Instance S D) : Set (@Vect outs D) :=
  { t |
    ∃ q ∈ qs,
    ∃ v : V -> D,
    Vect.map v q.head = t /\
    ∀ A ∈ q.body, (Vect.map v A.vars) ∈ (I A.R) }

end UCQ_set_semantics

namespace UCQ_semiring_semantics
  variable {V : Type}
  variable {D : Type}
  variable (V_fin : Finite V) (D_fin : Finite D)
  /- Semiring K -/
  variable {K : Type}
  variable [K_SR : Semiring K]

  structure tuple where
    R : S.relSym
    val : @Vect (S.arities R) adom

  def valuation := V -> D

  /-- An instance is a map from a relation symbol to its corresponding K-relation. -/
  def Instance := Π (R : S.relSym), @Vect (S.arities R) D -> K

  noncomputable
  def semiring_semantics (q : CQ V outs) (I : Instance) (t : @Vect outs D) :=
    let valuations := { v : V -> D | Vect.map v q.head = t }
    let valuations' := Set.Finite.toFinset (finite_impl_finite_set valuations)
    Finset.sum valuations' (fun v : V -> D => List.foldl (fun (acc : K) (A : Atom S V) => acc + (I A.R (Vect.map v A.vars))) 0 q.body)

  def natural_order (K : Type) [Semiring K] : K -> K -> Prop :=
    fun (a b : K) => ∃ (c : K), a + c = b

  instance : Preorder K where
    le := natural_order K
    le_refl := by intro a; exists 0; simp
    le_trans := by
      intros a b c le1 le2
      let ⟨k1, E1⟩ := le1
      let ⟨k2, E2⟩ := le2
      exists (k1 + k2)
      rw [<- K_SR.add_assoc]
      rw [E1]
      exact E2

  -- def contained (q1 : CQ V1 outs) (q2 : CQ V2 outs) := sorry

end UCQ_semiring_semantics
