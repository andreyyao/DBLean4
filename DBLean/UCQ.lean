import DBLean.CQ
import DBLean.Utils
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.BigOperators.Finprod

variable {S : Schema}
/- The output arity -/
variable {outs : Nat}
variable {V : Type}

open CQ_syntax

/-- A UCQ is a list of CQ's with the same variable set and output arity -/
@[reducible] /- Makes the definition transparent -/
def UCQ := List (@CQ S outs V)

namespace UCQ_set_semantics

  variable {D : Type}
  variable {adom : Set D}

  def Instance := @CQ_semantics.Instance

  open Set
  def set_semantics (qs : @UCQ S outs V) (I : @Instance S D) : Set (@Vect outs D) :=
  { t |
    ∃ q ∈ qs,
    ∃ v : V -> D,
    Vect.map v q.head = t /\
    ∀ A ∈ q.body, (Vect.map v A.var_vec) ∈ (I A.R) }

end UCQ_set_semantics

namespace UCQ_semiring_semantics
  variable {V : Type}
  variable {D : Type}
  variable (V_fin : Finite V) (D_fin : Finite D)
  /- Semiring K -/
  variable {K : Type}
  variable {K_SR : Semiring K}

  structure tuple where
    R : S.relSym
    val : @Vect (S.arities R) adom

  def valuation := V -> D

  /-- An instance is a map from a relation symbol to its corresponding K-relation. -/
  def Instance := Π (R : S.relSym), @Vect (S.arities R) D -> K

  noncomputable
  def semiring_semantics (q : CQ S) (I : Instance) (t : @Vect outs D) :=
    let valuations := { v : V -> D | Vect.map v q.head = t }
    let valuations' := Set.Finite.toFinset (finite_impl_finite_set valuations)
    Finset.sum valuations' (fun v : V -> D => List.foldl (fun (acc : K) (A : Atom S) => acc + (I A.R (Vect.map v A.var_vec))) 0 q.body)

end UCQ_semiring_semantics
