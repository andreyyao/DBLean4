import DBLean.CQ
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.BigOperators.Finprod

variable {S : Schema}
/- The output arity -/
variable {outs : Nat}
variable {V : Type}
variable (vars : Set V)

open CQ_syntax

/-- A UCQ is a list of CQ's with the same variable set and output arity -/
@[reducible] /- Makes the definition transparent -/
def UCQ := List (@CQ S outs V vars)

namespace UCQ_set_semantics

  variable {dom : Type}
  variable {adom : Set dom}

  def Instance := @CQ_semantics.Instance

  open Set
  def set_semantics (qs : @UCQ S outs V vars) (I : @Instance S dom adom) : Set (@Vect outs adom) :=
  { t |
    ∃ q ∈ qs,
    ∃ v : vars -> adom,
    Vect.map v q.head = t /\
    ∀ A ∈ q.body, (Vect.map v A.var_vec) ∈ (I A.R) }

end UCQ_set_semantics

namespace UCQ_semiring_semantics
  variable {dom : Type}
  variable {adom : Set dom}
  variable {adom_fin : Finite adom}
  variable {vars_fin : Finite vars}
  /- Semiring K -/
  variable {K : Type}
  variable {K_SR : Semiring K}

  structure tuple where
    R : S.relSym
    val : @Vect (S.arities R) adom

  def valuation := vars -> adom

  /-- An instance is a map from a relation symbol to its corresponding K-relation. -/
  def Instance := Π (R : S.relSym), @Vect (S.arities R) adom -> K

  /- TODO change to using Finset -/
  /-- Semiring semantics for CQ -/
  @[irreducible]
  noncomputable
  def semiring_semantics (q : @CQ S outs V vars) (I : @Instance S dom adom K) (t : @Vect outs adom) :=
    let valuations := { v : vars -> adom | Vect.map v q.head = t }
    finsum (fun v : valuations => List.foldl (fun (acc : K) (A : Atom S vars) => acc + (I A.R (Vect.map v A.var_vec))) 0 q.body)



end UCQ_semiring_semantics
