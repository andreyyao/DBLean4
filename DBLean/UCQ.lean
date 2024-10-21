import DBLean.CQ

variable {S : Schema}
/- The output arity -/
variable {outs : Nat}
variable (vars : Type)

open CQ_syntax

/-- A UCQ is a list of CQ's with the same variable set and output arity -/
@[reducible] /- Makes the definition transparent -/
def UCQ := List (@CQ S outs vars)

section semantics

  def Instance := CQ_semantics.Instance

  open Set
  def semantics (qs : @UCQ S outs vars) (I : Instance S adom) : Set (@Vect outs adom) :=
    { t | ∃ q ∈ qs,
          ∃ v : vars -> adom,
          Vect.map v q.head = t /\
          ∀ A ∈ q.body, (Vect.map v A.var_list) ∈ (I A.R) }

end semantics
