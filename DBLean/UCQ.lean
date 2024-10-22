import DBLean.CQ

variable {S : Schema}
/- The output arity -/
variable {outs : Nat}
variable {V : Type}
variable (vars : Set V)

open CQ_syntax

/-- A UCQ is a list of CQ's with the same variable set and output arity -/
@[reducible] /- Makes the definition transparent -/
def UCQ := List (@CQ S outs V vars)

section UCQ_semantics

  variable {dom : Type}
  variable {adom : Set dom}

  def Instance := @CQ_semantics.Instance

  open Set
  def semantics (qs : @UCQ S outs V vars) (I : @Instance S dom adom) : Set (@Vect outs adom) :=
  { t |
    ∃ q ∈ qs,
    ∃ v : vars -> adom,
    Vect.map v q.head = t /\
    ∀ A ∈ q.body, (Vect.map v A.var_vec) ∈ (I A.R) }

end UCQ_semantics
