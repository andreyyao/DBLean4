/-
! This module contains the basic definitions for defining the
! syntax of a conjunctive query
-/
import DBLean.Utils

/-- The type of database schema specifies a collection of relational symbols
as well as their arities -/
structure Schema where
  relSym : Type
  arities : relSym -> Nat

variable (S : Schema)
/- The output arity -/
variable {outs : Nat}
variable {V V1 V2 : Type}
-- variable (vars : Set V) (vars1 : Set V1) (vars2 : Set V2)

namespace CQ_syntax

  /-- An Atom is a relation symbol with list of variables of the right arity -/
  structure Atom where
    R : S.relSym
    var_vec : @Vect (S.arities R) V

  structure CQ where
    head : @Vect outs V
    body : List (@Atom S V)

  def Atom.map (f : V1 -> V2) (A : @Atom S V1) : @Atom S V2 :=
  { R := A.R, var_vec := Vect.map f A.var_vec }

  class homomorphism (q1 : @CQ S outs V1) (q2 : @CQ S outs V2) where
    f : vars1 -> vars2
    body_cond : List.Forall (fun (A : Atom S) => q2.body.Mem (Atom.map S f A)) q1.body
    head_cond : q2.head = Vect.map f q1.head

end CQ_syntax


namespace CQ_semantics

  variable {S : Schema}
  /- Variable names -/
  variable {V : Type}
  /- The active domain is a subset of the domain -/
  variable {D : Type}

  /-- An instance is a set of vectors of the right arity for each relational symbol -/
  def Instance := Π (R : S.relSym), Set (@Vect (S.arities R) D)

  open Set CQ_syntax
  /-- The semantics is a set of output tuples obtained by valuations-/
  def semantics (q : @CQ S outs V) (I : @Instance S D) : Set (@Vect outs D) :=
  { t |
    ∃ v : V -> D,
    t = Vect.map v q.head /\
    ∀ A ∈ q.body, (Vect.map v A.var_vec) ∈ (I A.R) }

  def contained (q1 q2 : @CQ S outs V) := ∀ I : @Instance S D, (semantics q1 I) ⊆ (semantics q2 I)

end CQ_semantics


open CQ_syntax CQ_semantics Set

lemma helper {R1 R2 : S.relSym} {A : Type} (eq : R1 = R2) : @Vect (S.arities R1) A = @Vect (S.arities R2) A := by rw [eq]

def canonical_DB (q : @CQ S outs V) : @Instance S V :=
  fun (R : S.relSym) =>
  { t : @Vect (S.arities R) V |
    ∃ A ∈ q.body, ∃ (eq : A.R = R), t = cast (helper S eq) A.var_vec }

-- lemma homomorphism_1_2 : ∀ (q1 : @CQ S outs V1 vars1) (q2 : @CQ S outs V2 vars2) (I : @Instance S dom adom), [homomorphism S vars1 vars2 q1 q2] -> @contained _ _ _ _ dom adom q1 q2 := by
