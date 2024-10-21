/-
! This module contains the basic definitions for defining the
! syntax of a conjunctive query
-/
import Mathlib.Data.Finset.Basic
import DBLean.Utils

/- The type of database schema -/
structure Schema where
  relSym : Type
  arities : relSym -> Nat

variable {S : Schema}
/- The output arity -/
variable {outs : Nat}
variable (vars : Type)


namespace CQ_syntax

  structure Atom where
    R : S.relSym
    var_list : @Vect (S.arities R) vars

  structure CQ where
    head : @Vect outs vars
    body : List (@Atom S vars)

  def Atom.map {vars1 vars2 : Type} (f : vars1 -> vars2) (A : @Atom S vars1) : @Atom S vars2 :=
  { R := A.R, var_list := Vect.map f A.var_list }

  class homomorphism {vars1 vars2 : Type} (q1 : @CQ S outs vars1) (q2 : @CQ S outs vars2) where
    f : vars1 -> vars2
    body_cond : List.Forall (fun (A : Atom vars1) => q2.body.Mem (Atom.map f A)) q1.body
    /- https://proofassistants.stackexchange.com/questions/1740/given-a-b-how-to-prove-a-a-also-has-type-b-in-lean-4 -/
    head_cond : q2.head = cast (len_transport outs_eq) (Vect.map f q1.head)

end CQ_syntax


namespace CQ_semantics

  variable {S : Schema}
  variable {vars : Type}
  /- The active domain is a subset of the domain -/
  variable {dom : Type} {adom : Set dom}

  /- An instance is a set of vectors of the right arity for each relational symbol -/
  def Instance := Π (R : S.relSym), Set (@Vect (S.arities R) adom)

  open Set CQ_syntax
  def semantics (q : @CQ S outs vars) (I : @Instance S dom adom) : Set (@Vect outs adom) :=
    { t | ∃ v : vars -> adom,
          Vect.map v q.head = t /\
          ∀ A ∈ q.body, (Vect.map v A.var_list) ∈ (I A.R) }

  def leq (q1 q2 : @CQ S outs vars) := ∀ I : @Instance S dom adom, (semantics q1 I) ⊆ (semantics q2 I)

end CQ_semantics


open CQ_syntax CQ_semantics

lemma homomorphism_1_2 : ∀ (q1 q2 : @CQ S outs vars) (I : @Instance S dom adom), [homomorphism q1 q2] -> @leq _ _ _ dom adom q1 q2 := by
  intros q1 q2 I h
  #check h.f
  sorry
