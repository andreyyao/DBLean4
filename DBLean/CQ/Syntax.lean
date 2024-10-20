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

variable (S : Schema)

structure Atom (vars : Type) where
  R : S.relSym
  var_list : @Vect (S.arities R) vars

structure CQ where
  vars : Type
  head : List vars
  body : List (Atom sig vars)

def Atom.map {vars1 vars2 : Type} (f : vars1 -> vars2) (A : Atom S vars1) : Atom S vars2 :=
{ R := A.R, var_list := Vect.map f A.var_list }

class homomorphism (q1 q2 : CQ) where
  f : q1.vars -> q2.vars
  body_cond : List.Forall (fun (A : Atom S q1.vars) => q2.body.Mem (Atom.map S f A)) q1.body
  head_cond : q2.head = List.map f q1.head

def CQ.contained (q1 q2 : CQ) : Prop :=
    exists (_ : homomorphism S q1 q2), True
