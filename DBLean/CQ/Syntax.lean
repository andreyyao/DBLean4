/-
! This module contains the basic definitions for defining the
! syntax of a conjunctive query
-/
import Mathlib.Data.Finset.Basic

section query_syntax
    /- Schema -/
    structure schema where
        relSym : Type
        arities : relSym -> Nat

    variable (sig : schema)

    /- Variables, i.e. x, y, z, w -/
    variable (vars : Type)

    /-! An atom -/
    def atom : Type := Σ (R : sig.relSym), (Fin (sig.arities R) -> vars)

    structure query where
        head : List vars
        body : List (atom sig vars)
end query_syntax
