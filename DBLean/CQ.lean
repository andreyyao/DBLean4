/-
! This module contains the basic definitions for defining the
! syntax of a conjunctive query
-/
import DBLean.Utils

/-- The type of database schema specifies a collection of relational symbols
as well as their arities -/

structure Schema where
  relSym : Type /-Relation symbol -/
  arities : relSym -> Nat /- -/

variable {S : Schema}
/- The output arity -/
variable {outs : Nat}
variable {V V1 V2 : Type}
-- variable (vars : Set V) (vars1 : Set V1) (vars2 : Set V2)

namespace CQ_syntax

  /-- An Atom is a relation symbol with list of variables of the right arity -/
  structure Atom (S : Schema) (V : Type) where
    R : S.relSym
    vars : @Vect (S.arities R) V

  structure CQ (V : Type) (outs : Nat)  where
    head : @Vect outs V
    body : List (@Atom S V)

  def Atom.map (f : V1 -> V2) (A : Atom S V1) : Atom S V2 :=
  { R := A.R, vars := Vect.map f A.vars }

  structure homomorphism {V1 V2 : Type} (q1 : @CQ S V1 outs) (q2 : @CQ S V2 outs) (h : V1 -> V2) : Prop where
    -- body_cond : ∀ A ∈ q1.body, q2.body.Mem (Atom.map f A)
    body_cond : ∀ A ∈ q1.body, (Atom.map h A) ∈ q2.body
    head_cond : q2.head = Vect.map h q1.head

end CQ_syntax


namespace CQ_semantics

  variable {S : Schema}
  /- Variable names -/
  variable {V : Type}

  /-- An instance is a set of vectors of the right arity for each relational symbol -/
  def Instance (D : Type) := Π (R : S.relSym), Set (@Vect (S.arities R) D)

  open Set CQ_syntax

  /-- The semantics is a set of output tuples obtained by valuations-/
  def semantics {D : Type} (q : @CQ S V outs) (I : @Instance S D) : Set (@Vect outs D) :=
  { t : Vect D |
    ∃ v : V -> D,
    t = Vect.map v q.head /\
    ∀ A ∈ q.body, (Vect.map v A.vars) ∈ (I A.R) }

  @[simp]
  def contained (D : Type) (q1 : @CQ S V1 outs) (q2 : @CQ S V2 outs) :=
    ∀ (I : @Instance S D), (semantics q1 I) ⊆ (semantics q2 I)

end CQ_semantics


open CQ_syntax CQ_semantics Set

lemma helper {R1 R2 : S.relSym} {A : Type} (eq : R1 = R2) : @Vect (S.arities R1) A = @Vect (S.arities R2) A := by rw [eq]

/-- The canonical database `D[q]` of a query `[q]` -/
def canonical_DB (q : @CQ S V outs) : @Instance S V :=
  fun (R : S.relSym) =>
  { t : @Vect (S.arities R) V | { R := R , vars := t } ∈ q.body }

/-- The head of a query `q` is an element of `q(D[q])`-/
lemma head_in_canon_db_eval : ∀ (q : @CQ S V outs), q.head ∈ semantics q (canonical_DB q) := by
  intro q
  unfold semantics canonical_DB
  rw [Set.mem_setOf_eq]
  exists id;
  apply And.intro
  . rw [Vect.map_id]
  . intro A mem; rw [Vect.map_id, Set.mem_setOf_eq]
    exact mem

variable (D : Type)
variable (q1 : @CQ S V1 outs)
variable (q2 : @CQ S V2 outs)

lemma homomorphism_1_3 : contained V1 q1 q2 → q1.head ∈ semantics q2 (canonical_DB q1)  := by
  intro hypothesis
  unfold contained at hypothesis
  specialize hypothesis (canonical_DB q1)
  have h_head_q1 : q1.head ∈ semantics q1 (canonical_DB q1) := head_in_canon_db_eval q1
  exact hypothesis h_head_q1

lemma homomorphism_2_1 : (∃ h, homomorphism q2 q1 h) → contained D q1 q2 := by
  unfold contained; intros H I; rw [subset_def]; intros t mem
  obtain ⟨h, hom⟩ := H
  rw [semantics, Set.mem_setOf_eq] at mem
  rw [semantics, Set.mem_setOf_eq]
  obtain ⟨ν1, ⟨Eq, BodEq⟩⟩ := mem
  exists (ν1 ∘ h)
  apply And.intro
  . rw [Eq, hom.head_cond, Vect.comp_map]
  . intros A2 mem2
    have mem1 := hom.body_cond A2 mem2
    rw [<- Vect.comp_map]
    exact BodEq (Atom.map h A2) mem1

lemma homomorphism_3_2 : q1.head ∈ semantics q2 (canonical_DB q1) -> ∃ h, homomorphism q2 q1 h := by
  intro hypothesis
  rw [semantics, Set.mem_setOf_eq] at hypothesis
  obtain ⟨f, ⟨head_cond, body_cond⟩⟩ := hypothesis
  have body_cond_hom : ∀ A ∈ q2.body, Atom.map f A ∈ q1.body := by {
    unfold canonical_DB at body_cond
    unfold Atom.map
    intros A A_mem
    aesop
  }
  exists f; exact { head_cond := head_cond, body_cond := body_cond_hom }

theorem homomorpshim_theorem :
  (q1.head ∈ semantics q2 (canonical_DB q1) ↔ contained V1 q1 q2) ∧
  (contained V1 q1 q2 ↔ ∃ h, homomorphism q2 q1 h) := by
  apply And.intro;
  . apply Iff.intro
    . intro H; apply homomorphism_2_1; apply homomorphism_3_2; apply H
    . apply homomorphism_1_3
  . apply Iff.intro
    . intro H; apply homomorphism_3_2; apply homomorphism_1_3; apply H
    . intro H; apply homomorphism_2_1; exact H
