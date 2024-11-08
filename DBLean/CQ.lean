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

  class homomorphism {V1 V2 : Type} (q1 : CQ V1 outs) (q2 : CQ V2 outs) where
    f : V1 -> V2
    -- body_cond : ∀ A ∈ q1.body, q2.body.Mem (Atom.map f A)
    body_cond : List.Forall (fun (A : Atom S V1) => q2.body.Mem (Atom.map f A)) q1.body
    head_cond : q2.head = Vect.map f q1.head

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
  { t : @Vect (S.arities R) V |
    ∃ A ∈ q.body, ∃ (eq : A.R = R), t = cast (helper eq) A.vars }

/-- The head of a query `q` is an element of `q(D[q])`-/
lemma head_in_canon_db_eval : ∀ (q : @CQ S V outs), q.head ∈ semantics q (canonical_DB q) := by
  intro q
  unfold semantics canonical_DB
  rw [Set.mem_setOf_eq]
  exists id;
  apply And.intro
  . rw [Vect.map_id]
  . intro A mem; rw [Vect.map_id, Set.mem_setOf_eq]
    exists A; aesop

variable (D : Type)
variable (q1 : @CQ S V1 outs)
variable (q2 : @CQ S V2 outs)

lemma homomorphism_1_3 :  contained V1 q1 q2 -> q1.head ∈ semantics q2 (canonical_DB q1)  := by
  intro hypothesis
  unfold contained at hypothesis
  specialize hypothesis (canonical_DB q1)
  have h_head_q1 : q1.head ∈ semantics q1 (canonical_DB q1) := head_in_canon_db_eval q1
  exact hypothesis h_head_q1

lemma homomorphism_2_1 [h : homomorphism q2 q1] : contained D q1 q2 := by
  unfold contained; intro I; rw [subset_def]; intros t mem
  rw [semantics, Set.mem_setOf_eq] at mem
  rw [semantics, Set.mem_setOf_eq]
  let ⟨ν1, ⟨Eq, BodEq⟩⟩ := mem
  exists (ν1 ∘ h.f)
  apply And.intro
  . rw [Eq, h.head_cond, Vect.comp_map]
  . intros A2 mem2
    have mem1 := List.forall_iff_forall_mem.1 h.body_cond A2 mem2
    rw [<- Vect.comp_map]
    exact BodEq (Atom.map (homomorphism.f q2 q1) A2) mem1

lemma homomorphism_3_2 :  q1.head ∈ semantics q2 (canonical_DB q1) -> ∃ h : homomorphism q2 q1, True := by
  intro hypothesis
  rw [semantics, Set.mem_setOf_eq] at hypothesis
  obtain ⟨v, ⟨head_eq, body_cond⟩⟩ := hypothesis
  let f := v

  have head_cond : q1.head = Vect.map f q2.head:= by {
    rw [head_eq]
  }

  have body_cond_hom : List.Forall (fun (A : Atom S V2) => q1.body.Mem (Atom.map f A)) q2.body:= by {
    unfold canonical_DB at body_cond
    induction' eq : q2.body
    case nil => simp
    case cons hd tl IH =>
      simp; apply And.intro
      . have hd_mem : hd ∈ q2.body := by aesop
        specialize body_cond hd hd_mem
        unfold Atom.map
        rw [Set.mem_setOf_eq] at body_cond
        rcases body_cond with ⟨A, ⟨A_mem, ⟨R_eq, Eqq⟩⟩⟩
        sorry

  }
  -- Construct the homomorphism instance and conclude the proof
  sorry
