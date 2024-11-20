import Mathlib.Order.Defs
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Order.BooleanAlgebra
import Mathlib.Order.Lattice
import DBLean.CQ
import DBLean.Utils
import DBLean.Semirings
import DBLean.Lattices

variable {S : Schema}
variable {V : Type}
variable {outs : Nat}

open CQ_syntax

/-- A UCQ is a list of CQ's with the same variable set and output arity -/
@[reducible] /- Makes the definition transparent -/
def UCQ V outs := List (@CQ S V outs)/- Do all parts of the union need the same output arity?-/

namespace UCQ_set_semantics

  variable {D : Type}
  variable {adom : Set D}

  def Instance := @CQ_semantics.Instance

  open Set
  def set_semantics (qs : @UCQ S V outs) (I : @Instance S D) : Set (@Vect outs D) :=
  { t |
    ∃ q ∈ qs,
    ∃ v : V -> D,
    Vect.map v q.head = t /\
    ∀ A ∈ q.body, (Vect.map v A.vars) ∈ (I A.R) }

end UCQ_set_semantics

namespace UCQ_semiring_semantics
  variable {V : Type} [Fintype V]
  variable {V1 : Type} [Fintype V1]
  variable {V2 : Type} [Fintype V2]
  variable {D : Type} [Fintype D]
  /- Semiring K -/
  variable {K : Type}
  variable [Semiring K]

  structure tuple where
    R : S.relSym
    val : @Vect (S.arities R) adom

  def valuation := V -> D

  /-- An instance is a map from a relation symbol to its corresponding K-relation. -/
  def Instance := Π (R : S.relSym), @Vect (S.arities R) D -> K

  noncomputable
  def CQ_semiring_semantics (q : @CQ S V outs) (I : @Instance S D K) (t : @Vect outs D) : K :=
    let valuations := { v : V -> D | Vect.map v q.head = t }
    let valuations' := Set.Finite.toFinset (finite_impl_finite_set valuations)
    ∑ v ∈ valuations', List.foldl (fun (acc : K) (A : Atom S V) => acc * (I A.R (Vect.map v A.vars))) 1 q.body

  noncomputable
  def semiring_semantics (qs : @UCQ S V outs) (I : @Instance S D K) :=
   fun (t : @Vect outs D) =>
    List.foldl (fun acc q => acc + (CQ_semiring_semantics q I t)) 0 qs

  def contained (qs1 : @UCQ S V1 outs) (qs2 : @UCQ S V2 outs) :=
    ∀ (I : Instance) (t : @Vect outs D),
    (natural_order K) (semiring_semantics qs1 I t) (semiring_semantics qs2 I t)

end UCQ_semiring_semantics

open UCQ_semiring_semantics

variable {outs : Nat}
variable {K : Type} variable [Semiring K]
variable {K1 : Type} variable [Semiring K1]
variable {K2 : Type} variable [Semiring K2]
variable {V : Type} [Fintype V]
variable {V1 : Type} [Fintype V1]
variable {V2 : Type} [Fintype V2]
variable {D : Type} [Fintype D]
variable {S : Schema}
variable (I : @UCQ_set_semantics.Instance S D)
variable (dec : ∀ (R : S.relSym) (t : @Vect (S.arities R) D), Decidable (t ∈ I R))

/- Provided that a UCQ instance I maps each R to a set with decidable membership,
 - annotate_with_bool is the UCQ semiring semantics that is the indicator function
 - on each tuple corresponding to its membership in I -/
def annotate_with_bool : @Instance S D Bool :=
  fun (R : S.relSym) (t : @Vect (S.arities R) D) => t ∈ I R


/-- For any boolean UCQ `qs`, instance `I`, and tuple `t`, if `t` is an element
of the set semantics of UCQ of `qs` and `I`, then under the semiring semantics
applied to Bool, `qs(I)(t)` has the value `true` -/
lemma set_semantics_impl_bool_semiring_semantics :
  ∀ (qs : @UCQ S V outs) (t : @Vect outs D),
  t ∈ UCQ_set_semantics.set_semantics qs I →
  semiring_semantics qs (annotate_with_bool I dec) t = true := by
  intros qs t t_mem
  unfold UCQ_set_semantics.set_semantics at t_mem
  rw [Set.mem_setOf_eq] at t_mem
  rcases t_mem with ⟨q, ⟨q_mem, ⟨v, ⟨head_cond, body_cond⟩⟩⟩⟩
  unfold semiring_semantics
  have hehe : CQ_semiring_semantics q (annotate_with_bool I dec) t = true := by
    unfold CQ_semiring_semantics; simp
    apply entry_true_impl_bool_summation_true
    exists v; simp; apply And.intro
    . exact head_cond
    . apply forall_top_impl_list_fold_top; intros A A_mem
      specialize body_cond A A_mem
      unfold annotate_with_bool; aesop
  induction qs with
  | nil => contradiction
  | cons hd tl IHtl => simp; simp at q_mem; cases q_mem with
    | inl eq =>
      rw [<- eq]; rw [hehe]; apply list_fold_lattice_top
    | inr mem =>
      specialize IHtl mem; clear mem;
      cases (CQ_semiring_semantics hd (annotate_with_bool I dec) t)
      . exact IHtl
      . apply list_fold_lattice_top


/-- For any boolean UCQ `qs`, instance `I`, and tuple `t`, if under the semiring
semantics applied to Bool, `qs(I)(t)` has the value `true`, then `t` is an
element of the set semantics of UCQ of `qs` and `I` -/
lemma bool_semiring_semantics_impl_set_semantics :
  ∀ (qs : @UCQ S V outs) (t : @Vect outs D),
  semiring_semantics qs (annotate_with_bool I dec) t = true →
  t ∈ UCQ_set_semantics.set_semantics qs I := by
  intros qs t eq
  unfold semiring_semantics CQ_semiring_semantics at eq
  apply list_fold_true_impl_exists_top at eq
  rcases eq with ⟨q, ⟨q_mem, isT⟩⟩; simp at isT
  apply bool_summation_true_impl_entry_true at isT; simp at isT
  rcases isT with ⟨v, ⟨head_cond, body_cond⟩⟩
  apply list_fold_top_impl_forall_top at body_cond
  unfold UCQ_set_semantics.set_semantics
  rw [Set.mem_setOf_eq]
  exists q, q_mem, v; apply And.intro
  . exact head_cond
  . intro A A_mem; specialize body_cond A A_mem;
    unfold annotate_with_bool at body_cond; aesop


/-- For any boolean UCQ `qs`, instance `I`, and tuple `t`, `qs(I)(t)` has the
value `true` under the semiring semantics applied to Bool if and only if
`t` is an element of the set semantics of UCQ of `qs` and `I` -/
theorem set_semantics_iff_bool_semantics :
∀ (qs : @UCQ S V outs) (t : @Vect outs D),
  semiring_semantics qs (annotate_with_bool I dec) t = true ↔
  t ∈ UCQ_set_semantics.set_semantics qs I := by
  intros qs t; apply Iff.intro
  . apply bool_semiring_semantics_impl_set_semantics
  . apply set_semantics_impl_bool_semiring_semantics

/-- `R1 ≤K; R2` the containment relation between two K-relations -/
def KRel.contained [NatOrdSemiring K] (R1 R2 : @Vect outs D -> K) :=
  ∀ t : @Vect outs D, (R1 t) ≤ (R2 t)

/-- `Q1 ⊑K; Q2` is containment of queries wrt semiring K -/
@[simp]
def UCQ_semiring_contains (K : Type) [NatOrdSemiring K] (Q1 : @UCQ S V1 outs) (Q2 : @UCQ S V2 outs) :=
  ∀ (I : @Instance S D K), (KRel.contained (semiring_semantics Q1 I) (semiring_semantics Q2 I))

/-- A map `f : K1 -> K2` applied to a K1-relation `R1` is a K2-relation -/
@[simp]
def KRel.map (f : K1 -> K2) (R1 : @Vect outs D -> K1) : @Vect outs D -> K2 :=
  fun t => f (R1 t)

@[simp]
def Instance.map (f : K1 -> K2) (I : @Instance S D K1) : @Instance S D K2 :=
  fun R (t : @Vect (S.arities R) D) => f (I R t)

/-- `K1⇒K2` means that for any UCQ's and instances, containment wrt `K1`
determines containment wrt `K2` -/
def K_determines (K1 K2 : Type) [NatOrdSemiring K1] [NatOrdSemiring K2] :=
  ∀ (Q1 : @UCQ S V1 outs) (Q2 : @UCQ S V2 outs),
  @UCQ_semiring_contains _ _ _ _ _ D _ _ K1 _ Q1 Q2 →
  @UCQ_semiring_contains _ _ _ _ _ D _ _ K2 _ Q1 Q2

lemma homomorphism_KRel_map_commute {n : ℕ} {D : Type} {KR : @Vect n D -> K1} {hom : RingHom K1 K2} (t : @Vect n D) :
  KRel.map hom KR t = hom (KR t) := by rfl

lemma homomorphism_semantics_commute_CQ {q : @CQ S V outs} {I : @Instance S D K1} {hom : RingHom K1 K2} :
  CQ_semiring_semantics q (Instance.map hom I) = KRel.map hom (CQ_semiring_semantics q I) := by
  unfold CQ_semiring_semantics KRel.map; simp; funext
  induction q.body with
  | nil => simp
  | cons hd tl _ =>
    simp; rw [Finset.sum_congr]; simp; intros _ _; rw [List.foldl_hom]
    intros k A; aesop

/-- Prop 6.1 from "Containment of conjunctive queries on annotated relations" -/
lemma homomorphism_semantics_commute {Q : @UCQ S V outs} {I : @Instance S D K1} {hom : RingHom K1 K2} :
  semiring_semantics Q (Instance.map hom I) = KRel.map hom (semiring_semantics Q I) := by
  unfold semiring_semantics KRel.map; simp; funext t
  induction Q with
  | nil => simp
  | cons hd tl _ =>
    simp; rw [homomorphism_semantics_commute_CQ]; simp; rw [List.foldl_hom]
    intros k A; rw [map_add]
    rw [<- homomorphism_KRel_map_commute, homomorphism_semantics_commute_CQ]

/-- Lemma 6.2 from "Containment of conjunctive queries on annotated relations" -/
lemma epimorphism_imp_determines {D : Type} [Fintype D] (K1 K2 : Type) [NatOrdSemiring K1] [NatOrdSemiring K2]
  (hom : RingHom K1 K2) (surj : Function.Surjective hom)
  : @K_determines outs V1 _ V2 _ D _ S K1 K2 _ _ := by
  unfold K_determines UCQ_semiring_contains KRel.contained;
  intros Q1 Q2 query_contains; intros J t
  let I : @Instance S D K1 :=
    fun R (t : @Vect (S.arities R) D) => Function.surjInv surj (J R t)
  have map_I_J : J = Instance.map hom I := by
    unfold Instance.map; funext R t; unfold I; rw [Function.surjInv_eq surj]
  specialize query_contains I t
  rw [map_I_J]
  rw [homomorphism_semantics_commute, homomorphism_KRel_map_commute]
  rw [homomorphism_semantics_commute, homomorphism_KRel_map_commute]
  apply homomorphism_monotone; exact query_contains
