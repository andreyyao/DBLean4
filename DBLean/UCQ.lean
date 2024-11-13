import DBLean.CQ
import DBLean.Utils
import Mathlib.Order.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Order.BooleanAlgebra
import Mathlib.Order.Lattice

variable {S : Schema}
/- The output arity -/
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
    let valuations := { v : V -> D | Vect.map v q.head = t }/-Why more than 1? -/
    let valuations' := Set.Finite.toFinset (finite_impl_finite_set valuations)
    valuations'.sum (fun v : V -> D => List.foldl (fun (acc : K) (A : Atom S V) => acc * (I A.R (Vect.map v A.vars))) 1 q.body)

  noncomputable
  def semiring_semantics (qs : @UCQ S V outs) (I : @Instance S D K) :=
   fun (t : @Vect outs D) =>
    List.foldl (fun acc q => acc + (CQ_semiring_semantics q I t)) 0 qs

  def natural_order (K : Type) [Semiring K] : K -> K -> Prop :=
    fun (a b : K) => ∃ (c : K), a + c = b

  @[default_instance]
  instance instPreOrder {K : Type} [Semiring K] : Preorder K where
    le := natural_order K
    le_refl := by intro a; exists 0; simp
    le_trans := by
      intros a b c le1 le2
      let ⟨k1, E1⟩ := le1
      let ⟨k2, E2⟩ := le2
      exists (k1 + k2); rw [<- add_assoc, E1]; exact E2

  class NatOrdSemiring (K : Type) extends Semiring K where
    naturally_ordered : IsPartialOrder K (natural_order K)

  instance instPartialOrder (K : Type) [no : NatOrdSemiring K] : PartialOrder K where
    le_antisymm := by
      intros a b le_ab le_ba
      exact (no.naturally_ordered.antisymm a b le_ab le_ba)

  def contained (qs1 : @UCQ S V1 outs) (qs2 : @UCQ S V2 outs) :=
    ∀ (I : Instance) (t : @Vect outs D),
    (natural_order K) (semiring_semantics qs1 I t) (semiring_semantics qs2 I t)

end UCQ_semiring_semantics

@[simp]
def Bool.nsmul : Nat -> Bool -> Bool
| .zero => fun _ => false
| .succ n => fun b => b || (Bool.nsmul n b)

instance : Semiring Bool where
  add := or
  add_assoc := by intros; exact Bool.or_assoc _ _ _
  zero := false
  zero_add := by intros; exact Bool.false_or _
  add_zero := by intros; exact Bool.or_false _
  add_comm := by intros; exact Bool.or_comm _ _
  mul := and
  mul_assoc := by intros; exact Bool.and_assoc _ _ _
  one := true
  one_mul := by intros; exact Bool.true_and _
  mul_one := by intros; exact Bool.and_true _
  left_distrib := by intros; exact Bool.and_or_distrib_left _ _ _
  right_distrib := by intros; exact Bool.and_or_distrib_right _ _ _
  zero_mul := by intros; exact Bool.false_and _
  mul_zero := by intros; exact Bool.and_false _
  nsmul := Bool.nsmul
  nsmul_zero := by intro b; rfl
  nsmul_succ := by intros n b; simp; rw [Bool.or_comm]; rfl

instance : BoundedOrder Bool := by infer_instance

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

lemma entry_true_impl_bool_summation_true {D : Type}: ∀ (S : Finset D) (f : D -> Bool),
  (∃ s ∈ S, f s = true) → (S.sum f = true) := by
  intros S f ex
  apply Finset.sup_eq_top_iff.mpr at ex
  exact ex

lemma bool_summation_true_impl_entry_true {D : Type}: ∀ (S : Finset D) (f : D -> Bool),
  (S.sum f = true) → (∃ s ∈ S, f s = true) := by
  intros S f eq;
  rw [Finset.sum_eq_fold] at eq
  exact Finset.sup_eq_top_iff.mp eq /-Huh, nice find-/

lemma list_fold_lattice_top {α β : Type} [DistribLattice α] [OrderTop α] :
  ∀ (f : β -> α) (l : List β), List.foldl (fun acc e => acc ⊔ f e) ⊤ l = ⊤ := by
  intros f l
  induction l with
  | nil => rfl
  | cons hd tl IH => simp; exact IH

lemma list_fold_lattice_bot {α β : Type} [DistribLattice α] [OrderBot α] :
  ∀ (f : β -> α) (l : List β), List.foldl (fun acc e => acc ⊓ f e) ⊥ l = ⊥ := by
  intros f l
  induction l with
  | nil => rfl
  | cons hd tl IH => simp; exact IH

lemma list_fold_true_impl_exists_true {β : Type} : ∀ (f : β -> Bool) (l : List β),
  List.foldl (fun acc e => acc + f e) 0 l = 1 →
  ∃ e ∈ l, f e = 1 := by
  intros f l eq; induction l with
  | nil => contradiction
  | cons hd tl IHtl => simp; cases val : (f hd) with
    | true => aesop
    | false => right; aesop

lemma list_fold_init_lt_top_impl_lt_top {α β : Type} [DistribLattice β] [OrderTop β] :
  ∀ (f : α -> β) (l : List α) (i : β), i < ⊤ →
  List.foldl (fun acc e => acc ⊓ f e) i l < ⊤ := by
  intros f l i lt; induction l with
  | nil => simp; exact lt
  | cons hd tl IH =>
    rw [<- List.foldl_map] at *; simp; rw [inf_comm, List.foldl_assoc] at *
    generalize List.foldl Inf.inf i (List.map f tl) = x at *
    have _ : f hd ⊓ x ≤ x := by apply inf_le_right
    have _ : x ≤ ⊤ := (le_of_lt IH)
    apply lt_of_le_of_ne
    . aesop
    . aesop

lemma list_fold_top_impl_forall_top {α β : Type} [DistribLattice β] [OrderTop β] [Dec: DecidableEq β]:
  ∀ (f : α -> β) (l : List α),
  List.foldl (fun acc e => acc ⊓ f e) ⊤ l = ⊤ →
  (∀ e ∈ l, f e = ⊤) := by
  intros f l eq; induction l with
  | nil => simp
  | cons hd tl IHtl => simp; simp at eq; cases (Dec (f hd) ⊤) with
    | isTrue h => aesop
    | isFalse h =>
      apply lt_top_iff_ne_top.mpr at h
      have fold_lt := list_fold_init_lt_top_impl_lt_top f tl (f hd) h
      aesop

lemma forall_top_impl_list_fold_top {α β : Type} [DistribLattice β] [OrderTop β] :
  ∀ (f : α -> β) (l : List α),
  (∀ e ∈ l, f e = ⊤) →
  List.foldl (fun acc e => acc ⊓ f e) ⊤ l = ⊤ := by
  intros f l H; induction l with
  | nil => rfl
  | cons hd tl IHtl =>
    simp; simp at H; rcases H with ⟨eq, alltl⟩; rw [eq]; apply IHtl alltl

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
  apply list_fold_true_impl_exists_true at eq
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
def KRel.map (R1 : @Vect outs D -> K1) (f : K1 -> K2) : @Vect outs D -> K2 :=
  fun t => f (R1 t)

/-- `K1⇒K2` means that for any UCQ's and instances, containment wrt `K1`
determines containment wrt `K2` -/
def K_determines (K1 K2 : Type) [NatOrdSemiring K1] [NatOrdSemiring K2] :=
  ∀ (Q1 : @UCQ S V1 outs) (Q2 : @UCQ S V2 outs),
  @UCQ_semiring_contains _ _ _ _ _ D _ _ K1 _ Q1 Q2 →
  @UCQ_semiring_contains _ _ _ _ _ D _ _ K2 _ Q1 Q2

-- /-- Prop. A.2 from "Containment of conjunctive queries on annotated relations" -/
-- lemma homomorphism_monotone (K1 K2 : Type) [NatOrdSemiring K1] [NatOrdSemiring K2]
--   (hom : RingHom K1 K2) : Monotone hom.toFun := by


-- /-- Lemma 6.2 from "Containment of conjunctive queries on annotated relations" -/
-- lemma epimorphism_imp_determines {D : Type} [Fintype D] (K1 K2 : Type) [NatOrdSemiring K1] [NatOrdSemiring K2]
--  (hom : RingHom K1 K2) (surj : Function.Surjective hom.toFun)
--  : @K_determines outs V1 _ V2 _ D _ S K1 K2 _ _ := by
--  unfold K_determines UCQ_semiring_contains KRel.contained;
--  intros Q1 Q2 query_contains; intros I t
--  have J : @Instance S D K2 := fun t =>
