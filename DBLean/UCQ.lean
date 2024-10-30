import DBLean.CQ
import DBLean.Utils
import Mathlib.Order.Defs
import Mathlib.Algebra.Ring.Defs
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
def UCQ V outs := List (@CQ S V outs)

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
  variable [K_SR : Semiring K]

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
    valuations'.sum (fun v : V -> D => List.foldl (fun (acc : K) (A : Atom S V) => acc * (I A.R (Vect.map v A.vars))) 1 q.body)

  noncomputable
  def semiring_semantics (qs : @UCQ S V outs) (I : @Instance S D K) (t : @Vect outs D) : K :=
    List.foldl (fun acc q => acc + (CQ_semiring_semantics q I t)) 0 qs

  @[simp]
  def natural_order (K : Type) [Semiring K] : K -> K -> Prop :=
    fun (a b : K) => ∃ (c : K), a + c = b

  instance KIsPreorder : IsPreorder K (natural_order K) where
    refl := by intro a; exists 0; simp
    trans := by
      intros a b c le1 le2
      let ⟨k1, E1⟩ := le1
      let ⟨k2, E2⟩ := le2
      exists (k1 + k2)
      rw [<- K_SR.add_assoc]
      rw [E1]
      exact E2

  instance : Preorder K where
    le := natural_order K
    le_refl := KIsPreorder.refl
    le_trans := KIsPreorder.trans

  def naturally_ordered := IsPartialOrder K (natural_order K)

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
variable {V : Type} [Fintype V]
variable {D : Type} [Fintype D]
variable {S : Schema} {D : Type}
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
  rcases ex with ⟨s, eq⟩
  rw [Finset.sum_eq_fold]
  apply Eq.symm
  have and_true_eq : ∀ b : Bool, true && b → true = b := by
    intros b eq; rw [<- eq]; rfl
  apply and_true_eq
  apply (@Finset.fold_op_rel_iff_or D Bool or _ _ f false S (fun (b1 b2 : Bool) => b1 && b2) _ true).2
  right; aesop
  /- Going back to prove this proof obligation -/
  intros x y z; simp
  apply Iff.intro
  . intro H; cases x <;> cases y <;> cases z <;> simp at H <;> aesop
  . intro H; cases x <;> cases y <;> cases z <;> aesop

lemma list_fold_lattice_top {α β : Type} [DistribLattice α] [BoundedOrder α] :
  ∀ (f : β -> α) (l : List β), List.foldl (fun acc e => acc ⊔ f e) ⊤ l = ⊤ := by
  intros f l
  induction l with
  | nil => rfl
  | cons hd tl IH => simp; exact IH

/-- For any boolean UCQ `qs`, instance `I`, and tuple `t`, if `t` is an element
of the set-semantics of UCQ of `qs` and `I`, then under the semiring semantics
applied to Booleans, `qs(I)(t)` has the value `true` -/
lemma set_semantics_impl_bool_semiring_semantics [Fintype D] :
  ∀ (qs : @UCQ S V outs) (R : S.relSym) (t : @Vect outs D),
  t ∈ UCQ_set_semantics.set_semantics qs I →
  semiring_semantics qs (annotate_with_bool I dec) t = true := by
  intros qs _ t t_mem
  unfold UCQ_set_semantics.set_semantics at t_mem
  rw [Set.mem_setOf_eq] at t_mem
  rcases t_mem with ⟨q, ⟨q_mem, ⟨v, ⟨head_cond, body_cond⟩⟩⟩⟩
  unfold semiring_semantics
  have hehe : CQ_semiring_semantics q (annotate_with_bool I dec) t = true := by
    unfold CQ_semiring_semantics; simp
    apply entry_true_impl_bool_summation_true
    exists v; simp; apply And.intro
    . exact head_cond
    . generalize q.body = atoms at *; induction atoms with
      | nil => rfl
      | cons hd tl IHtl =>
        simp
        simp at body_cond; rcases body_cond with ⟨hd_cond, tl_cond⟩
        have eq : annotate_with_bool I dec hd.R (Vect.map v hd.vars) = 1 := by
          unfold annotate_with_bool; aesop
        rw [eq]; apply IHtl; aesop
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


lemma bool_semiring_semantics_impl_set_semantics [Fintype D] :
  ∀ (qs : @UCQ S V outs) (R : S.relSym) (t : @Vect outs D),
  semiring_semantics qs (annotate_with_bool I dec) t = true →
  t ∈ UCQ_set_semantics.set_semantics qs I := by
  intros qs R t eq
  sorry



theorem set_semantics_iff_bool_semantics : True
