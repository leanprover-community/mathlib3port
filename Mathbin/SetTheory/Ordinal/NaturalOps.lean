/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import SetTheory.Ordinal.Arithmetic
import Tactic.Abel

#align_import set_theory.ordinal.natural_ops from "leanprover-community/mathlib"@"31b269b60935483943542d547a6dd83a66b37dc7"

/-!
# Natural operations on ordinals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The goal of this file is to define natural addition and multiplication on ordinals, also known as
the Hessenberg sum and product, and provide a basic API. The natural addition of two ordinals
`a ♯ b` is recursively defined as the least ordinal greater than `a' ♯ b` and `a ♯ b'` for `a' < a`
and `b' < b`. The natural multiplication `a ⨳ b` is likewise recursively defined as the least
ordinal such that `a ⨳ b ♯ a' ⨳ b'` is greater than `a' ⨳ b ♯ a ⨳ b'` for any `a' < a` and
`b' < b`.

These operations form a rich algebraic structure: they're commutative, associative, preserve order,
have the usual `0` and `1` from ordinals, and distribute over one another.

Moreover, these operations are the addition and multiplication of ordinals when viewed as
combinatorial `game`s. This makes them particularly useful for game theory.

Finally, both operations admit simple, intuitive descriptions in terms of the Cantor normal form.
The natural addition of two ordinals corresponds to adding their Cantor normal forms as if they were
polynomials in `ω`. Likewise, their natural multiplication corresponds to multiplying the Cantor
normal forms as polynomials.

# Implementation notes

Given the rich algebraic structure of these two operations, we choose to create a type synonym
`nat_ordinal`, where we provide the appropriate instances. However, to avoid casting back and forth
between both types, we attempt to prove and state most results on `ordinal`.

# Todo

- Prove the characterizations of natural addition and multiplication in terms of the Cantor normal
  form.
-/


universe u v

open Function Order

noncomputable section

/-! ### Basic casts between `ordinal` and `nat_ordinal` -/


#print NatOrdinal /-
/-- A type synonym for ordinals with natural addition and multiplication. -/
def NatOrdinal : Type _ :=
  Ordinal
deriving Zero, Inhabited, One, LinearOrder, SuccOrder, WellFoundedRelation
#align nat_ordinal NatOrdinal
-/

#print Ordinal.toNatOrdinal /-
/-- The identity function between `ordinal` and `nat_ordinal`. -/
@[match_pattern]
def Ordinal.toNatOrdinal : Ordinal ≃o NatOrdinal :=
  OrderIso.refl _
#align ordinal.to_nat_ordinal Ordinal.toNatOrdinal
-/

#print NatOrdinal.toOrdinal /-
/-- The identity function between `nat_ordinal` and `ordinal`. -/
@[match_pattern]
def NatOrdinal.toOrdinal : NatOrdinal ≃o Ordinal :=
  OrderIso.refl _
#align nat_ordinal.to_ordinal NatOrdinal.toOrdinal
-/

namespace NatOrdinal

open Ordinal

variable {a b c : NatOrdinal.{u}}

#print NatOrdinal.toOrdinal_symm_eq /-
@[simp]
theorem toOrdinal_symm_eq : NatOrdinal.toOrdinal.symm = Ordinal.toNatOrdinal :=
  rfl
#align nat_ordinal.to_ordinal_symm_eq NatOrdinal.toOrdinal_symm_eq
-/

#print NatOrdinal.toOrdinal_toNatOrdinal /-
@[simp]
theorem toOrdinal_toNatOrdinal (a : NatOrdinal) : a.toOrdinal.toNatOrdinal = a :=
  rfl
#align nat_ordinal.to_ordinal_to_nat_ordinal NatOrdinal.toOrdinal_toNatOrdinal
-/

#print NatOrdinal.lt_wf /-
theorem lt_wf : @WellFounded NatOrdinal (· < ·) :=
  Ordinal.lt_wf
#align nat_ordinal.lt_wf NatOrdinal.lt_wf
-/

instance : WellFoundedLT NatOrdinal :=
  Ordinal.wellFoundedLT

instance : IsWellOrder NatOrdinal (· < ·) :=
  Ordinal.HasLt.Lt.isWellOrder

#print NatOrdinal.toOrdinal_zero /-
@[simp]
theorem toOrdinal_zero : toOrdinal 0 = 0 :=
  rfl
#align nat_ordinal.to_ordinal_zero NatOrdinal.toOrdinal_zero
-/

#print NatOrdinal.toOrdinal_one /-
@[simp]
theorem toOrdinal_one : toOrdinal 1 = 1 :=
  rfl
#align nat_ordinal.to_ordinal_one NatOrdinal.toOrdinal_one
-/

#print NatOrdinal.toOrdinal_eq_zero /-
@[simp]
theorem toOrdinal_eq_zero (a) : toOrdinal a = 0 ↔ a = 0 :=
  Iff.rfl
#align nat_ordinal.to_ordinal_eq_zero NatOrdinal.toOrdinal_eq_zero
-/

#print NatOrdinal.toOrdinal_eq_one /-
@[simp]
theorem toOrdinal_eq_one (a) : toOrdinal a = 1 ↔ a = 1 :=
  Iff.rfl
#align nat_ordinal.to_ordinal_eq_one NatOrdinal.toOrdinal_eq_one
-/

#print NatOrdinal.toOrdinal_max /-
@[simp]
theorem toOrdinal_max : (max a b).toOrdinal = max a.toOrdinal b.toOrdinal :=
  rfl
#align nat_ordinal.to_ordinal_max NatOrdinal.toOrdinal_max
-/

#print NatOrdinal.toOrdinal_min /-
@[simp]
theorem toOrdinal_min : (min a b).toOrdinal = min a.toOrdinal b.toOrdinal :=
  rfl
#align nat_ordinal.to_ordinal_min NatOrdinal.toOrdinal_min
-/

#print NatOrdinal.succ_def /-
theorem succ_def (a : NatOrdinal) : succ a = (a.toOrdinal + 1).toNatOrdinal :=
  rfl
#align nat_ordinal.succ_def NatOrdinal.succ_def
-/

#print NatOrdinal.rec /-
/-- A recursor for `nat_ordinal`. Use as `induction x using nat_ordinal.rec`. -/
protected def rec {β : NatOrdinal → Sort _} (h : ∀ a, β (toNatOrdinal a)) : ∀ a, β a := fun a =>
  h a.toOrdinal
#align nat_ordinal.rec NatOrdinal.rec
-/

#print NatOrdinal.induction /-
/-- `ordinal.induction` but for `nat_ordinal`. -/
theorem induction {p : NatOrdinal → Prop} : ∀ (i) (h : ∀ j, (∀ k, k < j → p k) → p j), p i :=
  Ordinal.induction
#align nat_ordinal.induction NatOrdinal.induction
-/

end NatOrdinal

namespace Ordinal

#print Ordinal.toNatOrdinal_symm_eq /-
@[simp]
theorem toNatOrdinal_symm_eq : toNatOrdinal.symm = NatOrdinal.toOrdinal :=
  rfl
#align ordinal.to_nat_ordinal_symm_eq Ordinal.toNatOrdinal_symm_eq
-/

#print Ordinal.toNatOrdinal_toOrdinal /-
@[simp]
theorem toNatOrdinal_toOrdinal (a : Ordinal) : a.toNatOrdinal.toOrdinal = a :=
  rfl
#align ordinal.to_nat_ordinal_to_ordinal Ordinal.toNatOrdinal_toOrdinal
-/

#print Ordinal.toNatOrdinal_zero /-
@[simp]
theorem toNatOrdinal_zero : toNatOrdinal 0 = 0 :=
  rfl
#align ordinal.to_nat_ordinal_zero Ordinal.toNatOrdinal_zero
-/

#print Ordinal.toNatOrdinal_one /-
@[simp]
theorem toNatOrdinal_one : toNatOrdinal 1 = 1 :=
  rfl
#align ordinal.to_nat_ordinal_one Ordinal.toNatOrdinal_one
-/

#print Ordinal.toNatOrdinal_eq_zero /-
@[simp]
theorem toNatOrdinal_eq_zero (a) : toNatOrdinal a = 0 ↔ a = 0 :=
  Iff.rfl
#align ordinal.to_nat_ordinal_eq_zero Ordinal.toNatOrdinal_eq_zero
-/

#print Ordinal.toNatOrdinal_eq_one /-
@[simp]
theorem toNatOrdinal_eq_one (a) : toNatOrdinal a = 1 ↔ a = 1 :=
  Iff.rfl
#align ordinal.to_nat_ordinal_eq_one Ordinal.toNatOrdinal_eq_one
-/

#print Ordinal.toNatOrdinal_max /-
@[simp]
theorem toNatOrdinal_max (a b : Ordinal) :
    toNatOrdinal (max a b) = max a.toNatOrdinal b.toNatOrdinal :=
  rfl
#align ordinal.to_nat_ordinal_max Ordinal.toNatOrdinal_max
-/

#print Ordinal.toNatOrdinal_min /-
@[simp]
theorem toNatOrdinal_min (a b : Ordinal) :
    (LinearOrder.min a b).toNatOrdinal = LinearOrder.min a.toNatOrdinal b.toNatOrdinal :=
  rfl
#align ordinal.to_nat_ordinal_min Ordinal.toNatOrdinal_min
-/

/-! We place the definitions of `nadd` and `nmul` before actually developing their API, as this
guarantees we only need to open the `natural_ops` locale once. -/


#print Ordinal.nadd /-
/-- Natural addition on ordinals `a ♯ b`, also known as the Hessenberg sum, is recursively defined
as the least ordinal greater than `a' ♯ b` and `a ♯ b'` for all `a' < a` and `b' < b`. In contrast
to normal ordinal addition, it is commutative.

Natural addition can equivalently be characterized as the ordinal resulting from adding up
corresponding coefficients in the Cantor normal forms of `a` and `b`. -/
noncomputable def nadd : Ordinal → Ordinal → Ordinal
  | a, b => max (blsub.{u, u} a fun a' h => nadd a' b) (blsub.{u, u} b fun b' h => nadd a b')
decreasing_by solve_by_elim [PSigma.Lex.left, PSigma.Lex.right]
#align ordinal.nadd Ordinal.nadd
-/

scoped[NaturalOps] infixl:65 " ♯ " => Ordinal.nadd

#print Ordinal.nmul /-
/-- Natural multiplication on ordinals `a ⨳ b`, also known as the Hessenberg product, is recursively
defined as the least ordinal such that `a ⨳ b + a' ⨳ b'` is greater than `a' ⨳ b + a ⨳ b'` for all
`a' < a` and `b < b'`. In contrast to normal ordinal multiplication, it is commutative and
distributive (over natural addition).

Natural multiplication can equivalently be characterized as the ordinal resulting from multiplying
the Cantor normal forms of `a` and `b` as if they were polynomials in `ω`. Addition of exponents is
done via natural addition. -/
noncomputable def nmul : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}
  | a, b => sInf {c | ∀ a' < a, ∀ b' < b, nmul a' b ♯ nmul a b' < c ♯ nmul a' b'}
decreasing_by solve_by_elim [PSigma.Lex.left, PSigma.Lex.right]
#align ordinal.nmul Ordinal.nmul
-/

scoped[NaturalOps] infixl:70 " ⨳ " => Ordinal.nmul

end Ordinal

open scoped NaturalOps

/-! ### Natural addition -/


namespace Ordinal

variable {a b c : Ordinal.{u}}

#print Ordinal.nadd_def /-
theorem nadd_def (a b : Ordinal) :
    a ♯ b = max (blsub.{u, u} a fun a' h => a' ♯ b) (blsub.{u, u} b fun b' h => a ♯ b') := by
  rw [nadd]
#align ordinal.nadd_def Ordinal.nadd_def
-/

#print Ordinal.lt_nadd_iff /-
theorem lt_nadd_iff : a < b ♯ c ↔ (∃ b' < b, a ≤ b' ♯ c) ∨ ∃ c' < c, a ≤ b ♯ c' := by rw [nadd_def];
  simp [lt_blsub_iff]
#align ordinal.lt_nadd_iff Ordinal.lt_nadd_iff
-/

#print Ordinal.nadd_le_iff /-
theorem nadd_le_iff : b ♯ c ≤ a ↔ (∀ b' < b, b' ♯ c < a) ∧ ∀ c' < c, b ♯ c' < a := by rw [nadd_def];
  simp [blsub_le_iff]
#align ordinal.nadd_le_iff Ordinal.nadd_le_iff
-/

#print Ordinal.nadd_lt_nadd_left /-
theorem nadd_lt_nadd_left (h : b < c) (a) : a ♯ b < a ♯ c :=
  lt_nadd_iff.2 (Or.inr ⟨b, h, le_rfl⟩)
#align ordinal.nadd_lt_nadd_left Ordinal.nadd_lt_nadd_left
-/

#print Ordinal.nadd_lt_nadd_right /-
theorem nadd_lt_nadd_right (h : b < c) (a) : b ♯ a < c ♯ a :=
  lt_nadd_iff.2 (Or.inl ⟨b, h, le_rfl⟩)
#align ordinal.nadd_lt_nadd_right Ordinal.nadd_lt_nadd_right
-/

#print Ordinal.nadd_le_nadd_left /-
theorem nadd_le_nadd_left (h : b ≤ c) (a) : a ♯ b ≤ a ♯ c :=
  by
  rcases lt_or_eq_of_le h with (h | rfl)
  · exact (nadd_lt_nadd_left h a).le
  · exact le_rfl
#align ordinal.nadd_le_nadd_left Ordinal.nadd_le_nadd_left
-/

#print Ordinal.nadd_le_nadd_right /-
theorem nadd_le_nadd_right (h : b ≤ c) (a) : b ♯ a ≤ c ♯ a :=
  by
  rcases lt_or_eq_of_le h with (h | rfl)
  · exact (nadd_lt_nadd_right h a).le
  · exact le_rfl
#align ordinal.nadd_le_nadd_right Ordinal.nadd_le_nadd_right
-/

variable (a b)

#print Ordinal.nadd_comm /-
theorem nadd_comm : ∀ a b, a ♯ b = b ♯ a
  | a, b => by
    rw [nadd_def, nadd_def, max_comm]
    congr <;> ext c hc <;> apply nadd_comm
decreasing_by solve_by_elim [PSigma.Lex.left, PSigma.Lex.right]
#align ordinal.nadd_comm Ordinal.nadd_comm
-/

#print Ordinal.blsub_nadd_of_mono /-
theorem blsub_nadd_of_mono {f : ∀ c < a ♯ b, Ordinal.{max u v}}
    (hf : ∀ {i j} (hi hj), i ≤ j → f i hi ≤ f j hj) :
    blsub _ f =
      max (blsub.{u, v} a fun a' ha' => f (a' ♯ b) <| nadd_lt_nadd_right ha' b)
        (blsub.{u, v} b fun b' hb' => f (a ♯ b') <| nadd_lt_nadd_left hb' a) :=
  by
  apply (blsub_le_iff.2 fun i h => _).antisymm (max_le _ _)
  · rcases lt_nadd_iff.1 h with (⟨a', ha', hi⟩ | ⟨b', hb', hi⟩)
    · exact lt_max_of_lt_left ((hf h (nadd_lt_nadd_right ha' b) hi).trans_lt (lt_blsub _ _ _))
    · exact lt_max_of_lt_right ((hf h (nadd_lt_nadd_left hb' a) hi).trans_lt (lt_blsub _ _ _))
  all_goals
    apply blsub_le_of_brange_subset.{u, u, v}
    rintro c ⟨d, hd, rfl⟩
    apply mem_brange_self
#align ordinal.blsub_nadd_of_mono Ordinal.blsub_nadd_of_mono
-/

#print Ordinal.nadd_assoc /-
theorem nadd_assoc : ∀ a b c, a ♯ b ♯ c = a ♯ (b ♯ c)
  | a, b, c =>
    by
    rw [nadd_def a (b ♯ c), nadd_def, blsub_nadd_of_mono, blsub_nadd_of_mono, max_assoc]
    · congr <;> ext d hd <;> apply nadd_assoc
    · exact fun i j _ _ h => nadd_le_nadd_left h a
    · exact fun i j _ _ h => nadd_le_nadd_right h c
decreasing_by solve_by_elim [PSigma.Lex.left, PSigma.Lex.right]
#align ordinal.nadd_assoc Ordinal.nadd_assoc
-/

#print Ordinal.nadd_zero /-
@[simp]
theorem nadd_zero : a ♯ 0 = a :=
  by
  induction' a using Ordinal.induction with a IH
  rw [nadd_def, blsub_zero, max_zero_right]
  convert blsub_id a
  ext b hb
  exact IH _ hb
#align ordinal.nadd_zero Ordinal.nadd_zero
-/

#print Ordinal.zero_nadd /-
@[simp]
theorem zero_nadd : 0 ♯ a = a := by rw [nadd_comm, nadd_zero]
#align ordinal.zero_nadd Ordinal.zero_nadd
-/

#print Ordinal.nadd_one /-
@[simp]
theorem nadd_one : a ♯ 1 = succ a :=
  by
  induction' a using Ordinal.induction with a IH
  rw [nadd_def, blsub_one, nadd_zero, max_eq_right_iff, blsub_le_iff]
  intro i hi
  rwa [IH i hi, succ_lt_succ_iff]
#align ordinal.nadd_one Ordinal.nadd_one
-/

#print Ordinal.one_nadd /-
@[simp]
theorem one_nadd : 1 ♯ a = succ a := by rw [nadd_comm, nadd_one]
#align ordinal.one_nadd Ordinal.one_nadd
-/

#print Ordinal.nadd_succ /-
theorem nadd_succ : a ♯ succ b = succ (a ♯ b) := by rw [← nadd_one (a ♯ b), nadd_assoc, nadd_one]
#align ordinal.nadd_succ Ordinal.nadd_succ
-/

#print Ordinal.succ_nadd /-
theorem succ_nadd : succ a ♯ b = succ (a ♯ b) := by rw [← one_nadd (a ♯ b), ← nadd_assoc, one_nadd]
#align ordinal.succ_nadd Ordinal.succ_nadd
-/

#print Ordinal.nadd_nat /-
@[simp]
theorem nadd_nat (n : ℕ) : a ♯ n = a + n :=
  by
  induction' n with n hn
  · simp
  · rw [Nat.cast_succ, add_one_eq_succ, nadd_succ, add_succ, hn]
#align ordinal.nadd_nat Ordinal.nadd_nat
-/

#print Ordinal.nat_nadd /-
@[simp]
theorem nat_nadd (n : ℕ) : ↑n ♯ a = a + n := by rw [nadd_comm, nadd_nat]
#align ordinal.nat_nadd Ordinal.nat_nadd
-/

#print Ordinal.add_le_nadd /-
theorem add_le_nadd : a + b ≤ a ♯ b := by
  apply b.limit_rec_on
  · simp
  · intro c h
    rwa [add_succ, nadd_succ, succ_le_succ_iff]
  · intro c hc H
    rw [← IsNormal.blsub_eq.{u, u} (add_is_normal a) hc, blsub_le_iff]
    exact fun i hi => (H i hi).trans_lt (nadd_lt_nadd_left hi a)
#align ordinal.add_le_nadd Ordinal.add_le_nadd
-/

end Ordinal

namespace NatOrdinal

open Ordinal

instance : Add NatOrdinal :=
  ⟨nadd⟩

#print NatOrdinal.add_covariantClass_lt /-
instance add_covariantClass_lt : CovariantClass NatOrdinal.{u} NatOrdinal.{u} (· + ·) (· < ·) :=
  ⟨fun a b c h => nadd_lt_nadd_left h a⟩
#align nat_ordinal.add_covariant_class_lt NatOrdinal.add_covariantClass_lt
-/

#print NatOrdinal.add_covariantClass_le /-
instance add_covariantClass_le : CovariantClass NatOrdinal.{u} NatOrdinal.{u} (· + ·) (· ≤ ·) :=
  ⟨fun a b c h => nadd_le_nadd_left h a⟩
#align nat_ordinal.add_covariant_class_le NatOrdinal.add_covariantClass_le
-/

#print NatOrdinal.add_contravariantClass_le /-
instance add_contravariantClass_le :
    ContravariantClass NatOrdinal.{u} NatOrdinal.{u} (· + ·) (· ≤ ·) :=
  ⟨fun a b c h => by by_contra' h'; exact h.not_lt (add_lt_add_left h' a)⟩
#align nat_ordinal.add_contravariant_class_le NatOrdinal.add_contravariantClass_le
-/

instance : OrderedCancelAddCommMonoid NatOrdinal :=
  { NatOrdinal.linearOrder with
    add := (· + ·)
    add_assoc := nadd_assoc
    add_le_add_left := fun a b => add_le_add_left
    le_of_add_le_add_left := fun a b c => le_of_add_le_add_left
    zero := 0
    zero_add := zero_nadd
    add_zero := nadd_zero
    add_comm := nadd_comm }

instance : AddMonoidWithOne NatOrdinal :=
  AddMonoidWithOne.unary

#print NatOrdinal.add_one_eq_succ /-
@[simp]
theorem add_one_eq_succ : ∀ a : NatOrdinal, a + 1 = succ a :=
  nadd_one
#align nat_ordinal.add_one_eq_succ NatOrdinal.add_one_eq_succ
-/

#print NatOrdinal.toOrdinal_cast_nat /-
@[simp]
theorem toOrdinal_cast_nat (n : ℕ) : toOrdinal n = n :=
  by
  induction' n with n hn
  · rfl
  · change to_ordinal n ♯ 1 = n + 1
    rw [hn]; exact nadd_one n
#align nat_ordinal.to_ordinal_cast_nat NatOrdinal.toOrdinal_cast_nat
-/

end NatOrdinal

namespace Ordinal

#print Ordinal.nadd_eq_add /-
theorem nadd_eq_add (a b : Ordinal) : a ♯ b = (a.toNatOrdinal + b.toNatOrdinal).toOrdinal :=
  rfl
#align ordinal.nadd_eq_add Ordinal.nadd_eq_add
-/

#print Ordinal.toNatOrdinal_cast_nat /-
@[simp]
theorem toNatOrdinal_cast_nat (n : ℕ) : toNatOrdinal n = n := by
  rw [← NatOrdinal.toOrdinal_cast_nat n]; rfl
#align ordinal.to_nat_ordinal_cast_nat Ordinal.toNatOrdinal_cast_nat
-/

#print Ordinal.lt_of_nadd_lt_nadd_left /-
theorem lt_of_nadd_lt_nadd_left : ∀ {a b c}, a ♯ b < a ♯ c → b < c :=
  @lt_of_add_lt_add_left NatOrdinal _ _ _
#align ordinal.lt_of_nadd_lt_nadd_left Ordinal.lt_of_nadd_lt_nadd_left
-/

#print Ordinal.lt_of_nadd_lt_nadd_right /-
theorem lt_of_nadd_lt_nadd_right : ∀ {a b c}, b ♯ a < c ♯ a → b < c :=
  @lt_of_add_lt_add_right NatOrdinal _ _ _
#align ordinal.lt_of_nadd_lt_nadd_right Ordinal.lt_of_nadd_lt_nadd_right
-/

#print Ordinal.le_of_nadd_le_nadd_left /-
theorem le_of_nadd_le_nadd_left : ∀ {a b c}, a ♯ b ≤ a ♯ c → b ≤ c :=
  @le_of_add_le_add_left NatOrdinal _ _ _
#align ordinal.le_of_nadd_le_nadd_left Ordinal.le_of_nadd_le_nadd_left
-/

#print Ordinal.le_of_nadd_le_nadd_right /-
theorem le_of_nadd_le_nadd_right : ∀ {a b c}, b ♯ a ≤ c ♯ a → b ≤ c :=
  @le_of_add_le_add_right NatOrdinal _ _ _
#align ordinal.le_of_nadd_le_nadd_right Ordinal.le_of_nadd_le_nadd_right
-/

#print Ordinal.nadd_lt_nadd_iff_left /-
theorem nadd_lt_nadd_iff_left : ∀ (a) {b c}, a ♯ b < a ♯ c ↔ b < c :=
  @add_lt_add_iff_left NatOrdinal _ _ _ _
#align ordinal.nadd_lt_nadd_iff_left Ordinal.nadd_lt_nadd_iff_left
-/

#print Ordinal.nadd_lt_nadd_iff_right /-
theorem nadd_lt_nadd_iff_right : ∀ (a) {b c}, b ♯ a < c ♯ a ↔ b < c :=
  @add_lt_add_iff_right NatOrdinal _ _ _ _
#align ordinal.nadd_lt_nadd_iff_right Ordinal.nadd_lt_nadd_iff_right
-/

#print Ordinal.nadd_le_nadd_iff_left /-
theorem nadd_le_nadd_iff_left : ∀ (a) {b c}, a ♯ b ≤ a ♯ c ↔ b ≤ c :=
  @add_le_add_iff_left NatOrdinal _ _ _ _
#align ordinal.nadd_le_nadd_iff_left Ordinal.nadd_le_nadd_iff_left
-/

#print Ordinal.nadd_le_nadd_iff_right /-
theorem nadd_le_nadd_iff_right : ∀ (a) {b c}, b ♯ a ≤ c ♯ a ↔ b ≤ c :=
  @add_le_add_iff_right NatOrdinal _ _ _ _
#align ordinal.nadd_le_nadd_iff_right Ordinal.nadd_le_nadd_iff_right
-/

#print Ordinal.nadd_le_nadd /-
theorem nadd_le_nadd : ∀ {a b c d}, a ≤ b → c ≤ d → a ♯ c ≤ b ♯ d :=
  @add_le_add NatOrdinal _ _ _ _
#align ordinal.nadd_le_nadd Ordinal.nadd_le_nadd
-/

#print Ordinal.nadd_lt_nadd /-
theorem nadd_lt_nadd : ∀ {a b c d}, a < b → c < d → a ♯ c < b ♯ d :=
  @add_lt_add NatOrdinal _ _ _ _
#align ordinal.nadd_lt_nadd Ordinal.nadd_lt_nadd
-/

#print Ordinal.nadd_lt_nadd_of_lt_of_le /-
theorem nadd_lt_nadd_of_lt_of_le : ∀ {a b c d}, a < b → c ≤ d → a ♯ c < b ♯ d :=
  @add_lt_add_of_lt_of_le NatOrdinal _ _ _ _
#align ordinal.nadd_lt_nadd_of_lt_of_le Ordinal.nadd_lt_nadd_of_lt_of_le
-/

#print Ordinal.nadd_lt_nadd_of_le_of_lt /-
theorem nadd_lt_nadd_of_le_of_lt : ∀ {a b c d}, a ≤ b → c < d → a ♯ c < b ♯ d :=
  @add_lt_add_of_le_of_lt NatOrdinal _ _ _ _
#align ordinal.nadd_lt_nadd_of_le_of_lt Ordinal.nadd_lt_nadd_of_le_of_lt
-/

#print Ordinal.nadd_left_cancel /-
theorem nadd_left_cancel : ∀ {a b c}, a ♯ b = a ♯ c → b = c :=
  @add_left_cancel NatOrdinal _ _
#align ordinal.nadd_left_cancel Ordinal.nadd_left_cancel
-/

#print Ordinal.nadd_right_cancel /-
theorem nadd_right_cancel : ∀ {a b c}, a ♯ b = c ♯ b → a = c :=
  @add_right_cancel NatOrdinal _ _
#align ordinal.nadd_right_cancel Ordinal.nadd_right_cancel
-/

#print Ordinal.nadd_left_cancel_iff /-
theorem nadd_left_cancel_iff : ∀ {a b c}, a ♯ b = a ♯ c ↔ b = c :=
  @add_left_cancel_iff NatOrdinal _ _
#align ordinal.nadd_left_cancel_iff Ordinal.nadd_left_cancel_iff
-/

#print Ordinal.nadd_right_cancel_iff /-
theorem nadd_right_cancel_iff : ∀ {a b c}, b ♯ a = c ♯ a ↔ b = c :=
  @add_right_cancel_iff NatOrdinal _ _
#align ordinal.nadd_right_cancel_iff Ordinal.nadd_right_cancel_iff
-/

#print Ordinal.le_nadd_self /-
theorem le_nadd_self {a b} : a ≤ b ♯ a := by simpa using nadd_le_nadd_right (Ordinal.zero_le b) a
#align ordinal.le_nadd_self Ordinal.le_nadd_self
-/

#print Ordinal.le_nadd_left /-
theorem le_nadd_left {a b c} (h : a ≤ c) : a ≤ b ♯ c :=
  le_nadd_self.trans (nadd_le_nadd_left h b)
#align ordinal.le_nadd_left Ordinal.le_nadd_left
-/

#print Ordinal.le_self_nadd /-
theorem le_self_nadd {a b} : a ≤ a ♯ b := by simpa using nadd_le_nadd_left (Ordinal.zero_le b) a
#align ordinal.le_self_nadd Ordinal.le_self_nadd
-/

#print Ordinal.le_nadd_right /-
theorem le_nadd_right {a b c} (h : a ≤ b) : a ≤ b ♯ c :=
  le_self_nadd.trans (nadd_le_nadd_right h c)
#align ordinal.le_nadd_right Ordinal.le_nadd_right
-/

#print Ordinal.nadd_left_comm /-
theorem nadd_left_comm : ∀ a b c, a ♯ (b ♯ c) = b ♯ (a ♯ c) :=
  @add_left_comm NatOrdinal _
#align ordinal.nadd_left_comm Ordinal.nadd_left_comm
-/

#print Ordinal.nadd_right_comm /-
theorem nadd_right_comm : ∀ a b c, a ♯ b ♯ c = a ♯ c ♯ b :=
  @add_right_comm NatOrdinal _
#align ordinal.nadd_right_comm Ordinal.nadd_right_comm
-/

/-! ### Natural multiplication -/


variable {a b c d : Ordinal.{u}}

#print Ordinal.nmul_def /-
theorem nmul_def (a b : Ordinal) :
    a ⨳ b = sInf {c | ∀ a' < a, ∀ b' < b, a' ⨳ b ♯ a ⨳ b' < c ♯ a' ⨳ b'} := by rw [nmul]
#align ordinal.nmul_def Ordinal.nmul_def
-/

#print Ordinal.nmul_nonempty /-
/-- The set in the definition of `nmul` is nonempty. -/
theorem nmul_nonempty (a b : Ordinal.{u}) :
    {c : Ordinal.{u} | ∀ a' < a, ∀ b' < b, a' ⨳ b ♯ a ⨳ b' < c ♯ a' ⨳ b'}.Nonempty :=
  ⟨_, fun a' ha b' hb => (lt_blsub₂.{u, u, u} _ ha hb).trans_le le_self_nadd⟩
#align ordinal.nmul_nonempty Ordinal.nmul_nonempty
-/

#print Ordinal.nmul_nadd_lt /-
theorem nmul_nadd_lt {a' b' : Ordinal} (ha : a' < a) (hb : b' < b) :
    a' ⨳ b ♯ a ⨳ b' < a ⨳ b ♯ a' ⨳ b' := by rw [nmul_def a b];
  exact csInf_mem (nmul_nonempty a b) a' ha b' hb
#align ordinal.nmul_nadd_lt Ordinal.nmul_nadd_lt
-/

#print Ordinal.nmul_nadd_le /-
theorem nmul_nadd_le {a' b' : Ordinal} (ha : a' ≤ a) (hb : b' ≤ b) :
    a' ⨳ b ♯ a ⨳ b' ≤ a ⨳ b ♯ a' ⨳ b' :=
  by
  rcases lt_or_eq_of_le ha with (ha | rfl)
  · rcases lt_or_eq_of_le hb with (hb | rfl)
    · exact (nmul_nadd_lt ha hb).le
    · rw [nadd_comm]
  · exact le_rfl
#align ordinal.nmul_nadd_le Ordinal.nmul_nadd_le
-/

#print Ordinal.lt_nmul_iff /-
theorem lt_nmul_iff : c < a ⨳ b ↔ ∃ a' < a, ∃ b' < b, c ♯ a' ⨳ b' ≤ a' ⨳ b ♯ a ⨳ b' :=
  by
  refine' ⟨fun h => _, _⟩
  · rw [nmul] at h 
    simpa using not_mem_of_lt_csInf h ⟨0, fun _ _ => bot_le⟩
  · rintro ⟨a', ha, b', hb, h⟩
    have := h.trans_lt (nmul_nadd_lt ha hb)
    rwa [nadd_lt_nadd_iff_right] at this 
#align ordinal.lt_nmul_iff Ordinal.lt_nmul_iff
-/

#print Ordinal.nmul_le_iff /-
theorem nmul_le_iff : a ⨳ b ≤ c ↔ ∀ a' < a, ∀ b' < b, a' ⨳ b ♯ a ⨳ b' < c ♯ a' ⨳ b' := by
  rw [← not_iff_not]; simp [lt_nmul_iff]
#align ordinal.nmul_le_iff Ordinal.nmul_le_iff
-/

#print Ordinal.nmul_comm /-
theorem nmul_comm : ∀ a b, a ⨳ b = b ⨳ a
  | a, b => by
    rw [nmul, nmul]
    congr; ext x; constructor <;> intro H c hc d hd
    · rw [nadd_comm, ← nmul_comm, ← nmul_comm a, ← nmul_comm d]
      exact H _ hd _ hc
    · rw [nadd_comm, nmul_comm, nmul_comm c, nmul_comm c]
      exact H _ hd _ hc
decreasing_by solve_by_elim [PSigma.Lex.left, PSigma.Lex.right]
#align ordinal.nmul_comm Ordinal.nmul_comm
-/

#print Ordinal.nmul_zero /-
@[simp]
theorem nmul_zero (a) : a ⨳ 0 = 0 := by rw [← Ordinal.le_zero, nmul_le_iff];
  exact fun _ _ a ha => (Ordinal.not_lt_zero a ha).elim
#align ordinal.nmul_zero Ordinal.nmul_zero
-/

#print Ordinal.zero_nmul /-
@[simp]
theorem zero_nmul (a) : 0 ⨳ a = 0 := by rw [nmul_comm, nmul_zero]
#align ordinal.zero_nmul Ordinal.zero_nmul
-/

#print Ordinal.nmul_one /-
@[simp]
theorem nmul_one : ∀ a, a ⨳ 1 = a
  | a => by
    rw [nmul]
    simp only [lt_one_iff_zero, forall_eq, nmul_zero, nadd_zero]
    convert csInf_Ici
    ext b
    refine' ⟨fun H => le_of_forall_lt fun c hc => _, fun ha c hc => _⟩
    · simpa only [nmul_one] using H c hc
    · simpa only [nmul_one] using hc.trans_le ha
#align ordinal.nmul_one Ordinal.nmul_one
-/

#print Ordinal.one_nmul /-
@[simp]
theorem one_nmul (a) : 1 ⨳ a = a := by rw [nmul_comm, nmul_one]
#align ordinal.one_nmul Ordinal.one_nmul
-/

#print Ordinal.nmul_lt_nmul_of_pos_left /-
theorem nmul_lt_nmul_of_pos_left (h₁ : a < b) (h₂ : 0 < c) : c ⨳ a < c ⨳ b :=
  lt_nmul_iff.2 ⟨0, h₂, a, h₁, by simp⟩
#align ordinal.nmul_lt_nmul_of_pos_left Ordinal.nmul_lt_nmul_of_pos_left
-/

#print Ordinal.nmul_lt_nmul_of_pos_right /-
theorem nmul_lt_nmul_of_pos_right (h₁ : a < b) (h₂ : 0 < c) : a ⨳ c < b ⨳ c :=
  lt_nmul_iff.2 ⟨a, h₁, 0, h₂, by simp⟩
#align ordinal.nmul_lt_nmul_of_pos_right Ordinal.nmul_lt_nmul_of_pos_right
-/

#print Ordinal.nmul_le_nmul_of_nonneg_left /-
theorem nmul_le_nmul_of_nonneg_left (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c ⨳ a ≤ c ⨳ b :=
  by
  rcases lt_or_eq_of_le h₁ with (h₁ | rfl) <;> rcases lt_or_eq_of_le h₂ with (h₂ | rfl)
  · exact (nmul_lt_nmul_of_pos_left h₁ h₂).le
  all_goals simp
#align ordinal.nmul_le_nmul_of_nonneg_left Ordinal.nmul_le_nmul_of_nonneg_left
-/

#print Ordinal.nmul_le_nmul_of_nonneg_right /-
theorem nmul_le_nmul_of_nonneg_right (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a ⨳ c ≤ b ⨳ c :=
  by
  rw [nmul_comm, nmul_comm b]
  exact nmul_le_nmul_of_nonneg_left h₁ h₂
#align ordinal.nmul_le_nmul_of_nonneg_right Ordinal.nmul_le_nmul_of_nonneg_right
-/

#print Ordinal.nmul_nadd /-
theorem nmul_nadd : ∀ a b c, a ⨳ (b ♯ c) = a ⨳ b ♯ a ⨳ c
  | a, b, c =>
    by
    apply
      le_antisymm (nmul_le_iff.2 fun a' ha d hd => _) (nadd_le_iff.2 ⟨fun d hd => _, fun d hd => _⟩)
    · rw [nmul_nadd]
      rcases lt_nadd_iff.1 hd with (⟨b', hb, hd⟩ | ⟨c', hc, hd⟩)
      · have := nadd_lt_nadd_of_lt_of_le (nmul_nadd_lt ha hb) (nmul_nadd_le ha.le hd)
        rw [nmul_nadd, nmul_nadd] at this 
        simp only [nadd_assoc] at this 
        rwa [nadd_left_comm, nadd_left_comm _ (a ⨳ b'), nadd_left_comm (a ⨳ b),
          nadd_lt_nadd_iff_left, nadd_left_comm (a' ⨳ b), nadd_left_comm (a ⨳ b),
          nadd_lt_nadd_iff_left, ← nadd_assoc, ← nadd_assoc] at this 
      · have := nadd_lt_nadd_of_le_of_lt (nmul_nadd_le ha.le hd) (nmul_nadd_lt ha hc)
        rw [nmul_nadd, nmul_nadd] at this 
        simp only [nadd_assoc] at this 
        rwa [nadd_left_comm, nadd_comm (a ⨳ c), nadd_left_comm (a' ⨳ d), nadd_left_comm (a ⨳ c'),
          nadd_left_comm (a ⨳ b), nadd_lt_nadd_iff_left, nadd_comm (a' ⨳ c), nadd_left_comm (a ⨳ d),
          nadd_left_comm (a' ⨳ b), nadd_left_comm (a ⨳ b), nadd_lt_nadd_iff_left, nadd_comm (a ⨳ d),
          nadd_comm (a' ⨳ d), ← nadd_assoc, ← nadd_assoc] at this 
    · rcases lt_nmul_iff.1 hd with ⟨a', ha, b', hb, hd⟩
      have := nadd_lt_nadd_of_le_of_lt hd (nmul_nadd_lt ha (nadd_lt_nadd_right hb c))
      rw [nmul_nadd, nmul_nadd, nmul_nadd a'] at this 
      simp only [nadd_assoc] at this 
      rwa [nadd_left_comm (a' ⨳ b'), nadd_left_comm, nadd_lt_nadd_iff_left, nadd_left_comm,
        nadd_left_comm _ (a' ⨳ b'), nadd_left_comm (a ⨳ b'), nadd_lt_nadd_iff_left,
        nadd_left_comm (a' ⨳ c), nadd_left_comm, nadd_lt_nadd_iff_left, nadd_left_comm,
        nadd_comm _ (a' ⨳ c), nadd_lt_nadd_iff_left] at this 
    · rcases lt_nmul_iff.1 hd with ⟨a', ha, c', hc, hd⟩
      have := nadd_lt_nadd_of_lt_of_le (nmul_nadd_lt ha (nadd_lt_nadd_left hc b)) hd
      rw [nmul_nadd, nmul_nadd, nmul_nadd a'] at this 
      simp only [nadd_assoc] at this 
      rwa [nadd_left_comm _ (a' ⨳ b), nadd_lt_nadd_iff_left, nadd_left_comm (a' ⨳ c'),
        nadd_left_comm _ (a' ⨳ c), nadd_lt_nadd_iff_left, nadd_left_comm, nadd_comm (a' ⨳ c'),
        nadd_left_comm _ (a ⨳ c'), nadd_lt_nadd_iff_left, nadd_comm _ (a' ⨳ c'),
        nadd_comm _ (a' ⨳ c'), nadd_left_comm, nadd_lt_nadd_iff_left] at this 
decreasing_by solve_by_elim [PSigma.Lex.left, PSigma.Lex.right]
#align ordinal.nmul_nadd Ordinal.nmul_nadd
-/

#print Ordinal.nadd_nmul /-
theorem nadd_nmul (a b c) : (a ♯ b) ⨳ c = a ⨳ c ♯ b ⨳ c := by
  rw [nmul_comm, nmul_nadd, nmul_comm, nmul_comm c]
#align ordinal.nadd_nmul Ordinal.nadd_nmul
-/

#print Ordinal.nmul_nadd_lt₃ /-
theorem nmul_nadd_lt₃ {a' b' c' : Ordinal} (ha : a' < a) (hb : b' < b) (hc : c' < c) :
    a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' <
      a ⨳ b ⨳ c ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' :=
  by simpa only [nadd_nmul, ← nadd_assoc] using nmul_nadd_lt (nmul_nadd_lt ha hb) hc
#align ordinal.nmul_nadd_lt₃ Ordinal.nmul_nadd_lt₃
-/

#print Ordinal.nmul_nadd_le₃ /-
theorem nmul_nadd_le₃ {a' b' c' : Ordinal} (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) :
    a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' ≤
      a ⨳ b ⨳ c ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' :=
  by simpa only [nadd_nmul, ← nadd_assoc] using nmul_nadd_le (nmul_nadd_le ha hb) hc
#align ordinal.nmul_nadd_le₃ Ordinal.nmul_nadd_le₃
-/

#print Ordinal.nmul_nadd_lt₃' /-
theorem nmul_nadd_lt₃' {a' b' c' : Ordinal} (ha : a' < a) (hb : b' < b) (hc : c' < c) :
    a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') <
      a ⨳ (b ⨳ c) ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') :=
  by
  simp only [nmul_comm _ (_ ⨳ _)]
  convert nmul_nadd_lt₃ hb hc ha using 1 <;>
    · simp only [nadd_eq_add, NatOrdinal.toOrdinal_toNatOrdinal]; abel
#align ordinal.nmul_nadd_lt₃' Ordinal.nmul_nadd_lt₃'
-/

#print Ordinal.nmul_nadd_le₃' /-
theorem nmul_nadd_le₃' {a' b' c' : Ordinal} (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) :
    a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') ≤
      a ⨳ (b ⨳ c) ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') :=
  by
  simp only [nmul_comm _ (_ ⨳ _)]
  convert nmul_nadd_le₃ hb hc ha using 1 <;>
    · simp only [nadd_eq_add, NatOrdinal.toOrdinal_toNatOrdinal]; abel
#align ordinal.nmul_nadd_le₃' Ordinal.nmul_nadd_le₃'
-/

#print Ordinal.lt_nmul_iff₃ /-
theorem lt_nmul_iff₃ :
    d < a ⨳ b ⨳ c ↔
      ∃ a' < a,
        ∃ b' < b,
          ∃ c' < c,
            d ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' ≤
              a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' :=
  by
  refine' ⟨fun h => _, _⟩
  · rcases lt_nmul_iff.1 h with ⟨e, he, c', hc, H₁⟩
    rcases lt_nmul_iff.1 he with ⟨a', ha, b', hb, H₂⟩
    refine' ⟨a', ha, b', hb, c', hc, _⟩
    have := nadd_le_nadd H₁ (nmul_nadd_le H₂ hc.le)
    simp only [nadd_nmul, nadd_assoc] at this 
    rw [nadd_left_comm, nadd_left_comm d, nadd_left_comm, nadd_le_nadd_iff_left,
      nadd_left_comm (a ⨳ b' ⨳ c), nadd_left_comm (a' ⨳ b ⨳ c), nadd_left_comm (a ⨳ b ⨳ c'),
      nadd_le_nadd_iff_left, nadd_left_comm (a ⨳ b ⨳ c'), nadd_left_comm (a ⨳ b ⨳ c')] at this 
    simpa only [nadd_assoc]
  · rintro ⟨a', ha, b', hb, c', hc, h⟩
    have := h.trans_lt (nmul_nadd_lt₃ ha hb hc)
    repeat' rwa [nadd_lt_nadd_iff_right] at this 
#align ordinal.lt_nmul_iff₃ Ordinal.lt_nmul_iff₃
-/

#print Ordinal.nmul_le_iff₃ /-
theorem nmul_le_iff₃ :
    a ⨳ b ⨳ c ≤ d ↔
      ∀ a' < a,
        ∀ b' < b,
          ∀ c' < c,
            a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' <
              d ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' :=
  by rw [← not_iff_not]; simp [lt_nmul_iff₃]
#align ordinal.nmul_le_iff₃ Ordinal.nmul_le_iff₃
-/

#print Ordinal.lt_nmul_iff₃' /-
theorem lt_nmul_iff₃' :
    d < a ⨳ (b ⨳ c) ↔
      ∃ a' < a,
        ∃ b' < b,
          ∃ c' < c,
            d ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') ≤
              a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') :=
  by
  simp only [nmul_comm _ (_ ⨳ _), lt_nmul_iff₃, nadd_eq_add, NatOrdinal.toOrdinal_toNatOrdinal]
  constructor <;> rintro ⟨b', hb, c', hc, a', ha, h⟩
  · use a', ha, b', hb, c', hc; convert h using 1 <;> abel
  · use c', hc, a', ha, b', hb; convert h using 1 <;> abel
#align ordinal.lt_nmul_iff₃' Ordinal.lt_nmul_iff₃'
-/

#print Ordinal.nmul_le_iff₃' /-
theorem nmul_le_iff₃' :
    a ⨳ (b ⨳ c) ≤ d ↔
      ∀ a' < a,
        ∀ b' < b,
          ∀ c' < c,
            a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') <
              d ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') :=
  by rw [← not_iff_not]; simp [lt_nmul_iff₃']
#align ordinal.nmul_le_iff₃' Ordinal.nmul_le_iff₃'
-/

#print Ordinal.nmul_assoc /-
theorem nmul_assoc : ∀ a b c, a ⨳ b ⨳ c = a ⨳ (b ⨳ c)
  | a, b, c => by
    apply le_antisymm
    · rw [nmul_le_iff₃]
      intro a' ha b' hb c' hc
      repeat' rw [nmul_assoc]
      exact nmul_nadd_lt₃' ha hb hc
    · rw [nmul_le_iff₃']
      intro a' ha b' hb c' hc
      repeat' rw [← nmul_assoc]
      exact nmul_nadd_lt₃ ha hb hc
decreasing_by solve_by_elim [PSigma.Lex.left, PSigma.Lex.right]
#align ordinal.nmul_assoc Ordinal.nmul_assoc
-/

end Ordinal

open Ordinal

instance : Mul NatOrdinal :=
  ⟨nmul⟩

instance : OrderedCommSemiring NatOrdinal :=
  { NatOrdinal.orderedCancelAddCommMonoid,
    NatOrdinal.linearOrder with
    mul := (· * ·)
    left_distrib := nmul_nadd
    right_distrib := nadd_nmul
    zero_mul := zero_nmul
    mul_zero := nmul_zero
    mul_assoc := nmul_assoc
    one := 1
    one_mul := one_nmul
    mul_one := nmul_one
    mul_comm := nmul_comm
    zero_le_one := @zero_le_one Ordinal _ _ _ _
    mul_le_mul_of_nonneg_left := fun a b c => nmul_le_nmul_of_nonneg_left
    mul_le_mul_of_nonneg_right := fun a b c => nmul_le_nmul_of_nonneg_right }

namespace Ordinal

#print Ordinal.nmul_eq_mul /-
theorem nmul_eq_mul (a b) : a ⨳ b = (a.toNatOrdinal * b.toNatOrdinal).toOrdinal :=
  rfl
#align ordinal.nmul_eq_mul Ordinal.nmul_eq_mul
-/

#print Ordinal.nmul_nadd_one /-
theorem nmul_nadd_one : ∀ a b, a ⨳ (b ♯ 1) = a ⨳ b ♯ a :=
  @mul_add_one NatOrdinal _ _ _
#align ordinal.nmul_nadd_one Ordinal.nmul_nadd_one
-/

#print Ordinal.nadd_one_nmul /-
theorem nadd_one_nmul : ∀ a b, (a ♯ 1) ⨳ b = a ⨳ b ♯ b :=
  @add_one_mul NatOrdinal _ _ _
#align ordinal.nadd_one_nmul Ordinal.nadd_one_nmul
-/

#print Ordinal.nmul_succ /-
theorem nmul_succ (a b) : a ⨳ succ b = a ⨳ b ♯ a := by rw [← nadd_one, nmul_nadd_one]
#align ordinal.nmul_succ Ordinal.nmul_succ
-/

#print Ordinal.succ_nmul /-
theorem succ_nmul (a b) : succ a ⨳ b = a ⨳ b ♯ b := by rw [← nadd_one, nadd_one_nmul]
#align ordinal.succ_nmul Ordinal.succ_nmul
-/

#print Ordinal.nmul_add_one /-
theorem nmul_add_one : ∀ a b, a ⨳ (b + 1) = a ⨳ b ♯ a :=
  nmul_succ
#align ordinal.nmul_add_one Ordinal.nmul_add_one
-/

#print Ordinal.add_one_nmul /-
theorem add_one_nmul : ∀ a b, (a + 1) ⨳ b = a ⨳ b ♯ b :=
  succ_nmul
#align ordinal.add_one_nmul Ordinal.add_one_nmul
-/

end Ordinal

namespace NatOrdinal

open Ordinal

#print NatOrdinal.mul_le_nmul /-
theorem mul_le_nmul (a b : Ordinal.{u}) : a * b ≤ a ⨳ b :=
  by
  apply b.limit_rec_on
  · simp
  · intro c h
    rw [mul_succ, nmul_succ]
    exact (add_le_nadd _ a).trans (nadd_le_nadd_right h a)
  · intro c hc H
    rcases eq_zero_or_pos a with (rfl | ha)
    · simp
    · rw [← IsNormal.blsub_eq.{u, u} (mul_is_normal ha) hc, blsub_le_iff]
      exact fun i hi => (H i hi).trans_lt (nmul_lt_nmul_of_pos_left hi ha)
#align nat_ordinal.mul_le_nmul NatOrdinal.mul_le_nmul
-/

end NatOrdinal

