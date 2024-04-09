/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Algebra.Algebra.Basic
import Algebra.Order.Field.Canonical.Basic
import Algebra.Order.Nonneg.Field
import Algebra.Order.Nonneg.Floor
import Data.Real.Pointwise
import Order.ConditionallyCompleteLattice.Group
import Tactic.Positivity

#align_import data.real.nnreal from "leanprover-community/mathlib"@"b1abe23ae96fef89ad30d9f4362c307f72a55010"

/-!
# Nonnegative real numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `nnreal` (notation: `ℝ≥0`) to be the type of non-negative real numbers,
a.k.a. the interval `[0, ∞)`. We also define the following operations and structures on `ℝ≥0`:

* the order on `ℝ≥0` is the restriction of the order on `ℝ`; these relations define a conditionally
  complete linear order with a bottom element, `conditionally_complete_linear_order_bot`;

* `a + b` and `a * b` are the restrictions of addition and multiplication of real numbers to `ℝ≥0`;
  these operations together with `0 = ⟨0, _⟩` and `1 = ⟨1, _⟩` turn `ℝ≥0` into a conditionally
  complete linear ordered archimedean commutative semifield; we have no typeclass for this in
  `mathlib` yet, so we define the following instances instead:

  - `linear_ordered_semiring ℝ≥0`;
  - `ordered_comm_semiring ℝ≥0`;
  - `canonically_ordered_comm_semiring ℝ≥0`;
  - `linear_ordered_comm_group_with_zero ℝ≥0`;
  - `canonically_linear_ordered_add_monoid ℝ≥0`;
  - `archimedean ℝ≥0`;
  - `conditionally_complete_linear_order_bot ℝ≥0`.

  These instances are derived from corresponding instances about the type `{x : α // 0 ≤ x}` in an
  appropriate ordered field/ring/group/monoid `α`. See `algebra/order/nonneg`.

* `real.to_nnreal x` is defined as `⟨max x 0, _⟩`, i.e. `↑(real.to_nnreal x) = x` when `0 ≤ x` and
  `↑(real.to_nnreal x) = 0` otherwise.

We also define an instance `can_lift ℝ ℝ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℝ` and `hx : 0 ≤ x` in the proof context with `x : ℝ≥0` while replacing all occurences
of `x` with `↑x`. This tactic also works for a function `f : α → ℝ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notations

This file defines `ℝ≥0` as a localized notation for `nnreal`.
-/


open scoped Classical BigOperators

#print NNReal /-
-- to ensure these instances are computable
/-- Nonnegative real numbers. -/
def NNReal :=
  { r : ℝ // 0 ≤ r }
deriving StrictOrderedSemiring, CommMonoidWithZero, FloorSemiring, CommSemiring, Semiring,
  SemilatticeInf, SemilatticeSup, DistribLattice, DenselyOrdered, OrderBot,
  CanonicallyLinearOrderedSemifield, LinearOrderedCommGroupWithZero, Archimedean,
  LinearOrderedSemiring, OrderedCommSemiring, CanonicallyOrderedCommSemiring, Sub, OrderedSub, Div,
  Inhabited
#align nnreal NNReal
-/

scoped[NNReal] notation "ℝ≥0" => NNReal

namespace NNReal

instance : Coe ℝ≥0 ℝ :=
  ⟨Subtype.val⟩

#print NNReal.val_eq_coe /-
-- Simp lemma to put back `n.val` into the normal form given by the coercion.
@[simp]
theorem val_eq_coe (n : ℝ≥0) : n.val = n :=
  rfl
#align nnreal.val_eq_coe NNReal.val_eq_coe
-/

#print NNReal.canLift /-
instance canLift : CanLift ℝ ℝ≥0 coe fun r => 0 ≤ r :=
  Subtype.canLift _
#align nnreal.can_lift NNReal.canLift
-/

#print NNReal.eq /-
protected theorem eq {n m : ℝ≥0} : (n : ℝ) = (m : ℝ) → n = m :=
  Subtype.eq
#align nnreal.eq NNReal.eq
-/

#print NNReal.eq_iff /-
protected theorem eq_iff {n m : ℝ≥0} : (n : ℝ) = (m : ℝ) ↔ n = m :=
  Iff.intro NNReal.eq (congr_arg coe)
#align nnreal.eq_iff NNReal.eq_iff
-/

#print NNReal.ne_iff /-
theorem ne_iff {x y : ℝ≥0} : (x : ℝ) ≠ (y : ℝ) ↔ x ≠ y :=
  not_congr <| NNReal.eq_iff
#align nnreal.ne_iff NNReal.ne_iff
-/

#print NNReal.forall /-
protected theorem forall {p : ℝ≥0 → Prop} : (∀ x : ℝ≥0, p x) ↔ ∀ (x : ℝ) (hx : 0 ≤ x), p ⟨x, hx⟩ :=
  Subtype.forall
#align nnreal.forall NNReal.forall
-/

#print NNReal.exists /-
protected theorem exists {p : ℝ≥0 → Prop} : (∃ x : ℝ≥0, p x) ↔ ∃ (x : ℝ) (hx : 0 ≤ x), p ⟨x, hx⟩ :=
  Subtype.exists
#align nnreal.exists NNReal.exists
-/

#print Real.toNNReal /-
/-- Reinterpret a real number `r` as a non-negative real number. Returns `0` if `r < 0`. -/
noncomputable def Real.toNNReal (r : ℝ) : ℝ≥0 :=
  ⟨max r 0, le_max_right _ _⟩
#align real.to_nnreal Real.toNNReal
-/

#print Real.coe_toNNReal /-
theorem Real.coe_toNNReal (r : ℝ) (hr : 0 ≤ r) : (Real.toNNReal r : ℝ) = r :=
  max_eq_left hr
#align real.coe_to_nnreal Real.coe_toNNReal
-/

#print Real.toNNReal_of_nonneg /-
theorem Real.toNNReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : r.toNNReal = ⟨r, hr⟩ := by
  simp_rw [Real.toNNReal, max_eq_left hr]
#align real.to_nnreal_of_nonneg Real.toNNReal_of_nonneg
-/

#print Real.le_coe_toNNReal /-
theorem Real.le_coe_toNNReal (r : ℝ) : r ≤ Real.toNNReal r :=
  le_max_left r 0
#align real.le_coe_to_nnreal Real.le_coe_toNNReal
-/

#print NNReal.coe_nonneg /-
theorem coe_nonneg (r : ℝ≥0) : (0 : ℝ) ≤ r :=
  r.2
#align nnreal.coe_nonneg NNReal.coe_nonneg
-/

#print NNReal.coe_mk /-
@[norm_cast]
theorem coe_mk (a : ℝ) (ha) : ((⟨a, ha⟩ : ℝ≥0) : ℝ) = a :=
  rfl
#align nnreal.coe_mk NNReal.coe_mk
-/

example : Zero ℝ≥0 := by infer_instance

example : One ℝ≥0 := by infer_instance

example : Add ℝ≥0 := by infer_instance

noncomputable example : Sub ℝ≥0 := by infer_instance

example : Mul ℝ≥0 := by infer_instance

noncomputable example : Inv ℝ≥0 := by infer_instance

noncomputable example : Div ℝ≥0 := by infer_instance

example : LE ℝ≥0 := by infer_instance

example : Bot ℝ≥0 := by infer_instance

example : Inhabited ℝ≥0 := by infer_instance

example : Nontrivial ℝ≥0 := by infer_instance

#print NNReal.coe_injective /-
protected theorem coe_injective : Function.Injective (coe : ℝ≥0 → ℝ) :=
  Subtype.coe_injective
#align nnreal.coe_injective NNReal.coe_injective
-/

#print NNReal.coe_inj /-
@[simp, norm_cast]
protected theorem coe_inj {r₁ r₂ : ℝ≥0} : (r₁ : ℝ) = r₂ ↔ r₁ = r₂ :=
  NNReal.coe_injective.eq_iff
#align nnreal.coe_eq NNReal.coe_inj
-/

#print NNReal.coe_zero /-
protected theorem coe_zero : ((0 : ℝ≥0) : ℝ) = 0 :=
  rfl
#align nnreal.coe_zero NNReal.coe_zero
-/

#print NNReal.coe_one /-
protected theorem coe_one : ((1 : ℝ≥0) : ℝ) = 1 :=
  rfl
#align nnreal.coe_one NNReal.coe_one
-/

#print NNReal.coe_add /-
protected theorem coe_add (r₁ r₂ : ℝ≥0) : ((r₁ + r₂ : ℝ≥0) : ℝ) = r₁ + r₂ :=
  rfl
#align nnreal.coe_add NNReal.coe_add
-/

#print NNReal.coe_mul /-
protected theorem coe_mul (r₁ r₂ : ℝ≥0) : ((r₁ * r₂ : ℝ≥0) : ℝ) = r₁ * r₂ :=
  rfl
#align nnreal.coe_mul NNReal.coe_mul
-/

#print NNReal.coe_inv /-
protected theorem coe_inv (r : ℝ≥0) : ((r⁻¹ : ℝ≥0) : ℝ) = r⁻¹ :=
  rfl
#align nnreal.coe_inv NNReal.coe_inv
-/

#print NNReal.coe_div /-
protected theorem coe_div (r₁ r₂ : ℝ≥0) : ((r₁ / r₂ : ℝ≥0) : ℝ) = r₁ / r₂ :=
  rfl
#align nnreal.coe_div NNReal.coe_div
-/

@[simp, norm_cast]
protected theorem coe_bit0 (r : ℝ≥0) : ((bit0 r : ℝ≥0) : ℝ) = bit0 r :=
  rfl
#align nnreal.coe_bit0 NNReal.coe_bit0

@[simp, norm_cast]
protected theorem coe_bit1 (r : ℝ≥0) : ((bit1 r : ℝ≥0) : ℝ) = bit1 r :=
  rfl
#align nnreal.coe_bit1 NNReal.coe_bit1

#print NNReal.coe_two /-
protected theorem coe_two : ((2 : ℝ≥0) : ℝ) = 2 :=
  rfl
#align nnreal.coe_two NNReal.coe_two
-/

#print NNReal.coe_sub /-
@[simp, norm_cast]
protected theorem coe_sub {r₁ r₂ : ℝ≥0} (h : r₂ ≤ r₁) : ((r₁ - r₂ : ℝ≥0) : ℝ) = r₁ - r₂ :=
  max_eq_left <| le_sub_comm.2 <| by simp [show (r₂ : ℝ) ≤ r₁ from h]
#align nnreal.coe_sub NNReal.coe_sub
-/

/- warning: nnreal.coe_eq_zero clashes with coe_eq_zero -> NNReal.coe_eq_zero
Case conversion may be inaccurate. Consider using '#align nnreal.coe_eq_zero NNReal.coe_eq_zeroₓ'. -/
#print NNReal.coe_eq_zero /-
@[simp, norm_cast]
protected theorem coe_eq_zero (r : ℝ≥0) : ↑r = (0 : ℝ) ↔ r = 0 := by
  rw [← NNReal.coe_zero, NNReal.coe_inj]
#align nnreal.coe_eq_zero NNReal.coe_eq_zero
-/

/- warning: nnreal.coe_eq_one clashes with coe_inj_one -> NNReal.coe_eq_one
Case conversion may be inaccurate. Consider using '#align nnreal.coe_eq_one NNReal.coe_eq_oneₓ'. -/
#print NNReal.coe_eq_one /-
@[simp, norm_cast]
protected theorem coe_eq_one (r : ℝ≥0) : ↑r = (1 : ℝ) ↔ r = 1 := by
  rw [← NNReal.coe_one, NNReal.coe_inj]
#align nnreal.coe_eq_one NNReal.coe_eq_one
-/

#print NNReal.coe_ne_zero /-
theorem coe_ne_zero {r : ℝ≥0} : (r : ℝ) ≠ 0 ↔ r ≠ 0 := by norm_cast
#align nnreal.coe_ne_zero NNReal.coe_ne_zero
-/

example : CommSemiring ℝ≥0 := by infer_instance

#print NNReal.toRealHom /-
/-- Coercion `ℝ≥0 → ℝ` as a `ring_hom`. -/
def toRealHom : ℝ≥0 →+* ℝ :=
  ⟨coe, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_zero, NNReal.coe_add⟩
#align nnreal.to_real_hom NNReal.toRealHom
-/

#print NNReal.coe_toRealHom /-
@[simp]
theorem coe_toRealHom : ⇑toRealHom = coe :=
  rfl
#align nnreal.coe_to_real_hom NNReal.coe_toRealHom
-/

section Actions

/-- A `mul_action` over `ℝ` restricts to a `mul_action` over `ℝ≥0`. -/
instance {M : Type _} [MulAction ℝ M] : MulAction ℝ≥0 M :=
  MulAction.compHom M toRealHom.toMonoidHom

#print NNReal.smul_def /-
theorem smul_def {M : Type _} [MulAction ℝ M] (c : ℝ≥0) (x : M) : c • x = (c : ℝ) • x :=
  rfl
#align nnreal.smul_def NNReal.smul_def
-/

instance {M N : Type _} [MulAction ℝ M] [MulAction ℝ N] [SMul M N] [IsScalarTower ℝ M N] :
    IsScalarTower ℝ≥0 M N where smul_assoc r := (smul_assoc (r : ℝ) : _)

#print NNReal.smulCommClass_left /-
instance smulCommClass_left {M N : Type _} [MulAction ℝ N] [SMul M N] [SMulCommClass ℝ M N] :
    SMulCommClass ℝ≥0 M N where smul_comm r := (smul_comm (r : ℝ) : _)
#align nnreal.smul_comm_class_left NNReal.smulCommClass_left
-/

#print NNReal.smulCommClass_right /-
instance smulCommClass_right {M N : Type _} [MulAction ℝ N] [SMul M N] [SMulCommClass M ℝ N] :
    SMulCommClass M ℝ≥0 N where smul_comm m r := (smul_comm m (r : ℝ) : _)
#align nnreal.smul_comm_class_right NNReal.smulCommClass_right
-/

/-- A `distrib_mul_action` over `ℝ` restricts to a `distrib_mul_action` over `ℝ≥0`. -/
instance {M : Type _} [AddMonoid M] [DistribMulAction ℝ M] : DistribMulAction ℝ≥0 M :=
  DistribMulAction.compHom M toRealHom.toMonoidHom

/-- A `module` over `ℝ` restricts to a `module` over `ℝ≥0`. -/
instance {M : Type _} [AddCommMonoid M] [Module ℝ M] : Module ℝ≥0 M :=
  Module.compHom M toRealHom

/-- An `algebra` over `ℝ` restricts to an `algebra` over `ℝ≥0`. -/
instance {A : Type _} [Semiring A] [Algebra ℝ A] : Algebra ℝ≥0 A
    where
  smul := (· • ·)
  commutes' r x := by simp [Algebra.commutes]
  smul_def' r x := by simp [← Algebra.smul_def (r : ℝ) x, smul_def]
  toRingHom := (algebraMap ℝ A).comp (toRealHom : ℝ≥0 →+* ℝ)

-- verify that the above produces instances we might care about
example : Algebra ℝ≥0 ℝ := by infer_instance

example : DistribMulAction ℝ≥0ˣ ℝ := by infer_instance

end Actions

example : MonoidWithZero ℝ≥0 := by infer_instance

example : CommMonoidWithZero ℝ≥0 := by infer_instance

noncomputable example : CommGroupWithZero ℝ≥0 := by infer_instance

#print NNReal.coe_indicator /-
@[simp, norm_cast]
theorem coe_indicator {α} (s : Set α) (f : α → ℝ≥0) (a : α) :
    ((s.indicator f a : ℝ≥0) : ℝ) = s.indicator (fun x => f x) a :=
  (toRealHom : ℝ≥0 →+ ℝ).map_indicator _ _ _
#align nnreal.coe_indicator NNReal.coe_indicator
-/

#print NNReal.coe_pow /-
@[simp, norm_cast]
theorem coe_pow (r : ℝ≥0) (n : ℕ) : ((r ^ n : ℝ≥0) : ℝ) = r ^ n :=
  toRealHom.map_pow r n
#align nnreal.coe_pow NNReal.coe_pow
-/

#print NNReal.coe_zpow /-
@[simp, norm_cast]
theorem coe_zpow (r : ℝ≥0) (n : ℤ) : ((r ^ n : ℝ≥0) : ℝ) = r ^ n := by cases n <;> simp
#align nnreal.coe_zpow NNReal.coe_zpow
-/

#print NNReal.coe_list_sum /-
@[norm_cast]
theorem coe_list_sum (l : List ℝ≥0) : ((l.Sum : ℝ≥0) : ℝ) = (l.map coe).Sum :=
  toRealHom.map_list_sum l
#align nnreal.coe_list_sum NNReal.coe_list_sum
-/

#print NNReal.coe_list_prod /-
@[norm_cast]
theorem coe_list_prod (l : List ℝ≥0) : ((l.Prod : ℝ≥0) : ℝ) = (l.map coe).Prod :=
  toRealHom.map_list_prod l
#align nnreal.coe_list_prod NNReal.coe_list_prod
-/

#print NNReal.coe_multiset_sum /-
@[norm_cast]
theorem coe_multiset_sum (s : Multiset ℝ≥0) : ((s.Sum : ℝ≥0) : ℝ) = (s.map coe).Sum :=
  toRealHom.map_multiset_sum s
#align nnreal.coe_multiset_sum NNReal.coe_multiset_sum
-/

#print NNReal.coe_multiset_prod /-
@[norm_cast]
theorem coe_multiset_prod (s : Multiset ℝ≥0) : ((s.Prod : ℝ≥0) : ℝ) = (s.map coe).Prod :=
  toRealHom.map_multiset_prod s
#align nnreal.coe_multiset_prod NNReal.coe_multiset_prod
-/

#print NNReal.coe_sum /-
@[norm_cast]
theorem coe_sum {α} {s : Finset α} {f : α → ℝ≥0} : ↑(∑ a in s, f a) = ∑ a in s, (f a : ℝ) :=
  toRealHom.map_sum _ _
#align nnreal.coe_sum NNReal.coe_sum
-/

#print Real.toNNReal_sum_of_nonneg /-
theorem Real.toNNReal_sum_of_nonneg {α} {s : Finset α} {f : α → ℝ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    Real.toNNReal (∑ a in s, f a) = ∑ a in s, Real.toNNReal (f a) :=
  by
  rw [← NNReal.coe_inj, NNReal.coe_sum, Real.coe_toNNReal _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs => by rw [Real.coe_toNNReal _ (hf x hxs)]
#align real.to_nnreal_sum_of_nonneg Real.toNNReal_sum_of_nonneg
-/

#print NNReal.coe_prod /-
@[norm_cast]
theorem coe_prod {α} {s : Finset α} {f : α → ℝ≥0} : ↑(∏ a in s, f a) = ∏ a in s, (f a : ℝ) :=
  toRealHom.map_prod _ _
#align nnreal.coe_prod NNReal.coe_prod
-/

#print Real.toNNReal_prod_of_nonneg /-
theorem Real.toNNReal_prod_of_nonneg {α} {s : Finset α} {f : α → ℝ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    Real.toNNReal (∏ a in s, f a) = ∏ a in s, Real.toNNReal (f a) :=
  by
  rw [← NNReal.coe_inj, NNReal.coe_prod, Real.coe_toNNReal _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs => by rw [Real.coe_toNNReal _ (hf x hxs)]
#align real.to_nnreal_prod_of_nonneg Real.toNNReal_prod_of_nonneg
-/

#print NNReal.coe_nsmul /-
theorem coe_nsmul (r : ℝ≥0) (n : ℕ) : ↑(n • r) = n • (r : ℝ) := by norm_cast
#align nnreal.nsmul_coe NNReal.coe_nsmul
-/

#print NNReal.coe_nat_cast /-
@[simp, norm_cast]
protected theorem coe_nat_cast (n : ℕ) : (↑(↑n : ℝ≥0) : ℝ) = n :=
  map_natCast toRealHom n
#align nnreal.coe_nat_cast NNReal.coe_nat_cast
-/

noncomputable example : LinearOrder ℝ≥0 := by infer_instance

#print NNReal.coe_le_coe /-
@[simp, norm_cast]
protected theorem coe_le_coe {r₁ r₂ : ℝ≥0} : (r₁ : ℝ) ≤ r₂ ↔ r₁ ≤ r₂ :=
  Iff.rfl
#align nnreal.coe_le_coe NNReal.coe_le_coe
-/

#print NNReal.coe_lt_coe /-
@[simp, norm_cast]
protected theorem coe_lt_coe {r₁ r₂ : ℝ≥0} : (r₁ : ℝ) < r₂ ↔ r₁ < r₂ :=
  Iff.rfl
#align nnreal.coe_lt_coe NNReal.coe_lt_coe
-/

#print NNReal.coe_pos /-
@[simp, norm_cast]
protected theorem coe_pos {r : ℝ≥0} : (0 : ℝ) < r ↔ 0 < r :=
  Iff.rfl
#align nnreal.coe_pos NNReal.coe_pos
-/

#print NNReal.coe_mono /-
protected theorem coe_mono : Monotone (coe : ℝ≥0 → ℝ) := fun _ _ => NNReal.coe_le_coe.2
#align nnreal.coe_mono NNReal.coe_mono
-/

#print Real.toNNReal_mono /-
protected theorem Real.toNNReal_mono : Monotone Real.toNNReal := fun x y h =>
  max_le_max h (le_refl 0)
#align real.to_nnreal_mono Real.toNNReal_mono
-/

#print Real.toNNReal_coe /-
@[simp]
theorem Real.toNNReal_coe {r : ℝ≥0} : Real.toNNReal r = r :=
  NNReal.eq <| max_eq_left r.2
#align real.to_nnreal_coe Real.toNNReal_coe
-/

#print NNReal.mk_natCast /-
@[simp]
theorem mk_natCast (n : ℕ) : @Eq ℝ≥0 (⟨(n : ℝ), n.cast_nonneg⟩ : ℝ≥0) n :=
  NNReal.eq (NNReal.coe_nat_cast n).symm
#align nnreal.mk_coe_nat NNReal.mk_natCast
-/

#print NNReal.toNNReal_coe_nat /-
@[simp]
theorem toNNReal_coe_nat (n : ℕ) : Real.toNNReal n = n :=
  NNReal.eq <| by simp [Real.coe_toNNReal]
#align nnreal.to_nnreal_coe_nat NNReal.toNNReal_coe_nat
-/

#print NNReal.gi /-
/-- `real.to_nnreal` and `coe : ℝ≥0 → ℝ` form a Galois insertion. -/
noncomputable def gi : GaloisInsertion Real.toNNReal coe :=
  GaloisInsertion.monotoneIntro NNReal.coe_mono Real.toNNReal_mono Real.le_coe_toNNReal fun _ =>
    Real.toNNReal_coe
#align nnreal.gi NNReal.gi
-/

-- note that anything involving the (decidability of the) linear order,
-- will be noncomputable, everything else should not be.
example : OrderBot ℝ≥0 := by infer_instance

example : PartialOrder ℝ≥0 := by infer_instance

noncomputable example : CanonicallyLinearOrderedAddCommMonoid ℝ≥0 := by infer_instance

noncomputable example : LinearOrderedAddCommMonoid ℝ≥0 := by infer_instance

example : DistribLattice ℝ≥0 := by infer_instance

example : SemilatticeInf ℝ≥0 := by infer_instance

example : SemilatticeSup ℝ≥0 := by infer_instance

noncomputable example : LinearOrderedSemiring ℝ≥0 := by infer_instance

example : OrderedCommSemiring ℝ≥0 := by infer_instance

noncomputable example : LinearOrderedCommMonoid ℝ≥0 := by infer_instance

noncomputable example : LinearOrderedCommMonoidWithZero ℝ≥0 := by infer_instance

noncomputable example : LinearOrderedCommGroupWithZero ℝ≥0 := by infer_instance

example : CanonicallyOrderedCommSemiring ℝ≥0 := by infer_instance

example : DenselyOrdered ℝ≥0 := by infer_instance

example : NoMaxOrder ℝ≥0 := by infer_instance

#print NNReal.orderIsoIccZeroCoe /-
/-- If `a` is a nonnegative real number, then the closed interval `[0, a]` in `ℝ` is order
isomorphic to the interval `set.Iic a`. -/
@[simps apply_coe_coe]
def orderIsoIccZeroCoe (a : ℝ≥0) : Set.Icc (0 : ℝ) a ≃o Set.Iic a
    where
  toEquiv := Equiv.Set.sep (Set.Ici 0) fun x => x ≤ a
  map_rel_iff' x y := Iff.rfl
#align nnreal.order_iso_Icc_zero_coe NNReal.orderIsoIccZeroCoe
-/

#print NNReal.orderIsoIccZeroCoe_symm_apply_coe /-
@[simp]
theorem orderIsoIccZeroCoe_symm_apply_coe (a : ℝ≥0) (b : Set.Iic a) :
    ((orderIsoIccZeroCoe a).symm b : ℝ) = b :=
  rfl
#align nnreal.order_iso_Icc_zero_coe_symm_apply_coe NNReal.orderIsoIccZeroCoe_symm_apply_coe
-/

#print NNReal.coe_image /-
-- note we need the `@` to make the `has_mem.mem` have a sensible type
theorem coe_image {s : Set ℝ≥0} :
    coe '' s = {x : ℝ | ∃ h : 0 ≤ x, @Membership.Mem ℝ≥0 _ _ ⟨x, h⟩ s} :=
  Subtype.coe_image
#align nnreal.coe_image NNReal.coe_image
-/

#print NNReal.bddAbove_coe /-
theorem bddAbove_coe {s : Set ℝ≥0} : BddAbove ((coe : ℝ≥0 → ℝ) '' s) ↔ BddAbove s :=
  Iff.intro
    (fun ⟨b, hb⟩ =>
      ⟨Real.toNNReal b, fun ⟨y, hy⟩ hys =>
        show y ≤ max b 0 from le_max_of_le_left <| hb <| Set.mem_image_of_mem _ hys⟩)
    fun ⟨b, hb⟩ => ⟨b, fun y ⟨x, hx, Eq⟩ => Eq ▸ hb hx⟩
#align nnreal.bdd_above_coe NNReal.bddAbove_coe
-/

#print NNReal.bddBelow_coe /-
theorem bddBelow_coe (s : Set ℝ≥0) : BddBelow ((coe : ℝ≥0 → ℝ) '' s) :=
  ⟨0, fun r ⟨q, _, Eq⟩ => Eq ▸ q.2⟩
#align nnreal.bdd_below_coe NNReal.bddBelow_coe
-/

noncomputable instance : ConditionallyCompleteLinearOrderBot ℝ≥0 :=
  Nonneg.conditionallyCompleteLinearOrderBot Real.sSup_empty.le

#print NNReal.coe_sSup /-
@[norm_cast]
theorem coe_sSup (s : Set ℝ≥0) : (↑(sSup s) : ℝ) = sSup ((coe : ℝ≥0 → ℝ) '' s) :=
  Eq.symm <|
    @subset_sSup_of_within ℝ (Set.Ici 0) _ ⟨(0 : ℝ≥0)⟩ s <|
      Real.sSup_nonneg _ fun y ⟨x, _, hy⟩ => hy ▸ x.2
#align nnreal.coe_Sup NNReal.coe_sSup
-/

#print NNReal.coe_iSup /-
@[norm_cast]
theorem coe_iSup {ι : Sort _} (s : ι → ℝ≥0) : (↑(⨆ i, s i) : ℝ) = ⨆ i, s i := by
  rw [iSup, iSup, coe_Sup, Set.range_comp]
#align nnreal.coe_supr NNReal.coe_iSup
-/

#print NNReal.coe_sInf /-
@[norm_cast]
theorem coe_sInf (s : Set ℝ≥0) : (↑(sInf s) : ℝ) = sInf ((coe : ℝ≥0 → ℝ) '' s) :=
  Eq.symm <|
    @subset_sInf_of_within ℝ (Set.Ici 0) _ ⟨(0 : ℝ≥0)⟩ s <|
      Real.sInf_nonneg _ fun y ⟨x, _, hy⟩ => hy ▸ x.2
#align nnreal.coe_Inf NNReal.coe_sInf
-/

#print NNReal.sInf_empty /-
@[simp]
theorem sInf_empty : sInf (∅ : Set ℝ≥0) = 0 := by
  rw [← NNReal.coe_eq_zero, coe_Inf, Set.image_empty, Real.sInf_empty]
#align nnreal.Inf_empty NNReal.sInf_empty
-/

#print NNReal.coe_iInf /-
@[norm_cast]
theorem coe_iInf {ι : Sort _} (s : ι → ℝ≥0) : (↑(⨅ i, s i) : ℝ) = ⨅ i, s i := by
  rw [iInf, iInf, coe_Inf, Set.range_comp]
#align nnreal.coe_infi NNReal.coe_iInf
-/

#print NNReal.le_iInf_add_iInf /-
theorem le_iInf_add_iInf {ι ι' : Sort _} [Nonempty ι] [Nonempty ι'] {f : ι → ℝ≥0} {g : ι' → ℝ≥0}
    {a : ℝ≥0} (h : ∀ i j, a ≤ f i + g j) : a ≤ (⨅ i, f i) + ⨅ j, g j :=
  by
  rw [← NNReal.coe_le_coe, NNReal.coe_add, coe_infi, coe_infi]
  exact le_ciInf_add_ciInf h
#align nnreal.le_infi_add_infi NNReal.le_iInf_add_iInf
-/

example : Archimedean ℝ≥0 := by infer_instance

#print NNReal.covariant_add /-
-- TODO: why are these three instances necessary? why aren't they inferred?
instance covariant_add : CovariantClass ℝ≥0 ℝ≥0 (· + ·) (· ≤ ·) :=
  OrderedAddCommMonoid.toCovariantClassLeft ℝ≥0
#align nnreal.covariant_add NNReal.covariant_add
-/

#print NNReal.contravariant_add /-
instance contravariant_add : ContravariantClass ℝ≥0 ℝ≥0 (· + ·) (· < ·) :=
  OrderedCancelAddCommMonoid.toContravariantClassLeft ℝ≥0
#align nnreal.contravariant_add NNReal.contravariant_add
-/

#print NNReal.covariant_mul /-
instance covariant_mul : CovariantClass ℝ≥0 ℝ≥0 (· * ·) (· ≤ ·) :=
  OrderedCommMonoid.toCovariantClassLeft ℝ≥0
#align nnreal.covariant_mul NNReal.covariant_mul
-/

#print NNReal.le_of_forall_pos_le_add /-
-- Why isn't `nnreal.contravariant_add` inferred?
theorem le_of_forall_pos_le_add {a b : ℝ≥0} (h : ∀ ε, 0 < ε → a ≤ b + ε) : a ≤ b :=
  @le_of_forall_pos_le_add _ _ _ _ _ _ NNReal.contravariant_add _ _ h
#align nnreal.le_of_forall_pos_le_add NNReal.le_of_forall_pos_le_add
-/

#print NNReal.lt_iff_exists_rat_btwn /-
theorem lt_iff_exists_rat_btwn (a b : ℝ≥0) :
    a < b ↔ ∃ q : ℚ, 0 ≤ q ∧ a < Real.toNNReal q ∧ Real.toNNReal q < b :=
  Iff.intro
    (fun h : (↑a : ℝ) < (↑b : ℝ) =>
      let ⟨q, haq, hqb⟩ := exists_rat_btwn h
      have : 0 ≤ (q : ℝ) := le_trans a.2 <| le_of_lt haq
      ⟨q, Rat.cast_nonneg.1 this, by
        simp [Real.coe_toNNReal _ this, nnreal.coe_lt_coe.symm, haq, hqb]⟩)
    fun ⟨q, _, haq, hqb⟩ => lt_trans haq hqb
#align nnreal.lt_iff_exists_rat_btwn NNReal.lt_iff_exists_rat_btwn
-/

#print NNReal.bot_eq_zero /-
theorem bot_eq_zero : (⊥ : ℝ≥0) = 0 :=
  rfl
#align nnreal.bot_eq_zero NNReal.bot_eq_zero
-/

#print NNReal.mul_sup /-
theorem mul_sup (a b c : ℝ≥0) : a * (b ⊔ c) = a * b ⊔ a * c :=
  mul_max_of_nonneg _ _ <| zero_le a
#align nnreal.mul_sup NNReal.mul_sup
-/

#print NNReal.sup_mul /-
theorem sup_mul (a b c : ℝ≥0) : (a ⊔ b) * c = a * c ⊔ b * c :=
  max_mul_of_nonneg _ _ <| zero_le c
#align nnreal.sup_mul NNReal.sup_mul
-/

#print NNReal.mul_finset_sup /-
theorem mul_finset_sup {α} (r : ℝ≥0) (s : Finset α) (f : α → ℝ≥0) :
    r * s.sup f = s.sup fun a => r * f a :=
  Finset.comp_sup_eq_sup_comp _ (NNReal.mul_sup r) (MulZeroClass.mul_zero r)
#align nnreal.mul_finset_sup NNReal.mul_finset_sup
-/

#print NNReal.finset_sup_mul /-
theorem finset_sup_mul {α} (s : Finset α) (f : α → ℝ≥0) (r : ℝ≥0) :
    s.sup f * r = s.sup fun a => f a * r :=
  Finset.comp_sup_eq_sup_comp (· * r) (fun x y => NNReal.sup_mul x y r) (MulZeroClass.zero_mul r)
#align nnreal.finset_sup_mul NNReal.finset_sup_mul
-/

#print NNReal.finset_sup_div /-
theorem finset_sup_div {α} {f : α → ℝ≥0} {s : Finset α} (r : ℝ≥0) :
    s.sup f / r = s.sup fun a => f a / r := by simp only [div_eq_inv_mul, mul_finset_sup]
#align nnreal.finset_sup_div NNReal.finset_sup_div
-/

#print NNReal.coe_max /-
@[simp, norm_cast]
theorem coe_max (x y : ℝ≥0) : ((max x y : ℝ≥0) : ℝ) = max (x : ℝ) (y : ℝ) :=
  NNReal.coe_mono.map_max
#align nnreal.coe_max NNReal.coe_max
-/

#print NNReal.coe_min /-
@[simp, norm_cast]
theorem coe_min (x y : ℝ≥0) : ((min x y : ℝ≥0) : ℝ) = min (x : ℝ) (y : ℝ) :=
  NNReal.coe_mono.map_min
#align nnreal.coe_min NNReal.coe_min
-/

#print NNReal.zero_le_coe /-
@[simp]
theorem zero_le_coe {q : ℝ≥0} : 0 ≤ (q : ℝ) :=
  q.2
#align nnreal.zero_le_coe NNReal.zero_le_coe
-/

end NNReal

namespace Real

section ToNnreal

#print Real.toNNReal_zero /-
@[simp]
theorem toNNReal_zero : Real.toNNReal 0 = 0 := by simp [Real.toNNReal] <;> rfl
#align real.to_nnreal_zero Real.toNNReal_zero
-/

#print Real.toNNReal_one /-
@[simp]
theorem toNNReal_one : Real.toNNReal 1 = 1 := by
  simp [Real.toNNReal, max_eq_left (zero_le_one : (0 : ℝ) ≤ 1)] <;> rfl
#align real.to_nnreal_one Real.toNNReal_one
-/

#print Real.toNNReal_pos /-
@[simp]
theorem toNNReal_pos {r : ℝ} : 0 < Real.toNNReal r ↔ 0 < r := by
  simp [Real.toNNReal, nnreal.coe_lt_coe.symm, lt_irrefl]
#align real.to_nnreal_pos Real.toNNReal_pos
-/

#print Real.toNNReal_eq_zero /-
@[simp]
theorem toNNReal_eq_zero {r : ℝ} : Real.toNNReal r = 0 ↔ r ≤ 0 := by
  simpa [-to_nnreal_pos] using not_iff_not.2 (@to_nnreal_pos r)
#align real.to_nnreal_eq_zero Real.toNNReal_eq_zero
-/

#print Real.toNNReal_of_nonpos /-
theorem toNNReal_of_nonpos {r : ℝ} : r ≤ 0 → Real.toNNReal r = 0 :=
  toNNReal_eq_zero.2
#align real.to_nnreal_of_nonpos Real.toNNReal_of_nonpos
-/

#print Real.coe_toNNReal' /-
@[simp]
theorem coe_toNNReal' (r : ℝ) : (Real.toNNReal r : ℝ) = max r 0 :=
  rfl
#align real.coe_to_nnreal' Real.coe_toNNReal'
-/

#print Real.toNNReal_le_toNNReal_iff /-
@[simp]
theorem toNNReal_le_toNNReal_iff {r p : ℝ} (hp : 0 ≤ p) :
    Real.toNNReal r ≤ Real.toNNReal p ↔ r ≤ p := by simp [nnreal.coe_le_coe.symm, Real.toNNReal, hp]
#align real.to_nnreal_le_to_nnreal_iff Real.toNNReal_le_toNNReal_iff
-/

#print Real.toNNReal_eq_toNNReal_iff /-
@[simp]
theorem toNNReal_eq_toNNReal_iff {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    Real.toNNReal r = Real.toNNReal p ↔ r = p := by simp [← NNReal.coe_inj, coe_to_nnreal, hr, hp]
#align real.to_nnreal_eq_to_nnreal_iff Real.toNNReal_eq_toNNReal_iff
-/

#print Real.toNNReal_lt_toNNReal_iff' /-
@[simp]
theorem toNNReal_lt_toNNReal_iff' {r p : ℝ} : Real.toNNReal r < Real.toNNReal p ↔ r < p ∧ 0 < p :=
  NNReal.coe_lt_coe.symm.trans max_lt_max_left_iff
#align real.to_nnreal_lt_to_nnreal_iff' Real.toNNReal_lt_toNNReal_iff'
-/

#print Real.toNNReal_lt_toNNReal_iff /-
theorem toNNReal_lt_toNNReal_iff {r p : ℝ} (h : 0 < p) :
    Real.toNNReal r < Real.toNNReal p ↔ r < p :=
  toNNReal_lt_toNNReal_iff'.trans (and_iff_left h)
#align real.to_nnreal_lt_to_nnreal_iff Real.toNNReal_lt_toNNReal_iff
-/

#print Real.toNNReal_lt_toNNReal_iff_of_nonneg /-
theorem toNNReal_lt_toNNReal_iff_of_nonneg {r p : ℝ} (hr : 0 ≤ r) :
    Real.toNNReal r < Real.toNNReal p ↔ r < p :=
  toNNReal_lt_toNNReal_iff'.trans ⟨And.left, fun h => ⟨h, lt_of_le_of_lt hr h⟩⟩
#align real.to_nnreal_lt_to_nnreal_iff_of_nonneg Real.toNNReal_lt_toNNReal_iff_of_nonneg
-/

#print Real.toNNReal_add /-
@[simp]
theorem toNNReal_add {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    Real.toNNReal (r + p) = Real.toNNReal r + Real.toNNReal p :=
  NNReal.eq <| by simp [Real.toNNReal, hr, hp, add_nonneg]
#align real.to_nnreal_add Real.toNNReal_add
-/

#print Real.toNNReal_add_toNNReal /-
theorem toNNReal_add_toNNReal {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    Real.toNNReal r + Real.toNNReal p = Real.toNNReal (r + p) :=
  (Real.toNNReal_add hr hp).symm
#align real.to_nnreal_add_to_nnreal Real.toNNReal_add_toNNReal
-/

#print Real.toNNReal_le_toNNReal /-
theorem toNNReal_le_toNNReal {r p : ℝ} (h : r ≤ p) : Real.toNNReal r ≤ Real.toNNReal p :=
  Real.toNNReal_mono h
#align real.to_nnreal_le_to_nnreal Real.toNNReal_le_toNNReal
-/

#print Real.toNNReal_add_le /-
theorem toNNReal_add_le {r p : ℝ} : Real.toNNReal (r + p) ≤ Real.toNNReal r + Real.toNNReal p :=
  NNReal.coe_le_coe.1 <| max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) NNReal.zero_le_coe
#align real.to_nnreal_add_le Real.toNNReal_add_le
-/

#print Real.toNNReal_le_iff_le_coe /-
theorem toNNReal_le_iff_le_coe {r : ℝ} {p : ℝ≥0} : Real.toNNReal r ≤ p ↔ r ≤ ↑p :=
  NNReal.gi.gc r p
#align real.to_nnreal_le_iff_le_coe Real.toNNReal_le_iff_le_coe
-/

#print Real.le_toNNReal_iff_coe_le /-
theorem le_toNNReal_iff_coe_le {r : ℝ≥0} {p : ℝ} (hp : 0 ≤ p) : r ≤ Real.toNNReal p ↔ ↑r ≤ p := by
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal p hp]
#align real.le_to_nnreal_iff_coe_le Real.le_toNNReal_iff_coe_le
-/

#print Real.le_toNNReal_iff_coe_le' /-
theorem le_toNNReal_iff_coe_le' {r : ℝ≥0} {p : ℝ} (hr : 0 < r) : r ≤ Real.toNNReal p ↔ ↑r ≤ p :=
  (le_or_lt 0 p).elim le_toNNReal_iff_coe_le fun hp => by
    simp only [(hp.trans_le r.coe_nonneg).not_le, to_nnreal_eq_zero.2 hp.le, hr.not_le]
#align real.le_to_nnreal_iff_coe_le' Real.le_toNNReal_iff_coe_le'
-/

#print Real.toNNReal_lt_iff_lt_coe /-
theorem toNNReal_lt_iff_lt_coe {r : ℝ} {p : ℝ≥0} (ha : 0 ≤ r) : Real.toNNReal r < p ↔ r < ↑p := by
  rw [← NNReal.coe_lt_coe, Real.coe_toNNReal r ha]
#align real.to_nnreal_lt_iff_lt_coe Real.toNNReal_lt_iff_lt_coe
-/

#print Real.lt_toNNReal_iff_coe_lt /-
theorem lt_toNNReal_iff_coe_lt {r : ℝ≥0} {p : ℝ} : r < Real.toNNReal p ↔ ↑r < p :=
  by
  cases le_total 0 p
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal p h]
  · rw [to_nnreal_eq_zero.2 h]; constructor
    · intro; have := not_lt_of_le (zero_le r); contradiction
    · intro rp; have : ¬p ≤ 0 := not_le_of_lt (lt_of_le_of_lt (NNReal.coe_nonneg _) rp)
      contradiction
#align real.lt_to_nnreal_iff_coe_lt Real.lt_toNNReal_iff_coe_lt
-/

@[simp]
theorem toNNReal_bit0 (r : ℝ) : Real.toNNReal (bit0 r) = bit0 (Real.toNNReal r) :=
  by
  cases' le_total r 0 with hr hr
  · rw [to_nnreal_of_nonpos hr, to_nnreal_of_nonpos, bit0_zero]
    exact add_nonpos hr hr
  · exact to_nnreal_add hr hr
#align real.to_nnreal_bit0 Real.toNNReal_bit0

@[simp]
theorem toNNReal_bit1 {r : ℝ} (hr : 0 ≤ r) : Real.toNNReal (bit1 r) = bit1 (Real.toNNReal r) :=
  (Real.toNNReal_add (by simp [hr]) zero_le_one).trans (by simp [bit1])
#align real.to_nnreal_bit1 Real.toNNReal_bit1

#print Real.toNNReal_pow /-
theorem toNNReal_pow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : (x ^ n).toNNReal = x.toNNReal ^ n := by
  rw [← NNReal.coe_inj, NNReal.coe_pow, Real.coe_toNNReal _ (pow_nonneg hx _),
    Real.coe_toNNReal x hx]
#align real.to_nnreal_pow Real.toNNReal_pow
-/

end ToNnreal

end Real

open Real

namespace NNReal

section Mul

#print NNReal.mul_eq_mul_left /-
theorem mul_eq_mul_left {a b c : ℝ≥0} (h : a ≠ 0) : a * b = a * c ↔ b = c := by
  rw [mul_eq_mul_left_iff, or_iff_left h]
#align nnreal.mul_eq_mul_left NNReal.mul_eq_mul_left
-/

#print Real.toNNReal_mul /-
theorem Real.toNNReal_mul {p q : ℝ} (hp : 0 ≤ p) :
    Real.toNNReal (p * q) = Real.toNNReal p * Real.toNNReal q :=
  by
  cases' le_total 0 q with hq hq
  · apply NNReal.eq
    simp [Real.toNNReal, hp, hq, max_eq_left, mul_nonneg]
  · have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq
    rw [to_nnreal_eq_zero.2 hq, to_nnreal_eq_zero.2 hpq, MulZeroClass.mul_zero]
#align real.to_nnreal_mul Real.toNNReal_mul
-/

end Mul

section Pow

#print NNReal.pow_antitone_exp /-
theorem pow_antitone_exp {a : ℝ≥0} (m n : ℕ) (mn : m ≤ n) (a1 : a ≤ 1) : a ^ n ≤ a ^ m :=
  pow_le_pow_of_le_one (zero_le a) a1 mn
#align nnreal.pow_antitone_exp NNReal.pow_antitone_exp
-/

#print NNReal.exists_pow_lt_of_lt_one /-
theorem exists_pow_lt_of_lt_one {a b : ℝ≥0} (ha : 0 < a) (hb : b < 1) : ∃ n : ℕ, b ^ n < a := by
  simpa only [← coe_pow, NNReal.coe_lt_coe] using
    exists_pow_lt_of_lt_one (NNReal.coe_pos.2 ha) (NNReal.coe_lt_coe.2 hb)
#align nnreal.exists_pow_lt_of_lt_one NNReal.exists_pow_lt_of_lt_one
-/

#print NNReal.exists_mem_Ico_zpow /-
theorem exists_mem_Ico_zpow {x : ℝ≥0} {y : ℝ≥0} (hx : x ≠ 0) (hy : 1 < y) :
    ∃ n : ℤ, x ∈ Set.Ico (y ^ n) (y ^ (n + 1)) :=
  by
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, (y : ℝ) ^ n ≤ x ∧ (x : ℝ) < y ^ (n + 1) :=
    exists_mem_Ico_zpow (bot_lt_iff_ne_bot.mpr hx) hy
  rw [← NNReal.coe_zpow] at hn h'n
  exact ⟨n, hn, h'n⟩
#align nnreal.exists_mem_Ico_zpow NNReal.exists_mem_Ico_zpow
-/

#print NNReal.exists_mem_Ioc_zpow /-
theorem exists_mem_Ioc_zpow {x : ℝ≥0} {y : ℝ≥0} (hx : x ≠ 0) (hy : 1 < y) :
    ∃ n : ℤ, x ∈ Set.Ioc (y ^ n) (y ^ (n + 1)) :=
  by
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, (y : ℝ) ^ n < x ∧ (x : ℝ) ≤ y ^ (n + 1) :=
    exists_mem_Ioc_zpow (bot_lt_iff_ne_bot.mpr hx) hy
  rw [← NNReal.coe_zpow] at hn h'n
  exact ⟨n, hn, h'n⟩
#align nnreal.exists_mem_Ioc_zpow NNReal.exists_mem_Ioc_zpow
-/

end Pow

section Sub

/-!
### Lemmas about subtraction

In this section we provide a few lemmas about subtraction that do not fit well into any other
typeclass. For lemmas about subtraction and addition see lemmas
about `has_ordered_sub` in the file `algebra.order.sub`. See also `mul_tsub` and `tsub_mul`. -/


#print NNReal.sub_def /-
theorem sub_def {r p : ℝ≥0} : r - p = Real.toNNReal (r - p) :=
  rfl
#align nnreal.sub_def NNReal.sub_def
-/

#print NNReal.coe_sub_def /-
theorem coe_sub_def {r p : ℝ≥0} : ↑(r - p) = max (r - p : ℝ) 0 :=
  rfl
#align nnreal.coe_sub_def NNReal.coe_sub_def
-/

example : OrderedSub ℝ≥0 := by infer_instance

#print NNReal.sub_div /-
theorem sub_div (a b c : ℝ≥0) : (a - b) / c = a / c - b / c :=
  tsub_div _ _ _
#align nnreal.sub_div NNReal.sub_div
-/

end Sub

section Inv

/- warning: nnreal.sum_div clashes with finset.sum_div -> Finset.sum_div
Case conversion may be inaccurate. Consider using '#align nnreal.sum_div Finset.sum_divₓ'. -/
#print Finset.sum_div /-
theorem sum_div {ι} (s : Finset ι) (f : ι → ℝ≥0) (b : ℝ≥0) :
    (∑ i in s, f i) / b = ∑ i in s, f i / b :=
  Finset.sum_div
#align nnreal.sum_div Finset.sum_div
-/

#print NNReal.inv_le /-
@[simp]
theorem inv_le {r p : ℝ≥0} (h : r ≠ 0) : r⁻¹ ≤ p ↔ 1 ≤ r * p := by
  rw [← mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h]
#align nnreal.inv_le NNReal.inv_le
-/

#print NNReal.inv_le_of_le_mul /-
theorem inv_le_of_le_mul {r p : ℝ≥0} (h : 1 ≤ r * p) : r⁻¹ ≤ p := by
  by_cases r = 0 <;> simp [*, inv_le]
#align nnreal.inv_le_of_le_mul NNReal.inv_le_of_le_mul
-/

#print NNReal.le_inv_iff_mul_le /-
@[simp]
theorem le_inv_iff_mul_le {r p : ℝ≥0} (h : p ≠ 0) : r ≤ p⁻¹ ↔ r * p ≤ 1 := by
  rw [← mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]
#align nnreal.le_inv_iff_mul_le NNReal.le_inv_iff_mul_le
-/

#print NNReal.lt_inv_iff_mul_lt /-
@[simp]
theorem lt_inv_iff_mul_lt {r p : ℝ≥0} (h : p ≠ 0) : r < p⁻¹ ↔ r * p < 1 := by
  rw [← mul_lt_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]
#align nnreal.lt_inv_iff_mul_lt NNReal.lt_inv_iff_mul_lt
-/

#print NNReal.mul_le_iff_le_inv /-
theorem mul_le_iff_le_inv {a b r : ℝ≥0} (hr : r ≠ 0) : r * a ≤ b ↔ a ≤ r⁻¹ * b :=
  by
  have : 0 < r := lt_of_le_of_ne (zero_le r) hr.symm
  rw [← mul_le_mul_left (inv_pos.mpr this), ← mul_assoc, inv_mul_cancel hr, one_mul]
#align nnreal.mul_le_iff_le_inv NNReal.mul_le_iff_le_inv
-/

#print NNReal.le_div_iff_mul_le /-
theorem le_div_iff_mul_le {a b r : ℝ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ a * r ≤ b :=
  le_div_iff₀ hr
#align nnreal.le_div_iff_mul_le NNReal.le_div_iff_mul_le
-/

#print NNReal.div_le_iff /-
theorem div_le_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a / r ≤ b ↔ a ≤ b * r :=
  div_le_iff₀ hr
#align nnreal.div_le_iff NNReal.div_le_iff
-/

#print NNReal.div_le_iff' /-
theorem div_le_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a / r ≤ b ↔ a ≤ r * b :=
  @div_le_iff' ℝ _ a r b <| pos_iff_ne_zero.2 hr
#align nnreal.div_le_iff' NNReal.div_le_iff'
-/

#print NNReal.div_le_of_le_mul /-
theorem div_le_of_le_mul {a b c : ℝ≥0} (h : a ≤ b * c) : a / c ≤ b :=
  if h0 : c = 0 then by simp [h0] else (div_le_iff h0).2 h
#align nnreal.div_le_of_le_mul NNReal.div_le_of_le_mul
-/

#print NNReal.div_le_of_le_mul' /-
theorem div_le_of_le_mul' {a b c : ℝ≥0} (h : a ≤ b * c) : a / b ≤ c :=
  div_le_of_le_mul <| mul_comm b c ▸ h
#align nnreal.div_le_of_le_mul' NNReal.div_le_of_le_mul'
-/

#print NNReal.le_div_iff /-
theorem le_div_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ a * r ≤ b :=
  @le_div_iff ℝ _ a b r <| pos_iff_ne_zero.2 hr
#align nnreal.le_div_iff NNReal.le_div_iff
-/

#print NNReal.le_div_iff' /-
theorem le_div_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ r * a ≤ b :=
  @le_div_iff' ℝ _ a b r <| pos_iff_ne_zero.2 hr
#align nnreal.le_div_iff' NNReal.le_div_iff'
-/

#print NNReal.div_lt_iff /-
theorem div_lt_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a / r < b ↔ a < b * r :=
  lt_iff_lt_of_le_iff_le (le_div_iff hr)
#align nnreal.div_lt_iff NNReal.div_lt_iff
-/

#print NNReal.div_lt_iff' /-
theorem div_lt_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a / r < b ↔ a < r * b :=
  lt_iff_lt_of_le_iff_le (le_div_iff' hr)
#align nnreal.div_lt_iff' NNReal.div_lt_iff'
-/

#print NNReal.lt_div_iff /-
theorem lt_div_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a < b / r ↔ a * r < b :=
  lt_iff_lt_of_le_iff_le (div_le_iff hr)
#align nnreal.lt_div_iff NNReal.lt_div_iff
-/

#print NNReal.lt_div_iff' /-
theorem lt_div_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a < b / r ↔ r * a < b :=
  lt_iff_lt_of_le_iff_le (div_le_iff' hr)
#align nnreal.lt_div_iff' NNReal.lt_div_iff'
-/

#print NNReal.mul_lt_of_lt_div /-
theorem mul_lt_of_lt_div {a b r : ℝ≥0} (h : a < b / r) : a * r < b :=
  by
  refine' (lt_div_iff fun hr => False.elim _).1 h
  subst r
  simpa using h
#align nnreal.mul_lt_of_lt_div NNReal.mul_lt_of_lt_div
-/

theorem div_le_div_left_of_le {a b c : ℝ≥0} (b0 : 0 < b) (c0 : 0 < c) (cb : c ≤ b) :
    a / b ≤ a / c := by
  by_cases a0 : a = 0
  · rw [a0, zero_div, zero_div]
  · cases' a with a ha
    replace a0 : 0 < a := lt_of_le_of_ne ha (ne_of_lt (zero_lt_iff.mpr a0))
    exact (div_le_div_left a0 b0 c0).mpr cb
#align nnreal.div_le_div_left_of_le NNReal.div_le_div_left_of_leₓ

#print NNReal.div_le_div_left /-
theorem div_le_div_left {a b c : ℝ≥0} (a0 : 0 < a) (b0 : 0 < b) (c0 : 0 < c) :
    a / b ≤ a / c ↔ c ≤ b :=
  div_le_div_left a0 b0 c0
#align nnreal.div_le_div_left NNReal.div_le_div_left
-/

#print NNReal.le_of_forall_lt_one_mul_le /-
theorem le_of_forall_lt_one_mul_le {x y : ℝ≥0} (h : ∀ a < 1, a * x ≤ y) : x ≤ y :=
  le_of_forall_ge_of_dense fun a ha =>
    by
    have hx : x ≠ 0 := pos_iff_ne_zero.1 (lt_of_le_of_lt (zero_le _) ha)
    have hx' : x⁻¹ ≠ 0 := by rwa [(· ≠ ·), inv_eq_zero]
    have : a * x⁻¹ < 1 := by rwa [← lt_inv_iff_mul_lt hx', inv_inv]
    have : a * x⁻¹ * x ≤ y := h _ this
    rwa [mul_assoc, inv_mul_cancel hx, mul_one] at this
#align nnreal.le_of_forall_lt_one_mul_le NNReal.le_of_forall_lt_one_mul_le
-/

#print NNReal.half_le_self /-
theorem half_le_self (a : ℝ≥0) : a / 2 ≤ a :=
  half_le_self bot_le
#align nnreal.half_le_self NNReal.half_le_self
-/

#print NNReal.half_lt_self /-
theorem half_lt_self {a : ℝ≥0} (h : a ≠ 0) : a / 2 < a :=
  half_lt_self h.bot_lt
#align nnreal.half_lt_self NNReal.half_lt_self
-/

#print NNReal.div_lt_one_of_lt /-
theorem div_lt_one_of_lt {a b : ℝ≥0} (h : a < b) : a / b < 1 :=
  by
  rwa [div_lt_iff, one_mul]
  exact ne_of_gt (lt_of_le_of_lt (zero_le _) h)
#align nnreal.div_lt_one_of_lt NNReal.div_lt_one_of_lt
-/

#print Real.toNNReal_inv /-
theorem Real.toNNReal_inv {x : ℝ} : Real.toNNReal x⁻¹ = (Real.toNNReal x)⁻¹ :=
  by
  by_cases hx : 0 ≤ x
  · nth_rw 1 [← Real.coe_toNNReal x hx]
    rw [← NNReal.coe_inv, Real.toNNReal_coe]
  · have hx' := le_of_not_ge hx
    rw [to_nnreal_eq_zero.mpr hx', inv_zero, to_nnreal_eq_zero.mpr (inv_nonpos.mpr hx')]
#align real.to_nnreal_inv Real.toNNReal_inv
-/

#print Real.toNNReal_div /-
theorem Real.toNNReal_div {x y : ℝ} (hx : 0 ≤ x) :
    Real.toNNReal (x / y) = Real.toNNReal x / Real.toNNReal y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← Real.toNNReal_inv, ← Real.toNNReal_mul hx]
#align real.to_nnreal_div Real.toNNReal_div
-/

#print Real.toNNReal_div' /-
theorem Real.toNNReal_div' {x y : ℝ} (hy : 0 ≤ y) :
    Real.toNNReal (x / y) = Real.toNNReal x / Real.toNNReal y := by
  rw [div_eq_inv_mul, div_eq_inv_mul, Real.toNNReal_mul (inv_nonneg.2 hy), Real.toNNReal_inv]
#align real.to_nnreal_div' Real.toNNReal_div'
-/

#print NNReal.inv_lt_one_iff /-
theorem inv_lt_one_iff {x : ℝ≥0} (hx : x ≠ 0) : x⁻¹ < 1 ↔ 1 < x := by
  rwa [← one_div, div_lt_iff hx, one_mul]
#align nnreal.inv_lt_one_iff NNReal.inv_lt_one_iff
-/

#print NNReal.zpow_pos /-
theorem zpow_pos {x : ℝ≥0} (hx : x ≠ 0) (n : ℤ) : 0 < x ^ n :=
  by
  cases n
  · simp [pow_pos hx.bot_lt _]
  · simp [pow_pos hx.bot_lt _]
#align nnreal.zpow_pos NNReal.zpow_pos
-/

#print NNReal.inv_lt_inv /-
theorem inv_lt_inv {x y : ℝ≥0} (hx : x ≠ 0) (h : x < y) : y⁻¹ < x⁻¹ :=
  inv_lt_inv_of_lt hx.bot_lt h
#align nnreal.inv_lt_inv NNReal.inv_lt_inv
-/

end Inv

#print NNReal.abs_eq /-
@[simp]
theorem abs_eq (x : ℝ≥0) : |(x : ℝ)| = x :=
  abs_of_nonneg x.property
#align nnreal.abs_eq NNReal.abs_eq
-/

section Csupr

open Set

variable {ι : Sort _} {f : ι → ℝ≥0}

#print NNReal.le_toNNReal_of_coe_le /-
theorem le_toNNReal_of_coe_le {x : ℝ≥0} {y : ℝ} (h : ↑x ≤ y) : x ≤ y.toNNReal :=
  (le_toNNReal_iff_coe_le <| x.2.trans h).2 h
#align nnreal.le_to_nnreal_of_coe_le NNReal.le_toNNReal_of_coe_le
-/

#print NNReal.sSup_of_not_bddAbove /-
theorem sSup_of_not_bddAbove {s : Set ℝ≥0} (hs : ¬BddAbove s) : SupSet.sSup s = 0 :=
  by
  rw [← bdd_above_coe] at hs
  rw [← NNReal.coe_inj, coe_Sup]
  exact Sup_of_not_bdd_above hs
#align nnreal.Sup_of_not_bdd_above NNReal.sSup_of_not_bddAbove
-/

#print NNReal.iSup_of_not_bddAbove /-
theorem iSup_of_not_bddAbove (hf : ¬BddAbove (range f)) : (⨆ i, f i) = 0 :=
  sSup_of_not_bddAbove hf
#align nnreal.supr_of_not_bdd_above NNReal.iSup_of_not_bddAbove
-/

#print NNReal.iInf_empty /-
theorem iInf_empty [IsEmpty ι] (f : ι → ℝ≥0) : (⨅ i, f i) = 0 := by rw [← NNReal.coe_inj, coe_infi];
  exact Real.iInf_of_isEmpty _
#align nnreal.infi_empty NNReal.iInf_empty
-/

#print NNReal.iInf_const_zero /-
@[simp]
theorem iInf_const_zero {α : Sort _} : (⨅ i : α, (0 : ℝ≥0)) = 0 := by
  rw [← NNReal.coe_inj, coe_infi]; exact Real.ciInf_const_zero
#align nnreal.infi_const_zero NNReal.iInf_const_zero
-/

#print NNReal.iInf_mul /-
theorem iInf_mul (f : ι → ℝ≥0) (a : ℝ≥0) : iInf f * a = ⨅ i, f i * a :=
  by
  rw [← NNReal.coe_inj, NNReal.coe_mul, coe_infi, coe_infi]
  exact Real.iInf_mul_of_nonneg (NNReal.coe_nonneg _) _
#align nnreal.infi_mul NNReal.iInf_mul
-/

#print NNReal.mul_iInf /-
theorem mul_iInf (f : ι → ℝ≥0) (a : ℝ≥0) : a * iInf f = ⨅ i, a * f i := by
  simpa only [mul_comm] using infi_mul f a
#align nnreal.mul_infi NNReal.mul_iInf
-/

#print NNReal.mul_iSup /-
theorem mul_iSup (f : ι → ℝ≥0) (a : ℝ≥0) : (a * ⨆ i, f i) = ⨆ i, a * f i :=
  by
  rw [← NNReal.coe_inj, NNReal.coe_mul, NNReal.coe_iSup, NNReal.coe_iSup]
  exact Real.mul_iSup_of_nonneg (NNReal.coe_nonneg _) _
#align nnreal.mul_supr NNReal.mul_iSup
-/

#print NNReal.iSup_mul /-
theorem iSup_mul (f : ι → ℝ≥0) (a : ℝ≥0) : (⨆ i, f i) * a = ⨆ i, f i * a := by
  rw [mul_comm, mul_supr]; simp_rw [mul_comm]
#align nnreal.supr_mul NNReal.iSup_mul
-/

#print NNReal.iSup_div /-
theorem iSup_div (f : ι → ℝ≥0) (a : ℝ≥0) : (⨆ i, f i) / a = ⨆ i, f i / a := by
  simp only [div_eq_mul_inv, supr_mul]
#align nnreal.supr_div NNReal.iSup_div
-/

variable [Nonempty ι]

#print NNReal.le_mul_iInf /-
theorem le_mul_iInf {a : ℝ≥0} {g : ℝ≥0} {h : ι → ℝ≥0} (H : ∀ j, a ≤ g * h j) : a ≤ g * iInf h := by
  rw [mul_infi]; exact le_ciInf H
#align nnreal.le_mul_infi NNReal.le_mul_iInf
-/

#print NNReal.mul_iSup_le /-
theorem mul_iSup_le {a : ℝ≥0} {g : ℝ≥0} {h : ι → ℝ≥0} (H : ∀ j, g * h j ≤ a) : g * iSup h ≤ a := by
  rw [mul_supr]; exact ciSup_le H
#align nnreal.mul_supr_le NNReal.mul_iSup_le
-/

#print NNReal.le_iInf_mul /-
theorem le_iInf_mul {a : ℝ≥0} {g : ι → ℝ≥0} {h : ℝ≥0} (H : ∀ i, a ≤ g i * h) : a ≤ iInf g * h := by
  rw [infi_mul]; exact le_ciInf H
#align nnreal.le_infi_mul NNReal.le_iInf_mul
-/

#print NNReal.iSup_mul_le /-
theorem iSup_mul_le {a : ℝ≥0} {g : ι → ℝ≥0} {h : ℝ≥0} (H : ∀ i, g i * h ≤ a) : iSup g * h ≤ a := by
  rw [supr_mul]; exact ciSup_le H
#align nnreal.supr_mul_le NNReal.iSup_mul_le
-/

#print NNReal.le_iInf_mul_iInf /-
theorem le_iInf_mul_iInf {a : ℝ≥0} {g h : ι → ℝ≥0} (H : ∀ i j, a ≤ g i * h j) :
    a ≤ iInf g * iInf h :=
  le_iInf_mul fun i => le_mul_iInf <| H i
#align nnreal.le_infi_mul_infi NNReal.le_iInf_mul_iInf
-/

#print NNReal.iSup_mul_iSup_le /-
theorem iSup_mul_iSup_le {a : ℝ≥0} {g h : ι → ℝ≥0} (H : ∀ i j, g i * h j ≤ a) :
    iSup g * iSup h ≤ a :=
  iSup_mul_le fun i => mul_iSup_le <| H _
#align nnreal.supr_mul_supr_le NNReal.iSup_mul_iSup_le
-/

end Csupr

end NNReal

namespace Set

namespace OrdConnected

variable {s : Set ℝ} {t : Set ℝ≥0}

#print Set.OrdConnected.preimage_coe_nnreal_real /-
theorem preimage_coe_nnreal_real (h : s.OrdConnected) : (coe ⁻¹' s : Set ℝ≥0).OrdConnected :=
  h.preimage_mono NNReal.coe_mono
#align set.ord_connected.preimage_coe_nnreal_real Set.OrdConnected.preimage_coe_nnreal_real
-/

#print Set.OrdConnected.image_coe_nnreal_real /-
theorem image_coe_nnreal_real (h : t.OrdConnected) : (coe '' t : Set ℝ).OrdConnected :=
  ⟨forall_mem_image.2 fun x hx =>
      forall_mem_image.2 fun y hy z hz => ⟨⟨z, x.2.trans hz.1⟩, h.out hx hy hz, rfl⟩⟩
#align set.ord_connected.image_coe_nnreal_real Set.OrdConnected.image_coe_nnreal_real
-/

#print Set.OrdConnected.image_real_toNNReal /-
theorem image_real_toNNReal (h : s.OrdConnected) : (Real.toNNReal '' s).OrdConnected :=
  by
  refine' ⟨ball_image_iff.2 fun x hx => ball_image_iff.2 fun y hy z hz => _⟩
  cases' le_total y 0 with hy₀ hy₀
  · rw [mem_Icc, Real.toNNReal_of_nonpos hy₀, nonpos_iff_eq_zero] at hz
    exact ⟨y, hy, (to_nnreal_of_nonpos hy₀).trans hz.2.symm⟩
  · lift y to ℝ≥0 using hy₀
    rw [to_nnreal_coe] at hz
    exact ⟨z, h.out hx hy ⟨to_nnreal_le_iff_le_coe.1 hz.1, hz.2⟩, to_nnreal_coe⟩
#align set.ord_connected.image_real_to_nnreal Set.OrdConnected.image_real_toNNReal
-/

#print Set.OrdConnected.preimage_real_toNNReal /-
theorem preimage_real_toNNReal (h : t.OrdConnected) : (Real.toNNReal ⁻¹' t).OrdConnected :=
  h.preimage_mono Real.toNNReal_mono
#align set.ord_connected.preimage_real_to_nnreal Set.OrdConnected.preimage_real_toNNReal
-/

end OrdConnected

end Set

namespace Real

#print Real.nnabs /-
/-- The absolute value on `ℝ` as a map to `ℝ≥0`. -/
@[pp_nodot]
def nnabs : ℝ →*₀ ℝ≥0 where
  toFun x := ⟨|x|, abs_nonneg x⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [abs_mul]
#align real.nnabs Real.nnabs
-/

#print Real.coe_nnabs /-
@[norm_cast, simp]
theorem coe_nnabs (x : ℝ) : (nnabs x : ℝ) = |x| :=
  rfl
#align real.coe_nnabs Real.coe_nnabs
-/

#print Real.nnabs_of_nonneg /-
@[simp]
theorem nnabs_of_nonneg {x : ℝ} (h : 0 ≤ x) : nnabs x = toNNReal x := by ext;
  simp [coe_to_nnreal x h, abs_of_nonneg h]
#align real.nnabs_of_nonneg Real.nnabs_of_nonneg
-/

#print Real.nnabs_coe /-
theorem nnabs_coe (x : ℝ≥0) : nnabs x = x := by simp
#align real.nnabs_coe Real.nnabs_coe
-/

#print Real.coe_toNNReal_le /-
theorem coe_toNNReal_le (x : ℝ) : (toNNReal x : ℝ) ≤ |x| :=
  max_le (le_abs_self _) (abs_nonneg _)
#align real.coe_to_nnreal_le Real.coe_toNNReal_le
-/

#print Real.toNNReal_abs /-
@[simp]
theorem toNNReal_abs (x : ℝ) : |x|.toNNReal = x.nnabs :=
  NNReal.coe_injective <| by simp
#align real.to_nnreal_abs Real.toNNReal_abs
-/

#print Real.cast_natAbs_eq_nnabs_cast /-
theorem cast_natAbs_eq_nnabs_cast (n : ℤ) : (n.natAbs : ℝ≥0) = nnabs n := by ext;
  rw [NNReal.coe_nat_cast, Int.cast_natAbs, Real.coe_nnabs]
#align real.cast_nat_abs_eq_nnabs_cast Real.cast_natAbs_eq_nnabs_cast
-/

end Real

namespace Tactic

open Positivity

private theorem nnreal_coe_pos {r : ℝ≥0} : 0 < r → 0 < (r : ℝ) :=
  NNReal.coe_pos.2

/-- Extension for the `positivity` tactic: cast from `ℝ≥0` to `ℝ`. -/
@[positivity]
unsafe def positivity_coe_nnreal_real : expr → tactic strictness
  | q(@coe _ _ $(inst) $(a)) => do
    unify inst q(@coeToLift _ _ <| @coeBase _ _ NNReal.Real.hasCoe)
    let strictness_a ← core a
    match strictness_a with
      | positive p => positive <$> mk_app `` nnreal_coe_pos [p]
      | _ => nonnegative <$> mk_app `` NNReal.coe_nonneg [a]
  | e =>
    pp e >>= fail ∘ format.bracket "The expression " " is not of the form `(r : ℝ)` for `r : ℝ≥0`"
#align tactic.positivity_coe_nnreal_real tactic.positivity_coe_nnreal_real

end Tactic

