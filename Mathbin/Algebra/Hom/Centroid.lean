/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christopher Hoskin
-/
import Algebra.GroupPower.Lemmas
import Algebra.Hom.GroupInstances

#align_import algebra.hom.centroid from "leanprover-community/mathlib"@"cc70d9141824ea8982d1562ce009952f2c3ece30"

/-!
# Centroid homomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Let `A` be a (non unital, non associative) algebra. The centroid of `A` is the set of linear maps
`T` on `A` such that `T` commutes with left and right multiplication, that is to say, for all `a`
and `b` in `A`,
$$
T(ab) = (Ta)b, T(ab) = a(Tb).
$$
In mathlib we call elements of the centroid "centroid homomorphisms" (`centroid_hom`) in keeping
with `add_monoid_hom` etc.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `centroid_hom`: Maps which preserve left and right multiplication.

## Typeclasses

* `centroid_hom_class`

## References

* [Jacobson, Structure of Rings][Jacobson1956]
* [McCrimmon, A taste of Jordan algebras][mccrimmon2004]

## Tags

centroid
-/


open Function

variable {F α : Type _}

#print CentroidHom /-
-- Making `centroid_hom` an old structure will allow the lemma `to_add_monoid_hom_eq_coe`
-- to be true by `rfl`. After upgrading to Lean 4, this should no longer be needed
-- because eta for structures should provide the same result.
/-- The type of centroid homomorphisms from `α` to `α`. -/
structure CentroidHom (α : Type _) [NonUnitalNonAssocSemiring α] extends α →+ α where
  map_hMul_left' (a b : α) : to_fun (a * b) = a * to_fun b
  map_hMul_right' (a b : α) : to_fun (a * b) = to_fun a * b
#align centroid_hom CentroidHom
-/

attribute [nolint doc_blame] CentroidHom.toAddMonoidHom

#print CentroidHomClass /-
/-- `centroid_hom_class F α` states that `F` is a type of centroid homomorphisms.

You should extend this class when you extend `centroid_hom`. -/
class CentroidHomClass (F : Type _) (α : outParam <| Type _) [NonUnitalNonAssocSemiring α] extends
    AddMonoidHomClass F α α where
  map_hMul_left (f : F) (a b : α) : f (a * b) = a * f b
  map_hMul_right (f : F) (a b : α) : f (a * b) = f a * b
#align centroid_hom_class CentroidHomClass
-/

export CentroidHomClass (map_hMul_left map_hMul_right)

instance [NonUnitalNonAssocSemiring α] [CentroidHomClass F α] : CoeTC F (CentroidHom α) :=
  ⟨fun f =>
    { (f : α →+ α) with
      toFun := f
      map_hMul_left' := map_hMul_left f
      map_hMul_right' := map_hMul_right f }⟩

/-! ### Centroid homomorphisms -/


namespace CentroidHom

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

instance : CentroidHomClass (CentroidHom α) α
    where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_zero f := f.map_zero'
  map_add f := f.map_add'
  map_hMul_left f := f.map_hMul_left'
  map_hMul_right f := f.map_hMul_right'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (CentroidHom α) fun _ => α → α :=
  DFunLike.hasCoeToFun

#print CentroidHom.toFun_eq_coe /-
@[simp]
theorem toFun_eq_coe {f : CentroidHom α} : f.toFun = (f : α → α) :=
  rfl
#align centroid_hom.to_fun_eq_coe CentroidHom.toFun_eq_coe
-/

#print CentroidHom.ext /-
@[ext]
theorem ext {f g : CentroidHom α} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
#align centroid_hom.ext CentroidHom.ext
-/

#print CentroidHom.coe_toAddMonoidHom /-
@[simp, norm_cast]
theorem coe_toAddMonoidHom (f : CentroidHom α) : ⇑(f : α →+ α) = f :=
  rfl
#align centroid_hom.coe_to_add_monoid_hom CentroidHom.coe_toAddMonoidHom
-/

#print CentroidHom.toAddMonoidHom_eq_coe /-
@[simp]
theorem toAddMonoidHom_eq_coe (f : CentroidHom α) : f.toAddMonoidHom = f :=
  rfl
#align centroid_hom.to_add_monoid_hom_eq_coe CentroidHom.toAddMonoidHom_eq_coe
-/

#print CentroidHom.coe_toAddMonoidHom_injective /-
theorem coe_toAddMonoidHom_injective : Injective (coe : CentroidHom α → α →+ α) := fun f g h =>
  ext fun a =>
    haveI := DFunLike.congr_fun h a
    this
#align centroid_hom.coe_to_add_monoid_hom_injective CentroidHom.coe_toAddMonoidHom_injective
-/

#print CentroidHom.toEnd /-
/-- Turn a centroid homomorphism into an additive monoid endomorphism. -/
def toEnd (f : CentroidHom α) : AddMonoid.End α :=
  (f : α →+ α)
#align centroid_hom.to_End CentroidHom.toEnd
-/

#print CentroidHom.toEnd_injective /-
theorem toEnd_injective : Injective (CentroidHom.toEnd : CentroidHom α → AddMonoid.End α) :=
  coe_toAddMonoidHom_injective
#align centroid_hom.to_End_injective CentroidHom.toEnd_injective
-/

#print CentroidHom.copy /-
/-- Copy of a `centroid_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : CentroidHom α) (f' : α → α) (h : f' = f) : CentroidHom α :=
  { f.toAddMonoidHom.copy f' <| h with
    toFun := f'
    map_hMul_left' := fun a b => by simp_rw [h, map_mul_left]
    map_hMul_right' := fun a b => by simp_rw [h, map_mul_right] }
#align centroid_hom.copy CentroidHom.copy
-/

#print CentroidHom.coe_copy /-
@[simp]
theorem coe_copy (f : CentroidHom α) (f' : α → α) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align centroid_hom.coe_copy CentroidHom.coe_copy
-/

#print CentroidHom.copy_eq /-
theorem copy_eq (f : CentroidHom α) (f' : α → α) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
#align centroid_hom.copy_eq CentroidHom.copy_eq
-/

variable (α)

#print CentroidHom.id /-
/-- `id` as a `centroid_hom`. -/
protected def id : CentroidHom α :=
  { AddMonoidHom.id α with
    map_hMul_left' := fun _ _ => rfl
    map_hMul_right' := fun _ _ => rfl }
#align centroid_hom.id CentroidHom.id
-/

instance : Inhabited (CentroidHom α) :=
  ⟨CentroidHom.id α⟩

#print CentroidHom.coe_id /-
@[simp, norm_cast]
theorem coe_id : ⇑(CentroidHom.id α) = id :=
  rfl
#align centroid_hom.coe_id CentroidHom.coe_id
-/

#print CentroidHom.toAddMonoidHom_id /-
@[simp, norm_cast]
theorem toAddMonoidHom_id : (CentroidHom.id α : α →+ α) = AddMonoidHom.id α :=
  rfl
#align centroid_hom.coe_to_add_monoid_hom_id CentroidHom.toAddMonoidHom_id
-/

variable {α}

#print CentroidHom.id_apply /-
@[simp]
theorem id_apply (a : α) : CentroidHom.id α a = a :=
  rfl
#align centroid_hom.id_apply CentroidHom.id_apply
-/

#print CentroidHom.comp /-
/-- Composition of `centroid_hom`s as a `centroid_hom`. -/
def comp (g f : CentroidHom α) : CentroidHom α :=
  {
    g.toAddMonoidHom.comp
      f.toAddMonoidHom with
    map_hMul_left' := fun a b => (congr_arg g <| f.map_hMul_left' _ _).trans <| g.map_hMul_left' _ _
    map_hMul_right' := fun a b =>
      (congr_arg g <| f.map_hMul_right' _ _).trans <| g.map_hMul_right' _ _ }
#align centroid_hom.comp CentroidHom.comp
-/

#print CentroidHom.coe_comp /-
@[simp, norm_cast]
theorem coe_comp (g f : CentroidHom α) : ⇑(g.comp f) = g ∘ f :=
  rfl
#align centroid_hom.coe_comp CentroidHom.coe_comp
-/

#print CentroidHom.comp_apply /-
@[simp]
theorem comp_apply (g f : CentroidHom α) (a : α) : g.comp f a = g (f a) :=
  rfl
#align centroid_hom.comp_apply CentroidHom.comp_apply
-/

#print CentroidHom.coe_comp_addMonoidHom /-
@[simp, norm_cast]
theorem coe_comp_addMonoidHom (g f : CentroidHom α) : (g.comp f : α →+ α) = (g : α →+ α).comp f :=
  rfl
#align centroid_hom.coe_comp_add_monoid_hom CentroidHom.coe_comp_addMonoidHom
-/

#print CentroidHom.comp_assoc /-
@[simp]
theorem comp_assoc (h g f : CentroidHom α) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
#align centroid_hom.comp_assoc CentroidHom.comp_assoc
-/

#print CentroidHom.comp_id /-
@[simp]
theorem comp_id (f : CentroidHom α) : f.comp (CentroidHom.id α) = f :=
  ext fun a => rfl
#align centroid_hom.comp_id CentroidHom.comp_id
-/

#print CentroidHom.id_comp /-
@[simp]
theorem id_comp (f : CentroidHom α) : (CentroidHom.id α).comp f = f :=
  ext fun a => rfl
#align centroid_hom.id_comp CentroidHom.id_comp
-/

#print CentroidHom.cancel_right /-
theorem cancel_right {g₁ g₂ f : CentroidHom α} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg _⟩
#align centroid_hom.cancel_right CentroidHom.cancel_right
-/

#print CentroidHom.cancel_left /-
theorem cancel_left {g f₁ f₂ : CentroidHom α} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align centroid_hom.cancel_left CentroidHom.cancel_left
-/

instance : Zero (CentroidHom α) :=
  ⟨{ (0 : α →+ α) with
      map_hMul_left' := fun a b => (MulZeroClass.mul_zero _).symm
      map_hMul_right' := fun a b => (MulZeroClass.zero_mul _).symm }⟩

instance : One (CentroidHom α) :=
  ⟨CentroidHom.id α⟩

instance : Add (CentroidHom α) :=
  ⟨fun f g =>
    {
      (f + g : α →+
          α) with
      map_hMul_left' := fun a b => by simp [map_mul_left, mul_add]
      map_hMul_right' := fun a b => by simp [map_mul_right, add_mul] }⟩

instance : Mul (CentroidHom α) :=
  ⟨comp⟩

instance hasNsmul : SMul ℕ (CentroidHom α) :=
  ⟨fun n f =>
    {
      (n • f :
        α →+
          α) with
      map_hMul_left' := fun a b => by change n • f (a * b) = a * n • f b;
        rw [map_mul_left f, ← mul_smul_comm]
      map_hMul_right' := fun a b => by change n • f (a * b) = n • f a * b;
        rw [map_mul_right f, ← smul_mul_assoc] }⟩
#align centroid_hom.has_nsmul CentroidHom.hasNsmul

#print CentroidHom.hasNPowNat /-
instance hasNPowNat : Pow (CentroidHom α) ℕ :=
  ⟨fun f n =>
    {
      (f.toEnd ^ n :
        AddMonoid.End
          α) with
      map_hMul_left' := fun a b => by
        induction' n with n ih
        · simp
        · rw [pow_succ]
          exact (congr_arg f.to_End ih).trans (f.map_mul_left' _ _)
      map_hMul_right' := fun a b => by
        induction' n with n ih
        · simp
        · rw [pow_succ]
          exact (congr_arg f.to_End ih).trans (f.map_mul_right' _ _) }⟩
#align centroid_hom.has_npow_nat CentroidHom.hasNPowNat
-/

#print CentroidHom.coe_zero /-
@[simp, norm_cast]
theorem coe_zero : ⇑(0 : CentroidHom α) = 0 :=
  rfl
#align centroid_hom.coe_zero CentroidHom.coe_zero
-/

#print CentroidHom.coe_one /-
@[simp, norm_cast]
theorem coe_one : ⇑(1 : CentroidHom α) = id :=
  rfl
#align centroid_hom.coe_one CentroidHom.coe_one
-/

#print CentroidHom.coe_add /-
@[simp, norm_cast]
theorem coe_add (f g : CentroidHom α) : ⇑(f + g) = f + g :=
  rfl
#align centroid_hom.coe_add CentroidHom.coe_add
-/

#print CentroidHom.coe_mul /-
@[simp, norm_cast]
theorem coe_mul (f g : CentroidHom α) : ⇑(f * g) = f ∘ g :=
  rfl
#align centroid_hom.coe_mul CentroidHom.coe_mul
-/

#print CentroidHom.coe_smul /-
-- Eligible for `dsimp`
@[simp, norm_cast, nolint simp_nf]
theorem coe_smul (f : CentroidHom α) (n : ℕ) : ⇑(n • f) = n • f :=
  rfl
#align centroid_hom.coe_nsmul CentroidHom.coe_smul
-/

#print CentroidHom.zero_apply /-
@[simp]
theorem zero_apply (a : α) : (0 : CentroidHom α) a = 0 :=
  rfl
#align centroid_hom.zero_apply CentroidHom.zero_apply
-/

#print CentroidHom.one_apply /-
@[simp]
theorem one_apply (a : α) : (1 : CentroidHom α) a = a :=
  rfl
#align centroid_hom.one_apply CentroidHom.one_apply
-/

#print CentroidHom.add_apply /-
@[simp]
theorem add_apply (f g : CentroidHom α) (a : α) : (f + g) a = f a + g a :=
  rfl
#align centroid_hom.add_apply CentroidHom.add_apply
-/

#print CentroidHom.mul_apply /-
@[simp]
theorem mul_apply (f g : CentroidHom α) (a : α) : (f * g) a = f (g a) :=
  rfl
#align centroid_hom.mul_apply CentroidHom.mul_apply
-/

#print CentroidHom.smul_apply /-
-- Eligible for `dsimp`
@[simp, nolint simp_nf]
theorem smul_apply (f : CentroidHom α) (n : ℕ) (a : α) : (n • f) a = n • f a :=
  rfl
#align centroid_hom.nsmul_apply CentroidHom.smul_apply
-/

#print CentroidHom.toEnd_zero /-
@[simp]
theorem toEnd_zero : (0 : CentroidHom α).toEnd = 0 :=
  rfl
#align centroid_hom.to_End_zero CentroidHom.toEnd_zero
-/

#print CentroidHom.toEnd_add /-
@[simp]
theorem toEnd_add (x y : CentroidHom α) : (x + y).toEnd = x.toEnd + y.toEnd :=
  rfl
#align centroid_hom.to_End_add CentroidHom.toEnd_add
-/

#print CentroidHom.toEnd_smul /-
theorem toEnd_smul (x : CentroidHom α) (n : ℕ) : (n • x).toEnd = n • x.toEnd :=
  rfl
#align centroid_hom.to_End_nsmul CentroidHom.toEnd_smul
-/

-- cf.`add_monoid_hom.add_comm_monoid`
instance : AddCommMonoid (CentroidHom α) :=
  coe_toAddMonoidHom_injective.AddCommMonoid _ toEnd_zero toEnd_add toEnd_smul

instance : NatCast (CentroidHom α) where natCast n := n • 1

#print CentroidHom.coe_nat_cast /-
@[simp, norm_cast]
theorem coe_nat_cast (n : ℕ) : ⇑(n : CentroidHom α) = n • id :=
  rfl
#align centroid_hom.coe_nat_cast CentroidHom.coe_nat_cast
-/

#print CentroidHom.nat_cast_apply /-
theorem nat_cast_apply (n : ℕ) (m : α) : (n : CentroidHom α) m = n • m :=
  rfl
#align centroid_hom.nat_cast_apply CentroidHom.nat_cast_apply
-/

#print CentroidHom.toEnd_one /-
@[simp]
theorem toEnd_one : (1 : CentroidHom α).toEnd = 1 :=
  rfl
#align centroid_hom.to_End_one CentroidHom.toEnd_one
-/

#print CentroidHom.toEnd_mul /-
@[simp]
theorem toEnd_mul (x y : CentroidHom α) : (x * y).toEnd = x.toEnd * y.toEnd :=
  rfl
#align centroid_hom.to_End_mul CentroidHom.toEnd_mul
-/

#print CentroidHom.toEnd_pow /-
@[simp]
theorem toEnd_pow (x : CentroidHom α) (n : ℕ) : (x ^ n).toEnd = x.toEnd ^ n := by ext; rfl
#align centroid_hom.to_End_pow CentroidHom.toEnd_pow
-/

#print CentroidHom.toEnd_nat_cast /-
@[simp, norm_cast]
theorem toEnd_nat_cast (n : ℕ) : (n : CentroidHom α).toEnd = ↑n :=
  rfl
#align centroid_hom.to_End_nat_cast CentroidHom.toEnd_nat_cast
-/

-- cf `add_monoid.End.semiring`
instance : Semiring (CentroidHom α) :=
  toEnd_injective.Semiring _ toEnd_zero toEnd_one toEnd_add toEnd_mul toEnd_smul toEnd_pow
    toEnd_nat_cast

#print CentroidHom.comp_mul_comm /-
theorem comp_mul_comm (T S : CentroidHom α) (a b : α) : (T ∘ S) (a * b) = (S ∘ T) (a * b) := by
  rw [comp_app, map_mul_right, map_mul_left, ← map_mul_right, ← map_mul_left]
#align centroid_hom.comp_mul_comm CentroidHom.comp_mul_comm
-/

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

/-- Negation of `centroid_hom`s as a `centroid_hom`. -/
instance : Neg (CentroidHom α) :=
  ⟨fun f =>
    { (-f : α →+ α) with
      map_hMul_left' := by simp [map_mul_left]
      map_hMul_right' := by simp [map_mul_right] }⟩

instance : Sub (CentroidHom α) :=
  ⟨fun f g =>
    {
      (f - g : α →+
          α) with
      map_hMul_left' := fun a b => by simp [map_mul_left, mul_sub]
      map_hMul_right' := fun a b => by simp [map_mul_right, sub_mul] }⟩

instance hasZsmul : SMul ℤ (CentroidHom α) :=
  ⟨fun n f =>
    {
      (n • f :
        α →+
          α) with
      map_hMul_left' := fun a b => by change n • f (a * b) = a * n • f b;
        rw [map_mul_left f, ← mul_smul_comm]
      map_hMul_right' := fun a b => by change n • f (a * b) = n • f a * b;
        rw [map_mul_right f, ← smul_mul_assoc] }⟩
#align centroid_hom.has_zsmul CentroidHom.hasZsmul

instance : IntCast (CentroidHom α) where intCast z := z • 1

#print CentroidHom.coe_int_cast /-
@[simp, norm_cast]
theorem coe_int_cast (z : ℤ) : ⇑(z : CentroidHom α) = z • id :=
  rfl
#align centroid_hom.coe_int_cast CentroidHom.coe_int_cast
-/

#print CentroidHom.int_cast_apply /-
theorem int_cast_apply (z : ℤ) (m : α) : (z : CentroidHom α) m = z • m :=
  rfl
#align centroid_hom.int_cast_apply CentroidHom.int_cast_apply
-/

#print CentroidHom.toEnd_neg /-
@[simp]
theorem toEnd_neg (x : CentroidHom α) : (-x).toEnd = -x.toEnd :=
  rfl
#align centroid_hom.to_End_neg CentroidHom.toEnd_neg
-/

#print CentroidHom.toEnd_sub /-
@[simp]
theorem toEnd_sub (x y : CentroidHom α) : (x - y).toEnd = x.toEnd - y.toEnd :=
  rfl
#align centroid_hom.to_End_sub CentroidHom.toEnd_sub
-/

/- warning: centroid_hom.to_End_zsmul clashes with centroid_hom.to_End_nsmul -> CentroidHom.toEnd_smul
Case conversion may be inaccurate. Consider using '#align centroid_hom.to_End_zsmul CentroidHom.toEnd_smulₓ'. -/
#print CentroidHom.toEnd_smul /-
theorem toEnd_smul (x : CentroidHom α) (n : ℤ) : (n • x).toEnd = n • x.toEnd :=
  rfl
#align centroid_hom.to_End_zsmul CentroidHom.toEnd_smul
-/

instance : AddCommGroup (CentroidHom α) :=
  toEnd_injective.AddCommGroup _ toEnd_zero toEnd_add toEnd_neg toEnd_sub toEnd_smul toEnd_smul

#print CentroidHom.coe_neg /-
@[simp, norm_cast]
theorem coe_neg (f : CentroidHom α) : ⇑(-f) = -f :=
  rfl
#align centroid_hom.coe_neg CentroidHom.coe_neg
-/

#print CentroidHom.coe_sub /-
@[simp, norm_cast]
theorem coe_sub (f g : CentroidHom α) : ⇑(f - g) = f - g :=
  rfl
#align centroid_hom.coe_sub CentroidHom.coe_sub
-/

#print CentroidHom.neg_apply /-
@[simp]
theorem neg_apply (f : CentroidHom α) (a : α) : (-f) a = -f a :=
  rfl
#align centroid_hom.neg_apply CentroidHom.neg_apply
-/

#print CentroidHom.sub_apply /-
@[simp]
theorem sub_apply (f g : CentroidHom α) (a : α) : (f - g) a = f a - g a :=
  rfl
#align centroid_hom.sub_apply CentroidHom.sub_apply
-/

#print CentroidHom.toEnd_int_cast /-
@[simp, norm_cast]
theorem toEnd_int_cast (z : ℤ) : (z : CentroidHom α).toEnd = ↑z :=
  rfl
#align centroid_hom.to_End_int_cast CentroidHom.toEnd_int_cast
-/

instance : Ring (CentroidHom α) :=
  toEnd_injective.Ring _ toEnd_zero toEnd_one toEnd_add toEnd_mul toEnd_neg toEnd_sub toEnd_smul
    toEnd_smul toEnd_pow toEnd_nat_cast toEnd_int_cast

end NonUnitalNonAssocRing

section NonUnitalRing

variable [NonUnitalRing α]

#print CentroidHom.commRing /-
-- See note [reducible non instances]
/-- A prime associative ring has commutative centroid. -/
@[reducible]
def commRing (h : ∀ a b : α, (∀ r : α, a * r * b = 0) → a = 0 ∨ b = 0) : CommRing (CentroidHom α) :=
  { CentroidHom.ring with
    mul_comm := fun f g => by
      ext
      refine' sub_eq_zero.1 ((or_self_iff _).1 <| h _ _ fun r => _)
      rw [mul_assoc, sub_mul, sub_eq_zero, ← map_mul_right, ← map_mul_right, coe_mul, coe_mul,
        comp_mul_comm] }
#align centroid_hom.comm_ring CentroidHom.commRing
-/

end NonUnitalRing

end CentroidHom

