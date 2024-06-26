/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import NumberTheory.Cyclotomic.PrimitiveRoots
import FieldTheory.Finite.Trace

#align_import number_theory.legendre_symbol.add_character from "leanprover-community/mathlib"@"fdc286cc6967a012f41b87f76dcd2797b53152af"

/-!
# Additive characters of finite rings and fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Let `R` be a finite commutative ring. An *additive character* of `R` with values
in another commutative ring `R'` is simply a morphism from the additive group
of `R` into the multiplicative monoid of `R'`.

The additive characters on `R` with values in `R'` form a commutative group.

We use the namespace `add_char`.

## Main definitions and results

We define `mul_shift ψ a`, where `ψ : add_char R R'` and `a : R`, to be the
character defined by `x ↦ ψ (a * x)`. An additive character `ψ` is *primitive*
if `mul_shift ψ a` is trivial only when `a = 0`.

We show that when `ψ` is primitive, then the map `a ↦ mul_shift ψ a` is injective
(`add_char.to_mul_shift_inj_of_is_primitive`) and that `ψ` is primitive when `R` is a field
and `ψ` is nontrivial (`add_char.is_nontrivial.is_primitive`).

We also show that there are primitive additive characters on `R` (with suitable
target `R'`) when `R` is a field or `R = zmod n` (`add_char.primitive_char_finite_field`
and `add_char.primitive_zmod_char`).

Finally, we show that the sum of all character values is zero when the character
is nontrivial (and the target is a domain); see `add_char.sum_eq_zero_of_is_nontrivial`.

## Tags

additive character
-/


universe u v

/-!
### Definitions related to and results on additive characters
-/


section AddCharDef

-- The domain of our additive characters
variable (R : Type u) [AddMonoid R]

-- The target
variable (R' : Type v) [CommMonoid R']

#print AddChar /-
/-- Define `add_char R R'` as `(multiplicative R) →* R'`.
The definition works for an additive monoid `R` and a monoid `R'`,
but we will restrict to the case that both are commutative rings below.
We assume right away that `R'` is commutative, so that `add_char R R'` carries
a structure of commutative monoid.
The trivial additive character (sending everything to `1`) is `(1 : add_char R R').` -/
def AddChar : Type max u v :=
  Multiplicative R →* R'
deriving CommMonoid, Inhabited
#align add_char AddChar
-/

end AddCharDef

namespace AddChar

section CoeToFun

variable {R : Type u} [AddMonoid R] {R' : Type v} [CommMonoid R']

#print AddChar.toMonoidHom /-
/-- Interpret an additive character as a monoid homomorphism. -/
def toMonoidHom : AddChar R R' → Multiplicative R →* R' :=
  id
#align add_char.to_monoid_hom AddChar.toMonoidHom
-/

open Multiplicative

/-- Define coercion to a function so that it includes the move from `R` to `multiplicative R`.
After we have proved the API lemmas below, we don't need to worry about writing `of_add a`
when we want to apply an additive character. -/
instance hasCoeToFun : CoeFun (AddChar R R') fun x => R → R'
    where coe ψ x := ψ.toMonoidHom (ofAdd x)
#align add_char.has_coe_to_fun AddChar.hasCoeToFun

#print AddChar.toMonoidHom_apply /-
theorem toMonoidHom_apply (ψ : AddChar R R') (a : R) : ψ a = ψ.toMonoidHom (ofAdd a) :=
  rfl
#align add_char.coe_to_fun_apply AddChar.toMonoidHom_apply
-/

instance monoidHomClass : MonoidHomClass (AddChar R R') (Multiplicative R) R' :=
  MonoidHom.instMonoidHomClass
#align add_char.monoid_hom_class AddChar.monoidHomClass

#print AddChar.map_zero_eq_one /-
/-- An additive character maps `0` to `1`. -/
@[simp]
theorem map_zero_eq_one (ψ : AddChar R R') : ψ 0 = 1 := by
  rw [coe_to_fun_apply, ofAdd_zero, map_one]
#align add_char.map_zero_one AddChar.map_zero_eq_one
-/

#print AddChar.map_add_eq_mul /-
/-- An additive character maps sums to products. -/
@[simp]
theorem map_add_eq_mul (ψ : AddChar R R') (x y : R) : ψ (x + y) = ψ x * ψ y := by
  rw [coe_to_fun_apply, coe_to_fun_apply _ x, coe_to_fun_apply _ y, ofAdd_add, map_mul]
#align add_char.map_add_mul AddChar.map_add_eq_mul
-/

#print AddChar.map_nsmul_eq_pow /-
/-- An additive character maps multiples by natural numbers to powers. -/
@[simp]
theorem map_nsmul_eq_pow (ψ : AddChar R R') (n : ℕ) (x : R) : ψ (n • x) = ψ x ^ n := by
  rw [coe_to_fun_apply, coe_to_fun_apply _ x, ofAdd_nsmul, map_pow]
#align add_char.map_nsmul_pow AddChar.map_nsmul_eq_pow
-/

end CoeToFun

section GroupStructure

open Multiplicative

variable {R : Type u} [AddCommGroup R] {R' : Type v} [CommMonoid R']

/- warning: add_char.has_inv clashes with add_char.comm_group -> AddChar.instCommGroup
Case conversion may be inaccurate. Consider using '#align add_char.has_inv AddChar.instCommGroupₓ'. -/
#print AddChar.instCommGroup /-
/-- An additive character on a commutative additive group has an inverse.

Note that this is a different inverse to the one provided by `monoid_hom.has_inv`,
as it acts on the domain instead of the codomain. -/
instance instCommGroup : Inv (AddChar R R') :=
  ⟨fun ψ => ψ.comp invMonoidHom⟩
#align add_char.has_inv AddChar.instCommGroup
-/

#print AddChar.inv_apply /-
theorem inv_apply (ψ : AddChar R R') (x : R) : ψ⁻¹ x = ψ (-x) :=
  rfl
#align add_char.inv_apply AddChar.inv_apply
-/

#print AddChar.map_zsmul_eq_zpow /-
/-- An additive character maps multiples by integers to powers. -/
@[simp]
theorem map_zsmul_eq_zpow {R' : Type v} [CommGroup R'] (ψ : AddChar R R') (n : ℤ) (x : R) :
    ψ (n • x) = ψ x ^ n := by rw [coe_to_fun_apply, coe_to_fun_apply _ x, ofAdd_zsmul, map_zpow]
#align add_char.map_zsmul_zpow AddChar.map_zsmul_eq_zpow
-/

#print AddChar.instCommGroup /-
/-- The additive characters on a commutative additive group form a commutative group. -/
instance instCommGroup : CommGroup (AddChar R R') :=
  { MonoidHom.commMonoid with
    inv := Inv.inv
    hMul_left_inv := fun ψ => by ext;
      rw [MonoidHom.mul_apply, MonoidHom.one_apply, inv_apply, ← map_add_mul, add_left_neg,
        map_zero_one] }
#align add_char.comm_group AddChar.instCommGroup
-/

end GroupStructure

section Additive

-- The domain and target of our additive characters. Now we restrict to rings on both sides.
variable {R : Type u} [CommRing R] {R' : Type v} [CommRing R']

#print AddChar.IsNontrivial /-
/-- An additive character is *nontrivial* if it takes a value `≠ 1`. -/
def IsNontrivial (ψ : AddChar R R') : Prop :=
  ∃ a : R, ψ a ≠ 1
#align add_char.is_nontrivial AddChar.IsNontrivial
-/

#print AddChar.isNontrivial_iff_ne_trivial /-
/-- An additive character is nontrivial iff it is not the trivial character. -/
theorem isNontrivial_iff_ne_trivial (ψ : AddChar R R') : IsNontrivial ψ ↔ ψ ≠ 1 :=
  by
  refine' not_forall.symm.trans (Iff.not _)
  rw [DFunLike.ext_iff]
  rfl
#align add_char.is_nontrivial_iff_ne_trivial AddChar.isNontrivial_iff_ne_trivial
-/

#print AddChar.mulShift /-
/-- Define the multiplicative shift of an additive character.
This satisfies `mul_shift ψ a x = ψ (a * x)`. -/
def mulShift (ψ : AddChar R R') (a : R) : AddChar R R' :=
  ψ.comp (AddMonoidHom.mulLeft a).toMultiplicative
#align add_char.mul_shift AddChar.mulShift
-/

#print AddChar.mulShift_apply /-
@[simp]
theorem mulShift_apply {ψ : AddChar R R'} {a : R} {x : R} : mulShift ψ a x = ψ (a * x) :=
  rfl
#align add_char.mul_shift_apply AddChar.mulShift_apply
-/

#print AddChar.inv_mulShift /-
/-- `ψ⁻¹ = mul_shift ψ (-1))`. -/
theorem inv_mulShift (ψ : AddChar R R') : ψ⁻¹ = mulShift ψ (-1) :=
  by
  ext
  rw [inv_apply, mul_shift_apply, neg_mul, one_mul]
#align add_char.inv_mul_shift AddChar.inv_mulShift
-/

#print AddChar.mulShift_spec' /-
/-- If `n` is a natural number, then `mul_shift ψ n x = (ψ x) ^ n`. -/
theorem mulShift_spec' (ψ : AddChar R R') (n : ℕ) (x : R) : mulShift ψ n x = ψ x ^ n := by
  rw [mul_shift_apply, ← nsmul_eq_mul, map_nsmul_pow]
#align add_char.mul_shift_spec' AddChar.mulShift_spec'
-/

#print AddChar.pow_mulShift /-
/-- If `n` is a natural number, then `ψ ^ n = mul_shift ψ n`. -/
theorem pow_mulShift (ψ : AddChar R R') (n : ℕ) : ψ ^ n = mulShift ψ n :=
  by
  ext x
  rw [show (ψ ^ n) x = ψ x ^ n from rfl, ← mul_shift_spec']
#align add_char.pow_mul_shift AddChar.pow_mulShift
-/

#print AddChar.mulShift_mul /-
/-- The product of `mul_shift ψ a` and `mul_shift ψ b` is `mul_shift ψ (a + b)`. -/
theorem mulShift_mul (ψ : AddChar R R') (a b : R) :
    mulShift ψ a * mulShift ψ b = mulShift ψ (a + b) :=
  by
  ext
  simp only [right_distrib, MonoidHom.mul_apply, mul_shift_apply, map_add_mul]
#align add_char.mul_shift_mul AddChar.mulShift_mul
-/

#print AddChar.mulShift_zero /-
/-- `mul_shift ψ 0` is the trivial character. -/
@[simp]
theorem mulShift_zero (ψ : AddChar R R') : mulShift ψ 0 = 1 :=
  by
  ext
  simp only [mul_shift_apply, MulZeroClass.zero_mul, map_zero_one, MonoidHom.one_apply]
#align add_char.mul_shift_zero AddChar.mulShift_zero
-/

#print AddChar.IsPrimitive /-
/-- An additive character is *primitive* iff all its multiplicative shifts by nonzero
elements are nontrivial. -/
def IsPrimitive (ψ : AddChar R R') : Prop :=
  ∀ a : R, a ≠ 0 → IsNontrivial (mulShift ψ a)
#align add_char.is_primitive AddChar.IsPrimitive
-/

#print AddChar.to_mulShift_inj_of_isPrimitive /-
/-- The map associating to `a : R` the multiplicative shift of `ψ` by `a`
is injective when `ψ` is primitive. -/
theorem to_mulShift_inj_of_isPrimitive {ψ : AddChar R R'} (hψ : IsPrimitive ψ) :
    Function.Injective ψ.mulShift := by
  intro a b h
  apply_fun fun x => x * mul_shift ψ (-b) at h
  simp only [mul_shift_mul, mul_shift_zero, add_right_neg] at h
  have h₂ := hψ (a + -b)
  rw [h, is_nontrivial_iff_ne_trivial, ← sub_eq_add_neg, sub_ne_zero] at h₂
  exact not_not.mp fun h => h₂ h rfl
#align add_char.to_mul_shift_inj_of_is_primitive AddChar.to_mulShift_inj_of_isPrimitive
-/

#print AddChar.IsPrimitive.of_ne_one /-
-- `add_comm_group.equiv_direct_sum_zmod_of_fintype`
-- gives the structure theorem for finite abelian groups.
-- This could be used to show that the map above is a bijection.
-- We leave this for a later occasion.
/-- When `R` is a field `F`, then a nontrivial additive character is primitive -/
theorem IsPrimitive.of_ne_one {F : Type u} [Field F] {ψ : AddChar F R'} (hψ : IsNontrivial ψ) :
    IsPrimitive ψ := by
  intro a ha
  cases' hψ with x h
  use a⁻¹ * x
  rwa [mul_shift_apply, mul_inv_cancel_left₀ ha]
#align add_char.is_nontrivial.is_primitive AddChar.IsPrimitive.of_ne_one
-/

#print AddChar.PrimitiveAddChar /-
-- Using `structure` gives a timeout, see
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/mysterious.20finsupp.20related.20timeout/near/365719262 and
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/mysterious.20finsupp.20related.20timeout
-- In Lean4, `set_option genInjectivity false in` may solve this issue.
-- can't prove that they always exist
/-- Definition for a primitive additive character on a finite ring `R` into a cyclotomic extension
of a field `R'`. It records which cyclotomic extension it is, the character, and the
fact that the character is primitive. -/
@[nolint has_nonempty_instance]
def PrimitiveAddChar (R : Type u) [CommRing R] (R' : Type v) [Field R'] :=
  Σ n : ℕ+, Σ' char : AddChar R (CyclotomicField n R'), IsPrimitive Char
#align add_char.primitive_add_char AddChar.PrimitiveAddChar
-/

#print AddChar.PrimitiveAddChar.n /-
/-- The first projection from `primitive_add_char`, giving the cyclotomic field. -/
noncomputable def PrimitiveAddChar.n {R : Type u} [CommRing R] {R' : Type v} [Field R'] :
    PrimitiveAddChar R R' → ℕ+ := fun χ => χ.1
#align add_char.primitive_add_char.n AddChar.PrimitiveAddChar.n
-/

#print AddChar.PrimitiveAddChar.char /-
/-- The second projection from `primitive_add_char`, giving the character. -/
noncomputable def PrimitiveAddChar.char {R : Type u} [CommRing R] {R' : Type v} [Field R'] :
    ∀ χ : PrimitiveAddChar R R', AddChar R (CyclotomicField χ.n R') := fun χ => χ.2.1
#align add_char.primitive_add_char.char AddChar.PrimitiveAddChar.char
-/

#print AddChar.PrimitiveAddChar.prim /-
/-- The third projection from `primitive_add_char`, showing that `χ.2` is primitive. -/
theorem PrimitiveAddChar.prim {R : Type u} [CommRing R] {R' : Type v} [Field R'] :
    ∀ χ : PrimitiveAddChar R R', IsPrimitive χ.Char := fun χ => χ.2.2
#align add_char.primitive_add_char.prim AddChar.PrimitiveAddChar.prim
-/

/-!
### Additive characters on `zmod n`
-/


variable {C : Type v} [CommRing C]

section ZmodCharDef

open Multiplicative

#print AddChar.zmodChar /-
-- so we can write simply `to_add`, which we need here again
/-- We can define an additive character on `zmod n` when we have an `n`th root of unity `ζ : C`. -/
def zmodChar (n : ℕ+) {ζ : C} (hζ : ζ ^ ↑n = 1) : AddChar (ZMod n) C
    where
  toFun := fun a : Multiplicative (ZMod n) => ζ ^ a.toAdd.val
  map_one' := by simp only [toAdd_one, ZMod.val_zero, pow_zero]
  map_mul' x y := by
    rw [toAdd_mul, ← pow_add, ZMod.val_add (to_add x) (to_add y), ← pow_eq_pow_mod _ hζ]
#align add_char.zmod_char AddChar.zmodChar
-/

#print AddChar.zmodChar_apply /-
/-- The additive character on `zmod n` defined using `ζ` sends `a` to `ζ^a`. -/
theorem zmodChar_apply {n : ℕ+} {ζ : C} (hζ : ζ ^ ↑n = 1) (a : ZMod n) :
    zmodChar n hζ a = ζ ^ a.val :=
  rfl
#align add_char.zmod_char_apply AddChar.zmodChar_apply
-/

#print AddChar.zmodChar_apply' /-
theorem zmodChar_apply' {n : ℕ+} {ζ : C} (hζ : ζ ^ ↑n = 1) (a : ℕ) : zmodChar n hζ a = ζ ^ a := by
  rw [pow_eq_pow_mod a hζ, zmod_char_apply, ZMod.val_natCast a]
#align add_char.zmod_char_apply' AddChar.zmodChar_apply'
-/

end ZmodCharDef

#print AddChar.zmod_char_ne_one_iff /-
/-- An additive character on `zmod n` is nontrivial iff it takes a value `≠ 1` on `1`. -/
theorem zmod_char_ne_one_iff (n : ℕ+) (ψ : AddChar (ZMod n) C) : IsNontrivial ψ ↔ ψ 1 ≠ 1 :=
  by
  refine' ⟨_, fun h => ⟨1, h⟩⟩
  contrapose!
  rintro h₁ ⟨a, ha⟩
  have ha₁ : a = a.val • 1 := by rw [nsmul_eq_mul, mul_one]; exact (ZMod.natCast_zmod_val a).symm
  rw [ha₁, map_nsmul_pow, h₁, one_pow] at ha
  exact ha rfl
#align add_char.zmod_char_is_nontrivial_iff AddChar.zmod_char_ne_one_iff
-/

#print AddChar.IsPrimitive.zmod_char_eq_one_iff /-
/-- A primitive additive character on `zmod n` takes the value `1` only at `0`. -/
theorem IsPrimitive.zmod_char_eq_one_iff (n : ℕ+) {ψ : AddChar (ZMod n) C} (hψ : IsPrimitive ψ)
    (a : ZMod n) : ψ a = 1 ↔ a = 0 :=
  by
  refine' ⟨fun h => not_imp_comm.mp (hψ a) _, fun ha => by rw [ha, map_zero_one]⟩
  rw [zmod_char_is_nontrivial_iff n (mul_shift ψ a), mul_shift_apply, mul_one, h, Classical.not_not]
#align add_char.is_primitive.zmod_char_eq_one_iff AddChar.IsPrimitive.zmod_char_eq_one_iff
-/

#print AddChar.zmod_char_primitive_of_eq_one_only_at_zero /-
/-- The converse: if the additive character takes the value `1` only at `0`,
then it is primitive. -/
theorem zmod_char_primitive_of_eq_one_only_at_zero (n : ℕ) (ψ : AddChar (ZMod n) C)
    (hψ : ∀ a, ψ a = 1 → a = 0) : IsPrimitive ψ :=
  by
  refine' fun a ha => (is_nontrivial_iff_ne_trivial _).mpr fun hf => _
  have h : mul_shift ψ a 1 = (1 : AddChar (ZMod n) C) (1 : ZMod n) :=
    congr_fun (congr_arg coeFn hf) 1
  rw [mul_shift_apply, mul_one, MonoidHom.one_apply] at h
  exact ha (hψ a h)
#align add_char.zmod_char_primitive_of_eq_one_only_at_zero AddChar.zmod_char_primitive_of_eq_one_only_at_zero
-/

#print AddChar.zmodChar_primitive_of_primitive_root /-
/-- The additive character on `zmod n` associated to a primitive `n`th root of unity
is primitive -/
theorem zmodChar_primitive_of_primitive_root (n : ℕ+) {ζ : C} (h : IsPrimitiveRoot ζ n) :
    IsPrimitive (zmodChar n ((IsPrimitiveRoot.iff_def ζ n).mp h).left) :=
  by
  apply zmod_char_primitive_of_eq_one_only_at_zero
  intro a ha
  rw [zmod_char_apply, ← pow_zero ζ] at ha
  exact (ZMod.val_eq_zero a).mp (IsPrimitiveRoot.pow_inj h (ZMod.val_lt a) n.pos ha)
#align add_char.zmod_char_primitive_of_primitive_root AddChar.zmodChar_primitive_of_primitive_root
-/

#print AddChar.primitiveZModChar /-
/-- There is a primitive additive character on `zmod n` if the characteristic of the target
does not divide `n` -/
noncomputable def primitiveZModChar (n : ℕ+) (F' : Type v) [Field F'] (h : (n : F') ≠ 0) :
    PrimitiveAddChar (ZMod n) F' :=
  haveI : NeZero ((n : ℕ) : F') := ⟨h⟩
  ⟨n, zmod_char n (IsCyclotomicExtension.zeta_pow n F' _),
    zmod_char_primitive_of_primitive_root n (IsCyclotomicExtension.zeta_spec n F' _)⟩
#align add_char.primitive_zmod_char AddChar.primitiveZModChar
-/

/-!
### Existence of a primitive additive character on a finite field
-/


#print AddChar.FiniteField.primitiveChar /-
/-- There is a primitive additive character on the finite field `F` if the characteristic
of the target is different from that of `F`.
We obtain it as the composition of the trace from `F` to `zmod p` with a primitive
additive character on `zmod p`, where `p` is the characteristic of `F`. -/
noncomputable def AddChar.FiniteField.primitiveChar (F F' : Type _) [Field F] [Fintype F] [Field F']
    (h : ringChar F' ≠ ringChar F) : PrimitiveAddChar F F' :=
  by
  let p := ringChar F
  haveI hp : Fact p.prime := ⟨CharP.char_is_prime F _⟩
  let pp := p.to_pnat hp.1.Pos
  have hp₂ : ¬ringChar F' ∣ p :=
    by
    cases' CharP.char_is_prime_or_zero F' (ringChar F') with hq hq
    · exact mt (Nat.Prime.dvd_iff_eq hp.1 (Nat.Prime.ne_one hq)).mp h.symm
    · rw [hq]
      exact fun hf => Nat.Prime.ne_zero hp.1 (zero_dvd_iff.mp hf)
  let ψ := primitive_zmod_char pp F' (ne_zero_iff.mp (NeZero.of_not_dvd F' hp₂))
  letI : Algebra (ZMod p) F := ZMod.algebra _ _
  let ψ' := ψ.char.comp (Algebra.trace (ZMod p) F).toAddMonoidHom.toMultiplicative
  have hψ' : is_nontrivial ψ' :=
    by
    obtain ⟨a, ha⟩ := FiniteField.trace_to_zmod_nondegenerate F one_ne_zero
    rw [one_mul] at ha
    exact ⟨a, fun hf => ha <| (ψ.prim.zmod_char_eq_one_iff pp <| Algebra.trace (ZMod p) F a).mp hf⟩
  exact ⟨ψ.n, ψ', hψ'.is_primitive⟩
#align add_char.primitive_char_finite_field AddChar.FiniteField.primitiveChar
-/

/-!
### The sum of all character values
-/


open scoped BigOperators

variable [Fintype R]

#print AddChar.sum_eq_zero_of_ne_one /-
/-- The sum over the values of a nontrivial additive character vanishes if the target ring
is a domain. -/
theorem sum_eq_zero_of_ne_one [IsDomain R'] {ψ : AddChar R R'} (hψ : IsNontrivial ψ) :
    ∑ a, ψ a = 0 := by
  rcases hψ with ⟨b, hb⟩
  have h₁ : ∑ a : R, ψ (b + a) = ∑ a : R, ψ a :=
    Fintype.sum_bijective _ (AddGroup.addLeft_bijective b) _ _ fun x => rfl
  simp_rw [map_add_mul] at h₁
  have h₂ : ∑ a : R, ψ a = finset.univ.sum ⇑ψ := rfl
  rw [← Finset.mul_sum, h₂] at h₁
  exact eq_zero_of_mul_eq_self_left hb h₁
#align add_char.sum_eq_zero_of_is_nontrivial AddChar.sum_eq_zero_of_ne_one
-/

#print AddChar.sum_eq_card_of_eq_one /-
/-- The sum over the values of the trivial additive character is the cardinality of the source. -/
theorem sum_eq_card_of_eq_one {ψ : AddChar R R'} (hψ : ¬IsNontrivial ψ) :
    ∑ a, ψ a = Fintype.card R := by
  simp only [is_nontrivial] at hψ
  push_neg at hψ
  simp only [hψ, Finset.sum_const, Nat.smul_one_eq_cast]
  rfl
#align add_char.sum_eq_card_of_is_trivial AddChar.sum_eq_card_of_eq_one
-/

#print AddChar.sum_mulShift /-
/-- The sum over the values of `mul_shift ψ b` for `ψ` primitive is zero when `b ≠ 0`
and `#R` otherwise. -/
theorem sum_mulShift [DecidableEq R] [IsDomain R'] {ψ : AddChar R R'} (b : R) (hψ : IsPrimitive ψ) :
    ∑ x : R, ψ (x * b) = if b = 0 then Fintype.card R else 0 :=
  by
  split_ifs with h
  · -- case `b = 0`
    simp only [h, MulZeroClass.mul_zero, map_zero_one, Finset.sum_const, Nat.smul_one_eq_cast]
    rfl
  · -- case `b ≠ 0`
    simp_rw [mul_comm]
    exact sum_eq_zero_of_is_nontrivial (hψ b h)
#align add_char.sum_mul_shift AddChar.sum_mulShift
-/

end Additive

end AddChar

