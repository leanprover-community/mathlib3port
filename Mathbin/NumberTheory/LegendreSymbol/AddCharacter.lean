/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathbin.Tactic.Basic
import Mathbin.FieldTheory.Finite.GaloisField
import Mathbin.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathbin.FieldTheory.Finite.Trace

/-!
# Additive characters of finite rings and fields

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


/-!
### Definitions related to and results on additive characters
-/


section AddCharDef

universe u v

-- The domain of our additive characters
variable (R : Type u) [AddMonoidₓ R]

-- The target
variable (R' : Type v) [CommMonoidₓ R']

/-- Define `add_char R R'` as `(multiplicative R) →* R'`.
The definition works for an additive monoid `R` and a monoid `R'`,
but we will restrict to the case that both are commutative rings below.
We assume right away that `R'` is commutative, so that `add_char R R'` carries
a structure of commutative monoid.
The trivial additive character (sending everything to `1`) is `(1 : add_char R R').` -/
def AddChar : Type max u v :=
  Multiplicative R →* R' deriving CommMonoidₓ, Inhabited

instance AddChar.hasCoeToFun : CoeFun (AddChar R R') fun x => Multiplicative R → R' :=
  MonoidHom.hasCoeToFun

instance AddChar.monoidHomClass : MonoidHomClass (AddChar R R') (Multiplicative R) R' :=
  MonoidHom.monoidHomClass

end AddCharDef

section GroupStructure

universe u v

namespace AddChar

open Multiplicative

variable {R : Type u} [AddCommGroupₓ R] {R' : Type v} [CommMonoidₓ R']

/-- An additive character on a commutative additive group has an inverse.

Note that this is a different inverse to the one provided by `monoid_hom.has_inv`,
as it acts on the domain instead of the codomain. -/
instance hasInv : Inv (AddChar R R') :=
  ⟨fun ψ => ψ.comp invMonoidHom⟩

theorem inv_apply (ψ : AddChar R R') (x : Multiplicative R) : ψ⁻¹ x = ψ (ofAdd (-toAdd x)) :=
  rfl

theorem inv_apply' (ψ : AddChar R R') (x : R) : ψ⁻¹ (ofAdd x) = ψ (ofAdd (-x)) :=
  rfl

/-- The additive characters on a commutative additive group form a commutative group. -/
instance commGroup : CommGroupₓ (AddChar R R') :=
  { MonoidHom.commMonoid with inv := Inv.inv,
    mul_left_inv := fun ψ => by
      ext
      rw [MonoidHom.mul_apply, MonoidHom.one_apply, inv_apply, ← map_mul, of_add_neg, of_add_to_add, mul_left_invₓ,
        map_one] }

end AddChar

end GroupStructure

section Additive

namespace AddChar

open Multiplicative

universe u v

-- The domain of our additive characters
variable {R : Type u} [CommRingₓ R]

-- The target
variable {R' : Type v} [CommRingₓ R']

/-- An additive character is *nontrivial* if it takes a value `≠ 1`. -/
def IsNontrivial (ψ : AddChar R R') : Prop :=
  ∃ a : R, ψ (ofAdd a) ≠ 1

/-- An additive character is nontrivial iff it is not the trivial character. -/
theorem is_nontrivial_iff_ne_trivial (ψ : AddChar R R') : IsNontrivial ψ ↔ ψ ≠ 1 := by
  refine' not_forall.symm.trans (Iff.not _)
  rw [FunLike.ext_iff]
  rfl

/-- Define the multiplicative shift of an additive character.
This satisfies `mul_shift ψ a x = ψ (a * x)`. -/
def mulShift (ψ : AddChar R R') (a : R) : AddChar R R' :=
  ψ.comp (AddMonoidHom.mulLeft a).toMultiplicative

@[simp]
theorem mul_shift_apply {ψ : AddChar R R'} {a : R} {x : Multiplicative R} : mulShift ψ a x = ψ (ofAdd (a * toAdd x)) :=
  rfl

/-- `ψ⁻¹ = mul_shift ψ (-1))`. -/
theorem inv_mul_shift (ψ : AddChar R R') : ψ⁻¹ = mulShift ψ (-1) := by
  ext
  rw [inv_apply, mul_shift_apply, neg_mul, one_mulₓ]

/-- If `n` is a natural number, then `mul_shift ψ n x = (ψ x) ^ n`. -/
theorem mul_shift_spec' (ψ : AddChar R R') (n : ℕ) (x : Multiplicative R) : mulShift ψ n x = ψ x ^ n := by
  rw [mul_shift_apply, ← nsmul_eq_mul, of_add_nsmul, map_pow, of_add_to_add]

/-- If `n` is a natural number, then `ψ ^ n = mul_shift ψ n`. -/
theorem pow_mul_shift (ψ : AddChar R R') (n : ℕ) : ψ ^ n = mulShift ψ n := by
  ext x
  rw [show (ψ ^ n) x = ψ x ^ n from rfl, ← mul_shift_spec']

/-- The product of `mul_shift ψ a` and `mul_shift ψ b` is `mul_shift ψ (a + b)`. -/
theorem mul_shift_mul (ψ : AddChar R R') (a b : R) : mulShift ψ a * mulShift ψ b = mulShift ψ (a + b) := by
  ext
  simp only [← MonoidHom.mul_apply, ← mul_shift_apply, ← add_mulₓ, ← of_add_add, ← ψ.map_mul]

/-- `mul_shift ψ 0` is the trivial character. -/
@[simp]
theorem mul_shift_zero (ψ : AddChar R R') : mulShift ψ 0 = 1 := by
  ext
  simp only [← mul_shift_apply, ← zero_mul, ← of_add_zero, ← map_one, ← MonoidHom.one_apply]

/-- An additive character is *primitive* iff all its multiplicative shifts by nonzero
elements are nontrivial. -/
def IsPrimitive (ψ : AddChar R R') : Prop :=
  ∀ a : R, a ≠ 0 → IsNontrivial (mulShift ψ a)

/-- The map associating to `a : R` the multiplicative shift of `ψ` by `a`
is injective when `ψ` is primitive. -/
theorem to_mul_shift_inj_of_is_primitive {ψ : AddChar R R'} (hψ : IsPrimitive ψ) : Function.Injective ψ.mulShift := by
  intro a b h
  apply_fun fun x => x * mul_shift ψ (-b)  at h
  simp only [← mul_shift_mul, ← mul_shift_zero, ← add_right_negₓ] at h
  have h₂ := hψ (a + -b)
  rw [h, is_nontrivial_iff_ne_trivial, ← sub_eq_add_neg, sub_ne_zero] at h₂
  exact not_not.mp fun h => h₂ h rfl

/-- When `R` is a field `F`, then a nontrivial additive character is primitive -/
-- `add_comm_group.equiv_direct_sum_zmod_of_fintype`
-- gives the structure theorem for finite abelian groups.
-- This could be used to show that the map above is a bijection.
-- We leave this for a later occasion.
theorem IsNontrivial.is_primitive {F : Type u} [Field F] (ψ : AddChar F R') (hψ : IsNontrivial ψ) : IsPrimitive ψ := by
  intro a ha
  cases' hψ with x h
  use a⁻¹ * x
  rwa [mul_shift_apply, to_add_of_add, mul_inv_cancel_left₀ ha]

/-- Structure for a primitive additive character on a finite ring `R` into a cyclotomic extension
of a field `R'`. It records which cyclotomic extension it is, the character, and the
fact that the character is primitive. -/
-- can't prove that they always exist
@[nolint has_nonempty_instance]
structure PrimitiveAddChar (R : Type u) [CommRingₓ R] [Fintype R] (R' : Type v) [Field R'] where
  n : Pnat
  Char : AddChar R (CyclotomicField n R')
  prim : IsPrimitive Charₓ

/-!
### Additive characters on `zmod n`
-/


variable {C : Type v} [CommRingₓ C]

/-- We can define an additive character on `zmod n` when we have an `n`th root of unity `ζ : C`. -/
def zmodChar (n : ℕ) [Fact (0 < n)] {ζ : C} (hζ : ζ ^ n = 1) : AddChar (Zmod n) C where
  toFun := fun a : Multiplicative (Zmod n) => ζ ^ a.toAdd.val
  map_one' := by
    simp only [← to_add_one, ← Zmod.val_zero, ← pow_zeroₓ]
  map_mul' := fun x y => by
    rw [to_add_mul, ← pow_addₓ, Zmod.val_add (to_add x) (to_add y), ← pow_eq_pow_mod _ hζ]

/-- An additive character on `zmod n` is nontrivial iff it takes a value `≠ 1` on `1`. -/
theorem zmod_char_is_nontrivial_iff (n : ℕ) [Fact (0 < n)] (ψ : AddChar (Zmod n) C) :
    IsNontrivial ψ ↔ ψ (ofAdd 1) ≠ 1 := by
  refine' ⟨_, fun h => ⟨1, h⟩⟩
  contrapose!
  rintro h₁ ⟨a, ha⟩
  have ha₁ : a = a.val • 1 := by
    rw [nsmul_eq_mul, mul_oneₓ]
    exact (Zmod.nat_cast_zmod_val a).symm
  have ha₂ : of_add a = of_add 1 ^ a.val := by
    rw [← of_add_nsmul _ a.val, ← ha₁]
  rw [ha₂, map_pow, h₁, one_pow] at ha
  exact ha rfl

/-- A primitive additive character on `zmod n` takes the value `1` only at `0`. -/
theorem IsPrimitive.zmod_char_eq_one_iff (n : ℕ) [Fact (0 < n)] {ψ : AddChar (Zmod n) C} (hψ : IsPrimitive ψ)
    (a : Zmod n) : ψ (ofAdd a) = 1 ↔ a = 0 := by
  refine'
    ⟨fun h => not_imp_comm.mp (hψ a) _, fun ha => by
      rw [ha, of_add_zero, map_one]⟩
  rw [zmod_char_is_nontrivial_iff n (mul_shift ψ a)]
  simpa only [← mul_shift, ← MonoidHom.coe_comp, ← Function.comp_app, ← AddMonoidHom.coe_mul_left, ←
    AddMonoidHom.to_multiplicative_apply_apply, ← to_add_of_add, ← mul_oneₓ, ← not_not]

/-- The converse: if the additive character takes the value `1` only at `0`,
then it is primitive. -/
theorem zmod_char_primitive_of_eq_one_only_at_zero (n : ℕ) (ψ : AddChar (Zmod n) C)
    (hψ : ∀ a, ψ (ofAdd a) = 1 → a = 0) : IsPrimitive ψ := by
  refine' fun a ha => (is_nontrivial_iff_ne_trivial _).mpr fun hf => _
  have h : mul_shift ψ a (of_add 1) = (1 : AddChar (Zmod n) C) (of_add (1 : Zmod n)) := congr_fun (congr_arg coeFn hf) 1
  simp only [← mul_shift, ← MonoidHom.coe_comp, ← Function.comp_app, ← AddMonoidHom.to_multiplicative_apply_apply, ←
    to_add_of_add, ← AddMonoidHom.coe_mul_left, ← mul_oneₓ, ← MonoidHom.one_apply] at h
  exact ha (hψ a h)

/-- The additive character on `zmod n` associated to a primitive `n`th root of unity
is primitive -/
theorem zmod_char_primitive_of_primitive_root (n : ℕ) [hn : Fact (0 < n)] {ζ : C} (h : IsPrimitiveRoot ζ n) :
    IsPrimitive (zmodChar n ((IsPrimitiveRoot.iff_def ζ n).mp h).left) := by
  apply zmod_char_primitive_of_eq_one_only_at_zero
  intro a ha
  simp only [← zmod_char, ← MonoidHom.coe_mk, ← to_add_of_add, pow_zeroₓ ζ] at ha
  exact (Zmod.val_eq_zero a).mp (IsPrimitiveRoot.pow_inj h (Zmod.val_lt a) hn.1 ha)

/-- There is a primitive additive character on `zmod n` if the characteristic of the target
does not divide `n` -/
noncomputable def primitiveZmodChar (n : ℕ) [hn : Fact (0 < n)] (F' : Type v) [Field F'] (h : (n : F') ≠ 0) :
    PrimitiveAddChar (Zmod n) F' := by
  let nn := n.to_pnat hn.1
  haveI : NeZero ((nn : ℕ) : F') := ⟨h⟩
  haveI : NeZero ((nn : ℕ) : CyclotomicField nn F') := NeZero.of_no_zero_smul_divisors F' _ n
  exact
    { n := nn, Char := zmod_char n (IsCyclotomicExtension.zeta_pow nn F' _),
      prim := zmod_char_primitive_of_primitive_root n (IsCyclotomicExtension.zeta_spec nn F' _) }

/-!
### Existence of a primitive additive character on a finite field
-/


/-- There is a primitive additive character on the finite field `F` if the characteristic
of the target is different from that of `F`.
We obtain it as the composition of the trace from `F` to `zmod p` with a primitive
additive character on `zmod p`, where `p` is the characteristic of `F`. -/
noncomputable def primitiveCharFiniteField (F F' : Type) [Field F] [Fintype F] [Field F']
    (h : ringChar F' ≠ ringChar F) : PrimitiveAddChar F F' := by
  let p := ringChar F
  haveI hp : Fact p.prime := ⟨CharP.char_is_prime F _⟩
  haveI hp₁ : Fact (0 < p) := ⟨hp.1.Pos⟩
  have hp₂ : ¬ringChar F' ∣ p := by
    cases' CharP.char_is_prime_or_zero F' (ringChar F') with hq hq
    · exact mt (Nat.Prime.dvd_iff_eq hp.1 (Nat.Prime.ne_one hq)).mp h.symm
      
    · rw [hq]
      exact fun hf => Nat.Prime.ne_zero hp.1 (zero_dvd_iff.mp hf)
      
  let ψ := primitive_zmod_char p F' (ne_zero_iff.mp (NeZero.of_not_dvd F' hp₂))
  let ψ' := ψ.char.comp (AddMonoidHom.toMultiplicative (Algebra.trace (Zmod p) F).toAddMonoidHom)
  have hψ' : is_nontrivial ψ' := by
    obtain ⟨a, ha⟩ := FiniteField.trace_to_zmod_nondegenerate F one_ne_zero
    rw [one_mulₓ] at ha
    exact ⟨a, fun hf => ha <| (ψ.prim.zmod_char_eq_one_iff p <| Algebra.trace (Zmod p) F a).mp hf⟩
  exact { n := ψ.n, Char := ψ', prim := hψ'.is_primitive ψ' }

/-!
### The sum of all character values
-/


open BigOperators

variable [Fintype R]

/-- The sum over the values of a nontrivial additive character vanishes if the target ring
is a domain. -/
theorem sum_eq_zero_of_is_nontrivial' [IsDomain R'] {ψ : AddChar R R'} (hψ : IsNontrivial ψ) : (∑ a, ψ a) = 0 := by
  rcases hψ with ⟨b, hb⟩
  have h₁ : (∑ a : R, ψ (of_add (b + a))) = ∑ a : R, ψ a :=
    Fintype.sum_bijective _ (AddGroupₓ.add_left_bijective b) _ _ fun x => rfl
  simp_rw [of_add_add, ψ.map_mul] at h₁
  have h₂ : (∑ a : R, ψ (of_add a)) = finset.univ.sum ⇑ψ := rfl
  rw [← Finset.mul_sum, h₂] at h₁
  exact eq_zero_of_mul_eq_self_left hb h₁

theorem sum_eq_zero_of_is_nontrivial [IsDomain R'] {ψ : AddChar R R'} (hψ : IsNontrivial ψ) : (∑ a, ψ (ofAdd a)) = 0 :=
  sum_eq_zero_of_is_nontrivial' hψ

/-- The sum over the values of the trivial additive character is the cardinality of the source. -/
theorem sum_eq_card_of_is_trivial {ψ : AddChar R R'} (hψ : ¬IsNontrivial ψ) : (∑ a, ψ (ofAdd a)) = Fintype.card R := by
  simp only [← is_nontrivial] at hψ
  push_neg  at hψ
  simp only [← hψ, ← Finset.sum_const, ← Nat.smul_one_eq_coe]
  rfl

theorem sum_eq_card_of_is_trivial' {ψ : AddChar R R'} (hψ : ¬IsNontrivial ψ) : (∑ a, ψ a) = Fintype.card R :=
  sum_eq_card_of_is_trivial hψ

/-- The sum over the values of `mul_shift ψ b` for `ψ` primitive is zero when `b ≠ 0`
and `#R` otherwise. -/
theorem sum_mul_shift [DecidableEq R] [IsDomain R'] (ψ : AddChar R R') (b : R) (hψ : IsPrimitive ψ) :
    (∑ x : R, ψ (ofAdd (x * b))) = if b = 0 then Fintype.card R else 0 := by
  split_ifs with h
  · -- case `b = 0`
    simp only [← h, ← sub_self, ← mul_zero, ← of_add_zero, ← map_one, ← Finset.sum_const, ← Nat.smul_one_eq_coe]
    rfl
    
  · -- case `b ≠ 0`
    simp_rw [mul_comm]
    exact sum_eq_zero_of_is_nontrivial (hψ b h)
    

end AddChar

end Additive

