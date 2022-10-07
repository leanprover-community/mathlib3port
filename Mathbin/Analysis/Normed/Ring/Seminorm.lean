/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathbin.Analysis.Seminorm

/-!
# Seminorms and norms on rings

This file defines seminorms and norms on rings. These definitions are useful when one needs to
consider multiple (semi)norms on a given ring.

## Main declarations

For a ring `R`:
* `ring_seminorm`: A seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero, takes
  nonnegative values, is subadditive and submultiplicative and such that `f (-x) = f x` for all
  `x ∈ R`.
* `ring_norm`: A seminorm `f` is a norm if `f x = 0` if and only if `x = 0`.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags
ring_seminorm, ring_norm
-/


open Nnreal

variable {R S : Type _} (x y : R) (r : ℝ)

/-- A seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero, takes nonnegative
  values, is subadditive and submultiplicative and such that `f (-x) = f x` for all `x ∈ R`. -/
structure RingSeminorm (R : Type _) [NonUnitalRing R] extends AddGroupSeminorm R where
  mul_le' : ∀ x y : R, to_fun (x * y) ≤ to_fun x * to_fun y

/-- A function `f : R → ℝ` is a norm on a (nonunital) ring if it is a seminorm and `f x = 0`
  implies `x = 0`. -/
structure RingNorm (R : Type _) [NonUnitalRing R] extends AddGroupNorm R, RingSeminorm R

attribute [nolint doc_blame] RingSeminorm.toAddGroupSeminorm RingNorm.toAddGroupNorm RingNorm.toRingSeminorm

/-- `ring_seminorm_class F α` states that `F` is a type of seminorms on the ring `α`.

You should extend this class when you extend `ring_seminorm`. -/
class RingSeminormClass (F : Type _) (α : outParam <| Type _) [NonUnitalRing α] extends AddGroupSeminormClass F α,
  SubmultiplicativeHomClass F α ℝ

/-- `ring_norm_class F α` states that `F` is a type of norms on the ring `α`.

You should extend this class when you extend `ring_norm`. -/
class RingNormClass (F : Type _) (α : outParam <| Type _) [NonUnitalRing α] extends RingSeminormClass F α,
  AddGroupNormClass F α

namespace RingSeminorm

section NonUnitalRing

variable [NonUnitalRing R]

instance ringSeminormClass : RingSeminormClass (RingSeminorm R) R where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by cases f <;> cases g <;> congr
  map_zero := fun f => f.map_zero'
  map_add_le_add := fun f => f.add_le'
  map_mul_le_mul := fun f => f.mul_le'
  map_neg_eq_map := fun f => f.neg'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : CoeFun (RingSeminorm R) fun _ => R → ℝ :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe (p : RingSeminorm R) : p.toFun = p :=
  rfl

@[ext]
theorem ext {p q : RingSeminorm R} : (∀ x, p x = q x) → p = q :=
  FunLike.ext p q

instance : Zero (RingSeminorm R) :=
  ⟨{ AddGroupSeminorm.hasZero.zero with mul_le' := fun _ _ => (zero_mul _).Ge }⟩

theorem eq_zero_iff {p : RingSeminorm R} : p = 0 ↔ ∀ x, p x = 0 :=
  FunLike.ext_iff

theorem ne_zero_iff {p : RingSeminorm R} : p ≠ 0 ↔ ∃ x, p x ≠ 0 := by simp [eq_zero_iff]

instance : Inhabited (RingSeminorm R) :=
  ⟨0⟩

/-- The trivial seminorm on a ring `R` is the `ring_seminorm` taking value `0` at `0` and `1` at
every other element. -/
instance [DecidableEq R] : One (RingSeminorm R) :=
  ⟨{ (1 : AddGroupSeminorm R) with
      mul_le' := fun x y => by
        by_cases h:x * y = 0
        · refine' (if_pos h).trans_le (mul_nonneg _ _) <;>
            · change _ ≤ ite _ _ _
              split_ifs
              exacts[le_rflₓ, zero_le_one]
              
          
        · change ite _ _ _ ≤ ite _ _ _ * ite _ _ _
          simp only [if_false, h, left_ne_zero_of_mul h, right_ne_zero_of_mul h, mul_oneₓ]
           }⟩

@[simp]
theorem apply_one [DecidableEq R] (x : R) : (1 : RingSeminorm R) x = if x = 0 then 0 else 1 :=
  rfl

end NonUnitalRing

section Ringₓ

variable [Ringₓ R] (p : RingSeminorm R)

theorem seminorm_one_eq_one_iff_ne_zero (hp : p 1 ≤ 1) : p 1 = 1 ↔ p ≠ 0 := by
  refine'
    ⟨fun h =>
      ne_zero_iff.mpr
        ⟨1, by
          rw [h]
          exact one_ne_zero⟩,
      fun h => _⟩
  obtain hp0 | hp0 := (map_nonneg p (1 : R)).eq_or_gt
  · cases h (ext fun x => (map_nonneg _ _).antisymm' _)
    simpa only [hp0, mul_oneₓ, mul_zero] using map_mul_le_mul p x 1
    
  · refine' hp.antisymm ((le_mul_iff_one_le_left hp0).1 _)
    simpa only [one_mulₓ] using map_mul_le_mul p (1 : R) _
    

end Ringₓ

end RingSeminorm

/-- The norm of a `non_unital_semi_normed_ring` as a `ring_seminorm`. -/
def normRingSeminorm (R : Type _) [NonUnitalSemiNormedRing R] : RingSeminorm R :=
  { normAddGroupSeminorm R with toFun := norm, mul_le' := norm_mul_le }

namespace RingNorm

variable [NonUnitalRing R]

instance ringNormClass : RingNormClass (RingNorm R) R where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by cases f <;> cases g <;> congr
  map_zero := fun f => f.map_zero'
  map_add_le_add := fun f => f.add_le'
  map_mul_le_mul := fun f => f.mul_le'
  map_neg_eq_map := fun f => f.neg'
  eq_zero_of_map_eq_zero := fun f => f.eq_zero_of_map_eq_zero'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : CoeFun (RingNorm R) fun _ => R → ℝ :=
  ⟨fun p => p.toFun⟩

@[simp]
theorem to_fun_eq_coe (p : RingNorm R) : p.toFun = p :=
  rfl

@[ext]
theorem ext {p q : RingNorm R} : (∀ x, p x = q x) → p = q :=
  FunLike.ext p q

variable (R)

/-- The trivial norm on a ring `R` is the `ring_norm` taking value `0` at `0` and `1` at every
  other element. -/
instance [DecidableEq R] : One (RingNorm R) :=
  ⟨{ (1 : RingSeminorm R), (1 : AddGroupNorm R) with }⟩

@[simp]
theorem apply_one [DecidableEq R] (x : R) : (1 : RingNorm R) x = if x = 0 then 0 else 1 :=
  rfl

instance [DecidableEq R] : Inhabited (RingNorm R) :=
  ⟨1⟩

end RingNorm

/-- A nonzero ring seminorm on a field `K` is a ring norm. -/
def RingSeminorm.toRingNorm {K : Type _} [Field K] (f : RingSeminorm K) (hnt : f ≠ 0) : RingNorm K :=
  { f with
    eq_zero_of_map_eq_zero' := fun x hx => by
      obtain ⟨c, hc⟩ := ring_seminorm.ne_zero_iff.mp hnt
      by_contra hn0
      have hc0 : f c = 0 := by
        rw [← mul_oneₓ c, ← mul_inv_cancel hn0, ← mul_assoc, mul_comm c, mul_assoc]
        exact
          le_antisymmₓ (le_transₓ (map_mul_le_mul f _ _) (by rw [← RingSeminorm.to_fun_eq_coe, hx, zero_mul]))
            (map_nonneg f _)
      exact hc hc0 }

/-- The norm of a normed_ring as a ring_norm. -/
@[simps]
def normRingNorm (R : Type _) [NonUnitalNormedRing R] : RingNorm R :=
  { normAddGroupNorm R, normRingSeminorm R with }

