/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers

! This file was ported from Lean 3 source module linear_algebra.orientation
! leanprover-community/mathlib commit 46a64b5b4268c594af770c44d9e502afc6a515cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Ray
import Mathbin.LinearAlgebra.Determinant

/-!
# Orientations of modules

This file defines orientations of modules.

## Main definitions

* `orientation` is a type synonym for `module.ray` for the case where the module is that of
alternating maps from a module to its underlying ring.  An orientation may be associated with an
alternating map or with a basis.

* `module.oriented` is a type class for a choice of orientation of a module that is considered
the positive orientation.

## Implementation notes

`orientation` is defined for an arbitrary index type, but the main intended use case is when
that index type is a `fintype` and there exists a basis of the same cardinality.

## References

* https://en.wikipedia.org/wiki/Orientation_(vector_space)

-/


noncomputable section

open BigOperators

section OrderedCommSemiring

variable (R : Type _) [StrictOrderedCommSemiring R]

variable (M : Type _) [AddCommMonoid M] [Module R M]

variable {N : Type _} [AddCommMonoid N] [Module R N]

variable (ι : Type _) [DecidableEq ι]

/-- An orientation of a module, intended to be used when `ι` is a `fintype` with the same
cardinality as a basis. -/
abbrev Orientation :=
  Module.Ray R (AlternatingMap R M R ι)
#align orientation Orientation

/-- A type class fixing an orientation of a module. -/
class Module.Oriented where
  positiveOrientation : Orientation R M ι
#align module.oriented Module.Oriented

export Module.Oriented (positiveOrientation)

variable {R M}

/-- An equivalence between modules implies an equivalence between orientations. -/
def Orientation.map (e : M ≃ₗ[R] N) : Orientation R M ι ≃ Orientation R N ι :=
  Module.Ray.map <| AlternatingMap.domLcongr R R ι R e
#align orientation.map Orientation.map

@[simp]
theorem Orientation.map_apply (e : M ≃ₗ[R] N) (v : AlternatingMap R M R ι) (hv : v ≠ 0) :
    Orientation.map ι e (rayOfNeZero _ v hv) =
      rayOfNeZero _ (v.compLinearMap e.symm) (mt (v.comp_linear_equiv_eq_zero_iff e.symm).mp hv) :=
  rfl
#align orientation.map_apply Orientation.map_apply

@[simp]
theorem Orientation.map_refl : (Orientation.map ι <| LinearEquiv.refl R M) = Equiv.refl _ := by
  rw [Orientation.map, AlternatingMap.dom_lcongr_refl, Module.Ray.map_refl]
#align orientation.map_refl Orientation.map_refl

@[simp]
theorem Orientation.map_symm (e : M ≃ₗ[R] N) :
    (Orientation.map ι e).symm = Orientation.map ι e.symm :=
  rfl
#align orientation.map_symm Orientation.map_symm

/-- A module is canonically oriented with respect to an empty index type. -/
instance (priority := 100) IsEmpty.oriented [Nontrivial R] [IsEmpty ι] : Module.Oriented R M ι
    where positiveOrientation :=
    rayOfNeZero R (AlternatingMap.constLinearEquivOfIsEmpty 1) <|
      AlternatingMap.constLinearEquivOfIsEmpty.Injective.Ne (by simp)
#align is_empty.oriented IsEmpty.oriented

@[simp]
theorem Orientation.map_positive_orientation_of_is_empty [Nontrivial R] [IsEmpty ι]
    (f : M ≃ₗ[R] N) : Orientation.map ι f positiveOrientation = positive_orientation :=
  rfl
#align
  orientation.map_positive_orientation_of_is_empty Orientation.map_positive_orientation_of_is_empty

@[simp]
theorem Orientation.map_of_is_empty [IsEmpty ι] (x : Orientation R M ι) (f : M ≃ₗ[R] M) :
    Orientation.map ι f x = x :=
  by
  induction' x using Module.Ray.ind with g hg
  rw [Orientation.map_apply]
  congr
  ext i
  rw [AlternatingMap.comp_linear_map_apply]
  congr
#align orientation.map_of_is_empty Orientation.map_of_is_empty

end OrderedCommSemiring

section OrderedCommRing

variable {R : Type _} [StrictOrderedCommRing R]

variable {M N : Type _} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

@[simp]
protected theorem Orientation.map_neg {ι : Type _} [DecidableEq ι] (f : M ≃ₗ[R] N)
    (x : Orientation R M ι) : Orientation.map ι f (-x) = -Orientation.map ι f x :=
  Module.Ray.map_neg _ x
#align orientation.map_neg Orientation.map_neg

namespace Basis

variable {ι : Type _} [DecidableEq ι]

/-- The value of `orientation.map` when the index type has the cardinality of a basis, in terms
of `f.det`. -/
theorem map_orientation_eq_det_inv_smul [Finite ι] (e : Basis ι R M) (x : Orientation R M ι)
    (f : M ≃ₗ[R] M) : Orientation.map ι f x = f.det⁻¹ • x :=
  by
  cases nonempty_fintype ι
  induction' x using Module.Ray.ind with g hg
  rw [Orientation.map_apply, smul_ray_of_ne_zero, ray_eq_iff, Units.smul_def,
    (g.comp_linear_map ↑f.symm).eq_smul_basis_det e, g.eq_smul_basis_det e,
    AlternatingMap.comp_linear_map_apply, AlternatingMap.smul_apply, Basis.det_comp, Basis.det_self,
    mul_one, smul_eq_mul, mul_comm, mul_smul, LinearEquiv.coe_inv_det]
#align basis.map_orientation_eq_det_inv_smul Basis.map_orientation_eq_det_inv_smul

variable [Fintype ι]

/-- The orientation given by a basis. -/
protected def orientation [Nontrivial R] (e : Basis ι R M) : Orientation R M ι :=
  rayOfNeZero R _ e.det_ne_zero
#align basis.orientation Basis.orientation

theorem orientation_map [Nontrivial R] (e : Basis ι R M) (f : M ≃ₗ[R] N) :
    (e.map f).Orientation = Orientation.map ι f e.Orientation := by
  simp_rw [Basis.orientation, Orientation.map_apply, Basis.det_map']
#align basis.orientation_map Basis.orientation_map

/-- The orientation given by a basis derived using `units_smul`, in terms of the product of those
units. -/
theorem orientation_units_smul [Nontrivial R] (e : Basis ι R M) (w : ι → Units R) :
    (e.units_smul w).Orientation = (∏ i, w i)⁻¹ • e.Orientation :=
  by
  rw [Basis.orientation, Basis.orientation, smul_ray_of_ne_zero, ray_eq_iff,
    e.det.eq_smul_basis_det (e.units_smul w), det_units_smul_self, Units.smul_def, smul_smul]
  norm_cast
  simp
#align basis.orientation_units_smul Basis.orientation_units_smul

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr ray_of_ne_zero _ _ _]] -/
@[simp]
theorem orientation_is_empty [Nontrivial R] [IsEmpty ι] (b : Basis ι R M) :
    b.Orientation = positive_orientation :=
  by
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr ray_of_ne_zero _ _ _]]"
  convert b.det_is_empty
#align basis.orientation_is_empty Basis.orientation_is_empty

end Basis

end OrderedCommRing

section LinearOrderedCommRing

variable {R : Type _} [LinearOrderedCommRing R]

variable {M : Type _} [AddCommGroup M] [Module R M]

variable {ι : Type _} [DecidableEq ι]

namespace Orientation

/-- A module `M` over a linearly ordered commutative ring has precisely two "orientations" with
respect to an empty index type. (Note that these are only orientations of `M` of in the conventional
mathematical sense if `M` is zero-dimensional.) -/
theorem eq_or_eq_neg_of_is_empty [Nontrivial R] [IsEmpty ι] (o : Orientation R M ι) :
    o = positive_orientation ∨ o = -positive_orientation :=
  by
  induction' o using Module.Ray.ind with x hx
  dsimp [positive_orientation]
  simp only [ray_eq_iff, same_ray_neg_swap]
  rw [same_ray_or_same_ray_neg_iff_not_linear_independent]
  intro h
  let a : R := alternating_map.const_linear_equiv_of_is_empty.symm x
  have H : LinearIndependent R ![a, 1] :=
    by
    convert h.map' (↑alternating_map.const_linear_equiv_of_is_empty.symm) (LinearEquiv.ker _)
    ext i
    fin_cases i <;> simp [a]
  rw [linear_independent_iff'] at H
  simpa using H Finset.univ ![1, -a] (by simp [Fin.sum_univ_succ]) 0 (by simp)
#align orientation.eq_or_eq_neg_of_is_empty Orientation.eq_or_eq_neg_of_is_empty

end Orientation

namespace Basis

variable [Fintype ι]

/-- The orientations given by two bases are equal if and only if the determinant of one basis
with respect to the other is positive. -/
theorem orientation_eq_iff_det_pos (e₁ e₂ : Basis ι R M) :
    e₁.Orientation = e₂.Orientation ↔ 0 < e₁.det e₂ :=
  calc
    e₁.Orientation = e₂.Orientation ↔ SameRay R e₁.det e₂.det := ray_eq_iff _ _
    _ ↔ SameRay R (e₁.det e₂ • e₂.det) e₂.det := by rw [← e₁.det.eq_smul_basis_det e₂]
    _ ↔ 0 < e₁.det e₂ := same_ray_smul_left_iff_of_ne e₂.det_ne_zero (e₁.is_unit_det e₂).NeZero
    
#align basis.orientation_eq_iff_det_pos Basis.orientation_eq_iff_det_pos

/-- Given a basis, any orientation equals the orientation given by that basis or its negation. -/
theorem orientation_eq_or_eq_neg (e : Basis ι R M) (x : Orientation R M ι) :
    x = e.Orientation ∨ x = -e.Orientation :=
  by
  induction' x using Module.Ray.ind with x hx
  rw [← x.map_basis_ne_zero_iff e] at hx
  rwa [Basis.orientation, ray_eq_iff, neg_ray_of_ne_zero, ray_eq_iff, x.eq_smul_basis_det e,
    same_ray_neg_smul_left_iff_of_ne e.det_ne_zero hx,
    same_ray_smul_left_iff_of_ne e.det_ne_zero hx, lt_or_lt_iff_ne, ne_comm]
#align basis.orientation_eq_or_eq_neg Basis.orientation_eq_or_eq_neg

/-- Given a basis, an orientation equals the negation of that given by that basis if and only
if it does not equal that given by that basis. -/
theorem orientation_ne_iff_eq_neg (e : Basis ι R M) (x : Orientation R M ι) :
    x ≠ e.Orientation ↔ x = -e.Orientation :=
  ⟨fun h => (e.orientation_eq_or_eq_neg x).resolve_left h, fun h =>
    h.symm ▸ (Module.Ray.ne_neg_self e.Orientation).symm⟩
#align basis.orientation_ne_iff_eq_neg Basis.orientation_ne_iff_eq_neg

/-- Composing a basis with a linear equiv gives the same orientation if and only if the
determinant is positive. -/
theorem orientation_comp_linear_equiv_eq_iff_det_pos (e : Basis ι R M) (f : M ≃ₗ[R] M) :
    (e.map f).Orientation = e.Orientation ↔ 0 < (f : M →ₗ[R] M).det := by
  rw [orientation_map, e.map_orientation_eq_det_inv_smul, units_inv_smul, units_smul_eq_self_iff,
    LinearEquiv.coe_det]
#align
  basis.orientation_comp_linear_equiv_eq_iff_det_pos Basis.orientation_comp_linear_equiv_eq_iff_det_pos

/-- Composing a basis with a linear equiv gives the negation of that orientation if and only if
the determinant is negative. -/
theorem orientation_comp_linear_equiv_eq_neg_iff_det_neg (e : Basis ι R M) (f : M ≃ₗ[R] M) :
    (e.map f).Orientation = -e.Orientation ↔ (f : M →ₗ[R] M).det < 0 := by
  rw [orientation_map, e.map_orientation_eq_det_inv_smul, units_inv_smul, units_smul_eq_neg_iff,
    LinearEquiv.coe_det]
#align
  basis.orientation_comp_linear_equiv_eq_neg_iff_det_neg Basis.orientation_comp_linear_equiv_eq_neg_iff_det_neg

/-- Negating a single basis vector (represented using `units_smul`) negates the corresponding
orientation. -/
@[simp]
theorem orientation_neg_single [Nontrivial R] (e : Basis ι R M) (i : ι) :
    (e.units_smul (Function.update 1 i (-1))).Orientation = -e.Orientation :=
  by
  rw [orientation_units_smul, Finset.prod_update_of_mem (Finset.mem_univ _)]
  simp
#align basis.orientation_neg_single Basis.orientation_neg_single

/-- Given a basis and an orientation, return a basis giving that orientation: either the original
basis, or one constructed by negating a single (arbitrary) basis vector. -/
def adjustToOrientation [Nontrivial R] [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι) :
    Basis ι R M :=
  haveI := Classical.decEq (Orientation R M ι)
  if e.orientation = x then e else e.units_smul (Function.update 1 (Classical.arbitrary ι) (-1))
#align basis.adjust_to_orientation Basis.adjustToOrientation

/-- `adjust_to_orientation` gives a basis with the required orientation. -/
@[simp]
theorem orientation_adjust_to_orientation [Nontrivial R] [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) : (e.adjustToOrientation x).Orientation = x :=
  by
  rw [adjust_to_orientation]
  split_ifs with h
  · exact h
  · rw [orientation_neg_single, eq_comm, ← orientation_ne_iff_eq_neg, ne_comm]
    exact h
#align basis.orientation_adjust_to_orientation Basis.orientation_adjust_to_orientation

/-- Every basis vector from `adjust_to_orientation` is either that from the original basis or its
negation. -/
theorem adjust_to_orientation_apply_eq_or_eq_neg [Nontrivial R] [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) (i : ι) :
    e.adjustToOrientation x i = e i ∨ e.adjustToOrientation x i = -e i :=
  by
  rw [adjust_to_orientation]
  split_ifs with h
  · simp
  · by_cases hi : i = Classical.arbitrary ι <;> simp [units_smul_apply, hi]
#align basis.adjust_to_orientation_apply_eq_or_eq_neg Basis.adjust_to_orientation_apply_eq_or_eq_neg

theorem det_adjust_to_orientation [Nontrivial R] [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) :
    (e.adjustToOrientation x).det = e.det ∨ (e.adjustToOrientation x).det = -e.det :=
  by
  dsimp [Basis.adjustToOrientation]
  split_ifs
  · left
    rfl
  · right
    simp [e.det_units_smul, ← Units.coe_prod, Finset.prod_update_of_mem]
#align basis.det_adjust_to_orientation Basis.det_adjust_to_orientation

@[simp]
theorem abs_det_adjust_to_orientation [Nontrivial R] [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) (v : ι → M) : |(e.adjustToOrientation x).det v| = |e.det v| := by
  cases' e.det_adjust_to_orientation x with h h <;> simp [h]
#align basis.abs_det_adjust_to_orientation Basis.abs_det_adjust_to_orientation

end Basis

end LinearOrderedCommRing

section LinearOrderedField

variable {R : Type _} [LinearOrderedField R]

variable {M : Type _} [AddCommGroup M] [Module R M]

variable {ι : Type _} [DecidableEq ι]

namespace Orientation

variable [Fintype ι] [_i : FiniteDimensional R M]

open FiniteDimensional

include _i

/-- If the index type has cardinality equal to the finite dimension, any two orientations are
equal or negations. -/
theorem eq_or_eq_neg (x₁ x₂ : Orientation R M ι) (h : Fintype.card ι = finrank R M) :
    x₁ = x₂ ∨ x₁ = -x₂ :=
  by
  have e := (fin_basis R M).reindex (Fintype.equivFinOfCardEq h).symm
  rcases e.orientation_eq_or_eq_neg x₁ with (h₁ | h₁) <;>
      rcases e.orientation_eq_or_eq_neg x₂ with (h₂ | h₂) <;>
    simp [h₁, h₂]
#align orientation.eq_or_eq_neg Orientation.eq_or_eq_neg

/-- If the index type has cardinality equal to the finite dimension, an orientation equals the
negation of another orientation if and only if they are not equal. -/
theorem ne_iff_eq_neg (x₁ x₂ : Orientation R M ι) (h : Fintype.card ι = finrank R M) :
    x₁ ≠ x₂ ↔ x₁ = -x₂ :=
  ⟨fun hn => (eq_or_eq_neg x₁ x₂ h).resolve_left hn, fun he =>
    he.symm ▸ (Module.Ray.ne_neg_self x₂).symm⟩
#align orientation.ne_iff_eq_neg Orientation.ne_iff_eq_neg

/-- The value of `orientation.map` when the index type has cardinality equal to the finite
dimension, in terms of `f.det`. -/
theorem map_eq_det_inv_smul (x : Orientation R M ι) (f : M ≃ₗ[R] M)
    (h : Fintype.card ι = finrank R M) : Orientation.map ι f x = f.det⁻¹ • x :=
  haveI e := (fin_basis R M).reindex (Fintype.equivFinOfCardEq h).symm
  e.map_orientation_eq_det_inv_smul x f
#align orientation.map_eq_det_inv_smul Orientation.map_eq_det_inv_smul

omit _i

/-- If the index type has cardinality equal to the finite dimension, composing an alternating
map with the same linear equiv on each argument gives the same orientation if and only if the
determinant is positive. -/
theorem map_eq_iff_det_pos (x : Orientation R M ι) (f : M ≃ₗ[R] M)
    (h : Fintype.card ι = finrank R M) : Orientation.map ι f x = x ↔ 0 < (f : M →ₗ[R] M).det :=
  by
  cases isEmpty_or_nonempty ι
  · have H : finrank R M = 0 := by
      refine' h.symm.trans _
      convert Fintype.card_of_is_empty
      infer_instance
    simp [LinearMap.det_eq_one_of_finrank_eq_zero H]
  have H : 0 < finrank R M := by
    rw [← h]
    exact Fintype.card_pos
  haveI : FiniteDimensional R M := finite_dimensional_of_finrank H
  rw [map_eq_det_inv_smul _ _ h, units_inv_smul, units_smul_eq_self_iff, LinearEquiv.coe_det]
#align orientation.map_eq_iff_det_pos Orientation.map_eq_iff_det_pos

/-- If the index type has cardinality equal to the finite dimension, composing an alternating
map with the same linear equiv on each argument gives the negation of that orientation if and
only if the determinant is negative. -/
theorem map_eq_neg_iff_det_neg (x : Orientation R M ι) (f : M ≃ₗ[R] M)
    (h : Fintype.card ι = finrank R M) : Orientation.map ι f x = -x ↔ (f : M →ₗ[R] M).det < 0 :=
  by
  cases isEmpty_or_nonempty ι
  · have H : finrank R M = 0 := by
      refine' h.symm.trans _
      convert Fintype.card_of_is_empty
      infer_instance
    simp [LinearMap.det_eq_one_of_finrank_eq_zero H, Module.Ray.ne_neg_self x]
  have H : 0 < finrank R M := by
    rw [← h]
    exact Fintype.card_pos
  haveI : FiniteDimensional R M := finite_dimensional_of_finrank H
  rw [map_eq_det_inv_smul _ _ h, units_inv_smul, units_smul_eq_neg_iff, LinearEquiv.coe_det]
#align orientation.map_eq_neg_iff_det_neg Orientation.map_eq_neg_iff_det_neg

include _i

/-- If the index type has cardinality equal to the finite dimension, a basis with the given
orientation. -/
def someBasis [Nonempty ι] (x : Orientation R M ι) (h : Fintype.card ι = finrank R M) :
    Basis ι R M :=
  ((finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm).adjustToOrientation x
#align orientation.some_basis Orientation.someBasis

/-- `some_basis` gives a basis with the required orientation. -/
@[simp]
theorem some_basis_orientation [Nonempty ι] (x : Orientation R M ι)
    (h : Fintype.card ι = finrank R M) : (x.someBasis h).Orientation = x :=
  Basis.orientation_adjust_to_orientation _ _
#align orientation.some_basis_orientation Orientation.some_basis_orientation

end Orientation

end LinearOrderedField

