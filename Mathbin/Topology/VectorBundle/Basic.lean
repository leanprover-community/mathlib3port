/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sebastien Gouezel, Heather Macbeth, Patrick Massot, Floris van Doorn
-/
import Analysis.NormedSpace.BoundedLinearMaps
import Topology.FiberBundle.Basic

#align_import topology.vector_bundle.basic from "leanprover-community/mathlib"@"e473c3198bb41f68560cab68a0529c854b618833"

/-!
# Vector bundles

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define (topological) vector bundles.

Let `B` be the base space, let `F` be a normed space over a normed field `R`, and let
`E : B → Type*` be a `fiber_bundle` with fiber `F`, in which, for each `x`, the fiber `E x` is a
topological vector space over `R`.

To have a vector bundle structure on `bundle.total_space F E`, one should additionally have the
following properties:

* The bundle trivializations in the trivialization atlas should be continuous linear equivs in the
fibers;
* For any two trivializations `e`, `e'` in the atlas the transition function considered as a map
from `B` into `F →L[R] F` is continuous on `e.base_set ∩ e'.base_set` with respect to the operator
norm topology on `F →L[R] F`.

If these conditions are satisfied, we register the typeclass `vector_bundle R F E`.

We define constructions on vector bundles like pullbacks and direct sums in other files.

## Main Definitions

* `trivialization.is_linear`: a class stating that a trivialization is fiberwise linear on its base
  set.
* `trivialization.linear_equiv_at` and `trivialization.continuous_linear_map_at` are the
  (continuous) linear fiberwise equivalences a trivialization induces.
* They have forward maps `trivialization.linear_map_at` / `trivialization.continuous_linear_map_at`
  and inverses `trivialization.symmₗ` / `trivialization.symmL`. Note that these are all defined
  everywhere, since they are extended using the zero function.
* `trivialization.coord_changeL` is the coordinate change induced by two trivializations. It only
  makes sense on the intersection of their base sets, but is extended outside it using the identity.
* Given a continuous (semi)linear map between `E x` and `E' y` where `E` and `E'` are bundles over
  possibly different base sets, `continuous_linear_map.in_coordinates` turns this into a continuous
  (semi)linear map between the chosen fibers of those bundles.

## Implementation notes

The implementation choices in the vector bundle definition are discussed in the "Implementation
notes" section of `topology.fiber_bundle.basic`.

## Tags
Vector bundle
-/


noncomputable section

open Bundle Set

open scoped Classical Bundle

variable (R : Type _) {B : Type _} (F : Type _) (E : B → Type _)

section TopologicalVectorSpace

variable {B F E} [Semiring R] [TopologicalSpace F] [TopologicalSpace B]

#print Pretrivialization.IsLinear /-
/-- A mixin class for `pretrivialization`, stating that a pretrivialization is fiberwise linear with
respect to given module structures on its fibers and the model fiber. -/
protected class Pretrivialization.IsLinear [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)]
    [∀ x, Module R (E x)] (e : Pretrivialization F (π F E)) : Prop where
  linear : ∀ b ∈ e.baseSet, IsLinearMap R fun x : E b => (e ⟨b, x⟩).2
#align pretrivialization.is_linear Pretrivialization.IsLinear
-/

namespace Pretrivialization

variable {F E} (e : Pretrivialization F (π F E)) {x : TotalSpace F E} {b : B} {y : E b}

#print Pretrivialization.linear /-
theorem linear [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]
    [e.isLinear R] {b : B} (hb : b ∈ e.baseSet) : IsLinearMap R fun x : E b => (e ⟨b, x⟩).2 :=
  Pretrivialization.IsLinear.linear b hb
#align pretrivialization.linear Pretrivialization.linear
-/

variable [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]

#print Pretrivialization.symmₗ /-
/-- A fiberwise linear inverse to `e`. -/
@[simps]
protected def symmₗ (e : Pretrivialization F (π F E)) [e.isLinear R] (b : B) : F →ₗ[R] E b :=
  by
  refine' IsLinearMap.mk' (e.symm b) _
  by_cases hb : b ∈ e.base_set
  ·
    exact
      (((e.linear R hb).mk' _).inverse (e.symm b) (e.symm_apply_apply_mk hb) fun v =>
          congr_arg Prod.snd <| e.apply_mk_symm hb v).isLinear
  · rw [e.coe_symm_of_not_mem hb]; exact (0 : F →ₗ[R] E b).isLinear
#align pretrivialization.symmₗ Pretrivialization.symmₗ
-/

#print Pretrivialization.linearEquivAt /-
/-- A pretrivialization for a vector bundle defines linear equivalences between the
fibers and the model space. -/
@[simps (config := { fullyApplied := false })]
def linearEquivAt (e : Pretrivialization F (π F E)) [e.isLinear R] (b : B) (hb : b ∈ e.baseSet) :
    E b ≃ₗ[R] F where
  toFun y := (e ⟨b, y⟩).2
  invFun := e.symm b
  left_inv := e.symm_apply_apply_mk hb
  right_inv v := by simp_rw [e.apply_mk_symm hb v]
  map_add' v w := (e.linear R hb).map_add v w
  map_smul' c v := (e.linear R hb).map_smul c v
#align pretrivialization.linear_equiv_at Pretrivialization.linearEquivAt
-/

#print Pretrivialization.linearMapAt /-
/-- A fiberwise linear map equal to `e` on `e.base_set`. -/
protected def linearMapAt (e : Pretrivialization F (π F E)) [e.isLinear R] (b : B) : E b →ₗ[R] F :=
  if hb : b ∈ e.baseSet then e.linearEquivAt R b hb else 0
#align pretrivialization.linear_map_at Pretrivialization.linearMapAt
-/

variable {R}

#print Pretrivialization.coe_linearMapAt /-
theorem coe_linearMapAt (e : Pretrivialization F (π F E)) [e.isLinear R] (b : B) :
    ⇑(e.linearMapAt R b) = fun y => if b ∈ e.baseSet then (e ⟨b, y⟩).2 else 0 := by
  rw [Pretrivialization.linearMapAt]; split_ifs <;> rfl
#align pretrivialization.coe_linear_map_at Pretrivialization.coe_linearMapAt
-/

#print Pretrivialization.coe_linearMapAt_of_mem /-
theorem coe_linearMapAt_of_mem (e : Pretrivialization F (π F E)) [e.isLinear R] {b : B}
    (hb : b ∈ e.baseSet) : ⇑(e.linearMapAt R b) = fun y => (e ⟨b, y⟩).2 := by
  simp_rw [coe_linear_map_at, if_pos hb]
#align pretrivialization.coe_linear_map_at_of_mem Pretrivialization.coe_linearMapAt_of_mem
-/

#print Pretrivialization.linearMapAt_apply /-
theorem linearMapAt_apply (e : Pretrivialization F (π F E)) [e.isLinear R] {b : B} (y : E b) :
    e.linearMapAt R b y = if b ∈ e.baseSet then (e ⟨b, y⟩).2 else 0 := by rw [coe_linear_map_at]
#align pretrivialization.linear_map_at_apply Pretrivialization.linearMapAt_apply
-/

#print Pretrivialization.linearMapAt_def_of_mem /-
theorem linearMapAt_def_of_mem (e : Pretrivialization F (π F E)) [e.isLinear R] {b : B}
    (hb : b ∈ e.baseSet) : e.linearMapAt R b = e.linearEquivAt R b hb :=
  dif_pos hb
#align pretrivialization.linear_map_at_def_of_mem Pretrivialization.linearMapAt_def_of_mem
-/

#print Pretrivialization.linearMapAt_def_of_not_mem /-
theorem linearMapAt_def_of_not_mem (e : Pretrivialization F (π F E)) [e.isLinear R] {b : B}
    (hb : b ∉ e.baseSet) : e.linearMapAt R b = 0 :=
  dif_neg hb
#align pretrivialization.linear_map_at_def_of_not_mem Pretrivialization.linearMapAt_def_of_not_mem
-/

#print Pretrivialization.linearMapAt_eq_zero /-
theorem linearMapAt_eq_zero (e : Pretrivialization F (π F E)) [e.isLinear R] {b : B}
    (hb : b ∉ e.baseSet) : e.linearMapAt R b = 0 :=
  dif_neg hb
#align pretrivialization.linear_map_at_eq_zero Pretrivialization.linearMapAt_eq_zero
-/

#print Pretrivialization.symmₗ_linearMapAt /-
theorem symmₗ_linearMapAt (e : Pretrivialization F (π F E)) [e.isLinear R] {b : B}
    (hb : b ∈ e.baseSet) (y : E b) : e.symmₗ R b (e.linearMapAt R b y) = y := by
  rw [e.linear_map_at_def_of_mem hb]; exact (e.linear_equiv_at R b hb).left_inv y
#align pretrivialization.symmₗ_linear_map_at Pretrivialization.symmₗ_linearMapAt
-/

#print Pretrivialization.linearMapAt_symmₗ /-
theorem linearMapAt_symmₗ (e : Pretrivialization F (π F E)) [e.isLinear R] {b : B}
    (hb : b ∈ e.baseSet) (y : F) : e.linearMapAt R b (e.symmₗ R b y) = y := by
  rw [e.linear_map_at_def_of_mem hb]; exact (e.linear_equiv_at R b hb).right_inv y
#align pretrivialization.linear_map_at_symmₗ Pretrivialization.linearMapAt_symmₗ
-/

end Pretrivialization

variable (R) [TopologicalSpace (TotalSpace F E)]

#print Trivialization.IsLinear /-
/-- A mixin class for `trivialization`, stating that a trivialization is fiberwise linear with
respect to given module structures on its fibers and the model fiber. -/
protected class Trivialization.IsLinear [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)]
    [∀ x, Module R (E x)] (e : Trivialization F (π F E)) : Prop where
  linear : ∀ b ∈ e.baseSet, IsLinearMap R fun x : E b => (e ⟨b, x⟩).2
#align trivialization.is_linear Trivialization.IsLinear
-/

namespace Trivialization

variable (e : Trivialization F (π F E)) {x : TotalSpace F E} {b : B} {y : E b}

#print Trivialization.linear /-
protected theorem linear [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)]
    [∀ x, Module R (E x)] [e.isLinear R] {b : B} (hb : b ∈ e.baseSet) :
    IsLinearMap R fun y : E b => (e ⟨b, y⟩).2 :=
  Trivialization.IsLinear.linear b hb
#align trivialization.linear Trivialization.linear
-/

#print Trivialization.toPretrivialization.isLinear /-
instance toPretrivialization.isLinear [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)]
    [∀ x, Module R (E x)] [e.isLinear R] : e.toPretrivialization.isLinear R :=
  { (‹_› : e.isLinear R) with }
#align trivialization.to_pretrivialization.is_linear Trivialization.toPretrivialization.isLinear
-/

variable [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]

#print Trivialization.linearEquivAt /-
/-- A trivialization for a vector bundle defines linear equivalences between the
fibers and the model space. -/
def linearEquivAt (e : Trivialization F (π F E)) [e.isLinear R] (b : B) (hb : b ∈ e.baseSet) :
    E b ≃ₗ[R] F :=
  e.toPretrivialization.linearEquivAt R b hb
#align trivialization.linear_equiv_at Trivialization.linearEquivAt
-/

variable {R}

#print Trivialization.linearEquivAt_apply /-
@[simp]
theorem linearEquivAt_apply (e : Trivialization F (π F E)) [e.isLinear R] (b : B)
    (hb : b ∈ e.baseSet) (v : E b) : e.linearEquivAt R b hb v = (e ⟨b, v⟩).2 :=
  rfl
#align trivialization.linear_equiv_at_apply Trivialization.linearEquivAt_apply
-/

#print Trivialization.linearEquivAt_symm_apply /-
@[simp]
theorem linearEquivAt_symm_apply (e : Trivialization F (π F E)) [e.isLinear R] (b : B)
    (hb : b ∈ e.baseSet) (v : F) : (e.linearEquivAt R b hb).symm v = e.symm b v :=
  rfl
#align trivialization.linear_equiv_at_symm_apply Trivialization.linearEquivAt_symm_apply
-/

variable (R)

#print Trivialization.symmₗ /-
/-- A fiberwise linear inverse to `e`. -/
protected def symmₗ (e : Trivialization F (π F E)) [e.isLinear R] (b : B) : F →ₗ[R] E b :=
  e.toPretrivialization.symmₗ R b
#align trivialization.symmₗ Trivialization.symmₗ
-/

variable {R}

#print Trivialization.coe_symmₗ /-
theorem coe_symmₗ (e : Trivialization F (π F E)) [e.isLinear R] (b : B) :
    ⇑(e.symmₗ R b) = e.symm b :=
  rfl
#align trivialization.coe_symmₗ Trivialization.coe_symmₗ
-/

variable (R)

#print Trivialization.linearMapAt /-
/-- A fiberwise linear map equal to `e` on `e.base_set`. -/
protected def linearMapAt (e : Trivialization F (π F E)) [e.isLinear R] (b : B) : E b →ₗ[R] F :=
  e.toPretrivialization.linearMapAt R b
#align trivialization.linear_map_at Trivialization.linearMapAt
-/

variable {R}

#print Trivialization.coe_linearMapAt /-
theorem coe_linearMapAt (e : Trivialization F (π F E)) [e.isLinear R] (b : B) :
    ⇑(e.linearMapAt R b) = fun y => if b ∈ e.baseSet then (e ⟨b, y⟩).2 else 0 :=
  e.toPretrivialization.coe_linearMapAt b
#align trivialization.coe_linear_map_at Trivialization.coe_linearMapAt
-/

#print Trivialization.coe_linearMapAt_of_mem /-
theorem coe_linearMapAt_of_mem (e : Trivialization F (π F E)) [e.isLinear R] {b : B}
    (hb : b ∈ e.baseSet) : ⇑(e.linearMapAt R b) = fun y => (e ⟨b, y⟩).2 := by
  simp_rw [coe_linear_map_at, if_pos hb]
#align trivialization.coe_linear_map_at_of_mem Trivialization.coe_linearMapAt_of_mem
-/

#print Trivialization.linearMapAt_apply /-
theorem linearMapAt_apply (e : Trivialization F (π F E)) [e.isLinear R] {b : B} (y : E b) :
    e.linearMapAt R b y = if b ∈ e.baseSet then (e ⟨b, y⟩).2 else 0 := by rw [coe_linear_map_at]
#align trivialization.linear_map_at_apply Trivialization.linearMapAt_apply
-/

#print Trivialization.linearMapAt_def_of_mem /-
theorem linearMapAt_def_of_mem (e : Trivialization F (π F E)) [e.isLinear R] {b : B}
    (hb : b ∈ e.baseSet) : e.linearMapAt R b = e.linearEquivAt R b hb :=
  dif_pos hb
#align trivialization.linear_map_at_def_of_mem Trivialization.linearMapAt_def_of_mem
-/

#print Trivialization.linearMapAt_def_of_not_mem /-
theorem linearMapAt_def_of_not_mem (e : Trivialization F (π F E)) [e.isLinear R] {b : B}
    (hb : b ∉ e.baseSet) : e.linearMapAt R b = 0 :=
  dif_neg hb
#align trivialization.linear_map_at_def_of_not_mem Trivialization.linearMapAt_def_of_not_mem
-/

#print Trivialization.symmₗ_linearMapAt /-
theorem symmₗ_linearMapAt (e : Trivialization F (π F E)) [e.isLinear R] {b : B} (hb : b ∈ e.baseSet)
    (y : E b) : e.symmₗ R b (e.linearMapAt R b y) = y :=
  e.toPretrivialization.symmₗ_linearMapAt hb y
#align trivialization.symmₗ_linear_map_at Trivialization.symmₗ_linearMapAt
-/

#print Trivialization.linearMapAt_symmₗ /-
theorem linearMapAt_symmₗ (e : Trivialization F (π F E)) [e.isLinear R] {b : B} (hb : b ∈ e.baseSet)
    (y : F) : e.linearMapAt R b (e.symmₗ R b y) = y :=
  e.toPretrivialization.linearMapAt_symmₗ hb y
#align trivialization.linear_map_at_symmₗ Trivialization.linearMapAt_symmₗ
-/

variable (R)

#print Trivialization.coordChangeL /-
/-- A coordinate change function between two trivializations, as a continuous linear equivalence.
  Defined to be the identity when `b` does not lie in the base set of both trivializations. -/
def coordChangeL (e e' : Trivialization F (π F E)) [e.isLinear R] [e'.isLinear R] (b : B) :
    F ≃L[R] F :=
  {
    if hb : b ∈ e.baseSet ∩ e'.baseSet then
      (e.linearEquivAt R b (hb.1 : _)).symm.trans (e'.linearEquivAt R b hb.2)
    else
      LinearEquiv.refl R
        F with
    continuous_toFun := by
      by_cases hb : b ∈ e.base_set ∩ e'.base_set
      · simp_rw [dif_pos hb]
        refine' (e'.continuous_on.comp_continuous _ _).snd
        exact
          e.continuous_on_symm.comp_continuous (Continuous.Prod.mk b) fun y =>
            mk_mem_prod hb.1 (mem_univ y)
        exact fun y => e'.mem_source.mpr hb.2
      · rw [dif_neg hb]; exact continuous_id
    continuous_invFun := by
      by_cases hb : b ∈ e.base_set ∩ e'.base_set
      · simp_rw [dif_pos hb]
        refine' (e.continuous_on.comp_continuous _ _).snd
        exact
          e'.continuous_on_symm.comp_continuous (Continuous.Prod.mk b) fun y =>
            mk_mem_prod hb.2 (mem_univ y)
        exact fun y => e.mem_source.mpr hb.1
      · rw [dif_neg hb]; exact continuous_id }
#align trivialization.coord_changeL Trivialization.coordChangeL
-/

variable {R}

#print Trivialization.coe_coordChangeL /-
theorem coe_coordChangeL (e e' : Trivialization F (π F E)) [e.isLinear R] [e'.isLinear R] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    ⇑(coordChangeL R e e' b) = (e.linearEquivAt R b hb.1).symm.trans (e'.linearEquivAt R b hb.2) :=
  congr_arg LinearEquiv.toFun (dif_pos hb)
#align trivialization.coe_coord_changeL Trivialization.coe_coordChangeL
-/

#print Trivialization.coe_coordChangeL' /-
theorem coe_coordChangeL' (e e' : Trivialization F (π F E)) [e.isLinear R] [e'.isLinear R] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    (coordChangeL R e e' b).toLinearEquiv =
      (e.linearEquivAt R b hb.1).symm.trans (e'.linearEquivAt R b hb.2) :=
  LinearEquiv.coe_injective (coe_coordChangeL _ _ _)
#align trivialization.coe_coord_changeL' Trivialization.coe_coordChangeL'
-/

#print Trivialization.symm_coordChangeL /-
theorem symm_coordChangeL (e e' : Trivialization F (π F E)) [e.isLinear R] [e'.isLinear R] {b : B}
    (hb : b ∈ e'.baseSet ∩ e.baseSet) : (e.coordChangeL R e' b).symm = e'.coordChangeL R e b :=
  by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  rw [coe_coord_changeL' e' e hb, (coord_changeL R e e' b).symm_toLinearEquiv,
    coe_coord_changeL' e e' hb.symm, LinearEquiv.trans_symm, LinearEquiv.symm_symm]
#align trivialization.symm_coord_changeL Trivialization.symm_coordChangeL
-/

#print Trivialization.coordChangeL_apply /-
theorem coordChangeL_apply (e e' : Trivialization F (π F E)) [e.isLinear R] [e'.isLinear R] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (y : F) : coordChangeL R e e' b y = (e' ⟨b, e.symm b y⟩).2 :=
  congr_arg (fun f => LinearEquiv.toFun f y) (dif_pos hb)
#align trivialization.coord_changeL_apply Trivialization.coordChangeL_apply
-/

#print Trivialization.mk_coordChangeL /-
theorem mk_coordChangeL (e e' : Trivialization F (π F E)) [e.isLinear R] [e'.isLinear R] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (y : F) : (b, coordChangeL R e e' b y) = e' ⟨b, e.symm b y⟩ :=
  by
  ext
  · rw [e.mk_symm hb.1 y, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]; exact hb.2
  · exact e.coord_changeL_apply e' hb y
#align trivialization.mk_coord_changeL Trivialization.mk_coordChangeL
-/

#print Trivialization.apply_symm_apply_eq_coordChangeL /-
theorem apply_symm_apply_eq_coordChangeL (e e' : Trivialization F (π F E)) [e.isLinear R]
    [e'.isLinear R] {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : F) :
    e' (e.toPartialHomeomorph.symm (b, v)) = (b, e.coordChangeL R e' b v) := by
  rw [e.mk_coord_changeL e' hb, e.mk_symm hb.1]
#align trivialization.apply_symm_apply_eq_coord_changeL Trivialization.apply_symm_apply_eq_coordChangeL
-/

#print Trivialization.coordChangeL_apply' /-
/-- A version of `coord_change_apply` that fully unfolds `coord_change`. The right-hand side is
ugly, but has good definitional properties for specifically defined trivializations. -/
theorem coordChangeL_apply' (e e' : Trivialization F (π F E)) [e.isLinear R] [e'.isLinear R] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (y : F) :
    coordChangeL R e e' b y = (e' (e.toPartialHomeomorph.symm (b, y))).2 := by
  rw [e.coord_changeL_apply e' hb, e.mk_symm hb.1]
#align trivialization.coord_changeL_apply' Trivialization.coordChangeL_apply'
-/

#print Trivialization.coordChangeL_symm_apply /-
theorem coordChangeL_symm_apply (e e' : Trivialization F (π F E)) [e.isLinear R] [e'.isLinear R]
    {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    ⇑(coordChangeL R e e' b).symm =
      (e'.linearEquivAt R b hb.2).symm.trans (e.linearEquivAt R b hb.1) :=
  congr_arg LinearEquiv.invFun (dif_pos hb)
#align trivialization.coord_changeL_symm_apply Trivialization.coordChangeL_symm_apply
-/

end Trivialization

end TopologicalVectorSpace

section

namespace Bundle

#print Bundle.zeroSection /-
/-- The zero section of a vector bundle -/
def zeroSection [∀ x, Zero (E x)] : B → TotalSpace F E := fun x => ⟨x, 0⟩
#align bundle.zero_section Bundle.zeroSection
-/

#print Bundle.zeroSection_proj /-
@[simp, mfld_simps]
theorem zeroSection_proj [∀ x, Zero (E x)] (x : B) : (zeroSection F E x).proj = x :=
  rfl
#align bundle.zero_section_proj Bundle.zeroSection_proj
-/

#print Bundle.zeroSection_snd /-
@[simp, mfld_simps]
theorem zeroSection_snd [∀ x, Zero (E x)] (x : B) : (zeroSection F E x).2 = 0 :=
  rfl
#align bundle.zero_section_snd Bundle.zeroSection_snd
-/

end Bundle

open Bundle

variable [NontriviallyNormedField R] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]
  [NormedAddCommGroup F] [NormedSpace R F] [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E]

#print VectorBundle /-
/- ./././Mathport/Syntax/Translate/Command.lean:400:30: infer kinds are unsupported in Lean 4: #[`continuousOn_coord_change'] [] -/
/-- The space `total_space F E` (for `E : B → Type*` such that each `E x` is a topological vector
space) has a topological vector space structure with fiber `F` (denoted with
`vector_bundle R F E`) if around every point there is a fiber bundle trivialization
which is linear in the fibers. -/
class VectorBundle : Prop where
  trivialization_linear' : ∀ (e : Trivialization F (π F E)) [MemTrivializationAtlas e], e.isLinear R
  continuousOn_coord_change' :
    ∀ (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'],
      ContinuousOn (fun b => Trivialization.coordChangeL R e e' b : B → F →L[R] F)
        (e.baseSet ∩ e'.baseSet)
#align vector_bundle VectorBundle
-/

variable {F E}

#print trivialization_linear /-
instance (priority := 100) trivialization_linear [VectorBundle R F E] (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] : e.isLinear R :=
  VectorBundle.trivialization_linear' e
#align trivialization_linear trivialization_linear
-/

#print continuousOn_coordChange /-
theorem continuousOn_coordChange [VectorBundle R F E] (e e' : Trivialization F (π F E))
    [he : MemTrivializationAtlas e] [he' : MemTrivializationAtlas e'] :
    ContinuousOn (fun b => Trivialization.coordChangeL R e e' b : B → F →L[R] F)
      (e.baseSet ∩ e'.baseSet) :=
  VectorBundle.continuousOn_coord_change' R e e'
#align continuous_on_coord_change continuousOn_coordChange
-/

namespace Trivialization

#print Trivialization.continuousLinearMapAt /-
/-- Forward map of `continuous_linear_equiv_at` (only propositionally equal),
  defined everywhere (`0` outside domain). -/
@[simps (config := { fullyApplied := false }) apply]
def continuousLinearMapAt (e : Trivialization F (π F E)) [e.isLinear R] (b : B) : E b →L[R] F :=
  {-- given explicitly to help `simps`
        e.linearMapAt
      R b with
    toFun := e.linearMapAt R b
    cont := by
      dsimp
      rw [e.coe_linear_map_at b]
      refine' continuous_if_const _ (fun hb => _) fun _ => continuous_zero
      exact
        continuous_snd.comp
          (e.continuous_on.comp_continuous (FiberBundle.totalSpace_mk_inducing F E b).Continuous
            fun x => e.mem_source.mpr hb) }
#align trivialization.continuous_linear_map_at Trivialization.continuousLinearMapAt
-/

#print Trivialization.symmL /-
/-- Backwards map of `continuous_linear_equiv_at`, defined everywhere. -/
@[simps (config := { fullyApplied := false }) apply]
def symmL (e : Trivialization F (π F E)) [e.isLinear R] (b : B) : F →L[R] E b :=
  {-- given explicitly to help `simps`
        e.symmₗ
      R b with
    toFun := e.symm b
    cont := by
      by_cases hb : b ∈ e.base_set
      · rw [(FiberBundle.totalSpace_mk_inducing F E b).continuous_iff]
        exact
          e.continuous_on_symm.comp_continuous (continuous_const.prod_mk continuous_id) fun x =>
            mk_mem_prod hb (mem_univ x)
      · refine' continuous_zero.congr fun x => (e.symm_apply_of_not_mem hb x).symm }
#align trivialization.symmL Trivialization.symmL
-/

variable {R}

#print Trivialization.symmL_continuousLinearMapAt /-
theorem symmL_continuousLinearMapAt (e : Trivialization F (π F E)) [e.isLinear R] {b : B}
    (hb : b ∈ e.baseSet) (y : E b) : e.symmL R b (e.continuousLinearMapAt R b y) = y :=
  e.symmₗ_linearMapAt hb y
#align trivialization.symmL_continuous_linear_map_at Trivialization.symmL_continuousLinearMapAt
-/

#print Trivialization.continuousLinearMapAt_symmL /-
theorem continuousLinearMapAt_symmL (e : Trivialization F (π F E)) [e.isLinear R] {b : B}
    (hb : b ∈ e.baseSet) (y : F) : e.continuousLinearMapAt R b (e.symmL R b y) = y :=
  e.linearMapAt_symmₗ hb y
#align trivialization.continuous_linear_map_at_symmL Trivialization.continuousLinearMapAt_symmL
-/

variable (R)

#print Trivialization.continuousLinearEquivAt /-
/-- In a vector bundle, a trivialization in the fiber (which is a priori only linear)
is in fact a continuous linear equiv between the fibers and the model fiber. -/
@[simps (config := { fullyApplied := false }) apply symm_apply]
def continuousLinearEquivAt (e : Trivialization F (π F E)) [e.isLinear R] (b : B)
    (hb : b ∈ e.baseSet) : E b ≃L[R] F :=
  {-- given explicitly to help `simps`
          -- given explicitly to help `simps`
          e.toPretrivialization.linearEquivAt
      R b hb with
    toFun := fun y => (e ⟨b, y⟩).2
    invFun := e.symm b
    continuous_toFun :=
      continuous_snd.comp
        (e.ContinuousOn.comp_continuous (FiberBundle.totalSpace_mk_inducing F E b).Continuous
          fun x => e.mem_source.mpr hb)
    continuous_invFun := (e.symmL R b).Continuous }
#align trivialization.continuous_linear_equiv_at Trivialization.continuousLinearEquivAt
-/

variable {R}

#print Trivialization.coe_continuousLinearEquivAt_eq /-
theorem coe_continuousLinearEquivAt_eq (e : Trivialization F (π F E)) [e.isLinear R] {b : B}
    (hb : b ∈ e.baseSet) :
    (e.continuousLinearEquivAt R b hb : E b → F) = e.continuousLinearMapAt R b :=
  (e.coe_linearMapAt_of_mem hb).symm
#align trivialization.coe_continuous_linear_equiv_at_eq Trivialization.coe_continuousLinearEquivAt_eq
-/

#print Trivialization.symm_continuousLinearEquivAt_eq /-
theorem symm_continuousLinearEquivAt_eq (e : Trivialization F (π F E)) [e.isLinear R] {b : B}
    (hb : b ∈ e.baseSet) : ((e.continuousLinearEquivAt R b hb).symm : F → E b) = e.symmL R b :=
  rfl
#align trivialization.symm_continuous_linear_equiv_at_eq Trivialization.symm_continuousLinearEquivAt_eq
-/

#print Trivialization.continuousLinearEquivAt_apply' /-
@[simp]
theorem continuousLinearEquivAt_apply' (e : Trivialization F (π F E)) [e.isLinear R]
    (x : TotalSpace F E) (hx : x ∈ e.source) :
    e.continuousLinearEquivAt R x.proj (e.mem_source.1 hx) x.2 = (e x).2 := by cases x; rfl
#align trivialization.continuous_linear_equiv_at_apply' Trivialization.continuousLinearEquivAt_apply'
-/

variable (R)

#print Trivialization.apply_eq_prod_continuousLinearEquivAt /-
theorem apply_eq_prod_continuousLinearEquivAt (e : Trivialization F (π F E)) [e.isLinear R] (b : B)
    (hb : b ∈ e.baseSet) (z : E b) : e ⟨b, z⟩ = (b, e.continuousLinearEquivAt R b hb z) :=
  by
  ext
  · refine' e.coe_fst _
    rw [e.source_eq]
    exact hb
  · simp only [coe_coe, continuous_linear_equiv_at_apply]
#align trivialization.apply_eq_prod_continuous_linear_equiv_at Trivialization.apply_eq_prod_continuousLinearEquivAt
-/

#print Trivialization.zeroSection /-
protected theorem zeroSection (e : Trivialization F (π F E)) [e.isLinear R] {x : B}
    (hx : x ∈ e.baseSet) : e (zeroSection F E x) = (x, 0) := by
  simp_rw [zero_section, e.apply_eq_prod_continuous_linear_equiv_at R x hx 0, map_zero]
#align trivialization.zero_section Trivialization.zeroSection
-/

variable {R}

#print Trivialization.symm_apply_eq_mk_continuousLinearEquivAt_symm /-
theorem symm_apply_eq_mk_continuousLinearEquivAt_symm (e : Trivialization F (π F E)) [e.isLinear R]
    (b : B) (hb : b ∈ e.baseSet) (z : F) :
    e.toPartialHomeomorph.symm ⟨b, z⟩ = ⟨b, (e.continuousLinearEquivAt R b hb).symm z⟩ :=
  by
  have h : (b, z) ∈ e.target := by
    rw [e.target_eq]
    exact ⟨hb, mem_univ _⟩
  apply e.inj_on (e.map_target h)
  · simp only [e.source_eq, hb, mem_preimage]
  simp_rw [e.right_inv h, coe_coe, e.apply_eq_prod_continuous_linear_equiv_at R b hb,
    ContinuousLinearEquiv.apply_symm_apply]
#align trivialization.symm_apply_eq_mk_continuous_linear_equiv_at_symm Trivialization.symm_apply_eq_mk_continuousLinearEquivAt_symm
-/

#print Trivialization.comp_continuousLinearEquivAt_eq_coord_change /-
theorem comp_continuousLinearEquivAt_eq_coord_change (e e' : Trivialization F (π F E))
    [e.isLinear R] [e'.isLinear R] {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    (e.continuousLinearEquivAt R b hb.1).symm.trans (e'.continuousLinearEquivAt R b hb.2) =
      coordChangeL R e e' b :=
  by ext v; rw [coord_changeL_apply e e' hb]; rfl
#align trivialization.comp_continuous_linear_equiv_at_eq_coord_change Trivialization.comp_continuousLinearEquivAt_eq_coord_change
-/

end Trivialization

/-! ### Constructing vector bundles -/


variable (R B F)

#print VectorBundleCore /-
/-- Analogous construction of `fiber_bundle_core` for vector bundles. This
construction gives a way to construct vector bundles from a structure registering how
trivialization changes act on fibers. -/
structure VectorBundleCore (ι : Type _) where
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (base_set i)
  indexAt : B → ι
  mem_baseSet_at : ∀ x, x ∈ base_set (index_at x)
  coordChange : ι → ι → B → F →L[R] F
  coordChange_self : ∀ i, ∀ x ∈ base_set i, ∀ v, coord_change i i x v = v
  continuousOn_coordChange : ∀ i j, ContinuousOn (coord_change i j) (base_set i ∩ base_set j)
  coordChange_comp :
    ∀ i j k,
      ∀ x ∈ base_set i ∩ base_set j ∩ base_set k,
        ∀ v, (coord_change j k x) (coord_change i j x v) = coord_change i k x v
#align vector_bundle_core VectorBundleCore
-/

#print trivialVectorBundleCore /-
/-- The trivial vector bundle core, in which all the changes of coordinates are the
identity. -/
def trivialVectorBundleCore (ι : Type _) [Inhabited ι] : VectorBundleCore R B F ι
    where
  baseSet ι := univ
  isOpen_baseSet i := isOpen_univ
  indexAt := default
  mem_baseSet_at x := mem_univ x
  coordChange i j x := ContinuousLinearMap.id R F
  coordChange_self i x hx v := rfl
  coordChange_comp i j k x hx v := rfl
  continuousOn_coordChange i j := continuousOn_const
#align trivial_vector_bundle_core trivialVectorBundleCore
-/

instance (ι : Type _) [Inhabited ι] : Inhabited (VectorBundleCore R B F ι) :=
  ⟨trivialVectorBundleCore R B F ι⟩

namespace VectorBundleCore

variable {R B F} {ι : Type _} (Z : VectorBundleCore R B F ι)

#print VectorBundleCore.toFiberBundleCore /-
/-- Natural identification to a `fiber_bundle_core`. -/
@[simps (config := mfld_cfg)]
def toFiberBundleCore : FiberBundleCore ι B F :=
  { Z with
    coordChange := fun i j b => Z.coordChange i j b
    continuousOn_coordChange := fun i j =>
      isBoundedBilinearMap_apply.Continuous.comp_continuousOn
        ((Z.continuousOn_coordChange i j).Prod_map continuousOn_id) }
#align vector_bundle_core.to_fiber_bundle_core VectorBundleCore.toFiberBundleCore
-/

instance toFiberBundleCoreCoe : Coe (VectorBundleCore R B F ι) (FiberBundleCore ι B F) :=
  ⟨toFiberBundleCore⟩
#align vector_bundle_core.to_fiber_bundle_core_coe VectorBundleCore.toFiberBundleCoreCoe

#print VectorBundleCore.coordChange_linear_comp /-
theorem coordChange_linear_comp (i j k : ι) :
    ∀ x ∈ Z.baseSet i ∩ Z.baseSet j ∩ Z.baseSet k,
      (Z.coordChange j k x).comp (Z.coordChange i j x) = Z.coordChange i k x :=
  fun x hx => by ext v; exact Z.coord_change_comp i j k x hx v
#align vector_bundle_core.coord_change_linear_comp VectorBundleCore.coordChange_linear_comp
-/

#print VectorBundleCore.Index /-
/-- The index set of a vector bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments has_nonempty_instance]
def Index :=
  ι
#align vector_bundle_core.index VectorBundleCore.Index
-/

#print VectorBundleCore.Base /-
/-- The base space of a vector bundle core, as a convenience function for dot notation-/
@[nolint unused_arguments, reducible]
def Base :=
  B
#align vector_bundle_core.base VectorBundleCore.Base
-/

#print VectorBundleCore.Fiber /-
/-- The fiber of a vector bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unused_arguments has_nonempty_instance]
def Fiber : B → Type _ :=
  Z.toFiberBundleCore.Fiber
#align vector_bundle_core.fiber VectorBundleCore.Fiber
-/

#print VectorBundleCore.topologicalSpaceFiber /-
instance topologicalSpaceFiber (x : B) : TopologicalSpace (Z.Fiber x) := by
  delta_instance vector_bundle_core.fiber
#align vector_bundle_core.topological_space_fiber VectorBundleCore.topologicalSpaceFiber
-/

instance addCommMonoidFiber : ∀ x : B, AddCommMonoid (Z.Fiber x) := by
  dsimp [VectorBundleCore.Fiber] <;> delta_instance fiber_bundle_core.fiber
#align vector_bundle_core.add_comm_monoid_fiber VectorBundleCore.addCommMonoidFiber

#print VectorBundleCore.moduleFiber /-
instance moduleFiber : ∀ x : B, Module R (Z.Fiber x) := by
  dsimp [VectorBundleCore.Fiber] <;> delta_instance fiber_bundle_core.fiber
#align vector_bundle_core.module_fiber VectorBundleCore.moduleFiber
-/

#print VectorBundleCore.addCommGroupFiber /-
instance addCommGroupFiber [AddCommGroup F] : ∀ x : B, AddCommGroup (Z.Fiber x) := by
  dsimp [VectorBundleCore.Fiber] <;> delta_instance fiber_bundle_core.fiber
#align vector_bundle_core.add_comm_group_fiber VectorBundleCore.addCommGroupFiber
-/

#print VectorBundleCore.proj /-
/-- The projection from the total space of a fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps]
protected def proj : TotalSpace F Z.Fiber → B :=
  TotalSpace.proj
#align vector_bundle_core.proj VectorBundleCore.proj
-/

#print VectorBundleCore.TotalSpace /-
/-- The total space of the vector bundle, as a convenience function for dot notation.
It is by definition equal to `bundle.total_space Z.fiber`. -/
@[nolint unused_arguments, reducible]
protected def TotalSpace :=
  Bundle.TotalSpace F Z.Fiber
#align vector_bundle_core.total_space VectorBundleCore.TotalSpace
-/

#print VectorBundleCore.trivChange /-
/-- Local homeomorphism version of the trivialization change. -/
def trivChange (i j : ι) : PartialHomeomorph (B × F) (B × F) :=
  FiberBundleCore.trivChange (↑Z) i j
#align vector_bundle_core.triv_change VectorBundleCore.trivChange
-/

#print VectorBundleCore.mem_trivChange_source /-
@[simp, mfld_simps]
theorem mem_trivChange_source (i j : ι) (p : B × F) :
    p ∈ (Z.trivChange i j).source ↔ p.1 ∈ Z.baseSet i ∩ Z.baseSet j :=
  FiberBundleCore.mem_trivChange_source (↑Z) i j p
#align vector_bundle_core.mem_triv_change_source VectorBundleCore.mem_trivChange_source
-/

#print VectorBundleCore.toTopologicalSpace /-
/-- Topological structure on the total space of a vector bundle created from core, designed so
that all the local trivialization are continuous. -/
instance toTopologicalSpace : TopologicalSpace Z.TotalSpace :=
  Z.toFiberBundleCore.toTopologicalSpace
#align vector_bundle_core.to_topological_space VectorBundleCore.toTopologicalSpace
-/

variable (b : B) (a : F)

#print VectorBundleCore.coe_coordChange /-
@[simp, mfld_simps]
theorem coe_coordChange (i j : ι) : Z.toFiberBundleCore.coordChange i j b = Z.coordChange i j b :=
  rfl
#align vector_bundle_core.coe_coord_change VectorBundleCore.coe_coordChange
-/

#print VectorBundleCore.localTriv /-
/-- One of the standard local trivializations of a vector bundle constructed from core, taken by
considering this in particular as a fiber bundle constructed from core. -/
def localTriv (i : ι) : Trivialization F (π F Z.Fiber) := by
  dsimp [VectorBundleCore.TotalSpace, VectorBundleCore.Fiber] <;>
    exact Z.to_fiber_bundle_core.local_triv i
#align vector_bundle_core.local_triv VectorBundleCore.localTriv
-/

#print VectorBundleCore.localTriv.isLinear /-
/-- The standard local trivializations of a vector bundle constructed from core are linear. -/
instance localTriv.isLinear (i : ι) : (Z.localTriv i).isLinear R
    where linear x hx := by
    dsimp [VectorBundleCore.localTriv] <;>
      exact
        { map_add := fun v w => by simp only [ContinuousLinearMap.map_add, mfld_simps]
          map_smul := fun r v => by simp only [ContinuousLinearMap.map_smul, mfld_simps] }
#align vector_bundle_core.local_triv.is_linear VectorBundleCore.localTriv.isLinear
-/

variable (i j : ι)

#print VectorBundleCore.mem_localTriv_source /-
@[simp, mfld_simps]
theorem mem_localTriv_source (p : Z.TotalSpace) : p ∈ (Z.localTriv i).source ↔ p.1 ∈ Z.baseSet i :=
  by dsimp [VectorBundleCore.Fiber] <;> exact Iff.rfl
#align vector_bundle_core.mem_local_triv_source VectorBundleCore.mem_localTriv_source
-/

#print VectorBundleCore.baseSet_at /-
@[simp, mfld_simps]
theorem baseSet_at : Z.baseSet i = (Z.localTriv i).baseSet :=
  rfl
#align vector_bundle_core.base_set_at VectorBundleCore.baseSet_at
-/

#print VectorBundleCore.localTriv_apply /-
@[simp, mfld_simps]
theorem localTriv_apply (p : Z.TotalSpace) :
    (Z.localTriv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl
#align vector_bundle_core.local_triv_apply VectorBundleCore.localTriv_apply
-/

#print VectorBundleCore.mem_localTriv_target /-
@[simp, mfld_simps]
theorem mem_localTriv_target (p : B × F) :
    p ∈ (Z.localTriv i).target ↔ p.1 ∈ (Z.localTriv i).baseSet :=
  Z.toFiberBundleCore.mem_localTriv_target i p
#align vector_bundle_core.mem_local_triv_target VectorBundleCore.mem_localTriv_target
-/

#print VectorBundleCore.localTriv_symm_fst /-
@[simp, mfld_simps]
theorem localTriv_symm_fst (p : B × F) :
    (Z.localTriv i).toPartialHomeomorph.symm p = ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩ :=
  rfl
#align vector_bundle_core.local_triv_symm_fst VectorBundleCore.localTriv_symm_fst
-/

#print VectorBundleCore.localTriv_symm_apply /-
@[simp, mfld_simps]
theorem localTriv_symm_apply {b : B} (hb : b ∈ Z.baseSet i) (v : F) :
    (Z.localTriv i).symm b v = Z.coordChange i (Z.indexAt b) b v := by
  apply (Z.local_triv i).symm_apply hb v
#align vector_bundle_core.local_triv_symm_apply VectorBundleCore.localTriv_symm_apply
-/

#print VectorBundleCore.localTriv_coordChange_eq /-
@[simp, mfld_simps]
theorem localTriv_coordChange_eq {b : B} (hb : b ∈ Z.baseSet i ∩ Z.baseSet j) (v : F) :
    (Z.localTriv i).coordChangeL R (Z.localTriv j) b v = Z.coordChange i j b v :=
  by
  rw [Trivialization.coordChangeL_apply', local_triv_symm_fst, local_triv_apply, coord_change_comp]
  exacts [⟨⟨hb.1, Z.mem_base_set_at b⟩, hb.2⟩, hb]
#align vector_bundle_core.local_triv_coord_change_eq VectorBundleCore.localTriv_coordChange_eq
-/

#print VectorBundleCore.localTrivAt /-
/-- Preferred local trivialization of a vector bundle constructed from core, at a given point, as
a bundle trivialization -/
def localTrivAt (b : B) : Trivialization F (π F Z.Fiber) :=
  Z.localTriv (Z.indexAt b)
#align vector_bundle_core.local_triv_at VectorBundleCore.localTrivAt
-/

#print VectorBundleCore.localTrivAt_def /-
@[simp, mfld_simps]
theorem localTrivAt_def : Z.localTriv (Z.indexAt b) = Z.localTrivAt b :=
  rfl
#align vector_bundle_core.local_triv_at_def VectorBundleCore.localTrivAt_def
-/

#print VectorBundleCore.mem_source_at /-
@[simp, mfld_simps]
theorem mem_source_at : (⟨b, a⟩ : Z.TotalSpace) ∈ (Z.localTrivAt b).source := by
  rw [local_triv_at, mem_local_triv_source]; exact Z.mem_base_set_at b
#align vector_bundle_core.mem_source_at VectorBundleCore.mem_source_at
-/

#print VectorBundleCore.localTrivAt_apply /-
@[simp, mfld_simps]
theorem localTrivAt_apply (p : Z.TotalSpace) : (Z.localTrivAt p.1) p = ⟨p.1, p.2⟩ :=
  FiberBundleCore.localTrivAt_apply Z p
#align vector_bundle_core.local_triv_at_apply VectorBundleCore.localTrivAt_apply
-/

#print VectorBundleCore.localTrivAt_apply_mk /-
@[simp, mfld_simps]
theorem localTrivAt_apply_mk (b : B) (a : F) : (Z.localTrivAt b) ⟨b, a⟩ = ⟨b, a⟩ :=
  Z.localTrivAt_apply _
#align vector_bundle_core.local_triv_at_apply_mk VectorBundleCore.localTrivAt_apply_mk
-/

#print VectorBundleCore.mem_localTrivAt_baseSet /-
@[simp, mfld_simps]
theorem mem_localTrivAt_baseSet : b ∈ (Z.localTrivAt b).baseSet :=
  FiberBundleCore.mem_localTrivAt_baseSet Z b
#align vector_bundle_core.mem_local_triv_at_base_set VectorBundleCore.mem_localTrivAt_baseSet
-/

#print VectorBundleCore.fiberBundle /-
instance fiberBundle : FiberBundle F Z.Fiber :=
  Z.toFiberBundleCore.FiberBundle
#align vector_bundle_core.fiber_bundle VectorBundleCore.fiberBundle
-/

#print VectorBundleCore.vectorBundle /-
instance vectorBundle : VectorBundle R F Z.Fiber
    where
  trivialization_linear' := by
    rintro _ ⟨i, rfl⟩
    apply local_triv.is_linear
  continuousOn_coord_change' := by
    rintro _ _ ⟨i, rfl⟩ ⟨i', rfl⟩
    refine' (Z.continuous_on_coord_change i i').congr fun b hb => _
    ext v
    exact Z.local_triv_coord_change_eq i i' hb v
#align vector_bundle_core.vector_bundle VectorBundleCore.vectorBundle
-/

#print VectorBundleCore.continuous_proj /-
/-- The projection on the base of a vector bundle created from core is continuous -/
@[continuity]
theorem continuous_proj : Continuous Z.proj :=
  FiberBundleCore.continuous_proj Z
#align vector_bundle_core.continuous_proj VectorBundleCore.continuous_proj
-/

#print VectorBundleCore.isOpenMap_proj /-
/-- The projection on the base of a vector bundle created from core is an open map -/
theorem isOpenMap_proj : IsOpenMap Z.proj :=
  FiberBundleCore.isOpenMap_proj Z
#align vector_bundle_core.is_open_map_proj VectorBundleCore.isOpenMap_proj
-/

variable {i j}

#print VectorBundleCore.localTriv_continuousLinearMapAt /-
@[simp, mfld_simps]
theorem localTriv_continuousLinearMapAt {b : B} (hb : b ∈ Z.baseSet i) :
    (Z.localTriv i).continuousLinearMapAt R b = Z.coordChange (Z.indexAt b) i b :=
  by
  ext1 v
  rw [(Z.local_triv i).continuousLinearMapAt_apply R, (Z.local_triv i).coe_linearMapAt_of_mem]
  exacts [rfl, hb]
#align vector_bundle_core.local_triv_continuous_linear_map_at VectorBundleCore.localTriv_continuousLinearMapAt
-/

#print VectorBundleCore.trivializationAt_continuousLinearMapAt /-
@[simp, mfld_simps]
theorem trivializationAt_continuousLinearMapAt {b₀ b : B}
    (hb : b ∈ (trivializationAt F Z.Fiber b₀).baseSet) :
    (trivializationAt F Z.Fiber b₀).continuousLinearMapAt R b =
      Z.coordChange (Z.indexAt b) (Z.indexAt b₀) b :=
  Z.localTriv_continuousLinearMapAt hb
#align vector_bundle_core.trivialization_at_continuous_linear_map_at VectorBundleCore.trivializationAt_continuousLinearMapAt
-/

#print VectorBundleCore.localTriv_symmL /-
@[simp, mfld_simps]
theorem localTriv_symmL {b : B} (hb : b ∈ Z.baseSet i) :
    (Z.localTriv i).symmL R b = Z.coordChange i (Z.indexAt b) b := by ext1 v;
  rw [(Z.local_triv i).symmL_apply R, (Z.local_triv i).symm_apply]; exacts [rfl, hb]
#align vector_bundle_core.local_triv_symmL VectorBundleCore.localTriv_symmL
-/

#print VectorBundleCore.trivializationAt_symmL /-
@[simp, mfld_simps]
theorem trivializationAt_symmL {b₀ b : B} (hb : b ∈ (trivializationAt F Z.Fiber b₀).baseSet) :
    (trivializationAt F Z.Fiber b₀).symmL R b = Z.coordChange (Z.indexAt b₀) (Z.indexAt b) b :=
  Z.localTriv_symmL hb
#align vector_bundle_core.trivialization_at_symmL VectorBundleCore.trivializationAt_symmL
-/

#print VectorBundleCore.trivializationAt_coordChange_eq /-
@[simp, mfld_simps]
theorem trivializationAt_coordChange_eq {b₀ b₁ b : B}
    (hb : b ∈ (trivializationAt F Z.Fiber b₀).baseSet ∩ (trivializationAt F Z.Fiber b₁).baseSet)
    (v : F) :
    (trivializationAt F Z.Fiber b₀).coordChangeL R (trivializationAt F Z.Fiber b₁) b v =
      Z.coordChange (Z.indexAt b₀) (Z.indexAt b₁) b v :=
  Z.localTriv_coordChange_eq _ _ hb v
#align vector_bundle_core.trivialization_at_coord_change_eq VectorBundleCore.trivializationAt_coordChange_eq
-/

end VectorBundleCore

end

/-! ### Vector prebundle -/


section

variable [NontriviallyNormedField R] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]
  [NormedAddCommGroup F] [NormedSpace R F] [TopologicalSpace B] [∀ x, TopologicalSpace (E x)]

open TopologicalSpace

open VectorBundle

#print VectorPrebundle /-
/- ./././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (e e' «expr ∈ » pretrivialization_atlas) -/
/-- This structure permits to define a vector bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space or the fibers.
The total space is hence given a topology in such a way that there is a fiber bundle structure for
which the local equivalences are also local homeomorphisms and hence vector bundle trivializations.
The topology on the fibers is induced from the one on the total space.

The field `exists_coord_change` is stated as an existential statement (instead of 3 separate
fields), since it depends on propositional information (namely `e e' ∈ pretrivialization_atlas`).
This makes it inconvenient to explicitly define a `coord_change` function when constructing a
`vector_prebundle`. -/
@[nolint has_nonempty_instance]
structure VectorPrebundle where
  pretrivializationAtlas : Set (Pretrivialization F (π F E))
  pretrivialization_linear' :
    ∀ (e : Pretrivialization F (π F E)) (he : e ∈ pretrivialization_atlas), e.isLinear R
  pretrivializationAt : B → Pretrivialization F (π F E)
  mem_base_pretrivializationAt : ∀ x : B, x ∈ (pretrivialization_at x).baseSet
  pretrivialization_mem_atlas : ∀ x : B, pretrivialization_at x ∈ pretrivialization_atlas
  exists_coord_change :
    ∀ (e) (_ : e ∈ pretrivialization_atlas) (e') (_ : e' ∈ pretrivialization_atlas),
      ∃ f : B → F →L[R] F,
        ContinuousOn f (e.baseSet ∩ e'.baseSet) ∧
          ∀ (b : B) (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : F), f b v = (e' ⟨b, e.symm b v⟩).2
  totalSpace_mk_inducing : ∀ b : B, Inducing (pretrivialization_at b ∘ TotalSpace.mk b)
#align vector_prebundle VectorPrebundle
-/

namespace VectorPrebundle

variable {R E F}

#print VectorPrebundle.coordChange /-
/-- A randomly chosen coordinate change on a `vector_prebundle`, given by
  the field `exists_coord_change`. -/
def coordChange (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
    (he : e ∈ a.pretrivializationAtlas) (he' : e' ∈ a.pretrivializationAtlas) (b : B) : F →L[R] F :=
  Classical.choose (a.exists_coord_change e he e' he') b
#align vector_prebundle.coord_change VectorPrebundle.coordChange
-/

#print VectorPrebundle.continuousOn_coordChange /-
theorem continuousOn_coordChange (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
    (he : e ∈ a.pretrivializationAtlas) (he' : e' ∈ a.pretrivializationAtlas) :
    ContinuousOn (a.coordChange he he') (e.baseSet ∩ e'.baseSet) :=
  (Classical.choose_spec (a.exists_coord_change e he e' he')).1
#align vector_prebundle.continuous_on_coord_change VectorPrebundle.continuousOn_coordChange
-/

#print VectorPrebundle.coordChange_apply /-
theorem coordChange_apply (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
    (he : e ∈ a.pretrivializationAtlas) (he' : e' ∈ a.pretrivializationAtlas) {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : F) : a.coordChange he he' b v = (e' ⟨b, e.symm b v⟩).2 :=
  (Classical.choose_spec (a.exists_coord_change e he e' he')).2 b hb v
#align vector_prebundle.coord_change_apply VectorPrebundle.coordChange_apply
-/

#print VectorPrebundle.mk_coordChange /-
theorem mk_coordChange (a : VectorPrebundle R F E) {e e' : Pretrivialization F (π F E)}
    (he : e ∈ a.pretrivializationAtlas) (he' : e' ∈ a.pretrivializationAtlas) {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : F) :
    (b, a.coordChange he he' b v) = e' ⟨b, e.symm b v⟩ :=
  by
  ext
  · rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]; exact hb.2
  · exact a.coord_change_apply he he' hb v
#align vector_prebundle.mk_coord_change VectorPrebundle.mk_coordChange
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print VectorPrebundle.toFiberPrebundle /-
/-- Natural identification of `vector_prebundle` as a `fiber_prebundle`. -/
def toFiberPrebundle (a : VectorPrebundle R F E) : FiberPrebundle F E :=
  { a with
    continuous_triv_change := by
      intro e he e' he'
      have :=
        is_bounded_bilinear_map_apply.continuous.comp_continuous_on
          ((a.continuous_on_coord_change he' he).Prod_map continuousOn_id)
      have H :
        e'.to_local_equiv.target ∩ e'.to_local_equiv.symm ⁻¹' e.to_local_equiv.source =
          (e'.base_set ∩ e.base_set) ×ˢ univ :=
        by
        rw [e'.target_eq, e.source_eq]
        ext ⟨b, f⟩
        simp (config := { contextual := true }) only [-total_space.proj, and_congr_right_iff,
          e'.proj_symm_apply', iff_self_iff, imp_true_iff, mfld_simps]
      rw [H]
      refine' (continuous_on_fst.prod this).congr _
      rintro ⟨b, f⟩ ⟨hb, -⟩
      dsimp only [Function.comp, Prod.map]
      rw [a.mk_coord_change _ _ hb, e'.mk_symm hb.1]
      rfl }
#align vector_prebundle.to_fiber_prebundle VectorPrebundle.toFiberPrebundle
-/

#print VectorPrebundle.totalSpaceTopology /-
/-- Topology on the total space that will make the prebundle into a bundle. -/
def totalSpaceTopology (a : VectorPrebundle R F E) : TopologicalSpace (TotalSpace F E) :=
  a.toFiberPrebundle.totalSpaceTopology
#align vector_prebundle.total_space_topology VectorPrebundle.totalSpaceTopology
-/

#print VectorPrebundle.trivializationOfMemPretrivializationAtlas /-
/-- Promotion from a `trivialization` in the `pretrivialization_atlas` of a
`vector_prebundle` to a `trivialization`. -/
def trivializationOfMemPretrivializationAtlas (a : VectorPrebundle R F E)
    {e : Pretrivialization F (π F E)} (he : e ∈ a.pretrivializationAtlas) :
    @Trivialization B F _ _ _ a.totalSpaceTopology (π F E) :=
  a.toFiberPrebundle.trivializationOfMemPretrivializationAtlas he
#align vector_prebundle.trivialization_of_mem_pretrivialization_atlas VectorPrebundle.trivializationOfMemPretrivializationAtlas
-/

#print VectorPrebundle.linear_trivializationOfMemPretrivializationAtlas /-
theorem linear_trivializationOfMemPretrivializationAtlas (a : VectorPrebundle R F E)
    {e : Pretrivialization F (π F E)} (he : e ∈ a.pretrivializationAtlas) :
    @Trivialization.IsLinear R B F _ _ _ _ a.totalSpaceTopology _ _ _ _
      (trivializationOfMemPretrivializationAtlas a he) :=
  { linear := (a.pretrivialization_linear' e he).linear }
#align vector_prebundle.linear_of_mem_pretrivialization_atlas VectorPrebundle.linear_trivializationOfMemPretrivializationAtlas
-/

variable (a : VectorPrebundle R F E)

#print VectorPrebundle.mem_trivialization_at_source /-
theorem mem_trivialization_at_source (b : B) (x : E b) :
    TotalSpace.mk b x ∈ (a.pretrivializationAt b).source :=
  a.toFiberPrebundle.mem_pretrivializationAt_source b x
#align vector_prebundle.mem_trivialization_at_source VectorPrebundle.mem_trivialization_at_source
-/

#print VectorPrebundle.totalSpaceMk_preimage_source /-
@[simp]
theorem totalSpaceMk_preimage_source (b : B) :
    TotalSpace.mk b ⁻¹' (a.pretrivializationAt b).source = univ :=
  a.toFiberPrebundle.totalSpaceMk_preimage_source b
#align vector_prebundle.total_space_mk_preimage_source VectorPrebundle.totalSpaceMk_preimage_source
-/

#print VectorPrebundle.continuous_totalSpaceMk /-
@[continuity]
theorem continuous_totalSpaceMk (b : B) :
    @Continuous _ _ _ a.totalSpaceTopology (TotalSpace.mk b) :=
  a.toFiberPrebundle.continuous_totalSpaceMk b
#align vector_prebundle.continuous_total_space_mk VectorPrebundle.continuous_totalSpaceMk
-/

#print VectorPrebundle.toFiberBundle /-
/-- Make a `fiber_bundle` from a `vector_prebundle`; auxiliary construction for
`vector_prebundle.vector_bundle`. -/
def toFiberBundle : @FiberBundle B F _ _ _ a.totalSpaceTopology _ :=
  a.toFiberPrebundle.toFiberBundle
#align vector_prebundle.to_fiber_bundle VectorPrebundle.toFiberBundle
-/

#print VectorPrebundle.toVectorBundle /-
/-- Make a `vector_bundle` from a `vector_prebundle`.  Concretely this means
that, given a `vector_prebundle` structure for a sigma-type `E` -- which consists of a
number of "pretrivializations" identifying parts of `E` with product spaces `U × F` -- one
establishes that for the topology constructed on the sigma-type using
`vector_prebundle.total_space_topology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology). -/
theorem toVectorBundle : @VectorBundle R _ F E _ _ _ _ _ _ a.totalSpaceTopology _ a.toFiberBundle :=
  { trivialization_linear' := by
      rintro _ ⟨e, he, rfl⟩
      apply linear_of_mem_pretrivialization_atlas
    continuousOn_coord_change' :=
      by
      rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
      refine' (a.continuous_on_coord_change he he').congr _
      intro b hb
      ext v
      rw [a.coord_change_apply he he' hb v, ContinuousLinearEquiv.coe_coe,
        Trivialization.coordChangeL_apply]
      exacts [rfl, hb] }
#align vector_prebundle.to_vector_bundle VectorPrebundle.toVectorBundle
-/

end VectorPrebundle

namespace ContinuousLinearMap

variable {𝕜₁ 𝕜₂ : Type _} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]

variable {σ : 𝕜₁ →+* 𝕜₂}

variable {B' : Type _} [TopologicalSpace B']

variable [NormedSpace 𝕜₁ F] [∀ x, Module 𝕜₁ (E x)] [TopologicalSpace (TotalSpace F E)]

variable {F' : Type _} [NormedAddCommGroup F'] [NormedSpace 𝕜₂ F'] {E' : B' → Type _}
  [∀ x, AddCommMonoid (E' x)] [∀ x, Module 𝕜₂ (E' x)] [TopologicalSpace (TotalSpace F' E')]

variable [FiberBundle F E] [VectorBundle 𝕜₁ F E]

variable [∀ x, TopologicalSpace (E' x)] [FiberBundle F' E'] [VectorBundle 𝕜₂ F' E']

variable (F E F' E')

#print ContinuousLinearMap.inCoordinates /-
/-- When `ϕ` is a continuous (semi)linear map between the fibers `E x` and `E' y` of two vector
bundles `E` and `E'`, `continuous_linear_map.in_coordinates F E F' E' x₀ x y₀ y ϕ` is a coordinate
change of this continuous linear map w.r.t. the chart around `x₀` and the chart around `y₀`.

It is defined by composing `ϕ` with appropriate coordinate changes given by the vector bundles
`E` and `E'`.
We use the operations `trivialization.continuous_linear_map_at` and `trivialization.symmL` in the
definition, instead of `trivialization.continuous_linear_equiv_at`, so that
`continuous_linear_map.in_coordinates` is defined everywhere (but see
`continuous_linear_map.in_coordinates_eq`).

This is the (second component of the) underlying function of a trivialization of the hom-bundle
(see `hom_trivialization_at_apply`). However, note that `continuous_linear_map.in_coordinates` is
defined even when `x` and `y` live in different base sets.
Therefore, it is is also convenient when working with the hom-bundle between pulled back bundles.
-/
def inCoordinates (x₀ x : B) (y₀ y : B') (ϕ : E x →SL[σ] E' y) : F →SL[σ] F' :=
  ((trivializationAt F' E' y₀).continuousLinearMapAt 𝕜₂ y).comp <|
    ϕ.comp <| (trivializationAt F E x₀).symmL 𝕜₁ x
#align continuous_linear_map.in_coordinates ContinuousLinearMap.inCoordinates
-/

variable {F F'}

#print ContinuousLinearMap.inCoordinates_eq /-
/-- rewrite `in_coordinates` using continuous linear equivalences. -/
theorem inCoordinates_eq (x₀ x : B) (y₀ y : B') (ϕ : E x →SL[σ] E' y)
    (hx : x ∈ (trivializationAt F E x₀).baseSet) (hy : y ∈ (trivializationAt F' E' y₀).baseSet) :
    inCoordinates F E F' E' x₀ x y₀ y ϕ =
      ((trivializationAt F' E' y₀).continuousLinearEquivAt 𝕜₂ y hy : E' y →L[𝕜₂] F').comp
        (ϕ.comp <|
          (((trivializationAt F E x₀).continuousLinearEquivAt 𝕜₁ x hx).symm : F →L[𝕜₁] E x)) :=
  by
  ext
  simp_rw [in_coordinates, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
    Trivialization.coe_continuousLinearEquivAt_eq, Trivialization.symm_continuousLinearEquivAt_eq]
#align continuous_linear_map.in_coordinates_eq ContinuousLinearMap.inCoordinates_eq
-/

#print VectorBundleCore.inCoordinates_eq /-
/-- rewrite `in_coordinates` in a `vector_bundle_core`. -/
protected theorem VectorBundleCore.inCoordinates_eq {ι ι'} (Z : VectorBundleCore 𝕜₁ B F ι)
    (Z' : VectorBundleCore 𝕜₂ B' F' ι') {x₀ x : B} {y₀ y : B'} (ϕ : F →SL[σ] F')
    (hx : x ∈ Z.baseSet (Z.indexAt x₀)) (hy : y ∈ Z'.baseSet (Z'.indexAt y₀)) :
    inCoordinates F Z.Fiber F' Z'.Fiber x₀ x y₀ y ϕ =
      (Z'.coordChange (Z'.indexAt y) (Z'.indexAt y₀) y).comp
        (ϕ.comp <| Z.coordChange (Z.indexAt x₀) (Z.indexAt x) x) :=
  by
  simp_rw [in_coordinates, Z'.trivialization_at_continuous_linear_map_at hy,
    Z.trivialization_at_symmL hx]
#align continuous_linear_map.vector_bundle_core.in_coordinates_eq VectorBundleCore.inCoordinates_eq
-/

end ContinuousLinearMap

end

