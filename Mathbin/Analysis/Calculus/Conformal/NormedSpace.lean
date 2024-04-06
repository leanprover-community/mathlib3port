/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import Analysis.NormedSpace.ConformalLinearMap
import Analysis.Calculus.FDeriv.Add
import Analysis.Calculus.FDeriv.Mul
import Analysis.Calculus.FDeriv.Equiv
import Analysis.Calculus.FDeriv.RestrictScalars

#align_import analysis.calculus.conformal.normed_space from "leanprover-community/mathlib"@"0b7c740e25651db0ba63648fbae9f9d6f941e31b"

/-!
# Conformal Maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A continuous linear map between real normed spaces `X` and `Y` is `conformal_at` some point `x`
if it is real differentiable at that point and its differential `is_conformal_linear_map`.

## Main definitions

* `conformal_at`: the main definition of conformal maps
* `conformal`: maps that are conformal at every point
* `conformal_factor_at`: the conformal factor of a conformal map at some point

## Main results
* The conformality of the composition of two conformal maps, the identity map
  and multiplications by nonzero constants
* `conformal_at_iff_is_conformal_map_fderiv`: an equivalent definition of the conformality of a map

In `analysis.calculus.conformal.inner_product`:
* `conformal_at_iff`: an equivalent definition of the conformality of a map

In `geometry.euclidean.angle.unoriented.conformal`:
* `conformal_at.preserves_angle`: if a map is conformal at `x`, then its differential
                                  preserves all angles at `x`

## Tags

conformal

## Warning

The definition of conformality in this file does NOT require the maps to be orientation-preserving.
Maps such as the complex conjugate are considered to be conformal.
-/


noncomputable section

variable {X Y Z : Type _} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
  [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ Z]

section LocConformality

open LinearIsometry ContinuousLinearMap

#print ConformalAt /-
/-- A map `f` is said to be conformal if it has a conformal differential `f'`. -/
def ConformalAt (f : X → Y) (x : X) :=
  ∃ f' : X →L[ℝ] Y, HasFDerivAt f f' x ∧ IsConformalMap f'
#align conformal_at ConformalAt
-/

#print conformalAt_id /-
theorem conformalAt_id (x : X) : ConformalAt id x :=
  ⟨id ℝ X, hasFDerivAt_id _, isConformalMap_id⟩
#align conformal_at_id conformalAt_id
-/

#print conformalAt_const_smul /-
theorem conformalAt_const_smul {c : ℝ} (h : c ≠ 0) (x : X) : ConformalAt (fun x' : X => c • x') x :=
  ⟨c • ContinuousLinearMap.id ℝ X, (hasFDerivAt_id x).const_smul c, isConformalMap_const_smul h⟩
#align conformal_at_const_smul conformalAt_const_smul
-/

#print Subsingleton.conformalAt /-
@[nontriviality]
theorem Subsingleton.conformalAt [Subsingleton X] (f : X → Y) (x : X) : ConformalAt f x :=
  ⟨0, hasFDerivAt_of_subsingleton _ _, isConformalMap_of_subsingleton _⟩
#align subsingleton.conformal_at Subsingleton.conformalAt
-/

#print conformalAt_iff_isConformalMap_fderiv /-
/-- A function is a conformal map if and only if its differential is a conformal linear map-/
theorem conformalAt_iff_isConformalMap_fderiv {f : X → Y} {x : X} :
    ConformalAt f x ↔ IsConformalMap (fderiv ℝ f x) :=
  by
  constructor
  · rintro ⟨f', hf, hf'⟩
    rwa [hf.fderiv]
  · intro H
    by_cases h : DifferentiableAt ℝ f x
    · exact ⟨fderiv ℝ f x, h.has_fderiv_at, H⟩
    · nontriviality X
      exact absurd (fderiv_zero_of_not_differentiableAt h) H.ne_zero
#align conformal_at_iff_is_conformal_map_fderiv conformalAt_iff_isConformalMap_fderiv
-/

namespace ConformalAt

#print ConformalAt.differentiableAt /-
theorem differentiableAt {f : X → Y} {x : X} (h : ConformalAt f x) : DifferentiableAt ℝ f x :=
  let ⟨_, h₁, _⟩ := h
  h₁.DifferentiableAt
#align conformal_at.differentiable_at ConformalAt.differentiableAt
-/

#print ConformalAt.congr /-
theorem congr {f g : X → Y} {x : X} {u : Set X} (hx : x ∈ u) (hu : IsOpen u) (hf : ConformalAt f x)
    (h : ∀ x : X, x ∈ u → g x = f x) : ConformalAt g x :=
  let ⟨f', hfderiv, hf'⟩ := hf
  ⟨f', hfderiv.congr_of_eventuallyEq ((hu.eventually_mem hx).mono h), hf'⟩
#align conformal_at.congr ConformalAt.congr
-/

#print ConformalAt.comp /-
theorem comp {f : X → Y} {g : Y → Z} (x : X) (hg : ConformalAt g (f x)) (hf : ConformalAt f x) :
    ConformalAt (g ∘ f) x := by
  rcases hf with ⟨f', hf₁, cf⟩
  rcases hg with ⟨g', hg₁, cg⟩
  exact ⟨g'.comp f', hg₁.comp x hf₁, cg.comp cf⟩
#align conformal_at.comp ConformalAt.comp
-/

#print ConformalAt.const_smul /-
theorem const_smul {f : X → Y} {x : X} {c : ℝ} (hc : c ≠ 0) (hf : ConformalAt f x) :
    ConformalAt (c • f) x :=
  (conformalAt_const_smul hc <| f x).comp x hf
#align conformal_at.const_smul ConformalAt.const_smul
-/

end ConformalAt

end LocConformality

section GlobalConformality

#print Conformal /-
/-- A map `f` is conformal if it's conformal at every point. -/
def Conformal (f : X → Y) :=
  ∀ x : X, ConformalAt f x
#align conformal Conformal
-/

#print conformal_id /-
theorem conformal_id : Conformal (id : X → X) := fun x => conformalAt_id x
#align conformal_id conformal_id
-/

#print conformal_const_smul /-
theorem conformal_const_smul {c : ℝ} (h : c ≠ 0) : Conformal fun x : X => c • x := fun x =>
  conformalAt_const_smul h x
#align conformal_const_smul conformal_const_smul
-/

namespace Conformal

#print Conformal.conformalAt /-
theorem conformalAt {f : X → Y} (h : Conformal f) (x : X) : ConformalAt f x :=
  h x
#align conformal.conformal_at Conformal.conformalAt
-/

#print Conformal.differentiable /-
theorem differentiable {f : X → Y} (h : Conformal f) : Differentiable ℝ f := fun x =>
  (h x).DifferentiableAt
#align conformal.differentiable Conformal.differentiable
-/

#print Conformal.comp /-
theorem comp {f : X → Y} {g : Y → Z} (hf : Conformal f) (hg : Conformal g) : Conformal (g ∘ f) :=
  fun x => (hg <| f x).comp x (hf x)
#align conformal.comp Conformal.comp
-/

#print Conformal.const_smul /-
theorem const_smul {f : X → Y} (hf : Conformal f) {c : ℝ} (hc : c ≠ 0) : Conformal (c • f) :=
  fun x => (hf x).const_smul hc
#align conformal.const_smul Conformal.const_smul
-/

end Conformal

end GlobalConformality

