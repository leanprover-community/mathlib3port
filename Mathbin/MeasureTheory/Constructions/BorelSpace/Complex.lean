/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.constructions.borel_space.complex
! leanprover-community/mathlib commit bf6a01357ff5684b1ebcd0f1a13be314fc82c0bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Complex.Basic
import Mathbin.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Equip `ℂ` with the Borel sigma-algebra -/


noncomputable section

#print IsROrC.measurableSpace /-
instance (priority := 900) IsROrC.measurableSpace {𝕜 : Type _} [IsROrC 𝕜] : MeasurableSpace 𝕜 :=
  borel 𝕜
#align is_R_or_C.measurable_space IsROrC.measurableSpace
-/

#print IsROrC.borelSpace /-
instance (priority := 900) IsROrC.borelSpace {𝕜 : Type _} [IsROrC 𝕜] : BorelSpace 𝕜 :=
  ⟨rfl⟩
#align is_R_or_C.borel_space IsROrC.borelSpace
-/

#print Complex.measurableSpace /-
instance Complex.measurableSpace : MeasurableSpace ℂ :=
  borel ℂ
#align complex.measurable_space Complex.measurableSpace
-/

/- warning: complex.borel_space -> Complex.borelSpace is a dubious translation:
lean 3 declaration is
  BorelSpace.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) Complex.measurableSpace
but is expected to have type
  BorelSpace.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) Complex.measurableSpace
Case conversion may be inaccurate. Consider using '#align complex.borel_space Complex.borelSpaceₓ'. -/
instance Complex.borelSpace : BorelSpace ℂ :=
  ⟨rfl⟩
#align complex.borel_space Complex.borelSpace

