/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.Complex.Basic
import Mathbin.MeasureTheory.Constructions.BorelSpace.Basic

#align_import measure_theory.constructions.borel_space.complex from "leanprover-community/mathlib"@"4280f5f32e16755ec7985ce11e189b6cd6ff6735"

/-! # Equip `ℂ` with the Borel sigma-algebra 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/


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

#print Complex.borelSpace /-
instance Complex.borelSpace : BorelSpace ℂ :=
  ⟨rfl⟩
#align complex.borel_space Complex.borelSpace
-/

