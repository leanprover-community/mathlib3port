/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.Algebra.Homology.HomologicalComplex
import Mathbin.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotent completeness and homological complexes

This file contains simplifications lemmas for categories
`karoubi (homological_complex C c)`.

TODO @joelriou : Get an equivalence of categories
`karoubi (homological_complex C c) ≌ homological_complex (karoubi C) c`
for all preadditive categories `C` and complex shape `c`.

-/


namespace CategoryTheory

variable {C : Type _} [Category C] [Preadditive C] {ι : Type _} {c : ComplexShape ι}

namespace Idempotents

namespace Karoubi

namespace HomologicalComplex

variable {P Q : Karoubi (HomologicalComplex C c)} (f : P ⟶ Q) (n : ι)

@[simp, reassoc]
theorem p_comp_d : P.p.f n ≫ f.f.f n = f.f.f n :=
  HomologicalComplex.congr_hom (p_comp f) n

@[simp, reassoc]
theorem comp_p_d : f.f.f n ≫ Q.p.f n = f.f.f n :=
  HomologicalComplex.congr_hom (comp_p f) n

@[reassoc]
theorem p_comm_f : P.p.f n ≫ f.f.f n = f.f.f n ≫ Q.p.f n :=
  HomologicalComplex.congr_hom (p_comm f) n

end HomologicalComplex

end Karoubi

end Idempotents

end CategoryTheory

