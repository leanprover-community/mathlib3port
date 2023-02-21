/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module category_theory.idempotents.homological_complex
! leanprover-community/mathlib commit 31019c2504b17f85af7e0577585fad996935a317
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Homology.HomologicalComplex
import Mathbin.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotent completeness and homological complexes

This file contains simplifications lemmas for categories
`karoubi (homological_complex C c)` and the construction of an equivalence
of categories `karoubi (homological_complex C c) ≌ homological_complex (karoubi C) c`.

-/


namespace CategoryTheory

open Category

variable {C : Type _} [Category C] [Preadditive C] {ι : Type _} {c : ComplexShape ι}

namespace Idempotents

namespace Karoubi

namespace HomologicalComplex

variable {P Q : Karoubi (HomologicalComplex C c)} (f : P ⟶ Q) (n : ι)

@[simp, reassoc.1]
theorem p_comp_d : P.p.f n ≫ f.f.f n = f.f.f n :=
  HomologicalComplex.congr_hom (p_comp f) n
#align category_theory.idempotents.karoubi.homological_complex.p_comp_d CategoryTheory.Idempotents.Karoubi.HomologicalComplex.p_comp_d

@[simp, reassoc.1]
theorem comp_p_d : f.f.f n ≫ Q.p.f n = f.f.f n :=
  HomologicalComplex.congr_hom (comp_p f) n
#align category_theory.idempotents.karoubi.homological_complex.comp_p_d CategoryTheory.Idempotents.Karoubi.HomologicalComplex.comp_p_d

@[reassoc.1]
theorem p_comm_f : P.p.f n ≫ f.f.f n = f.f.f n ≫ Q.p.f n :=
  HomologicalComplex.congr_hom (p_comm f) n
#align category_theory.idempotents.karoubi.homological_complex.p_comm_f CategoryTheory.Idempotents.Karoubi.HomologicalComplex.p_comm_f

variable (P)

@[simp, reassoc.1]
theorem p_idem : P.p.f n ≫ P.p.f n = P.p.f n :=
  HomologicalComplex.congr_hom P.idem n
#align category_theory.idempotents.karoubi.homological_complex.p_idem CategoryTheory.Idempotents.Karoubi.HomologicalComplex.p_idem

end HomologicalComplex

end Karoubi

open Karoubi

namespace KaroubiHomologicalComplexEquivalence

namespace Functor

/-- The functor `karoubi (homological_complex C c) ⥤ homological_complex (karoubi C) c`,
on objects. -/
@[simps]
def obj (P : Karoubi (HomologicalComplex C c)) : HomologicalComplex (Karoubi C) c
    where
  x n :=
    ⟨P.x.x n, P.p.f n, by
      simpa only [HomologicalComplex.comp_f] using HomologicalComplex.congr_hom P.idem n⟩
  d i j :=
    { f := P.p.f i ≫ P.x.d i j
      comm := by tidy }
  shape' i j hij := by simp only [hom_eq_zero_iff, P.X.shape i j hij, limits.comp_zero]
#align category_theory.idempotents.karoubi_homological_complex_equivalence.functor.obj CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Functor.obj

/-- The functor `karoubi (homological_complex C c) ⥤ homological_complex (karoubi C) c`,
on morphisms. -/
@[simps]
def map {P Q : Karoubi (HomologicalComplex C c)} (f : P ⟶ Q) : obj P ⟶ obj Q
    where f n :=
    { f := f.f.f n
      comm := by simp }
#align category_theory.idempotents.karoubi_homological_complex_equivalence.functor.map CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Functor.map

end Functor

/-- The functor `karoubi (homological_complex C c) ⥤ homological_complex (karoubi C) c`. -/
@[simps]
def functor : Karoubi (HomologicalComplex C c) ⥤ HomologicalComplex (Karoubi C) c
    where
  obj := Functor.obj
  map P Q f := Functor.map f
#align category_theory.idempotents.karoubi_homological_complex_equivalence.functor CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.functor

namespace Inverse

/-- The functor `homological_complex (karoubi C) c ⥤ karoubi (homological_complex C c)`,
on objects -/
@[simps]
def obj (K : HomologicalComplex (Karoubi C) c) : Karoubi (HomologicalComplex C c)
    where
  x :=
    { x := fun n => (K.x n).x
      d := fun i j => (K.d i j).f
      shape' := fun i j hij => hom_eq_zero_iff.mp (K.shape i j hij)
      d_comp_d' := fun i j k hij hjk => by
        simpa only [comp_f] using hom_eq_zero_iff.mp (K.d_comp_d i j k) }
  p :=
    { f := fun n => (K.x n).p
      comm' := by simp }
  idem := by tidy
#align category_theory.idempotents.karoubi_homological_complex_equivalence.inverse.obj CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Inverse.obj

/-- The functor `homological_complex (karoubi C) c ⥤ karoubi (homological_complex C c)`,
on morphisms -/
@[simps]
def map {K L : HomologicalComplex (Karoubi C) c} (f : K ⟶ L) : obj K ⟶ obj L
    where
  f :=
    { f := fun n => (f.f n).f
      comm' := fun i j hij => by simpa only [comp_f] using hom_ext.mp (f.comm' i j hij) }
  comm := by tidy
#align category_theory.idempotents.karoubi_homological_complex_equivalence.inverse.map CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Inverse.map

end Inverse

/-- The functor `homological_complex (karoubi C) c ⥤ karoubi (homological_complex C c)`. -/
@[simps]
def inverse : HomologicalComplex (Karoubi C) c ⥤ Karoubi (HomologicalComplex C c)
    where
  obj := Inverse.obj
  map K L f := Inverse.map f
#align category_theory.idempotents.karoubi_homological_complex_equivalence.inverse CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.inverse

/-- The counit isomorphism of the equivalence
`karoubi (homological_complex C c) ≌ homological_complex (karoubi C) c`. -/
@[simps]
def counitIso : inverse ⋙ functor ≅ 𝟭 (HomologicalComplex (Karoubi C) c) :=
  eqToIso (Functor.ext (fun P => HomologicalComplex.ext (by tidy) (by tidy)) (by tidy))
#align category_theory.idempotents.karoubi_homological_complex_equivalence.counit_iso CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.counitIso

/-- The unit isomorphism of the equivalence
`karoubi (homological_complex C c) ≌ homological_complex (karoubi C) c`. -/
@[simps]
def unitIso : 𝟭 (Karoubi (HomologicalComplex C c)) ≅ functor ⋙ inverse
    where
  Hom :=
    { app := fun P =>
        { f :=
            { f := fun n => P.p.f n
              comm' := fun i j hij => by
                dsimp
                simp only [HomologicalComplex.Hom.comm, HomologicalComplex.Hom.comm_assoc,
                  homological_complex.p_idem] }
          comm := by
            ext n
            dsimp
            simp only [homological_complex.p_idem] }
      naturality' := fun P Q φ => by
        ext
        dsimp
        simp only [comp_f, HomologicalComplex.comp_f, homological_complex.comp_p_d, inverse.map_f_f,
          functor.map_f_f, homological_complex.p_comp_d] }
  inv :=
    { app := fun P =>
        { f :=
            { f := fun n => P.p.f n
              comm' := fun i j hij => by
                dsimp
                simp only [HomologicalComplex.Hom.comm, assoc, homological_complex.p_idem] }
          comm := by
            ext n
            dsimp
            simp only [homological_complex.p_idem] }
      naturality' := fun P Q φ => by
        ext
        dsimp
        simp only [comp_f, HomologicalComplex.comp_f, inverse.map_f_f, functor.map_f_f,
          homological_complex.comp_p_d, homological_complex.p_comp_d] }
  hom_inv_id' := by
    ext
    dsimp
    simp only [homological_complex.p_idem, comp_f, HomologicalComplex.comp_f, id_eq]
  inv_hom_id' := by
    ext
    dsimp
    simp only [homological_complex.p_idem, comp_f, HomologicalComplex.comp_f, id_eq,
      inverse.obj_p_f, functor.obj_X_p]
#align category_theory.idempotents.karoubi_homological_complex_equivalence.unit_iso CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.unitIso

end KaroubiHomologicalComplexEquivalence

variable (C) (c)

/-- The equivalence `karoubi (homological_complex C c) ≌ homological_complex (karoubi C) c`. -/
@[simps]
def karoubiHomologicalComplexEquivalence :
    Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi C) c
    where
  Functor := KaroubiHomologicalComplexEquivalence.functor
  inverse := KaroubiHomologicalComplexEquivalence.inverse
  unitIso := KaroubiHomologicalComplexEquivalence.unitIso
  counitIso := KaroubiHomologicalComplexEquivalence.counitIso
#align category_theory.idempotents.karoubi_homological_complex_equivalence CategoryTheory.Idempotents.karoubiHomologicalComplexEquivalence

variable (α : Type _) [AddRightCancelSemigroup α] [One α]

/-- The equivalence `karoubi (chain_complex C α) ≌ chain_complex (karoubi C) α`. -/
@[simps]
def karoubiChainComplexEquivalence : Karoubi (ChainComplex C α) ≌ ChainComplex (Karoubi C) α :=
  karoubiHomologicalComplexEquivalence C (ComplexShape.down α)
#align category_theory.idempotents.karoubi_chain_complex_equivalence CategoryTheory.Idempotents.karoubiChainComplexEquivalence

/-- The equivalence `karoubi (cochain_complex C α) ≌ cochain_complex (karoubi C) α`. -/
@[simps]
def karoubiCochainComplexEquivalence :
    Karoubi (CochainComplex C α) ≌ CochainComplex (Karoubi C) α :=
  karoubiHomologicalComplexEquivalence C (ComplexShape.up α)
#align category_theory.idempotents.karoubi_cochain_complex_equivalence CategoryTheory.Idempotents.karoubiCochainComplexEquivalence

end Idempotents

end CategoryTheory

