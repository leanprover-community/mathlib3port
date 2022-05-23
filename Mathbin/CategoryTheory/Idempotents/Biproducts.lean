/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.CategoryTheory.Idempotents.Karoubi
import Mathbin.CategoryTheory.Additive.Basic

/-!

# Biproducts in the idempotent completion of a preadditive category

In this file, we define an instance expressing that if `C` is an additive category,
then `karoubi C` is also an additive category.

We also obtain that for all `P : karoubi C` where `C` is a preadditive category `C`, there
is a canonical isomorphism `P ⊞ P.complement ≅ (to_karoubi C).obj P.X` in the category
`karoubi C` where `P.complement` is the formal direct factor of `P.X` corresponding to
the idempotent endomorphism `𝟙 P.X - P.p`.

-/


noncomputable section

open CategoryTheory.Category

open CategoryTheory.Limits

open CategoryTheory.Preadditive

universe v

namespace CategoryTheory

namespace Idempotents

namespace Karoubi

variable {C : Type _} [Category.{v} C] [Preadditive C]

namespace Biproducts

/-- The `bicone` used in order to obtain the existence of
the biproduct of a functor `J ⥤ karoubi C` when the category `C` is additive. -/
@[simps]
def bicone [HasFiniteBiproducts C] {J : Type v} [Fintype J] (F : J → Karoubi C) : Bicone F where
  x :=
    { x := biproduct fun j => (F j).x, p := biproduct.map fun j => (F j).p,
      idem := by
        ext j
        simp only [biproduct.ι_map_assoc, biproduct.ι_map]
        slice_lhs 1 2 => rw [(F j).idem] }
  π := fun j =>
    { f := (biproduct.map fun j => (F j).p) ≫ Bicone.π _ j,
      comm := by
        simp only [assoc, biproduct.bicone_π, biproduct.map_π, biproduct.map_π_assoc, (F j).idem] }
  ι := fun j =>
    { f := bicone.ι _ j ≫ biproduct.map fun j => (F j).p,
      comm := by
        rw [biproduct.ι_map, ← assoc, ← assoc, (F j).idem, assoc, biproduct.ι_map, ← assoc, (F j).idem] }
  ι_π := fun j j' => by
    split_ifs
    · subst h
      simp only [biproduct.bicone_ι, biproduct.ι_map, biproduct.bicone_π, biproduct.ι_π_self_assoc, comp,
        category.assoc, eq_to_hom_refl, id_eq, biproduct.map_π, (F j).idem]
      
    · simpa only [hom_ext, biproduct.ι_π_ne_assoc _ h, assoc, biproduct.map_π, biproduct.map_π_assoc, zero_comp, comp]
      

end Biproducts

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
theorem karoubi_has_finite_biproducts [HasFiniteBiproducts C] : HasFiniteBiproducts (Karoubi C) :=
  { HasBiproductsOfShape := fun J hJ =>
      { HasBiproduct := fun F => by
          classical
          let this := hJ
          apply has_biproduct_of_total (biproducts.bicone F)
          ext1
          ext1
          simp only [id_eq, comp_id, biproducts.bicone_X_p, biproduct.ι_map]
          rw [sum_hom, comp_sum, Finset.sum_eq_single j]
          rotate_left
          · intro j' h1 h2
            simp only [biproduct.ι_map, biproducts.bicone_ι_f, biproducts.bicone_π_f, assoc, comp, biproduct.map_π]
            slice_lhs 1 2 => rw [biproduct.ι_π]
            split_ifs
            · exfalso
              exact h2 h.symm
              
            · simp only [zero_comp]
              
            
          · intro h
            exfalso
            simpa only [Finset.mem_univ, not_true] using h
            
          · simp only [biproducts.bicone_π_f, comp, biproduct.ι_map, assoc, biproducts.bicone_ι_f, biproduct.map_π]
            slice_lhs 1 2 => rw [biproduct.ι_π]
            split_ifs
            swap
            · exfalso
              exact h rfl
              
            simp only [eq_to_hom_refl, id_comp, (F j).idem]
             } }

instance {D : Type _} [Category D] [AdditiveCategory D] : AdditiveCategory (Karoubi D) where
  toPreadditive := inferInstance
  to_has_finite_biproducts := karoubi_has_finite_biproducts

/-- `P.complement` is the formal direct factor of `P.X` given by the idempotent
endomorphism `𝟙 P.X - P.p` -/
@[simps]
def complement (P : Karoubi C) : Karoubi C where
  x := P.x
  p := 𝟙 _ - P.p
  idem := idem_of_id_sub_idem P.p P.idem

instance (P : Karoubi C) : HasBinaryBiproduct P P.complement :=
  has_binary_biproduct_of_total
    { x := P.x, fst := P.decompIdP, snd := P.complement.decompIdP, inl := P.decompIdI, inr := P.complement.decompIdI,
      inl_fst' := P.decomp_id.symm,
      inl_snd' := by
        simp only [decomp_id_i_f, decomp_id_p_f, complement_p, comp_sub, comp, hom_ext,
          quiver.hom.add_comm_group_zero_f, P.idem]
        erw [comp_id, sub_self],
      inr_fst' := by
        simp only [decomp_id_i_f, complement_p, decomp_id_p_f, sub_comp, comp, hom_ext,
          quiver.hom.add_comm_group_zero_f, P.idem]
        erw [id_comp, sub_self],
      inr_snd' := P.complement.decomp_id.symm }
    (by
      simp only [hom_ext, ← decomp_p, quiver.hom.add_comm_group_add_f, to_karoubi_map_f, id_eq, coe_p, complement_p,
        add_sub_cancel'_right])

/-- A formal direct factor `P : karoubi C` of an object `P.X : C` in a
preadditive category is actually a direct factor of the image `(to_karoubi C).obj P.X`
of `P.X` in the category `karoubi C` -/
def decomposition (P : Karoubi C) : P ⊞ P.complement ≅ (toKaroubi _).obj P.x where
  Hom := biprod.desc P.decompIdI P.complement.decompIdI
  inv := biprod.lift P.decompIdP P.complement.decompIdP
  hom_inv_id' := by
    ext1
    · simp only [← assoc, biprod.inl_desc, comp_id, biprod.lift_eq, comp_add, ← decomp_id, id_comp, add_right_eq_selfₓ]
      convert zero_comp
      ext
      simp only [decomp_id_i_f, decomp_id_p_f, complement_p, comp_sub, comp, quiver.hom.add_comm_group_zero_f, P.idem]
      erw [comp_id, sub_self]
      
    · simp only [← assoc, biprod.inr_desc, biprod.lift_eq, comp_add, ← decomp_id, comp_id, id_comp, add_left_eq_self]
      convert zero_comp
      ext
      simp only [decomp_id_i_f, decomp_id_p_f, complement_p, sub_comp, comp, quiver.hom.add_comm_group_zero_f, P.idem]
      erw [id_comp, sub_self]
      
  inv_hom_id' := by
    rw [biprod.lift_desc]
    simp only [← decomp_p]
    ext
    dsimp' only [complement, to_karoubi]
    simp only [quiver.hom.add_comm_group_add_f, add_sub_cancel'_right, id_eq]

end Karoubi

end Idempotents

end CategoryTheory

