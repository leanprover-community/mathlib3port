import Mathbin.CategoryTheory.Adjunction.Basic 
import Mathbin.CategoryTheory.Conj 
import Mathbin.CategoryTheory.Yoneda

/-!
# Adjoints of fully faithful functors

A left adjoint is fully faithful, if and only if the unit is an isomorphism
(and similarly for right adjoints and the counit).

`adjunction.restrict_fully_faithful` shows that an adjunction can be restricted along fully faithful
inclusions.

## Future work

The statements from Riehl 4.5.13 for adjoints which are either full, or faithful.
-/


open CategoryTheory

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

open Category

open Opposite

variable{C : Type u₁}[category.{v₁} C]

variable{D : Type u₂}[category.{v₂} D]

variable{L : C ⥤ D}{R : D ⥤ C}(h : L ⊣ R)

/--
If the left adjoint is fully faithful, then the unit is an isomorphism.

See
* Lemma 4.5.13 from [Riehl][riehl2017]
* https://math.stackexchange.com/a/2727177
* https://stacks.math.columbia.edu/tag/07RB (we only prove the forward direction!)
-/
instance unit_is_iso_of_L_fully_faithful [full L] [faithful L] : is_iso (adjunction.unit h) :=
  @nat_iso.is_iso_of_is_iso_app _ _ _ _ _ _ (adjunction.unit h)$
    fun X =>
      @yoneda.is_iso _ _ _ _ ((adjunction.unit h).app X)
        ⟨⟨{ app := fun Y f => L.preimage ((h.hom_equiv (unop Y) (L.obj X)).symm f) },
            ⟨by 
                ext x f 
                dsimp 
                apply L.map_injective 
                simp ,
              by 
                ext x f 
                dsimp 
                simp only [adjunction.hom_equiv_counit, preimage_comp, preimage_map, category.assoc]
                rw [←h.unit_naturality]
                simp ⟩⟩⟩

/--
If the right adjoint is fully faithful, then the counit is an isomorphism.

See https://stacks.math.columbia.edu/tag/07RB (we only prove the forward direction!)
-/
instance counit_is_iso_of_R_fully_faithful [full R] [faithful R] : is_iso (adjunction.counit h) :=
  @nat_iso.is_iso_of_is_iso_app _ _ _ _ _ _ (adjunction.counit h)$
    fun X =>
      @is_iso_of_op _ _ _ _ _$
        @coyoneda.is_iso _ _ _ _ ((adjunction.counit h).app X).op
          ⟨⟨{ app := fun Y f => R.preimage ((h.hom_equiv (R.obj X) Y) f) },
              ⟨by 
                  ext x f 
                  dsimp 
                  apply R.map_injective 
                  simp ,
                by 
                  ext x f 
                  dsimp 
                  simp only [adjunction.hom_equiv_unit, preimage_comp, preimage_map]
                  rw [←h.counit_naturality]
                  simp ⟩⟩⟩

/-- If the unit of an adjunction is an isomorphism, then its inverse on the image of L is given
by L whiskered with the counit. -/
@[simp]
theorem inv_map_unit {X : C} [is_iso (h.unit.app X)] : inv (L.map (h.unit.app X)) = h.counit.app (L.obj X) :=
  is_iso.inv_eq_of_hom_inv_id h.left_triangle_components

/-- If the unit is an isomorphism, bundle one has an isomorphism `L ⋙ R ⋙ L ≅ L`. -/
@[simps]
noncomputable def whisker_left_L_counit_iso_of_is_iso_unit [is_iso h.unit] : L ⋙ R ⋙ L ≅ L :=
  (L.associator R L).symm ≪≫ iso_whisker_right (as_iso h.unit).symm L ≪≫ functor.left_unitor _

/-- If the counit of an adjunction is an isomorphism, then its inverse on the image of R is given
by R whiskered with the unit. -/
@[simp]
theorem inv_counit_map {X : D} [is_iso (h.counit.app X)] : inv (R.map (h.counit.app X)) = h.unit.app (R.obj X) :=
  is_iso.inv_eq_of_inv_hom_id h.right_triangle_components

/-- If the counit of an is an isomorphism, one has an isomorphism `(R ⋙ L ⋙ R) ≅ R`. -/
@[simps]
noncomputable def whisker_left_R_unit_iso_of_is_iso_counit [is_iso h.counit] : R ⋙ L ⋙ R ≅ R :=
  (R.associator L R).symm ≪≫ iso_whisker_right (as_iso h.counit) R ≪≫ functor.left_unitor _

/-- If the unit is an isomorphism, then the left adjoint is full-/
noncomputable def L_full_of_unit_is_iso [is_iso h.unit] : full L :=
  { Preimage := fun X Y f => h.hom_equiv X (L.obj Y) f ≫ inv (h.unit.app Y) }

/-- If the unit is an isomorphism, then the left adjoint is faithful-/
theorem L_faithful_of_unit_is_iso [is_iso h.unit] : faithful L :=
  { map_injective' :=
      fun X Y f g H =>
        by 
          rw [←(h.hom_equiv X (L.obj Y)).apply_eq_iff_eq] at H 
          simpa using H =≫ inv (h.unit.app Y) }

/-- If the counit is an isomorphism, then the right adjoint is full-/
noncomputable def R_full_of_counit_is_iso [is_iso h.counit] : full R :=
  { Preimage := fun X Y f => inv (h.counit.app X) ≫ (h.hom_equiv (R.obj X) Y).symm f }

/-- If the counit is an isomorphism, then the right adjoint is faithful-/
theorem R_faithful_of_counit_is_iso [is_iso h.counit] : faithful R :=
  { map_injective' :=
      fun X Y f g H =>
        by 
          rw [←(h.hom_equiv (R.obj X) Y).symm.apply_eq_iff_eq] at H 
          simpa using inv (h.counit.app X) ≫= H }

universe v₃ v₄ u₃ u₄

variable{C' : Type u₃}[category.{v₃} C']

variable{D' : Type u₄}[category.{v₄} D']

/--
If `C` is a full subcategory of `C'` and `D` is a full subcategory of `D'`, then we can restrict
an adjunction `L' ⊣ R'` where `L' : C' ⥤ D'` and `R' : D' ⥤ C'` to `C` and `D`.
The construction here is slightly more general, in that `C` is required only to have a full and
faithful "inclusion" functor `iC : C ⥤ C'` (and similarly `iD : D ⥤ D'`) which commute (up to
natural isomorphism) with the proposed restrictions.
-/
def adjunction.restrict_fully_faithful (iC : C ⥤ C') (iD : D ⥤ D') {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj : L' ⊣ R')
  {L : C ⥤ D} {R : D ⥤ C} (comm1 : iC ⋙ L' ≅ L ⋙ iD) (comm2 : iD ⋙ R' ≅ R ⋙ iC) [full iC] [faithful iC] [full iD]
  [faithful iD] : L ⊣ R :=
  adjunction.mk_of_hom_equiv
    { homEquiv :=
        fun X Y =>
          calc (L.obj X ⟶ Y) ≃ (iD.obj (L.obj X) ⟶ iD.obj Y) := equiv_of_fully_faithful iD 
            _ ≃ (L'.obj (iC.obj X) ⟶ iD.obj Y) := iso.hom_congr (comm1.symm.app X) (iso.refl _)
            _ ≃ (iC.obj X ⟶ R'.obj (iD.obj Y)) := adj.hom_equiv _ _ 
            _ ≃ (iC.obj X ⟶ iC.obj (R.obj Y)) := iso.hom_congr (iso.refl _) (comm2.app Y)
            _ ≃ (X ⟶ R.obj Y) := (equiv_of_fully_faithful iC).symm
            ,
      hom_equiv_naturality_left_symm' :=
        fun X' X Y f g =>
          by 
            apply iD.map_injective 
            simpa using (comm1.inv.naturality_assoc f _).symm,
      hom_equiv_naturality_right' :=
        fun X Y' Y f g =>
          by 
            apply iC.map_injective 
            suffices  : R'.map (iD.map g) ≫ comm2.hom.app Y = comm2.hom.app Y' ≫ iC.map (R.map g)
            simp [this]
            apply comm2.hom.naturality g }

end CategoryTheory

