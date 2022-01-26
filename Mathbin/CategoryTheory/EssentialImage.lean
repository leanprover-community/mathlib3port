import Mathbin.CategoryTheory.NaturalIsomorphism
import Mathbin.CategoryTheory.FullSubcategory

/-!
# Essential image of a functor

The essential image `ess_image` of a functor consists of the objects in the target category which
are isomorphic to an object in the image of the object function.
This, for instance, allows us to talk about objects belonging to a subcategory expressed as a
functor rather than a subtype, preserving the principle of equivalence. For example this lets us
define exponential ideals.

The essential image can also be seen as a subcategory of the target category, and witnesses that
a functor decomposes into a essentially surjective functor and a fully faithful functor.
(TODO: show that this decomposition forms an orthogonal factorisation system).
-/


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D] {F : C ⥤ D}

namespace Functor

/-- The essential image of a functor `F` consists of those objects in the target category which are
isomorphic to an object in the image of the function `F.obj`. In other words, this is the closure
under isomorphism of the function `F.obj`.
This is the "non-evil" way of describing the image of a functor.
-/
def ess_image (F : C ⥤ D) : Set D := fun Y => ∃ X : C, Nonempty (F.obj X ≅ Y)

/-- Get the witnessing object that `Y` is in the subcategory given by `F`. -/
def ess_image.witness {Y : D} (h : Y ∈ F.ess_image) : C :=
  h.some

/-- Extract the isomorphism between `F.obj h.witness` and `Y` itself. -/
def ess_image.get_iso {Y : D} (h : Y ∈ F.ess_image) : F.obj h.witness ≅ Y :=
  Classical.choice h.some_spec

/-- Being in the essential image is a "hygenic" property: it is preserved under isomorphism. -/
theorem ess_image.of_iso {Y Y' : D} (h : Y ≅ Y') (hY : Y ∈ ess_image F) : Y' ∈ ess_image F :=
  hY.imp fun B => Nonempty.map (· ≪≫ h)

/-- If `Y` is in the essential image of `F` then it is in the essential image of `F'` as long as
`F ≅ F'`.
-/
theorem ess_image.of_nat_iso {F' : C ⥤ D} (h : F ≅ F') {Y : D} (hY : Y ∈ ess_image F) : Y ∈ ess_image F' :=
  hY.imp fun X => Nonempty.map fun t => h.symm.app X ≪≫ t

/-- Isomorphic functors have equal essential images. -/
theorem ess_image_eq_of_nat_iso {F' : C ⥤ D} (h : F ≅ F') : ess_image F = ess_image F' :=
  Set.ext fun A => ⟨ess_image.of_nat_iso h, ess_image.of_nat_iso h.symm⟩

/-- An object in the image is in the essential image. -/
theorem obj_mem_ess_image (F : D ⥤ C) (Y : D) : F.obj Y ∈ ess_image F :=
  ⟨Y, ⟨iso.refl _⟩⟩

instance : category F.ess_image :=
  CategoryTheory.fullSubcategory _

/-- The essential image as a subcategory has a fully faithful inclusion into the target category. -/
@[simps]
def ess_image_inclusion (F : C ⥤ D) : F.ess_image ⥤ D :=
  full_subcategory_inclusion _ deriving full, faithful

/-- Given a functor `F : C ⥤ D`, we have an (essentially surjective) functor from `C` to the essential
image of `F`.
-/
@[simps]
def to_ess_image (F : C ⥤ D) : C ⥤ F.ess_image where
  obj := fun X => ⟨_, obj_mem_ess_image _ X⟩
  map := fun X Y f => (ess_image_inclusion F).Preimage (F.map f)

/-- The functor `F` factorises through its essential image, where the first functor is essentially
surjective and the second is fully faithful.
-/
@[simps]
def to_ess_image_comp_essential_image_inclusion (F : C ⥤ D) : F.to_ess_image ⋙ F.ess_image_inclusion ≅ F :=
  nat_iso.of_components (fun X => iso.refl _)
    (by
      tidy)

end Functor

/-- A functor `F : C ⥤ D` is essentially surjective if every object of `D` is in the essential image
of `F`. In other words, for every `Y : D`, there is some `X : C` with `F.obj X ≅ Y`.

See https://stacks.math.columbia.edu/tag/001C.
-/
class ess_surj (F : C ⥤ D) : Prop where
  mem_ess_image {} (Y : D) : Y ∈ F.ess_image

instance : ess_surj F.to_ess_image where
  mem_ess_image := fun ⟨Y, hY⟩ => ⟨_, ⟨⟨_, _, hY.get_iso.hom_inv_id, hY.get_iso.inv_hom_id⟩⟩⟩

variable (F) [ess_surj F]

/-- Given an essentially surjective functor, we can find a preimage for every object `Y` in the
    codomain. Applying the functor to this preimage will yield an object isomorphic to `Y`, see
    `obj_obj_preimage_iso`. -/
def functor.obj_preimage (Y : D) : C :=
  (ess_surj.mem_ess_image F Y).witness

/-- Applying an essentially surjective functor to a preimage of `Y` yields an object that is
    isomorphic to `Y`. -/
def functor.obj_obj_preimage_iso (Y : D) : F.obj (F.obj_preimage Y) ≅ Y :=
  (ess_surj.mem_ess_image F Y).getIso

/-- The induced functor of a faithful functor is faithful -/
instance faithful.to_ess_image (F : C ⥤ D) [faithful F] : faithful F.to_ess_image :=
  faithful.of_comp_iso F.to_ess_image_comp_essential_image_inclusion

/-- The induced functor of a full functor is full -/
instance full.to_ess_image (F : C ⥤ D) [full F] : full F.to_ess_image :=
  have := full.of_iso F.to_ess_image_comp_essential_image_inclusion.symm
  full.of_comp_faithful F.to_ess_image F.ess_image_inclusion

end CategoryTheory

