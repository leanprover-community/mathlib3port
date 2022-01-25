import Mathbin.AlgebraicGeometry.GammaSpecAdjunction
import Mathbin.AlgebraicGeometry.OpenImmersion
import Mathbin.CategoryTheory.Limits.Opposites

/-!
# Affine schemes

We define the category of `AffineScheme`s as the essential image of `Spec`.
We also define predicates about affine schemes and affine open sets.

## Main definitions

* `algebraic_geometry.AffineScheme`: The category of affine schemes.
* `algebraic_geometry.is_affine`: A scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an
  isomorphism.
* `algebraic_geometry.Scheme.iso_Spec`: The canonical isomorphism `X ≅ Spec Γ(X)` for an affine
  scheme.
* `algebraic_geometry.AffineScheme.equiv_CommRing`: The equivalence of categories
  `AffineScheme ≌ CommRingᵒᵖ` given by `AffineScheme.Spec : CommRingᵒᵖ ⥤ AffineScheme` and
  `AffineScheme.Γ : AffineSchemeᵒᵖ ⥤ CommRing`.
* `algebraic_geometry.is_affine_open`: An open subset of a scheme is affine if the open subscheme is
  affine.
* `algebraic_geometry.is_affine_open.from_Spec`: The immersion `Spec 𝒪ₓ(U) ⟶ X` for an affine `U`.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The category of affine schemes -/
def AffineScheme :=
  Scheme.Spec.EssImage

/-- A Scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an isomorphism. -/
class is_affine (X : Scheme) : Prop where
  affine : is_iso (Γ_Spec.adjunction.Unit.app X)

attribute [instance] is_affine.affine

/-- The canonical isomorphism `X ≅ Spec Γ(X)` for an affine scheme. -/
def Scheme.iso_Spec (X : Scheme) [is_affine X] : X ≅ Scheme.Spec.obj (op $ Scheme.Γ.obj $ op X) :=
  as_iso (Γ_Spec.adjunction.Unit.app X)

theorem mem_AffineScheme (X : Scheme) : X ∈ AffineScheme ↔ is_affine X :=
  ⟨fun h => ⟨functor.ess_image.unit_is_iso h⟩, fun h => @mem_ess_image_of_unit_is_iso _ _ _ X h.1⟩

instance is_affine_AffineScheme (X : AffineScheme.{u}) : is_affine (X : Scheme.{u}) :=
  (mem_AffineScheme _).mp X.prop

instance Spec_is_affine (R : CommRingₓₓᵒᵖ) : is_affine (Scheme.Spec.obj R) :=
  (mem_AffineScheme _).mp (Scheme.Spec.obj_mem_ess_image R)

theorem is_affine_of_iso {X Y : Scheme} (f : X ⟶ Y) [is_iso f] [h : is_affine Y] : is_affine X := by
  rw [← mem_AffineScheme] at h⊢
  exact functor.ess_image.of_iso (as_iso f).symm h

namespace AffineScheme

/-- The `Spec` functor into the category of affine schemes. -/
@[simps]
def Spec : CommRingₓₓᵒᵖ ⥤ AffineScheme :=
  Scheme.Spec.toEssImage deriving full, faithful, ess_surj

/-- The forgetful functor `AffineScheme ⥤ Scheme`. -/
@[simps]
def forget_to_Scheme : AffineScheme ⥤ Scheme :=
  Scheme.Spec.essImageInclusion deriving full, faithful

/-- The global section functor of an affine scheme. -/
def Γ : AffineSchemeᵒᵖ ⥤ CommRingₓₓ :=
  forget_to_Scheme.op ⋙ Scheme.Γ

/-- The category of affine schemes is equivalent to the category of commutative rings. -/
def equiv_CommRing : AffineScheme ≌ CommRingₓₓᵒᵖ :=
  equiv_ess_image_of_reflective.symm

instance Γ_is_equiv : is_equivalence Γ.{u} :=
  have : is_equivalence Γ.{u}.rightOp.op := is_equivalence.of_equivalence equiv_CommRing.op
  (functor.is_equivalence_trans Γ.{u}.rightOp.op (op_op_equivalence _).Functor : _)

instance : has_colimits AffineScheme.{u} := by
  have := adjunction.has_limits_of_equivalence.{u} Γ.{u}
  have : has_colimits (AffineScheme.{u}ᵒᵖᵒᵖ) := has_colimits_op_of_has_limits
  exact adjunction.has_colimits_of_equivalence.{u} (op_op_equivalence AffineScheme.{u}).inverse

instance : has_limits AffineScheme.{u} := by
  have := adjunction.has_colimits_of_equivalence Γ.{u}
  have : has_limits (AffineScheme.{u}ᵒᵖᵒᵖ) := limits.has_limits_op_of_has_colimits
  exact adjunction.has_limits_of_equivalence (op_op_equivalence AffineScheme.{u}).inverse

end AffineScheme

/-- An open subset of a scheme is affine if the open subscheme is affine. -/
def is_affine_open {X : Scheme} (U : opens X.carrier) : Prop :=
  is_affine (X.restrict U.open_embedding)

theorem range_is_affine_open_of_open_immersion {X Y : Scheme} [is_affine X] (f : X ⟶ Y) [H : is_open_immersion f] :
    is_affine_open ⟨Set.Range f.1.base, H.base_open.open_range⟩ := by
  refine' is_affine_of_iso (is_open_immersion.iso_of_range_eq f (Y.of_restrict _) _).inv
  exact subtype.range_coe.symm
  infer_instance

theorem top_is_affine_open (X : Scheme) [is_affine X] : is_affine_open (⊤ : opens X.carrier) := by
  convert range_is_affine_open_of_open_immersion (𝟙 X)
  ext1
  exact set.range_id.symm

instance Scheme.affine_basis_cover_is_affine (X : Scheme) (i : X.affine_basis_cover.J) :
    is_affine (X.affine_basis_cover.obj i) :=
  AlgebraicGeometry.Spec_is_affine _

theorem is_basis_affine_open (X : Scheme) : opens.is_basis { U : opens X.carrier | is_affine_open U } := by
  rw [opens.is_basis_iff_nbhd]
  rintro U x (hU : x ∈ (U : Set X.carrier))
  obtain ⟨S, hS, hxS, hSU⟩ := X.affine_basis_cover_is_basis.exists_subset_of_mem_open hU U.prop
  refine' ⟨⟨S, X.affine_basis_cover_is_basis.is_open hS⟩, _, hxS, hSU⟩
  rcases hS with ⟨i, rfl⟩
  exact range_is_affine_open_of_open_immersion _

/-- The open immersion `Spec 𝒪ₓ(U) ⟶ X` for an affine `U`. -/
def is_affine_open.from_Spec {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
    Scheme.Spec.obj (op $ X.presheaf.obj $ op U) ⟶ X := by
  have : is_affine (X.restrict U.open_embedding) := hU
  have : U.open_embedding.is_open_map.functor.obj ⊤ = U := by
    ext1
    exact set.image_univ.trans Subtype.range_coe
  exact
    Scheme.Spec.map (X.presheaf.map (eq_to_hom this.symm).op).op ≫
      (X.restrict U.open_embedding).isoSpec.inv ≫ X.of_restrict _

instance is_affine_open.is_open_immersion_from_Spec {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
    is_open_immersion hU.from_Spec := by
  delta' is_affine_open.from_Spec
  infer_instance

theorem is_affine_open.from_Spec_range {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
    Set.Range hU.from_Spec.1.base = (U : Set X.carrier) := by
  delta' is_affine_open.from_Spec
  erw [← category.assoc, Scheme.comp_val_base]
  rw [coe_comp, Set.range_comp, set.range_iff_surjective.mpr, Set.image_univ]
  exact Subtype.range_coe
  rw [← Top.epi_iff_surjective]
  infer_instance

theorem is_affine_open.from_Spec_image_top {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
    hU.is_open_immersion_from_Spec.base_open.is_open_map.functor.obj ⊤ = U := by
  ext1
  exact set.image_univ.trans hU.from_Spec_range

theorem is_affine_open.is_compact {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
    IsCompact (U : Set X.carrier) := by
  convert
    @IsCompact.image _ _ _ _ Set.Univ hU.from_Spec.1.base PrimeSpectrum.compact_space.1
      (by
        continuity)
  convert hU.from_Spec_range.symm
  exact Set.image_univ

instance Scheme.quasi_compact_of_affine (X : Scheme) [is_affine X] : CompactSpace X.carrier :=
  ⟨(top_is_affine_open X).IsCompact⟩

theorem is_affine_open.from_Spec_base_preimage {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
    (opens.map hU.from_Spec.val.base).obj U = ⊤ := by
  ext1
  change hU.from_Spec.1.base ⁻¹' (U : Set X.carrier) = Set.Univ
  rw [← hU.from_Spec_range, ← Set.image_univ]
  exact Set.preimage_image_eq _ PresheafedSpace.is_open_immersion.base_open.inj

theorem Scheme.Spec_map_presheaf_map_eq_to_hom {X : Scheme} {U V : opens X.carrier} (h : U = V) W :
    (Scheme.Spec.map (X.presheaf.map (eq_to_hom h).op).op).val.c.app W =
      eq_to_hom
        (by
          cases h
          dsimp
          induction W using Opposite.rec
          congr
          ext1
          simpa) :=
  by
  have : Scheme.Spec.map (X.presheaf.map (𝟙 (op U))).op = 𝟙 _ := by
    rw [X.presheaf.map_id, op_id, Scheme.Spec.map_id]
  cases h
  refine' (Scheme.congr_app this _).trans _
  erw [category.id_comp]
  simpa

theorem is_affine_open.Spec_Γ_identity_hom_app_from_Spec {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
    Spec_Γ_identity.Hom.app (X.presheaf.obj $ op U) ≫ hU.from_Spec.1.c.app (op U) =
      (Scheme.Spec.obj _).Presheaf.map (eq_to_hom hU.from_Spec_base_preimage).op :=
  by
  have : is_affine _ := hU
  have e₁ := Spec_Γ_identity.hom.naturality (X.presheaf.map (eq_to_hom U.open_embedding_obj_top).op)
  rw [← is_iso.comp_inv_eq] at e₁
  have e₂ := Γ_Spec.adjunction_unit_app_app_top (X.restrict U.open_embedding)
  erw [← e₂] at e₁
  simp only [functor.id_map, Quiver.Hom.unop_op, functor.comp_map, ← functor.map_inv, ← op_inv,
    LocallyRingedSpace.Γ_map, category.assoc, functor.right_op_map, inv_eq_to_hom] at e₁
  delta' is_affine_open.from_Spec Scheme.iso_Spec
  rw [Scheme.comp_val_c_app, Scheme.comp_val_c_app, ← e₁]
  simp_rw [category.assoc]
  erw [← X.presheaf.map_comp_assoc]
  rw [← op_comp]
  have e₃ :
    U.open_embedding.is_open_map.adjunction.counit.app U ≫ eq_to_hom U.open_embedding_obj_top.symm =
      U.open_embedding.is_open_map.functor.map (eq_to_hom U.inclusion_map_eq_top) :=
    Subsingleton.elimₓ _ _
  have e₄ : X.presheaf.map _ ≫ _ = _ :=
    (as_iso (Γ_Spec.adjunction.unit.app (X.restrict U.open_embedding))).inv.1.c.naturality_assoc
      (eq_to_hom U.inclusion_map_eq_top).op _
  erw [e₃, e₄, ← Scheme.comp_val_c_app_assoc, iso.inv_hom_id]
  simp only [eq_to_hom_map, eq_to_hom_op, Scheme.Spec_map_presheaf_map_eq_to_hom]
  erw [Scheme.Spec_map_presheaf_map_eq_to_hom, category.id_comp]
  simpa only [eq_to_hom_trans]

@[elementwise]
theorem is_affine_open.from_Spec_app_eq {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
    hU.from_Spec.1.c.app (op U) =
      Spec_Γ_identity.inv.app (X.presheaf.obj $ op U) ≫
        (Scheme.Spec.obj _).Presheaf.map (eq_to_hom hU.from_Spec_base_preimage).op :=
  by
  rw [← hU.Spec_Γ_identity_hom_app_from_Spec, iso.inv_hom_id_app_assoc]

theorem is_affine_open.basic_open_is_affine {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U)
    (f : X.presheaf.obj (op U)) : is_affine_open (X.basic_open f) := by
  convert
    range_is_affine_open_of_open_immersion
      (Scheme.Spec.map (CommRingₓₓ.ofHom (algebraMap (X.presheaf.obj (op U)) (Localization.Away f))).op ≫ hU.from_Spec)
  ext1
  have :
    hU.from_Spec.val.base '' (hU.from_Spec.val.base ⁻¹' (X.basic_open f : Set X.carrier)) =
      (X.basic_open f : Set X.carrier) :=
    by
    rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left_iff_subset, hU.from_Spec_range]
    exact Scheme.basic_open_subset _ _
  rw [Subtype.coe_mk, Scheme.comp_val_base, ← this, coe_comp, Set.range_comp]
  congr 1
  refine' (congr_argₓ coe $ Scheme.preimage_basic_open hU.from_Spec f).trans _
  refine' Eq.trans _ (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).symm
  congr 1
  have : (opens.map hU.from_Spec.val.base).obj U = ⊤ := by
    ext1
    change hU.from_Spec.1.base ⁻¹' (U : Set X.carrier) = Set.Univ
    rw [← hU.from_Spec_range, ← Set.image_univ]
    exact Set.preimage_image_eq _ PresheafedSpace.is_open_immersion.base_open.inj
  refine' Eq.trans _ (basic_open_eq_of_affine f)
  have lm : ∀ s, (opens.map hU.from_Spec.val.base).obj U⊓s = s := fun s => this.symm ▸ top_inf_eq
  refine' Eq.trans _ (lm _)
  refine' Eq.trans _ ((Scheme.Spec.obj $ op $ X.presheaf.obj $ op U).basic_open_res _ (eq_to_hom this).op)
  rw [← comp_apply]
  congr 2
  rw [iso.eq_inv_comp]
  erw [hU.Spec_Γ_identity_hom_app_from_Spec]

theorem Scheme.map_prime_spectrum_basic_open_of_affine (X : Scheme) [is_affine X] (f : Scheme.Γ.obj (op X)) :
    (opens.map X.iso_Spec.hom.1.base).obj (PrimeSpectrum.basicOpen f) = X.basic_open f := by
  rw [← basic_open_eq_of_affine]
  trans
    (opens.map X.iso_Spec.hom.1.base).obj
      ((Scheme.Spec.obj (op (Scheme.Γ.obj (op X)))).basicOpen
        ((inv (X.iso_Spec.hom.1.c.app (op ((opens.map (inv X.iso_Spec.hom).val.base).obj ⊤))))
          ((X.presheaf.map (eq_to_hom _)) f)))
  congr
  · rw [← is_iso.inv_eq_inv, is_iso.inv_inv, is_iso.iso.inv_inv, nat_iso.app_hom]
    erw [← Γ_Spec.adjunction_unit_app_app_top]
    rfl
    
  · rw [eq_to_hom_map]
    rfl
    
  · dsimp
    congr
    
  · refine' (Scheme.preimage_basic_open _ _).trans _
    rw [is_iso.inv_hom_id_apply, Scheme.basic_open_res_eq]
    

theorem is_basis_basic_open (X : Scheme) [is_affine X] :
    opens.is_basis (Set.Range (X.basic_open : X.presheaf.obj (op ⊤) → opens X.carrier)) := by
  delta' opens.is_basis
  convert
    prime_spectrum.is_basis_basic_opens.inducing
      (Top.homeoOfIso (Scheme.forget_to_Top.map_iso X.iso_Spec)).Inducing using
    1
  ext
  simp only [Set.mem_image, exists_exists_eq_and]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine' ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, _⟩
    exact congr_argₓ Subtype.val (X.map_prime_spectrum_basic_open_of_affine x)
    
  · rintro ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩
    refine' ⟨_, ⟨x, rfl⟩, _⟩
    exact congr_argₓ Subtype.val (X.map_prime_spectrum_basic_open_of_affine x).symm
    

end AlgebraicGeometry

