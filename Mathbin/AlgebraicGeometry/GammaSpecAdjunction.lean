import Mathbin.AlgebraicGeometry.Scheme
import Mathbin.CategoryTheory.Adjunction.Limits
import Mathbin.CategoryTheory.Adjunction.Reflective

/-!
# Adjunction between `Γ` and `Spec`

We define the adjunction `Γ_Spec.adjunction : Γ ⊣ Spec` by defining the unit (`to_Γ_Spec`,
in multiple steps in this file) and counit (done in Spec.lean) and checking that they satisfy
the left and right triangle identities. The constructions and proofs make use of
maps and lemmas defined and proved in structure_sheaf.lean extensively.

Notice that since the adjunction is between contravariant functors, you get to choose
one of the two categories to have arrows reversed, and it is equally valid to present
the adjunction as `Spec ⊣ Γ` (`Spec.to_LocallyRingedSpace.right_op ⊣ Γ`), in which
case the unit and the counit would switch to each other.

## Main definition

* `algebraic_geometry.identity_to_Γ_Spec` : The natural transformation `𝟭 _ ⟶ Γ ⋙ Spec`.
* `algebraic_geometry.Γ_Spec.LocallyRingedSpace_adjunction` : The adjunction `Γ ⊣ Spec` from
  `CommRingᵒᵖ` to `LocallyRingedSpace`.
* `algebraic_geometry.Γ_Spec.adjunction` : The adjunction `Γ ⊣ Spec` from
  `CommRingᵒᵖ` to `Scheme`.

-/


noncomputable section

universe u

open PrimeSpectrum

namespace AlgebraicGeometry

open Opposite

open CategoryTheory

open StructureSheaf

open TopologicalSpace

open AlgebraicGeometry.LocallyRingedSpace

open Top.Presheaf

open Top.Presheaf.SheafCondition

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

/-- The map from the global sections to a stalk. -/
def Γ_to_stalk (x : X) : Γ.obj (op X) ⟶ X.presheaf.stalk x :=
  X.presheaf.germ (⟨x, trivialₓ⟩ : (⊤ : opens X))

/-- The canonical map from the underlying set to the prime spectrum of `Γ(X)`. -/
def to_Γ_Spec_fun : X → PrimeSpectrum (Γ.obj (op X)) := fun x =>
  comap (X.Γ_to_stalk x) (LocalRing.closedPoint (X.presheaf.stalk x))

theorem not_mem_prime_iff_unit_in_stalk (r : Γ.obj (op X)) (x : X) :
    r ∉ (X.to_Γ_Spec_fun x).asIdeal ↔ IsUnit (X.Γ_to_stalk x r) := by
  erw [LocalRing.mem_maximal_ideal, not_not]

/-- The preimage of a basic open in `Spec Γ(X)` under the unit is the basic
open in `X` defined by the same element (they are equal as sets). -/
theorem to_Γ_Spec_preim_basic_open_eq (r : Γ.obj (op X)) :
    X.to_Γ_Spec_fun ⁻¹' (basic_open r).1 = (X.to_RingedSpace.basic_open r).1 := by
  ext
  erw [X.to_RingedSpace.mem_top_basic_open]
  apply not_mem_prime_iff_unit_in_stalk

/-- `to_Γ_Spec_fun` is continuous. -/
theorem to_Γ_Spec_continuous : Continuous X.to_Γ_Spec_fun := by
  apply is_topological_basis_basic_opens.continuous
  rintro _ ⟨r, rfl⟩
  erw [X.to_Γ_Spec_preim_basic_open_eq r]
  exact (X.to_RingedSpace.basic_open r).2

/-- The canonical (bundled) continuous map from the underlying topological
space of `X` to the prime spectrum of its global sections. -/
@[simps]
def to_Γ_Spec_base : X.to_Top ⟶ Spec.Top_obj (Γ.obj (op X)) where
  toFun := X.to_Γ_Spec_fun
  continuous_to_fun := X.to_Γ_Spec_continuous

variable (r : Γ.obj (op X))

/-- The preimage in `X` of a basic open in `Spec Γ(X)` (as an open set). -/
abbrev to_Γ_Spec_map_basic_open : opens X :=
  (opens.map X.to_Γ_Spec_base).obj (basic_open r)

/-- The preimage is the basic open in `X` defined by the same element `r`. -/
theorem to_Γ_Spec_map_basic_open_eq : X.to_Γ_Spec_map_basic_open r = X.to_RingedSpace.basic_open r :=
  Subtype.eq (X.to_Γ_Spec_preim_basic_open_eq r)

/-- The map from the global sections `Γ(X)` to the sections on the (preimage of) a basic open. -/
abbrev to_to_Γ_Spec_map_basic_open : X.presheaf.obj (op ⊤) ⟶ X.presheaf.obj (op $ X.to_Γ_Spec_map_basic_open r) :=
  X.presheaf.map (X.to_Γ_Spec_map_basic_open r).le_top.op

/-- `r` is a unit as a section on the basic open defined by `r`. -/
theorem is_unit_res_to_Γ_Spec_map_basic_open : IsUnit (X.to_to_Γ_Spec_map_basic_open r r) := by
  convert
    (X.presheaf.map $ (eq_to_hom $ X.to_Γ_Spec_map_basic_open_eq r).op).is_unit_map
      (X.to_RingedSpace.is_unit_res_basic_open r)
  rw [← comp_apply]
  erw [← functor.map_comp]
  congr

/-- Define the sheaf hom on individual basic opens for the unit. -/
def to_Γ_Spec_c_app :
    (structure_sheaf $ Γ.obj $ op X).val.obj (op $ basic_open r) ⟶ X.presheaf.obj (op $ X.to_Γ_Spec_map_basic_open r) :=
  IsLocalization.Away.lift r (is_unit_res_to_Γ_Spec_map_basic_open _ r)

/-- Characterization of the sheaf hom on basic opens,
    direction ← (next lemma) is used at various places, but → is not used in this file. -/
theorem to_Γ_Spec_c_app_iff
    (f :
      (structure_sheaf $ Γ.obj $ op X).val.obj (op $ basic_open r) ⟶
        X.presheaf.obj (op $ X.to_Γ_Spec_map_basic_open r)) :
    to_open _ (basic_open r) ≫ f = X.to_to_Γ_Spec_map_basic_open r ↔ f = X.to_Γ_Spec_c_app r := by
  rw [← IsLocalization.Away.AwayMap.lift_comp r (X.is_unit_res_to_Γ_Spec_map_basic_open r)]
  swap 5
  exact is_localization.to_basic_open _ r
  constructor
  · intro h
    refine' IsLocalization.ring_hom_ext _ _
    swap 5
    exact is_localization.to_basic_open _ r
    exact h
    
  apply congr_argₓ

theorem to_Γ_Spec_c_app_spec : to_open _ (basic_open r) ≫ X.to_Γ_Spec_c_app r = X.to_to_Γ_Spec_map_basic_open r :=
  (X.to_Γ_Spec_c_app_iff r _).2 rfl

/-- The sheaf hom on all basic opens, commuting with restrictions. -/
def to_Γ_Spec_c_basic_opens :
    (induced_functor basic_open).op ⋙ (structure_sheaf (Γ.obj (op X))).1 ⟶
      (induced_functor basic_open).op ⋙ ((Top.Sheaf.pushforward X.to_Γ_Spec_base).obj X.𝒪).1 where
  app := fun r => X.to_Γ_Spec_c_app r.unop
  naturality' := fun r s f => by
    apply (structure_sheaf.to_basic_open_epi (Γ.obj (op X)) r.unop).1
    simp only [← category.assoc]
    erw [X.to_Γ_Spec_c_app_spec r.unop]
    convert X.to_Γ_Spec_c_app_spec s.unop
    symm
    apply X.presheaf.map_comp

/-- The canonical morphism of sheafed spaces from `X` to the spectrum of its global sections. -/
@[simps]
def to_Γ_Spec_SheafedSpace : X.to_SheafedSpace ⟶ Spec.to_SheafedSpace.obj (op (Γ.obj (op X))) where
  base := X.to_Γ_Spec_base
  c := Top.Sheaf.restrictHomEquivHom (structure_sheaf (Γ.obj (op X))).1 _ is_basis_basic_opens X.to_Γ_Spec_c_basic_opens

theorem to_Γ_Spec_SheafedSpace_app_eq : X.to_Γ_Spec_SheafedSpace.c.app (op (basic_open r)) = X.to_Γ_Spec_c_app r :=
  Top.Sheaf.extend_hom_app _ _ _ _ _

theorem to_Γ_Spec_SheafedSpace_app_spec (r : Γ.obj (op X)) :
    to_open _ (basic_open r) ≫ X.to_Γ_Spec_SheafedSpace.c.app (op (basic_open r)) = X.to_to_Γ_Spec_map_basic_open r :=
  (X.to_Γ_Spec_SheafedSpace_app_eq r).symm ▸ X.to_Γ_Spec_c_app_spec r

/-- The map on stalks induced by the unit commutes with maps from `Γ(X)` to
    stalks (in `Spec Γ(X)` and in `X`). -/
theorem to_stalk_stalk_map_to_Γ_Spec (x : X) :
    to_stalk _ _ ≫ PresheafedSpace.stalk_map X.to_Γ_Spec_SheafedSpace x = X.Γ_to_stalk x := by
  rw [PresheafedSpace.stalk_map]
  erw [←
    to_open_germ _ (basic_open (1 : Γ.obj (op X)))
      ⟨X.to_Γ_Spec_fun x, by
        rw [basic_open_one] <;> triv⟩]
  rw [← category.assoc, category.assoc (to_open _ _)]
  erw [stalk_functor_map_germ]
  rw [← category.assoc (to_open _ _), X.to_Γ_Spec_SheafedSpace_app_spec 1]
  unfold Γ_to_stalk
  rw [← stalk_pushforward_germ _ X.to_Γ_Spec_base X.presheaf ⊤]
  congr 1
  change (X.to_Γ_Spec_base _* X.presheaf).map le_top.hom.op ≫ _ = _
  apply germ_res

/-- The canonical morphism from `X` to the spectrum of its global sections. -/
@[simps coeBase]
def to_Γ_Spec : X ⟶ Spec.LocallyRingedSpace_obj (Γ.obj (op X)) where
  val := X.to_Γ_Spec_SheafedSpace
  property := by
    intro x
    let p : PrimeSpectrum (Γ.obj (op X)) := X.to_Γ_Spec_fun x
    constructor
    let S := (structure_sheaf _).val.stalk p
    rintro (t : S) ht
    obtain ⟨⟨r, s⟩, he⟩ := IsLocalization.surj p.as_ideal.prime_compl t
    dsimp  at he
    apply is_unit_of_mul_is_unit_left
    rw [he]
    refine' IsLocalization.map_units S (⟨r, _⟩ : p.as_ideal.prime_compl)
    apply (not_mem_prime_iff_unit_in_stalk _ _ _).mpr
    rw [← to_stalk_stalk_map_to_Γ_Spec, comp_apply]
    erw [← he]
    rw [RingHom.map_mul]
    exact
      ht.mul ((IsLocalization.map_units S s : _).map (PresheafedSpace.stalk_map X.to_Γ_Spec_SheafedSpace x).toMonoidHom)

theorem comp_ring_hom_ext {X : LocallyRingedSpace} {R : CommRingₓₓ} {f : R ⟶ Γ.obj (op X)}
    {β : X ⟶ Spec.LocallyRingedSpace_obj R} (w : X.to_Γ_Spec.1.base ≫ (Spec.LocallyRingedSpace_map f).1.base = β.1.base)
    (h :
      ∀ r : R,
        f ≫ X.presheaf.map (hom_of_le le_top : (opens.map β.1.base).obj (basic_open r) ⟶ _).op =
          to_open R (basic_open r) ≫ β.1.c.app (op (basic_open r))) :
    X.to_Γ_Spec ≫ Spec.LocallyRingedSpace_map f = β := by
  ext1
  apply Spec.basic_open_hom_ext
  · intro r _
    rw [LocallyRingedSpace.comp_val_c_app]
    erw [to_open_comp_comap_assoc]
    rw [category.assoc]
    erw [to_Γ_Spec_SheafedSpace_app_spec, ← X.presheaf.map_comp]
    convert h r
    
  exact w

/-- `to_Spec_Γ _` is an isomorphism so these are mutually two-sided inverses. -/
theorem Γ_Spec_left_triangle : to_Spec_Γ (Γ.obj (op X)) ≫ X.to_Γ_Spec.1.c.app (op ⊤) = 𝟙 _ := by
  unfold to_Spec_Γ
  rw [← to_open_res _ (basic_open (1 : Γ.obj (op X))) ⊤ (eq_to_hom basic_open_one.symm)]
  erw [category.assoc]
  rw [nat_trans.naturality, ← category.assoc]
  erw [X.to_Γ_Spec_SheafedSpace_app_spec 1, ← functor.map_comp]
  convert eq_to_hom_map X.presheaf _
  rfl

end LocallyRingedSpace

/-- The unit as a natural transformation. -/
def identity_to_Γ_Spec : 𝟭 LocallyRingedSpace.{u} ⟶ Γ.rightOp ⋙ Spec.to_LocallyRingedSpace where
  app := LocallyRingedSpace.to_Γ_Spec
  naturality' := fun X Y f => by
    symm
    apply LocallyRingedSpace.comp_ring_hom_ext
    · ext1 x
      dsimp [Spec.Top_map, LocallyRingedSpace.to_Γ_Spec_fun]
      rw [← Subtype.val_eq_coe, ← LocalRing.comap_closed_point (PresheafedSpace.stalk_map _ x), ←
        PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
      congr 2
      exact (PresheafedSpace.stalk_map_germ f.1 ⊤ ⟨x, trivialₓ⟩).symm
      infer_instance
      
    · intro r
      rw [LocallyRingedSpace.comp_val_c_app, ← category.assoc]
      erw [Y.to_Γ_Spec_SheafedSpace_app_spec, f.1.c.naturality]
      rfl
      

namespace ΓSpec

theorem left_triangle (X : LocallyRingedSpace) :
    Spec_Γ_identity.inv.app (Γ.obj (op X)) ≫ (identity_to_Γ_Spec.app X).val.c.app (op ⊤) = 𝟙 _ :=
  X.Γ_Spec_left_triangle

/-- `Spec_Γ_identity` is iso so these are mutually two-sided inverses. -/
theorem right_triangle (R : CommRingₓₓ) :
    identity_to_Γ_Spec.app (Spec.to_LocallyRingedSpace.obj $ op R) ≫
        Spec.to_LocallyRingedSpace.map (Spec_Γ_identity.inv.app R).op =
      𝟙 _ :=
  by
  apply LocallyRingedSpace.comp_ring_hom_ext
  · ext (p : PrimeSpectrum R) x
    erw [← IsLocalization.AtPrime.to_map_mem_maximal_iff ((structure_sheaf R).val.stalk p) p.as_ideal x]
    rfl
    
  · intro r
    apply to_open_res
    

/-- The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `LocallyRingedSpace`. -/
@[simps Unit counit]
def LocallyRingedSpace_adjunction : Γ.rightOp ⊣ Spec.to_LocallyRingedSpace :=
  adjunction.mk_of_unit_counit
    { Unit := identity_to_Γ_Spec, counit := (nat_iso.op Spec_Γ_identity).inv,
      left_triangle' := by
        ext X
        erw [category.id_comp]
        exact congr_argₓ Quiver.Hom.op (left_triangle X),
      right_triangle' := by
        ext1
        ext1 R
        erw [category.id_comp]
        exact right_triangle R.unop }

attribute [local semireducible] Spec.to_LocallyRingedSpace

/-- The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `Scheme`. -/
def adjunction : Scheme.Γ.rightOp ⊣ Scheme.Spec :=
  LocallyRingedSpace_adjunction.restrictFullyFaithful Scheme.forget_to_LocallyRingedSpace (𝟭 _)
    (nat_iso.of_components (fun X => iso.refl _) fun _ _ f => by
      simpa)
    (nat_iso.of_components (fun X => iso.refl _) fun _ _ f => by
      simpa)

theorem adjunction_hom_equiv_apply {X : Scheme} {R : CommRingₓₓᵒᵖ} (f : (op $ Scheme.Γ.obj $ op X) ⟶ R) :
    Γ_Spec.adjunction.homEquiv X R f = LocallyRingedSpace_adjunction.homEquiv X.1 R f := by
  dsimp [adjunction, adjunction.restrict_fully_faithful]
  simp

theorem adjunction_hom_equiv (X : Scheme) (R : CommRingₓₓᵒᵖ) :
    Γ_Spec.adjunction.homEquiv X R = LocallyRingedSpace_adjunction.homEquiv X.1 R :=
  Equivₓ.ext $ fun f => adjunction_hom_equiv_apply f

theorem adjunction_hom_equiv_symm_apply {X : Scheme} {R : CommRingₓₓᵒᵖ} (f : X ⟶ Scheme.Spec.obj R) :
    (Γ_Spec.adjunction.homEquiv X R).symm f = (LocallyRingedSpace_adjunction.homEquiv X.1 R).symm f := by
  congr 2
  exact adjunction_hom_equiv _ _

@[simp]
theorem adjunction_counit_app {R : CommRingₓₓᵒᵖ} :
    Γ_Spec.adjunction.counit.app R = LocallyRingedSpace_adjunction.counit.app R := by
  rw [← adjunction.hom_equiv_symm_id, ← adjunction.hom_equiv_symm_id, adjunction_hom_equiv_symm_apply]
  rfl

@[simp]
theorem adjunction_unit_app {X : Scheme} : Γ_Spec.adjunction.Unit.app X = LocallyRingedSpace_adjunction.Unit.app X.1 :=
  by
  rw [← adjunction.hom_equiv_id, ← adjunction.hom_equiv_id, adjunction_hom_equiv_apply]
  rfl

attribute [local semireducible] LocallyRingedSpace_adjunction Γ_Spec.adjunction

instance is_iso_LocallyRingedSpace_adjunction_counit : is_iso LocallyRingedSpace_adjunction.counit :=
  is_iso.of_iso_inv _

instance is_iso_adjunction_counit : is_iso Γ_Spec.adjunction.counit := by
  apply nat_iso.is_iso_of_is_iso_app with { instances := ff }
  intro R
  rw [adjunction_counit_app]
  infer_instance

theorem adjunction_unit_app_app_top (X : Scheme) :
    @Eq
      ((Scheme.Spec.obj (op $ X.presheaf.obj (op ⊤))).Presheaf.obj (op ⊤) ⟶
        ((Γ_Spec.adjunction.Unit.app X).1.base _* X.presheaf).obj (op ⊤))
      ((Γ_Spec.adjunction.Unit.app X).val.c.app (op ⊤)) (Spec_Γ_identity.Hom.app (X.presheaf.obj (op ⊤))) :=
  by
  have := congr_app Γ_Spec.adjunction.left_triangle X
  dsimp  at this
  rw [← is_iso.eq_comp_inv] at this
  simp only [Γ_Spec.LocallyRingedSpace_adjunction_counit, nat_trans.op_app, category.id_comp,
    Γ_Spec.adjunction_counit_app] at this
  rw [← op_inv, nat_iso.inv_inv_app, quiver.hom.op_inj.eq_iff] at this
  exact this

end ΓSpec

/-! Immediate consequences of the adjunction. -/


/-- Spec preserves limits. -/
instance : limits.preserves_limits Spec.to_LocallyRingedSpace :=
  Γ_Spec.LocallyRingedSpace_adjunction.rightAdjointPreservesLimits

instance Spec.preserves_limits : limits.preserves_limits Scheme.Spec :=
  Γ_Spec.adjunction.rightAdjointPreservesLimits

/-- Spec is a full functor. -/
instance : full Spec.to_LocallyRingedSpace :=
  R_full_of_counit_is_iso Γ_Spec.LocallyRingedSpace_adjunction

instance Spec.full : full Scheme.Spec :=
  R_full_of_counit_is_iso Γ_Spec.adjunction

/-- Spec is a faithful functor. -/
instance : faithful Spec.to_LocallyRingedSpace :=
  R_faithful_of_counit_is_iso Γ_Spec.LocallyRingedSpace_adjunction

instance Spec.faithful : faithful Scheme.Spec :=
  R_faithful_of_counit_is_iso Γ_Spec.adjunction

instance : is_right_adjoint Spec.to_LocallyRingedSpace :=
  ⟨_, Γ_Spec.LocallyRingedSpace_adjunction⟩

instance : is_right_adjoint Scheme.Spec :=
  ⟨_, Γ_Spec.adjunction⟩

instance : reflective Spec.to_LocallyRingedSpace :=
  ⟨⟩

instance Spec.reflective : reflective Scheme.Spec :=
  ⟨⟩

end AlgebraicGeometry

