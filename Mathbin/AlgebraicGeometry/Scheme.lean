import Mathbin.AlgebraicGeometry.Spec

/-!
# The category of schemes

A scheme is a locally ringed space such that every point is contained in some open set
where there is an isomorphism of presheaves between the restriction to that open set,
and the structure sheaf of `Spec R`, for some commutative ring `R`.

A morphism of schemes is just a morphism of the underlying locally ringed spaces.

-/


noncomputable section

open TopologicalSpace

open CategoryTheory

open Top

open Opposite

namespace AlgebraicGeometry

-- ././Mathport/Syntax/Translate/Basic.lean:1165:11: unsupported: advanced extends in structure
/-- We define `Scheme` as a `X : LocallyRingedSpace`,
along with a proof that every point has an open neighbourhood `U`
so that that the restriction of `X` to `U` is isomorphic,
as a locally ringed space, to `Spec.to_LocallyRingedSpace.obj (op R)`
for some `R : CommRing`.
-/
structure Scheme extends
  "././Mathport/Syntax/Translate/Basic.lean:1165:11: unsupported: advanced extends in structure" where
  local_affine :
    ∀ x : to_LocallyRingedSpace,
      ∃ (U : open_nhds x)(R : CommRingₓₓ),
        Nonempty (to_LocallyRingedSpace.restrict U.open_embedding ≅ Spec.to_LocallyRingedSpace.obj (op R))

namespace Scheme

/-- Schemes are a full subcategory of locally ringed spaces.
-/
instance : category Scheme :=
  induced_category.category Scheme.to_LocallyRingedSpace

/-- The structure sheaf of a Scheme. -/
protected abbrev sheaf (X : Scheme) :=
  X.to_SheafedSpace.sheaf

/-- The forgetful functor from `Scheme` to `LocallyRingedSpace`. -/
@[simps]
def forget_to_LocallyRingedSpace : Scheme ⥤ LocallyRingedSpace :=
  induced_functor _ deriving full, faithful

@[simp]
theorem forget_to_LocallyRingedSpace_preimage {X Y : Scheme} (f : X ⟶ Y) :
    Scheme.forget_to_LocallyRingedSpace.Preimage f = f :=
  rfl

/-- The forgetful functor from `Scheme` to `Top`. -/
@[simps]
def forget_to_Top : Scheme ⥤ Top :=
  Scheme.forget_to_LocallyRingedSpace ⋙ LocallyRingedSpace.forget_to_Top

instance {X Y : Scheme} : HasLiftT (X ⟶ Y) (X.to_SheafedSpace ⟶ Y.to_SheafedSpace) :=
  @coeToLift $ @coeBaseₓ coeSubtype

@[reassoc]
theorem comp_val {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).val = f.val ≫ g.val :=
  rfl

@[reassoc, simp]
theorem comp_coe_base {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (↑(f ≫ g) : X.to_SheafedSpace ⟶ Z.to_SheafedSpace).base = f.val.base ≫ g.val.base :=
  rfl

@[reassoc]
theorem comp_val_base {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).val.base = f.val.base ≫ g.val.base :=
  rfl

@[reassoc, simp]
theorem comp_val_c_app {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) U :
    (f ≫ g).val.c.app U = g.val.c.app U ≫ f.val.c.app _ :=
  rfl

theorem congr_app {X Y : Scheme} {f g : X ⟶ Y} (e : f = g) U :
    f.val.c.app U =
      g.val.c.app U ≫
        X.presheaf.map
          (eq_to_hom
            (by
              subst e)) :=
  by
  subst e
  dsimp
  simp

instance is_LocallyRingedSpace_iso {X Y : Scheme} (f : X ⟶ Y) [is_iso f] : @is_iso LocallyRingedSpace _ _ _ f :=
  forget_to_LocallyRingedSpace.map_is_iso f

/-- The spectrum of a commutative ring, as a scheme.
-/
def Spec_obj (R : CommRingₓₓ) : Scheme where
  local_affine := fun x => ⟨⟨⊤, trivialₓ⟩, R, ⟨(Spec.to_LocallyRingedSpace.obj (op R)).restrictTopIso⟩⟩
  toLocallyRingedSpace := Spec.LocallyRingedSpace_obj R

@[simp]
theorem Spec_obj_to_LocallyRingedSpace (R : CommRingₓₓ) :
    (Spec_obj R).toLocallyRingedSpace = Spec.LocallyRingedSpace_obj R :=
  rfl

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of schemes.
-/
def Spec_map {R S : CommRingₓₓ} (f : R ⟶ S) : Spec_obj S ⟶ Spec_obj R :=
  (Spec.LocallyRingedSpace_map f : Spec.LocallyRingedSpace_obj S ⟶ Spec.LocallyRingedSpace_obj R)

@[simp]
theorem Spec_map_id (R : CommRingₓₓ) : Spec_map (𝟙 R) = 𝟙 (Spec_obj R) :=
  Spec.LocallyRingedSpace_map_id R

theorem Spec_map_comp {R S T : CommRingₓₓ} (f : R ⟶ S) (g : S ⟶ T) : Spec_map (f ≫ g) = Spec_map g ≫ Spec_map f :=
  Spec.LocallyRingedSpace_map_comp f g

/-- The spectrum, as a contravariant functor from commutative rings to schemes.
-/
@[simps]
def Spec : CommRingₓₓᵒᵖ ⥤ Scheme where
  obj := fun R => Spec_obj (unop R)
  map := fun R S f => Spec_map f.unop
  map_id' := fun R => by
    rw [unop_id, Spec_map_id]
  map_comp' := fun R S T f g => by
    rw [unop_comp, Spec_map_comp]

/-- The empty scheme, as `Spec 0`.
-/
def Empty : Scheme :=
  Spec_obj (CommRingₓₓ.of PUnit)

instance : HasEmptyc Scheme :=
  ⟨Empty⟩

instance : Inhabited Scheme :=
  ⟨∅⟩

/-- The global sections, notated Gamma.
-/
def Γ : Schemeᵒᵖ ⥤ CommRingₓₓ :=
  (induced_functor Scheme.to_LocallyRingedSpace).op ⋙ LocallyRingedSpace.Γ

theorem Γ_def : Γ = (induced_functor Scheme.to_LocallyRingedSpace).op ⋙ LocallyRingedSpace.Γ :=
  rfl

@[simp]
theorem Γ_obj (X : Schemeᵒᵖ) : Γ.obj X = (unop X).Presheaf.obj (op ⊤) :=
  rfl

theorem Γ_obj_op (X : Scheme) : Γ.obj (op X) = X.presheaf.obj (op ⊤) :=
  rfl

@[simp]
theorem Γ_map {X Y : Schemeᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.1.c.app (op ⊤) :=
  rfl

theorem Γ_map_op {X Y : Scheme} (f : X ⟶ Y) : Γ.map f.op = f.1.c.app (op ⊤) :=
  rfl

section BasicOpen

variable (X : Scheme) {V U : opens X.carrier} (f g : X.presheaf.obj (op U))

/-- The subset of the underlying space where the given section does not vanish. -/
def basic_open : opens X.carrier :=
  X.to_LocallyRingedSpace.to_RingedSpace.basic_open f

@[simp]
theorem mem_basic_open (x : U) : ↑x ∈ X.basic_open f ↔ IsUnit (X.presheaf.germ x f) :=
  RingedSpace.mem_basic_open _ _ _

@[simp]
theorem mem_basic_open_top (f : X.presheaf.obj (op ⊤)) (x : X.carrier) :
    x ∈ X.basic_open f ↔ IsUnit (X.presheaf.germ (⟨x, trivialₓ⟩ : (⊤ : opens _)) f) :=
  RingedSpace.mem_basic_open _ f ⟨x, trivialₓ⟩

@[simp]
theorem basic_open_res (i : op U ⟶ op V) : X.basic_open (X.presheaf.map i f) = V ∩ X.basic_open f :=
  RingedSpace.basic_open_res _ i f

@[simp]
theorem basic_open_res_eq (i : op U ⟶ op V) [is_iso i] : X.basic_open (X.presheaf.map i f) = X.basic_open f :=
  RingedSpace.basic_open_res_eq _ i f

theorem basic_open_subset : X.basic_open f ⊆ U :=
  RingedSpace.basic_open_subset _ _

theorem preimage_basic_open {X Y : Scheme} (f : X ⟶ Y) {U : opens Y.carrier} (r : Y.presheaf.obj $ op U) :
    (opens.map f.1.base).obj (Y.basic_open r) = @Scheme.basic_open X ((opens.map f.1.base).obj U) (f.1.c.app _ r) :=
  LocallyRingedSpace.preimage_basic_open f r

@[simp]
theorem preimage_basic_open' {X Y : Scheme} (f : X ⟶ Y) {U : opens Y.carrier} (r : Y.presheaf.obj $ op U) :
    (opens.map (↑f : X.to_SheafedSpace ⟶ Y.to_SheafedSpace).base).obj (Y.basic_open r) =
      @Scheme.basic_open X ((opens.map f.1.base).obj U) (f.1.c.app _ r) :=
  LocallyRingedSpace.preimage_basic_open f r

@[simp]
theorem basic_open_zero (U : opens X.carrier) : X.basic_open (0 : X.presheaf.obj $ op U) = ∅ :=
  LocallyRingedSpace.basic_open_zero _ U

@[simp]
theorem basic_open_mul : X.basic_open (f * g) = X.basic_open f⊓X.basic_open g :=
  RingedSpace.basic_open_mul _ _ _

@[simp]
theorem basic_open_of_is_unit {f : X.presheaf.obj (op U)} (hf : IsUnit f) : X.basic_open f = U :=
  RingedSpace.basic_open_of_is_unit _ hf

end BasicOpen

end Scheme

theorem basic_open_eq_of_affine {R : CommRingₓₓ} (f : R) :
    (Scheme.Spec.obj $ op R).basicOpen ((Spec_Γ_identity.app R).inv f) = PrimeSpectrum.basicOpen f := by
  ext
  erw [Scheme.mem_basic_open_top]
  suffices IsUnit (structure_sheaf.to_stalk R x f) ↔ f ∉ PrimeSpectrum.asIdeal x by
    exact this
  erw [← is_unit_map_iff (structure_sheaf.stalk_to_fiber_ring_hom R x),
    structure_sheaf.stalk_to_fiber_ring_hom_to_stalk]
  exact
    (IsLocalization.AtPrime.is_unit_to_map_iff (Localization.AtPrime (PrimeSpectrum.asIdeal x))
      (PrimeSpectrum.asIdeal x) f :
      _)

@[simp]
theorem basic_open_eq_of_affine' {R : CommRingₓₓ} (f : (Spec.to_SheafedSpace.obj (op R)).Presheaf.obj (op ⊤)) :
    (Scheme.Spec.obj $ op R).basicOpen f = PrimeSpectrum.basicOpen ((Spec_Γ_identity.app R).Hom f) := by
  convert basic_open_eq_of_affine ((Spec_Γ_identity.app R).Hom f)
  exact (coe_hom_inv_id _ _).symm

end AlgebraicGeometry

