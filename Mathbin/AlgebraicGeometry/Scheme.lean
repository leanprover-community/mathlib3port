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

-- ././Mathport/Syntax/Translate/Basic.lean:1141:11: unsupported: advanced extends in structure
/-- 
We define `Scheme` as a `X : LocallyRingedSpace`,
along with a proof that every point has an open neighbourhood `U`
so that that the restriction of `X` to `U` is isomorphic,
as a locally ringed space, to `Spec.to_LocallyRingedSpace.obj (op R)`
for some `R : CommRing`.
-/
structure Scheme extends
  "././Mathport/Syntax/Translate/Basic.lean:1141:11: unsupported: advanced extends in structure" where
  local_affine :
    ∀ x : X,
      ∃ (U : open_nhds x)(R : CommRingₓₓ),
        Nonempty (X.restrict U.open_embedding ≅ Spec.to_LocallyRingedSpace.obj (op R))

namespace Scheme

/-- 
Every `Scheme` is a `LocallyRingedSpace`.
-/
def to_LocallyRingedSpace (S : Scheme) : LocallyRingedSpace :=
  { S with }

/-- 
Schemes are a full subcategory of locally ringed spaces.
-/
instance : category Scheme :=
  induced_category.category Scheme.to_LocallyRingedSpace

/--  The structure sheaf of a Scheme. -/
protected abbrev sheaf (X : Scheme) :=
  X.to_SheafedSpace.sheaf

/-- 
The spectrum of a commutative ring, as a scheme.
-/
def Spec_obj (R : CommRingₓₓ) : Scheme :=
  { Spec.LocallyRingedSpace_obj R with
    local_affine := fun x => ⟨⟨⊤, trivialₓ⟩, R, ⟨(Spec.to_LocallyRingedSpace.obj (op R)).restrictTopIso⟩⟩ }

@[simp]
theorem Spec_obj_to_LocallyRingedSpace (R : CommRingₓₓ) :
    (Spec_obj R).toLocallyRingedSpace = Spec.LocallyRingedSpace_obj R :=
  rfl

/-- 
The induced map of a ring homomorphism on the ring spectra, as a morphism of schemes.
-/
def Spec_map {R S : CommRingₓₓ} (f : R ⟶ S) : Spec_obj S ⟶ Spec_obj R :=
  (Spec.LocallyRingedSpace_map f : Spec.LocallyRingedSpace_obj S ⟶ Spec.LocallyRingedSpace_obj R)

@[simp]
theorem Spec_map_id (R : CommRingₓₓ) : Spec_map (𝟙 R) = 𝟙 (Spec_obj R) :=
  Spec.LocallyRingedSpace_map_id R

theorem Spec_map_comp {R S T : CommRingₓₓ} (f : R ⟶ S) (g : S ⟶ T) : Spec_map (f ≫ g) = Spec_map g ≫ Spec_map f :=
  Spec.LocallyRingedSpace_map_comp f g

/-- 
The spectrum, as a contravariant functor from commutative rings to schemes.
-/
@[simps]
def Spec : CommRingₓₓᵒᵖ ⥤ Scheme :=
  { obj := fun R => Spec_obj (unop R), map := fun R S f => Spec_map f.unop,
    map_id' := fun R => by
      rw [unop_id, Spec_map_id],
    map_comp' := fun R S T f g => by
      rw [unop_comp, Spec_map_comp] }

/-- 
The empty scheme, as `Spec 0`.
-/
def Empty : Scheme :=
  Spec_obj (CommRingₓₓ.of PUnit)

instance : HasEmptyc Scheme :=
  ⟨Empty⟩

instance : Inhabited Scheme :=
  ⟨∅⟩

/-- 
The global sections, notated Gamma.
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

end Scheme

end AlgebraicGeometry

