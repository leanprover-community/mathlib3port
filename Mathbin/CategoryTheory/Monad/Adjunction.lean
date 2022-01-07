import Mathbin.CategoryTheory.Adjunction.Reflective
import Mathbin.CategoryTheory.Monad.Algebra

namespace CategoryTheory

open Category

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

variable {L : C ⥤ D} {R : D ⥤ C}

namespace Adjunction

/-- For a pair of functors `L : C ⥤ D`, `R : D ⥤ C`, an adjunction `h : L ⊣ R` induces a monad on
the category `C`.
-/
@[simps]
def to_monad (h : L ⊣ R) : Monadₓ C where
  toFunctor := L ⋙ R
  η' := h.unit
  μ' := whisker_right (whisker_left L h.counit) R
  assoc' := fun X => by
    dsimp
    rw [← R.map_comp]
    simp
  right_unit' := fun X => by
    dsimp
    rw [← R.map_comp]
    simp

/-- For a pair of functors `L : C ⥤ D`, `R : D ⥤ C`, an adjunction `h : L ⊣ R` induces a comonad on
the category `D`.
-/
@[simps]
def to_comonad (h : L ⊣ R) : comonad D where
  toFunctor := R ⋙ L
  ε' := h.counit
  δ' := whisker_right (whisker_left R h.unit) L
  coassoc' := fun X => by
    dsimp
    rw [← L.map_comp]
    simp
  right_counit' := fun X => by
    dsimp
    rw [← L.map_comp]
    simp

/-- The monad induced by the Eilenberg-Moore adjunction is the original monad.  -/
@[simps]
def adj_to_monad_iso (T : Monadₓ C) : T.adj.to_monad ≅ T :=
  monad_iso.mk
    (nat_iso.of_components (fun X => iso.refl _)
      (by
        tidy))
    (fun X => by
      dsimp
      simp )
    fun X => by
    dsimp
    simp

/-- The comonad induced by the Eilenberg-Moore adjunction is the original comonad. -/
@[simps]
def adj_to_comonad_iso (G : comonad C) : G.adj.to_comonad ≅ G :=
  comonad_iso.mk
    (nat_iso.of_components (fun X => iso.refl _)
      (by
        tidy))
    (fun X => by
      dsimp
      simp )
    fun X => by
    dsimp
    simp

end Adjunction

/-- Gven any adjunction `L ⊣ R`, there is a comparison functor `category_theory.monad.comparison R`
sending objects `Y : D` to Eilenberg-Moore algebras for `L ⋙ R` with underlying object `R.obj X`.

We later show that this is full when `R` is full, faithful when `R` is faithful,
and essentially surjective when `R` is reflective.
-/
@[simps]
def monad.comparison (h : L ⊣ R) : D ⥤ h.to_monad.algebra where
  obj := fun X =>
    { a := R.obj X, a := R.map (h.counit.app X),
      assoc' := by
        dsimp
        rw [← R.map_comp, ← adjunction.counit_naturality, R.map_comp]
        rfl }
  map := fun X Y f =>
    { f := R.map f,
      h' := by
        dsimp
        rw [← R.map_comp, adjunction.counit_naturality, R.map_comp] }

/-- The underlying object of `(monad.comparison R).obj X` is just `R.obj X`.
-/
@[simps]
def monad.comparison_forget (h : L ⊣ R) : monad.comparison h ⋙ h.to_monad.forget ≅ R where
  Hom := { app := fun X => 𝟙 _ }
  inv := { app := fun X => 𝟙 _ }

theorem monad.left_comparison (h : L ⊣ R) : L ⋙ monad.comparison h = h.to_monad.free :=
  rfl

instance [faithful R] (h : L ⊣ R) : faithful (monad.comparison h) where
  map_injective' := fun X Y f g w => R.map_injective (congr_argₓ monad.algebra.hom.f w : _)

instance (T : Monadₓ C) : full (monad.comparison T.adj) where
  Preimage := fun X Y f =>
    ⟨f.f, by
      simpa using f.h⟩

instance (T : Monadₓ C) : ess_surj (monad.comparison T.adj) where
  mem_ess_image := fun X =>
    ⟨{ a := X.A, a := X.a,
        unit' := by
          simpa using X.unit,
        assoc' := by
          simpa using X.assoc },
      ⟨monad.algebra.iso_mk (iso.refl _)
          (by
            simp )⟩⟩

/-- Gven any adjunction `L ⊣ R`, there is a comparison functor `category_theory.comonad.comparison L`
sending objects `X : C` to Eilenberg-Moore coalgebras for `L ⋙ R` with underlying object
`L.obj X`.
-/
@[simps]
def comonad.comparison (h : L ⊣ R) : C ⥤ h.to_comonad.coalgebra where
  obj := fun X =>
    { a := L.obj X, a := L.map (h.unit.app X),
      coassoc' := by
        dsimp
        rw [← L.map_comp, ← adjunction.unit_naturality, L.map_comp]
        rfl }
  map := fun X Y f =>
    { f := L.map f,
      h' := by
        dsimp
        rw [← L.map_comp]
        simp }

/-- The underlying object of `(comonad.comparison L).obj X` is just `L.obj X`.
-/
@[simps]
def comonad.comparison_forget {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) : comonad.comparison h ⋙ h.to_comonad.forget ≅ L where
  Hom := { app := fun X => 𝟙 _ }
  inv := { app := fun X => 𝟙 _ }

theorem comonad.left_comparison (h : L ⊣ R) : R ⋙ comonad.comparison h = h.to_comonad.cofree :=
  rfl

instance comonad.comparison_faithful_of_faithful [faithful L] (h : L ⊣ R) : faithful (comonad.comparison h) where
  map_injective' := fun X Y f g w => L.map_injective (congr_argₓ comonad.coalgebra.hom.f w : _)

instance (G : comonad C) : full (comonad.comparison G.adj) where
  Preimage := fun X Y f =>
    ⟨f.f, by
      simpa using f.h⟩

instance (G : comonad C) : ess_surj (comonad.comparison G.adj) where
  mem_ess_image := fun X =>
    ⟨{ a := X.A, a := X.a,
        counit' := by
          simpa using X.counit,
        coassoc' := by
          simpa using X.coassoc },
      ⟨comonad.coalgebra.iso_mk (iso.refl _)
          (by
            simp )⟩⟩

/-- A right adjoint functor `R : D ⥤ C` is *monadic* if the comparison functor `monad.comparison R`
from `D` to the category of Eilenberg-Moore algebras for the adjunction is an equivalence.
-/
class monadic_right_adjoint (R : D ⥤ C) extends is_right_adjoint R where
  eqv : is_equivalence (monad.comparison (adjunction.of_right_adjoint R))

/-- A left adjoint functor `L : C ⥤ D` is *comonadic* if the comparison functor `comonad.comparison L`
from `C` to the category of Eilenberg-Moore algebras for the adjunction is an equivalence.
-/
class comonadic_left_adjoint (L : C ⥤ D) extends is_left_adjoint L where
  eqv : is_equivalence (comonad.comparison (adjunction.of_left_adjoint L))

noncomputable instance (T : Monadₓ C) : monadic_right_adjoint T.forget :=
  ⟨(equivalence.of_fully_faithfully_ess_surj _ : is_equivalence (monad.comparison T.adj))⟩

noncomputable instance (G : comonad C) : comonadic_left_adjoint G.forget :=
  ⟨(equivalence.of_fully_faithfully_ess_surj _ : is_equivalence (comonad.comparison G.adj))⟩

instance μ_iso_of_reflective [reflective R] : is_iso (adjunction.of_right_adjoint R).toMonad.μ := by
  dsimp
  infer_instance

attribute [instance] monadic_right_adjoint.eqv

attribute [instance] comonadic_left_adjoint.eqv

namespace Reflective

instance [reflective R] (X : (adjunction.of_right_adjoint R).toMonad.Algebra) :
    is_iso ((adjunction.of_right_adjoint R).Unit.app X.A) :=
  ⟨⟨X.a,
      ⟨X.unit, by
        dsimp only [functor.id_obj]
        rw [← (adjunction.of_right_adjoint R).unit_naturality]
        dsimp only [functor.comp_obj, adjunction.to_monad_coe]
        rw [unit_obj_eq_map_unit, ← functor.map_comp, ← functor.map_comp]
        erw [X.unit]
        simp ⟩⟩⟩

instance comparison_ess_surj [reflective R] : ess_surj (monad.comparison (adjunction.of_right_adjoint R)) := by
  refine' ⟨fun X => ⟨(left_adjoint R).obj X.A, ⟨_⟩⟩⟩
  symm
  refine' monad.algebra.iso_mk _ _
  · exact as_iso ((adjunction.of_right_adjoint R).Unit.app X.A)
    
  dsimp only [functor.comp_map, monad.comparison_obj_a, as_iso_hom, functor.comp_obj, monad.comparison_obj_A,
    monad_to_functor_eq_coe, adjunction.to_monad_coe]
  rw [← cancel_epi ((adjunction.of_right_adjoint R).Unit.app X.A), adjunction.unit_naturality_assoc,
    adjunction.right_triangle_components, comp_id]
  apply (X.unit_assoc _).symm

instance comparison_full [full R] [is_right_adjoint R] : full (monad.comparison (adjunction.of_right_adjoint R)) where
  Preimage := fun X Y f => R.preimage f.f

end Reflective

/-- Any reflective inclusion has a monadic right adjoint.
    cf Prop 5.3.3 of [Riehl][riehl2017] -/
noncomputable instance (priority := 100) monadic_of_reflective [reflective R] : monadic_right_adjoint R where
  eqv := equivalence.of_fully_faithfully_ess_surj _

end CategoryTheory

