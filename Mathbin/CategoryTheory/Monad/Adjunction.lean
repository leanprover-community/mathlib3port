import Mathbin.CategoryTheory.Adjunction.Reflective
import Mathbin.CategoryTheory.Monad.Algebra

namespace CategoryTheory

open Category

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {L : C ⥤ D} {R : D ⥤ C}

namespace Adjunction

/-- For a pair of functors `L : C ⥤ D`, `R : D ⥤ C`, an adjunction `h : L ⊣ R` induces a monad on
the category `C`.
-/
@[simps]
def to_monad (h : L ⊣ R) : Monad C where
  toFunctor := L ⋙ R
  η' := h.Unit
  μ' := whiskerRight (whiskerLeft L h.counit) R
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
def to_comonad (h : L ⊣ R) : Comonad D where
  toFunctor := R ⋙ L
  ε' := h.counit
  δ' := whiskerRight (whiskerLeft R h.Unit) L
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
def adj_to_monad_iso (T : Monad C) : T.adj.toMonad ≅ T :=
  MonadIso.mk
    (NatIso.ofComponents (fun X => Iso.refl _)
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
def adj_to_comonad_iso (G : Comonad C) : G.adj.toComonad ≅ G :=
  ComonadIso.mk
    (NatIso.ofComponents (fun X => Iso.refl _)
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
def monad.comparison (h : L ⊣ R) : D ⥤ h.toMonad.Algebra where
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
def monad.comparison_forget (h : L ⊣ R) : Monad.comparison h ⋙ h.toMonad.forget ≅ R where
  Hom := { app := fun X => 𝟙 _ }
  inv := { app := fun X => 𝟙 _ }

theorem monad.left_comparison (h : L ⊣ R) : L ⋙ Monad.comparison h = h.toMonad.free :=
  rfl

instance [Faithful R] (h : L ⊣ R) : Faithful (Monad.comparison h) where
  map_injective' := fun X Y f g w => R.map_injective (congr_argₓ Monad.Algebra.Hom.f w : _)

instance (T : Monad C) : Full (Monad.comparison T.adj) where
  Preimage := fun X Y f =>
    ⟨f.f, by
      simpa using f.h⟩

instance (T : Monad C) : EssSurj (Monad.comparison T.adj) where
  mem_ess_image := fun X =>
    ⟨{ a := X.a, a := X.a,
        unit' := by
          simpa using X.unit,
        assoc' := by
          simpa using X.assoc },
      ⟨Monad.Algebra.isoMk (Iso.refl _)
          (by
            simp )⟩⟩

/-- Gven any adjunction `L ⊣ R`, there is a comparison functor `category_theory.comonad.comparison L`
sending objects `X : C` to Eilenberg-Moore coalgebras for `L ⋙ R` with underlying object
`L.obj X`.
-/
@[simps]
def comonad.comparison (h : L ⊣ R) : C ⥤ h.toComonad.Coalgebra where
  obj := fun X =>
    { a := L.obj X, a := L.map (h.Unit.app X),
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
def comonad.comparison_forget {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) : Comonad.comparison h ⋙ h.toComonad.forget ≅ L where
  Hom := { app := fun X => 𝟙 _ }
  inv := { app := fun X => 𝟙 _ }

theorem comonad.left_comparison (h : L ⊣ R) : R ⋙ Comonad.comparison h = h.toComonad.cofree :=
  rfl

instance comonad.comparison_faithful_of_faithful [Faithful L] (h : L ⊣ R) : Faithful (Comonad.comparison h) where
  map_injective' := fun X Y f g w => L.map_injective (congr_argₓ Comonad.Coalgebra.Hom.f w : _)

instance (G : Comonad C) : Full (Comonad.comparison G.adj) where
  Preimage := fun X Y f =>
    ⟨f.f, by
      simpa using f.h⟩

instance (G : Comonad C) : EssSurj (Comonad.comparison G.adj) where
  mem_ess_image := fun X =>
    ⟨{ a := X.a, a := X.a,
        counit' := by
          simpa using X.counit,
        coassoc' := by
          simpa using X.coassoc },
      ⟨Comonad.Coalgebra.isoMk (Iso.refl _)
          (by
            simp )⟩⟩

/-- A right adjoint functor `R : D ⥤ C` is *monadic* if the comparison functor `monad.comparison R`
from `D` to the category of Eilenberg-Moore algebras for the adjunction is an equivalence.
-/
class monadic_right_adjoint (R : D ⥤ C) extends IsRightAdjoint R where
  eqv : IsEquivalence (Monad.comparison (Adjunction.ofRightAdjoint R))

/-- A left adjoint functor `L : C ⥤ D` is *comonadic* if the comparison functor `comonad.comparison L`
from `C` to the category of Eilenberg-Moore algebras for the adjunction is an equivalence.
-/
class comonadic_left_adjoint (L : C ⥤ D) extends IsLeftAdjoint L where
  eqv : IsEquivalence (Comonad.comparison (Adjunction.ofLeftAdjoint L))

noncomputable instance (T : Monad C) : MonadicRightAdjoint T.forget :=
  ⟨(Equivalence.ofFullyFaithfullyEssSurj _ : IsEquivalence (Monad.comparison T.adj))⟩

noncomputable instance (G : Comonad C) : ComonadicLeftAdjoint G.forget :=
  ⟨(Equivalence.ofFullyFaithfullyEssSurj _ : IsEquivalence (Comonad.comparison G.adj))⟩

instance μ_iso_of_reflective [Reflective R] : IsIso (Adjunction.ofRightAdjoint R).toMonad.μ := by
  dsimp
  infer_instance

attribute [instance] monadic_right_adjoint.eqv

attribute [instance] comonadic_left_adjoint.eqv

namespace Reflective

instance [Reflective R] (X : (Adjunction.ofRightAdjoint R).toMonad.Algebra) :
    IsIso ((Adjunction.ofRightAdjoint R).Unit.app X.a) :=
  ⟨⟨X.a,
      ⟨X.Unit, by
        dsimp only [functor.id_obj]
        rw [← (adjunction.of_right_adjoint R).unit_naturality]
        dsimp only [functor.comp_obj, adjunction.to_monad_coe]
        rw [unit_obj_eq_map_unit, ← functor.map_comp, ← functor.map_comp]
        erw [X.unit]
        simp ⟩⟩⟩

instance comparison_ess_surj [Reflective R] : EssSurj (Monad.comparison (Adjunction.ofRightAdjoint R)) := by
  refine' ⟨fun X => ⟨(left_adjoint R).obj X.a, ⟨_⟩⟩⟩
  symm
  refine' monad.algebra.iso_mk _ _
  · exact as_iso ((adjunction.of_right_adjoint R).Unit.app X.A)
    
  dsimp only [functor.comp_map, monad.comparison_obj_a, as_iso_hom, functor.comp_obj, monad.comparison_obj_A,
    monad_to_functor_eq_coe, adjunction.to_monad_coe]
  rw [← cancel_epi ((adjunction.of_right_adjoint R).Unit.app X.A), adjunction.unit_naturality_assoc,
    adjunction.right_triangle_components, comp_id]
  apply (X.unit_assoc _).symm

instance comparison_full [Full R] [IsRightAdjoint R] : Full (Monad.comparison (Adjunction.ofRightAdjoint R)) where
  Preimage := fun X Y f => R.Preimage f.f

end Reflective

/-- Any reflective inclusion has a monadic right adjoint.
    cf Prop 5.3.3 of [Riehl][riehl2017] -/
noncomputable instance (priority := 100) monadic_of_reflective [Reflective R] : MonadicRightAdjoint R where
  eqv := Equivalence.ofFullyFaithfullyEssSurj _

end CategoryTheory

