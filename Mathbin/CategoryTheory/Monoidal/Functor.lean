/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison, Bhavik Mehta
-/
import Mathbin.CategoryTheory.Monoidal.Category
import Mathbin.CategoryTheory.Adjunction.Basic
import Mathbin.CategoryTheory.Products.Basic

/-!
# (Lax) monoidal functors

A lax monoidal functor `F` between monoidal categories `C` and `D`
is a functor between the underlying categories equipped with morphisms
* `Īµ : š_ D ā¶ F.obj (š_ C)` (called the unit morphism)
* `Ī¼ X Y : (F.obj X) ā (F.obj Y) ā¶ F.obj (X ā Y)` (called the tensorator, or strength).
satisfying various axioms.

A monoidal functor is a lax monoidal functor for which `Īµ` and `Ī¼` are isomorphisms.

We show that the composition of (lax) monoidal functors gives a (lax) monoidal functor.

See also `category_theory.monoidal.functorial` for a typeclass decorating an object-level
function with the additional data of a monoidal functor.
This is useful when stating that a pre-existing functor is monoidal.

See `category_theory.monoidal.natural_transformation` for monoidal natural transformations.

We show in `category_theory.monoidal.Mon_` that lax monoidal functors take monoid objects
to monoid objects.

## Future work
* Oplax monoidal functors.

## References

See <https://stacks.math.columbia.edu/tag/0FFL>.
-/


open CategoryTheory

universe vā vā vā uā uā uā

open CategoryTheory.Category

open CategoryTheory.Functor

namespace CategoryTheory

section

open MonoidalCategory

variable (C : Type uā) [Category.{vā} C] [MonoidalCategory.{vā} C] (D : Type uā) [Category.{vā} D]
  [MonoidalCategory.{vā} D]

/-- A lax monoidal functor is a functor `F : C ā„¤ D` between monoidal categories,
equipped with morphisms `Īµ : š _D ā¶ F.obj (š_ C)` and `Ī¼ X Y : F.obj X ā F.obj Y ā¶ F.obj (X ā Y)`,
satisfying the appropriate coherences. -/
-- The direction of `left_unitality` and `right_unitality` as simp lemmas may look strange:
-- remember the rule of thumb that component indices of natural transformations
-- "weigh more" than structural maps.
-- (However by this argument `associativity` is currently stated backwards!)
structure LaxMonoidalFunctor extends C ā„¤ D where
  -- unit morphism
  Īµ : š_ D ā¶ obj (š_ C)
  -- tensorator
  Ī¼ : ā X Y : C, obj X ā obj Y ā¶ obj (X ā Y)
  Ī¼_natural' : ā {X Y X' Y' : C} (f : X ā¶ Y) (g : X' ā¶ Y'), (map f ā map g) ā« Ī¼ Y Y' = Ī¼ X X' ā« map (f ā g) := by
    run_tac
      obviously
  -- associativity of the tensorator
  associativity' :
    ā X Y Z : C,
      (Ī¼ X Y ā š (obj Z)) ā« Ī¼ (X ā Y) Z ā« map (Ī±_ X Y Z).Hom =
        (Ī±_ (obj X) (obj Y) (obj Z)).Hom ā« (š (obj X) ā Ī¼ Y Z) ā« Ī¼ X (Y ā Z) := by
    run_tac
      obviously
  -- unitality
  left_unitality' : ā X : C, (Ī»_ (obj X)).Hom = (Īµ ā š (obj X)) ā« Ī¼ (š_ C) X ā« map (Ī»_ X).Hom := by
    run_tac
      obviously
  right_unitality' : ā X : C, (Ļ_ (obj X)).Hom = (š (obj X) ā Īµ) ā« Ī¼ X (š_ C) ā« map (Ļ_ X).Hom := by
    run_tac
      obviously

restate_axiom lax_monoidal_functor.Ī¼_natural'

attribute [simp, reassoc] lax_monoidal_functor.Ī¼_natural

restate_axiom lax_monoidal_functor.left_unitality'

attribute [simp] lax_monoidal_functor.left_unitality

restate_axiom lax_monoidal_functor.right_unitality'

attribute [simp] lax_monoidal_functor.right_unitality

restate_axiom lax_monoidal_functor.associativity'

attribute [simp, reassoc] lax_monoidal_functor.associativity

-- When `rewrite_search` lands, add @[search] attributes to
-- lax_monoidal_functor.Ī¼_natural lax_monoidal_functor.left_unitality
-- lax_monoidal_functor.right_unitality lax_monoidal_functor.associativity
section

variable {C D}

@[simp, reassoc]
theorem LaxMonoidalFunctor.left_unitality_inv (F : LaxMonoidalFunctor C D) (X : C) :
    (Ī»_ (F.obj X)).inv ā« (F.Īµ ā š (F.obj X)) ā« F.Ī¼ (š_ C) X = F.map (Ī»_ X).inv := by
  rw [iso.inv_comp_eq, F.left_unitality, category.assoc, category.assoc, ā F.to_functor.map_comp, iso.hom_inv_id,
    F.to_functor.map_id, comp_id]

@[simp, reassoc]
theorem LaxMonoidalFunctor.right_unitality_inv (F : LaxMonoidalFunctor C D) (X : C) :
    (Ļ_ (F.obj X)).inv ā« (š (F.obj X) ā F.Īµ) ā« F.Ī¼ X (š_ C) = F.map (Ļ_ X).inv := by
  rw [iso.inv_comp_eq, F.right_unitality, category.assoc, category.assoc, ā F.to_functor.map_comp, iso.hom_inv_id,
    F.to_functor.map_id, comp_id]

@[simp, reassoc]
theorem LaxMonoidalFunctor.associativity_inv (F : LaxMonoidalFunctor C D) (X Y Z : C) :
    (š (F.obj X) ā F.Ī¼ Y Z) ā« F.Ī¼ X (Y ā Z) ā« F.map (Ī±_ X Y Z).inv =
      (Ī±_ (F.obj X) (F.obj Y) (F.obj Z)).inv ā« (F.Ī¼ X Y ā š (F.obj Z)) ā« F.Ī¼ (X ā Y) Z :=
  by
  rw [iso.eq_inv_comp, ā F.associativity_assoc, ā F.to_functor.map_comp, iso.hom_inv_id, F.to_functor.map_id, comp_id]

end

/-- A monoidal functor is a lax monoidal functor for which the tensorator and unitor as isomorphisms.

See <https://stacks.math.columbia.edu/tag/0FFL>.
-/
structure MonoidalFunctor extends LaxMonoidalFunctor.{vā, vā} C D where
  Īµ_is_iso : IsIso Īµ := by
    run_tac
      tactic.apply_instance
  Ī¼_is_iso : ā X Y : C, IsIso (Ī¼ X Y) := by
    run_tac
      tactic.apply_instance

attribute [instance] monoidal_functor.Īµ_is_iso monoidal_functor.Ī¼_is_iso

variable {C D}

/-- The unit morphism of a (strong) monoidal functor as an isomorphism.
-/
noncomputable def MonoidalFunctor.ĪµIso (F : MonoidalFunctor.{vā, vā} C D) : tensorUnit D ā F.obj (tensorUnit C) :=
  asIso F.Īµ

/-- The tensorator of a (strong) monoidal functor as an isomorphism.
-/
noncomputable def MonoidalFunctor.Ī¼Iso (F : MonoidalFunctor.{vā, vā} C D) (X Y : C) :
    F.obj X ā F.obj Y ā F.obj (X ā Y) :=
  asIso (F.Ī¼ X Y)

end

open MonoidalCategory

namespace LaxMonoidalFunctor

variable (C : Type uā) [Category.{vā} C] [MonoidalCategory.{vā} C]

/-- The identity lax monoidal functor. -/
@[simps]
def id : LaxMonoidalFunctor.{vā, vā} C C :=
  { š­ C with Īµ := š _, Ī¼ := fun X Y => š _ }

instance : Inhabited (LaxMonoidalFunctor C C) :=
  āØid Cā©

end LaxMonoidalFunctor

namespace MonoidalFunctor

section

variable {C : Type uā} [Category.{vā} C] [MonoidalCategory.{vā} C]

variable {D : Type uā} [Category.{vā} D] [MonoidalCategory.{vā} D]

variable (F : MonoidalFunctor.{vā, vā} C D)

theorem map_tensor {X Y X' Y' : C} (f : X ā¶ Y) (g : X' ā¶ Y') :
    F.map (f ā g) = inv (F.Ī¼ X X') ā« (F.map f ā F.map g) ā« F.Ī¼ Y Y' := by
  simp

theorem map_left_unitor (X : C) :
    F.map (Ī»_ X).Hom = inv (F.Ī¼ (š_ C) X) ā« (inv F.Īµ ā š (F.obj X)) ā« (Ī»_ (F.obj X)).Hom := by
  simp only [ā lax_monoidal_functor.left_unitality]
  slice_rhs 2 3 => rw [ā comp_tensor_id]simp
  simp

theorem map_right_unitor (X : C) :
    F.map (Ļ_ X).Hom = inv (F.Ī¼ X (š_ C)) ā« (š (F.obj X) ā inv F.Īµ) ā« (Ļ_ (F.obj X)).Hom := by
  simp only [ā lax_monoidal_functor.right_unitality]
  slice_rhs 2 3 => rw [ā id_tensor_comp]simp
  simp

/-- The tensorator as a natural isomorphism. -/
noncomputable def Ī¼NatIso : Functor.prod F.toFunctor F.toFunctor ā tensor D ā tensor C ā F.toFunctor :=
  NatIso.ofComponents
    (by
      intros
      apply F.Ī¼_iso)
    (by
      intros
      apply F.to_lax_monoidal_functor.Ī¼_natural)

@[simp]
theorem Ī¼_iso_hom (X Y : C) : (F.Ī¼Iso X Y).Hom = F.Ī¼ X Y :=
  rfl

@[simp, reassoc]
theorem Ī¼_inv_hom_id (X Y : C) : (F.Ī¼Iso X Y).inv ā« F.Ī¼ X Y = š _ :=
  (F.Ī¼Iso X Y).inv_hom_id

@[simp]
theorem Ī¼_hom_inv_id (X Y : C) : F.Ī¼ X Y ā« (F.Ī¼Iso X Y).inv = š _ :=
  (F.Ī¼Iso X Y).hom_inv_id

@[simp]
theorem Īµ_iso_hom : F.ĪµIso.Hom = F.Īµ :=
  rfl

@[simp, reassoc]
theorem Īµ_inv_hom_id : F.ĪµIso.inv ā« F.Īµ = š _ :=
  F.ĪµIso.inv_hom_id

@[simp]
theorem Īµ_hom_inv_id : F.Īµ ā« F.ĪµIso.inv = š _ :=
  F.ĪµIso.hom_inv_id

end

section

variable (C : Type uā) [Category.{vā} C] [MonoidalCategory.{vā} C]

/-- The identity monoidal functor. -/
@[simps]
def id : MonoidalFunctor.{vā, vā} C C :=
  { š­ C with Īµ := š _, Ī¼ := fun X Y => š _ }

instance : Inhabited (MonoidalFunctor C C) :=
  āØid Cā©

end

end MonoidalFunctor

variable {C : Type uā} [Category.{vā} C] [MonoidalCategory.{vā} C]

variable {D : Type uā} [Category.{vā} D] [MonoidalCategory.{vā} D]

variable {E : Type uā} [Category.{vā} E] [MonoidalCategory.{vā} E]

namespace LaxMonoidalFunctor

variable (F : LaxMonoidalFunctor.{vā, vā} C D) (G : LaxMonoidalFunctor.{vā, vā} D E)

/-- The composition of two lax monoidal functors is again lax monoidal. -/
-- The proofs here are horrendous; rewrite_search helps a lot.
@[simps]
def comp : LaxMonoidalFunctor.{vā, vā} C E :=
  { F.toFunctor ā G.toFunctor with Īµ := G.Īµ ā« G.map F.Īµ, Ī¼ := fun X Y => G.Ī¼ (F.obj X) (F.obj Y) ā« G.map (F.Ī¼ X Y),
    Ī¼_natural' := fun _ _ _ _ f g => by
      simp only [ā functor.comp_map, ā assoc]
      rw [ā category.assoc, lax_monoidal_functor.Ī¼_natural, category.assoc, ā map_comp, ā map_comp, ā
        lax_monoidal_functor.Ī¼_natural],
    associativity' := fun X Y Z => by
      dsimp'
      rw [id_tensor_comp]
      slice_rhs 3 4 => rw [ā G.to_functor.map_id, G.Ī¼_natural]
      slice_rhs 1 3 => rw [ā G.associativity]
      rw [comp_tensor_id]
      slice_lhs 2 3 => rw [ā G.to_functor.map_id, G.Ī¼_natural]
      rw [category.assoc, category.assoc, category.assoc, category.assoc, category.assoc, ā G.to_functor.map_comp, ā
        G.to_functor.map_comp, ā G.to_functor.map_comp, ā G.to_functor.map_comp, F.associativity],
    left_unitality' := fun X => by
      dsimp'
      rw [G.left_unitality, comp_tensor_id, category.assoc, category.assoc]
      apply congr_arg
      rw [F.left_unitality, map_comp, ā nat_trans.id_app, ā category.assoc, ā lax_monoidal_functor.Ī¼_natural,
        nat_trans.id_app, map_id, ā category.assoc, map_comp],
    right_unitality' := fun X => by
      dsimp'
      rw [G.right_unitality, id_tensor_comp, category.assoc, category.assoc]
      apply congr_arg
      rw [F.right_unitality, map_comp, ā nat_trans.id_app, ā category.assoc, ā lax_monoidal_functor.Ī¼_natural,
        nat_trans.id_app, map_id, ā category.assoc, map_comp] }

-- mathport name: Ā«expr āā Ā»
infixr:80 " āā " => comp

end LaxMonoidalFunctor

namespace LaxMonoidalFunctor

universe vā uā

variable {B : Type uā} [Category.{vā} B] [MonoidalCategory.{vā} B]

variable (F : LaxMonoidalFunctor.{vā, vā} B C) (G : LaxMonoidalFunctor.{vā, vā} D E)

attribute [local simp] Ī¼_natural associativity left_unitality right_unitality

/-- The cartesian product of two lax monoidal functors is lax monoidal. -/
@[simps]
def prod : LaxMonoidalFunctor (B Ć D) (C Ć E) :=
  { F.toFunctor.Prod G.toFunctor with Īµ := (Īµ F, Īµ G), Ī¼ := fun X Y => (Ī¼ F X.1 Y.1, Ī¼ G X.2 Y.2) }

end LaxMonoidalFunctor

namespace MonoidalFunctor

variable (C)

/-- The diagonal functor as a monoidal functor. -/
@[simps]
def diag : MonoidalFunctor C (C Ć C) :=
  { Functor.diag C with Īµ := š _, Ī¼ := fun X Y => š _ }

end MonoidalFunctor

namespace LaxMonoidalFunctor

variable (F : LaxMonoidalFunctor.{vā, vā} C D) (G : LaxMonoidalFunctor.{vā, vā} C E)

/-- The cartesian product of two lax monoidal functors starting from the same monoidal category `C`
    is lax monoidal. -/
def prod' : LaxMonoidalFunctor C (D Ć E) :=
  (MonoidalFunctor.diag C).toLaxMonoidalFunctor āā F.Prod G

@[simp]
theorem prod'_to_functor : (F.prod' G).toFunctor = F.toFunctor.prod' G.toFunctor :=
  rfl

@[simp]
theorem prod'_Īµ : (F.prod' G).Īµ = (F.Īµ, G.Īµ) := by
  dsimp' [ā prod']
  simp

@[simp]
theorem prod'_Ī¼ (X Y : C) : (F.prod' G).Ī¼ X Y = (F.Ī¼ X Y, G.Ī¼ X Y) := by
  dsimp' [ā prod']
  simp

end LaxMonoidalFunctor

namespace MonoidalFunctor

variable (F : MonoidalFunctor.{vā, vā} C D) (G : MonoidalFunctor.{vā, vā} D E)

/-- The composition of two monoidal functors is again monoidal. -/
@[simps]
def comp : MonoidalFunctor.{vā, vā} C E :=
  { F.toLaxMonoidalFunctor.comp G.toLaxMonoidalFunctor with
    Īµ_is_iso := by
      dsimp'
      infer_instance,
    Ī¼_is_iso := by
      dsimp'
      infer_instance }

-- mathport name: Ā«expr āā Ā»
infixr:80 " āā " => comp

-- We overload notation; potentially dangerous, but it seems to work.
end MonoidalFunctor

namespace MonoidalFunctor

universe vā uā

variable {B : Type uā} [Category.{vā} B] [MonoidalCategory.{vā} B]

variable (F : MonoidalFunctor.{vā, vā} B C) (G : MonoidalFunctor.{vā, vā} D E)

/-- The cartesian product of two monoidal functors is monoidal. -/
@[simps]
def prod : MonoidalFunctor (B Ć D) (C Ć E) :=
  { F.toLaxMonoidalFunctor.Prod G.toLaxMonoidalFunctor with
    Īµ_is_iso := (is_iso_prod_iff C E).mpr āØĪµ_is_iso F, Īµ_is_iso Gā©,
    Ī¼_is_iso := fun X Y => (is_iso_prod_iff C E).mpr āØĪ¼_is_iso F X.1 Y.1, Ī¼_is_iso G X.2 Y.2ā© }

end MonoidalFunctor

namespace MonoidalFunctor

variable (F : MonoidalFunctor.{vā, vā} C D) (G : MonoidalFunctor.{vā, vā} C E)

/-- The cartesian product of two monoidal functors starting from the same monoidal category `C`
    is monoidal. -/
def prod' : MonoidalFunctor C (D Ć E) :=
  diag C āā F.Prod G

@[simp]
theorem prod'_to_lax_monoidal_functor :
    (F.prod' G).toLaxMonoidalFunctor = F.toLaxMonoidalFunctor.prod' G.toLaxMonoidalFunctor :=
  rfl

end MonoidalFunctor

/-- If we have a right adjoint functor `G` to a monoidal functor `F`, then `G` has a lax monoidal
structure as well.
-/
@[simps]
noncomputable def monoidalAdjoint (F : MonoidalFunctor C D) {G : D ā„¤ C} (h : F.toFunctor ā£ G) :
    LaxMonoidalFunctor D C where
  toFunctor := G
  Īµ := h.homEquiv _ _ (inv F.Īµ)
  Ī¼ := fun X Y => h.homEquiv _ (X ā Y) (inv (F.Ī¼ (G.obj X) (G.obj Y)) ā« (h.counit.app X ā h.counit.app Y))
  Ī¼_natural' := fun X Y X' Y' f g => by
    rw [ā h.hom_equiv_naturality_left, ā h.hom_equiv_naturality_right, Equivā.apply_eq_iff_eq, assoc,
      is_iso.eq_inv_comp, ā F.to_lax_monoidal_functor.Ī¼_natural_assoc, is_iso.hom_inv_id_assoc, ā tensor_comp,
      adjunction.counit_naturality, adjunction.counit_naturality, tensor_comp]
  associativity' := fun X Y Z => by
    rw [ā h.hom_equiv_naturality_right, ā h.hom_equiv_naturality_left, ā h.hom_equiv_naturality_left, ā
      h.hom_equiv_naturality_left, Equivā.apply_eq_iff_eq, ā
      cancel_epi (F.to_lax_monoidal_functor.Ī¼ (G.obj X ā G.obj Y) (G.obj Z)), ā
      cancel_epi (F.to_lax_monoidal_functor.Ī¼ (G.obj X) (G.obj Y) ā š (F.obj (G.obj Z))),
      F.to_lax_monoidal_functor.associativity_assoc (G.obj X) (G.obj Y) (G.obj Z), ā
      F.to_lax_monoidal_functor.Ī¼_natural_assoc, assoc, is_iso.hom_inv_id_assoc, ā
      F.to_lax_monoidal_functor.Ī¼_natural_assoc, is_iso.hom_inv_id_assoc, ā tensor_comp, ā tensor_comp, id_comp,
      Functor.map_id, Functor.map_id, id_comp, ā tensor_comp_assoc, ā tensor_comp_assoc, id_comp, id_comp,
      h.hom_equiv_unit, h.hom_equiv_unit, functor.map_comp, assoc, assoc, h.counit_naturality,
      h.left_triangle_components_assoc, is_iso.hom_inv_id_assoc, functor.map_comp, assoc, h.counit_naturality,
      h.left_triangle_components_assoc, is_iso.hom_inv_id_assoc]
    exact associator_naturality (h.counit.app X) (h.counit.app Y) (h.counit.app Z)
  left_unitality' := fun X => by
    rw [ā h.hom_equiv_naturality_right, ā h.hom_equiv_naturality_left, ā Equivā.symm_apply_eq, h.hom_equiv_counit,
      F.map_left_unitor, h.hom_equiv_unit, assoc, assoc, assoc, F.map_tensor, assoc, assoc, is_iso.hom_inv_id_assoc, ā
      tensor_comp_assoc, Functor.map_id, id_comp, functor.map_comp, assoc, h.counit_naturality,
      h.left_triangle_components_assoc, ā left_unitor_naturality, ā tensor_comp_assoc, id_comp, comp_id]
  right_unitality' := fun X => by
    rw [ā h.hom_equiv_naturality_right, ā h.hom_equiv_naturality_left, ā Equivā.symm_apply_eq, h.hom_equiv_counit,
      F.map_right_unitor, assoc, assoc, ā right_unitor_naturality, ā tensor_comp_assoc, comp_id, id_comp,
      h.hom_equiv_unit, F.map_tensor, assoc, assoc, assoc, is_iso.hom_inv_id_assoc, functor.map_comp, Functor.map_id, ā
      tensor_comp_assoc, assoc, h.counit_naturality, h.left_triangle_components_assoc, id_comp]

/-- If a monoidal functor `F` is an equivalence of categories then its inverse is also monoidal. -/
@[simps]
noncomputable def monoidalInverse (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor] : MonoidalFunctor D C where
  toLaxMonoidalFunctor := monoidalAdjoint F (asEquivalence _).toAdjunction
  Īµ_is_iso := by
    dsimp' [ā equivalence.to_adjunction]
    infer_instance
  Ī¼_is_iso := fun X Y => by
    dsimp' [ā equivalence.to_adjunction]
    infer_instance

end CategoryTheory

