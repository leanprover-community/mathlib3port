import Mathbin.Topology.Sheaves.SheafCondition.EqualizerProducts 
import Mathbin.CategoryTheory.FullSubcategory

/-!
# Sheaves

We define sheaves on a topological space, with values in an arbitrary category with products.

The sheaf condition for a `F : presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ F.obj (U i) ⟶ ∏ F.obj (U i ⊓ U j)`.

We provide the instance `category (sheaf C X)` as the full subcategory of presheaves,
and the fully faithful functor `sheaf.forget : sheaf C X ⥤ presheaf C X`.

## Equivalent conditions

While the "official" definition is in terms of an equalizer diagram,
in `src/topology/sheaves/sheaf_condition/pairwise_intersections.lean`
and in `src/topology/sheaves/sheaf_condition/open_le_cover.lean`
we provide two equivalent conditions (and prove they are equivalent).

The first is that `F.obj U` is the limit point of the diagram consisting of all the `F.obj (U i)`
and `F.obj (U i ⊓ U j)`.
(That is, we explode the equalizer of two products out into its component pieces.)

The second is that `F.obj U` is the limit point of the diagram constisting of all the `F.obj V`,
for those `V : opens X` such that `V ≤ U i` for some `i`.
(This condition is particularly easy to state, and perhaps should become the "official" definition.)

-/


universe v u

noncomputable theory

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

open Opposite

open TopologicalSpace.Opens

namespace Top

variable{C : Type u}[category.{v} C][has_products C]

variable{X : Top.{v}}(F : presheaf C X){ι : Type v}(U : ι → opens X)

namespace Presheaf

open SheafConditionEqualizerProducts

/--
The sheaf condition for a `F : presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ F.obj (U i) ⟶ ∏ F.obj (U i) ⊓ (U j)`.
-/
def is_sheaf (F : presheaf C X) : Prop :=
  ∀ ⦃ι : Type v⦄ U : ι → opens X, Nonempty (is_limit (sheaf_condition_equalizer_products.fork F U))

/--
The presheaf valued in `punit` over any topological space is a sheaf.
-/
theorem is_sheaf_punit (F : presheaf (CategoryTheory.Discrete PUnit) X) : F.is_sheaf :=
  fun ι U => ⟨punit_cone_is_limit⟩

/--
Transfer the sheaf condition across an isomorphism of presheaves.
-/
theorem is_sheaf_of_iso {F G : presheaf C X} (α : F ≅ G) (h : F.is_sheaf) : G.is_sheaf :=
  fun ι U =>
    ⟨is_limit.of_iso_limit ((is_limit.postcompose_inv_equiv _ _).symm (h U).some)
        (sheaf_condition_equalizer_products.fork.iso_of_iso U α.symm).symm⟩

theorem is_sheaf_iso_iff {F G : presheaf C X} (α : F ≅ G) : F.is_sheaf ↔ G.is_sheaf :=
  ⟨fun h => is_sheaf_of_iso α h, fun h => is_sheaf_of_iso α.symm h⟩

end Presheaf

variable(C X)

-- error in Topology.Sheaves.Sheaf: ././Mathport/Syntax/Translate/Basic.lean:702:9: unsupported derive handler category
/--
A `sheaf C X` is a presheaf of objects from `C` over a (bundled) topological space `X`,
satisfying the sheaf condition.
-/ @[derive #[expr category]] def sheaf : Type max u v :=
{F : presheaf C X // F.is_sheaf}

instance sheaf_inhabited : Inhabited (sheaf (CategoryTheory.Discrete PUnit) X) :=
  ⟨⟨functor.star _, presheaf.is_sheaf_punit _⟩⟩

namespace Sheaf

-- error in Topology.Sheaves.Sheaf: ././Mathport/Syntax/Translate/Basic.lean:702:9: unsupported derive handler full
/--
The forgetful functor from sheaves to presheaves.
-/ @[derive #["[", expr full, ",", expr faithful, "]"]] def forget : «expr ⥤ »(Top.sheaf C X, Top.presheaf C X) :=
full_subcategory_inclusion presheaf.is_sheaf

end Sheaf

end Top

