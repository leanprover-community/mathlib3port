import Mathbin.Topology.Sheaves.Presheaf
import Mathbin.CategoryTheory.Limits.Final
import Mathbin.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# Another version of the sheaf condition.

Given a family of open sets `U : ι → opens X` we can form the subcategory
`{ V : opens X // ∃ i, V ≤ U i }`, which has `supr U` as a cocone.

The sheaf condition on a presheaf `F` is equivalent to
`F` sending the opposite of this cocone to a limit cone in `C`, for every `U`.

This condition is particularly nice when checking the sheaf condition
because we don't need to do any case bashing
(depending on whether we're looking at single or double intersections,
or equivalently whether we're looking at the first or second object in an equalizer diagram).

## References
* This is the definition Lurie uses in [Spectral Algebraic Geometry][LurieSAG].
-/


universe v u

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

open Opposite

open TopologicalSpace.Opens

namespace Top

variable {C : Type u} [category.{v} C]

variable {X : Top.{v}} (F : presheaf C X) {ι : Type v} (U : ι → opens X)

namespace Presheaf

namespace SheafCondition

/-- The category of open sets contained in some element of the cover.
-/
def opens_le_cover : Type v :=
  { V : opens X // ∃ i, V ≤ U i }

instance [Inhabited ι] : Inhabited (opens_le_cover U) :=
  ⟨⟨⊥, default, bot_le⟩⟩

instance : category (opens_le_cover U) :=
  CategoryTheory.fullSubcategory _

namespace OpensLeCover

variable {U}

/-- An arbitrarily chosen index such that `V ≤ U i`.
-/
def index (V : opens_le_cover U) : ι :=
  V.property.some

/-- The morphism from `V` to `U i` for some `i`.
-/
def hom_to_index (V : opens_le_cover U) : V.val ⟶ U (index V) :=
  V.property.some_spec.Hom

end OpensLeCover

/-- `supr U` as a cocone over the opens sets contained in some element of the cover.

(In fact this is a colimit cocone.)
-/
def opens_le_cover_cocone : cocone (full_subcategory_inclusion _ : opens_le_cover U ⥤ opens X) where
  x := supr U
  ι := { app := fun V : opens_le_cover U => V.hom_to_index ≫ opens.le_supr U _ }

end SheafCondition

open SheafCondition

/-- An equivalent formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`is_sheaf_iff_is_sheaf_opens_le_cover`).

A presheaf is a sheaf if `F` sends the cone `(opens_le_cover_cocone U).op` to a limit cone.
(Recall `opens_le_cover_cocone U`, has cone point `supr U`,
mapping down to any `V` which is contained in some `U i`.)
-/
def is_sheaf_opens_le_cover : Prop :=
  ∀ ⦃ι : Type v⦄ U : ι → opens X, Nonempty (is_limit (F.map_cone (opens_le_cover_cocone U).op))

namespace SheafCondition

open CategoryTheory.Pairwise

/-- Implementation detail:
the object level of `pairwise_to_opens_le_cover : pairwise ι ⥤ opens_le_cover U`
-/
@[simp]
def pairwise_to_opens_le_cover_obj : Pairwise ι → opens_le_cover U
  | single i => ⟨U i, ⟨i, le_reflₓ _⟩⟩
  | pair i j => ⟨U i⊓U j, ⟨i, inf_le_left⟩⟩

open CategoryTheory.Pairwise.Hom

/-- Implementation detail:
the morphism level of `pairwise_to_opens_le_cover : pairwise ι ⥤ opens_le_cover U`
-/
def pairwise_to_opens_le_cover_map :
    ∀ {V W : Pairwise ι}, (V ⟶ W) → (pairwise_to_opens_le_cover_obj U V ⟶ pairwise_to_opens_le_cover_obj U W)
  | _, _, id_single i => 𝟙 _
  | _, _, id_pair i j => 𝟙 _
  | _, _, left i j => hom_of_le inf_le_left
  | _, _, right i j => hom_of_le inf_le_right

/-- The category of single and double intersections of the `U i` maps into the category
of open sets below some `U i`.
-/
@[simps]
def pairwise_to_opens_le_cover : Pairwise ι ⥤ opens_le_cover U where
  obj := pairwise_to_opens_le_cover_obj U
  map := fun V W i => pairwise_to_opens_le_cover_map U i

instance (V : opens_le_cover U) : Nonempty (structured_arrow V (pairwise_to_opens_le_cover U)) :=
  ⟨{ right := single V.index, Hom := V.hom_to_index }⟩

/-- The diagram consisting of the `U i` and `U i ⊓ U j` is cofinal in the diagram
of all opens contained in some `U i`.
-/
instance : functor.final (pairwise_to_opens_le_cover U) :=
  ⟨fun V =>
    is_connected_of_zigzag $ fun A B => by
      rcases A with ⟨⟨⟩, ⟨i⟩ | ⟨i, j⟩, a⟩ <;> rcases B with ⟨⟨⟩, ⟨i'⟩ | ⟨i', j'⟩, b⟩ <;> dsimp  at *
      · refine' ⟨[{ left := PUnit.unit, right := pair i i', Hom := (le_inf a.le b.le).Hom }, _], _, rfl⟩
        exact
          List.Chain.cons (Or.inr ⟨{ left := 𝟙 _, right := left i i' }⟩)
            (List.Chain.cons (Or.inl ⟨{ left := 𝟙 _, right := right i i' }⟩) List.Chain.nil)
        
      · refine'
          ⟨[{ left := PUnit.unit, right := pair i' i, Hom := (le_inf (b.le.trans inf_le_left) a.le).Hom },
              { left := PUnit.unit, right := single i', Hom := (b.le.trans inf_le_left).Hom }, _],
            _, rfl⟩
        exact
          List.Chain.cons (Or.inr ⟨{ left := 𝟙 _, right := right i' i }⟩)
            (List.Chain.cons (Or.inl ⟨{ left := 𝟙 _, right := left i' i }⟩)
              (List.Chain.cons (Or.inr ⟨{ left := 𝟙 _, right := left i' j' }⟩) List.Chain.nil))
        
      · refine'
          ⟨[{ left := PUnit.unit, right := single i, Hom := (a.le.trans inf_le_left).Hom },
              { left := PUnit.unit, right := pair i i', Hom := (le_inf (a.le.trans inf_le_left) b.le).Hom }, _],
            _, rfl⟩
        exact
          List.Chain.cons (Or.inl ⟨{ left := 𝟙 _, right := left i j }⟩)
            (List.Chain.cons (Or.inr ⟨{ left := 𝟙 _, right := left i i' }⟩)
              (List.Chain.cons (Or.inl ⟨{ left := 𝟙 _, right := right i i' }⟩) List.Chain.nil))
        
      · refine'
          ⟨[{ left := PUnit.unit, right := single i, Hom := (a.le.trans inf_le_left).Hom },
              { left := PUnit.unit, right := pair i i',
                Hom := (le_inf (a.le.trans inf_le_left) (b.le.trans inf_le_left)).Hom },
              { left := PUnit.unit, right := single i', Hom := (b.le.trans inf_le_left).Hom }, _],
            _, rfl⟩
        exact
          List.Chain.cons (Or.inl ⟨{ left := 𝟙 _, right := left i j }⟩)
            (List.Chain.cons (Or.inr ⟨{ left := 𝟙 _, right := left i i' }⟩)
              (List.Chain.cons (Or.inl ⟨{ left := 𝟙 _, right := right i i' }⟩)
                (List.Chain.cons (Or.inr ⟨{ left := 𝟙 _, right := left i' j' }⟩) List.Chain.nil)))
        ⟩

/-- The diagram in `opens X` indexed by pairwise intersections from `U` is isomorphic
(in fact, equal) to the diagram factored through `opens_le_cover U`.
-/
def pairwise_diagram_iso : pairwise.diagram U ≅ pairwise_to_opens_le_cover U ⋙ full_subcategory_inclusion _ where
  Hom :=
    { app := by
        rintro (i | ⟨i, j⟩) <;> exact 𝟙 _ }
  inv :=
    { app := by
        rintro (i | ⟨i, j⟩) <;> exact 𝟙 _ }

/-- The cocone `pairwise.cocone U` with cocone point `supr U` over `pairwise.diagram U` is isomorphic
to the cocone `opens_le_cover_cocone U` (with the same cocone point)
after appropriate whiskering and postcomposition.
-/
def pairwise_cocone_iso :
    (pairwise.cocone U).op ≅
      (cones.postcompose_equivalence (nat_iso.op (pairwise_diagram_iso U : _) : _)).Functor.obj
        ((opens_le_cover_cocone U).op.whisker (pairwise_to_opens_le_cover U).op) :=
  cones.ext (iso.refl _)
    (by
      tidy)

end SheafCondition

open SheafCondition

/-- The sheaf condition
in terms of a limit diagram over all `{ V : opens X // ∃ i, V ≤ U i }`
is equivalent to the reformulation
in terms of a limit diagram over `U i` and `U i ⊓ U j`.
-/
theorem is_sheaf_opens_le_cover_iff_is_sheaf_pairwise_intersections (F : presheaf C X) :
    F.is_sheaf_opens_le_cover ↔ F.is_sheaf_pairwise_intersections :=
  forall₂_congrₓ $ fun ι U =>
    Equivₓ.nonempty_congr $
      calc
        is_limit (F.map_cone (opens_le_cover_cocone U).op) ≃
            is_limit ((F.map_cone (opens_le_cover_cocone U).op).whisker (pairwise_to_opens_le_cover U).op) :=
          (functor.initial.is_limit_whisker_equiv (pairwise_to_opens_le_cover U).op _).symm
        _ ≃ is_limit (F.map_cone ((opens_le_cover_cocone U).op.whisker (pairwise_to_opens_le_cover U).op)) :=
          is_limit.equiv_iso_limit F.map_cone_whisker.symm
        _ ≃
            is_limit
              ((cones.postcompose_equivalence _).Functor.obj
                (F.map_cone ((opens_le_cover_cocone U).op.whisker (pairwise_to_opens_le_cover U).op))) :=
          (is_limit.postcompose_hom_equiv _ _).symm
        _ ≃
            is_limit
              (F.map_cone
                ((cones.postcompose_equivalence _).Functor.obj
                  ((opens_le_cover_cocone U).op.whisker (pairwise_to_opens_le_cover U).op))) :=
          is_limit.equiv_iso_limit (functor.map_cone_postcompose_equivalence_functor _).symm
        _ ≃ is_limit (F.map_cone (pairwise.cocone U).op) :=
          is_limit.equiv_iso_limit ((cones.functoriality _ _).mapIso (pairwise_cocone_iso U : _).symm)
        

variable [has_products C]

/-- The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of a limit diagram over all `{ V : opens X // ∃ i, V ≤ U i }`.
-/
theorem is_sheaf_iff_is_sheaf_opens_le_cover (F : presheaf C X) : F.is_sheaf ↔ F.is_sheaf_opens_le_cover :=
  Iff.trans (is_sheaf_iff_is_sheaf_pairwise_intersections F)
    (is_sheaf_opens_le_cover_iff_is_sheaf_pairwise_intersections F).symm

end Presheaf

end Top

