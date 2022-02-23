/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.Data.List.Chain
import Mathbin.CategoryTheory.Punit
import Mathbin.CategoryTheory.Groupoid

/-!
# Connected category

Define a connected category as a _nonempty_ category for which every functor
to a discrete category is isomorphic to the constant functor.

NB. Some authors include the empty category as connected, we do not.
We instead are interested in categories with exactly one 'connected
component'.

We give some equivalent definitions:
- A nonempty category for which every functor to a discrete category is
  constant on objects.
  See `any_functor_const_on_obj` and `connected.of_any_functor_const_on_obj`.
- A nonempty category for which every function `F` for which the presence of a
  morphism `f : j₁ ⟶ j₂` implies `F j₁ = F j₂` must be constant everywhere.
  See `constant_of_preserves_morphisms` and `connected.of_constant_of_preserves_morphisms`.
- A nonempty category for which any subset of its elements containing the
  default and closed under morphisms is everything.
  See `induct_on_objects` and `connected.of_induct`.
- A nonempty category for which every object is related under the reflexive
  transitive closure of the relation "there is a morphism in some direction
  from `j₁` to `j₂`".
  See `connected_zigzag` and `zigzag_connected`.
- A nonempty category for which for any two objects there is a sequence of
  morphisms (some reversed) from one to the other.
  See `exists_zigzag'` and `connected_of_zigzag`.

We also prove the result that the functor given by `(X × -)` preserves any
connected limit. That is, any limit of shape `J` where `J` is a connected
category is preserved by the functor `(X × -)`. This appears in `category_theory.limits.connected`.
-/


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory.Category

open Opposite

namespace CategoryTheory

/-- A possibly empty category for which every functor to a discrete category is constant.
-/
class IsPreconnected (J : Type u₁) [Category.{v₁} J] : Prop where
  iso_constant : ∀ {α : Type u₁} F : J ⥤ Discrete α j : J, Nonempty (F ≅ (Functor.const J).obj (F.obj j))

/-- We define a connected category as a _nonempty_ category for which every
functor to a discrete category is constant.

NB. Some authors include the empty category as connected, we do not.
We instead are interested in categories with exactly one 'connected
component'.

This allows us to show that the functor X ⨯ - preserves connected limits.

See https://stacks.math.columbia.edu/tag/002S
-/
class IsConnected (J : Type u₁) [Category.{v₁} J] extends IsPreconnected J : Prop where
  [is_nonempty : Nonempty J]

attribute [instance] is_connected.is_nonempty

variable {J : Type u₁} [Category.{v₁} J]

variable {K : Type u₂} [Category.{v₂} K]

/-- If `J` is connected, any functor `F : J ⥤ discrete α` is isomorphic to
the constant functor with value `F.obj j` (for any choice of `j`).
-/
def isoConstant [IsPreconnected J] {α : Type u₁} (F : J ⥤ Discrete α) (j : J) : F ≅ (Functor.const J).obj (F.obj j) :=
  (IsPreconnected.iso_constant F j).some

/-- If J is connected, any functor to a discrete category is constant on objects.
The converse is given in `is_connected.of_any_functor_const_on_obj`.
-/
theorem any_functor_const_on_obj [IsPreconnected J] {α : Type u₁} (F : J ⥤ Discrete α) (j j' : J) :
    F.obj j = F.obj j' :=
  ((isoConstant F j').Hom.app j).down.1

/-- If any functor to a discrete category is constant on objects, J is connected.
The converse of `any_functor_const_on_obj`.
-/
theorem IsConnected.of_any_functor_const_on_obj [Nonempty J]
    (h : ∀ {α : Type u₁} F : J ⥤ Discrete α, ∀ j j' : J, F.obj j = F.obj j') : IsConnected J :=
  { iso_constant := fun α F j' =>
      ⟨NatIso.ofComponents (fun j => eqToIso (h F j j')) fun _ _ _ => Subsingleton.elimₓ _ _⟩ }

/-- If `J` is connected, then given any function `F` such that the presence of a
morphism `j₁ ⟶ j₂` implies `F j₁ = F j₂`, we have that `F` is constant.
This can be thought of as a local-to-global property.

The converse is shown in `is_connected.of_constant_of_preserves_morphisms`
-/
theorem constant_of_preserves_morphisms [IsPreconnected J] {α : Type u₁} (F : J → α)
    (h : ∀ j₁ j₂ : J f : j₁ ⟶ j₂, F j₁ = F j₂) (j j' : J) : F j = F j' :=
  any_functor_const_on_obj { obj := F, map := fun _ _ f => eqToHom (h _ _ f) } j j'

/-- `J` is connected if: given any function `F : J → α` which is constant for any
`j₁, j₂` for which there is a morphism `j₁ ⟶ j₂`, then `F` is constant.
This can be thought of as a local-to-global property.

The converse of `constant_of_preserves_morphisms`.
-/
theorem IsConnected.of_constant_of_preserves_morphisms [Nonempty J]
    (h : ∀ {α : Type u₁} F : J → α, (∀ {j₁ j₂ : J} f : j₁ ⟶ j₂, F j₁ = F j₂) → ∀ j j' : J, F j = F j') :
    IsConnected J :=
  IsConnected.of_any_functor_const_on_obj fun _ F => h F.obj fun _ _ f => (F.map f).down.1

/-- An inductive-like property for the objects of a connected category.
If the set `p` is nonempty, and `p` is closed under morphisms of `J`,
then `p` contains all of `J`.

The converse is given in `is_connected.of_induct`.
-/
theorem induct_on_objects [IsPreconnected J] (p : Set J) {j₀ : J} (h0 : j₀ ∈ p)
    (h1 : ∀ {j₁ j₂ : J} f : j₁ ⟶ j₂, j₁ ∈ p ↔ j₂ ∈ p) (j : J) : j ∈ p := by
  injection constant_of_preserves_morphisms (fun k => ULift.up (k ∈ p)) (fun j₁ j₂ f => _) j j₀ with i
  rwa [i]
  dsimp
  exact congr_argₓ ULift.up (propext (h1 f))

/-- If any maximal connected component containing some element j₀ of J is all of J, then J is connected.

The converse of `induct_on_objects`.
-/
theorem IsConnected.of_induct [Nonempty J] {j₀ : J}
    (h : ∀ p : Set J, j₀ ∈ p → (∀ {j₁ j₂ : J} f : j₁ ⟶ j₂, j₁ ∈ p ↔ j₂ ∈ p) → ∀ j : J, j ∈ p) : IsConnected J :=
  IsConnected.of_constant_of_preserves_morphisms fun α F a => by
    have w :=
      h { j | F j = F j₀ } rfl fun _ _ f => by
        simp [a f]
    dsimp  at w
    intro j j'
    rw [w j, w j']

/-- Another induction principle for `is_preconnected J`:
given a type family `Z : J → Sort*` and
a rule for transporting in *both* directions along a morphism in `J`,
we can transport an `x : Z j₀` to a point in `Z j` for any `j`.
-/
theorem is_preconnected_induction [IsPreconnected J] (Z : J → Sort _) (h₁ : ∀ {j₁ j₂ : J} f : j₁ ⟶ j₂, Z j₁ → Z j₂)
    (h₂ : ∀ {j₁ j₂ : J} f : j₁ ⟶ j₂, Z j₂ → Z j₁) {j₀ : J} (x : Z j₀) (j : J) : Nonempty (Z j) :=
  (induct_on_objects { j | Nonempty (Z j) } ⟨x⟩
    (fun j₁ j₂ f =>
      ⟨by
        rintro ⟨y⟩
        exact ⟨h₁ f y⟩, by
        rintro ⟨y⟩
        exact ⟨h₂ f y⟩⟩)
    j :
    _)

/-- If `J` and `K` are equivalent, then if `J` is preconnected then `K` is as well. -/
theorem is_preconnected_of_equivalent {K : Type u₁} [Category.{v₂} K] [IsPreconnected J] (e : J ≌ K) :
    IsPreconnected K :=
  { iso_constant := fun α F k =>
      ⟨calc
          F ≅ e.inverse ⋙ e.Functor ⋙ F := (e.invFunIdAssoc F).symm
          _ ≅ e.inverse ⋙ (Functor.const J).obj ((e.Functor ⋙ F).obj (e.inverse.obj k)) :=
            isoWhiskerLeft e.inverse (isoConstant (e.Functor ⋙ F) (e.inverse.obj k))
          _ ≅ e.inverse ⋙ (Functor.const J).obj (F.obj k) :=
            isoWhiskerLeft _ ((F ⋙ Functor.const J).mapIso (e.counitIso.app k))
          _ ≅ (Functor.const K).obj (F.obj k) :=
            NatIso.ofComponents (fun X => Iso.refl _)
              (by
                simp )
          ⟩ }

/-- If `J` and `K` are equivalent, then if `J` is connected then `K` is as well. -/
theorem is_connected_of_equivalent {K : Type u₁} [Category.{v₂} K] (e : J ≌ K) [IsConnected J] : IsConnected K :=
  { is_nonempty :=
      Nonempty.map e.Functor.obj
        (by
          infer_instance),
    to_is_preconnected := is_preconnected_of_equivalent e }

/-- If `J` is preconnected, then `Jᵒᵖ` is preconnected as well. -/
instance is_preconnected_op [IsPreconnected J] : IsPreconnected Jᵒᵖ where
  iso_constant := fun α F X =>
    ⟨NatIso.ofComponents
        (fun Y =>
          (Nonempty.some <| IsPreconnected.iso_constant (F.rightOp ⋙ (Discrete.opposite α).Functor) (unop X)).app
            (unop Y))
        fun Y Z f => Subsingleton.elimₓ _ _⟩

/-- If `J` is connected, then `Jᵒᵖ` is connected as well. -/
instance is_connected_op [IsConnected J] : IsConnected Jᵒᵖ where
  is_nonempty := Nonempty.intro (op (Classical.arbitrary J))

theorem is_preconnected_of_is_preconnected_op [IsPreconnected Jᵒᵖ] : IsPreconnected J :=
  is_preconnected_of_equivalent (opOpEquivalence J)

theorem is_connected_of_is_connected_op [IsConnected Jᵒᵖ] : IsConnected J :=
  is_connected_of_equivalent (opOpEquivalence J)

/-- j₁ and j₂ are related by `zag` if there is a morphism between them. -/
@[reducible]
def Zag (j₁ j₂ : J) : Prop :=
  Nonempty (j₁ ⟶ j₂) ∨ Nonempty (j₂ ⟶ j₁)

theorem zag_symmetric : Symmetric (@Zag J _) := fun j₂ j₁ h => h.swap

/-- `j₁` and `j₂` are related by `zigzag` if there is a chain of
morphisms from `j₁` to `j₂`, with backward morphisms allowed.
-/
@[reducible]
def Zigzag : J → J → Prop :=
  Relation.ReflTransGen Zag

theorem zigzag_symmetric : Symmetric (@Zigzag J _) :=
  Relation.ReflTransGen.symmetric zag_symmetric

theorem zigzag_equivalence : Equivalenceₓ (@Zigzag J _) :=
  mk_equivalence _ Relation.reflexive_refl_trans_gen zigzag_symmetric Relation.transitive_refl_trans_gen

/-- The setoid given by the equivalence relation `zigzag`. A quotient for this
setoid is a connected component of the category.
-/
def Zigzag.setoid (J : Type u₂) [Category.{v₁} J] : Setoidₓ J where
  R := Zigzag
  iseqv := zigzag_equivalence

/-- If there is a zigzag from `j₁` to `j₂`, then there is a zigzag from `F j₁` to
`F j₂` as long as `F` is a functor.
-/
theorem zigzag_obj_of_zigzag (F : J ⥤ K) {j₁ j₂ : J} (h : Zigzag j₁ j₂) : Zigzag (F.obj j₁) (F.obj j₂) :=
  (h.lift _) fun j k => Or.imp (Nonempty.map fun f => F.map f) (Nonempty.map fun f => F.map f)

-- TODO: figure out the right way to generalise this to `zigzag`.
theorem zag_of_zag_obj (F : J ⥤ K) [Full F] {j₁ j₂ : J} (h : Zag (F.obj j₁) (F.obj j₂)) : Zag j₁ j₂ :=
  Or.imp (Nonempty.map F.Preimage) (Nonempty.map F.Preimage) h

/-- Any equivalence relation containing (⟶) holds for all pairs of a connected category. -/
theorem equiv_relation [IsConnected J] (r : J → J → Prop) (hr : Equivalenceₓ r)
    (h : ∀ {j₁ j₂ : J} f : j₁ ⟶ j₂, r j₁ j₂) : ∀ j₁ j₂ : J, r j₁ j₂ := by
  have z : ∀ j : J, r (Classical.arbitrary J) j :=
    induct_on_objects (fun k => r (Classical.arbitrary J) k) (hr.1 (Classical.arbitrary J)) fun _ _ f =>
      ⟨fun t => hr.2.2 t (h f), fun t => hr.2.2 t (hr.2.1 (h f))⟩
  intros
  apply hr.2.2 (hr.2.1 (z _)) (z _)

/-- In a connected category, any two objects are related by `zigzag`. -/
theorem is_connected_zigzag [IsConnected J] (j₁ j₂ : J) : Zigzag j₁ j₂ :=
  equiv_relation _ zigzag_equivalence (fun _ _ f => Relation.ReflTransGen.single (Or.inl (Nonempty.intro f))) _ _

/-- If any two objects in an nonempty category are related by `zigzag`, the category is connected.
-/
theorem zigzag_is_connected [Nonempty J] (h : ∀ j₁ j₂ : J, Zigzag j₁ j₂) : IsConnected J := by
  apply is_connected.of_induct
  intro p hp hjp j
  have : ∀ j₁ j₂ : J, zigzag j₁ j₂ → (j₁ ∈ p ↔ j₂ ∈ p) := by
    introv k
    induction' k with _ _ rt_zag zag
    · rfl
      
    · rw [k_ih]
      rcases zag with (⟨⟨_⟩⟩ | ⟨⟨_⟩⟩)
      apply hjp zag
      apply (hjp zag).symm
      
  rwa [this j (Classical.arbitrary J) (h _ _)]

theorem exists_zigzag' [IsConnected J] (j₁ j₂ : J) :
    ∃ l, List.Chain Zag j₁ l ∧ List.last (j₁ :: l) (List.cons_ne_nil _ _) = j₂ :=
  List.exists_chain_of_relation_refl_trans_gen (is_connected_zigzag _ _)

/-- If any two objects in an nonempty category are linked by a sequence of (potentially reversed)
morphisms, then J is connected.

The converse of `exists_zigzag'`.
-/
theorem is_connected_of_zigzag [Nonempty J]
    (h : ∀ j₁ j₂ : J, ∃ l, List.Chain Zag j₁ l ∧ List.last (j₁ :: l) (List.cons_ne_nil _ _) = j₂) : IsConnected J := by
  apply zigzag_is_connected
  intro j₁ j₂
  rcases h j₁ j₂ with ⟨l, hl₁, hl₂⟩
  apply List.relation_refl_trans_gen_of_exists_chain l hl₁ hl₂

/-- If `discrete α` is connected, then `α` is (type-)equivalent to `punit`. -/
def discreteIsConnectedEquivPunit {α : Type u₁} [IsConnected (Discrete α)] : α ≃ PUnit :=
  Discrete.equivOfEquivalence.{u₁, u₁}
    { Functor := Functor.star α, inverse := Discrete.functor fun _ => Classical.arbitrary _,
      unitIso := iso_constant _ (Classical.arbitrary _), counitIso := Functor.punitExt _ _ }

variable {C : Type u₂} [Category.{u₁} C]

/-- For objects `X Y : C`, any natural transformation `α : const X ⟶ const Y` from a connected
category must be constant.
This is the key property of connected categories which we use to establish properties about limits.
-/
theorem nat_trans_from_is_connected [IsPreconnected J] {X Y : C}
    (α : (Functor.const J).obj X ⟶ (Functor.const J).obj Y) : ∀ j j' : J, α.app j = (α.app j' : X ⟶ Y) :=
  @constant_of_preserves_morphisms _ _ _ (X ⟶ Y) (fun j => α.app j) fun _ _ f => by
    have := α.naturality f
    erw [id_comp, comp_id] at this
    exact this.symm

instance [IsConnected J] : Full (Functor.const J : C ⥤ J ⥤ C) where
  Preimage := fun X Y f => f.app (Classical.arbitrary J)
  witness' := fun X Y f => by
    ext j
    apply nat_trans_from_is_connected f (Classical.arbitrary J) j

instance nonempty_hom_of_connected_groupoid {G} [Groupoid G] [IsConnected G] : ∀ x y : G, Nonempty (x ⟶ y) := by
  refine' equiv_relation _ _ fun j₁ j₂ => Nonempty.intro
  exact ⟨fun j => ⟨𝟙 _⟩, fun j₁ j₂ => Nonempty.map fun f => inv f, fun _ _ _ => Nonempty.map2 (· ≫ ·)⟩

end CategoryTheory

