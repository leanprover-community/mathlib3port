/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn

! This file was ported from Lean 3 source module group_theory.nielsen_schreier
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Action
import Mathbin.Combinatorics.Quiver.Arborescence
import Mathbin.Combinatorics.Quiver.ConnectedComponent
import Mathbin.GroupTheory.IsFreeGroup

/-!
# The Nielsen-Schreier theorem

This file proves that a subgroup of a free group is itself free.

## Main result

- `subgroup_is_free_of_is_free H`: an instance saying that a subgroup of a free group is free.

## Proof overview

The proof is analogous to the proof using covering spaces and fundamental groups of graphs,
but we work directly with groupoids instead of topological spaces. Under this analogy,

- `is_free_groupoid G` corresponds to saying that a space is a graph.
- `End_mul_equiv_subgroup H` plays the role of replacing 'subgroup of fundamental group' with
  'fundamental group of covering space'.
- `action_groupoid_is_free G A` corresponds to the fact that a covering of a (single-vertex)
  graph is a graph.
- `End_is_free T` corresponds to the fact that, given a spanning tree `T` of a
  graph, its fundamental group is free (generated by loops from the complement of the tree).

## Implementation notes

Our definition of `is_free_groupoid` is nonstandard. Normally one would require that functors
`G ⥤ X` to any _groupoid_ `X` are given by graph homomorphisms from the generators, but we only
consider _groups_ `X`. This simplifies the argument since functor equality is complicated in
general, but simple for functors to single object categories.

## References

https://ncatlab.org/nlab/show/Nielsen-Schreier+theorem

## Tags

free group, free groupoid, Nielsen-Schreier

-/


noncomputable section

open Classical

universe v u

/- ./././Mathport/Syntax/Translate/Command.lean:224:11: unsupported: unusual advanced open style -/
open CategoryTheory CategoryTheory.ActionCategory CategoryTheory.SingleObj Quiver

/-- `is_free_groupoid.generators G` is a type synonym for `G`. We think of this as
the vertices of the generating quiver of `G` when `G` is free. We can't use `G` directly,
since `G` already has a quiver instance from being a groupoid. -/
@[nolint unused_arguments has_nonempty_instance]
def IsFreeGroupoid.Generators (G) [Groupoid G] :=
  G
#align is_free_groupoid.generators IsFreeGroupoid.Generators

/-- A groupoid `G` is free when we have the following data:
 - a quiver on `is_free_groupoid.generators G` (a type synonym for `G`)
 - a function `of` taking a generating arrow to a morphism in `G`
 - such that a functor from `G` to any group `X` is uniquely determined
   by assigning labels in `X` to the generating arrows.

   This definition is nonstandard. Normally one would require that functors `G ⥤ X`
   to any _groupoid_ `X` are given by graph homomorphisms from `generators`. -/
class IsFreeGroupoid (G) [Groupoid.{v} G] where
  quiverGenerators : Quiver.{v + 1} (IsFreeGroupoid.Generators G)
  of : ∀ {a b : IsFreeGroupoid.Generators G}, (a ⟶ b) → ((show G from a) ⟶ b)
  unique_lift :
    ∀ {X : Type v} [Group X] (f : Labelling (IsFreeGroupoid.Generators G) X),
      ∃! F : G ⥤ CategoryTheory.SingleObj X, ∀ (a b) (g : a ⟶ b), F.map (of g) = f g
#align is_free_groupoid IsFreeGroupoid

namespace IsFreeGroupoid

attribute [instance] quiver_generators

/-- Two functors from a free groupoid to a group are equal when they agree on the generating
quiver. -/
@[ext]
theorem ext_functor {G} [Groupoid.{v} G] [IsFreeGroupoid G] {X : Type v} [Group X]
    (f g : G ⥤ CategoryTheory.SingleObj X) (h : ∀ (a b) (e : a ⟶ b), f.map (of e) = g.map (of e)) :
    f = g :=
  let ⟨_, _, u⟩ := @unique_lift G _ _ X _ fun (a b : Generators G) (e : a ⟶ b) => g.map (of e)
  trans (u _ h) (u _ fun _ _ _ => rfl).symm
#align is_free_groupoid.ext_functor IsFreeGroupoid.ext_functor

/-- An action groupoid over a free froup is free. More generally, one could show that the groupoid
of elements over a free groupoid is free, but this version is easier to prove and suffices for our
purposes.

Analogous to the fact that a covering space of a graph is a graph. (A free groupoid is like a graph,
and a groupoid of elements is like a covering space.) -/
instance actionGroupoidIsFree {G A : Type u} [Group G] [IsFreeGroup G] [MulAction G A] :
    IsFreeGroupoid (ActionCategory G A)
    where
  quiverGenerators :=
    ⟨fun a b => { e : IsFreeGroup.Generators G // IsFreeGroup.of e • a.back = b.back }⟩
  of a b e := ⟨IsFreeGroup.of e, e.property⟩
  unique_lift := by
    intro X _ f
    let f' : fgp.generators G → (A → X) ⋊[mulAutArrow] G := fun e =>
      ⟨fun b => @f ⟨(), _⟩ ⟨(), b⟩ ⟨e, smul_inv_smul _ b⟩, fgp.of e⟩
    rcases fgp.unique_lift f' with ⟨F', hF', uF'⟩
    refine' ⟨uncurry F' _, _, _⟩
    · suffices semidirect_product.right_hom.comp F' = MonoidHom.id _ by
        exact monoid_hom.ext_iff.mp this
      ext
      rw [MonoidHom.comp_apply, hF']
      rfl
    · rintro ⟨⟨⟩, a : A⟩ ⟨⟨⟩, b⟩ ⟨e, h : fgp.of e • a = b⟩
      change (F' (fgp.of _)).left _ = _
      rw [hF']
      cases inv_smul_eq_iff.mpr h.symm
      rfl
    · intro E hE
      have : curry E = F' := by
        apply uF'
        intro e
        ext
        · convert hE _ _ _
          rfl
        · rfl
      apply functor.hext
      · intro
        apply Unit.ext
      · refine' action_category.cases _
        intros
        simp only [← this, uncurry_map, curry_apply_left, coe_back, hom_of_pair.val]
#align is_free_groupoid.action_groupoid_is_free IsFreeGroupoid.actionGroupoidIsFree

namespace SpanningTree

/- In this section, we suppose we have a free groupoid with a spanning tree for its generating
quiver. The goal is to prove that the vertex group at the root is free. A picture to have in mind
is that we are 'pulling' the endpoints of all the edges of the quiver along the spanning tree to
the root. -/
variable {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
  (T : WideSubquiver (symmetrify <| Generators G)) [Arborescence T]

/-- The root of `T`, except its type is `G` instead of the type synonym `T`. -/
private def root' : G :=
  show T from root T
#align is_free_groupoid.spanning_tree.root' is_free_groupoid.spanning_tree.root'

-- this has to be marked noncomputable, see issue #451.
-- It might be nicer to define this in terms of `compose_path`
/-- A path in the tree gives a hom, by composition. -/
noncomputable def homOfPath : ∀ {a : G}, Path (root T) a → (root' T ⟶ a)
  | _, path.nil => 𝟙 _
  | a, path.cons p f => hom_of_path p ≫ Sum.recOn f.val (fun e => of e) fun e => inv (of e)
#align is_free_groupoid.spanning_tree.hom_of_path IsFreeGroupoid.SpanningTree.homOfPath

/-- For every vertex `a`, there is a canonical hom from the root, given by the path in the tree. -/
def treeHom (a : G) : root' T ⟶ a :=
  homOfPath T default
#align is_free_groupoid.spanning_tree.tree_hom IsFreeGroupoid.SpanningTree.treeHom

/-- Any path to `a` gives `tree_hom T a`, since paths in the tree are unique. -/
theorem tree_hom_eq {a : G} (p : Path (root T) a) : treeHom T a = homOfPath T p := by
  rw [tree_hom, Unique.default_eq]
#align is_free_groupoid.spanning_tree.tree_hom_eq IsFreeGroupoid.SpanningTree.tree_hom_eq

@[simp]
theorem tree_hom_root : treeHom T (root' T) = 𝟙 _ :=
  -- this should just be `tree_hom_eq T path.nil`, but Lean treats `hom_of_path` with suspicion.
    trans
    (tree_hom_eq T Path.nil) rfl
#align is_free_groupoid.spanning_tree.tree_hom_root IsFreeGroupoid.SpanningTree.tree_hom_root

/-- Any hom in `G` can be made into a loop, by conjugating with `tree_hom`s. -/
def loopOfHom {a b : G} (p : a ⟶ b) : EndCat (root' T) :=
  treeHom T a ≫ p ≫ inv (treeHom T b)
#align is_free_groupoid.spanning_tree.loop_of_hom IsFreeGroupoid.SpanningTree.loopOfHom

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (e «expr ∈ » wide_subquiver_symmetrify[quiver.wide_subquiver_symmetrify] T a b) -/
/-- Turning an edge in the spanning tree into a loop gives the indentity loop. -/
theorem loop_of_hom_eq_id {a b : Generators G} (e) (_ : e ∈ wideSubquiverSymmetrify T a b) :
    loopOfHom T (of e) = 𝟙 (root' T) :=
  by
  rw [loop_of_hom, ← category.assoc, is_iso.comp_inv_eq, category.id_comp]
  cases H
  · rw [tree_hom_eq T (path.cons default ⟨Sum.inl e, H⟩), hom_of_path]
    rfl
  · rw [tree_hom_eq T (path.cons default ⟨Sum.inr e, H⟩), hom_of_path]
    simp only [is_iso.inv_hom_id, category.comp_id, category.assoc, tree_hom]
#align is_free_groupoid.spanning_tree.loop_of_hom_eq_id IsFreeGroupoid.SpanningTree.loop_of_hom_eq_id

/-- Since a hom gives a loop, any homomorphism from the vertex group at the root
    extends to a functor on the whole groupoid. -/
@[simps]
def functorOfMonoidHom {X} [Monoid X] (f : EndCat (root' T) →* X) : G ⥤ CategoryTheory.SingleObj X
    where
  obj _ := ()
  map a b p := f (loopOfHom T p)
  map_id' := by
    intro a
    rw [loop_of_hom, category.id_comp, is_iso.hom_inv_id, ← End.one_def, f.map_one, id_as_one]
  map_comp' := by
    intros
    rw [comp_as_mul, ← f.map_mul]
    simp only [is_iso.inv_hom_id_assoc, loop_of_hom, End.mul_def, category.assoc]
#align is_free_groupoid.spanning_tree.functor_of_monoid_hom IsFreeGroupoid.SpanningTree.functorOfMonoidHom

/-- Given a free groupoid and an arborescence of its generating quiver, the vertex
    group at the root is freely generated by loops coming from generating arrows
    in the complement of the tree. -/
def endIsFree : IsFreeGroup (EndCat (root' T)) :=
  IsFreeGroup.ofUniqueLift ((wide_subquiver_equiv_set_total <| wideSubquiverSymmetrify T)ᶜ : Set _)
    (fun e => loopOfHom T (of e.val.Hom))
    (by
      intro X _ f
      let f' : labelling (generators G) X := fun a b e =>
        if h : e ∈ wide_subquiver_symmetrify T a b then 1 else f ⟨⟨a, b, e⟩, h⟩
      rcases unique_lift f' with ⟨F', hF', uF'⟩
      refine' ⟨F'.map_End _, _, _⟩
      · suffices ∀ {x y} (q : x ⟶ y), F'.map (loop_of_hom T q) = (F'.map q : X)
          by
          rintro ⟨⟨a, b, e⟩, h⟩
          rw [functor.map_End_apply, this, hF']
          exact dif_neg h
        intros
        suffices ∀ {a} (p : path (root' T) a), F'.map (hom_of_path T p) = 1 by
          simp only [this, tree_hom, comp_as_mul, inv_as_inv, loop_of_hom, inv_one, mul_one,
            one_mul, functor.map_inv, functor.map_comp]
        intro a p
        induction' p with b c p e ih
        · rw [hom_of_path, F'.map_id, id_as_one]
        rw [hom_of_path, F'.map_comp, comp_as_mul, ih, mul_one]
        rcases e with ⟨e | e, eT⟩
        · rw [hF']
          exact dif_pos (Or.inl eT)
        · rw [F'.map_inv, inv_as_inv, inv_eq_one, hF']
          exact dif_pos (Or.inr eT)
      · intro E hE
        ext
        suffices (functor_of_monoid_hom T E).map x = F'.map x by
          simpa only [loop_of_hom, functor_of_monoid_hom_map, is_iso.inv_id, tree_hom_root,
            category.id_comp, category.comp_id] using this
        congr
        apply uF'
        intro a b e
        change E (loop_of_hom T _) = dite _ _ _
        split_ifs
        · rw [loop_of_hom_eq_id T e h, ← End.one_def, E.map_one]
        · exact hE ⟨⟨a, b, e⟩, h⟩)
#align is_free_groupoid.spanning_tree.End_is_free IsFreeGroupoid.SpanningTree.endIsFree

end SpanningTree

/-- Another name for the identity function `G → G`, to help type checking. -/
private def symgen {G : Type u} [Groupoid.{v} G] [IsFreeGroupoid G] :
    G → Symmetrify (Generators G) :=
  id
#align is_free_groupoid.symgen is_free_groupoid.symgen

/-- If there exists a morphism `a → b` in a free groupoid, then there also exists a zigzag
from `a` to `b` in the generating quiver. -/
theorem path_nonempty_of_hom {G} [Groupoid.{u, u} G] [IsFreeGroupoid G] {a b : G} :
    Nonempty (a ⟶ b) → Nonempty (Path (symgen a) (symgen b)) :=
  by
  rintro ⟨p⟩
  rw [← @weakly_connected_component.eq (generators G), eq_comm, ← free_group.of_injective.eq_iff, ←
    mul_inv_eq_one]
  let X := FreeGroup (weakly_connected_component <| generators G)
  let f : G → X := fun g => FreeGroup.of (weakly_connected_component.mk g)
  let F : G ⥤ CategoryTheory.SingleObj X := single_obj.difference_functor f
  change F.map p = ((CategoryTheory.Functor.const G).obj ()).map p
  congr ; ext
  rw [functor.const_obj_map, id_as_one, difference_functor_map, mul_inv_eq_one]
  apply congr_arg FreeGroup.of
  apply (weakly_connected_component.eq _ _).mpr
  exact ⟨hom.to_path (Sum.inr e)⟩
#align is_free_groupoid.path_nonempty_of_hom IsFreeGroupoid.path_nonempty_of_hom

/-- Given a connected free groupoid, its generating quiver is rooted-connected. -/
instance generators_connected (G) [Groupoid.{u, u} G] [IsConnected G] [IsFreeGroupoid G] (r : G) :
    RootedConnected (symgen r) :=
  ⟨fun b => path_nonempty_of_hom (CategoryTheory.nonempty_hom_of_connected_groupoid r b)⟩
#align is_free_groupoid.generators_connected IsFreeGroupoid.generators_connected

/-- A vertex group in a free connected groupoid is free. With some work one could drop the
connectedness assumption, by looking at connected components. -/
instance endIsFreeOfConnectedFree {G} [Groupoid G] [IsConnected G] [IsFreeGroupoid G] (r : G) :
    IsFreeGroup (EndCat r) :=
  spanning_tree.End_is_free <| geodesicSubtree (symgen r)
#align is_free_groupoid.End_is_free_of_connected_free IsFreeGroupoid.endIsFreeOfConnectedFree

end IsFreeGroupoid

/-- The Nielsen-Schreier theorem: a subgroup of a free group is free. -/
instance subgroupIsFreeOfIsFree {G : Type u} [Group G] [IsFreeGroup G] (H : Subgroup G) :
    IsFreeGroup H :=
  IsFreeGroup.ofMulEquiv (endMulEquivSubgroup H)
#align subgroup_is_free_of_is_free subgroupIsFreeOfIsFree

