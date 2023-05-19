/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module topology.locally_finite
! leanprover-community/mathlib commit 55d771df074d0dd020139ee1cd4b95521422df9f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.ContinuousOn
import Mathbin.Order.Filter.SmallSets

/-!
### Locally finite families of sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We say that a family of sets in a topological space is *locally finite* if at every point `x : X`,
there is a neighborhood of `x` which meets only finitely many sets in the family.

In this file we give the definition and prove basic properties of locally finite families of sets.
-/


-- locally finite family [General Topology (Bourbaki, 1995)]
open Set Function Filter

open Topology Filter

universe u

variable {ι : Type u} {ι' α X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : ι → Set X}

#print LocallyFinite /-
/-- A family of sets in `set X` is locally finite if at every point `x : X`,
there is a neighborhood of `x` which meets only finitely many sets in the family. -/
def LocallyFinite (f : ι → Set X) :=
  ∀ x : X, ∃ t ∈ 𝓝 x, { i | (f i ∩ t).Nonempty }.Finite
#align locally_finite LocallyFinite
-/

/- warning: locally_finite_of_finite -> locallyFinite_of_finite is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_3 : Finite.{succ u1} ι] (f : ι -> (Set.{u2} X)), LocallyFinite.{u1, u2} ι X _inst_1 f
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_3 : Finite.{succ u2} ι] (f : ι -> (Set.{u1} X)), LocallyFinite.{u2, u1} ι X _inst_1 f
Case conversion may be inaccurate. Consider using '#align locally_finite_of_finite locallyFinite_of_finiteₓ'. -/
theorem locallyFinite_of_finite [Finite ι] (f : ι → Set X) : LocallyFinite f := fun x =>
  ⟨univ, univ_mem, toFinite _⟩
#align locally_finite_of_finite locallyFinite_of_finite

namespace LocallyFinite

/- warning: locally_finite.point_finite -> LocallyFinite.point_finite is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {f : ι -> (Set.{u2} X)}, (LocallyFinite.{u1, u2} ι X _inst_1 f) -> (forall (x : X), Set.Finite.{u1} ι (setOf.{u1} ι (fun (b : ι) => Membership.Mem.{u2, u2} X (Set.{u2} X) (Set.hasMem.{u2} X) x (f b))))
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {f : ι -> (Set.{u1} X)}, (LocallyFinite.{u2, u1} ι X _inst_1 f) -> (forall (x : X), Set.Finite.{u2} ι (setOf.{u2} ι (fun (b : ι) => Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) x (f b))))
Case conversion may be inaccurate. Consider using '#align locally_finite.point_finite LocallyFinite.point_finiteₓ'. -/
theorem point_finite (hf : LocallyFinite f) (x : X) : { b | x ∈ f b }.Finite :=
  let ⟨t, hxt, ht⟩ := hf x
  ht.Subset fun b hb => ⟨x, hb, mem_of_mem_nhds hxt⟩
#align locally_finite.point_finite LocallyFinite.point_finite

/- warning: locally_finite.subset -> LocallyFinite.subset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {f : ι -> (Set.{u2} X)} {g : ι -> (Set.{u2} X)}, (LocallyFinite.{u1, u2} ι X _inst_1 f) -> (forall (i : ι), HasSubset.Subset.{u2} (Set.{u2} X) (Set.hasSubset.{u2} X) (g i) (f i)) -> (LocallyFinite.{u1, u2} ι X _inst_1 g)
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {f : ι -> (Set.{u1} X)} {g : ι -> (Set.{u1} X)}, (LocallyFinite.{u2, u1} ι X _inst_1 f) -> (forall (i : ι), HasSubset.Subset.{u1} (Set.{u1} X) (Set.instHasSubsetSet.{u1} X) (g i) (f i)) -> (LocallyFinite.{u2, u1} ι X _inst_1 g)
Case conversion may be inaccurate. Consider using '#align locally_finite.subset LocallyFinite.subsetₓ'. -/
protected theorem subset (hf : LocallyFinite f) (hg : ∀ i, g i ⊆ f i) : LocallyFinite g := fun a =>
  let ⟨t, ht₁, ht₂⟩ := hf a
  ⟨t, ht₁, ht₂.Subset fun i hi => hi.mono <| inter_subset_inter (hg i) Subset.rfl⟩
#align locally_finite.subset LocallyFinite.subset

/- warning: locally_finite.comp_inj_on -> LocallyFinite.comp_injOn is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {X : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} X] {f : ι -> (Set.{u3} X)} {g : ι' -> ι}, (LocallyFinite.{u1, u3} ι X _inst_1 f) -> (Set.InjOn.{u2, u1} ι' ι g (setOf.{u2} ι' (fun (i : ι') => Set.Nonempty.{u3} X (f (g i))))) -> (LocallyFinite.{u2, u3} ι' X _inst_1 (Function.comp.{succ u2, succ u1, succ u3} ι' ι (Set.{u3} X) f g))
but is expected to have type
  forall {ι : Type.{u3}} {ι' : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {f : ι -> (Set.{u2} X)} {g : ι' -> ι}, (LocallyFinite.{u3, u2} ι X _inst_1 f) -> (Set.InjOn.{u1, u3} ι' ι g (setOf.{u1} ι' (fun (i : ι') => Set.Nonempty.{u2} X (f (g i))))) -> (LocallyFinite.{u1, u2} ι' X _inst_1 (Function.comp.{succ u1, succ u3, succ u2} ι' ι (Set.{u2} X) f g))
Case conversion may be inaccurate. Consider using '#align locally_finite.comp_inj_on LocallyFinite.comp_injOnₓ'. -/
theorem comp_injOn {g : ι' → ι} (hf : LocallyFinite f) (hg : InjOn g { i | (f (g i)).Nonempty }) :
    LocallyFinite (f ∘ g) := fun x =>
  let ⟨t, htx, htf⟩ := hf x
  ⟨t, htx, htf.Preimage <| hg.mono fun i hi => hi.out.mono <| inter_subset_left _ _⟩
#align locally_finite.comp_inj_on LocallyFinite.comp_injOn

/- warning: locally_finite.comp_injective -> LocallyFinite.comp_injective is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {X : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} X] {f : ι -> (Set.{u3} X)} {g : ι' -> ι}, (LocallyFinite.{u1, u3} ι X _inst_1 f) -> (Function.Injective.{succ u2, succ u1} ι' ι g) -> (LocallyFinite.{u2, u3} ι' X _inst_1 (Function.comp.{succ u2, succ u1, succ u3} ι' ι (Set.{u3} X) f g))
but is expected to have type
  forall {ι : Type.{u3}} {ι' : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {f : ι -> (Set.{u2} X)} {g : ι' -> ι}, (LocallyFinite.{u3, u2} ι X _inst_1 f) -> (Function.Injective.{succ u1, succ u3} ι' ι g) -> (LocallyFinite.{u1, u2} ι' X _inst_1 (Function.comp.{succ u1, succ u3, succ u2} ι' ι (Set.{u2} X) f g))
Case conversion may be inaccurate. Consider using '#align locally_finite.comp_injective LocallyFinite.comp_injectiveₓ'. -/
theorem comp_injective {g : ι' → ι} (hf : LocallyFinite f) (hg : Injective g) :
    LocallyFinite (f ∘ g) :=
  hf.comp_injOn (hg.InjOn _)
#align locally_finite.comp_injective LocallyFinite.comp_injective

/- warning: locally_finite_iff_small_sets -> locallyFinite_iff_smallSets is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {f : ι -> (Set.{u2} X)}, Iff (LocallyFinite.{u1, u2} ι X _inst_1 f) (forall (x : X), Filter.Eventually.{u2} (Set.{u2} X) (fun (s : Set.{u2} X) => Set.Finite.{u1} ι (setOf.{u1} ι (fun (i : ι) => Set.Nonempty.{u2} X (Inter.inter.{u2} (Set.{u2} X) (Set.hasInter.{u2} X) (f i) s)))) (Filter.smallSets.{u2} X (nhds.{u2} X _inst_1 x)))
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {f : ι -> (Set.{u1} X)}, Iff (LocallyFinite.{u2, u1} ι X _inst_1 f) (forall (x : X), Filter.Eventually.{u1} (Set.{u1} X) (fun (s : Set.{u1} X) => Set.Finite.{u2} ι (setOf.{u2} ι (fun (i : ι) => Set.Nonempty.{u1} X (Inter.inter.{u1} (Set.{u1} X) (Set.instInterSet.{u1} X) (f i) s)))) (Filter.smallSets.{u1} X (nhds.{u1} X _inst_1 x)))
Case conversion may be inaccurate. Consider using '#align locally_finite_iff_small_sets locallyFinite_iff_smallSetsₓ'. -/
theorem locallyFinite_iff_smallSets :
    LocallyFinite f ↔ ∀ x, ∀ᶠ s in (𝓝 x).smallSets, { i | (f i ∩ s).Nonempty }.Finite :=
  forall_congr' fun x =>
    Iff.symm <|
      eventually_small_sets' fun s t hst ht =>
        ht.Subset fun i hi => hi.mono <| inter_subset_inter_right _ hst
#align locally_finite_iff_small_sets locallyFinite_iff_smallSets

/- warning: locally_finite.eventually_small_sets -> LocallyFinite.eventually_smallSets is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {f : ι -> (Set.{u2} X)}, (LocallyFinite.{u1, u2} ι X _inst_1 f) -> (forall (x : X), Filter.Eventually.{u2} (Set.{u2} X) (fun (s : Set.{u2} X) => Set.Finite.{u1} ι (setOf.{u1} ι (fun (i : ι) => Set.Nonempty.{u2} X (Inter.inter.{u2} (Set.{u2} X) (Set.hasInter.{u2} X) (f i) s)))) (Filter.smallSets.{u2} X (nhds.{u2} X _inst_1 x)))
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {f : ι -> (Set.{u1} X)}, (LocallyFinite.{u2, u1} ι X _inst_1 f) -> (forall (x : X), Filter.Eventually.{u1} (Set.{u1} X) (fun (s : Set.{u1} X) => Set.Finite.{u2} ι (setOf.{u2} ι (fun (i : ι) => Set.Nonempty.{u1} X (Inter.inter.{u1} (Set.{u1} X) (Set.instInterSet.{u1} X) (f i) s)))) (Filter.smallSets.{u1} X (nhds.{u1} X _inst_1 x)))
Case conversion may be inaccurate. Consider using '#align locally_finite.eventually_small_sets LocallyFinite.eventually_smallSetsₓ'. -/
protected theorem eventually_smallSets (hf : LocallyFinite f) (x : X) :
    ∀ᶠ s in (𝓝 x).smallSets, { i | (f i ∩ s).Nonempty }.Finite :=
  locallyFinite_iff_smallSets.mp hf x
#align locally_finite.eventually_small_sets LocallyFinite.eventually_smallSets

/- warning: locally_finite.exists_mem_basis -> LocallyFinite.exists_mem_basis is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {f : ι -> (Set.{u2} X)} {ι' : Sort.{u3}}, (LocallyFinite.{u1, u2} ι X _inst_1 f) -> (forall {p : ι' -> Prop} {s : ι' -> (Set.{u2} X)} {x : X}, (Filter.HasBasis.{u2, u3} X ι' (nhds.{u2} X _inst_1 x) p s) -> (Exists.{u3} ι' (fun (i : ι') => Exists.{0} (p i) (fun (hi : p i) => Set.Finite.{u1} ι (setOf.{u1} ι (fun (j : ι) => Set.Nonempty.{u2} X (Inter.inter.{u2} (Set.{u2} X) (Set.hasInter.{u2} X) (f j) (s i))))))))
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {f : ι -> (Set.{u1} X)} {ι' : Sort.{u3}}, (LocallyFinite.{u2, u1} ι X _inst_1 f) -> (forall {p : ι' -> Prop} {s : ι' -> (Set.{u1} X)} {x : X}, (Filter.HasBasis.{u1, u3} X ι' (nhds.{u1} X _inst_1 x) p s) -> (Exists.{u3} ι' (fun (i : ι') => And (p i) (Set.Finite.{u2} ι (setOf.{u2} ι (fun (j : ι) => Set.Nonempty.{u1} X (Inter.inter.{u1} (Set.{u1} X) (Set.instInterSet.{u1} X) (f j) (s i))))))))
Case conversion may be inaccurate. Consider using '#align locally_finite.exists_mem_basis LocallyFinite.exists_mem_basisₓ'. -/
theorem exists_mem_basis {ι' : Sort _} (hf : LocallyFinite f) {p : ι' → Prop} {s : ι' → Set X}
    {x : X} (hb : (𝓝 x).HasBasis p s) : ∃ (i : _)(hi : p i), { j | (f j ∩ s i).Nonempty }.Finite :=
  let ⟨i, hpi, hi⟩ := hb.smallSets.eventually_iff.mp (hf.eventually_smallSets x)
  ⟨i, hpi, hi Subset.rfl⟩
#align locally_finite.exists_mem_basis LocallyFinite.exists_mem_basis

/- warning: locally_finite.nhds_within_Union -> LocallyFinite.nhdsWithin_iUnion is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {f : ι -> (Set.{u2} X)}, (LocallyFinite.{u1, u2} ι X _inst_1 f) -> (forall (a : X), Eq.{succ u2} (Filter.{u2} X) (nhdsWithin.{u2} X _inst_1 a (Set.iUnion.{u2, succ u1} X ι (fun (i : ι) => f i))) (iSup.{u2, succ u1} (Filter.{u2} X) (ConditionallyCompleteLattice.toHasSup.{u2} (Filter.{u2} X) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} X) (Filter.completeLattice.{u2} X))) ι (fun (i : ι) => nhdsWithin.{u2} X _inst_1 a (f i))))
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {f : ι -> (Set.{u1} X)}, (LocallyFinite.{u2, u1} ι X _inst_1 f) -> (forall (a : X), Eq.{succ u1} (Filter.{u1} X) (nhdsWithin.{u1} X _inst_1 a (Set.iUnion.{u1, succ u2} X ι (fun (i : ι) => f i))) (iSup.{u1, succ u2} (Filter.{u1} X) (ConditionallyCompleteLattice.toSupSet.{u1} (Filter.{u1} X) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} X) (Filter.instCompleteLatticeFilter.{u1} X))) ι (fun (i : ι) => nhdsWithin.{u1} X _inst_1 a (f i))))
Case conversion may be inaccurate. Consider using '#align locally_finite.nhds_within_Union LocallyFinite.nhdsWithin_iUnionₓ'. -/
protected theorem nhdsWithin_iUnion (hf : LocallyFinite f) (a : X) :
    𝓝[⋃ i, f i] a = ⨆ i, 𝓝[f i] a :=
  by
  rcases hf a with ⟨U, haU, hfin⟩
  refine' le_antisymm _ (iSup_le fun i => nhdsWithin_mono _ (subset_Union _ _))
  calc
    𝓝[⋃ i, f i] a = 𝓝[⋃ i, f i ∩ U] a := by
      rw [← Union_inter, ← nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds haU)]
    _ = 𝓝[⋃ i ∈ { j | (f j ∩ U).Nonempty }, f i ∩ U] a := by
      simp only [mem_set_of_eq, Union_nonempty_self]
    _ = ⨆ i ∈ { j | (f j ∩ U).Nonempty }, 𝓝[f i ∩ U] a := (nhdsWithin_biUnion hfin _ _)
    _ ≤ ⨆ i, 𝓝[f i ∩ U] a := (iSup₂_le_iSup _ _)
    _ ≤ ⨆ i, 𝓝[f i] a := iSup_mono fun i => nhdsWithin_mono _ <| inter_subset_left _ _
    
#align locally_finite.nhds_within_Union LocallyFinite.nhdsWithin_iUnion

/- warning: locally_finite.continuous_on_Union' -> LocallyFinite.continuousOn_iUnion' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {Y : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u3} Y] {f : ι -> (Set.{u2} X)} {g : X -> Y}, (LocallyFinite.{u1, u2} ι X _inst_1 f) -> (forall (i : ι) (x : X), (Membership.Mem.{u2, u2} X (Set.{u2} X) (Set.hasMem.{u2} X) x (closure.{u2} X _inst_1 (f i))) -> (ContinuousWithinAt.{u2, u3} X Y _inst_1 _inst_2 g (f i) x)) -> (ContinuousOn.{u2, u3} X Y _inst_1 _inst_2 g (Set.iUnion.{u2, succ u1} X ι (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : ι -> (Set.{u2} X)} {g : X -> Y}, (LocallyFinite.{u3, u2} ι X _inst_1 f) -> (forall (i : ι) (x : X), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x (closure.{u2} X _inst_1 (f i))) -> (ContinuousWithinAt.{u2, u1} X Y _inst_1 _inst_2 g (f i) x)) -> (ContinuousOn.{u2, u1} X Y _inst_1 _inst_2 g (Set.iUnion.{u2, succ u3} X ι (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align locally_finite.continuous_on_Union' LocallyFinite.continuousOn_iUnion'ₓ'. -/
theorem continuousOn_iUnion' {g : X → Y} (hf : LocallyFinite f)
    (hc : ∀ i x, x ∈ closure (f i) → ContinuousWithinAt g (f i) x) : ContinuousOn g (⋃ i, f i) :=
  by
  rintro x -
  rw [ContinuousWithinAt, hf.nhds_within_Union, tendsto_supr]
  intro i
  by_cases hx : x ∈ closure (f i)
  · exact hc i _ hx
  · rw [mem_closure_iff_nhdsWithin_neBot, not_ne_bot] at hx
    rw [hx]
    exact tendsto_bot
#align locally_finite.continuous_on_Union' LocallyFinite.continuousOn_iUnion'

/- warning: locally_finite.continuous_on_Union -> LocallyFinite.continuousOn_iUnion is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {Y : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u3} Y] {f : ι -> (Set.{u2} X)} {g : X -> Y}, (LocallyFinite.{u1, u2} ι X _inst_1 f) -> (forall (i : ι), IsClosed.{u2} X _inst_1 (f i)) -> (forall (i : ι), ContinuousOn.{u2, u3} X Y _inst_1 _inst_2 g (f i)) -> (ContinuousOn.{u2, u3} X Y _inst_1 _inst_2 g (Set.iUnion.{u2, succ u1} X ι (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : ι -> (Set.{u2} X)} {g : X -> Y}, (LocallyFinite.{u3, u2} ι X _inst_1 f) -> (forall (i : ι), IsClosed.{u2} X _inst_1 (f i)) -> (forall (i : ι), ContinuousOn.{u2, u1} X Y _inst_1 _inst_2 g (f i)) -> (ContinuousOn.{u2, u1} X Y _inst_1 _inst_2 g (Set.iUnion.{u2, succ u3} X ι (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align locally_finite.continuous_on_Union LocallyFinite.continuousOn_iUnionₓ'. -/
theorem continuousOn_iUnion {g : X → Y} (hf : LocallyFinite f) (h_cl : ∀ i, IsClosed (f i))
    (h_cont : ∀ i, ContinuousOn g (f i)) : ContinuousOn g (⋃ i, f i) :=
  hf.continuousOn_iUnion' fun i x hx => h_cont i x <| (h_cl i).closure_subset hx
#align locally_finite.continuous_on_Union LocallyFinite.continuousOn_iUnion

/- warning: locally_finite.continuous' -> LocallyFinite.continuous' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {Y : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u3} Y] {f : ι -> (Set.{u2} X)} {g : X -> Y}, (LocallyFinite.{u1, u2} ι X _inst_1 f) -> (Eq.{succ u2} (Set.{u2} X) (Set.iUnion.{u2, succ u1} X ι (fun (i : ι) => f i)) (Set.univ.{u2} X)) -> (forall (i : ι) (x : X), (Membership.Mem.{u2, u2} X (Set.{u2} X) (Set.hasMem.{u2} X) x (closure.{u2} X _inst_1 (f i))) -> (ContinuousWithinAt.{u2, u3} X Y _inst_1 _inst_2 g (f i) x)) -> (Continuous.{u2, u3} X Y _inst_1 _inst_2 g)
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : ι -> (Set.{u2} X)} {g : X -> Y}, (LocallyFinite.{u3, u2} ι X _inst_1 f) -> (Eq.{succ u2} (Set.{u2} X) (Set.iUnion.{u2, succ u3} X ι (fun (i : ι) => f i)) (Set.univ.{u2} X)) -> (forall (i : ι) (x : X), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x (closure.{u2} X _inst_1 (f i))) -> (ContinuousWithinAt.{u2, u1} X Y _inst_1 _inst_2 g (f i) x)) -> (Continuous.{u2, u1} X Y _inst_1 _inst_2 g)
Case conversion may be inaccurate. Consider using '#align locally_finite.continuous' LocallyFinite.continuous'ₓ'. -/
protected theorem continuous' {g : X → Y} (hf : LocallyFinite f) (h_cov : (⋃ i, f i) = univ)
    (hc : ∀ i x, x ∈ closure (f i) → ContinuousWithinAt g (f i) x) : Continuous g :=
  continuous_iff_continuousOn_univ.2 <| h_cov ▸ hf.continuousOn_iUnion' hc
#align locally_finite.continuous' LocallyFinite.continuous'

/- warning: locally_finite.continuous -> LocallyFinite.continuous is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {Y : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u3} Y] {f : ι -> (Set.{u2} X)} {g : X -> Y}, (LocallyFinite.{u1, u2} ι X _inst_1 f) -> (Eq.{succ u2} (Set.{u2} X) (Set.iUnion.{u2, succ u1} X ι (fun (i : ι) => f i)) (Set.univ.{u2} X)) -> (forall (i : ι), IsClosed.{u2} X _inst_1 (f i)) -> (forall (i : ι), ContinuousOn.{u2, u3} X Y _inst_1 _inst_2 g (f i)) -> (Continuous.{u2, u3} X Y _inst_1 _inst_2 g)
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : ι -> (Set.{u2} X)} {g : X -> Y}, (LocallyFinite.{u3, u2} ι X _inst_1 f) -> (Eq.{succ u2} (Set.{u2} X) (Set.iUnion.{u2, succ u3} X ι (fun (i : ι) => f i)) (Set.univ.{u2} X)) -> (forall (i : ι), IsClosed.{u2} X _inst_1 (f i)) -> (forall (i : ι), ContinuousOn.{u2, u1} X Y _inst_1 _inst_2 g (f i)) -> (Continuous.{u2, u1} X Y _inst_1 _inst_2 g)
Case conversion may be inaccurate. Consider using '#align locally_finite.continuous LocallyFinite.continuousₓ'. -/
protected theorem continuous {g : X → Y} (hf : LocallyFinite f) (h_cov : (⋃ i, f i) = univ)
    (h_cl : ∀ i, IsClosed (f i)) (h_cont : ∀ i, ContinuousOn g (f i)) : Continuous g :=
  continuous_iff_continuousOn_univ.2 <| h_cov ▸ hf.continuousOn_iUnion h_cl h_cont
#align locally_finite.continuous LocallyFinite.continuous

/- warning: locally_finite.closure -> LocallyFinite.closure is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {f : ι -> (Set.{u2} X)}, (LocallyFinite.{u1, u2} ι X _inst_1 f) -> (LocallyFinite.{u1, u2} ι X _inst_1 (fun (i : ι) => closure.{u2} X _inst_1 (f i)))
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {f : ι -> (Set.{u1} X)}, (LocallyFinite.{u2, u1} ι X _inst_1 f) -> (LocallyFinite.{u2, u1} ι X _inst_1 (fun (i : ι) => closure.{u1} X _inst_1 (f i)))
Case conversion may be inaccurate. Consider using '#align locally_finite.closure LocallyFinite.closureₓ'. -/
protected theorem closure (hf : LocallyFinite f) : LocallyFinite fun i => closure (f i) :=
  by
  intro x
  rcases hf x with ⟨s, hsx, hsf⟩
  refine' ⟨interior s, interior_mem_nhds.2 hsx, hsf.subset fun i hi => _⟩
  exact
    (hi.mono is_open_interior.closure_inter).of_closure.mono
      (inter_subset_inter_right _ interior_subset)
#align locally_finite.closure LocallyFinite.closure

/- warning: locally_finite.closure_Union -> LocallyFinite.closure_iUnion is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {f : ι -> (Set.{u2} X)}, (LocallyFinite.{u1, u2} ι X _inst_1 f) -> (Eq.{succ u2} (Set.{u2} X) (closure.{u2} X _inst_1 (Set.iUnion.{u2, succ u1} X ι (fun (i : ι) => f i))) (Set.iUnion.{u2, succ u1} X ι (fun (i : ι) => closure.{u2} X _inst_1 (f i))))
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {f : ι -> (Set.{u1} X)}, (LocallyFinite.{u2, u1} ι X _inst_1 f) -> (Eq.{succ u1} (Set.{u1} X) (closure.{u1} X _inst_1 (Set.iUnion.{u1, succ u2} X ι (fun (i : ι) => f i))) (Set.iUnion.{u1, succ u2} X ι (fun (i : ι) => closure.{u1} X _inst_1 (f i))))
Case conversion may be inaccurate. Consider using '#align locally_finite.closure_Union LocallyFinite.closure_iUnionₓ'. -/
theorem closure_iUnion (h : LocallyFinite f) : closure (⋃ i, f i) = ⋃ i, closure (f i) :=
  by
  ext x
  simp only [mem_closure_iff_nhdsWithin_neBot, h.nhds_within_Union, supr_ne_bot, mem_Union]
#align locally_finite.closure_Union LocallyFinite.closure_iUnion

/- warning: locally_finite.is_closed_Union -> LocallyFinite.isClosed_iUnion is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {f : ι -> (Set.{u2} X)}, (LocallyFinite.{u1, u2} ι X _inst_1 f) -> (forall (i : ι), IsClosed.{u2} X _inst_1 (f i)) -> (IsClosed.{u2} X _inst_1 (Set.iUnion.{u2, succ u1} X ι (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {f : ι -> (Set.{u1} X)}, (LocallyFinite.{u2, u1} ι X _inst_1 f) -> (forall (i : ι), IsClosed.{u1} X _inst_1 (f i)) -> (IsClosed.{u1} X _inst_1 (Set.iUnion.{u1, succ u2} X ι (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align locally_finite.is_closed_Union LocallyFinite.isClosed_iUnionₓ'. -/
theorem isClosed_iUnion (hf : LocallyFinite f) (hc : ∀ i, IsClosed (f i)) : IsClosed (⋃ i, f i) :=
  by simp only [← closure_eq_iff_isClosed, hf.closure_Union, (hc _).closure_eq]
#align locally_finite.is_closed_Union LocallyFinite.isClosed_iUnion

/- warning: locally_finite.Inter_compl_mem_nhds -> LocallyFinite.iInter_compl_mem_nhds is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {f : ι -> (Set.{u2} X)}, (LocallyFinite.{u1, u2} ι X _inst_1 f) -> (forall (i : ι), IsClosed.{u2} X _inst_1 (f i)) -> (forall (x : X), Membership.Mem.{u2, u2} (Set.{u2} X) (Filter.{u2} X) (Filter.hasMem.{u2} X) (Set.iInter.{u2, succ u1} X ι (fun (i : ι) => Set.iInter.{u2, 0} X (Not (Membership.Mem.{u2, u2} X (Set.{u2} X) (Set.hasMem.{u2} X) x (f i))) (fun (hi : Not (Membership.Mem.{u2, u2} X (Set.{u2} X) (Set.hasMem.{u2} X) x (f i))) => HasCompl.compl.{u2} (Set.{u2} X) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} X) (Set.booleanAlgebra.{u2} X)) (f i)))) (nhds.{u2} X _inst_1 x))
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {f : ι -> (Set.{u1} X)}, (LocallyFinite.{u2, u1} ι X _inst_1 f) -> (forall (i : ι), IsClosed.{u1} X _inst_1 (f i)) -> (forall (x : X), Membership.mem.{u1, u1} (Set.{u1} X) (Filter.{u1} X) (instMembershipSetFilter.{u1} X) (Set.iInter.{u1, succ u2} X ι (fun (i : ι) => Set.iInter.{u1, 0} X (Not (Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) x (f i))) (fun (hi : Not (Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) x (f i))) => HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.instBooleanAlgebraSet.{u1} X)) (f i)))) (nhds.{u1} X _inst_1 x))
Case conversion may be inaccurate. Consider using '#align locally_finite.Inter_compl_mem_nhds LocallyFinite.iInter_compl_mem_nhdsₓ'. -/
/-- If `f : β → set α` is a locally finite family of closed sets, then for any `x : α`, the
intersection of the complements to `f i`, `x ∉ f i`, is a neighbourhood of `x`. -/
theorem iInter_compl_mem_nhds (hf : LocallyFinite f) (hc : ∀ i, IsClosed (f i)) (x : X) :
    (⋂ (i) (hi : x ∉ f i), f iᶜ) ∈ 𝓝 x :=
  by
  refine' IsOpen.mem_nhds _ (mem_Inter₂.2 fun i => id)
  suffices IsClosed (⋃ i : { i // x ∉ f i }, f i) by
    rwa [← isOpen_compl_iff, compl_Union, Inter_subtype] at this
  exact (hf.comp_injective Subtype.coe_injective).isClosed_iUnion fun i => hc _
#align locally_finite.Inter_compl_mem_nhds LocallyFinite.iInter_compl_mem_nhds

#print LocallyFinite.exists_forall_eventually_eq_prod /-
/-- Let `f : ℕ → Π a, β a` be a sequence of (dependent) functions on a topological space. Suppose
that the family of sets `s n = {x | f (n + 1) x ≠ f n x}` is locally finite. Then there exists a
function `F : Π a, β a` such that for any `x`, we have `f n x = F x` on the product of an infinite
interval `[N, +∞)` and a neighbourhood of `x`.

We formulate the conclusion in terms of the product of filter `filter.at_top` and `𝓝 x`. -/
theorem exists_forall_eventually_eq_prod {π : X → Sort _} {f : ℕ → ∀ x : X, π x}
    (hf : LocallyFinite fun n => { x | f (n + 1) x ≠ f n x }) :
    ∃ F : ∀ x : X, π x, ∀ x, ∀ᶠ p : ℕ × X in atTop ×ᶠ 𝓝 x, f p.1 p.2 = F p.2 :=
  by
  choose U hUx hU using hf
  choose N hN using fun x => (hU x).BddAbove
  replace hN : ∀ (x), ∀ n > N x, ∀ y ∈ U x, f (n + 1) y = f n y
  exact fun x n hn y hy => by_contra fun hne => hn.lt.not_le <| hN x ⟨y, hne, hy⟩
  replace hN : ∀ (x), ∀ n ≥ N x + 1, ∀ y ∈ U x, f n y = f (N x + 1) y
  exact fun x n hn y hy => Nat.le_induction rfl (fun k hle => (hN x _ hle _ hy).trans) n hn
  refine' ⟨fun x => f (N x + 1) x, fun x => _⟩
  filter_upwards [Filter.prod_mem_prod (eventually_gt_at_top (N x)) (hUx x)]
  rintro ⟨n, y⟩ ⟨hn : N x < n, hy : y ∈ U x⟩
  calc
    f n y = f (N x + 1) y := hN _ _ hn _ hy
    _ = f (max (N x + 1) (N y + 1)) y := (hN _ _ (le_max_left _ _) _ hy).symm
    _ = f (N y + 1) y := hN _ _ (le_max_right _ _) _ (mem_of_mem_nhds <| hUx y)
    
#align locally_finite.exists_forall_eventually_eq_prod LocallyFinite.exists_forall_eventually_eq_prod
-/

#print LocallyFinite.exists_forall_eventually_atTop_eventually_eq' /-
/-- Let `f : ℕ → Π a, β a` be a sequence of (dependent) functions on a topological space. Suppose
that the family of sets `s n = {x | f (n + 1) x ≠ f n x}` is locally finite. Then there exists a
function `F : Π a, β a` such that for any `x`, for sufficiently large values of `n`, we have
`f n y = F y` in a neighbourhood of `x`. -/
theorem exists_forall_eventually_atTop_eventually_eq' {π : X → Sort _} {f : ℕ → ∀ x : X, π x}
    (hf : LocallyFinite fun n => { x | f (n + 1) x ≠ f n x }) :
    ∃ F : ∀ x : X, π x, ∀ x, ∀ᶠ n : ℕ in atTop, ∀ᶠ y : X in 𝓝 x, f n y = F y :=
  hf.exists_forall_eventually_eq_prod.imp fun F hF x => (hF x).curry
#align locally_finite.exists_forall_eventually_at_top_eventually_eq' LocallyFinite.exists_forall_eventually_atTop_eventually_eq'
-/

#print LocallyFinite.exists_forall_eventually_atTop_eventuallyEq /-
/-- Let `f : ℕ → α → β` be a sequence of functions on a topological space. Suppose
that the family of sets `s n = {x | f (n + 1) x ≠ f n x}` is locally finite. Then there exists a
function `F :  α → β` such that for any `x`, for sufficiently large values of `n`, we have
`f n =ᶠ[𝓝 x] F`. -/
theorem exists_forall_eventually_atTop_eventuallyEq {f : ℕ → X → α}
    (hf : LocallyFinite fun n => { x | f (n + 1) x ≠ f n x }) :
    ∃ F : X → α, ∀ x, ∀ᶠ n : ℕ in atTop, f n =ᶠ[𝓝 x] F :=
  hf.exists_forall_eventually_atTop_eventually_eq'
#align locally_finite.exists_forall_eventually_at_top_eventually_eq LocallyFinite.exists_forall_eventually_atTop_eventuallyEq
-/

/- warning: locally_finite.preimage_continuous -> LocallyFinite.preimage_continuous is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {Y : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u3} Y] {f : ι -> (Set.{u2} X)} {g : Y -> X}, (LocallyFinite.{u1, u2} ι X _inst_1 f) -> (Continuous.{u3, u2} Y X _inst_2 _inst_1 g) -> (LocallyFinite.{u1, u3} ι Y _inst_2 (fun (i : ι) => Set.preimage.{u3, u2} Y X g (f i)))
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : ι -> (Set.{u2} X)} {g : Y -> X}, (LocallyFinite.{u3, u2} ι X _inst_1 f) -> (Continuous.{u1, u2} Y X _inst_2 _inst_1 g) -> (LocallyFinite.{u3, u1} ι Y _inst_2 (fun (i : ι) => Set.preimage.{u1, u2} Y X g (f i)))
Case conversion may be inaccurate. Consider using '#align locally_finite.preimage_continuous LocallyFinite.preimage_continuousₓ'. -/
theorem preimage_continuous {g : Y → X} (hf : LocallyFinite f) (hg : Continuous g) :
    LocallyFinite fun i => g ⁻¹' f i := fun x =>
  let ⟨s, hsx, hs⟩ := hf (g x)
  ⟨g ⁻¹' s, hg.ContinuousAt hsx, hs.Subset fun i ⟨y, hy⟩ => ⟨g y, hy⟩⟩
#align locally_finite.preimage_continuous LocallyFinite.preimage_continuous

end LocallyFinite

/- warning: equiv.locally_finite_comp_iff -> Equiv.locallyFinite_comp_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {X : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} X] {f : ι -> (Set.{u3} X)} (e : Equiv.{succ u2, succ u1} ι' ι), Iff (LocallyFinite.{u2, u3} ι' X _inst_1 (Function.comp.{succ u2, succ u1, succ u3} ι' ι (Set.{u3} X) f (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} ι' ι) (fun (_x : Equiv.{succ u2, succ u1} ι' ι) => ι' -> ι) (Equiv.hasCoeToFun.{succ u2, succ u1} ι' ι) e))) (LocallyFinite.{u1, u3} ι X _inst_1 f)
but is expected to have type
  forall {ι : Type.{u2}} {ι' : Type.{u3}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {f : ι -> (Set.{u1} X)} (e : Equiv.{succ u3, succ u2} ι' ι), Iff (LocallyFinite.{u3, u1} ι' X _inst_1 (Function.comp.{succ u3, succ u2, succ u1} ι' ι (Set.{u1} X) f (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (Equiv.{succ u3, succ u2} ι' ι) ι' (fun (_x : ι') => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : ι') => ι) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u2} ι' ι) e))) (LocallyFinite.{u2, u1} ι X _inst_1 f)
Case conversion may be inaccurate. Consider using '#align equiv.locally_finite_comp_iff Equiv.locallyFinite_comp_iffₓ'. -/
@[simp]
theorem Equiv.locallyFinite_comp_iff (e : ι' ≃ ι) : LocallyFinite (f ∘ e) ↔ LocallyFinite f :=
  ⟨fun h => by simpa only [(· ∘ ·), e.apply_symm_apply] using h.comp_injective e.symm.injective,
    fun h => h.comp_injective e.Injective⟩
#align equiv.locally_finite_comp_iff Equiv.locallyFinite_comp_iff

/- warning: locally_finite_sum -> locallyFinite_sum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {X : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} X] {f : (Sum.{u1, u2} ι ι') -> (Set.{u3} X)}, Iff (LocallyFinite.{max u1 u2, u3} (Sum.{u1, u2} ι ι') X _inst_1 f) (And (LocallyFinite.{u1, u3} ι X _inst_1 (Function.comp.{succ u1, max (succ u1) (succ u2), succ u3} ι (Sum.{u1, u2} ι ι') (Set.{u3} X) f (Sum.inl.{u1, u2} ι ι'))) (LocallyFinite.{u2, u3} ι' X _inst_1 (Function.comp.{succ u2, max (succ u1) (succ u2), succ u3} ι' (Sum.{u1, u2} ι ι') (Set.{u3} X) f (Sum.inr.{u1, u2} ι ι'))))
but is expected to have type
  forall {ι : Type.{u3}} {ι' : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {f : (Sum.{u3, u2} ι ι') -> (Set.{u1} X)}, Iff (LocallyFinite.{max u3 u2, u1} (Sum.{u3, u2} ι ι') X _inst_1 f) (And (LocallyFinite.{u3, u1} ι X _inst_1 (Function.comp.{succ u3, max (succ u3) (succ u2), succ u1} ι (Sum.{u3, u2} ι ι') (Set.{u1} X) f (Sum.inl.{u3, u2} ι ι'))) (LocallyFinite.{u2, u1} ι' X _inst_1 (Function.comp.{succ u2, max (succ u3) (succ u2), succ u1} ι' (Sum.{u3, u2} ι ι') (Set.{u1} X) f (Sum.inr.{u3, u2} ι ι'))))
Case conversion may be inaccurate. Consider using '#align locally_finite_sum locallyFinite_sumₓ'. -/
theorem locallyFinite_sum {f : Sum ι ι' → Set X} :
    LocallyFinite f ↔ LocallyFinite (f ∘ Sum.inl) ∧ LocallyFinite (f ∘ Sum.inr) := by
  simp only [locallyFinite_iff_smallSets, ← forall_and, ← finite_preimage_inl_and_inr,
    preimage_set_of_eq, (· ∘ ·), eventually_and]
#align locally_finite_sum locallyFinite_sum

/- warning: locally_finite.sum_elim -> LocallyFinite.sum_elim is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {X : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} X] {f : ι -> (Set.{u3} X)} {g : ι' -> (Set.{u3} X)}, (LocallyFinite.{u1, u3} ι X _inst_1 f) -> (LocallyFinite.{u2, u3} ι' X _inst_1 g) -> (LocallyFinite.{max u1 u2, u3} (Sum.{u1, u2} ι ι') X _inst_1 (Sum.elim.{u1, u2, succ u3} ι ι' (Set.{u3} X) f g))
but is expected to have type
  forall {ι : Type.{u2}} {ι' : Type.{u1}} {X : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} X] {f : ι -> (Set.{u3} X)} {g : ι' -> (Set.{u3} X)}, (LocallyFinite.{u2, u3} ι X _inst_1 f) -> (LocallyFinite.{u1, u3} ι' X _inst_1 g) -> (LocallyFinite.{max u1 u2, u3} (Sum.{u2, u1} ι ι') X _inst_1 (Sum.elim.{u2, u1, succ u3} ι ι' (Set.{u3} X) f g))
Case conversion may be inaccurate. Consider using '#align locally_finite.sum_elim LocallyFinite.sum_elimₓ'. -/
theorem LocallyFinite.sum_elim {g : ι' → Set X} (hf : LocallyFinite f) (hg : LocallyFinite g) :
    LocallyFinite (Sum.elim f g) :=
  locallyFinite_sum.mpr ⟨hf, hg⟩
#align locally_finite.sum_elim LocallyFinite.sum_elim

/- warning: locally_finite_option -> locallyFinite_option is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {f : (Option.{u1} ι) -> (Set.{u2} X)}, Iff (LocallyFinite.{u1, u2} (Option.{u1} ι) X _inst_1 f) (LocallyFinite.{u1, u2} ι X _inst_1 (Function.comp.{succ u1, succ u1, succ u2} ι (Option.{u1} ι) (Set.{u2} X) f (Option.some.{u1} ι)))
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {f : (Option.{u2} ι) -> (Set.{u1} X)}, Iff (LocallyFinite.{u2, u1} (Option.{u2} ι) X _inst_1 f) (LocallyFinite.{u2, u1} ι X _inst_1 (Function.comp.{succ u2, succ u2, succ u1} ι (Option.{u2} ι) (Set.{u1} X) f (Option.some.{u2} ι)))
Case conversion may be inaccurate. Consider using '#align locally_finite_option locallyFinite_optionₓ'. -/
theorem locallyFinite_option {f : Option ι → Set X} : LocallyFinite f ↔ LocallyFinite (f ∘ some) :=
  by
  simp only [← (Equiv.optionEquivSumPUnit.{u} ι).symm.locallyFinite_comp_iff, locallyFinite_sum,
    locallyFinite_of_finite, and_true_iff]
  rfl
#align locally_finite_option locallyFinite_option

/- warning: locally_finite.option_elim -> LocallyFinite.option_elim' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {f : ι -> (Set.{u2} X)}, (LocallyFinite.{u1, u2} ι X _inst_1 f) -> (forall (s : Set.{u2} X), LocallyFinite.{u1, u2} (Option.{u1} ι) X _inst_1 (Option.elim'.{u1, u2} ι (Set.{u2} X) s f))
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {f : ι -> (Set.{u1} X)}, (LocallyFinite.{u2, u1} ι X _inst_1 f) -> (forall (s : Set.{u1} X), LocallyFinite.{u2, u1} (Option.{u2} ι) X _inst_1 (Option.elim'.{u2, u1} ι (Set.{u1} X) s f))
Case conversion may be inaccurate. Consider using '#align locally_finite.option_elim LocallyFinite.option_elim'ₓ'. -/
theorem LocallyFinite.option_elim' (hf : LocallyFinite f) (s : Set X) :
    LocallyFinite (Option.elim' s f) :=
  locallyFinite_option.2 hf
#align locally_finite.option_elim LocallyFinite.option_elim'

