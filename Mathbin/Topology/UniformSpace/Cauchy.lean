/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module topology.uniform_space.cauchy
! leanprover-community/mathlib commit dde670c9a3f503647fd5bfdf1037bad526d3397a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Bases
import Mathbin.Topology.UniformSpace.Basic

/-!
# Theory of Cauchy filters in uniform spaces. Complete uniform spaces. Totally bounded subsets.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


universe u v

open Filter TopologicalSpace Set Classical UniformSpace Function

open Classical uniformity Topology Filter

variable {α : Type u} {β : Type v} [UniformSpace α]

#print Cauchy /-
/-- A filter `f` is Cauchy if for every entourage `r`, there exists an
  `s ∈ f` such that `s × s ⊆ r`. This is a generalization of Cauchy
  sequences, because if `a : ℕ → α` then the filter of sets containing
  cofinitely many of the `a n` is Cauchy iff `a` is a Cauchy sequence. -/
def Cauchy (f : Filter α) :=
  NeBot f ∧ f ×ᶠ f ≤ 𝓤 α
#align cauchy Cauchy
-/

#print IsComplete /-
/-- A set `s` is called *complete*, if any Cauchy filter `f` such that `s ∈ f`
has a limit in `s` (formally, it satisfies `f ≤ 𝓝 x` for some `x ∈ s`). -/
def IsComplete (s : Set α) :=
  ∀ f, Cauchy f → f ≤ 𝓟 s → ∃ x ∈ s, f ≤ 𝓝 x
#align is_complete IsComplete
-/

/- warning: filter.has_basis.cauchy_iff -> Filter.HasBasis.cauchy_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {ι : Sort.{u2}} {p : ι -> Prop} {s : ι -> (Set.{u1} (Prod.{u1, u1} α α))}, (Filter.HasBasis.{u1, u2} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p s) -> (forall {f : Filter.{u1} α}, Iff (Cauchy.{u1} α _inst_1 f) (And (Filter.NeBot.{u1} α f) (forall (i : ι), (p i) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) -> (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) (s i)))))))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : UniformSpace.{u2} α] {ι : Sort.{u1}} {p : ι -> Prop} {s : ι -> (Set.{u2} (Prod.{u2, u2} α α))}, (Filter.HasBasis.{u2, u1} (Prod.{u2, u2} α α) ι (uniformity.{u2} α _inst_1) p s) -> (forall {f : Filter.{u2} α}, Iff (Cauchy.{u2} α _inst_1 f) (And (Filter.NeBot.{u2} α f) (forall (i : ι), (p i) -> (Exists.{succ u2} (Set.{u2} α) (fun (t : Set.{u2} α) => And (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) t f) (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) -> (forall (y : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y t) -> (Membership.mem.{u2, u2} (Prod.{u2, u2} α α) (Set.{u2} (Prod.{u2, u2} α α)) (Set.instMembershipSet.{u2} (Prod.{u2, u2} α α)) (Prod.mk.{u2, u2} α α x y) (s i)))))))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.cauchy_iff Filter.HasBasis.cauchy_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x y «expr ∈ » t) -/
theorem Filter.HasBasis.cauchy_iff {ι} {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s)
    {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ i, p i → ∃ t ∈ f, ∀ (x) (_ : x ∈ t) (y) (_ : y ∈ t), (x, y) ∈ s i :=
  and_congr Iff.rfl <|
    (f.basis_sets.prod_self.le_basis_iffₓ h).trans <| by
      simp only [subset_def, Prod.forall, mem_prod_eq, and_imp, id, ball_mem_comm]
#align filter.has_basis.cauchy_iff Filter.HasBasis.cauchy_iff

/- warning: cauchy_iff' -> cauchy_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {f : Filter.{u1} α}, Iff (Cauchy.{u1} α _inst_1 f) (And (Filter.NeBot.{u1} α f) (forall (s : Set.{u1} (Prod.{u1, u1} α α)), (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) -> (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) s)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {f : Filter.{u1} α}, Iff (Cauchy.{u1} α _inst_1 f) (And (Filter.NeBot.{u1} α f) (forall (s : Set.{u1} (Prod.{u1, u1} α α)), (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t f) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) -> (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) s)))))))
Case conversion may be inaccurate. Consider using '#align cauchy_iff' cauchy_iff'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x y «expr ∈ » t) -/
theorem cauchy_iff' {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ s ∈ 𝓤 α, ∃ t ∈ f, ∀ (x) (_ : x ∈ t) (y) (_ : y ∈ t), (x, y) ∈ s :=
  (𝓤 α).basis_sets.cauchy_iff
#align cauchy_iff' cauchy_iff'

/- warning: cauchy_iff -> cauchy_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {f : Filter.{u1} α}, Iff (Cauchy.{u1} α _inst_1 f) (And (Filter.NeBot.{u1} α f) (forall (s : Set.{u1} (Prod.{u1, u1} α α)), (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) => HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) (Set.prod.{u1, u1} α α t t) s)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {f : Filter.{u1} α}, Iff (Cauchy.{u1} α _inst_1 f) (And (Filter.NeBot.{u1} α f) (forall (s : Set.{u1} (Prod.{u1, u1} α α)), (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t f) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} α α)) (Set.prod.{u1, u1} α α t t) s)))))
Case conversion may be inaccurate. Consider using '#align cauchy_iff cauchy_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem cauchy_iff {f : Filter α} : Cauchy f ↔ NeBot f ∧ ∀ s ∈ 𝓤 α, ∃ t ∈ f, t ×ˢ t ⊆ s :=
  cauchy_iff'.trans <| by
    simp only [subset_def, Prod.forall, mem_prod_eq, and_imp, id, ball_mem_comm]
#align cauchy_iff cauchy_iff

#print Cauchy.ultrafilter_of /-
theorem Cauchy.ultrafilter_of {l : Filter α} (h : Cauchy l) :
    Cauchy (@Ultrafilter.of _ l h.1 : Filter α) :=
  by
  haveI := h.1
  have := Ultrafilter.of_le l
  exact ⟨Ultrafilter.neBot _, (Filter.prod_mono this this).trans h.2⟩
#align cauchy.ultrafilter_of Cauchy.ultrafilter_of
-/

#print cauchy_map_iff /-
theorem cauchy_map_iff {l : Filter β} {f : β → α} :
    Cauchy (l.map f) ↔ NeBot l ∧ Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ᶠ l) (𝓤 α) := by
  rw [Cauchy, map_ne_bot_iff, prod_map_map_eq, tendsto]
#align cauchy_map_iff cauchy_map_iff
-/

#print cauchy_map_iff' /-
theorem cauchy_map_iff' {l : Filter β} [hl : NeBot l] {f : β → α} :
    Cauchy (l.map f) ↔ Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ᶠ l) (𝓤 α) :=
  cauchy_map_iff.trans <| and_iff_right hl
#align cauchy_map_iff' cauchy_map_iff'
-/

/- warning: cauchy.mono -> Cauchy.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {f : Filter.{u1} α} {g : Filter.{u1} α} [hg : Filter.NeBot.{u1} α g], (Cauchy.{u1} α _inst_1 f) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) g f) -> (Cauchy.{u1} α _inst_1 g)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {f : Filter.{u1} α} {g : Filter.{u1} α} [hg : Filter.NeBot.{u1} α g], (Cauchy.{u1} α _inst_1 f) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) g f) -> (Cauchy.{u1} α _inst_1 g)
Case conversion may be inaccurate. Consider using '#align cauchy.mono Cauchy.monoₓ'. -/
theorem Cauchy.mono {f g : Filter α} [hg : NeBot g] (h_c : Cauchy f) (h_le : g ≤ f) : Cauchy g :=
  ⟨hg, le_trans (Filter.prod_mono h_le h_le) h_c.right⟩
#align cauchy.mono Cauchy.mono

/- warning: cauchy.mono' -> Cauchy.mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {f : Filter.{u1} α} {g : Filter.{u1} α}, (Cauchy.{u1} α _inst_1 f) -> (Filter.NeBot.{u1} α g) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) g f) -> (Cauchy.{u1} α _inst_1 g)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {f : Filter.{u1} α} {g : Filter.{u1} α}, (Cauchy.{u1} α _inst_1 f) -> (Filter.NeBot.{u1} α g) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) g f) -> (Cauchy.{u1} α _inst_1 g)
Case conversion may be inaccurate. Consider using '#align cauchy.mono' Cauchy.mono'ₓ'. -/
theorem Cauchy.mono' {f g : Filter α} (h_c : Cauchy f) (hg : NeBot g) (h_le : g ≤ f) : Cauchy g :=
  h_c.mono h_le
#align cauchy.mono' Cauchy.mono'

#print cauchy_nhds /-
theorem cauchy_nhds {a : α} : Cauchy (𝓝 a) :=
  ⟨nhds_neBot, nhds_prod_eq.symm.trans_le (nhds_le_uniformity a)⟩
#align cauchy_nhds cauchy_nhds
-/

#print cauchy_pure /-
theorem cauchy_pure {a : α} : Cauchy (pure a) :=
  cauchy_nhds.mono (pure_le_nhds a)
#align cauchy_pure cauchy_pure
-/

#print Filter.Tendsto.cauchy_map /-
theorem Filter.Tendsto.cauchy_map {l : Filter β} [NeBot l] {f : β → α} {a : α}
    (h : Tendsto f l (𝓝 a)) : Cauchy (map f l) :=
  cauchy_nhds.mono h
#align filter.tendsto.cauchy_map Filter.Tendsto.cauchy_map
-/

/- warning: cauchy.prod -> Cauchy.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {f : Filter.{u1} α} {g : Filter.{u2} β}, (Cauchy.{u1} α _inst_1 f) -> (Cauchy.{u2} β _inst_2 g) -> (Cauchy.{max u1 u2} (Prod.{u1, u2} α β) (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2) (Filter.prod.{u1, u2} α β f g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {f : Filter.{u1} α} {g : Filter.{u2} β}, (Cauchy.{u1} α _inst_1 f) -> (Cauchy.{u2} β _inst_2 g) -> (Cauchy.{max u2 u1} (Prod.{u1, u2} α β) (instUniformSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Filter.prod.{u1, u2} α β f g))
Case conversion may be inaccurate. Consider using '#align cauchy.prod Cauchy.prodₓ'. -/
theorem Cauchy.prod [UniformSpace β] {f : Filter α} {g : Filter β} (hf : Cauchy f) (hg : Cauchy g) :
    Cauchy (f ×ᶠ g) := by
  refine' ⟨hf.1.Prod hg.1, _⟩
  simp only [uniformity_prod, le_inf_iff, ← map_le_iff_le_comap, ← prod_map_map_eq]
  exact
    ⟨le_trans (prod_mono tendsto_fst tendsto_fst) hf.2,
      le_trans (prod_mono tendsto_snd tendsto_snd) hg.2⟩
#align cauchy.prod Cauchy.prod

/- warning: le_nhds_of_cauchy_adhp_aux -> le_nhds_of_cauchy_adhp_aux is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {f : Filter.{u1} α} {x : α}, (forall (s : Set.{u1} (Prod.{u1, u1} α α)), (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) => And (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) (Set.prod.{u1, u1} α α t t) s) (Exists.{succ u1} α (fun (y : α) => And (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) s) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t))))))) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {f : Filter.{u1} α} {x : α}, (forall (s : Set.{u1} (Prod.{u1, u1} α α)), (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t f) (And (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} α α)) (Set.prod.{u1, u1} α α t t) s) (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) s) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t))))))) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x))
Case conversion may be inaccurate. Consider using '#align le_nhds_of_cauchy_adhp_aux le_nhds_of_cauchy_adhp_auxₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The common part of the proofs of `le_nhds_of_cauchy_adhp` and
`sequentially_complete.le_nhds_of_seq_tendsto_nhds`: if for any entourage `s`
one can choose a set `t ∈ f` of diameter `s` such that it contains a point `y`
with `(x, y) ∈ s`, then `f` converges to `x`. -/
theorem le_nhds_of_cauchy_adhp_aux {f : Filter α} {x : α}
    (adhs : ∀ s ∈ 𝓤 α, ∃ t ∈ f, t ×ˢ t ⊆ s ∧ ∃ y, (x, y) ∈ s ∧ y ∈ t) : f ≤ 𝓝 x :=
  by
  -- Consider a neighborhood `s` of `x`
  intro s hs
  -- Take an entourage twice smaller than `s`
  rcases comp_mem_uniformity_sets (mem_nhds_uniformity_iff_right.1 hs) with ⟨U, U_mem, hU⟩
  -- Take a set `t ∈ f`, `t × t ⊆ U`, and a point `y ∈ t` such that `(x, y) ∈ U`
  rcases adhs U U_mem with ⟨t, t_mem, ht, y, hxy, hy⟩
  apply mem_of_superset t_mem
  -- Given a point `z ∈ t`, we have `(x, y) ∈ U` and `(y, z) ∈ t × t ⊆ U`, hence `z ∈ s`
  exact fun z hz => hU (prod_mk_mem_compRel hxy (ht <| mk_mem_prod hy hz)) rfl
#align le_nhds_of_cauchy_adhp_aux le_nhds_of_cauchy_adhp_aux

/- warning: le_nhds_of_cauchy_adhp -> le_nhds_of_cauchy_adhp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {f : Filter.{u1} α} {x : α}, (Cauchy.{u1} α _inst_1 f) -> (ClusterPt.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x f) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {f : Filter.{u1} α} {x : α}, (Cauchy.{u1} α _inst_1 f) -> (ClusterPt.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x f) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x))
Case conversion may be inaccurate. Consider using '#align le_nhds_of_cauchy_adhp le_nhds_of_cauchy_adhpₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- If `x` is an adherent (cluster) point for a Cauchy filter `f`, then it is a limit point
for `f`. -/
theorem le_nhds_of_cauchy_adhp {f : Filter α} {x : α} (hf : Cauchy f) (adhs : ClusterPt x f) :
    f ≤ 𝓝 x :=
  le_nhds_of_cauchy_adhp_aux
    (by
      intro s hs
      obtain ⟨t, t_mem, ht⟩ : ∃ t ∈ f, t ×ˢ t ⊆ s
      exact (cauchy_iff.1 hf).2 s hs
      use t, t_mem, ht
      exact forall_mem_nonempty_iff_ne_bot.2 adhs _ (inter_mem_inf (mem_nhds_left x hs) t_mem))
#align le_nhds_of_cauchy_adhp le_nhds_of_cauchy_adhp

/- warning: le_nhds_iff_adhp_of_cauchy -> le_nhds_iff_adhp_of_cauchy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {f : Filter.{u1} α} {x : α}, (Cauchy.{u1} α _inst_1 f) -> (Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x)) (ClusterPt.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x f))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {f : Filter.{u1} α} {x : α}, (Cauchy.{u1} α _inst_1 f) -> (Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x)) (ClusterPt.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x f))
Case conversion may be inaccurate. Consider using '#align le_nhds_iff_adhp_of_cauchy le_nhds_iff_adhp_of_cauchyₓ'. -/
theorem le_nhds_iff_adhp_of_cauchy {f : Filter α} {x : α} (hf : Cauchy f) :
    f ≤ 𝓝 x ↔ ClusterPt x f :=
  ⟨fun h => ClusterPt.of_le_nhds' h hf.1, le_nhds_of_cauchy_adhp hf⟩
#align le_nhds_iff_adhp_of_cauchy le_nhds_iff_adhp_of_cauchy

#print Cauchy.map /-
theorem Cauchy.map [UniformSpace β] {f : Filter α} {m : α → β} (hf : Cauchy f)
    (hm : UniformContinuous m) : Cauchy (map m f) :=
  ⟨hf.1.map _,
    calc
      map m f ×ᶠ map m f = map (fun p : α × α => (m p.1, m p.2)) (f ×ᶠ f) := Filter.prod_map_map_eq
      _ ≤ map (fun p : α × α => (m p.1, m p.2)) (𝓤 α) := map_mono hf.right
      _ ≤ 𝓤 β := hm
      ⟩
#align cauchy.map Cauchy.map
-/

/- warning: cauchy.comap -> Cauchy.comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {f : Filter.{u2} β} {m : α -> β}, (Cauchy.{u2} β _inst_2 f) -> (LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.partialOrder.{u1} (Prod.{u1, u1} α α)))) (Filter.comap.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) (fun (p : Prod.{u1, u1} α α) => Prod.mk.{u2, u2} β β (m (Prod.fst.{u1, u1} α α p)) (m (Prod.snd.{u1, u1} α α p))) (uniformity.{u2} β _inst_2)) (uniformity.{u1} α _inst_1)) -> (forall [_inst_3 : Filter.NeBot.{u1} α (Filter.comap.{u1, u2} α β m f)], Cauchy.{u1} α _inst_1 (Filter.comap.{u1, u2} α β m f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {f : Filter.{u2} β} {m : α -> β}, (Cauchy.{u2} β _inst_2 f) -> (LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.instPartialOrderFilter.{u1} (Prod.{u1, u1} α α)))) (Filter.comap.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) (fun (p : Prod.{u1, u1} α α) => Prod.mk.{u2, u2} β β (m (Prod.fst.{u1, u1} α α p)) (m (Prod.snd.{u1, u1} α α p))) (uniformity.{u2} β _inst_2)) (uniformity.{u1} α _inst_1)) -> (forall [_inst_3 : Filter.NeBot.{u1} α (Filter.comap.{u1, u2} α β m f)], Cauchy.{u1} α _inst_1 (Filter.comap.{u1, u2} α β m f))
Case conversion may be inaccurate. Consider using '#align cauchy.comap Cauchy.comapₓ'. -/
theorem Cauchy.comap [UniformSpace β] {f : Filter β} {m : α → β} (hf : Cauchy f)
    (hm : comap (fun p : α × α => (m p.1, m p.2)) (𝓤 β) ≤ 𝓤 α) [NeBot (comap m f)] :
    Cauchy (comap m f) :=
  ⟨‹_›,
    calc
      comap m f ×ᶠ comap m f = comap (fun p : α × α => (m p.1, m p.2)) (f ×ᶠ f) :=
        Filter.prod_comap_comap_eq
      _ ≤ comap (fun p : α × α => (m p.1, m p.2)) (𝓤 β) := comap_mono hf.right
      _ ≤ 𝓤 α := hm
      ⟩
#align cauchy.comap Cauchy.comap

/- warning: cauchy.comap' -> Cauchy.comap' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {f : Filter.{u2} β} {m : α -> β}, (Cauchy.{u2} β _inst_2 f) -> (LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.partialOrder.{u1} (Prod.{u1, u1} α α)))) (Filter.comap.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) (fun (p : Prod.{u1, u1} α α) => Prod.mk.{u2, u2} β β (m (Prod.fst.{u1, u1} α α p)) (m (Prod.snd.{u1, u1} α α p))) (uniformity.{u2} β _inst_2)) (uniformity.{u1} α _inst_1)) -> (Filter.NeBot.{u1} α (Filter.comap.{u1, u2} α β m f)) -> (Cauchy.{u1} α _inst_1 (Filter.comap.{u1, u2} α β m f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {f : Filter.{u2} β} {m : α -> β}, (Cauchy.{u2} β _inst_2 f) -> (LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.instPartialOrderFilter.{u1} (Prod.{u1, u1} α α)))) (Filter.comap.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) (fun (p : Prod.{u1, u1} α α) => Prod.mk.{u2, u2} β β (m (Prod.fst.{u1, u1} α α p)) (m (Prod.snd.{u1, u1} α α p))) (uniformity.{u2} β _inst_2)) (uniformity.{u1} α _inst_1)) -> (Filter.NeBot.{u1} α (Filter.comap.{u1, u2} α β m f)) -> (Cauchy.{u1} α _inst_1 (Filter.comap.{u1, u2} α β m f))
Case conversion may be inaccurate. Consider using '#align cauchy.comap' Cauchy.comap'ₓ'. -/
theorem Cauchy.comap' [UniformSpace β] {f : Filter β} {m : α → β} (hf : Cauchy f)
    (hm : comap (fun p : α × α => (m p.1, m p.2)) (𝓤 β) ≤ 𝓤 α) (hb : NeBot (comap m f)) :
    Cauchy (comap m f) :=
  hf.comap hm
#align cauchy.comap' Cauchy.comap'

#print CauchySeq /-
/-- Cauchy sequences. Usually defined on ℕ, but often it is also useful to say that a function
defined on ℝ is Cauchy at +∞ to deduce convergence. Therefore, we define it in a type class that
is general enough to cover both ℕ and ℝ, which are the main motivating examples. -/
def CauchySeq [SemilatticeSup β] (u : β → α) :=
  Cauchy (atTop.map u)
#align cauchy_seq CauchySeq
-/

/- warning: cauchy_seq.tendsto_uniformity -> CauchySeq.tendsto_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] {u : β -> α}, (CauchySeq.{u1, u2} α β _inst_1 _inst_2 u) -> (Filter.Tendsto.{u2, u1} (Prod.{u2, u2} β β) (Prod.{u1, u1} α α) (Prod.map.{u2, u1, u2, u1} β α β α u u) (Filter.atTop.{u2} (Prod.{u2, u2} β β) (Prod.preorder.{u2, u2} β β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)) (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)))) (uniformity.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] {u : β -> α}, (CauchySeq.{u1, u2} α β _inst_1 _inst_2 u) -> (Filter.Tendsto.{u2, u1} (Prod.{u2, u2} β β) (Prod.{u1, u1} α α) (Prod.map.{u2, u1, u2, u1} β α β α u u) (Filter.atTop.{u2} (Prod.{u2, u2} β β) (Prod.instPreorderProd.{u2, u2} β β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)) (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)))) (uniformity.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align cauchy_seq.tendsto_uniformity CauchySeq.tendsto_uniformityₓ'. -/
theorem CauchySeq.tendsto_uniformity [SemilatticeSup β] {u : β → α} (h : CauchySeq u) :
    Tendsto (Prod.map u u) atTop (𝓤 α) := by
  simpa only [tendsto, prod_map_map_eq', prod_at_top_at_top_eq] using h.right
#align cauchy_seq.tendsto_uniformity CauchySeq.tendsto_uniformity

#print CauchySeq.nonempty /-
theorem CauchySeq.nonempty [SemilatticeSup β] {u : β → α} (hu : CauchySeq u) : Nonempty β :=
  @nonempty_of_neBot _ _ <| (map_neBot_iff _).1 hu.1
#align cauchy_seq.nonempty CauchySeq.nonempty
-/

/- warning: cauchy_seq.mem_entourage -> CauchySeq.mem_entourage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {β : Type.{u2}} [_inst_2 : SemilatticeSup.{u2} β] {u : β -> α}, (CauchySeq.{u1, u2} α β _inst_1 _inst_2 u) -> (forall {V : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) -> (Exists.{succ u2} β (fun (k₀ : β) => forall (i : β) (j : β), (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2))) k₀ i) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2))) k₀ j) -> (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α (u i) (u j)) V))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : UniformSpace.{u2} α] {β : Type.{u1}} [_inst_2 : SemilatticeSup.{u1} β] {u : β -> α}, (CauchySeq.{u2, u1} α β _inst_1 _inst_2 u) -> (forall {V : Set.{u2} (Prod.{u2, u2} α α)}, (Membership.mem.{u2, u2} (Set.{u2} (Prod.{u2, u2} α α)) (Filter.{u2} (Prod.{u2, u2} α α)) (instMembershipSetFilter.{u2} (Prod.{u2, u2} α α)) V (uniformity.{u2} α _inst_1)) -> (Exists.{succ u1} β (fun (k₀ : β) => forall (i : β) (j : β), (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_2))) k₀ i) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_2))) k₀ j) -> (Membership.mem.{u2, u2} (Prod.{u2, u2} α α) (Set.{u2} (Prod.{u2, u2} α α)) (Set.instMembershipSet.{u2} (Prod.{u2, u2} α α)) (Prod.mk.{u2, u2} α α (u i) (u j)) V))))
Case conversion may be inaccurate. Consider using '#align cauchy_seq.mem_entourage CauchySeq.mem_entourageₓ'. -/
theorem CauchySeq.mem_entourage {β : Type _} [SemilatticeSup β] {u : β → α} (h : CauchySeq u)
    {V : Set (α × α)} (hV : V ∈ 𝓤 α) : ∃ k₀, ∀ i j, k₀ ≤ i → k₀ ≤ j → (u i, u j) ∈ V :=
  by
  haveI := h.nonempty
  have := h.tendsto_uniformity; rw [← prod_at_top_at_top_eq] at this
  simpa [maps_to] using at_top_basis.prod_self.tendsto_left_iff.1 this V hV
#align cauchy_seq.mem_entourage CauchySeq.mem_entourage

#print Filter.Tendsto.cauchySeq /-
theorem Filter.Tendsto.cauchySeq [SemilatticeSup β] [Nonempty β] {f : β → α} {x}
    (hx : Tendsto f atTop (𝓝 x)) : CauchySeq f :=
  hx.cauchy_map
#align filter.tendsto.cauchy_seq Filter.Tendsto.cauchySeq
-/

#print cauchySeq_const /-
theorem cauchySeq_const [SemilatticeSup β] [Nonempty β] (x : α) : CauchySeq fun n : β => x :=
  tendsto_const_nhds.CauchySeq
#align cauchy_seq_const cauchySeq_const
-/

/- warning: cauchy_seq_iff_tendsto -> cauchySeq_iff_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α}, Iff (CauchySeq.{u1, u2} α β _inst_1 _inst_3 u) (Filter.Tendsto.{u2, u1} (Prod.{u2, u2} β β) (Prod.{u1, u1} α α) (Prod.map.{u2, u1, u2, u1} β α β α u u) (Filter.atTop.{u2} (Prod.{u2, u2} β β) (Prod.preorder.{u2, u2} β β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3)) (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3)))) (uniformity.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α}, Iff (CauchySeq.{u1, u2} α β _inst_1 _inst_3 u) (Filter.Tendsto.{u2, u1} (Prod.{u2, u2} β β) (Prod.{u1, u1} α α) (Prod.map.{u2, u1, u2, u1} β α β α u u) (Filter.atTop.{u2} (Prod.{u2, u2} β β) (Prod.instPreorderProd.{u2, u2} β β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3)) (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3)))) (uniformity.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align cauchy_seq_iff_tendsto cauchySeq_iff_tendstoₓ'. -/
theorem cauchySeq_iff_tendsto [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ Tendsto (Prod.map u u) atTop (𝓤 α) :=
  cauchy_map_iff'.trans <| by simp only [prod_at_top_at_top_eq, Prod.map_def]
#align cauchy_seq_iff_tendsto cauchySeq_iff_tendsto

/- warning: cauchy_seq.comp_tendsto -> CauchySeq.comp_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] {γ : Type.{u3}} [_inst_2 : SemilatticeSup.{u2} β] [_inst_3 : SemilatticeSup.{u3} γ] [_inst_4 : Nonempty.{succ u3} γ] {f : β -> α}, (CauchySeq.{u1, u2} α β _inst_1 _inst_2 f) -> (forall {g : γ -> β}, (Filter.Tendsto.{u3, u2} γ β g (Filter.atTop.{u3} γ (PartialOrder.toPreorder.{u3} γ (SemilatticeSup.toPartialOrder.{u3} γ _inst_3))) (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)))) -> (CauchySeq.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u3, succ u2, succ u1} γ β α f g)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : UniformSpace.{u2} α] {γ : Type.{u1}} [_inst_2 : SemilatticeSup.{u3} β] [_inst_3 : SemilatticeSup.{u1} γ] [_inst_4 : Nonempty.{succ u1} γ] {f : β -> α}, (CauchySeq.{u2, u3} α β _inst_1 _inst_2 f) -> (forall {g : γ -> β}, (Filter.Tendsto.{u1, u3} γ β g (Filter.atTop.{u1} γ (PartialOrder.toPreorder.{u1} γ (SemilatticeSup.toPartialOrder.{u1} γ _inst_3))) (Filter.atTop.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_2)))) -> (CauchySeq.{u2, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u3, succ u2} γ β α f g)))
Case conversion may be inaccurate. Consider using '#align cauchy_seq.comp_tendsto CauchySeq.comp_tendstoₓ'. -/
theorem CauchySeq.comp_tendsto {γ} [SemilatticeSup β] [SemilatticeSup γ] [Nonempty γ] {f : β → α}
    (hf : CauchySeq f) {g : γ → β} (hg : Tendsto g atTop atTop) : CauchySeq (f ∘ g) :=
  cauchySeq_iff_tendsto.2 <| hf.tendsto_uniformity.comp (hg.prod_atTop hg)
#align cauchy_seq.comp_tendsto CauchySeq.comp_tendsto

#print CauchySeq.comp_injective /-
theorem CauchySeq.comp_injective [SemilatticeSup β] [NoMaxOrder β] [Nonempty β] {u : ℕ → α}
    (hu : CauchySeq u) {f : β → ℕ} (hf : Injective f) : CauchySeq (u ∘ f) :=
  hu.comp_tendsto <| Nat.cofinite_eq_atTop ▸ hf.tendsto_cofinite.mono_left atTop_le_cofinite
#align cauchy_seq.comp_injective CauchySeq.comp_injective
-/

#print Function.Bijective.cauchySeq_comp_iff /-
theorem Function.Bijective.cauchySeq_comp_iff {f : ℕ → ℕ} (hf : Bijective f) (u : ℕ → α) :
    CauchySeq (u ∘ f) ↔ CauchySeq u :=
  by
  refine' ⟨fun H => _, fun H => H.comp_injective hf.injective⟩
  lift f to ℕ ≃ ℕ using hf
  simpa only [(· ∘ ·), f.apply_symm_apply] using H.comp_injective f.symm.injective
#align function.bijective.cauchy_seq_comp_iff Function.Bijective.cauchySeq_comp_iff
-/

#print CauchySeq.subseq_subseq_mem /-
theorem CauchySeq.subseq_subseq_mem {V : ℕ → Set (α × α)} (hV : ∀ n, V n ∈ 𝓤 α) {u : ℕ → α}
    (hu : CauchySeq u) {f g : ℕ → ℕ} (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, ((u ∘ f ∘ φ) n, (u ∘ g ∘ φ) n) ∈ V n :=
  by
  rw [cauchySeq_iff_tendsto] at hu
  exact ((hu.comp <| hf.prod_at_top hg).comp tendsto_at_top_diagonal).subseq_mem hV
#align cauchy_seq.subseq_subseq_mem CauchySeq.subseq_subseq_mem
-/

/- warning: cauchy_seq_iff' -> cauchySeq_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {u : Nat -> α}, Iff (CauchySeq.{u1, 0} α Nat _inst_1 (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) u) (forall (V : Set.{u1} (Prod.{u1, u1} α α)), (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) -> (Filter.Eventually.{0} (Prod.{0, 0} Nat Nat) (fun (k : Prod.{0, 0} Nat Nat) => Membership.Mem.{0, 0} (Prod.{0, 0} Nat Nat) (Set.{0} (Prod.{0, 0} Nat Nat)) (Set.hasMem.{0} (Prod.{0, 0} Nat Nat)) k (Set.preimage.{0, u1} (Prod.{0, 0} Nat Nat) (Prod.{u1, u1} α α) (Prod.map.{0, u1, 0, u1} Nat α Nat α u u) V)) (Filter.atTop.{0} (Prod.{0, 0} Nat Nat) (Prod.preorder.{0, 0} Nat Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {u : Nat -> α}, Iff (CauchySeq.{u1, 0} α Nat _inst_1 (Lattice.toSemilatticeSup.{0} Nat (DistribLattice.toLattice.{0} Nat instDistribLatticeNat)) u) (forall (V : Set.{u1} (Prod.{u1, u1} α α)), (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) -> (Filter.Eventually.{0} (Prod.{0, 0} Nat Nat) (fun (k : Prod.{0, 0} Nat Nat) => Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Set.{0} (Prod.{0, 0} Nat Nat)) (Set.instMembershipSet.{0} (Prod.{0, 0} Nat Nat)) k (Set.preimage.{0, u1} (Prod.{0, 0} Nat Nat) (Prod.{u1, u1} α α) (Prod.map.{0, u1, 0, u1} Nat α Nat α u u) V)) (Filter.atTop.{0} (Prod.{0, 0} Nat Nat) (Prod.instPreorderProd.{0, 0} Nat Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))))))
Case conversion may be inaccurate. Consider using '#align cauchy_seq_iff' cauchySeq_iff'ₓ'. -/
theorem cauchySeq_iff' {u : ℕ → α} :
    CauchySeq u ↔ ∀ V ∈ 𝓤 α, ∀ᶠ k in atTop, k ∈ Prod.map u u ⁻¹' V := by
  simpa only [cauchySeq_iff_tendsto]
#align cauchy_seq_iff' cauchySeq_iff'

#print cauchySeq_iff /-
theorem cauchySeq_iff {u : ℕ → α} :
    CauchySeq u ↔ ∀ V ∈ 𝓤 α, ∃ N, ∀ k ≥ N, ∀ l ≥ N, (u k, u l) ∈ V := by
  simp [cauchySeq_iff', Filter.eventually_atTop_prod_self', Prod_map]
#align cauchy_seq_iff cauchySeq_iff
-/

/- warning: cauchy_seq.prod_map -> CauchySeq.prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] {γ : Type.{u3}} {δ : Type.{u4}} [_inst_2 : UniformSpace.{u2} β] [_inst_3 : SemilatticeSup.{u3} γ] [_inst_4 : SemilatticeSup.{u4} δ] {u : γ -> α} {v : δ -> β}, (CauchySeq.{u1, u3} α γ _inst_1 _inst_3 u) -> (CauchySeq.{u2, u4} β δ _inst_2 _inst_4 v) -> (CauchySeq.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ) (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.semilatticeSup.{u3, u4} γ δ _inst_3 _inst_4) (Prod.map.{u3, u1, u4, u2} γ α δ β u v))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : UniformSpace.{u3} α] {γ : Type.{u2}} {δ : Type.{u1}} [_inst_2 : UniformSpace.{u4} β] [_inst_3 : SemilatticeSup.{u2} γ] [_inst_4 : SemilatticeSup.{u1} δ] {u : γ -> α} {v : δ -> β}, (CauchySeq.{u3, u2} α γ _inst_1 _inst_3 u) -> (CauchySeq.{u4, u1} β δ _inst_2 _inst_4 v) -> (CauchySeq.{max u4 u3, max u1 u2} (Prod.{u3, u4} α β) (Prod.{u2, u1} γ δ) (instUniformSpaceProd.{u3, u4} α β _inst_1 _inst_2) (Prod.semilatticeSup.{u2, u1} γ δ _inst_3 _inst_4) (Prod.map.{u2, u3, u1, u4} γ α δ β u v))
Case conversion may be inaccurate. Consider using '#align cauchy_seq.prod_map CauchySeq.prod_mapₓ'. -/
theorem CauchySeq.prod_map {γ δ} [UniformSpace β] [SemilatticeSup γ] [SemilatticeSup δ] {u : γ → α}
    {v : δ → β} (hu : CauchySeq u) (hv : CauchySeq v) : CauchySeq (Prod.map u v) := by
  simpa only [CauchySeq, prod_map_map_eq', prod_at_top_at_top_eq] using hu.prod hv
#align cauchy_seq.prod_map CauchySeq.prod_map

/- warning: cauchy_seq.prod -> CauchySeq.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] {γ : Type.{u3}} [_inst_2 : UniformSpace.{u2} β] [_inst_3 : SemilatticeSup.{u3} γ] {u : γ -> α} {v : γ -> β}, (CauchySeq.{u1, u3} α γ _inst_1 _inst_3 u) -> (CauchySeq.{u2, u3} β γ _inst_2 _inst_3 v) -> (CauchySeq.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (fun (x : γ) => Prod.mk.{u1, u2} α β (u x) (v x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : UniformSpace.{u2} α] {γ : Type.{u1}} [_inst_2 : UniformSpace.{u3} β] [_inst_3 : SemilatticeSup.{u1} γ] {u : γ -> α} {v : γ -> β}, (CauchySeq.{u2, u1} α γ _inst_1 _inst_3 u) -> (CauchySeq.{u3, u1} β γ _inst_2 _inst_3 v) -> (CauchySeq.{max u3 u2, u1} (Prod.{u2, u3} α β) γ (instUniformSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3 (fun (x : γ) => Prod.mk.{u2, u3} α β (u x) (v x)))
Case conversion may be inaccurate. Consider using '#align cauchy_seq.prod CauchySeq.prodₓ'. -/
theorem CauchySeq.prod {γ} [UniformSpace β] [SemilatticeSup γ] {u : γ → α} {v : γ → β}
    (hu : CauchySeq u) (hv : CauchySeq v) : CauchySeq fun x => (u x, v x) :=
  haveI := hu.nonempty
  (hu.prod hv).mono (tendsto.prod_mk le_rfl le_rfl)
#align cauchy_seq.prod CauchySeq.prod

#print CauchySeq.eventually_eventually /-
theorem CauchySeq.eventually_eventually [SemilatticeSup β] {u : β → α} (hu : CauchySeq u)
    {V : Set (α × α)} (hV : V ∈ 𝓤 α) : ∀ᶠ k in atTop, ∀ᶠ l in atTop, (u k, u l) ∈ V :=
  eventually_atTop_curry <| hu.tendsto_uniformity hV
#align cauchy_seq.eventually_eventually CauchySeq.eventually_eventually
-/

/- warning: uniform_continuous.comp_cauchy_seq -> UniformContinuous.comp_cauchySeq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] {γ : Type.{u3}} [_inst_2 : UniformSpace.{u2} β] [_inst_3 : SemilatticeSup.{u3} γ] {f : α -> β}, (UniformContinuous.{u1, u2} α β _inst_1 _inst_2 f) -> (forall {u : γ -> α}, (CauchySeq.{u1, u3} α γ _inst_1 _inst_3 u) -> (CauchySeq.{u2, u3} β γ _inst_2 _inst_3 (Function.comp.{succ u3, succ u1, succ u2} γ α β f u)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : UniformSpace.{u2} α] {γ : Type.{u1}} [_inst_2 : UniformSpace.{u3} β] [_inst_3 : SemilatticeSup.{u1} γ] {f : α -> β}, (UniformContinuous.{u2, u3} α β _inst_1 _inst_2 f) -> (forall {u : γ -> α}, (CauchySeq.{u2, u1} α γ _inst_1 _inst_3 u) -> (CauchySeq.{u3, u1} β γ _inst_2 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} γ α β f u)))
Case conversion may be inaccurate. Consider using '#align uniform_continuous.comp_cauchy_seq UniformContinuous.comp_cauchySeqₓ'. -/
theorem UniformContinuous.comp_cauchySeq {γ} [UniformSpace β] [SemilatticeSup γ] {f : α → β}
    (hf : UniformContinuous f) {u : γ → α} (hu : CauchySeq u) : CauchySeq (f ∘ u) :=
  hu.map hf
#align uniform_continuous.comp_cauchy_seq UniformContinuous.comp_cauchySeq

#print CauchySeq.subseq_mem /-
theorem CauchySeq.subseq_mem {V : ℕ → Set (α × α)} (hV : ∀ n, V n ∈ 𝓤 α) {u : ℕ → α}
    (hu : CauchySeq u) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, (u <| φ (n + 1), u <| φ n) ∈ V n :=
  by
  have : ∀ n, ∃ N, ∀ k ≥ N, ∀ l ≥ k, (u l, u k) ∈ V n :=
    by
    intro n
    rw [cauchySeq_iff] at hu
    rcases hu _ (hV n) with ⟨N, H⟩
    exact ⟨N, fun k hk l hl => H _ (le_trans hk hl) _ hk⟩
  obtain ⟨φ : ℕ → ℕ, φ_extr : StrictMono φ, hφ : ∀ n, ∀ l ≥ φ n, (u l, u <| φ n) ∈ V n⟩ :=
    extraction_forall_of_eventually' this
  exact ⟨φ, φ_extr, fun n => hφ _ _ (φ_extr <| lt_add_one n).le⟩
#align cauchy_seq.subseq_mem CauchySeq.subseq_mem
-/

#print Filter.Tendsto.subseq_mem_entourage /-
theorem Filter.Tendsto.subseq_mem_entourage {V : ℕ → Set (α × α)} (hV : ∀ n, V n ∈ 𝓤 α) {u : ℕ → α}
    {a : α} (hu : Tendsto u atTop (𝓝 a)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (u (φ 0), a) ∈ V 0 ∧ ∀ n, (u <| φ (n + 1), u <| φ n) ∈ V (n + 1) :=
  by
  rcases mem_at_top_sets.1 (hu (ball_mem_nhds a (symm_le_uniformity <| hV 0))) with ⟨n, hn⟩
  rcases(hu.comp (tendsto_add_at_top_nat n)).CauchySeq.subseq_mem fun n => hV (n + 1) with
    ⟨φ, φ_mono, hφV⟩
  exact ⟨fun k => φ k + n, φ_mono.add_const _, hn _ le_add_self, hφV⟩
#align filter.tendsto.subseq_mem_entourage Filter.Tendsto.subseq_mem_entourage
-/

/- warning: tendsto_nhds_of_cauchy_seq_of_subseq -> tendsto_nhds_of_cauchySeq_of_subseq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] {u : β -> α}, (CauchySeq.{u1, u2} α β _inst_1 _inst_2 u) -> (forall {ι : Type.{u3}} {f : ι -> β} {p : Filter.{u3} ι} [_inst_3 : Filter.NeBot.{u3} ι p], (Filter.Tendsto.{u3, u2} ι β f p (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)))) -> (forall {a : α}, (Filter.Tendsto.{u3, u1} ι α (Function.comp.{succ u3, succ u2, succ u1} ι β α u f) p (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) a)) -> (Filter.Tendsto.{u2, u1} β α u (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) a))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : SemilatticeSup.{u3} β] {u : β -> α}, (CauchySeq.{u2, u3} α β _inst_1 _inst_2 u) -> (forall {ι : Type.{u1}} {f : ι -> β} {p : Filter.{u1} ι} [_inst_3 : Filter.NeBot.{u1} ι p], (Filter.Tendsto.{u1, u3} ι β f p (Filter.atTop.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_2)))) -> (forall {a : α}, (Filter.Tendsto.{u1, u2} ι α (Function.comp.{succ u1, succ u3, succ u2} ι β α u f) p (nhds.{u2} α (UniformSpace.toTopologicalSpace.{u2} α _inst_1) a)) -> (Filter.Tendsto.{u3, u2} β α u (Filter.atTop.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_2))) (nhds.{u2} α (UniformSpace.toTopologicalSpace.{u2} α _inst_1) a))))
Case conversion may be inaccurate. Consider using '#align tendsto_nhds_of_cauchy_seq_of_subseq tendsto_nhds_of_cauchySeq_of_subseqₓ'. -/
/-- If a Cauchy sequence has a convergent subsequence, then it converges. -/
theorem tendsto_nhds_of_cauchySeq_of_subseq [SemilatticeSup β] {u : β → α} (hu : CauchySeq u)
    {ι : Type _} {f : ι → β} {p : Filter ι} [NeBot p] (hf : Tendsto f p atTop) {a : α}
    (ha : Tendsto (u ∘ f) p (𝓝 a)) : Tendsto u atTop (𝓝 a) :=
  le_nhds_of_cauchy_adhp hu (mapClusterPt_of_comp hf ha)
#align tendsto_nhds_of_cauchy_seq_of_subseq tendsto_nhds_of_cauchySeq_of_subseq

/- warning: filter.has_basis.cauchy_seq_iff -> Filter.HasBasis.cauchySeq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] {γ : Sort.{u3}} [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α} {p : γ -> Prop} {s : γ -> (Set.{u1} (Prod.{u1, u1} α α))}, (Filter.HasBasis.{u1, u3} (Prod.{u1, u1} α α) γ (uniformity.{u1} α _inst_1) p s) -> (Iff (CauchySeq.{u1, u2} α β _inst_1 _inst_3 u) (forall (i : γ), (p i) -> (Exists.{succ u2} β (fun (N : β) => forall (m : β), (GE.ge.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) m N) -> (forall (n : β), (GE.ge.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) n N) -> (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α (u m) (u n)) (s i)))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : UniformSpace.{u2} α] {γ : Sort.{u1}} [_inst_2 : Nonempty.{succ u3} β] [_inst_3 : SemilatticeSup.{u3} β] {u : β -> α} {p : γ -> Prop} {s : γ -> (Set.{u2} (Prod.{u2, u2} α α))}, (Filter.HasBasis.{u2, u1} (Prod.{u2, u2} α α) γ (uniformity.{u2} α _inst_1) p s) -> (Iff (CauchySeq.{u2, u3} α β _inst_1 _inst_3 u) (forall (i : γ), (p i) -> (Exists.{succ u3} β (fun (N : β) => forall (m : β), (LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_3))) N m) -> (forall (n : β), (LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_3))) N n) -> (Membership.mem.{u2, u2} (Prod.{u2, u2} α α) (Set.{u2} (Prod.{u2, u2} α α)) (Set.instMembershipSet.{u2} (Prod.{u2, u2} α α)) (Prod.mk.{u2, u2} α α (u m) (u n)) (s i)))))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.cauchy_seq_iff Filter.HasBasis.cauchySeq_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (m n «expr ≥ » N) -/
-- see Note [nolint_ge]
@[nolint ge_or_gt]
theorem Filter.HasBasis.cauchySeq_iff {γ} [Nonempty β] [SemilatticeSup β] {u : β → α} {p : γ → Prop}
    {s : γ → Set (α × α)} (h : (𝓤 α).HasBasis p s) :
    CauchySeq u ↔ ∀ i, p i → ∃ N, ∀ (m) (_ : m ≥ N) (n) (_ : n ≥ N), (u m, u n) ∈ s i :=
  by
  rw [cauchySeq_iff_tendsto, ← prod_at_top_at_top_eq]
  refine' (at_top_basis.prod_self.tendsto_iff h).trans _
  simp only [exists_prop, true_and_iff, maps_to, preimage, subset_def, Prod.forall, mem_prod_eq,
    mem_set_of_eq, mem_Ici, and_imp, Prod.map, ge_iff_le, @forall_swap (_ ≤ _) β]
#align filter.has_basis.cauchy_seq_iff Filter.HasBasis.cauchySeq_iff

/- warning: filter.has_basis.cauchy_seq_iff' -> Filter.HasBasis.cauchySeq_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] {γ : Sort.{u3}} [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α} {p : γ -> Prop} {s : γ -> (Set.{u1} (Prod.{u1, u1} α α))}, (Filter.HasBasis.{u1, u3} (Prod.{u1, u1} α α) γ (uniformity.{u1} α _inst_1) p s) -> (Iff (CauchySeq.{u1, u2} α β _inst_1 _inst_3 u) (forall (i : γ), (p i) -> (Exists.{succ u2} β (fun (N : β) => forall (n : β), (GE.ge.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) n N) -> (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α (u n) (u N)) (s i))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : UniformSpace.{u2} α] {γ : Sort.{u1}} [_inst_2 : Nonempty.{succ u3} β] [_inst_3 : SemilatticeSup.{u3} β] {u : β -> α} {p : γ -> Prop} {s : γ -> (Set.{u2} (Prod.{u2, u2} α α))}, (Filter.HasBasis.{u2, u1} (Prod.{u2, u2} α α) γ (uniformity.{u2} α _inst_1) p s) -> (Iff (CauchySeq.{u2, u3} α β _inst_1 _inst_3 u) (forall (i : γ), (p i) -> (Exists.{succ u3} β (fun (N : β) => forall (n : β), (GE.ge.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_3))) n N) -> (Membership.mem.{u2, u2} (Prod.{u2, u2} α α) (Set.{u2} (Prod.{u2, u2} α α)) (Set.instMembershipSet.{u2} (Prod.{u2, u2} α α)) (Prod.mk.{u2, u2} α α (u n) (u N)) (s i))))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.cauchy_seq_iff' Filter.HasBasis.cauchySeq_iff'ₓ'. -/
theorem Filter.HasBasis.cauchySeq_iff' {γ} [Nonempty β] [SemilatticeSup β] {u : β → α}
    {p : γ → Prop} {s : γ → Set (α × α)} (H : (𝓤 α).HasBasis p s) :
    CauchySeq u ↔ ∀ i, p i → ∃ N, ∀ n ≥ N, (u n, u N) ∈ s i :=
  by
  refine' H.cauchy_seq_iff.trans ⟨fun h i hi => _, fun h i hi => _⟩
  · exact (h i hi).imp fun N hN n hn => hN n hn N le_rfl
  · rcases comp_symm_of_uniformity (H.mem_of_mem hi) with ⟨t, ht, ht', hts⟩
    rcases H.mem_iff.1 ht with ⟨j, hj, hjt⟩
    refine' (h j hj).imp fun N hN m hm n hn => hts ⟨u N, hjt _, ht' <| hjt _⟩
    · exact hN m hm
    · exact hN n hn
#align filter.has_basis.cauchy_seq_iff' Filter.HasBasis.cauchySeq_iff'

#print cauchySeq_of_controlled /-
theorem cauchySeq_of_controlled [SemilatticeSup β] [Nonempty β] (U : β → Set (α × α))
    (hU : ∀ s ∈ 𝓤 α, ∃ n, U n ⊆ s) {f : β → α}
    (hf : ∀ {N m n : β}, N ≤ m → N ≤ n → (f m, f n) ∈ U N) : CauchySeq f :=
  cauchySeq_iff_tendsto.2
    (by
      intro s hs
      rw [mem_map, mem_at_top_sets]
      cases' hU s hs with N hN
      refine' ⟨(N, N), fun mn hmn => _⟩
      cases' mn with m n
      exact hN (hf hmn.1 hmn.2))
#align cauchy_seq_of_controlled cauchySeq_of_controlled
-/

/- warning: is_complete_iff_cluster_pt -> isComplete_iff_clusterPt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α}, Iff (IsComplete.{u1} α _inst_1 s) (forall (l : Filter.{u1} α), (Cauchy.{u1} α _inst_1 l) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) l (Filter.principal.{u1} α s)) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => ClusterPt.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x l))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α}, Iff (IsComplete.{u1} α _inst_1 s) (forall (l : Filter.{u1} α), (Cauchy.{u1} α _inst_1 l) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) l (Filter.principal.{u1} α s)) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (ClusterPt.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x l))))
Case conversion may be inaccurate. Consider using '#align is_complete_iff_cluster_pt isComplete_iff_clusterPtₓ'. -/
theorem isComplete_iff_clusterPt {s : Set α} :
    IsComplete s ↔ ∀ l, Cauchy l → l ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x l :=
  forall₃_congr fun l hl hls => exists₂_congr fun x hx => le_nhds_iff_adhp_of_cauchy hl
#align is_complete_iff_cluster_pt isComplete_iff_clusterPt

/- warning: is_complete_iff_ultrafilter -> isComplete_iff_ultrafilter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α}, Iff (IsComplete.{u1} α _inst_1 s) (forall (l : Ultrafilter.{u1} α), (Cauchy.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) l)) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) l) (Filter.principal.{u1} α s)) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) l) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α}, Iff (IsComplete.{u1} α _inst_1 s) (forall (l : Ultrafilter.{u1} α), (Cauchy.{u1} α _inst_1 (Ultrafilter.toFilter.{u1} α l)) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Ultrafilter.toFilter.{u1} α l) (Filter.principal.{u1} α s)) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Ultrafilter.toFilter.{u1} α l) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x)))))
Case conversion may be inaccurate. Consider using '#align is_complete_iff_ultrafilter isComplete_iff_ultrafilterₓ'. -/
theorem isComplete_iff_ultrafilter {s : Set α} :
    IsComplete s ↔ ∀ l : Ultrafilter α, Cauchy (l : Filter α) → ↑l ≤ 𝓟 s → ∃ x ∈ s, ↑l ≤ 𝓝 x :=
  by
  refine' ⟨fun h l => h l, fun H => isComplete_iff_clusterPt.2 fun l hl hls => _⟩
  haveI := hl.1
  rcases H (Ultrafilter.of l) hl.ultrafilter_of ((Ultrafilter.of_le l).trans hls) with ⟨x, hxs, hxl⟩
  exact ⟨x, hxs, (ClusterPt.of_le_nhds hxl).mono (Ultrafilter.of_le l)⟩
#align is_complete_iff_ultrafilter isComplete_iff_ultrafilter

/- warning: is_complete_iff_ultrafilter' -> isComplete_iff_ultrafilter' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α}, Iff (IsComplete.{u1} α _inst_1 s) (forall (l : Ultrafilter.{u1} α), (Cauchy.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) l)) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Ultrafilter.{u1} α) (Ultrafilter.hasMem.{u1} α) s l) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) l) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α}, Iff (IsComplete.{u1} α _inst_1 s) (forall (l : Ultrafilter.{u1} α), (Cauchy.{u1} α _inst_1 (Ultrafilter.toFilter.{u1} α l)) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Ultrafilter.{u1} α) (Ultrafilter.instMembershipSetUltrafilter.{u1} α) s l) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Ultrafilter.toFilter.{u1} α l) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x)))))
Case conversion may be inaccurate. Consider using '#align is_complete_iff_ultrafilter' isComplete_iff_ultrafilter'ₓ'. -/
theorem isComplete_iff_ultrafilter' {s : Set α} :
    IsComplete s ↔ ∀ l : Ultrafilter α, Cauchy (l : Filter α) → s ∈ l → ∃ x ∈ s, ↑l ≤ 𝓝 x :=
  isComplete_iff_ultrafilter.trans <| by simp only [le_principal_iff, Ultrafilter.mem_coe]
#align is_complete_iff_ultrafilter' isComplete_iff_ultrafilter'

/- warning: is_complete.union -> IsComplete.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsComplete.{u1} α _inst_1 s) -> (IsComplete.{u1} α _inst_1 t) -> (IsComplete.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsComplete.{u1} α _inst_1 s) -> (IsComplete.{u1} α _inst_1 t) -> (IsComplete.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align is_complete.union IsComplete.unionₓ'. -/
protected theorem IsComplete.union {s t : Set α} (hs : IsComplete s) (ht : IsComplete t) :
    IsComplete (s ∪ t) :=
  by
  simp only [isComplete_iff_ultrafilter', Ultrafilter.union_mem_iff, or_imp] at *
  exact fun l hl =>
    ⟨fun hsl => (hs l hl hsl).imp fun x hx => ⟨Or.inl hx.fst, hx.snd⟩, fun htl =>
      (ht l hl htl).imp fun x hx => ⟨Or.inr hx.fst, hx.snd⟩⟩
#align is_complete.union IsComplete.union

/- warning: is_complete_Union_separated -> isComplete_unionᵢ_separated is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)}, (forall (i : ι), IsComplete.{u1} α _inst_1 (s i)) -> (forall {U : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) U (uniformity.{u1} α _inst_1)) -> (forall (i : ι) (j : ι) (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s i)) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (s j)) -> (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) U) -> (Eq.{u2} ι i j))) -> (IsComplete.{u1} α _inst_1 (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : UniformSpace.{u2} α] {ι : Sort.{u1}} {s : ι -> (Set.{u2} α)}, (forall (i : ι), IsComplete.{u2} α _inst_1 (s i)) -> (forall {U : Set.{u2} (Prod.{u2, u2} α α)}, (Membership.mem.{u2, u2} (Set.{u2} (Prod.{u2, u2} α α)) (Filter.{u2} (Prod.{u2, u2} α α)) (instMembershipSetFilter.{u2} (Prod.{u2, u2} α α)) U (uniformity.{u2} α _inst_1)) -> (forall (i : ι) (j : ι) (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (s i)) -> (forall (y : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y (s j)) -> (Membership.mem.{u2, u2} (Prod.{u2, u2} α α) (Set.{u2} (Prod.{u2, u2} α α)) (Set.instMembershipSet.{u2} (Prod.{u2, u2} α α)) (Prod.mk.{u2, u2} α α x y) U) -> (Eq.{u1} ι i j))) -> (IsComplete.{u2} α _inst_1 (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => s i))))
Case conversion may be inaccurate. Consider using '#align is_complete_Union_separated isComplete_unionᵢ_separatedₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (t «expr ⊆ » S) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem isComplete_unionᵢ_separated {ι : Sort _} {s : ι → Set α} (hs : ∀ i, IsComplete (s i))
    {U : Set (α × α)} (hU : U ∈ 𝓤 α) (hd : ∀ (i j : ι), ∀ x ∈ s i, ∀ y ∈ s j, (x, y) ∈ U → i = j) :
    IsComplete (⋃ i, s i) := by
  set S := ⋃ i, s i
  intro l hl hls
  rw [le_principal_iff] at hls
  cases' cauchy_iff.1 hl with hl_ne hl'
  obtain ⟨t, htS, htl, htU⟩ : ∃ (t : _)(_ : t ⊆ S), t ∈ l ∧ t ×ˢ t ⊆ U :=
    by
    rcases hl' U hU with ⟨t, htl, htU⟩
    exact
      ⟨t ∩ S, inter_subset_right _ _, inter_mem htl hls,
        (Set.prod_mono (inter_subset_left _ _) (inter_subset_left _ _)).trans htU⟩
  obtain ⟨i, hi⟩ : ∃ i, t ⊆ s i :=
    by
    rcases Filter.nonempty_of_mem htl with ⟨x, hx⟩
    rcases mem_Union.1 (htS hx) with ⟨i, hi⟩
    refine' ⟨i, fun y hy => _⟩
    rcases mem_Union.1 (htS hy) with ⟨j, hj⟩
    convert hj
    exact hd i j x hi y hj (htU <| mk_mem_prod hx hy)
  rcases hs i l hl (le_principal_iff.2 <| mem_of_superset htl hi) with ⟨x, hxs, hlx⟩
  exact ⟨x, mem_Union.2 ⟨i, hxs⟩, hlx⟩
#align is_complete_Union_separated isComplete_unionᵢ_separated

#print CompleteSpace /-
/-- A complete space is defined here using uniformities. A uniform space
  is complete if every Cauchy filter converges. -/
class CompleteSpace (α : Type u) [UniformSpace α] : Prop where
  complete : ∀ {f : Filter α}, Cauchy f → ∃ x, f ≤ 𝓝 x
#align complete_space CompleteSpace
-/

#print complete_univ /-
theorem complete_univ {α : Type u} [UniformSpace α] [CompleteSpace α] : IsComplete (univ : Set α) :=
  by
  intro f hf _
  rcases CompleteSpace.complete hf with ⟨x, hx⟩
  exact ⟨x, mem_univ x, hx⟩
#align complete_univ complete_univ
-/

/- warning: complete_space.prod -> CompleteSpace.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : CompleteSpace.{u1} α _inst_1] [_inst_4 : CompleteSpace.{u2} β _inst_2], CompleteSpace.{max u1 u2} (Prod.{u1, u2} α β) (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : CompleteSpace.{u1} α _inst_1] [_inst_4 : CompleteSpace.{u2} β _inst_2], CompleteSpace.{max u2 u1} (Prod.{u1, u2} α β) (instUniformSpaceProd.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align complete_space.prod CompleteSpace.prodₓ'. -/
instance CompleteSpace.prod [UniformSpace β] [CompleteSpace α] [CompleteSpace β] :
    CompleteSpace (α × β)
    where complete f hf :=
    let ⟨x1, hx1⟩ := CompleteSpace.complete <| hf.map uniformContinuous_fst
    let ⟨x2, hx2⟩ := CompleteSpace.complete <| hf.map uniformContinuous_snd
    ⟨(x1, x2), by
      rw [nhds_prod_eq, Filter.prod_def] <;>
        exact
          Filter.le_lift.2 fun s hs => Filter.le_lift'.2 fun t ht => inter_mem (hx1 hs) (hx2 ht)⟩
#align complete_space.prod CompleteSpace.prod

#print completeSpace_of_isComplete_univ /-
/-- If `univ` is complete, the space is a complete space -/
theorem completeSpace_of_isComplete_univ (h : IsComplete (univ : Set α)) : CompleteSpace α :=
  ⟨fun f hf =>
    let ⟨x, _, hx⟩ := h f hf ((@principal_univ α).symm ▸ le_top)
    ⟨x, hx⟩⟩
#align complete_space_of_is_complete_univ completeSpace_of_isComplete_univ
-/

#print completeSpace_iff_isComplete_univ /-
theorem completeSpace_iff_isComplete_univ : CompleteSpace α ↔ IsComplete (univ : Set α) :=
  ⟨@complete_univ α _, completeSpace_of_isComplete_univ⟩
#align complete_space_iff_is_complete_univ completeSpace_iff_isComplete_univ
-/

/- warning: complete_space_iff_ultrafilter -> completeSpace_iff_ultrafilter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], Iff (CompleteSpace.{u1} α _inst_1) (forall (l : Ultrafilter.{u1} α), (Cauchy.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) l)) -> (Exists.{succ u1} α (fun (x : α) => LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) l) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], Iff (CompleteSpace.{u1} α _inst_1) (forall (l : Ultrafilter.{u1} α), (Cauchy.{u1} α _inst_1 (Ultrafilter.toFilter.{u1} α l)) -> (Exists.{succ u1} α (fun (x : α) => LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Ultrafilter.toFilter.{u1} α l) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x))))
Case conversion may be inaccurate. Consider using '#align complete_space_iff_ultrafilter completeSpace_iff_ultrafilterₓ'. -/
theorem completeSpace_iff_ultrafilter :
    CompleteSpace α ↔ ∀ l : Ultrafilter α, Cauchy (l : Filter α) → ∃ x : α, ↑l ≤ 𝓝 x := by
  simp [completeSpace_iff_isComplete_univ, isComplete_iff_ultrafilter]
#align complete_space_iff_ultrafilter completeSpace_iff_ultrafilter

/- warning: cauchy_iff_exists_le_nhds -> cauchy_iff_exists_le_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : CompleteSpace.{u1} α _inst_1] {l : Filter.{u1} α} [_inst_3 : Filter.NeBot.{u1} α l], Iff (Cauchy.{u1} α _inst_1 l) (Exists.{succ u1} α (fun (x : α) => LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) l (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : CompleteSpace.{u1} α _inst_1] {l : Filter.{u1} α} [_inst_3 : Filter.NeBot.{u1} α l], Iff (Cauchy.{u1} α _inst_1 l) (Exists.{succ u1} α (fun (x : α) => LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) l (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x)))
Case conversion may be inaccurate. Consider using '#align cauchy_iff_exists_le_nhds cauchy_iff_exists_le_nhdsₓ'. -/
theorem cauchy_iff_exists_le_nhds [CompleteSpace α] {l : Filter α} [NeBot l] :
    Cauchy l ↔ ∃ x, l ≤ 𝓝 x :=
  ⟨CompleteSpace.complete, fun ⟨x, hx⟩ => cauchy_nhds.mono hx⟩
#align cauchy_iff_exists_le_nhds cauchy_iff_exists_le_nhds

#print cauchy_map_iff_exists_tendsto /-
theorem cauchy_map_iff_exists_tendsto [CompleteSpace α] {l : Filter β} {f : β → α} [NeBot l] :
    Cauchy (l.map f) ↔ ∃ x, Tendsto f l (𝓝 x) :=
  cauchy_iff_exists_le_nhds
#align cauchy_map_iff_exists_tendsto cauchy_map_iff_exists_tendsto
-/

#print cauchySeq_tendsto_of_complete /-
/-- A Cauchy sequence in a complete space converges -/
theorem cauchySeq_tendsto_of_complete [SemilatticeSup β] [CompleteSpace α] {u : β → α}
    (H : CauchySeq u) : ∃ x, Tendsto u atTop (𝓝 x) :=
  CompleteSpace.complete H
#align cauchy_seq_tendsto_of_complete cauchySeq_tendsto_of_complete
-/

/- warning: cauchy_seq_tendsto_of_is_complete -> cauchySeq_tendsto_of_isComplete is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] {K : Set.{u1} α}, (IsComplete.{u1} α _inst_1 K) -> (forall {u : β -> α}, (forall (n : β), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (u n) K) -> (CauchySeq.{u1, u2} α β _inst_1 _inst_2 u) -> (Exists.{succ u1} α (fun (v : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) v K) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) v K) => Filter.Tendsto.{u2, u1} β α u (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) v)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] {K : Set.{u1} α}, (IsComplete.{u1} α _inst_1 K) -> (forall {u : β -> α}, (forall (n : β), Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (u n) K) -> (CauchySeq.{u1, u2} α β _inst_1 _inst_2 u) -> (Exists.{succ u1} α (fun (v : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) v K) (Filter.Tendsto.{u2, u1} β α u (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) v)))))
Case conversion may be inaccurate. Consider using '#align cauchy_seq_tendsto_of_is_complete cauchySeq_tendsto_of_isCompleteₓ'. -/
/-- If `K` is a complete subset, then any cauchy sequence in `K` converges to a point in `K` -/
theorem cauchySeq_tendsto_of_isComplete [SemilatticeSup β] {K : Set α} (h₁ : IsComplete K)
    {u : β → α} (h₂ : ∀ n, u n ∈ K) (h₃ : CauchySeq u) : ∃ v ∈ K, Tendsto u atTop (𝓝 v) :=
  h₁ _ h₃ <|
    le_principal_iff.2 <|
      mem_map_iff_exists_image.2
        ⟨univ, univ_mem, by
          simp only [image_univ]
          rintro _ ⟨n, rfl⟩
          exact h₂ n⟩
#align cauchy_seq_tendsto_of_is_complete cauchySeq_tendsto_of_isComplete

/- warning: cauchy.le_nhds_Lim -> Cauchy.le_nhds_lim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : CompleteSpace.{u1} α _inst_1] [_inst_3 : Nonempty.{succ u1} α] {f : Filter.{u1} α}, (Cauchy.{u1} α _inst_1 f) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (lim.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) _inst_3 f)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : CompleteSpace.{u1} α _inst_1] [_inst_3 : Nonempty.{succ u1} α] {f : Filter.{u1} α}, (Cauchy.{u1} α _inst_1 f) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (lim.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) _inst_3 f)))
Case conversion may be inaccurate. Consider using '#align cauchy.le_nhds_Lim Cauchy.le_nhds_limₓ'. -/
theorem Cauchy.le_nhds_lim [CompleteSpace α] [Nonempty α] {f : Filter α} (hf : Cauchy f) :
    f ≤ 𝓝 (lim f) :=
  le_nhds_lim (CompleteSpace.complete hf)
#align cauchy.le_nhds_Lim Cauchy.le_nhds_lim

#print CauchySeq.tendsto_limUnder /-
theorem CauchySeq.tendsto_limUnder [SemilatticeSup β] [CompleteSpace α] [Nonempty α] {u : β → α}
    (h : CauchySeq u) : Tendsto u atTop (𝓝 <| limUnder atTop u) :=
  h.le_nhds_lim
#align cauchy_seq.tendsto_lim CauchySeq.tendsto_limUnder
-/

#print IsClosed.isComplete /-
theorem IsClosed.isComplete [CompleteSpace α] {s : Set α} (h : IsClosed s) : IsComplete s :=
  fun f cf fs =>
  let ⟨x, hx⟩ := CompleteSpace.complete cf
  ⟨x, isClosed_iff_clusterPt.mp h x (cf.left.mono (le_inf hx fs)), hx⟩
#align is_closed.is_complete IsClosed.isComplete
-/

#print TotallyBounded /-
/-- A set `s` is totally bounded if for every entourage `d` there is a finite
  set of points `t` such that every element of `s` is `d`-near to some element of `t`. -/
def TotallyBounded (s : Set α) : Prop :=
  ∀ d ∈ 𝓤 α, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, { x | (x, y) ∈ d }
#align totally_bounded TotallyBounded
-/

/- warning: totally_bounded.exists_subset -> TotallyBounded.exists_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α}, (TotallyBounded.{u1} α _inst_1 s) -> (forall {U : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) U (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) => And (Set.Finite.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.unionᵢ.{u1, succ u1} α α (fun (y : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) => setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) U)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α}, (TotallyBounded.{u1} α _inst_1 s) -> (forall {U : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) U (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s) (And (Set.Finite.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.unionᵢ.{u1, succ u1} α α (fun (y : α) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) (fun (h._@.Mathlib.Topology.UniformSpace.Cauchy._hyg.5625 : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) => setOf.{u1} α (fun (x : α) => Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) U)))))))))
Case conversion may be inaccurate. Consider using '#align totally_bounded.exists_subset TotallyBounded.exists_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (t «expr ⊆ » s) -/
theorem TotallyBounded.exists_subset {s : Set α} (hs : TotallyBounded s) {U : Set (α × α)}
    (hU : U ∈ 𝓤 α) : ∃ (t : _)(_ : t ⊆ s), Set.Finite t ∧ s ⊆ ⋃ y ∈ t, { x | (x, y) ∈ U } :=
  by
  rcases comp_symm_of_uniformity hU with ⟨r, hr, rs, rU⟩
  rcases hs r hr with ⟨k, fk, ks⟩
  let u := k ∩ { y | ∃ x ∈ s, (x, y) ∈ r }
  choose hk f hfs hfr using fun x : u => x.coe_prop
  refine' ⟨range f, _, _, _⟩
  · exact range_subset_iff.2 hfs
  · haveI : Fintype u := (fk.inter_of_left _).Fintype
    exact finite_range f
  · intro x xs
    obtain ⟨y, hy, xy⟩ : ∃ y ∈ k, (x, y) ∈ r
    exact mem_Union₂.1 (ks xs)
    rw [bUnion_range, mem_Union]
    set z : ↥u := ⟨y, hy, ⟨x, xs, xy⟩⟩
    exact ⟨z, rU <| mem_compRel.2 ⟨y, xy, rs (hfr z)⟩⟩
#align totally_bounded.exists_subset TotallyBounded.exists_subset

/- warning: totally_bounded_iff_subset -> totallyBounded_iff_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α}, Iff (TotallyBounded.{u1} α _inst_1 s) (forall (d : Set.{u1} (Prod.{u1, u1} α α)), (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) d (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) => And (Set.Finite.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.unionᵢ.{u1, succ u1} α α (fun (y : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) => setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) d)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α}, Iff (TotallyBounded.{u1} α _inst_1 s) (forall (d : Set.{u1} (Prod.{u1, u1} α α)), (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) d (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s) (And (Set.Finite.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.unionᵢ.{u1, succ u1} α α (fun (y : α) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) (fun (h._@.Mathlib.Topology.UniformSpace.Cauchy._hyg.6553 : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) => setOf.{u1} α (fun (x : α) => Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) d)))))))))
Case conversion may be inaccurate. Consider using '#align totally_bounded_iff_subset totallyBounded_iff_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (t «expr ⊆ » s) -/
theorem totallyBounded_iff_subset {s : Set α} :
    TotallyBounded s ↔
      ∀ d ∈ 𝓤 α, ∃ (t : _)(_ : t ⊆ s), Set.Finite t ∧ s ⊆ ⋃ y ∈ t, { x | (x, y) ∈ d } :=
  ⟨fun H d hd => H.exists_subset hd, fun H d hd =>
    let ⟨t, _, ht⟩ := H d hd
    ⟨t, ht⟩⟩
#align totally_bounded_iff_subset totallyBounded_iff_subset

/- warning: filter.has_basis.totally_bounded_iff -> Filter.HasBasis.totallyBounded_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {ι : Sort.{u2}} {p : ι -> Prop} {U : ι -> (Set.{u1} (Prod.{u1, u1} α α))}, (Filter.HasBasis.{u1, u2} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p U) -> (forall {s : Set.{u1} α}, Iff (TotallyBounded.{u1} α _inst_1 s) (forall (i : ι), (p i) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Set.Finite.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.unionᵢ.{u1, succ u1} α α (fun (y : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) => setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) (U i))))))))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : UniformSpace.{u2} α] {ι : Sort.{u1}} {p : ι -> Prop} {U : ι -> (Set.{u2} (Prod.{u2, u2} α α))}, (Filter.HasBasis.{u2, u1} (Prod.{u2, u2} α α) ι (uniformity.{u2} α _inst_1) p U) -> (forall {s : Set.{u2} α}, Iff (TotallyBounded.{u2} α _inst_1 s) (forall (i : ι), (p i) -> (Exists.{succ u2} (Set.{u2} α) (fun (t : Set.{u2} α) => And (Set.Finite.{u2} α t) (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (Set.unionᵢ.{u2, succ u2} α α (fun (y : α) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y t) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y t) => setOf.{u2} α (fun (x : α) => Membership.mem.{u2, u2} (Prod.{u2, u2} α α) (Set.{u2} (Prod.{u2, u2} α α)) (Set.instMembershipSet.{u2} (Prod.{u2, u2} α α)) (Prod.mk.{u2, u2} α α x y) (U i))))))))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.totally_bounded_iff Filter.HasBasis.totallyBounded_iffₓ'. -/
theorem Filter.HasBasis.totallyBounded_iff {ι} {p : ι → Prop} {U : ι → Set (α × α)}
    (H : (𝓤 α).HasBasis p U) {s : Set α} :
    TotallyBounded s ↔ ∀ i, p i → ∃ t : Set α, Set.Finite t ∧ s ⊆ ⋃ y ∈ t, { x | (x, y) ∈ U i } :=
  H.forall_iff fun U V hUV h =>
    h.imp fun t ht => ⟨ht.1, ht.2.trans <| unionᵢ₂_mono fun x hx y hy => hUV hy⟩
#align filter.has_basis.totally_bounded_iff Filter.HasBasis.totallyBounded_iff

#print totallyBounded_of_forall_symm /-
theorem totallyBounded_of_forall_symm {s : Set α}
    (h : ∀ V ∈ 𝓤 α, SymmetricRel V → ∃ t : Set α, Set.Finite t ∧ s ⊆ ⋃ y ∈ t, ball y V) :
    TotallyBounded s :=
  UniformSpace.hasBasis_symmetric.totallyBounded_iff.2 fun V hV => by
    simpa only [ball_eq_of_symmetry hV.2] using h V hV.1 hV.2
#align totally_bounded_of_forall_symm totallyBounded_of_forall_symm
-/

#print totallyBounded_subset /-
theorem totallyBounded_subset {s₁ s₂ : Set α} (hs : s₁ ⊆ s₂) (h : TotallyBounded s₂) :
    TotallyBounded s₁ := fun d hd =>
  let ⟨t, ht₁, ht₂⟩ := h d hd
  ⟨t, ht₁, Subset.trans hs ht₂⟩
#align totally_bounded_subset totallyBounded_subset
-/

#print totallyBounded_empty /-
theorem totallyBounded_empty : TotallyBounded (∅ : Set α) := fun d hd =>
  ⟨∅, finite_empty, empty_subset _⟩
#align totally_bounded_empty totallyBounded_empty
-/

#print TotallyBounded.closure /-
/-- The closure of a totally bounded set is totally bounded. -/
theorem TotallyBounded.closure {s : Set α} (h : TotallyBounded s) : TotallyBounded (closure s) :=
  uniformity_hasBasis_closed.totallyBounded_iff.2 fun V hV =>
    let ⟨t, htf, hst⟩ := h V hV.1
    ⟨t, htf,
      closure_minimal hst <|
        isClosed_bunionᵢ htf fun y hy => hV.2.Preimage (continuous_id.prod_mk continuous_const)⟩
#align totally_bounded.closure TotallyBounded.closure
-/

#print TotallyBounded.image /-
/-- The image of a totally bounded set under a uniformly continuous map is totally bounded. -/
theorem TotallyBounded.image [UniformSpace β] {f : α → β} {s : Set α} (hs : TotallyBounded s)
    (hf : UniformContinuous f) : TotallyBounded (f '' s) := fun t ht =>
  have : { p : α × α | (f p.1, f p.2) ∈ t } ∈ 𝓤 α := hf ht
  let ⟨c, hfc, hct⟩ := hs _ this
  ⟨f '' c, hfc.image f, by
    simp [image_subset_iff]
    simp [subset_def] at hct
    intro x hx; simp
    exact hct x hx⟩
#align totally_bounded.image TotallyBounded.image
-/

/- warning: ultrafilter.cauchy_of_totally_bounded -> Ultrafilter.cauchy_of_totallyBounded is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α} (f : Ultrafilter.{u1} α), (TotallyBounded.{u1} α _inst_1 s) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) f) (Filter.principal.{u1} α s)) -> (Cauchy.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) f))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α} (f : Ultrafilter.{u1} α), (TotallyBounded.{u1} α _inst_1 s) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Ultrafilter.toFilter.{u1} α f) (Filter.principal.{u1} α s)) -> (Cauchy.{u1} α _inst_1 (Ultrafilter.toFilter.{u1} α f))
Case conversion may be inaccurate. Consider using '#align ultrafilter.cauchy_of_totally_bounded Ultrafilter.cauchy_of_totallyBoundedₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Ultrafilter.cauchy_of_totallyBounded {s : Set α} (f : Ultrafilter α) (hs : TotallyBounded s)
    (h : ↑f ≤ 𝓟 s) : Cauchy (f : Filter α) :=
  ⟨f.ne_bot', fun t ht =>
    let ⟨t', ht'₁, ht'_symm, ht'_t⟩ := comp_symm_of_uniformity ht
    let ⟨i, hi, hs_union⟩ := hs t' ht'₁
    have : (⋃ y ∈ i, { x | (x, y) ∈ t' }) ∈ f := mem_of_superset (le_principal_iff.mp h) hs_union
    have : ∃ y ∈ i, { x | (x, y) ∈ t' } ∈ f := (Ultrafilter.finite_bunionᵢ_mem_iff hi).1 this
    let ⟨y, hy, hif⟩ := this
    have : { x | (x, y) ∈ t' } ×ˢ { x | (x, y) ∈ t' } ⊆ compRel t' t' :=
      fun ⟨x₁, x₂⟩ ⟨(h₁ : (x₁, y) ∈ t'), (h₂ : (x₂, y) ∈ t')⟩ => ⟨y, h₁, ht'_symm h₂⟩
    mem_of_superset (prod_mem_prod hif hif) (Subset.trans this ht'_t)⟩
#align ultrafilter.cauchy_of_totally_bounded Ultrafilter.cauchy_of_totallyBounded

/- warning: totally_bounded_iff_filter -> totallyBounded_iff_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α}, Iff (TotallyBounded.{u1} α _inst_1 s) (forall (f : Filter.{u1} α), (Filter.NeBot.{u1} α f) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (Filter.principal.{u1} α s)) -> (Exists.{succ u1} (Filter.{u1} α) (fun (c : Filter.{u1} α) => Exists.{0} (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) c f) (fun (H : LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) c f) => Cauchy.{u1} α _inst_1 c))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α}, Iff (TotallyBounded.{u1} α _inst_1 s) (forall (f : Filter.{u1} α), (Filter.NeBot.{u1} α f) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (Filter.principal.{u1} α s)) -> (Exists.{succ u1} (Filter.{u1} α) (fun (c : Filter.{u1} α) => And (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) c f) (Cauchy.{u1} α _inst_1 c))))
Case conversion may be inaccurate. Consider using '#align totally_bounded_iff_filter totallyBounded_iff_filterₓ'. -/
theorem totallyBounded_iff_filter {s : Set α} :
    TotallyBounded s ↔ ∀ f, NeBot f → f ≤ 𝓟 s → ∃ c ≤ f, Cauchy c :=
  by
  constructor
  · intro H f hf hfs
    exact
      ⟨Ultrafilter.of f, Ultrafilter.of_le f,
        (Ultrafilter.of f).cauchy_of_totallyBounded H ((Ultrafilter.of_le f).trans hfs)⟩
  · intro H d hd
    contrapose! H with hd_cover
    set f := ⨅ t : Finset α, 𝓟 (s \ ⋃ y ∈ t, { x | (x, y) ∈ d })
    have : ne_bot f := by
      refine' infi_ne_bot_of_directed' (directed_of_sup _) _
      · intro t₁ t₂ h
        exact principal_mono.2 (diff_subset_diff_right <| bUnion_subset_bUnion_left h)
      · intro t
        simpa [nonempty_diff] using hd_cover t t.finite_to_set
    have : f ≤ 𝓟 s := infᵢ_le_of_le ∅ (by simp)
    refine' ⟨f, ‹_›, ‹_›, fun c hcf hc => _⟩
    rcases mem_prod_same_iff.1 (hc.2 hd) with ⟨m, hm, hmd⟩
    have : m ∩ s ∈ c := inter_mem hm (le_principal_iff.mp (hcf.trans ‹_›))
    rcases hc.1.nonempty_of_mem this with ⟨y, hym, hys⟩
    set ys := ⋃ y' ∈ ({y} : Finset α), { x | (x, y') ∈ d }
    have : m ⊆ ys := by simpa [ys] using fun x hx => hmd (mk_mem_prod hx hym)
    have : c ≤ 𝓟 (s \ ys) := hcf.trans (infᵢ_le_of_le {y} le_rfl)
    refine' hc.1.Ne (empty_mem_iff_bot.mp _)
    filter_upwards [le_principal_iff.1 this, hm]
    refine' fun x hx hxm => hx.2 _
    simpa [ys] using hmd (mk_mem_prod hxm hym)
#align totally_bounded_iff_filter totallyBounded_iff_filter

/- warning: totally_bounded_iff_ultrafilter -> totallyBounded_iff_ultrafilter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α}, Iff (TotallyBounded.{u1} α _inst_1 s) (forall (f : Ultrafilter.{u1} α), (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) f) (Filter.principal.{u1} α s)) -> (Cauchy.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) f)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α}, Iff (TotallyBounded.{u1} α _inst_1 s) (forall (f : Ultrafilter.{u1} α), (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Ultrafilter.toFilter.{u1} α f) (Filter.principal.{u1} α s)) -> (Cauchy.{u1} α _inst_1 (Ultrafilter.toFilter.{u1} α f)))
Case conversion may be inaccurate. Consider using '#align totally_bounded_iff_ultrafilter totallyBounded_iff_ultrafilterₓ'. -/
theorem totallyBounded_iff_ultrafilter {s : Set α} :
    TotallyBounded s ↔ ∀ f : Ultrafilter α, ↑f ≤ 𝓟 s → Cauchy (f : Filter α) :=
  by
  refine' ⟨fun hs f => f.cauchy_of_totallyBounded hs, fun H => totallyBounded_iff_filter.2 _⟩
  intro f hf hfs
  exact ⟨Ultrafilter.of f, Ultrafilter.of_le f, H _ ((Ultrafilter.of_le f).trans hfs)⟩
#align totally_bounded_iff_ultrafilter totallyBounded_iff_ultrafilter

#print isCompact_iff_totallyBounded_isComplete /-
theorem isCompact_iff_totallyBounded_isComplete {s : Set α} :
    IsCompact s ↔ TotallyBounded s ∧ IsComplete s :=
  ⟨fun hs =>
    ⟨totallyBounded_iff_ultrafilter.2 fun f hf =>
        let ⟨x, xs, fx⟩ := isCompact_iff_ultrafilter_le_nhds.1 hs f hf
        cauchy_nhds.mono fx,
      fun f fc fs =>
      let ⟨a, as, fa⟩ := @hs f fc.1 fs
      ⟨a, as, le_nhds_of_cauchy_adhp fc fa⟩⟩,
    fun ⟨ht, hc⟩ =>
    isCompact_iff_ultrafilter_le_nhds.2 fun f hf =>
      hc _ (totallyBounded_iff_ultrafilter.1 ht f hf) hf⟩
#align is_compact_iff_totally_bounded_is_complete isCompact_iff_totallyBounded_isComplete
-/

#print IsCompact.totallyBounded /-
protected theorem IsCompact.totallyBounded {s : Set α} (h : IsCompact s) : TotallyBounded s :=
  (isCompact_iff_totallyBounded_isComplete.1 h).1
#align is_compact.totally_bounded IsCompact.totallyBounded
-/

#print IsCompact.isComplete /-
protected theorem IsCompact.isComplete {s : Set α} (h : IsCompact s) : IsComplete s :=
  (isCompact_iff_totallyBounded_isComplete.1 h).2
#align is_compact.is_complete IsCompact.isComplete
-/

#print complete_of_compact /-
-- see Note [lower instance priority]
instance (priority := 100) complete_of_compact {α : Type u} [UniformSpace α] [CompactSpace α] :
    CompleteSpace α :=
  ⟨fun f hf => by simpa using (isCompact_iff_totallyBounded_isComplete.1 isCompact_univ).2 f hf⟩
#align complete_of_compact complete_of_compact
-/

#print isCompact_of_totallyBounded_isClosed /-
theorem isCompact_of_totallyBounded_isClosed [CompleteSpace α] {s : Set α} (ht : TotallyBounded s)
    (hc : IsClosed s) : IsCompact s :=
  (@isCompact_iff_totallyBounded_isComplete α _ s).2 ⟨ht, hc.IsComplete⟩
#align is_compact_of_totally_bounded_is_closed isCompact_of_totallyBounded_isClosed
-/

#print CauchySeq.totallyBounded_range /-
/-- Every Cauchy sequence over `ℕ` is totally bounded. -/
theorem CauchySeq.totallyBounded_range {s : ℕ → α} (hs : CauchySeq s) : TotallyBounded (range s) :=
  by
  refine' totallyBounded_iff_subset.2 fun a ha => _
  cases' cauchySeq_iff.1 hs a ha with n hn
  refine' ⟨s '' { k | k ≤ n }, image_subset_range _ _, (finite_le_nat _).image _, _⟩
  rw [range_subset_iff, bUnion_image]
  intro m
  rw [mem_Union₂]
  cases' le_total m n with hm hm
  exacts[⟨m, hm, refl_mem_uniformity ha⟩, ⟨n, le_refl n, hn m hm n le_rfl⟩]
#align cauchy_seq.totally_bounded_range CauchySeq.totallyBounded_range
-/

/-!
### Sequentially complete space

In this section we prove that a uniform space is complete provided that it is sequentially complete
(i.e., any Cauchy sequence converges) and its uniformity filter admits a countable generating set.
In particular, this applies to (e)metric spaces, see the files `topology/metric_space/emetric_space`
and `topology/metric_space/basic`.

More precisely, we assume that there is a sequence of entourages `U_n` such that any other
entourage includes one of `U_n`. Then any Cauchy filter `f` generates a decreasing sequence of
sets `s_n ∈ f` such that `s_n × s_n ⊆ U_n`. Choose a sequence `x_n∈s_n`. It is easy to show
that this is a Cauchy sequence. If this sequence converges to some `a`, then `f ≤ 𝓝 a`. -/


namespace SequentiallyComplete

variable {f : Filter α} (hf : Cauchy f) {U : ℕ → Set (α × α)} (U_mem : ∀ n, U n ∈ 𝓤 α)
  (U_le : ∀ s ∈ 𝓤 α, ∃ n, U n ⊆ s)

open Set Finset

noncomputable section

/- warning: sequentially_complete.set_seq_aux -> SequentiallyComplete.setSeqAux is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {f : Filter.{u1} α}, (Cauchy.{u1} α _inst_1 f) -> (forall {U : Nat -> (Set.{u1} (Prod.{u1, u1} α α))}, (forall (n : Nat), Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) (U n) (uniformity.{u1} α _inst_1)) -> (forall (n : Nat), Subtype.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) (fun (_x : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) => HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) (Set.prod.{u1, u1} α α s s) (U n)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {f : Filter.{u1} α}, (Cauchy.{u1} α _inst_1 f) -> (forall {U : Nat -> (Set.{u1} (Prod.{u1, u1} α α))}, (forall (n : Nat), Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) (U n) (uniformity.{u1} α _inst_1)) -> (forall (n : Nat), Subtype.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} α α)) (Set.prod.{u1, u1} α α s s) (U n)))))
Case conversion may be inaccurate. Consider using '#align sequentially_complete.set_seq_aux SequentiallyComplete.setSeqAuxₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- An auxiliary sequence of sets approximating a Cauchy filter. -/
def setSeqAux (n : ℕ) : { s : Set α // ∃ _ : s ∈ f, s ×ˢ s ⊆ U n } :=
  indefiniteDescription _ <| (cauchy_iff.1 hf).2 (U n) (U_mem n)
#align sequentially_complete.set_seq_aux SequentiallyComplete.setSeqAux

#print SequentiallyComplete.setSeq /-
/-- Given a Cauchy filter `f` and a sequence `U` of entourages, `set_seq` provides
an antitone sequence of sets `s n ∈ f` such that `s n ×ˢ s n ⊆ U`. -/
def setSeq (n : ℕ) : Set α :=
  ⋂ m ∈ Set.Iic n, (setSeqAux hf U_mem m).val
#align sequentially_complete.set_seq SequentiallyComplete.setSeq
-/

#print SequentiallyComplete.setSeq_mem /-
theorem setSeq_mem (n : ℕ) : setSeq hf U_mem n ∈ f :=
  (binterᵢ_mem (finite_le_nat n)).2 fun m _ => (setSeqAux hf U_mem m).2.fst
#align sequentially_complete.set_seq_mem SequentiallyComplete.setSeq_mem
-/

#print SequentiallyComplete.setSeq_mono /-
theorem setSeq_mono ⦃m n : ℕ⦄ (h : m ≤ n) : setSeq hf U_mem n ⊆ setSeq hf U_mem m :=
  binterᵢ_subset_binterᵢ_left fun k hk => le_trans hk h
#align sequentially_complete.set_seq_mono SequentiallyComplete.setSeq_mono
-/

#print SequentiallyComplete.setSeq_sub_aux /-
theorem setSeq_sub_aux (n : ℕ) : setSeq hf U_mem n ⊆ setSeqAux hf U_mem n :=
  binterᵢ_subset_of_mem right_mem_Iic
#align sequentially_complete.set_seq_sub_aux SequentiallyComplete.setSeq_sub_aux
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SequentiallyComplete.setSeq_prod_subset /-
theorem setSeq_prod_subset {N m n} (hm : N ≤ m) (hn : N ≤ n) :
    setSeq hf U_mem m ×ˢ setSeq hf U_mem n ⊆ U N :=
  by
  intro p hp
  refine' (set_seq_aux hf U_mem N).2.snd ⟨_, _⟩ <;> apply set_seq_sub_aux
  exact set_seq_mono hf U_mem hm hp.1
  exact set_seq_mono hf U_mem hn hp.2
#align sequentially_complete.set_seq_prod_subset SequentiallyComplete.setSeq_prod_subset
-/

#print SequentiallyComplete.seq /-
/-- A sequence of points such that `seq n ∈ set_seq n`. Here `set_seq` is an antitone
sequence of sets `set_seq n ∈ f` with diameters controlled by a given sequence
of entourages. -/
def seq (n : ℕ) : α :=
  choose <| hf.1.nonempty_of_mem (setSeq_mem hf U_mem n)
#align sequentially_complete.seq SequentiallyComplete.seq
-/

#print SequentiallyComplete.seq_mem /-
theorem seq_mem (n : ℕ) : seq hf U_mem n ∈ setSeq hf U_mem n :=
  choose_spec <| hf.1.nonempty_of_mem (setSeq_mem hf U_mem n)
#align sequentially_complete.seq_mem SequentiallyComplete.seq_mem
-/

#print SequentiallyComplete.seq_pair_mem /-
theorem seq_pair_mem ⦃N m n : ℕ⦄ (hm : N ≤ m) (hn : N ≤ n) :
    (seq hf U_mem m, seq hf U_mem n) ∈ U N :=
  setSeq_prod_subset hf U_mem hm hn ⟨seq_mem hf U_mem m, seq_mem hf U_mem n⟩
#align sequentially_complete.seq_pair_mem SequentiallyComplete.seq_pair_mem
-/

include U_le

#print SequentiallyComplete.seq_is_cauchySeq /-
theorem seq_is_cauchySeq : CauchySeq <| seq hf U_mem :=
  cauchySeq_of_controlled U U_le <| seq_pair_mem hf U_mem
#align sequentially_complete.seq_is_cauchy_seq SequentiallyComplete.seq_is_cauchySeq
-/

/- warning: sequentially_complete.le_nhds_of_seq_tendsto_nhds -> SequentiallyComplete.le_nhds_of_seq_tendsto_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {f : Filter.{u1} α} (hf : Cauchy.{u1} α _inst_1 f) {U : Nat -> (Set.{u1} (Prod.{u1, u1} α α))} (U_mem : forall (n : Nat), Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) (U n) (uniformity.{u1} α _inst_1)), (forall (s : Set.{u1} (Prod.{u1, u1} α α)), (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{1} Nat (fun (n : Nat) => HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) (U n) s))) -> (forall {{a : α}}, (Filter.Tendsto.{0, u1} Nat α (SequentiallyComplete.seq.{u1} α _inst_1 f hf (fun (n : Nat) => U n) U_mem) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) a)) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {f : Filter.{u1} α} (hf : Cauchy.{u1} α _inst_1 f) {U : Nat -> (Set.{u1} (Prod.{u1, u1} α α))} (U_mem : forall (n : Nat), Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) (U n) (uniformity.{u1} α _inst_1)), (forall (s : Set.{u1} (Prod.{u1, u1} α α)), (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{1} Nat (fun (n : Nat) => HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} α α)) (U n) s))) -> (forall {{a : α}}, (Filter.Tendsto.{0, u1} Nat α (SequentiallyComplete.seq.{u1} α _inst_1 f hf (fun (n : Nat) => U n) U_mem) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) a)) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) a)))
Case conversion may be inaccurate. Consider using '#align sequentially_complete.le_nhds_of_seq_tendsto_nhds SequentiallyComplete.le_nhds_of_seq_tendsto_nhdsₓ'. -/
/-- If the sequence `sequentially_complete.seq` converges to `a`, then `f ≤ 𝓝 a`. -/
theorem le_nhds_of_seq_tendsto_nhds ⦃a : α⦄ (ha : Tendsto (seq hf U_mem) atTop (𝓝 a)) : f ≤ 𝓝 a :=
  le_nhds_of_cauchy_adhp_aux
    (by
      intro s hs
      rcases U_le s hs with ⟨m, hm⟩
      rcases tendsto_at_top'.1 ha _ (mem_nhds_left a (U_mem m)) with ⟨n, hn⟩
      refine'
        ⟨set_seq hf U_mem (max m n), set_seq_mem hf U_mem _, _, seq hf U_mem (max m n), _,
          seq_mem hf U_mem _⟩
      · have := le_max_left m n
        exact Set.Subset.trans (set_seq_prod_subset hf U_mem this this) hm
      · exact hm (hn _ <| le_max_right m n))
#align sequentially_complete.le_nhds_of_seq_tendsto_nhds SequentiallyComplete.le_nhds_of_seq_tendsto_nhds

end SequentiallyComplete

namespace UniformSpace

open SequentiallyComplete

variable [IsCountablyGenerated (𝓤 α)]

#print UniformSpace.complete_of_convergent_controlled_sequences /-
/-- A uniform space is complete provided that (a) its uniformity filter has a countable basis;
(b) any sequence satisfying a "controlled" version of the Cauchy condition converges. -/
theorem complete_of_convergent_controlled_sequences (U : ℕ → Set (α × α)) (U_mem : ∀ n, U n ∈ 𝓤 α)
    (HU : ∀ u : ℕ → α, (∀ N m n, N ≤ m → N ≤ n → (u m, u n) ∈ U N) → ∃ a, Tendsto u atTop (𝓝 a)) :
    CompleteSpace α :=
  by
  obtain ⟨U', U'_mono, hU'⟩ := (𝓤 α).exists_antitone_seq
  have Hmem : ∀ n, U n ∩ U' n ∈ 𝓤 α := fun n => inter_mem (U_mem n) (hU'.2 ⟨n, subset.refl _⟩)
  refine'
    ⟨fun f hf =>
      (HU (seq hf Hmem) fun N m n hm hn => _).imp <| le_nhds_of_seq_tendsto_nhds _ _ fun s hs => _⟩
  · rcases hU'.1 hs with ⟨N, hN⟩
    exact ⟨N, subset.trans (inter_subset_right _ _) hN⟩
  · exact inter_subset_left _ _ (seq_pair_mem hf Hmem hm hn)
#align uniform_space.complete_of_convergent_controlled_sequences UniformSpace.complete_of_convergent_controlled_sequences
-/

#print UniformSpace.complete_of_cauchySeq_tendsto /-
/-- A sequentially complete uniform space with a countable basis of the uniformity filter is
complete. -/
theorem complete_of_cauchySeq_tendsto (H' : ∀ u : ℕ → α, CauchySeq u → ∃ a, Tendsto u atTop (𝓝 a)) :
    CompleteSpace α :=
  let ⟨U', U'_mono, hU'⟩ := (𝓤 α).exists_antitone_seq
  complete_of_convergent_controlled_sequences U' (fun n => hU'.2 ⟨n, Subset.refl _⟩) fun u hu =>
    H' u <| cauchySeq_of_controlled U' (fun s hs => hU'.1 hs) hu
#align uniform_space.complete_of_cauchy_seq_tendsto UniformSpace.complete_of_cauchySeq_tendsto
-/

variable (α)

#print UniformSpace.firstCountableTopology /-
instance (priority := 100) firstCountableTopology : FirstCountableTopology α :=
  ⟨fun a => by
    rw [nhds_eq_comap_uniformity]
    infer_instance⟩
#align uniform_space.first_countable_topology UniformSpace.firstCountableTopology
-/

#print UniformSpace.secondCountable_of_separable /-
/-- A separable uniform space with countably generated uniformity filter is second countable:
one obtains a countable basis by taking the balls centered at points in a dense subset,
and with rational "radii" from a countable open symmetric antitone basis of `𝓤 α`. We do not
register this as an instance, as there is already an instance going in the other direction
from second countable spaces to separable spaces, and we want to avoid loops. -/
theorem secondCountable_of_separable [SeparableSpace α] : SecondCountableTopology α :=
  by
  rcases exists_countable_dense α with ⟨s, hsc, hsd⟩
  obtain
    ⟨t : ℕ → Set (α × α), hto : ∀ i : ℕ, t i ∈ (𝓤 α).sets ∧ IsOpen (t i) ∧ SymmetricRel (t i),
      h_basis : (𝓤 α).HasAntitoneBasis t⟩ :=
    (@uniformity_hasBasis_open_symmetric α _).exists_antitone_subbasis
  choose ht_mem hto hts using hto
  refine' ⟨⟨⋃ x ∈ s, range fun k => ball x (t k), hsc.bUnion fun x hx => countable_range _, _⟩⟩
  refine' (is_topological_basis_of_open_of_nhds _ _).eq_generateFrom
  · simp only [mem_Union₂, mem_range]
    rintro _ ⟨x, hxs, k, rfl⟩
    exact is_open_ball x (hto k)
  · intro x V hxV hVo
    simp only [mem_Union₂, mem_range, exists_prop]
    rcases UniformSpace.mem_nhds_iff.1 (IsOpen.mem_nhds hVo hxV) with ⟨U, hU, hUV⟩
    rcases comp_symm_of_uniformity hU with ⟨U', hU', hsymm, hUU'⟩
    rcases h_basis.to_has_basis.mem_iff.1 hU' with ⟨k, -, hk⟩
    rcases hsd.inter_open_nonempty (ball x <| t k) (is_open_ball x (hto k))
        ⟨x, UniformSpace.mem_ball_self _ (ht_mem k)⟩ with
      ⟨y, hxy, hys⟩
    refine' ⟨_, ⟨y, hys, k, rfl⟩, (hts k).Subset hxy, fun z hz => _⟩
    exact hUV (ball_subset_of_comp_subset (hk hxy) hUU' (hk hz))
#align uniform_space.second_countable_of_separable UniformSpace.secondCountable_of_separable
-/

end UniformSpace

