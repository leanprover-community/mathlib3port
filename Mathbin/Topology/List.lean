/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module topology.list
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Constructions
import Mathbin.Topology.Algebra.Monoid

/-!
# Topology on lists and vectors

-/


open TopologicalSpace Set Filter

open Topology Filter

variable {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

instance : TopologicalSpace (List α) :=
  TopologicalSpace.mkOfNhds (traverse nhds)

/- warning: nhds_list -> nhds_list is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (as : List.{u1} α), Eq.{succ u1} (Filter.{u1} (List.{u1} α)) (nhds.{u1} (List.{u1} α) (List.topologicalSpace.{u1} α _inst_1) as) (Traversable.traverse.{u1} List.{u1} List.traversable.{u1} Filter.{u1} Filter.applicative.{u1} α α (nhds.{u1} α _inst_1) as)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (as : List.{u1} α), Eq.{succ u1} (Filter.{u1} (List.{u1} α)) (nhds.{u1} (List.{u1} α) (instTopologicalSpaceList.{u1} α _inst_1) as) (Traversable.traverse.{u1} List.{u1} instTraversableList.{u1} Filter.{u1} (Alternative.toApplicative.{u1, u1} Filter.{u1} Filter.instAlternativeFilter.{u1}) α α (nhds.{u1} α _inst_1) as)
Case conversion may be inaccurate. Consider using '#align nhds_list nhds_listₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem nhds_list (as : List α) : 𝓝 as = traverse 𝓝 as :=
  by
  refine' nhds_mk_of_nhds _ _ _ _
  · intro l
    induction l
    case nil => exact le_rfl
    case
      cons a l ih =>
      suffices List.cons <$> pure a <*> pure l ≤ List.cons <$> 𝓝 a <*> traverse 𝓝 l by
        simpa only [functor_norm] using this
      exact Filter.seq_mono (Filter.map_mono <| pure_le_nhds a) ih
  · intro l s hs
    rcases(mem_traverse_iff _ _).1 hs with ⟨u, hu, hus⟩
    clear as hs
    have : ∃ v : List (Set α), l.forall₂ (fun a s => IsOpen s ∧ a ∈ s) v ∧ sequence v ⊆ s :=
      by
      induction hu generalizing s
      case nil hs this => exists ; simpa only [List.forall₂_nil_left_iff, exists_eq_left]
      case
        cons a s as ss ht h ih t hts =>
        rcases mem_nhds_iff.1 ht with ⟨u, hut, hu⟩
        rcases ih _ subset.rfl with ⟨v, hv, hvss⟩
        exact
          ⟨u::v, List.Forall₂.cons hu hv,
            subset.trans (Set.seq_mono (Set.image_subset _ hut) hvss) hts⟩
    rcases this with ⟨v, hv, hvs⟩
    refine' ⟨sequence v, mem_traverse _ _ _, hvs, _⟩
    · exact hv.imp fun a s ⟨hs, ha⟩ => IsOpen.mem_nhds hs ha
    · intro u hu
      have hu := (List.mem_traverse _ _).1 hu
      have : List.Forall₂ (fun a s => IsOpen s ∧ a ∈ s) u v :=
        by
        refine' List.Forall₂.flip _
        replace hv := hv.flip
        simp only [List.forall₂_and_left, flip] at hv⊢
        exact ⟨hv.1, hu.flip⟩
      refine' mem_of_superset _ hvs
      exact mem_traverse _ _ (this.imp fun a s ⟨hs, ha⟩ => IsOpen.mem_nhds hs ha)
#align nhds_list nhds_list

/- warning: nhds_nil -> nhds_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (Filter.{u1} (List.{u1} α)) (nhds.{u1} (List.{u1} α) (List.topologicalSpace.{u1} α _inst_1) (List.nil.{u1} α)) (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} (List.{u1} α) (List.nil.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (Filter.{u1} (List.{u1} α)) (nhds.{u1} (List.{u1} α) (instTopologicalSpaceList.{u1} α _inst_1) (List.nil.{u1} α)) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} (List.{u1} α) (List.nil.{u1} α))
Case conversion may be inaccurate. Consider using '#align nhds_nil nhds_nilₓ'. -/
@[simp]
theorem nhds_nil : 𝓝 ([] : List α) = pure [] := by
  rw [nhds_list, List.traverse_nil _] <;> infer_instance
#align nhds_nil nhds_nil

/- warning: nhds_cons -> nhds_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α) (l : List.{u1} α), Eq.{succ u1} (Filter.{u1} (List.{u1} α)) (nhds.{u1} (List.{u1} α) (List.topologicalSpace.{u1} α _inst_1) (List.cons.{u1} α a l)) (Seq.seq.{u1, u1} Filter.{u1} Filter.hasSeq.{u1} (List.{u1} α) (List.{u1} α) (Functor.map.{u1, u1} Filter.{u1} Filter.functor.{u1} α ((List.{u1} α) -> (List.{u1} α)) (List.cons.{u1} α) (nhds.{u1} α _inst_1 a)) (nhds.{u1} (List.{u1} α) (List.topologicalSpace.{u1} α _inst_1) l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α) (l : List.{u1} α), Eq.{succ u1} (Filter.{u1} (List.{u1} α)) (nhds.{u1} (List.{u1} α) (instTopologicalSpaceList.{u1} α _inst_1) (List.cons.{u1} α a l)) (Seq.seq.{u1, u1} Filter.{u1} (Applicative.toSeq.{u1, u1} Filter.{u1} (Alternative.toApplicative.{u1, u1} Filter.{u1} Filter.instAlternativeFilter.{u1})) (List.{u1} α) (List.{u1} α) (Functor.map.{u1, u1} Filter.{u1} Filter.instFunctorFilter.{u1} α ((List.{u1} α) -> (List.{u1} α)) (List.cons.{u1} α) (nhds.{u1} α _inst_1 a)) (fun (x._@.Mathlib.Topology.List._hyg.621 : Unit) => nhds.{u1} (List.{u1} α) (instTopologicalSpaceList.{u1} α _inst_1) l))
Case conversion may be inaccurate. Consider using '#align nhds_cons nhds_consₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem nhds_cons (a : α) (l : List α) : 𝓝 (a::l) = List.cons <$> 𝓝 a <*> 𝓝 l := by
  rw [nhds_list, List.traverse_cons _, ← nhds_list] <;> infer_instance
#align nhds_cons nhds_cons

/- warning: list.tendsto_cons -> List.tendsto_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {l : List.{u1} α}, Filter.Tendsto.{u1, u1} (Prod.{u1, u1} α (List.{u1} α)) (List.{u1} α) (fun (p : Prod.{u1, u1} α (List.{u1} α)) => List.cons.{u1} α (Prod.fst.{u1, u1} α (List.{u1} α) p) (Prod.snd.{u1, u1} α (List.{u1} α) p)) (Filter.prod.{u1, u1} α (List.{u1} α) (nhds.{u1} α _inst_1 a) (nhds.{u1} (List.{u1} α) (List.topologicalSpace.{u1} α _inst_1) l)) (nhds.{u1} (List.{u1} α) (List.topologicalSpace.{u1} α _inst_1) (List.cons.{u1} α a l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {l : List.{u1} α}, Filter.Tendsto.{u1, u1} (Prod.{u1, u1} α (List.{u1} α)) (List.{u1} α) (fun (p : Prod.{u1, u1} α (List.{u1} α)) => List.cons.{u1} α (Prod.fst.{u1, u1} α (List.{u1} α) p) (Prod.snd.{u1, u1} α (List.{u1} α) p)) (Filter.prod.{u1, u1} α (List.{u1} α) (nhds.{u1} α _inst_1 a) (nhds.{u1} (List.{u1} α) (instTopologicalSpaceList.{u1} α _inst_1) l)) (nhds.{u1} (List.{u1} α) (instTopologicalSpaceList.{u1} α _inst_1) (List.cons.{u1} α a l))
Case conversion may be inaccurate. Consider using '#align list.tendsto_cons List.tendsto_consₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem List.tendsto_cons {a : α} {l : List α} :
    Tendsto (fun p : α × List α => List.cons p.1 p.2) (𝓝 a ×ᶠ 𝓝 l) (𝓝 (a::l)) := by
  rw [nhds_cons, tendsto, Filter.map_prod] <;> exact le_rfl
#align list.tendsto_cons List.tendsto_cons

/- warning: filter.tendsto.cons -> Filter.Tendsto.cons is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {α : Type.{u2}} {f : α -> β} {g : α -> (List.{u1} β)} {a : Filter.{u2} α} {b : β} {l : List.{u1} β}, (Filter.Tendsto.{u2, u1} α β f a (nhds.{u1} β _inst_2 b)) -> (Filter.Tendsto.{u2, u1} α (List.{u1} β) g a (nhds.{u1} (List.{u1} β) (List.topologicalSpace.{u1} β _inst_2) l)) -> (Filter.Tendsto.{u2, u1} α (List.{u1} β) (fun (a : α) => List.cons.{u1} β (f a) (g a)) a (nhds.{u1} (List.{u1} β) (List.topologicalSpace.{u1} β _inst_2) (List.cons.{u1} β b l)))
but is expected to have type
  forall {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {α : Type.{u2}} {f : α -> β} {g : α -> (List.{u1} β)} {a : Filter.{u2} α} {b : β} {l : List.{u1} β}, (Filter.Tendsto.{u2, u1} α β f a (nhds.{u1} β _inst_2 b)) -> (Filter.Tendsto.{u2, u1} α (List.{u1} β) g a (nhds.{u1} (List.{u1} β) (instTopologicalSpaceList.{u1} β _inst_2) l)) -> (Filter.Tendsto.{u2, u1} α (List.{u1} β) (fun (a : α) => List.cons.{u1} β (f a) (g a)) a (nhds.{u1} (List.{u1} β) (instTopologicalSpaceList.{u1} β _inst_2) (List.cons.{u1} β b l)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.cons Filter.Tendsto.consₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Filter.Tendsto.cons {α : Type _} {f : α → β} {g : α → List β} {a : Filter α} {b : β}
    {l : List β} (hf : Tendsto f a (𝓝 b)) (hg : Tendsto g a (𝓝 l)) :
    Tendsto (fun a => List.cons (f a) (g a)) a (𝓝 (b::l)) :=
  List.tendsto_cons.comp (Tendsto.prod_mk hf hg)
#align filter.tendsto.cons Filter.Tendsto.cons

namespace List

/- warning: list.tendsto_cons_iff -> List.tendsto_cons_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} {f : (List.{u1} α) -> β} {b : Filter.{u2} β} {a : α} {l : List.{u1} α}, Iff (Filter.Tendsto.{u1, u2} (List.{u1} α) β f (nhds.{u1} (List.{u1} α) (List.topologicalSpace.{u1} α _inst_1) (List.cons.{u1} α a l)) b) (Filter.Tendsto.{u1, u2} (Prod.{u1, u1} α (List.{u1} α)) β (fun (p : Prod.{u1, u1} α (List.{u1} α)) => f (List.cons.{u1} α (Prod.fst.{u1, u1} α (List.{u1} α) p) (Prod.snd.{u1, u1} α (List.{u1} α) p))) (Filter.prod.{u1, u1} α (List.{u1} α) (nhds.{u1} α _inst_1 a) (nhds.{u1} (List.{u1} α) (List.topologicalSpace.{u1} α _inst_1) l)) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} {f : (List.{u1} α) -> β} {b : Filter.{u2} β} {a : α} {l : List.{u1} α}, Iff (Filter.Tendsto.{u1, u2} (List.{u1} α) β f (nhds.{u1} (List.{u1} α) (instTopologicalSpaceList.{u1} α _inst_1) (List.cons.{u1} α a l)) b) (Filter.Tendsto.{u1, u2} (Prod.{u1, u1} α (List.{u1} α)) β (fun (p : Prod.{u1, u1} α (List.{u1} α)) => f (List.cons.{u1} α (Prod.fst.{u1, u1} α (List.{u1} α) p) (Prod.snd.{u1, u1} α (List.{u1} α) p))) (Filter.prod.{u1, u1} α (List.{u1} α) (nhds.{u1} α _inst_1 a) (nhds.{u1} (List.{u1} α) (instTopologicalSpaceList.{u1} α _inst_1) l)) b)
Case conversion may be inaccurate. Consider using '#align list.tendsto_cons_iff List.tendsto_cons_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem tendsto_cons_iff {β : Type _} {f : List α → β} {b : Filter β} {a : α} {l : List α} :
    Tendsto f (𝓝 (a::l)) b ↔ Tendsto (fun p : α × List α => f (p.1::p.2)) (𝓝 a ×ᶠ 𝓝 l) b :=
  by
  have : 𝓝 (a::l) = (𝓝 a ×ᶠ 𝓝 l).map fun p : α × List α => p.1::p.2 :=
    by
    simp only [nhds_cons, Filter.prod_eq, (Filter.map_def _ _).symm,
      (Filter.seq_eq_filter_seq _ _).symm]
    simp [-Filter.seq_eq_filter_seq, -Filter.map_def, (· ∘ ·), functor_norm]
  rw [this, Filter.tendsto_map'_iff]
#align list.tendsto_cons_iff List.tendsto_cons_iff

/- warning: list.continuous_cons -> List.continuous_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Continuous.{u1, u1} (Prod.{u1, u1} α (List.{u1} α)) (List.{u1} α) (Prod.topologicalSpace.{u1, u1} α (List.{u1} α) _inst_1 (List.topologicalSpace.{u1} α _inst_1)) (List.topologicalSpace.{u1} α _inst_1) (fun (x : Prod.{u1, u1} α (List.{u1} α)) => List.cons.{u1} α (Prod.fst.{u1, u1} α (List.{u1} α) x) (Prod.snd.{u1, u1} α (List.{u1} α) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Continuous.{u1, u1} (Prod.{u1, u1} α (List.{u1} α)) (List.{u1} α) (instTopologicalSpaceProd.{u1, u1} α (List.{u1} α) _inst_1 (instTopologicalSpaceList.{u1} α _inst_1)) (instTopologicalSpaceList.{u1} α _inst_1) (fun (x : Prod.{u1, u1} α (List.{u1} α)) => List.cons.{u1} α (Prod.fst.{u1, u1} α (List.{u1} α) x) (Prod.snd.{u1, u1} α (List.{u1} α) x))
Case conversion may be inaccurate. Consider using '#align list.continuous_cons List.continuous_consₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem continuous_cons : Continuous fun x : α × List α => (x.1::x.2 : List α) :=
  continuous_iff_continuousAt.mpr fun ⟨x, y⟩ => continuousAt_fst.cons continuousAt_snd
#align list.continuous_cons List.continuous_cons

/- warning: list.tendsto_nhds -> List.tendsto_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} {f : (List.{u1} α) -> β} {r : (List.{u1} α) -> (Filter.{u2} β)}, (Filter.Tendsto.{u1, u2} (List.{u1} α) β f (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} (List.{u1} α) (List.nil.{u1} α)) (r (List.nil.{u1} α))) -> (forall (l : List.{u1} α) (a : α), (Filter.Tendsto.{u1, u2} (List.{u1} α) β f (nhds.{u1} (List.{u1} α) (List.topologicalSpace.{u1} α _inst_1) l) (r l)) -> (Filter.Tendsto.{u1, u2} (Prod.{u1, u1} α (List.{u1} α)) β (fun (p : Prod.{u1, u1} α (List.{u1} α)) => f (List.cons.{u1} α (Prod.fst.{u1, u1} α (List.{u1} α) p) (Prod.snd.{u1, u1} α (List.{u1} α) p))) (Filter.prod.{u1, u1} α (List.{u1} α) (nhds.{u1} α _inst_1 a) (nhds.{u1} (List.{u1} α) (List.topologicalSpace.{u1} α _inst_1) l)) (r (List.cons.{u1} α a l)))) -> (forall (l : List.{u1} α), Filter.Tendsto.{u1, u2} (List.{u1} α) β f (nhds.{u1} (List.{u1} α) (List.topologicalSpace.{u1} α _inst_1) l) (r l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} {f : (List.{u1} α) -> β} {r : (List.{u1} α) -> (Filter.{u2} β)}, (Filter.Tendsto.{u1, u2} (List.{u1} α) β f (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} (List.{u1} α) (List.nil.{u1} α)) (r (List.nil.{u1} α))) -> (forall (l : List.{u1} α) (a : α), (Filter.Tendsto.{u1, u2} (List.{u1} α) β f (nhds.{u1} (List.{u1} α) (instTopologicalSpaceList.{u1} α _inst_1) l) (r l)) -> (Filter.Tendsto.{u1, u2} (Prod.{u1, u1} α (List.{u1} α)) β (fun (p : Prod.{u1, u1} α (List.{u1} α)) => f (List.cons.{u1} α (Prod.fst.{u1, u1} α (List.{u1} α) p) (Prod.snd.{u1, u1} α (List.{u1} α) p))) (Filter.prod.{u1, u1} α (List.{u1} α) (nhds.{u1} α _inst_1 a) (nhds.{u1} (List.{u1} α) (instTopologicalSpaceList.{u1} α _inst_1) l)) (r (List.cons.{u1} α a l)))) -> (forall (l : List.{u1} α), Filter.Tendsto.{u1, u2} (List.{u1} α) β f (nhds.{u1} (List.{u1} α) (instTopologicalSpaceList.{u1} α _inst_1) l) (r l))
Case conversion may be inaccurate. Consider using '#align list.tendsto_nhds List.tendsto_nhdsₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem tendsto_nhds {β : Type _} {f : List α → β} {r : List α → Filter β}
    (h_nil : Tendsto f (pure []) (r []))
    (h_cons :
      ∀ l a,
        Tendsto f (𝓝 l) (r l) →
          Tendsto (fun p : α × List α => f (p.1::p.2)) (𝓝 a ×ᶠ 𝓝 l) (r (a::l))) :
    ∀ l, Tendsto f (𝓝 l) (r l)
  | [] => by rwa [nhds_nil]
  | a::l => by rw [tendsto_cons_iff] <;> exact h_cons l a (tendsto_nhds l)
#align list.tendsto_nhds List.tendsto_nhds

/- warning: list.continuous_at_length -> List.continuousAt_length is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (l : List.{u1} α), ContinuousAt.{u1, 0} (List.{u1} α) Nat (List.topologicalSpace.{u1} α _inst_1) Nat.topologicalSpace (List.length.{u1} α) l
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (l : List.{u1} α), ContinuousAt.{u1, 0} (List.{u1} α) Nat (instTopologicalSpaceList.{u1} α _inst_1) instTopologicalSpaceNat (List.length.{u1} α) l
Case conversion may be inaccurate. Consider using '#align list.continuous_at_length List.continuousAt_lengthₓ'. -/
theorem continuousAt_length : ∀ l : List α, ContinuousAt List.length l :=
  by
  simp only [ContinuousAt, nhds_discrete]
  refine' tendsto_nhds _ _
  · exact tendsto_pure_pure _ _
  · intro l a ih
    dsimp only [List.length]
    refine' tendsto.comp (tendsto_pure_pure (fun x => x + 1) _) _
    refine' tendsto.comp ih tendsto_snd
#align list.continuous_at_length List.continuousAt_length

/- warning: list.tendsto_insert_nth' -> List.tendsto_insert_nth' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {n : Nat} {l : List.{u1} α}, Filter.Tendsto.{u1, u1} (Prod.{u1, u1} α (List.{u1} α)) (List.{u1} α) (fun (p : Prod.{u1, u1} α (List.{u1} α)) => List.insertNth.{u1} α n (Prod.fst.{u1, u1} α (List.{u1} α) p) (Prod.snd.{u1, u1} α (List.{u1} α) p)) (Filter.prod.{u1, u1} α (List.{u1} α) (nhds.{u1} α _inst_1 a) (nhds.{u1} (List.{u1} α) (List.topologicalSpace.{u1} α _inst_1) l)) (nhds.{u1} (List.{u1} α) (List.topologicalSpace.{u1} α _inst_1) (List.insertNth.{u1} α n a l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {n : Nat} {l : List.{u1} α}, Filter.Tendsto.{u1, u1} (Prod.{u1, u1} α (List.{u1} α)) (List.{u1} α) (fun (p : Prod.{u1, u1} α (List.{u1} α)) => List.insertNth.{u1} α n (Prod.fst.{u1, u1} α (List.{u1} α) p) (Prod.snd.{u1, u1} α (List.{u1} α) p)) (Filter.prod.{u1, u1} α (List.{u1} α) (nhds.{u1} α _inst_1 a) (nhds.{u1} (List.{u1} α) (instTopologicalSpaceList.{u1} α _inst_1) l)) (nhds.{u1} (List.{u1} α) (instTopologicalSpaceList.{u1} α _inst_1) (List.insertNth.{u1} α n a l))
Case conversion may be inaccurate. Consider using '#align list.tendsto_insert_nth' List.tendsto_insert_nth'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem tendsto_insert_nth' {a : α} :
    ∀ {n : ℕ} {l : List α},
      Tendsto (fun p : α × List α => insertNth n p.1 p.2) (𝓝 a ×ᶠ 𝓝 l) (𝓝 (insertNth n a l))
  | 0, l => tendsto_cons
  | n + 1, [] => by simp
  | n + 1, a'::l =>
    by
    have :
      𝓝 a ×ᶠ 𝓝 (a'::l) = (𝓝 a ×ᶠ (𝓝 a' ×ᶠ 𝓝 l)).map fun p : α × α × List α => (p.1, p.2.1::p.2.2) :=
      by
      simp only [nhds_cons, Filter.prod_eq, ← Filter.map_def, ← Filter.seq_eq_filter_seq]
      simp [-Filter.seq_eq_filter_seq, -Filter.map_def, (· ∘ ·), functor_norm]
    rw [this, tendsto_map'_iff]
    exact
      (tendsto_fst.comp tendsto_snd).cons
        ((@tendsto_insert_nth' n l).comp <| tendsto_fst.prod_mk <| tendsto_snd.comp tendsto_snd)
#align list.tendsto_insert_nth' List.tendsto_insert_nth'

/- warning: list.tendsto_insert_nth -> List.tendsto_insertNth is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} {n : Nat} {a : α} {l : List.{u1} α} {f : β -> α} {g : β -> (List.{u1} α)} {b : Filter.{u2} β}, (Filter.Tendsto.{u2, u1} β α f b (nhds.{u1} α _inst_1 a)) -> (Filter.Tendsto.{u2, u1} β (List.{u1} α) g b (nhds.{u1} (List.{u1} α) (List.topologicalSpace.{u1} α _inst_1) l)) -> (Filter.Tendsto.{u2, u1} β (List.{u1} α) (fun (b : β) => List.insertNth.{u1} α n (f b) (g b)) b (nhds.{u1} (List.{u1} α) (List.topologicalSpace.{u1} α _inst_1) (List.insertNth.{u1} α n a l)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} {n : Nat} {a : α} {l : List.{u1} α} {f : β -> α} {g : β -> (List.{u1} α)} {b : Filter.{u2} β}, (Filter.Tendsto.{u2, u1} β α f b (nhds.{u1} α _inst_1 a)) -> (Filter.Tendsto.{u2, u1} β (List.{u1} α) g b (nhds.{u1} (List.{u1} α) (instTopologicalSpaceList.{u1} α _inst_1) l)) -> (Filter.Tendsto.{u2, u1} β (List.{u1} α) (fun (b : β) => List.insertNth.{u1} α n (f b) (g b)) b (nhds.{u1} (List.{u1} α) (instTopologicalSpaceList.{u1} α _inst_1) (List.insertNth.{u1} α n a l)))
Case conversion may be inaccurate. Consider using '#align list.tendsto_insert_nth List.tendsto_insertNthₓ'. -/
theorem tendsto_insertNth {β} {n : ℕ} {a : α} {l : List α} {f : β → α} {g : β → List α}
    {b : Filter β} (hf : Tendsto f b (𝓝 a)) (hg : Tendsto g b (𝓝 l)) :
    Tendsto (fun b : β => insertNth n (f b) (g b)) b (𝓝 (insertNth n a l)) :=
  tendsto_insert_nth'.comp (Tendsto.prod_mk hf hg)
#align list.tendsto_insert_nth List.tendsto_insertNth

/- warning: list.continuous_insert_nth -> List.continuous_insertNth is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat}, Continuous.{u1, u1} (Prod.{u1, u1} α (List.{u1} α)) (List.{u1} α) (Prod.topologicalSpace.{u1, u1} α (List.{u1} α) _inst_1 (List.topologicalSpace.{u1} α _inst_1)) (List.topologicalSpace.{u1} α _inst_1) (fun (p : Prod.{u1, u1} α (List.{u1} α)) => List.insertNth.{u1} α n (Prod.fst.{u1, u1} α (List.{u1} α) p) (Prod.snd.{u1, u1} α (List.{u1} α) p))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat}, Continuous.{u1, u1} (Prod.{u1, u1} α (List.{u1} α)) (List.{u1} α) (instTopologicalSpaceProd.{u1, u1} α (List.{u1} α) _inst_1 (instTopologicalSpaceList.{u1} α _inst_1)) (instTopologicalSpaceList.{u1} α _inst_1) (fun (p : Prod.{u1, u1} α (List.{u1} α)) => List.insertNth.{u1} α n (Prod.fst.{u1, u1} α (List.{u1} α) p) (Prod.snd.{u1, u1} α (List.{u1} α) p))
Case conversion may be inaccurate. Consider using '#align list.continuous_insert_nth List.continuous_insertNthₓ'. -/
theorem continuous_insertNth {n : ℕ} : Continuous fun p : α × List α => insertNth n p.1 p.2 :=
  continuous_iff_continuousAt.mpr fun ⟨a, l⟩ => by
    rw [ContinuousAt, nhds_prod_eq] <;> exact tendsto_insert_nth'
#align list.continuous_insert_nth List.continuous_insertNth

/- warning: list.tendsto_remove_nth -> List.tendsto_removeNth is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat} {l : List.{u1} α}, Filter.Tendsto.{u1, u1} (List.{u1} α) (List.{u1} α) (fun (l : List.{u1} α) => List.removeNth.{u1} α l n) (nhds.{u1} (List.{u1} α) (List.topologicalSpace.{u1} α _inst_1) l) (nhds.{u1} (List.{u1} α) (List.topologicalSpace.{u1} α _inst_1) (List.removeNth.{u1} α l n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat} {l : List.{u1} α}, Filter.Tendsto.{u1, u1} (List.{u1} α) (List.{u1} α) (fun (l : List.{u1} α) => List.removeNth.{u1} α l n) (nhds.{u1} (List.{u1} α) (instTopologicalSpaceList.{u1} α _inst_1) l) (nhds.{u1} (List.{u1} α) (instTopologicalSpaceList.{u1} α _inst_1) (List.removeNth.{u1} α l n))
Case conversion may be inaccurate. Consider using '#align list.tendsto_remove_nth List.tendsto_removeNthₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem tendsto_removeNth :
    ∀ {n : ℕ} {l : List α}, Tendsto (fun l => removeNth l n) (𝓝 l) (𝓝 (removeNth l n))
  | _, [] => by rw [nhds_nil] <;> exact tendsto_pure_nhds _ _
  | 0, a::l => by rw [tendsto_cons_iff] <;> exact tendsto_snd
  | n + 1, a::l => by
    rw [tendsto_cons_iff]
    dsimp [remove_nth]
    exact tendsto_fst.cons ((@tendsto_remove_nth n l).comp tendsto_snd)
#align list.tendsto_remove_nth List.tendsto_removeNth

/- warning: list.continuous_remove_nth -> List.continuous_removeNth is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat}, Continuous.{u1, u1} (List.{u1} α) (List.{u1} α) (List.topologicalSpace.{u1} α _inst_1) (List.topologicalSpace.{u1} α _inst_1) (fun (l : List.{u1} α) => List.removeNth.{u1} α l n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat}, Continuous.{u1, u1} (List.{u1} α) (List.{u1} α) (instTopologicalSpaceList.{u1} α _inst_1) (instTopologicalSpaceList.{u1} α _inst_1) (fun (l : List.{u1} α) => List.removeNth.{u1} α l n)
Case conversion may be inaccurate. Consider using '#align list.continuous_remove_nth List.continuous_removeNthₓ'. -/
theorem continuous_removeNth {n : ℕ} : Continuous fun l : List α => removeNth l n :=
  continuous_iff_continuousAt.mpr fun a => tendsto_removeNth
#align list.continuous_remove_nth List.continuous_removeNth

/- warning: list.tendsto_prod -> List.tendsto_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : Monoid.{u1} α] [_inst_4 : ContinuousMul.{u1} α _inst_1 (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))] {l : List.{u1} α}, Filter.Tendsto.{u1, u1} (List.{u1} α) α (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) (nhds.{u1} (List.{u1} α) (List.topologicalSpace.{u1} α _inst_1) l) (nhds.{u1} α _inst_1 (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : Monoid.{u1} α] [_inst_4 : ContinuousMul.{u1} α _inst_1 (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))] {l : List.{u1} α}, Filter.Tendsto.{u1, u1} (List.{u1} α) α (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (Monoid.toOne.{u1} α _inst_3)) (nhds.{u1} (List.{u1} α) (instTopologicalSpaceList.{u1} α _inst_1) l) (nhds.{u1} α _inst_1 (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (Monoid.toOne.{u1} α _inst_3) l))
Case conversion may be inaccurate. Consider using '#align list.tendsto_prod List.tendsto_prodₓ'. -/
@[to_additive]
theorem tendsto_prod [Monoid α] [ContinuousMul α] {l : List α} :
    Tendsto List.prod (𝓝 l) (𝓝 l.Prod) :=
  by
  induction' l with x l ih
  · simp (config := { contextual := true }) [nhds_nil, mem_of_mem_nhds, tendsto_pure_left]
  simp_rw [tendsto_cons_iff, prod_cons]
  have := continuous_iff_continuous_at.mp continuous_mul (x, l.prod)
  rw [ContinuousAt, nhds_prod_eq] at this
  exact this.comp (tendsto_id.prod_map ih)
#align list.tendsto_prod List.tendsto_prod
#align list.tendsto_sum List.tendsto_sum

/- warning: list.continuous_prod -> List.continuous_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : Monoid.{u1} α] [_inst_4 : ContinuousMul.{u1} α _inst_1 (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))], Continuous.{u1, u1} (List.{u1} α) α (List.topologicalSpace.{u1} α _inst_1) _inst_1 (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : Monoid.{u1} α] [_inst_4 : ContinuousMul.{u1} α _inst_1 (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))], Continuous.{u1, u1} (List.{u1} α) α (instTopologicalSpaceList.{u1} α _inst_1) _inst_1 (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (Monoid.toOne.{u1} α _inst_3))
Case conversion may be inaccurate. Consider using '#align list.continuous_prod List.continuous_prodₓ'. -/
@[to_additive]
theorem continuous_prod [Monoid α] [ContinuousMul α] : Continuous (prod : List α → α) :=
  continuous_iff_continuousAt.mpr fun l => tendsto_prod
#align list.continuous_prod List.continuous_prod
#align list.continuous_sum List.continuous_sum

end List

namespace Vector

open List

instance (n : ℕ) : TopologicalSpace (Vector α n) := by unfold Vector <;> infer_instance

/- warning: vector.tendsto_cons -> Vector.tendsto_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat} {a : α} {l : Vector.{u1} α n}, Filter.Tendsto.{u1, u1} (Prod.{u1, u1} α (Vector.{u1} α n)) (Vector.{u1} α (Nat.succ n)) (fun (p : Prod.{u1, u1} α (Vector.{u1} α n)) => Vector.cons.{u1} α n (Prod.fst.{u1, u1} α (Vector.{u1} α n) p) (Prod.snd.{u1, u1} α (Vector.{u1} α n) p)) (Filter.prod.{u1, u1} α (Vector.{u1} α n) (nhds.{u1} α _inst_1 a) (nhds.{u1} (Vector.{u1} α n) (Vector.topologicalSpace.{u1} α _inst_1 n) l)) (nhds.{u1} (Vector.{u1} α (Nat.succ n)) (Vector.topologicalSpace.{u1} α _inst_1 (Nat.succ n)) (Vector.cons.{u1} α n a l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat} {a : α} {l : Vector.{u1} α n}, Filter.Tendsto.{u1, u1} (Prod.{u1, u1} α (Vector.{u1} α n)) (Vector.{u1} α (Nat.succ n)) (fun (p : Prod.{u1, u1} α (Vector.{u1} α n)) => Vector.cons.{u1} α n (Prod.fst.{u1, u1} α (Vector.{u1} α n) p) (Prod.snd.{u1, u1} α (Vector.{u1} α n) p)) (Filter.prod.{u1, u1} α (Vector.{u1} α n) (nhds.{u1} α _inst_1 a) (nhds.{u1} (Vector.{u1} α n) (Vector.instTopologicalSpaceVector.{u1} α _inst_1 n) l)) (nhds.{u1} (Vector.{u1} α (Nat.succ n)) (Vector.instTopologicalSpaceVector.{u1} α _inst_1 (Nat.succ n)) (Vector.cons.{u1} α n a l))
Case conversion may be inaccurate. Consider using '#align vector.tendsto_cons Vector.tendsto_consₓ'. -/
theorem tendsto_cons {n : ℕ} {a : α} {l : Vector α n} :
    Tendsto (fun p : α × Vector α n => p.1 ::ᵥ p.2) (𝓝 a ×ᶠ 𝓝 l) (𝓝 (a ::ᵥ l)) :=
  by
  simp [tendsto_subtype_rng, ← Subtype.val_eq_coe, cons_val]
  exact tendsto_fst.cons (tendsto.comp continuousAt_subtype_val tendsto_snd)
#align vector.tendsto_cons Vector.tendsto_cons

/- warning: vector.tendsto_insert_nth -> Vector.tendsto_insertNth is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} {a : α} {l : Vector.{u1} α n}, Filter.Tendsto.{u1, u1} (Prod.{u1, u1} α (Vector.{u1} α n)) (Vector.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (p : Prod.{u1, u1} α (Vector.{u1} α n)) => Vector.insertNth.{u1} n α (Prod.fst.{u1, u1} α (Vector.{u1} α n) p) i (Prod.snd.{u1, u1} α (Vector.{u1} α n) p)) (Filter.prod.{u1, u1} α (Vector.{u1} α n) (nhds.{u1} α _inst_1 a) (nhds.{u1} (Vector.{u1} α n) (Vector.topologicalSpace.{u1} α _inst_1 n) l)) (nhds.{u1} (Vector.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Vector.topologicalSpace.{u1} α _inst_1 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Vector.insertNth.{u1} n α a i l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} {a : α} {l : Vector.{u1} α n}, Filter.Tendsto.{u1, u1} (Prod.{u1, u1} α (Vector.{u1} α n)) (Vector.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (p : Prod.{u1, u1} α (Vector.{u1} α n)) => Vector.insertNth.{u1} n α (Prod.fst.{u1, u1} α (Vector.{u1} α n) p) i (Prod.snd.{u1, u1} α (Vector.{u1} α n) p)) (Filter.prod.{u1, u1} α (Vector.{u1} α n) (nhds.{u1} α _inst_1 a) (nhds.{u1} (Vector.{u1} α n) (Vector.instTopologicalSpaceVector.{u1} α _inst_1 n) l)) (nhds.{u1} (Vector.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Vector.instTopologicalSpaceVector.{u1} α _inst_1 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Vector.insertNth.{u1} n α a i l))
Case conversion may be inaccurate. Consider using '#align vector.tendsto_insert_nth Vector.tendsto_insertNthₓ'. -/
theorem tendsto_insertNth {n : ℕ} {i : Fin (n + 1)} {a : α} :
    ∀ {l : Vector α n},
      Tendsto (fun p : α × Vector α n => insertNth p.1 i p.2) (𝓝 a ×ᶠ 𝓝 l) (𝓝 (insertNth a i l))
  | ⟨l, hl⟩ => by
    rw [insert_nth, tendsto_subtype_rng]
    simp [insert_nth_val]
    exact List.tendsto_insertNth tendsto_fst (tendsto.comp continuousAt_subtype_val tendsto_snd : _)
#align vector.tendsto_insert_nth Vector.tendsto_insertNth

/- warning: vector.continuous_insert_nth' -> Vector.continuous_insert_nth' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))}, Continuous.{u1, u1} (Prod.{u1, u1} α (Vector.{u1} α n)) (Vector.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Prod.topologicalSpace.{u1, u1} α (Vector.{u1} α n) _inst_1 (Vector.topologicalSpace.{u1} α _inst_1 n)) (Vector.topologicalSpace.{u1} α _inst_1 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (p : Prod.{u1, u1} α (Vector.{u1} α n)) => Vector.insertNth.{u1} n α (Prod.fst.{u1, u1} α (Vector.{u1} α n) p) i (Prod.snd.{u1, u1} α (Vector.{u1} α n) p))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))}, Continuous.{u1, u1} (Prod.{u1, u1} α (Vector.{u1} α n)) (Vector.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instTopologicalSpaceProd.{u1, u1} α (Vector.{u1} α n) _inst_1 (Vector.instTopologicalSpaceVector.{u1} α _inst_1 n)) (Vector.instTopologicalSpaceVector.{u1} α _inst_1 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (p : Prod.{u1, u1} α (Vector.{u1} α n)) => Vector.insertNth.{u1} n α (Prod.fst.{u1, u1} α (Vector.{u1} α n) p) i (Prod.snd.{u1, u1} α (Vector.{u1} α n) p))
Case conversion may be inaccurate. Consider using '#align vector.continuous_insert_nth' Vector.continuous_insert_nth'ₓ'. -/
theorem continuous_insert_nth' {n : ℕ} {i : Fin (n + 1)} :
    Continuous fun p : α × Vector α n => insertNth p.1 i p.2 :=
  continuous_iff_continuousAt.mpr fun ⟨a, l⟩ => by
    rw [ContinuousAt, nhds_prod_eq] <;> exact tendsto_insert_nth
#align vector.continuous_insert_nth' Vector.continuous_insert_nth'

/- warning: vector.continuous_insert_nth -> Vector.continuous_insertNth is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {n : Nat} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} {f : β -> α} {g : β -> (Vector.{u1} α n)}, (Continuous.{u2, u1} β α _inst_2 _inst_1 f) -> (Continuous.{u2, u1} β (Vector.{u1} α n) _inst_2 (Vector.topologicalSpace.{u1} α _inst_1 n) g) -> (Continuous.{u2, u1} β (Vector.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) _inst_2 (Vector.topologicalSpace.{u1} α _inst_1 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (b : β) => Vector.insertNth.{u1} n α (f b) i (g b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {n : Nat} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} {f : β -> α} {g : β -> (Vector.{u2} α n)}, (Continuous.{u1, u2} β α _inst_2 _inst_1 f) -> (Continuous.{u1, u2} β (Vector.{u2} α n) _inst_2 (Vector.instTopologicalSpaceVector.{u2} α _inst_1 n) g) -> (Continuous.{u1, u2} β (Vector.{u2} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _inst_2 (Vector.instTopologicalSpaceVector.{u2} α _inst_1 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (b : β) => Vector.insertNth.{u2} n α (f b) i (g b)))
Case conversion may be inaccurate. Consider using '#align vector.continuous_insert_nth Vector.continuous_insertNthₓ'. -/
theorem continuous_insertNth {n : ℕ} {i : Fin (n + 1)} {f : β → α} {g : β → Vector α n}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun b => insertNth (f b) i (g b) :=
  continuous_insert_nth'.comp (hf.prod_mk hg : _)
#align vector.continuous_insert_nth Vector.continuous_insertNth

/- warning: vector.continuous_at_remove_nth -> Vector.continuousAt_removeNth is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} {l : Vector.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))}, ContinuousAt.{u1, u1} (Vector.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Vector.{u1} α (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Vector.topologicalSpace.{u1} α _inst_1 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Vector.topologicalSpace.{u1} α _inst_1 (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Vector.removeNth.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) i) l
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} {l : Vector.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))}, ContinuousAt.{u1, u1} (Vector.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Vector.{u1} α (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Vector.instTopologicalSpaceVector.{u1} α _inst_1 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Vector.instTopologicalSpaceVector.{u1} α _inst_1 (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Vector.removeNth.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) i) l
Case conversion may be inaccurate. Consider using '#align vector.continuous_at_remove_nth Vector.continuousAt_removeNthₓ'. -/
theorem continuousAt_removeNth {n : ℕ} {i : Fin (n + 1)} :
    ∀ {l : Vector α (n + 1)}, ContinuousAt (removeNth i) l
  | ⟨l, hl⟩ =>--  ∀{l:vector α (n+1)}, tendsto (remove_nth i) (𝓝 l) (𝓝 (remove_nth i l))
  --| ⟨l, hl⟩ :=
  by
    rw [ContinuousAt, remove_nth, tendsto_subtype_rng]
    simp only [← Subtype.val_eq_coe, Vector.removeNth_val]
    exact tendsto.comp List.tendsto_removeNth continuousAt_subtype_val
#align vector.continuous_at_remove_nth Vector.continuousAt_removeNth

/- warning: vector.continuous_remove_nth -> Vector.continuous_removeNth is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))}, Continuous.{u1, u1} (Vector.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Vector.{u1} α (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Vector.topologicalSpace.{u1} α _inst_1 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Vector.topologicalSpace.{u1} α _inst_1 (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Vector.removeNth.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) i)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))}, Continuous.{u1, u1} (Vector.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Vector.{u1} α (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Vector.instTopologicalSpaceVector.{u1} α _inst_1 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Vector.instTopologicalSpaceVector.{u1} α _inst_1 (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Vector.removeNth.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) i)
Case conversion may be inaccurate. Consider using '#align vector.continuous_remove_nth Vector.continuous_removeNthₓ'. -/
theorem continuous_removeNth {n : ℕ} {i : Fin (n + 1)} :
    Continuous (removeNth i : Vector α (n + 1) → Vector α n) :=
  continuous_iff_continuousAt.mpr fun ⟨a, l⟩ => continuousAt_removeNth
#align vector.continuous_remove_nth Vector.continuous_removeNth

end Vector

