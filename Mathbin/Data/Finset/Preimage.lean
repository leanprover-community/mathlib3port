/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module data.finset.preimage
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Finite
import Mathbin.Algebra.BigOperators.Basic

/-!
# Preimage of a `finset` under an injective map.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Set Function

open BigOperators

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Finset

section Preimage

#print Finset.preimage /-
/-- Preimage of `s : finset β` under a map `f` injective of `f ⁻¹' s` as a `finset`.  -/
noncomputable def preimage (s : Finset β) (f : α → β) (hf : Set.InjOn f (f ⁻¹' ↑s)) : Finset α :=
  (s.finite_toSet.Preimage hf).toFinset
#align finset.preimage Finset.preimage
-/

#print Finset.mem_preimage /-
@[simp]
theorem mem_preimage {f : α → β} {s : Finset β} {hf : Set.InjOn f (f ⁻¹' ↑s)} {x : α} :
    x ∈ preimage s f hf ↔ f x ∈ s :=
  Set.Finite.mem_toFinset _
#align finset.mem_preimage Finset.mem_preimage
-/

#print Finset.coe_preimage /-
@[simp, norm_cast]
theorem coe_preimage {f : α → β} (s : Finset β) (hf : Set.InjOn f (f ⁻¹' ↑s)) :
    (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s :=
  Set.Finite.coe_toFinset _
#align finset.coe_preimage Finset.coe_preimage
-/

#print Finset.preimage_empty /-
@[simp]
theorem preimage_empty {f : α → β} : preimage ∅ f (by simp [inj_on]) = ∅ :=
  Finset.coe_injective (by simp)
#align finset.preimage_empty Finset.preimage_empty
-/

#print Finset.preimage_univ /-
@[simp]
theorem preimage_univ {f : α → β} [Fintype α] [Fintype β] (hf) : preimage univ f hf = univ :=
  Finset.coe_injective (by simp)
#align finset.preimage_univ Finset.preimage_univ
-/

#print Finset.preimage_inter /-
@[simp]
theorem preimage_inter [DecidableEq α] [DecidableEq β] {f : α → β} {s t : Finset β}
    (hs : Set.InjOn f (f ⁻¹' ↑s)) (ht : Set.InjOn f (f ⁻¹' ↑t)) :
    (preimage (s ∩ t) f fun x₁ hx₁ x₂ hx₂ =>
        hs (mem_of_mem_inter_left hx₁) (mem_of_mem_inter_left hx₂)) =
      preimage s f hs ∩ preimage t f ht :=
  Finset.coe_injective (by simp)
#align finset.preimage_inter Finset.preimage_inter
-/

#print Finset.preimage_union /-
@[simp]
theorem preimage_union [DecidableEq α] [DecidableEq β] {f : α → β} {s t : Finset β} (hst) :
    preimage (s ∪ t) f hst =
      (preimage s f fun x₁ hx₁ x₂ hx₂ => hst (mem_union_left _ hx₁) (mem_union_left _ hx₂)) ∪
        preimage t f fun x₁ hx₁ x₂ hx₂ => hst (mem_union_right _ hx₁) (mem_union_right _ hx₂) :=
  Finset.coe_injective (by simp)
#align finset.preimage_union Finset.preimage_union
-/

/- warning: finset.preimage_compl -> Finset.preimage_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] [_inst_3 : Fintype.{u1} α] [_inst_4 : Fintype.{u2} β] {f : α -> β} (s : Finset.{u2} β) (hf : Function.Injective.{succ u1, succ u2} α β f), Eq.{succ u1} (Finset.{u1} α) (Finset.preimage.{u1, u2} α β (HasCompl.compl.{u2} (Finset.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Finset.{u2} β) (Finset.booleanAlgebra.{u2} β _inst_4 (fun (a : β) (b : β) => _inst_2 a b))) s) f (Function.Injective.injOn.{u1, u2} α β f hf (Set.preimage.{u1, u2} α β f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (HasCompl.compl.{u2} (Finset.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Finset.{u2} β) (Finset.booleanAlgebra.{u2} β _inst_4 (fun (a : β) (b : β) => _inst_2 a b))) s))))) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_3 (fun (a : α) (b : α) => _inst_1 a b))) (Finset.preimage.{u1, u2} α β s f (Function.Injective.injOn.{u1, u2} α β f hf (Set.preimage.{u1, u2} α β f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) s)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] [_inst_3 : Fintype.{u1} α] [_inst_4 : Fintype.{u2} β] {f : α -> β} (s : Finset.{u2} β) (hf : Function.Injective.{succ u1, succ u2} α β f), Eq.{succ u1} (Finset.{u1} α) (Finset.preimage.{u1, u2} α β (HasCompl.compl.{u2} (Finset.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Finset.{u2} β) (Finset.instBooleanAlgebraFinset.{u2} β _inst_4 (fun (a : β) (b : β) => _inst_2 a b))) s) f (Function.Injective.injOn.{u2, u1} α β f hf (Set.preimage.{u1, u2} α β f (Finset.toSet.{u2} β (HasCompl.compl.{u2} (Finset.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Finset.{u2} β) (Finset.instBooleanAlgebraFinset.{u2} β _inst_4 (fun (a : β) (b : β) => _inst_2 a b))) s))))) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_3 (fun (a : α) (b : α) => _inst_1 a b))) (Finset.preimage.{u1, u2} α β s f (Function.Injective.injOn.{u2, u1} α β f hf (Set.preimage.{u1, u2} α β f (Finset.toSet.{u2} β s)))))
Case conversion may be inaccurate. Consider using '#align finset.preimage_compl Finset.preimage_complₓ'. -/
@[simp]
theorem preimage_compl [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {f : α → β}
    (s : Finset β) (hf : Function.Injective f) :
    preimage (sᶜ) f (hf.InjOn _) = preimage s f (hf.InjOn _)ᶜ :=
  Finset.coe_injective (by simp)
#align finset.preimage_compl Finset.preimage_compl

#print Finset.monotone_preimage /-
theorem monotone_preimage {f : α → β} (h : Injective f) :
    Monotone fun s => preimage s f (h.InjOn _) := fun s t hst x hx =>
  mem_preimage.2 (hst <| mem_preimage.1 hx)
#align finset.monotone_preimage Finset.monotone_preimage
-/

#print Finset.image_subset_iff_subset_preimage /-
theorem image_subset_iff_subset_preimage [DecidableEq β] {f : α → β} {s : Finset α} {t : Finset β}
    (hf : Set.InjOn f (f ⁻¹' ↑t)) : s.image f ⊆ t ↔ s ⊆ t.Preimage f hf :=
  image_subset_iff.trans <| by simp only [subset_iff, mem_preimage]
#align finset.image_subset_iff_subset_preimage Finset.image_subset_iff_subset_preimage
-/

#print Finset.map_subset_iff_subset_preimage /-
theorem map_subset_iff_subset_preimage {f : α ↪ β} {s : Finset α} {t : Finset β} :
    s.map f ⊆ t ↔ s ⊆ t.Preimage f (f.Injective.InjOn _) := by
  classical rw [map_eq_image, image_subset_iff_subset_preimage]
#align finset.map_subset_iff_subset_preimage Finset.map_subset_iff_subset_preimage
-/

#print Finset.image_preimage /-
theorem image_preimage [DecidableEq β] (f : α → β) (s : Finset β) [∀ x, Decidable (x ∈ Set.range f)]
    (hf : Set.InjOn f (f ⁻¹' ↑s)) :
    image f (preimage s f hf) = s.filterₓ fun x => x ∈ Set.range f :=
  Finset.coe_inj.1 <| by
    simp only [coe_image, coe_preimage, coe_filter, Set.image_preimage_eq_inter_range,
      Set.sep_mem_eq]
#align finset.image_preimage Finset.image_preimage
-/

#print Finset.image_preimage_of_bij /-
theorem image_preimage_of_bij [DecidableEq β] (f : α → β) (s : Finset β)
    (hf : Set.BijOn f (f ⁻¹' ↑s) ↑s) : image f (preimage s f hf.InjOn) = s :=
  Finset.coe_inj.1 <| by simpa using hf.image_eq
#align finset.image_preimage_of_bij Finset.image_preimage_of_bij
-/

#print Finset.preimage_subset /-
theorem preimage_subset {f : α ↪ β} {s : Finset β} {t : Finset α} (hs : s ⊆ t.map f) :
    s.Preimage f (f.Injective.InjOn _) ⊆ t := fun x hx => (mem_map' f).1 (hs (mem_preimage.1 hx))
#align finset.preimage_subset Finset.preimage_subset
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (u «expr ⊆ » t) -/
#print Finset.subset_map_iff /-
theorem subset_map_iff {f : α ↪ β} {s : Finset β} {t : Finset α} :
    s ⊆ t.map f ↔ ∃ (u : _)(_ : u ⊆ t), s = u.map f := by
  classical
    refine' ⟨fun h => ⟨_, preimage_subset h, _⟩, _⟩
    · rw [map_eq_image, image_preimage, filter_true_of_mem fun x hx => _]
      exact coe_map_subset_range _ _ (h hx)
    · rintro ⟨u, hut, rfl⟩
      exact map_subset_map.2 hut
#align finset.subset_map_iff Finset.subset_map_iff
-/

/- warning: finset.sigma_preimage_mk -> Finset.sigma_preimage_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) (t : Finset.{u1} α), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sigma.{u1, u2} α (fun (i : α) => β i))) (Finset.sigma.{u1, u2} α (fun (a : α) => β a) t (fun (a : α) => Finset.preimage.{u2, max u1 u2} (β a) (Sigma.{u1, u2} α (fun (a : α) => β a)) s (Sigma.mk.{u1, u2} α (fun (a : α) => β a) a) (Function.Injective.injOn.{u2, max u1 u2} (β a) (Sigma.{u1, u2} α (fun (a : α) => β a)) (Sigma.mk.{u1, u2} α (fun (a : α) => β a) a) (sigma_mk_injective.{u1, u2} α (fun (a : α) => β a) a) (Set.preimage.{u2, max u1 u2} (β a) (Sigma.{u1, u2} α (fun (a : α) => β a)) (Sigma.mk.{u1, u2} α (fun (a : α) => β a) a) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (Finset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Set.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (Finset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Set.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (Finset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Set.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Finset.Set.hasCoeT.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))))) s))))) (Finset.filter.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a)) (fun (a : Sigma.{u1, u2} α (fun (a : α) => β a)) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (Sigma.fst.{u1, u2} α (fun (a : α) => β a) a) t) (fun (a : Sigma.{u1, u2} α (fun (a : α) => β a)) => Finset.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Sigma.fst.{u1, u2} α (fun (a : α) => β a) a) t) s)
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] (s : Finset.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => β a))) (t : Finset.{u2} α), Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Sigma.{u2, u1} α (fun (i : α) => β i))) (Finset.sigma.{u2, u1} α (fun (a : α) => β a) t (fun (a : α) => Finset.preimage.{u1, max u2 u1} (β a) (Sigma.{u2, u1} α (fun (a : α) => β a)) s (Sigma.mk.{u2, u1} α (fun (a : α) => β a) a) (Function.Injective.injOn.{max u1 u2, u1} (β a) (Sigma.{u2, u1} α (fun (a : α) => β a)) (Sigma.mk.{u2, u1} α (fun (a : α) => β a) a) (sigma_mk_injective.{u2, u1} α (fun (a : α) => β a) a) (Set.preimage.{u1, max u2 u1} (β a) (Sigma.{u2, u1} α (fun (a : α) => β a)) (Sigma.mk.{u2, u1} α (fun (a : α) => β a) a) (Finset.toSet.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => β a)) s))))) (Finset.filter.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => β a)) (fun (a : Sigma.{u2, u1} α (fun (a : α) => β a)) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) (Sigma.fst.{u2, u1} α (fun (a : α) => β a) a) t) (fun (a : Sigma.{u2, u1} α (fun (a : α) => β a)) => Finset.decidableMem.{u2} α (fun (a : α) (b : α) => _inst_1 a b) (Sigma.fst.{u2, u1} α (fun (a : α) => β a) a) t) s)
Case conversion may be inaccurate. Consider using '#align finset.sigma_preimage_mk Finset.sigma_preimage_mkₓ'. -/
theorem sigma_preimage_mk {β : α → Type _} [DecidableEq α] (s : Finset (Σa, β a)) (t : Finset α) :
    (t.Sigma fun a => s.Preimage (Sigma.mk a) <| sigma_mk_injective.InjOn _) =
      s.filterₓ fun a => a.1 ∈ t :=
  by
  ext x
  simp [and_comm']
#align finset.sigma_preimage_mk Finset.sigma_preimage_mk

/- warning: finset.sigma_preimage_mk_of_subset -> Finset.sigma_preimage_mk_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Finset.image.{max u1 u2, u1} (Sigma.{u1, u2} α (fun (a : α) => β a)) α (fun (a : α) (b : α) => _inst_1 a b) (Sigma.fst.{u1, u2} α (fun (a : α) => β a)) s) t) -> (Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sigma.{u1, u2} α (fun (i : α) => β i))) (Finset.sigma.{u1, u2} α (fun (a : α) => β a) t (fun (a : α) => Finset.preimage.{u2, max u1 u2} (β a) (Sigma.{u1, u2} α (fun (a : α) => β a)) s (Sigma.mk.{u1, u2} α (fun (a : α) => β a) a) (Function.Injective.injOn.{u2, max u1 u2} (β a) (Sigma.{u1, u2} α (fun (a : α) => β a)) (Sigma.mk.{u1, u2} α (fun (a : α) => β a) a) (sigma_mk_injective.{u1, u2} α (fun (a : α) => β a) a) (Set.preimage.{u2, max u1 u2} (β a) (Sigma.{u1, u2} α (fun (a : α) => β a)) (Sigma.mk.{u1, u2} α (fun (a : α) => β a) a) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (Finset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Set.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (Finset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Set.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (Finset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Set.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Finset.Set.hasCoeT.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))))) s))))) s)
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] (s : Finset.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => β a))) {t : Finset.{u2} α}, (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) (Finset.image.{max u1 u2, u2} (Sigma.{u2, u1} α (fun (a : α) => β a)) α (fun (a : α) (b : α) => _inst_1 a b) (Sigma.fst.{u2, u1} α (fun (a : α) => β a)) s) t) -> (Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Sigma.{u2, u1} α (fun (i : α) => β i))) (Finset.sigma.{u2, u1} α (fun (a : α) => β a) t (fun (a : α) => Finset.preimage.{u1, max u2 u1} (β a) (Sigma.{u2, u1} α (fun (a : α) => β a)) s (Sigma.mk.{u2, u1} α (fun (a : α) => β a) a) (Function.Injective.injOn.{max u1 u2, u1} (β a) (Sigma.{u2, u1} α (fun (a : α) => β a)) (Sigma.mk.{u2, u1} α (fun (a : α) => β a) a) (sigma_mk_injective.{u2, u1} α (fun (a : α) => β a) a) (Set.preimage.{u1, max u2 u1} (β a) (Sigma.{u2, u1} α (fun (a : α) => β a)) (Sigma.mk.{u2, u1} α (fun (a : α) => β a) a) (Finset.toSet.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => β a)) s))))) s)
Case conversion may be inaccurate. Consider using '#align finset.sigma_preimage_mk_of_subset Finset.sigma_preimage_mk_of_subsetₓ'. -/
theorem sigma_preimage_mk_of_subset {β : α → Type _} [DecidableEq α] (s : Finset (Σa, β a))
    {t : Finset α} (ht : s.image Sigma.fst ⊆ t) :
    (t.Sigma fun a => s.Preimage (Sigma.mk a) <| sigma_mk_injective.InjOn _) = s := by
  rw [sigma_preimage_mk, filter_true_of_mem <| image_subset_iff.1 ht]
#align finset.sigma_preimage_mk_of_subset Finset.sigma_preimage_mk_of_subset

/- warning: finset.sigma_image_fst_preimage_mk -> Finset.sigma_image_fst_preimage_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sigma.{u1, u2} α (fun (i : α) => β i))) (Finset.sigma.{u1, u2} α (fun (a : α) => β a) (Finset.image.{max u1 u2, u1} (Sigma.{u1, u2} α (fun (a : α) => β a)) α (fun (a : α) (b : α) => _inst_1 a b) (Sigma.fst.{u1, u2} α (fun (a : α) => β a)) s) (fun (a : α) => Finset.preimage.{u2, max u1 u2} (β a) (Sigma.{u1, u2} α (fun (a : α) => β a)) s (Sigma.mk.{u1, u2} α (fun (a : α) => β a) a) (Function.Injective.injOn.{u2, max u1 u2} (β a) (Sigma.{u1, u2} α (fun (a : α) => β a)) (Sigma.mk.{u1, u2} α (fun (a : α) => β a) a) (sigma_mk_injective.{u1, u2} α (fun (a : α) => β a) a) (Set.preimage.{u2, max u1 u2} (β a) (Sigma.{u1, u2} α (fun (a : α) => β a)) (Sigma.mk.{u1, u2} α (fun (a : α) => β a) a) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (Finset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Set.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (Finset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Set.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (Finset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Set.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Finset.Set.hasCoeT.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))))) s))))) s
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] (s : Finset.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => β a))), Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Sigma.{u2, u1} α (fun (i : α) => β i))) (Finset.sigma.{u2, u1} α (fun (a : α) => β a) (Finset.image.{max u1 u2, u2} (Sigma.{u2, u1} α (fun (a : α) => β a)) α (fun (a : α) (b : α) => _inst_1 a b) (Sigma.fst.{u2, u1} α (fun (a : α) => β a)) s) (fun (a : α) => Finset.preimage.{u1, max u2 u1} (β a) (Sigma.{u2, u1} α (fun (a : α) => β a)) s (Sigma.mk.{u2, u1} α (fun (a : α) => β a) a) (Function.Injective.injOn.{max u1 u2, u1} (β a) (Sigma.{u2, u1} α (fun (a : α) => β a)) (Sigma.mk.{u2, u1} α (fun (a : α) => β a) a) (sigma_mk_injective.{u2, u1} α (fun (a : α) => β a) a) (Set.preimage.{u1, max u2 u1} (β a) (Sigma.{u2, u1} α (fun (a : α) => β a)) (Sigma.mk.{u2, u1} α (fun (a : α) => β a) a) (Finset.toSet.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => β a)) s))))) s
Case conversion may be inaccurate. Consider using '#align finset.sigma_image_fst_preimage_mk Finset.sigma_image_fst_preimage_mkₓ'. -/
theorem sigma_image_fst_preimage_mk {β : α → Type _} [DecidableEq α] (s : Finset (Σa, β a)) :
    ((s.image Sigma.fst).Sigma fun a => s.Preimage (Sigma.mk a) <| sigma_mk_injective.InjOn _) =
      s :=
  s.sigma_preimage_mk_of_subset (Subset.refl _)
#align finset.sigma_image_fst_preimage_mk Finset.sigma_image_fst_preimage_mk

end Preimage

#print Finset.prod_preimage' /-
@[to_additive]
theorem prod_preimage' [CommMonoid β] (f : α → γ) [DecidablePred fun x => x ∈ Set.range f]
    (s : Finset γ) (hf : Set.InjOn f (f ⁻¹' ↑s)) (g : γ → β) :
    (∏ x in s.Preimage f hf, g (f x)) = ∏ x in s.filterₓ fun x => x ∈ Set.range f, g x := by
  haveI := Classical.decEq γ <;>
    calc
      (∏ x in preimage s f hf, g (f x)) = ∏ x in image f (preimage s f hf), g x :=
        Eq.symm <| prod_image <| by simpa only [mem_preimage, inj_on] using hf
      _ = ∏ x in s.filter fun x => x ∈ Set.range f, g x := by rw [image_preimage]
      
#align finset.prod_preimage' Finset.prod_preimage'
#align finset.sum_preimage' Finset.sum_preimage'
-/

/- warning: finset.prod_preimage -> Finset.prod_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u2} β] (f : α -> γ) (s : Finset.{u3} γ) (hf : Set.InjOn.{u1, u3} α γ f (Set.preimage.{u1, u3} α γ f ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Finset.{u3} γ) (Set.{u3} γ) (HasLiftT.mk.{succ u3, succ u3} (Finset.{u3} γ) (Set.{u3} γ) (CoeTCₓ.coe.{succ u3, succ u3} (Finset.{u3} γ) (Set.{u3} γ) (Finset.Set.hasCoeT.{u3} γ))) s))) (g : γ -> β), (forall (x : γ), (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x s) -> (Not (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x (Set.range.{u3, succ u1} γ α f))) -> (Eq.{succ u2} β (g x) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_1)))))))) -> (Eq.{succ u2} β (Finset.prod.{u2, u1} β α _inst_1 (Finset.preimage.{u1, u3} α γ s f hf) (fun (x : α) => g (f x))) (Finset.prod.{u2, u3} β γ _inst_1 s (fun (x : γ) => g x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u2} β] (f : α -> γ) (s : Finset.{u3} γ) (hf : Set.InjOn.{u1, u3} α γ f (Set.preimage.{u1, u3} α γ f (Finset.toSet.{u3} γ s))) (g : γ -> β), (forall (x : γ), (Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) x s) -> (Not (Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) x (Set.range.{u3, succ u1} γ α f))) -> (Eq.{succ u2} β (g x) (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β (Monoid.toOne.{u2} β (CommMonoid.toMonoid.{u2} β _inst_1)))))) -> (Eq.{succ u2} β (Finset.prod.{u2, u1} β α _inst_1 (Finset.preimage.{u1, u3} α γ s f hf) (fun (x : α) => g (f x))) (Finset.prod.{u2, u3} β γ _inst_1 s (fun (x : γ) => g x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_preimage Finset.prod_preimageₓ'. -/
@[to_additive]
theorem prod_preimage [CommMonoid β] (f : α → γ) (s : Finset γ) (hf : Set.InjOn f (f ⁻¹' ↑s))
    (g : γ → β) (hg : ∀ x ∈ s, x ∉ Set.range f → g x = 1) :
    (∏ x in s.Preimage f hf, g (f x)) = ∏ x in s, g x := by
  classical
    rw [prod_preimage', prod_filter_of_ne]
    exact fun x hx => Not.imp_symm (hg x hx)
#align finset.prod_preimage Finset.prod_preimage
#align finset.sum_preimage Finset.sum_preimage

#print Finset.prod_preimage_of_bij /-
@[to_additive]
theorem prod_preimage_of_bij [CommMonoid β] (f : α → γ) (s : Finset γ)
    (hf : Set.BijOn f (f ⁻¹' ↑s) ↑s) (g : γ → β) :
    (∏ x in s.Preimage f hf.InjOn, g (f x)) = ∏ x in s, g x :=
  prod_preimage _ _ hf.InjOn g fun x hxs hxf => (hxf <| hf.subset_range hxs).elim
#align finset.prod_preimage_of_bij Finset.prod_preimage_of_bij
#align finset.sum_preimage_of_bij Finset.sum_preimage_of_bij
-/

end Finset

