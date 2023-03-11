/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Patrick Massot

! This file was ported from Lean 3 source module topology.uniform_space.uniform_embedding
! leanprover-community/mathlib commit 195fcd60ff2bfe392543bceb0ec2adcdb472db4c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.UniformSpace.Cauchy
import Mathbin.Topology.UniformSpace.Separation
import Mathbin.Topology.DenseEmbedding

/-!
# Uniform embeddings of uniform spaces.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Extension of uniform continuous functions.
-/


open Filter TopologicalSpace Set Function Classical

open Classical uniformity Topology Filter

section

variable {α : Type _} {β : Type _} {γ : Type _} [UniformSpace α] [UniformSpace β] [UniformSpace γ]

universe u v

/-!
### Uniform inducing maps
-/


#print UniformInducing /-
/-- A map `f : α → β` between uniform spaces is called *uniform inducing* if the uniformity filter
on `α` is the pullback of the uniformity filter on `β` under `prod.map f f`. If `α` is a separated
space, then this implies that `f` is injective, hence it is a `uniform_embedding`. -/
@[mk_iff]
structure UniformInducing (f : α → β) : Prop where
  comap_uniformity : comap (fun x : α × α => (f x.1, f x.2)) (𝓤 β) = 𝓤 α
#align uniform_inducing UniformInducing
-/

#print UniformInducing.comap_uniformSpace /-
protected theorem UniformInducing.comap_uniformSpace {f : α → β} (hf : UniformInducing f) :
    ‹UniformSpace β›.comap f = ‹UniformSpace α› :=
  uniformSpace_eq hf.1
#align uniform_inducing.comap_uniform_space UniformInducing.comap_uniformSpace
-/

/- warning: uniform_inducing_iff' -> uniformInducing_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {f : α -> β}, Iff (UniformInducing.{u1, u2} α β _inst_1 _inst_2 f) (And (UniformContinuous.{u1, u2} α β _inst_1 _inst_2 f) (LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.partialOrder.{u1} (Prod.{u1, u1} α α)))) (Filter.comap.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) (Prod.map.{u1, u2, u1, u2} α β α β f f) (uniformity.{u2} β _inst_2)) (uniformity.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {f : α -> β}, Iff (UniformInducing.{u1, u2} α β _inst_1 _inst_2 f) (And (UniformContinuous.{u1, u2} α β _inst_1 _inst_2 f) (LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.instPartialOrderFilter.{u1} (Prod.{u1, u1} α α)))) (Filter.comap.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) (Prod.map.{u1, u2, u1, u2} α β α β f f) (uniformity.{u2} β _inst_2)) (uniformity.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align uniform_inducing_iff' uniformInducing_iff'ₓ'. -/
theorem uniformInducing_iff' {f : α → β} :
    UniformInducing f ↔ UniformContinuous f ∧ comap (Prod.map f f) (𝓤 β) ≤ 𝓤 α := by
  rw [uniformInducing_iff, UniformContinuous, tendsto_iff_comap, le_antisymm_iff, and_comm'] <;> rfl
#align uniform_inducing_iff' uniformInducing_iff'

/- warning: filter.has_basis.uniform_inducing_iff -> Filter.HasBasis.uniformInducing_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {ι : Sort.{u3}} {ι' : Sort.{u4}} {p : ι -> Prop} {p' : ι' -> Prop} {s : ι -> (Set.{u1} (Prod.{u1, u1} α α))} {s' : ι' -> (Set.{u2} (Prod.{u2, u2} β β))}, (Filter.HasBasis.{u1, u3} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p s) -> (Filter.HasBasis.{u2, u4} (Prod.{u2, u2} β β) ι' (uniformity.{u2} β _inst_2) p' s') -> (forall {f : α -> β}, Iff (UniformInducing.{u1, u2} α β _inst_1 _inst_2 f) (And (forall (i : ι'), (p' i) -> (Exists.{u3} ι (fun (j : ι) => And (p j) (forall (x : α) (y : α), (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) (s j)) -> (Membership.Mem.{u2, u2} (Prod.{u2, u2} β β) (Set.{u2} (Prod.{u2, u2} β β)) (Set.hasMem.{u2} (Prod.{u2, u2} β β)) (Prod.mk.{u2, u2} β β (f x) (f y)) (s' i)))))) (forall (j : ι), (p j) -> (Exists.{u4} ι' (fun (i : ι') => And (p' i) (forall (x : α) (y : α), (Membership.Mem.{u2, u2} (Prod.{u2, u2} β β) (Set.{u2} (Prod.{u2, u2} β β)) (Set.hasMem.{u2} (Prod.{u2, u2} β β)) (Prod.mk.{u2, u2} β β (f x) (f y)) (s' i)) -> (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) (s j))))))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : UniformSpace.{u3} α] [_inst_2 : UniformSpace.{u4} β] {ι : Sort.{u2}} {ι' : Sort.{u1}} {p : ι -> Prop} {p' : ι' -> Prop} {s : ι -> (Set.{u3} (Prod.{u3, u3} α α))} {s' : ι' -> (Set.{u4} (Prod.{u4, u4} β β))}, (Filter.HasBasis.{u3, u2} (Prod.{u3, u3} α α) ι (uniformity.{u3} α _inst_1) p s) -> (Filter.HasBasis.{u4, u1} (Prod.{u4, u4} β β) ι' (uniformity.{u4} β _inst_2) p' s') -> (forall {f : α -> β}, Iff (UniformInducing.{u3, u4} α β _inst_1 _inst_2 f) (And (forall (i : ι'), (p' i) -> (Exists.{u2} ι (fun (j : ι) => And (p j) (forall (x : α) (y : α), (Membership.mem.{u3, u3} (Prod.{u3, u3} α α) (Set.{u3} (Prod.{u3, u3} α α)) (Set.instMembershipSet.{u3} (Prod.{u3, u3} α α)) (Prod.mk.{u3, u3} α α x y) (s j)) -> (Membership.mem.{u4, u4} (Prod.{u4, u4} β β) (Set.{u4} (Prod.{u4, u4} β β)) (Set.instMembershipSet.{u4} (Prod.{u4, u4} β β)) (Prod.mk.{u4, u4} β β (f x) (f y)) (s' i)))))) (forall (j : ι), (p j) -> (Exists.{u1} ι' (fun (i : ι') => And (p' i) (forall (x : α) (y : α), (Membership.mem.{u4, u4} (Prod.{u4, u4} β β) (Set.{u4} (Prod.{u4, u4} β β)) (Set.instMembershipSet.{u4} (Prod.{u4, u4} β β)) (Prod.mk.{u4, u4} β β (f x) (f y)) (s' i)) -> (Membership.mem.{u3, u3} (Prod.{u3, u3} α α) (Set.{u3} (Prod.{u3, u3} α α)) (Set.instMembershipSet.{u3} (Prod.{u3, u3} α α)) (Prod.mk.{u3, u3} α α x y) (s j))))))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.uniform_inducing_iff Filter.HasBasis.uniformInducing_iffₓ'. -/
protected theorem Filter.HasBasis.uniformInducing_iff {ι ι'} {p : ι → Prop} {p' : ι' → Prop} {s s'}
    (h : (𝓤 α).HasBasis p s) (h' : (𝓤 β).HasBasis p' s') {f : α → β} :
    UniformInducing f ↔
      (∀ i, p' i → ∃ j, p j ∧ ∀ x y, (x, y) ∈ s j → (f x, f y) ∈ s' i) ∧
        ∀ j, p j → ∃ i, p' i ∧ ∀ x y, (f x, f y) ∈ s' i → (x, y) ∈ s j :=
  by
  simp [uniformInducing_iff', h.uniform_continuous_iff h', (h'.comap _).le_basis_iffₓ h, subset_def]
#align filter.has_basis.uniform_inducing_iff Filter.HasBasis.uniformInducing_iff

/- warning: uniform_inducing.mk' -> UniformInducing.mk' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {f : α -> β}, (forall (s : Set.{u1} (Prod.{u1, u1} α α)), Iff (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) (Exists.{succ u2} (Set.{u2} (Prod.{u2, u2} β β)) (fun (t : Set.{u2} (Prod.{u2, u2} β β)) => Exists.{0} (Membership.Mem.{u2, u2} (Set.{u2} (Prod.{u2, u2} β β)) (Filter.{u2} (Prod.{u2, u2} β β)) (Filter.hasMem.{u2} (Prod.{u2, u2} β β)) t (uniformity.{u2} β _inst_2)) (fun (H : Membership.Mem.{u2, u2} (Set.{u2} (Prod.{u2, u2} β β)) (Filter.{u2} (Prod.{u2, u2} β β)) (Filter.hasMem.{u2} (Prod.{u2, u2} β β)) t (uniformity.{u2} β _inst_2)) => forall (x : α) (y : α), (Membership.Mem.{u2, u2} (Prod.{u2, u2} β β) (Set.{u2} (Prod.{u2, u2} β β)) (Set.hasMem.{u2} (Prod.{u2, u2} β β)) (Prod.mk.{u2, u2} β β (f x) (f y)) t) -> (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) s))))) -> (UniformInducing.{u1, u2} α β _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {f : α -> β}, (forall (s : Set.{u1} (Prod.{u1, u1} α α)), Iff (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) (Exists.{succ u2} (Set.{u2} (Prod.{u2, u2} β β)) (fun (t : Set.{u2} (Prod.{u2, u2} β β)) => And (Membership.mem.{u2, u2} (Set.{u2} (Prod.{u2, u2} β β)) (Filter.{u2} (Prod.{u2, u2} β β)) (instMembershipSetFilter.{u2} (Prod.{u2, u2} β β)) t (uniformity.{u2} β _inst_2)) (forall (x : α) (y : α), (Membership.mem.{u2, u2} (Prod.{u2, u2} β β) (Set.{u2} (Prod.{u2, u2} β β)) (Set.instMembershipSet.{u2} (Prod.{u2, u2} β β)) (Prod.mk.{u2, u2} β β (f x) (f y)) t) -> (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) s))))) -> (UniformInducing.{u1, u2} α β _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align uniform_inducing.mk' UniformInducing.mk'ₓ'. -/
theorem UniformInducing.mk' {f : α → β}
    (h : ∀ s, s ∈ 𝓤 α ↔ ∃ t ∈ 𝓤 β, ∀ x y : α, (f x, f y) ∈ t → (x, y) ∈ s) : UniformInducing f :=
  ⟨by simp [eq_comm, Filter.ext_iff, subset_def, h]⟩
#align uniform_inducing.mk' UniformInducing.mk'

#print uniformInducing_id /-
theorem uniformInducing_id : UniformInducing (@id α) :=
  ⟨by rw [← Prod.map_def, Prod.map_id, comap_id]⟩
#align uniform_inducing_id uniformInducing_id
-/

#print UniformInducing.comp /-
theorem UniformInducing.comp {g : β → γ} (hg : UniformInducing g) {f : α → β}
    (hf : UniformInducing f) : UniformInducing (g ∘ f) :=
  ⟨by rw [← hf.1, ← hg.1, comap_comap]⟩
#align uniform_inducing.comp UniformInducing.comp
-/

/- warning: uniform_inducing.basis_uniformity -> UniformInducing.basis_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {f : α -> β}, (UniformInducing.{u1, u2} α β _inst_1 _inst_2 f) -> (forall {ι : Sort.{u3}} {p : ι -> Prop} {s : ι -> (Set.{u2} (Prod.{u2, u2} β β))}, (Filter.HasBasis.{u2, u3} (Prod.{u2, u2} β β) ι (uniformity.{u2} β _inst_2) p s) -> (Filter.HasBasis.{u1, u3} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p (fun (i : ι) => Set.preimage.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) (Prod.map.{u1, u2, u1, u2} α β α β f f) (s i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u3} β] {f : α -> β}, (UniformInducing.{u2, u3} α β _inst_1 _inst_2 f) -> (forall {ι : Sort.{u1}} {p : ι -> Prop} {s : ι -> (Set.{u3} (Prod.{u3, u3} β β))}, (Filter.HasBasis.{u3, u1} (Prod.{u3, u3} β β) ι (uniformity.{u3} β _inst_2) p s) -> (Filter.HasBasis.{u2, u1} (Prod.{u2, u2} α α) ι (uniformity.{u2} α _inst_1) p (fun (i : ι) => Set.preimage.{u2, u3} (Prod.{u2, u2} α α) (Prod.{u3, u3} β β) (Prod.map.{u2, u3, u2, u3} α β α β f f) (s i))))
Case conversion may be inaccurate. Consider using '#align uniform_inducing.basis_uniformity UniformInducing.basis_uniformityₓ'. -/
theorem UniformInducing.basis_uniformity {f : α → β} (hf : UniformInducing f) {ι : Sort _}
    {p : ι → Prop} {s : ι → Set (β × β)} (H : (𝓤 β).HasBasis p s) :
    (𝓤 α).HasBasis p fun i => Prod.map f f ⁻¹' s i :=
  hf.1 ▸ H.comap _
#align uniform_inducing.basis_uniformity UniformInducing.basis_uniformity

#print UniformInducing.cauchy_map_iff /-
theorem UniformInducing.cauchy_map_iff {f : α → β} (hf : UniformInducing f) {F : Filter α} :
    Cauchy (map f F) ↔ Cauchy F := by
  simp only [Cauchy, map_ne_bot_iff, prod_map_map_eq, map_le_iff_le_comap, ← hf.comap_uniformity]
#align uniform_inducing.cauchy_map_iff UniformInducing.cauchy_map_iff
-/

#print uniformInducing_of_compose /-
theorem uniformInducing_of_compose {f : α → β} {g : β → γ} (hf : UniformContinuous f)
    (hg : UniformContinuous g) (hgf : UniformInducing (g ∘ f)) : UniformInducing f :=
  by
  refine' ⟨le_antisymm _ hf.le_comap⟩
  rw [← hgf.1, ← Prod.map_def, ← Prod.map_def, ← Prod.map_comp_map f f g g, ←
    @comap_comap _ _ _ _ (Prod.map f f)]
  exact comap_mono hg.le_comap
#align uniform_inducing_of_compose uniformInducing_of_compose
-/

#print UniformInducing.uniformContinuous /-
theorem UniformInducing.uniformContinuous {f : α → β} (hf : UniformInducing f) :
    UniformContinuous f :=
  (uniformInducing_iff'.1 hf).1
#align uniform_inducing.uniform_continuous UniformInducing.uniformContinuous
-/

#print UniformInducing.uniformContinuous_iff /-
theorem UniformInducing.uniformContinuous_iff {f : α → β} {g : β → γ} (hg : UniformInducing g) :
    UniformContinuous f ↔ UniformContinuous (g ∘ f) :=
  by
  dsimp only [UniformContinuous, tendsto]
  rw [← hg.comap_uniformity, ← map_le_iff_le_comap, Filter.map_map]
#align uniform_inducing.uniform_continuous_iff UniformInducing.uniformContinuous_iff
-/

#print UniformInducing.inducing /-
protected theorem UniformInducing.inducing {f : α → β} (h : UniformInducing f) : Inducing f :=
  by
  obtain rfl := h.comap_uniform_space
  letI := UniformSpace.comap f _
  exact ⟨rfl⟩
#align uniform_inducing.inducing UniformInducing.inducing
-/

/- warning: uniform_inducing.prod -> UniformInducing.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {α' : Type.{u3}} {β' : Type.{u4}} [_inst_4 : UniformSpace.{u3} α'] [_inst_5 : UniformSpace.{u4} β'] {e₁ : α -> α'} {e₂ : β -> β'}, (UniformInducing.{u1, u3} α α' _inst_1 _inst_4 e₁) -> (UniformInducing.{u2, u4} β β' _inst_2 _inst_5 e₂) -> (UniformInducing.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} α' β') (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.uniformSpace.{u3, u4} α' β' _inst_4 _inst_5) (fun (p : Prod.{u1, u2} α β) => Prod.mk.{u3, u4} α' β' (e₁ (Prod.fst.{u1, u2} α β p)) (e₂ (Prod.snd.{u1, u2} α β p))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : UniformSpace.{u3} α] [_inst_2 : UniformSpace.{u4} β] {α' : Type.{u2}} {β' : Type.{u1}} [_inst_4 : UniformSpace.{u2} α'] [_inst_5 : UniformSpace.{u1} β'] {e₁ : α -> α'} {e₂ : β -> β'}, (UniformInducing.{u3, u2} α α' _inst_1 _inst_4 e₁) -> (UniformInducing.{u4, u1} β β' _inst_2 _inst_5 e₂) -> (UniformInducing.{max u3 u4, max u1 u2} (Prod.{u3, u4} α β) (Prod.{u2, u1} α' β') (instUniformSpaceProd.{u3, u4} α β _inst_1 _inst_2) (instUniformSpaceProd.{u2, u1} α' β' _inst_4 _inst_5) (fun (p : Prod.{u3, u4} α β) => Prod.mk.{u2, u1} α' β' (e₁ (Prod.fst.{u3, u4} α β p)) (e₂ (Prod.snd.{u3, u4} α β p))))
Case conversion may be inaccurate. Consider using '#align uniform_inducing.prod UniformInducing.prodₓ'. -/
theorem UniformInducing.prod {α' : Type _} {β' : Type _} [UniformSpace α'] [UniformSpace β']
    {e₁ : α → α'} {e₂ : β → β'} (h₁ : UniformInducing e₁) (h₂ : UniformInducing e₂) :
    UniformInducing fun p : α × β => (e₁ p.1, e₂ p.2) :=
  ⟨by
    simp [(· ∘ ·), uniformity_prod, h₁.comap_uniformity.symm, h₂.comap_uniformity.symm, comap_inf,
      comap_comap]⟩
#align uniform_inducing.prod UniformInducing.prod

#print UniformInducing.denseInducing /-
theorem UniformInducing.denseInducing {f : α → β} (h : UniformInducing f) (hd : DenseRange f) :
    DenseInducing f :=
  { dense := hd
    induced := h.Inducing.induced }
#align uniform_inducing.dense_inducing UniformInducing.denseInducing
-/

#print UniformInducing.injective /-
protected theorem UniformInducing.injective [T0Space α] {f : α → β} (h : UniformInducing f) :
    Injective f :=
  h.Inducing.Injective
#align uniform_inducing.injective UniformInducing.injective
-/

#print UniformEmbedding /-
/-- A map `f : α → β` between uniform spaces is a *uniform embedding* if it is uniform inducing and
injective. If `α` is a separated space, then the latter assumption follows from the former. -/
@[mk_iff]
structure UniformEmbedding (f : α → β) extends UniformInducing f : Prop where
  inj : Function.Injective f
#align uniform_embedding UniformEmbedding
-/

/- warning: uniform_embedding_iff' -> uniformEmbedding_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {f : α -> β}, Iff (UniformEmbedding.{u1, u2} α β _inst_1 _inst_2 f) (And (Function.Injective.{succ u1, succ u2} α β f) (And (UniformContinuous.{u1, u2} α β _inst_1 _inst_2 f) (LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.partialOrder.{u1} (Prod.{u1, u1} α α)))) (Filter.comap.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) (Prod.map.{u1, u2, u1, u2} α β α β f f) (uniformity.{u2} β _inst_2)) (uniformity.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {f : α -> β}, Iff (UniformEmbedding.{u1, u2} α β _inst_1 _inst_2 f) (And (Function.Injective.{succ u1, succ u2} α β f) (And (UniformContinuous.{u1, u2} α β _inst_1 _inst_2 f) (LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.instPartialOrderFilter.{u1} (Prod.{u1, u1} α α)))) (Filter.comap.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) (Prod.map.{u1, u2, u1, u2} α β α β f f) (uniformity.{u2} β _inst_2)) (uniformity.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align uniform_embedding_iff' uniformEmbedding_iff'ₓ'. -/
theorem uniformEmbedding_iff' {f : α → β} :
    UniformEmbedding f ↔ Injective f ∧ UniformContinuous f ∧ comap (Prod.map f f) (𝓤 β) ≤ 𝓤 α := by
  rw [uniformEmbedding_iff, and_comm', uniformInducing_iff']
#align uniform_embedding_iff' uniformEmbedding_iff'

/- warning: filter.has_basis.uniform_embedding_iff' -> Filter.HasBasis.uniformEmbedding_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {ι : Sort.{u3}} {ι' : Sort.{u4}} {p : ι -> Prop} {p' : ι' -> Prop} {s : ι -> (Set.{u1} (Prod.{u1, u1} α α))} {s' : ι' -> (Set.{u2} (Prod.{u2, u2} β β))}, (Filter.HasBasis.{u1, u3} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p s) -> (Filter.HasBasis.{u2, u4} (Prod.{u2, u2} β β) ι' (uniformity.{u2} β _inst_2) p' s') -> (forall {f : α -> β}, Iff (UniformEmbedding.{u1, u2} α β _inst_1 _inst_2 f) (And (Function.Injective.{succ u1, succ u2} α β f) (And (forall (i : ι'), (p' i) -> (Exists.{u3} ι (fun (j : ι) => And (p j) (forall (x : α) (y : α), (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) (s j)) -> (Membership.Mem.{u2, u2} (Prod.{u2, u2} β β) (Set.{u2} (Prod.{u2, u2} β β)) (Set.hasMem.{u2} (Prod.{u2, u2} β β)) (Prod.mk.{u2, u2} β β (f x) (f y)) (s' i)))))) (forall (j : ι), (p j) -> (Exists.{u4} ι' (fun (i : ι') => And (p' i) (forall (x : α) (y : α), (Membership.Mem.{u2, u2} (Prod.{u2, u2} β β) (Set.{u2} (Prod.{u2, u2} β β)) (Set.hasMem.{u2} (Prod.{u2, u2} β β)) (Prod.mk.{u2, u2} β β (f x) (f y)) (s' i)) -> (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) (s j)))))))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : UniformSpace.{u3} α] [_inst_2 : UniformSpace.{u4} β] {ι : Sort.{u2}} {ι' : Sort.{u1}} {p : ι -> Prop} {p' : ι' -> Prop} {s : ι -> (Set.{u3} (Prod.{u3, u3} α α))} {s' : ι' -> (Set.{u4} (Prod.{u4, u4} β β))}, (Filter.HasBasis.{u3, u2} (Prod.{u3, u3} α α) ι (uniformity.{u3} α _inst_1) p s) -> (Filter.HasBasis.{u4, u1} (Prod.{u4, u4} β β) ι' (uniformity.{u4} β _inst_2) p' s') -> (forall {f : α -> β}, Iff (UniformEmbedding.{u3, u4} α β _inst_1 _inst_2 f) (And (Function.Injective.{succ u3, succ u4} α β f) (And (forall (i : ι'), (p' i) -> (Exists.{u2} ι (fun (j : ι) => And (p j) (forall (x : α) (y : α), (Membership.mem.{u3, u3} (Prod.{u3, u3} α α) (Set.{u3} (Prod.{u3, u3} α α)) (Set.instMembershipSet.{u3} (Prod.{u3, u3} α α)) (Prod.mk.{u3, u3} α α x y) (s j)) -> (Membership.mem.{u4, u4} (Prod.{u4, u4} β β) (Set.{u4} (Prod.{u4, u4} β β)) (Set.instMembershipSet.{u4} (Prod.{u4, u4} β β)) (Prod.mk.{u4, u4} β β (f x) (f y)) (s' i)))))) (forall (j : ι), (p j) -> (Exists.{u1} ι' (fun (i : ι') => And (p' i) (forall (x : α) (y : α), (Membership.mem.{u4, u4} (Prod.{u4, u4} β β) (Set.{u4} (Prod.{u4, u4} β β)) (Set.instMembershipSet.{u4} (Prod.{u4, u4} β β)) (Prod.mk.{u4, u4} β β (f x) (f y)) (s' i)) -> (Membership.mem.{u3, u3} (Prod.{u3, u3} α α) (Set.{u3} (Prod.{u3, u3} α α)) (Set.instMembershipSet.{u3} (Prod.{u3, u3} α α)) (Prod.mk.{u3, u3} α α x y) (s j)))))))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.uniform_embedding_iff' Filter.HasBasis.uniformEmbedding_iff'ₓ'. -/
theorem Filter.HasBasis.uniformEmbedding_iff' {ι ι'} {p : ι → Prop} {p' : ι' → Prop} {s s'}
    (h : (𝓤 α).HasBasis p s) (h' : (𝓤 β).HasBasis p' s') {f : α → β} :
    UniformEmbedding f ↔
      Injective f ∧
        (∀ i, p' i → ∃ j, p j ∧ ∀ x y, (x, y) ∈ s j → (f x, f y) ∈ s' i) ∧
          ∀ j, p j → ∃ i, p' i ∧ ∀ x y, (f x, f y) ∈ s' i → (x, y) ∈ s j :=
  by rw [uniformEmbedding_iff, and_comm', h.uniform_inducing_iff h']
#align filter.has_basis.uniform_embedding_iff' Filter.HasBasis.uniformEmbedding_iff'

/- warning: filter.has_basis.uniform_embedding_iff -> Filter.HasBasis.uniformEmbedding_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {ι : Sort.{u3}} {ι' : Sort.{u4}} {p : ι -> Prop} {p' : ι' -> Prop} {s : ι -> (Set.{u1} (Prod.{u1, u1} α α))} {s' : ι' -> (Set.{u2} (Prod.{u2, u2} β β))}, (Filter.HasBasis.{u1, u3} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p s) -> (Filter.HasBasis.{u2, u4} (Prod.{u2, u2} β β) ι' (uniformity.{u2} β _inst_2) p' s') -> (forall {f : α -> β}, Iff (UniformEmbedding.{u1, u2} α β _inst_1 _inst_2 f) (And (Function.Injective.{succ u1, succ u2} α β f) (And (UniformContinuous.{u1, u2} α β _inst_1 _inst_2 f) (forall (j : ι), (p j) -> (Exists.{u4} ι' (fun (i : ι') => And (p' i) (forall (x : α) (y : α), (Membership.Mem.{u2, u2} (Prod.{u2, u2} β β) (Set.{u2} (Prod.{u2, u2} β β)) (Set.hasMem.{u2} (Prod.{u2, u2} β β)) (Prod.mk.{u2, u2} β β (f x) (f y)) (s' i)) -> (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) (s j)))))))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : UniformSpace.{u3} α] [_inst_2 : UniformSpace.{u4} β] {ι : Sort.{u2}} {ι' : Sort.{u1}} {p : ι -> Prop} {p' : ι' -> Prop} {s : ι -> (Set.{u3} (Prod.{u3, u3} α α))} {s' : ι' -> (Set.{u4} (Prod.{u4, u4} β β))}, (Filter.HasBasis.{u3, u2} (Prod.{u3, u3} α α) ι (uniformity.{u3} α _inst_1) p s) -> (Filter.HasBasis.{u4, u1} (Prod.{u4, u4} β β) ι' (uniformity.{u4} β _inst_2) p' s') -> (forall {f : α -> β}, Iff (UniformEmbedding.{u3, u4} α β _inst_1 _inst_2 f) (And (Function.Injective.{succ u3, succ u4} α β f) (And (UniformContinuous.{u3, u4} α β _inst_1 _inst_2 f) (forall (j : ι), (p j) -> (Exists.{u1} ι' (fun (i : ι') => And (p' i) (forall (x : α) (y : α), (Membership.mem.{u4, u4} (Prod.{u4, u4} β β) (Set.{u4} (Prod.{u4, u4} β β)) (Set.instMembershipSet.{u4} (Prod.{u4, u4} β β)) (Prod.mk.{u4, u4} β β (f x) (f y)) (s' i)) -> (Membership.mem.{u3, u3} (Prod.{u3, u3} α α) (Set.{u3} (Prod.{u3, u3} α α)) (Set.instMembershipSet.{u3} (Prod.{u3, u3} α α)) (Prod.mk.{u3, u3} α α x y) (s j)))))))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.uniform_embedding_iff Filter.HasBasis.uniformEmbedding_iffₓ'. -/
theorem Filter.HasBasis.uniformEmbedding_iff {ι ι'} {p : ι → Prop} {p' : ι' → Prop} {s s'}
    (h : (𝓤 α).HasBasis p s) (h' : (𝓤 β).HasBasis p' s') {f : α → β} :
    UniformEmbedding f ↔
      Injective f ∧
        UniformContinuous f ∧ ∀ j, p j → ∃ i, p' i ∧ ∀ x y, (f x, f y) ∈ s' i → (x, y) ∈ s j :=
  by simp only [h.uniform_embedding_iff' h', h.uniform_continuous_iff h', exists_prop]
#align filter.has_basis.uniform_embedding_iff Filter.HasBasis.uniformEmbedding_iff

#print uniformEmbedding_subtype_val /-
theorem uniformEmbedding_subtype_val {p : α → Prop} :
    UniformEmbedding (Subtype.val : Subtype p → α) :=
  { comap_uniformity := rfl
    inj := Subtype.val_injective }
#align uniform_embedding_subtype_val uniformEmbedding_subtype_val
-/

/- warning: uniform_embedding_subtype_coe clashes with uniform_embedding_subtype_val -> uniformEmbedding_subtype_val
Case conversion may be inaccurate. Consider using '#align uniform_embedding_subtype_coe uniformEmbedding_subtype_valₓ'. -/
#print uniformEmbedding_subtype_val /-
theorem uniformEmbedding_subtype_val {p : α → Prop} : UniformEmbedding (coe : Subtype p → α) :=
  uniformEmbedding_subtype_val
#align uniform_embedding_subtype_coe uniformEmbedding_subtype_val
-/

#print uniformEmbedding_set_inclusion /-
theorem uniformEmbedding_set_inclusion {s t : Set α} (hst : s ⊆ t) :
    UniformEmbedding (inclusion hst) :=
  { comap_uniformity :=
      by
      erw [uniformity_subtype, uniformity_subtype, comap_comap]
      congr
    inj := inclusion_injective hst }
#align uniform_embedding_set_inclusion uniformEmbedding_set_inclusion
-/

#print UniformEmbedding.comp /-
theorem UniformEmbedding.comp {g : β → γ} (hg : UniformEmbedding g) {f : α → β}
    (hf : UniformEmbedding f) : UniformEmbedding (g ∘ f) :=
  { hg.to_uniformInducing.comp hf.to_uniformInducing with inj := hg.inj.comp hf.inj }
#align uniform_embedding.comp UniformEmbedding.comp
-/

/- warning: equiv.uniform_embedding -> Equiv.uniformEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_4 : UniformSpace.{u1} α] [_inst_5 : UniformSpace.{u2} β] (f : Equiv.{succ u1, succ u2} α β), (UniformContinuous.{u1, u2} α β _inst_4 _inst_5 (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) f)) -> (UniformContinuous.{u2, u1} β α _inst_5 _inst_4 (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β α) (fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β f))) -> (UniformEmbedding.{u1, u2} α β _inst_4 _inst_5 (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : UniformSpace.{u2} α] [_inst_5 : UniformSpace.{u1} β] (f : Equiv.{succ u2, succ u1} α β), (UniformContinuous.{u2, u1} α β _inst_4 _inst_5 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) f)) -> (UniformContinuous.{u1, u2} β α _inst_5 _inst_4 (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : β) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} β α) (Equiv.symm.{succ u2, succ u1} α β f))) -> (UniformEmbedding.{u2, u1} α β _inst_4 _inst_5 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) f))
Case conversion may be inaccurate. Consider using '#align equiv.uniform_embedding Equiv.uniformEmbeddingₓ'. -/
theorem Equiv.uniformEmbedding {α β : Type _} [UniformSpace α] [UniformSpace β] (f : α ≃ β)
    (h₁ : UniformContinuous f) (h₂ : UniformContinuous f.symm) : UniformEmbedding f :=
  uniformEmbedding_iff'.2 ⟨f.Injective, h₁, by rwa [← Equiv.prodCongr_apply, ← map_equiv_symm]⟩
#align equiv.uniform_embedding Equiv.uniformEmbedding

#print uniformEmbedding_inl /-
theorem uniformEmbedding_inl : UniformEmbedding (Sum.inl : α → Sum α β) :=
  by
  refine' ⟨⟨_⟩, Sum.inl_injective⟩
  rw [Sum.uniformity, comap_sup, comap_map, comap_eq_bot_iff_compl_range.2 _, sup_bot_eq]
  · refine' mem_map.2 (univ_mem' _)
    simp
  · exact sum.inl_injective.prod_map Sum.inl_injective
#align uniform_embedding_inl uniformEmbedding_inl
-/

#print uniformEmbedding_inr /-
theorem uniformEmbedding_inr : UniformEmbedding (Sum.inr : β → Sum α β) :=
  by
  refine' ⟨⟨_⟩, Sum.inr_injective⟩
  rw [Sum.uniformity, comap_sup, comap_eq_bot_iff_compl_range.2 _, comap_map, bot_sup_eq]
  · exact sum.inr_injective.prod_map Sum.inr_injective
  · refine' mem_map.2 (univ_mem' _)
    simp
#align uniform_embedding_inr uniformEmbedding_inr
-/

#print UniformInducing.uniformEmbedding /-
/-- If the domain of a `uniform_inducing` map `f` is a `separated_space`, then `f` is injective,
hence it is a `uniform_embedding`. -/
protected theorem UniformInducing.uniformEmbedding [T0Space α] {f : α → β}
    (hf : UniformInducing f) : UniformEmbedding f :=
  ⟨hf, hf.Injective⟩
#align uniform_inducing.uniform_embedding UniformInducing.uniformEmbedding
-/

#print uniformEmbedding_iff_uniformInducing /-
theorem uniformEmbedding_iff_uniformInducing [T0Space α] {f : α → β} :
    UniformEmbedding f ↔ UniformInducing f :=
  ⟨UniformEmbedding.to_uniformInducing, UniformInducing.uniformEmbedding⟩
#align uniform_embedding_iff_uniform_inducing uniformEmbedding_iff_uniformInducing
-/

/- warning: comap_uniformity_of_spaced_out -> comap_uniformity_of_spaced_out is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : UniformSpace.{u1} β] {α : Type.{u2}} {f : α -> β} {s : Set.{u1} (Prod.{u1, u1} β β)}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} β β)) (Filter.{u1} (Prod.{u1, u1} β β)) (Filter.hasMem.{u1} (Prod.{u1, u1} β β)) s (uniformity.{u1} β _inst_2)) -> (Pairwise.{u2} α (fun (x : α) (y : α) => Not (Membership.Mem.{u1, u1} (Prod.{u1, u1} β β) (Set.{u1} (Prod.{u1, u1} β β)) (Set.hasMem.{u1} (Prod.{u1, u1} β β)) (Prod.mk.{u1, u1} β β (f x) (f y)) s))) -> (Eq.{succ u2} (Filter.{u2} (Prod.{u2, u2} α α)) (Filter.comap.{u2, u1} (Prod.{u2, u2} α α) (Prod.{u1, u1} β β) (Prod.map.{u2, u1, u2, u1} α β α β f f) (uniformity.{u1} β _inst_2)) (Filter.principal.{u2} (Prod.{u2, u2} α α) (idRel.{u2} α)))
but is expected to have type
  forall {β : Type.{u2}} [_inst_2 : UniformSpace.{u2} β] {α : Type.{u1}} {f : α -> β} {s : Set.{u2} (Prod.{u2, u2} β β)}, (Membership.mem.{u2, u2} (Set.{u2} (Prod.{u2, u2} β β)) (Filter.{u2} (Prod.{u2, u2} β β)) (instMembershipSetFilter.{u2} (Prod.{u2, u2} β β)) s (uniformity.{u2} β _inst_2)) -> (Pairwise.{u1} α (fun (x : α) (y : α) => Not (Membership.mem.{u2, u2} (Prod.{u2, u2} β β) (Set.{u2} (Prod.{u2, u2} β β)) (Set.instMembershipSet.{u2} (Prod.{u2, u2} β β)) (Prod.mk.{u2, u2} β β (f x) (f y)) s))) -> (Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.comap.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) (Prod.map.{u1, u2, u1, u2} α β α β f f) (uniformity.{u2} β _inst_2)) (Filter.principal.{u1} (Prod.{u1, u1} α α) (idRel.{u1} α)))
Case conversion may be inaccurate. Consider using '#align comap_uniformity_of_spaced_out comap_uniformity_of_spaced_outₓ'. -/
/-- If a map `f : α → β` sends any two distinct points to point that are **not** related by a fixed
`s ∈ 𝓤 β`, then `f` is uniform inducing with respect to the discrete uniformity on `α`:
the preimage of `𝓤 β` under `prod.map f f` is the principal filter generated by the diagonal in
`α × α`. -/
theorem comap_uniformity_of_spaced_out {α} {f : α → β} {s : Set (β × β)} (hs : s ∈ 𝓤 β)
    (hf : Pairwise fun x y => (f x, f y) ∉ s) : comap (Prod.map f f) (𝓤 β) = 𝓟 idRel :=
  by
  refine' le_antisymm _ (@refl_le_uniformity α (UniformSpace.comap f ‹_›))
  calc
    comap (Prod.map f f) (𝓤 β) ≤ comap (Prod.map f f) (𝓟 s) := comap_mono (le_principal_iff.2 hs)
    _ = 𝓟 (Prod.map f f ⁻¹' s) := comap_principal
    _ ≤ 𝓟 idRel := principal_mono.2 _
    
  rintro ⟨x, y⟩; simpa [not_imp_not] using @hf x y
#align comap_uniformity_of_spaced_out comap_uniformity_of_spaced_out

/- warning: uniform_embedding_of_spaced_out -> uniformEmbedding_of_spaced_out is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : UniformSpace.{u1} β] {α : Type.{u2}} {f : α -> β} {s : Set.{u1} (Prod.{u1, u1} β β)}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} β β)) (Filter.{u1} (Prod.{u1, u1} β β)) (Filter.hasMem.{u1} (Prod.{u1, u1} β β)) s (uniformity.{u1} β _inst_2)) -> (Pairwise.{u2} α (fun (x : α) (y : α) => Not (Membership.Mem.{u1, u1} (Prod.{u1, u1} β β) (Set.{u1} (Prod.{u1, u1} β β)) (Set.hasMem.{u1} (Prod.{u1, u1} β β)) (Prod.mk.{u1, u1} β β (f x) (f y)) s))) -> (UniformEmbedding.{u2, u1} α β (Bot.bot.{u2} (UniformSpace.{u2} α) (UniformSpace.hasBot.{u2} α)) _inst_2 f)
but is expected to have type
  forall {β : Type.{u2}} [_inst_2 : UniformSpace.{u2} β] {α : Type.{u1}} {f : α -> β} {s : Set.{u2} (Prod.{u2, u2} β β)}, (Membership.mem.{u2, u2} (Set.{u2} (Prod.{u2, u2} β β)) (Filter.{u2} (Prod.{u2, u2} β β)) (instMembershipSetFilter.{u2} (Prod.{u2, u2} β β)) s (uniformity.{u2} β _inst_2)) -> (Pairwise.{u1} α (fun (x : α) (y : α) => Not (Membership.mem.{u2, u2} (Prod.{u2, u2} β β) (Set.{u2} (Prod.{u2, u2} β β)) (Set.instMembershipSet.{u2} (Prod.{u2, u2} β β)) (Prod.mk.{u2, u2} β β (f x) (f y)) s))) -> (UniformEmbedding.{u1, u2} α β (Bot.bot.{u1} (UniformSpace.{u1} α) (instBotUniformSpace.{u1} α)) _inst_2 f)
Case conversion may be inaccurate. Consider using '#align uniform_embedding_of_spaced_out uniformEmbedding_of_spaced_outₓ'. -/
/-- If a map `f : α → β` sends any two distinct points to point that are **not** related by a fixed
`s ∈ 𝓤 β`, then `f` is a uniform embedding with respect to the discrete uniformity on `α`. -/
theorem uniformEmbedding_of_spaced_out {α} {f : α → β} {s : Set (β × β)} (hs : s ∈ 𝓤 β)
    (hf : Pairwise fun x y => (f x, f y) ∉ s) : @UniformEmbedding α β ⊥ ‹_› f :=
  by
  letI : UniformSpace α := ⊥; haveI := discreteTopology_bot α
  haveI : SeparatedSpace α := separated_iff_t2.2 inferInstance
  exact UniformInducing.uniformEmbedding ⟨comap_uniformity_of_spaced_out hs hf⟩
#align uniform_embedding_of_spaced_out uniformEmbedding_of_spaced_out

#print UniformEmbedding.embedding /-
protected theorem UniformEmbedding.embedding {f : α → β} (h : UniformEmbedding f) : Embedding f :=
  { induced := h.to_uniformInducing.Inducing.induced
    inj := h.inj }
#align uniform_embedding.embedding UniformEmbedding.embedding
-/

#print UniformEmbedding.denseEmbedding /-
theorem UniformEmbedding.denseEmbedding {f : α → β} (h : UniformEmbedding f) (hd : DenseRange f) :
    DenseEmbedding f :=
  { dense := hd
    inj := h.inj
    induced := h.Embedding.induced }
#align uniform_embedding.dense_embedding UniformEmbedding.denseEmbedding
-/

/- warning: closed_embedding_of_spaced_out -> closedEmbedding_of_spaced_out is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : UniformSpace.{u1} β] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] [_inst_5 : DiscreteTopology.{u2} α _inst_4] [_inst_6 : SeparatedSpace.{u1} β _inst_2] {f : α -> β} {s : Set.{u1} (Prod.{u1, u1} β β)}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} β β)) (Filter.{u1} (Prod.{u1, u1} β β)) (Filter.hasMem.{u1} (Prod.{u1, u1} β β)) s (uniformity.{u1} β _inst_2)) -> (Pairwise.{u2} α (fun (x : α) (y : α) => Not (Membership.Mem.{u1, u1} (Prod.{u1, u1} β β) (Set.{u1} (Prod.{u1, u1} β β)) (Set.hasMem.{u1} (Prod.{u1, u1} β β)) (Prod.mk.{u1, u1} β β (f x) (f y)) s))) -> (ClosedEmbedding.{u2, u1} α β _inst_4 (UniformSpace.toTopologicalSpace.{u1} β _inst_2) f)
but is expected to have type
  forall {β : Type.{u2}} [_inst_2 : UniformSpace.{u2} β] {α : Type.{u1}} [_inst_4 : TopologicalSpace.{u1} α] [_inst_5 : DiscreteTopology.{u1} α _inst_4] [_inst_6 : SeparatedSpace.{u2} β _inst_2] {f : α -> β} {s : Set.{u2} (Prod.{u2, u2} β β)}, (Membership.mem.{u2, u2} (Set.{u2} (Prod.{u2, u2} β β)) (Filter.{u2} (Prod.{u2, u2} β β)) (instMembershipSetFilter.{u2} (Prod.{u2, u2} β β)) s (uniformity.{u2} β _inst_2)) -> (Pairwise.{u1} α (fun (x : α) (y : α) => Not (Membership.mem.{u2, u2} (Prod.{u2, u2} β β) (Set.{u2} (Prod.{u2, u2} β β)) (Set.instMembershipSet.{u2} (Prod.{u2, u2} β β)) (Prod.mk.{u2, u2} β β (f x) (f y)) s))) -> (ClosedEmbedding.{u1, u2} α β _inst_4 (UniformSpace.toTopologicalSpace.{u2} β _inst_2) f)
Case conversion may be inaccurate. Consider using '#align closed_embedding_of_spaced_out closedEmbedding_of_spaced_outₓ'. -/
theorem closedEmbedding_of_spaced_out {α} [TopologicalSpace α] [DiscreteTopology α]
    [SeparatedSpace β] {f : α → β} {s : Set (β × β)} (hs : s ∈ 𝓤 β)
    (hf : Pairwise fun x y => (f x, f y) ∉ s) : ClosedEmbedding f :=
  by
  rcases DiscreteTopology.eq_bot α with rfl; letI : UniformSpace α := ⊥
  exact
    { (uniformEmbedding_of_spaced_out hs hf).Embedding with
      closed_range := isClosed_range_of_spaced_out hs hf }
#align closed_embedding_of_spaced_out closedEmbedding_of_spaced_out

#print closure_image_mem_nhds_of_uniformInducing /-
theorem closure_image_mem_nhds_of_uniformInducing {s : Set (α × α)} {e : α → β} (b : β)
    (he₁ : UniformInducing e) (he₂ : DenseInducing e) (hs : s ∈ 𝓤 α) :
    ∃ a, closure (e '' { a' | (a, a') ∈ s }) ∈ 𝓝 b :=
  have : s ∈ comap (fun p : α × α => (e p.1, e p.2)) (𝓤 β) := he₁.comap_uniformity.symm ▸ hs
  let ⟨t₁, ht₁u, ht₁⟩ := this
  have ht₁ : ∀ p : α × α, (e p.1, e p.2) ∈ t₁ → p ∈ s := ht₁
  let ⟨t₂, ht₂u, ht₂s, ht₂c⟩ := comp_symm_of_uniformity ht₁u
  let ⟨t, htu, hts, htc⟩ := comp_symm_of_uniformity ht₂u
  have : preimage e { b' | (b, b') ∈ t₂ } ∈ comap e (𝓝 b) :=
    preimage_mem_comap <| mem_nhds_left b ht₂u
  let ⟨a, (ha : (b, e a) ∈ t₂)⟩ := (he₂.comap_nhds_neBot _).nonempty_of_mem this
  have :
    ∀ (b') (s' : Set (β × β)),
      (b, b') ∈ t →
        s' ∈ 𝓤 β → ({ y : β | (b', y) ∈ s' } ∩ e '' { a' : α | (a, a') ∈ s }).Nonempty :=
    fun b' s' hb' hs' =>
    have : preimage e { b'' | (b', b'') ∈ s' ∩ t } ∈ comap e (𝓝 b') :=
      preimage_mem_comap <| mem_nhds_left b' <| inter_mem hs' htu
    let ⟨a₂, ha₂s', ha₂t⟩ := (he₂.comap_nhds_neBot _).nonempty_of_mem this
    have : (e a, e a₂) ∈ t₁ :=
      ht₂c <| prod_mk_mem_compRel (ht₂s ha) <| htc <| prod_mk_mem_compRel hb' ha₂t
    have : e a₂ ∈ { b'' : β | (b', b'') ∈ s' } ∩ e '' { a' | (a, a') ∈ s } :=
      ⟨ha₂s', mem_image_of_mem _ <| ht₁ (a, a₂) this⟩
    ⟨_, this⟩
  have : ∀ b', (b, b') ∈ t → NeBot (𝓝 b' ⊓ 𝓟 (e '' { a' | (a, a') ∈ s })) :=
    by
    intro b' hb'
    rw [nhds_eq_uniformity, lift'_inf_principal_eq, lift'_ne_bot_iff]
    exact fun s => this b' s hb'
    exact monotone_preimage.inter monotone_const
  have : ∀ b', (b, b') ∈ t → b' ∈ closure (e '' { a' | (a, a') ∈ s }) := fun b' hb' => by
    rw [closure_eq_cluster_pts] <;> exact this b' hb'
  ⟨a, (𝓝 b).sets_of_superset (mem_nhds_left b htu) this⟩
#align closure_image_mem_nhds_of_uniform_inducing closure_image_mem_nhds_of_uniformInducing
-/

#print uniformEmbedding_subtypeEmb /-
theorem uniformEmbedding_subtypeEmb (p : α → Prop) {e : α → β} (ue : UniformEmbedding e)
    (de : DenseEmbedding e) : UniformEmbedding (DenseEmbedding.subtypeEmb p e) :=
  { comap_uniformity := by
      simp [comap_comap, (· ∘ ·), DenseEmbedding.subtypeEmb, uniformity_subtype,
        ue.comap_uniformity.symm]
    inj := (de.Subtype p).inj }
#align uniform_embedding_subtype_emb uniformEmbedding_subtypeEmb
-/

/- warning: uniform_embedding.prod -> UniformEmbedding.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {α' : Type.{u3}} {β' : Type.{u4}} [_inst_4 : UniformSpace.{u3} α'] [_inst_5 : UniformSpace.{u4} β'] {e₁ : α -> α'} {e₂ : β -> β'}, (UniformEmbedding.{u1, u3} α α' _inst_1 _inst_4 e₁) -> (UniformEmbedding.{u2, u4} β β' _inst_2 _inst_5 e₂) -> (UniformEmbedding.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} α' β') (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.uniformSpace.{u3, u4} α' β' _inst_4 _inst_5) (fun (p : Prod.{u1, u2} α β) => Prod.mk.{u3, u4} α' β' (e₁ (Prod.fst.{u1, u2} α β p)) (e₂ (Prod.snd.{u1, u2} α β p))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : UniformSpace.{u3} α] [_inst_2 : UniformSpace.{u4} β] {α' : Type.{u2}} {β' : Type.{u1}} [_inst_4 : UniformSpace.{u2} α'] [_inst_5 : UniformSpace.{u1} β'] {e₁ : α -> α'} {e₂ : β -> β'}, (UniformEmbedding.{u3, u2} α α' _inst_1 _inst_4 e₁) -> (UniformEmbedding.{u4, u1} β β' _inst_2 _inst_5 e₂) -> (UniformEmbedding.{max u3 u4, max u1 u2} (Prod.{u3, u4} α β) (Prod.{u2, u1} α' β') (instUniformSpaceProd.{u3, u4} α β _inst_1 _inst_2) (instUniformSpaceProd.{u2, u1} α' β' _inst_4 _inst_5) (fun (p : Prod.{u3, u4} α β) => Prod.mk.{u2, u1} α' β' (e₁ (Prod.fst.{u3, u4} α β p)) (e₂ (Prod.snd.{u3, u4} α β p))))
Case conversion may be inaccurate. Consider using '#align uniform_embedding.prod UniformEmbedding.prodₓ'. -/
theorem UniformEmbedding.prod {α' : Type _} {β' : Type _} [UniformSpace α'] [UniformSpace β']
    {e₁ : α → α'} {e₂ : β → β'} (h₁ : UniformEmbedding e₁) (h₂ : UniformEmbedding e₂) :
    UniformEmbedding fun p : α × β => (e₁ p.1, e₂ p.2) :=
  { h₁.to_uniformInducing.Prod h₂.to_uniformInducing with inj := h₁.inj.Prod_map h₂.inj }
#align uniform_embedding.prod UniformEmbedding.prod

#print isComplete_of_complete_image /-
theorem isComplete_of_complete_image {m : α → β} {s : Set α} (hm : UniformInducing m)
    (hs : IsComplete (m '' s)) : IsComplete s :=
  by
  intro f hf hfs
  rw [le_principal_iff] at hfs
  obtain ⟨_, ⟨x, hx, rfl⟩, hyf⟩ : ∃ y ∈ m '' s, map m f ≤ 𝓝 y
  exact hs (f.map m) (hf.map hm.uniform_continuous) (le_principal_iff.2 (image_mem_map hfs))
  rw [map_le_iff_le_comap, ← nhds_induced, ← hm.inducing.induced] at hyf
  exact ⟨x, hx, hyf⟩
#align is_complete_of_complete_image isComplete_of_complete_image
-/

#print IsComplete.completeSpace_coe /-
theorem IsComplete.completeSpace_coe {s : Set α} (hs : IsComplete s) : CompleteSpace s :=
  completeSpace_iff_isComplete_univ.2 <|
    isComplete_of_complete_image uniformEmbedding_subtype_val.to_uniformInducing <| by simp [hs]
#align is_complete.complete_space_coe IsComplete.completeSpace_coe
-/

#print isComplete_image_iff /-
/-- A set is complete iff its image under a uniform inducing map is complete. -/
theorem isComplete_image_iff {m : α → β} {s : Set α} (hm : UniformInducing m) :
    IsComplete (m '' s) ↔ IsComplete s :=
  by
  refine' ⟨isComplete_of_complete_image hm, fun c => _⟩
  haveI : CompleteSpace s := c.complete_space_coe
  set m' : s → β := m ∘ coe
  suffices IsComplete (range m') by rwa [range_comp, Subtype.range_coe] at this
  have hm' : UniformInducing m' := hm.comp uniform_embedding_subtype_coe.to_uniform_inducing
  intro f hf hfm
  rw [Filter.le_principal_iff] at hfm
  have cf' : Cauchy (comap m' f) :=
    hf.comap' hm'.comap_uniformity.le (ne_bot.comap_of_range_mem hf.1 hfm)
  rcases CompleteSpace.complete cf' with ⟨x, hx⟩
  rw [hm'.inducing.nhds_eq_comap, comap_le_comap_iff hfm] at hx
  use m' x, mem_range_self _, hx
#align is_complete_image_iff isComplete_image_iff
-/

#print completeSpace_iff_isComplete_range /-
theorem completeSpace_iff_isComplete_range {f : α → β} (hf : UniformInducing f) :
    CompleteSpace α ↔ IsComplete (range f) := by
  rw [completeSpace_iff_isComplete_univ, ← isComplete_image_iff hf, image_univ]
#align complete_space_iff_is_complete_range completeSpace_iff_isComplete_range
-/

#print UniformInducing.isComplete_range /-
theorem UniformInducing.isComplete_range [CompleteSpace α] {f : α → β} (hf : UniformInducing f) :
    IsComplete (range f) :=
  (completeSpace_iff_isComplete_range hf).1 ‹_›
#align uniform_inducing.is_complete_range UniformInducing.isComplete_range
-/

#print completeSpace_congr /-
theorem completeSpace_congr {e : α ≃ β} (he : UniformEmbedding e) :
    CompleteSpace α ↔ CompleteSpace β := by
  rw [completeSpace_iff_isComplete_range he.to_uniform_inducing, e.range_eq_univ,
    completeSpace_iff_isComplete_univ]
#align complete_space_congr completeSpace_congr
-/

#print completeSpace_coe_iff_isComplete /-
theorem completeSpace_coe_iff_isComplete {s : Set α} : CompleteSpace s ↔ IsComplete s :=
  (completeSpace_iff_isComplete_range uniformEmbedding_subtype_val.to_uniformInducing).trans <| by
    rw [Subtype.range_coe]
#align complete_space_coe_iff_is_complete completeSpace_coe_iff_isComplete
-/

#print IsClosed.completeSpace_coe /-
theorem IsClosed.completeSpace_coe [CompleteSpace α] {s : Set α} (hs : IsClosed s) :
    CompleteSpace s :=
  hs.IsComplete.completeSpace_coe
#align is_closed.complete_space_coe IsClosed.completeSpace_coe
-/

#print ULift.completeSpace /-
/-- The lift of a complete space to another universe is still complete. -/
instance ULift.completeSpace [h : CompleteSpace α] : CompleteSpace (ULift α) :=
  haveI : UniformEmbedding (@Equiv.ulift α) := ⟨⟨rfl⟩, ULift.down_injective⟩
  (completeSpace_congr this).2 h
#align ulift.complete_space ULift.completeSpace
-/

/- warning: complete_space_extension -> completeSpace_extension is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {m : β -> α}, (UniformInducing.{u2, u1} β α _inst_2 _inst_1 m) -> (DenseRange.{u1, u2} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) β m) -> (forall (f : Filter.{u2} β), (Cauchy.{u2} β _inst_2 f) -> (Exists.{succ u1} α (fun (x : α) => LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (Filter.map.{u2, u1} β α m f) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x)))) -> (CompleteSpace.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {m : β -> α}, (UniformInducing.{u2, u1} β α _inst_2 _inst_1 m) -> (DenseRange.{u1, u2} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) β m) -> (forall (f : Filter.{u2} β), (Cauchy.{u2} β _inst_2 f) -> (Exists.{succ u1} α (fun (x : α) => LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Filter.map.{u2, u1} β α m f) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x)))) -> (CompleteSpace.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align complete_space_extension completeSpace_extensionₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem completeSpace_extension {m : β → α} (hm : UniformInducing m) (dense : DenseRange m)
    (h : ∀ f : Filter β, Cauchy f → ∃ x : α, map m f ≤ 𝓝 x) : CompleteSpace α :=
  ⟨fun f : Filter α => fun hf : Cauchy f =>
    let p : Set (α × α) → Set α → Set α := fun s t => { y : α | ∃ x : α, x ∈ t ∧ (x, y) ∈ s }
    let g := (𝓤 α).lift fun s => f.lift' (p s)
    have mp₀ : Monotone p := fun a b h t s ⟨x, xs, xa⟩ => ⟨x, xs, h xa⟩
    have mp₁ : ∀ {s}, Monotone (p s) := fun s a b h x ⟨y, ya, yxs⟩ => ⟨y, h ya, yxs⟩
    have : f ≤ g :=
      le_infᵢ fun s =>
        le_infᵢ fun hs =>
          le_infᵢ fun t =>
            le_infᵢ fun ht =>
              le_principal_iff.mpr <| mem_of_superset ht fun x hx => ⟨x, hx, refl_mem_uniformity hs⟩
    have : NeBot g := hf.left.mono this
    have : NeBot (comap m g) :=
      comap_neBot fun t ht =>
        let ⟨t', ht', ht_mem⟩ := (mem_lift_sets <| monotone_lift' monotone_const mp₀).mp ht
        let ⟨t'', ht'', ht'_sub⟩ := (mem_lift'_sets mp₁).mp ht_mem
        let ⟨x, (hx : x ∈ t'')⟩ := hf.left.nonempty_of_mem ht''
        have h₀ : NeBot (𝓝[range m] x) := Dense.nhdsWithin_neBot x
        have h₁ : { y | (x, y) ∈ t' } ∈ 𝓝[range m] x :=
          @mem_inf_of_left α (𝓝 x) (𝓟 (range m)) _ <| mem_nhds_left x ht'
        have h₂ : range m ∈ 𝓝[range m] x :=
          @mem_inf_of_right α (𝓝 x) (𝓟 (range m)) _ <| Subset.refl _
        have : { y | (x, y) ∈ t' } ∩ range m ∈ 𝓝[range m] x := @inter_mem α (𝓝[range m] x) _ _ h₁ h₂
        let ⟨y, xyt', b, b_eq⟩ := h₀.nonempty_of_mem this
        ⟨b, b_eq.symm ▸ ht'_sub ⟨x, hx, xyt'⟩⟩
    have : Cauchy g :=
      ⟨‹NeBot g›, fun s hs =>
        let ⟨s₁, hs₁, (comp_s₁ : compRel s₁ s₁ ⊆ s)⟩ := comp_mem_uniformity_sets hs
        let ⟨s₂, hs₂, (comp_s₂ : compRel s₂ s₂ ⊆ s₁)⟩ := comp_mem_uniformity_sets hs₁
        let ⟨t, ht, (prod_t : t ×ˢ t ⊆ s₂)⟩ := mem_prod_same_iff.mp (hf.right hs₂)
        have hg₁ : p (preimage Prod.swap s₁) t ∈ g :=
          mem_lift (symm_le_uniformity hs₁) <| @mem_lift' α α f _ t ht
        have hg₂ : p s₂ t ∈ g := mem_lift hs₂ <| @mem_lift' α α f _ t ht
        have hg : p (Prod.swap ⁻¹' s₁) t ×ˢ p s₂ t ∈ g ×ᶠ g := @prod_mem_prod α α _ _ g g hg₁ hg₂
        (g ×ᶠ g).sets_of_superset hg fun ⟨a, b⟩ ⟨⟨c₁, c₁t, hc₁⟩, ⟨c₂, c₂t, hc₂⟩⟩ =>
          have : (c₁, c₂) ∈ t ×ˢ t := ⟨c₁t, c₂t⟩
          comp_s₁ <| prod_mk_mem_compRel hc₁ <| comp_s₂ <| prod_mk_mem_compRel (prod_t this) hc₂⟩
    have : Cauchy (Filter.comap m g) := ‹Cauchy g›.comap' (le_of_eq hm.comap_uniformity) ‹_›
    let ⟨x, (hx : map m (Filter.comap m g) ≤ 𝓝 x)⟩ := h _ this
    have : ClusterPt x (map m (Filter.comap m g)) :=
      (le_nhds_iff_adhp_of_cauchy (this.map hm.UniformContinuous)).mp hx
    have : ClusterPt x g := this.mono map_comap_le
    ⟨x,
      calc
        f ≤ g := by assumption
        _ ≤ 𝓝 x := le_nhds_of_cauchy_adhp ‹Cauchy g› this
        ⟩⟩
#align complete_space_extension completeSpace_extension

#print totallyBounded_preimage /-
theorem totallyBounded_preimage {f : α → β} {s : Set β} (hf : UniformEmbedding f)
    (hs : TotallyBounded s) : TotallyBounded (f ⁻¹' s) := fun t ht =>
  by
  rw [← hf.comap_uniformity] at ht
  rcases mem_comap.2 ht with ⟨t', ht', ts⟩
  rcases totallyBounded_iff_subset.1 (totallyBounded_subset (image_preimage_subset f s) hs) _
      ht' with
    ⟨c, cs, hfc, hct⟩
  refine' ⟨f ⁻¹' c, hfc.preimage (hf.inj.inj_on _), fun x h => _⟩
  have := hct (mem_image_of_mem f h); simp at this⊢
  rcases this with ⟨z, zc, zt⟩
  rcases cs zc with ⟨y, yc, rfl⟩
  exact ⟨y, zc, ts zt⟩
#align totally_bounded_preimage totallyBounded_preimage
-/

#print CompleteSpace.sum /-
instance CompleteSpace.sum [CompleteSpace α] [CompleteSpace β] : CompleteSpace (Sum α β) :=
  by
  rw [completeSpace_iff_isComplete_univ, ← range_inl_union_range_inr]
  exact
    uniform_embedding_inl.to_uniform_inducing.is_complete_range.union
      uniform_embedding_inr.to_uniform_inducing.is_complete_range
#align complete_space.sum CompleteSpace.sum
-/

end

/- warning: uniform_embedding_comap -> uniformEmbedding_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} [u : UniformSpace.{u2} β], (Function.Injective.{succ u1, succ u2} α β f) -> (UniformEmbedding.{u1, u2} α β (UniformSpace.comap.{u1, u2} α β f u) u f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} [u : UniformSpace.{u1} β], (Function.Injective.{succ u2, succ u1} α β f) -> (UniformEmbedding.{u2, u1} α β (UniformSpace.comap.{u2, u1} α β f u) u f)
Case conversion may be inaccurate. Consider using '#align uniform_embedding_comap uniformEmbedding_comapₓ'. -/
theorem uniformEmbedding_comap {α : Type _} {β : Type _} {f : α → β} [u : UniformSpace β]
    (hf : Function.Injective f) : @UniformEmbedding α β (UniformSpace.comap f u) u f :=
  @UniformEmbedding.mk _ _ (UniformSpace.comap f u) _ _
    (@UniformInducing.mk _ _ (UniformSpace.comap f u) _ _ rfl) hf
#align uniform_embedding_comap uniformEmbedding_comap

#print Embedding.comapUniformSpace /-
/-- Pull back a uniform space structure by an embedding, adjusting the new uniform structure to
make sure that its topology is defeq to the original one. -/
def Embedding.comapUniformSpace {α β} [TopologicalSpace α] [u : UniformSpace β] (f : α → β)
    (h : Embedding f) : UniformSpace α :=
  (u.comap f).replaceTopology h.induced
#align embedding.comap_uniform_space Embedding.comapUniformSpace
-/

/- warning: embedding.to_uniform_embedding -> Embedding.to_uniformEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [u : UniformSpace.{u2} β] (f : α -> β) (h : Embedding.{u1, u2} α β _inst_1 (UniformSpace.toTopologicalSpace.{u2} β u) f), UniformEmbedding.{u1, u2} α β (Embedding.comapUniformSpace.{u1, u2} α β _inst_1 u f h) u f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [u : UniformSpace.{u1} β] (f : α -> β) (h : Embedding.{u2, u1} α β _inst_1 (UniformSpace.toTopologicalSpace.{u1} β u) f), UniformEmbedding.{u2, u1} α β (Embedding.comapUniformSpace.{u2, u1} α β _inst_1 u f h) u f
Case conversion may be inaccurate. Consider using '#align embedding.to_uniform_embedding Embedding.to_uniformEmbeddingₓ'. -/
theorem Embedding.to_uniformEmbedding {α β} [TopologicalSpace α] [u : UniformSpace β] (f : α → β)
    (h : Embedding f) : @UniformEmbedding α β (h.comap_uniformSpace f) u f :=
  { comap_uniformity := rfl
    inj := h.inj }
#align embedding.to_uniform_embedding Embedding.to_uniformEmbedding

section UniformExtension

variable {α : Type _} {β : Type _} {γ : Type _} [UniformSpace α] [UniformSpace β] [UniformSpace γ]
  {e : β → α} (h_e : UniformInducing e) (h_dense : DenseRange e) {f : β → γ}
  (h_f : UniformContinuous f)

-- mathport name: exprψ
local notation "ψ" => (h_e.DenseInducing h_dense).extend f

#print uniformly_extend_exists /-
theorem uniformly_extend_exists [CompleteSpace γ] (a : α) : ∃ c, Tendsto f (comap e (𝓝 a)) (𝓝 c) :=
  let de := h_e.DenseInducing h_dense
  have : Cauchy (𝓝 a) := cauchy_nhds
  have : Cauchy (comap e (𝓝 a)) :=
    this.comap' (le_of_eq h_e.comap_uniformity) (de.comap_nhds_neBot _)
  have : Cauchy (map f (comap e (𝓝 a))) := this.map h_f
  CompleteSpace.complete this
#align uniformly_extend_exists uniformly_extend_exists
-/

/- warning: uniform_extend_subtype -> uniform_extend_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] [_inst_4 : CompleteSpace.{u3} γ _inst_3] {p : α -> Prop} {e : α -> β} {f : α -> γ} {b : β} {s : Set.{u1} α}, (UniformContinuous.{u1, u3} (Subtype.{succ u1} α p) γ (Subtype.uniformSpace.{u1} α p _inst_1) _inst_3 (fun (x : Subtype.{succ u1} α p) => f (Subtype.val.{succ u1} α p x))) -> (UniformEmbedding.{u1, u2} α β _inst_1 _inst_2 e) -> (forall (x : β), Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (closure.{u2} β (UniformSpace.toTopologicalSpace.{u2} β _inst_2) (Set.range.{u2, succ u1} β α e))) -> (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) (closure.{u2} β (UniformSpace.toTopologicalSpace.{u2} β _inst_2) (Set.image.{u1, u2} α β e s)) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β _inst_2) b)) -> (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) s) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (p x)) -> (Exists.{succ u3} γ (fun (c : γ) => Filter.Tendsto.{u1, u3} α γ f (Filter.comap.{u1, u2} α β e (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β _inst_2) b)) (nhds.{u3} γ (UniformSpace.toTopologicalSpace.{u3} γ _inst_3) c)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] [_inst_3 : UniformSpace.{u3} γ] [_inst_4 : CompleteSpace.{u3} γ _inst_3] {p : α -> Prop} {e : α -> β} {f : α -> γ} {b : β} {s : Set.{u2} α}, (UniformContinuous.{u2, u3} (Subtype.{succ u2} α p) γ (instUniformSpaceSubtype.{u2} α p _inst_1) _inst_3 (fun (x : Subtype.{succ u2} α p) => f (Subtype.val.{succ u2} α p x))) -> (UniformEmbedding.{u2, u1} α β _inst_1 _inst_2 e) -> (forall (x : β), Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (closure.{u1} β (UniformSpace.toTopologicalSpace.{u1} β _inst_2) (Set.range.{u1, succ u2} β α e))) -> (Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) (closure.{u1} β (UniformSpace.toTopologicalSpace.{u1} β _inst_2) (Set.image.{u2, u1} α β e s)) (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β _inst_2) b)) -> (IsClosed.{u2} α (UniformSpace.toTopologicalSpace.{u2} α _inst_1) s) -> (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (p x)) -> (Exists.{succ u3} γ (fun (c : γ) => Filter.Tendsto.{u2, u3} α γ f (Filter.comap.{u2, u1} α β e (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β _inst_2) b)) (nhds.{u3} γ (UniformSpace.toTopologicalSpace.{u3} γ _inst_3) c)))
Case conversion may be inaccurate. Consider using '#align uniform_extend_subtype uniform_extend_subtypeₓ'. -/
theorem uniform_extend_subtype [CompleteSpace γ] {p : α → Prop} {e : α → β} {f : α → γ} {b : β}
    {s : Set α} (hf : UniformContinuous fun x : Subtype p => f x.val) (he : UniformEmbedding e)
    (hd : ∀ x : β, x ∈ closure (range e)) (hb : closure (e '' s) ∈ 𝓝 b) (hs : IsClosed s)
    (hp : ∀ x ∈ s, p x) : ∃ c, Tendsto f (comap e (𝓝 b)) (𝓝 c) :=
  by
  have de : DenseEmbedding e := he.DenseEmbedding hd
  have de' : DenseEmbedding (DenseEmbedding.subtypeEmb p e) := de.subtype p
  have ue' : UniformEmbedding (DenseEmbedding.subtypeEmb p e) := uniformEmbedding_subtypeEmb _ he de
  have : b ∈ closure (e '' { x | p x }) :=
    (closure_mono <| monotone_image <| hp) (mem_of_mem_nhds hb)
  let
    ⟨c,
      (hc :
        tendsto (f ∘ Subtype.val) (comap (DenseEmbedding.subtypeEmb p e) (𝓝 ⟨b, this⟩)) (𝓝 c))⟩ :=
    uniformly_extend_exists ue'.to_uniformInducing de'.dense hf _
  rw [nhds_subtype_eq_comap] at hc
  simp [comap_comap] at hc
  change tendsto (f ∘ @Subtype.val α p) (comap (e ∘ @Subtype.val α p) (𝓝 b)) (𝓝 c) at hc
  rw [← comap_comap, tendsto_comap'_iff] at hc
  exact ⟨c, hc⟩
  exact
    ⟨_, hb, fun x => by
      change e x ∈ closure (e '' s) → x ∈ range Subtype.val
      rw [← closure_induced, mem_closure_iff_clusterPt, ClusterPt, ne_bot_iff, nhds_induced, ←
        de.to_dense_inducing.nhds_eq_comap, ← mem_closure_iff_nhds_neBot, hs.closure_eq]
      exact fun hxs => ⟨⟨x, hp x hxs⟩, rfl⟩⟩
#align uniform_extend_subtype uniform_extend_subtype

include h_f

#print uniformly_extend_spec /-
theorem uniformly_extend_spec [CompleteSpace γ] (a : α) : Tendsto f (comap e (𝓝 a)) (𝓝 (ψ a)) := by
  simpa only [DenseInducing.extend] using
    tendsto_nhds_limUnder (uniformly_extend_exists h_e ‹_› h_f _)
#align uniformly_extend_spec uniformly_extend_spec
-/

/- warning: uniform_continuous_uniformly_extend -> uniformContinuous_uniformly_extend is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] {e : β -> α} (h_e : UniformInducing.{u2, u1} β α _inst_2 _inst_1 e) (h_dense : DenseRange.{u1, u2} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) β e) {f : β -> γ}, (UniformContinuous.{u2, u3} β γ _inst_2 _inst_3 f) -> (forall [cγ : CompleteSpace.{u3} γ _inst_3], UniformContinuous.{u1, u3} α γ _inst_1 _inst_3 (DenseInducing.extend.{u2, u1, u3} β α γ (UniformSpace.toTopologicalSpace.{u2} β _inst_2) (UniformSpace.toTopologicalSpace.{u1} α _inst_1) e (UniformSpace.toTopologicalSpace.{u3} γ _inst_3) (UniformInducing.denseInducing.{u2, u1} β α _inst_2 _inst_1 e h_e h_dense) f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] [_inst_3 : UniformSpace.{u3} γ] {e : β -> α} (h_e : UniformInducing.{u1, u2} β α _inst_2 _inst_1 e) (h_dense : DenseRange.{u2, u1} α (UniformSpace.toTopologicalSpace.{u2} α _inst_1) β e) {f : β -> γ}, (UniformContinuous.{u1, u3} β γ _inst_2 _inst_3 f) -> (forall [cγ : CompleteSpace.{u3} γ _inst_3], UniformContinuous.{u2, u3} α γ _inst_1 _inst_3 (DenseInducing.extend.{u1, u2, u3} β α γ (UniformSpace.toTopologicalSpace.{u1} β _inst_2) (UniformSpace.toTopologicalSpace.{u2} α _inst_1) e (UniformSpace.toTopologicalSpace.{u3} γ _inst_3) (UniformInducing.denseInducing.{u1, u2} β α _inst_2 _inst_1 e h_e h_dense) f))
Case conversion may be inaccurate. Consider using '#align uniform_continuous_uniformly_extend uniformContinuous_uniformly_extendₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem uniformContinuous_uniformly_extend [cγ : CompleteSpace γ] : UniformContinuous ψ :=
  fun d hd =>
  let ⟨s, hs, hs_comp⟩ :=
    (mem_lift'_sets <| monotone_id.compRel <| monotone_id.compRel monotone_id).mp
      (comp_le_uniformity3 hd)
  have h_pnt : ∀ {a m}, m ∈ 𝓝 a → ∃ c, c ∈ f '' preimage e m ∧ (c, ψ a) ∈ s ∧ (ψ a, c) ∈ s :=
    fun a m hm =>
    have nb : NeBot (map f (comap e (𝓝 a))) :=
      ((h_e.DenseInducing h_dense).comap_nhds_neBot _).map _
    have :
      f '' preimage e m ∩ ({ c | (c, ψ a) ∈ s } ∩ { c | (ψ a, c) ∈ s }) ∈ map f (comap e (𝓝 a)) :=
      inter_mem (image_mem_map <| preimage_mem_comap <| hm)
        (uniformly_extend_spec h_e h_dense h_f _
          (inter_mem (mem_nhds_right _ hs) (mem_nhds_left _ hs)))
    nb.nonempty_of_mem this
  have : preimage (fun p : β × β => (f p.1, f p.2)) s ∈ 𝓤 β := h_f hs
  have :
    preimage (fun p : β × β => (f p.1, f p.2)) s ∈ comap (fun x : β × β => (e x.1, e x.2)) (𝓤 α) :=
    by rwa [h_e.comap_uniformity.symm] at this
  let ⟨t, ht, ts⟩ := this
  show preimage (fun p : α × α => (ψ p.1, ψ p.2)) d ∈ 𝓤 α from
    (𝓤 α).sets_of_superset (interior_mem_uniformity ht) fun ⟨x₁, x₂⟩ hx_t =>
      have : 𝓝 (x₁, x₂) ≤ 𝓟 (interior t) := isOpen_iff_nhds.mp isOpen_interior (x₁, x₂) hx_t
      have : interior t ∈ 𝓝 x₁ ×ᶠ 𝓝 x₂ := by rwa [nhds_prod_eq, le_principal_iff] at this
      let ⟨m₁, hm₁, m₂, hm₂, (hm : m₁ ×ˢ m₂ ⊆ interior t)⟩ := mem_prod_iff.mp this
      let ⟨a, ha₁, _, ha₂⟩ := h_pnt hm₁
      let ⟨b, hb₁, hb₂, _⟩ := h_pnt hm₂
      have : (e ⁻¹' m₁) ×ˢ (e ⁻¹' m₂) ⊆ (fun p : β × β => (f p.1, f p.2)) ⁻¹' s :=
        calc
          _ ⊆ preimage (fun p : β × β => (e p.1, e p.2)) (interior t) := preimage_mono hm
          _ ⊆ preimage (fun p : β × β => (e p.1, e p.2)) t := (preimage_mono interior_subset)
          _ ⊆ preimage (fun p : β × β => (f p.1, f p.2)) s := ts
          
      have : (f '' (e ⁻¹' m₁)) ×ˢ (f '' (e ⁻¹' m₂)) ⊆ s :=
        calc
          (f '' (e ⁻¹' m₁)) ×ˢ (f '' (e ⁻¹' m₂)) =
              (fun p : β × β => (f p.1, f p.2)) '' (e ⁻¹' m₁) ×ˢ (e ⁻¹' m₂) :=
            prod_image_image_eq
          _ ⊆ (fun p : β × β => (f p.1, f p.2)) '' ((fun p : β × β => (f p.1, f p.2)) ⁻¹' s) :=
            (monotone_image this)
          _ ⊆ s := image_preimage_subset _ _
          
      have : (a, b) ∈ s := @this (a, b) ⟨ha₁, hb₁⟩
      hs_comp <| show (ψ x₁, ψ x₂) ∈ compRel s (compRel s s) from ⟨a, ha₂, ⟨b, this, hb₂⟩⟩
#align uniform_continuous_uniformly_extend uniformContinuous_uniformly_extend

omit h_f

variable [SeparatedSpace γ]

#print uniformly_extend_of_ind /-
theorem uniformly_extend_of_ind (b : β) : ψ (e b) = f b :=
  DenseInducing.extend_eq_at _ h_f.Continuous.ContinuousAt
#align uniformly_extend_of_ind uniformly_extend_of_ind
-/

/- warning: uniformly_extend_unique -> uniformly_extend_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] {e : β -> α} (h_e : UniformInducing.{u2, u1} β α _inst_2 _inst_1 e) (h_dense : DenseRange.{u1, u2} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) β e) {f : β -> γ} [_inst_4 : SeparatedSpace.{u3} γ _inst_3] {g : α -> γ}, (forall (b : β), Eq.{succ u3} γ (g (e b)) (f b)) -> (Continuous.{u1, u3} α γ (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u3} γ _inst_3) g) -> (Eq.{max (succ u1) (succ u3)} (α -> γ) (DenseInducing.extend.{u2, u1, u3} β α γ (UniformSpace.toTopologicalSpace.{u2} β _inst_2) (UniformSpace.toTopologicalSpace.{u1} α _inst_1) e (UniformSpace.toTopologicalSpace.{u3} γ _inst_3) (UniformInducing.denseInducing.{u2, u1} β α _inst_2 _inst_1 e h_e h_dense) f) g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] [_inst_3 : UniformSpace.{u3} γ] {e : β -> α} (h_e : UniformInducing.{u1, u2} β α _inst_2 _inst_1 e) (h_dense : DenseRange.{u2, u1} α (UniformSpace.toTopologicalSpace.{u2} α _inst_1) β e) {f : β -> γ} [_inst_4 : SeparatedSpace.{u3} γ _inst_3] {g : α -> γ}, (forall (b : β), Eq.{succ u3} γ (g (e b)) (f b)) -> (Continuous.{u2, u3} α γ (UniformSpace.toTopologicalSpace.{u2} α _inst_1) (UniformSpace.toTopologicalSpace.{u3} γ _inst_3) g) -> (Eq.{max (succ u2) (succ u3)} (α -> γ) (DenseInducing.extend.{u1, u2, u3} β α γ (UniformSpace.toTopologicalSpace.{u1} β _inst_2) (UniformSpace.toTopologicalSpace.{u2} α _inst_1) e (UniformSpace.toTopologicalSpace.{u3} γ _inst_3) (UniformInducing.denseInducing.{u1, u2} β α _inst_2 _inst_1 e h_e h_dense) f) g)
Case conversion may be inaccurate. Consider using '#align uniformly_extend_unique uniformly_extend_uniqueₓ'. -/
theorem uniformly_extend_unique {g : α → γ} (hg : ∀ b, g (e b) = f b) (hc : Continuous g) : ψ = g :=
  DenseInducing.extend_unique _ hg hc
#align uniformly_extend_unique uniformly_extend_unique

end UniformExtension

