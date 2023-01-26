/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad

! This file was ported from Lean 3 source module topology.basic
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Filter.Ultrafilter
import Mathbin.Algebra.Support
import Mathbin.Order.Filter.Lift

/-!
# Basic theory of topological spaces.

The main definition is the type class `topological_space α` which endows a type `α` with a topology.
Then `set α` gets predicates `is_open`, `is_closed` and functions `interior`, `closure` and
`frontier`. Each point `x` of `α` gets a neighborhood filter `𝓝 x`. A filter `F` on `α` has
`x` as a cluster point if `cluster_pt x F : 𝓝 x ⊓ F ≠ ⊥`. A map `f : ι → α` clusters at `x`
along `F : filter ι` if `map_cluster_pt x F f : cluster_pt x (map f F)`. In particular
the notion of cluster point of a sequence `u` is `map_cluster_pt x at_top u`.

For topological spaces `α` and `β`, a function `f : α → β` and a point `a : α`,
`continuous_at f a` means `f` is continuous at `a`, and global continuity is
`continuous f`. There is also a version of continuity `pcontinuous` for
partially defined functions.

## Notation

* `𝓝 x`: the filter `nhds x` of neighborhoods of a point `x`;
* `𝓟 s`: the principal filter of a set `s`;
* `𝓝[s] x`: the filter `nhds_within x s` of neighborhoods of a point `x` within a set `s`;
* `𝓝[≤] x`: the filter `nhds_within x (set.Iic x)` of left-neighborhoods of `x`;
* `𝓝[≥] x`: the filter `nhds_within x (set.Ici x)` of right-neighborhoods of `x`;
* `𝓝[<] x`: the filter `nhds_within x (set.Iio x)` of punctured left-neighborhoods of `x`;
* `𝓝[>] x`: the filter `nhds_within x (set.Ioi x)` of punctured right-neighborhoods of `x`;
* `𝓝[≠] x`: the filter `nhds_within x {x}ᶜ` of punctured neighborhoods of `x`.

## Implementation notes

Topology in mathlib heavily uses filters (even more than in Bourbaki). See explanations in
<https://leanprover-community.github.io/theories/topology.html>.

## References

*  [N. Bourbaki, *General Topology*][bourbaki1966]
*  [I. M. James, *Topologies and Uniformities*][james1999]

## Tags

topological space, interior, closure, frontier, neighborhood, continuity, continuous function
-/


noncomputable section

open Set Filter Classical

open Classical Filter

universe u v w

/-!
### Topological spaces
-/


#print TopologicalSpace /-
/-- A topology on `α`. -/
@[protect_proj]
structure TopologicalSpace (α : Type u) where
  IsOpen : Set α → Prop
  is_open_univ : IsOpen univ
  is_open_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  is_open_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)
#align topological_space TopologicalSpace
-/

attribute [class] TopologicalSpace

/- warning: topological_space.of_closed -> TopologicalSpace.ofClosed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (T : Set.{u1} (Set.{u1} α)), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) T) -> (forall (A : Set.{u1} (Set.{u1} α)), (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasSubset.{u1} (Set.{u1} α)) A T) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (Set.interₛ.{u1} α A) T)) -> (forall (A : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) A T) -> (forall (B : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) B T) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) A B) T))) -> (TopologicalSpace.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} (T : Set.{u1} (Set.{u1} α)), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) T) -> (forall (A : Set.{u1} (Set.{u1} α)), (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.instHasSubsetSet.{u1} (Set.{u1} α)) A T) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (Set.interₛ.{u1} α A) T)) -> (forall (A : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) A T) -> (forall (B : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) B T) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) A B) T))) -> (TopologicalSpace.{u1} α)
Case conversion may be inaccurate. Consider using '#align topological_space.of_closed TopologicalSpace.ofClosedₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (A «expr ⊆ » T) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (A B «expr ∈ » T) -/
/-- A constructor for topologies by specifying the closed sets,
and showing that they satisfy the appropriate conditions. -/
def TopologicalSpace.ofClosed {α : Type u} (T : Set (Set α)) (empty_mem : ∅ ∈ T)
    (sInter_mem : ∀ (A) (_ : A ⊆ T), ⋂₀ A ∈ T)
    (union_mem : ∀ (A) (_ : A ∈ T) (B) (_ : B ∈ T), A ∪ B ∈ T) : TopologicalSpace α
    where
  IsOpen X := Xᶜ ∈ T
  is_open_univ := by simp [empty_mem]
  is_open_inter s t hs ht := by simpa only [compl_inter] using union_mem (sᶜ) hs (tᶜ) ht
  is_open_sUnion s hs := by
    rw [Set.compl_unionₛ] <;>
      exact sInter_mem (compl '' s) fun z ⟨y, hy, hz⟩ => by simpa [hz.symm] using hs y hy
#align topological_space.of_closed TopologicalSpace.ofClosed

section TopologicalSpace

variable {α : Type u} {β : Type v} {ι : Sort w} {a : α} {s s₁ s₂ t : Set α} {p p₁ p₂ : α → Prop}

#print topologicalSpace_eq /-
@[ext]
theorem topologicalSpace_eq : ∀ {f g : TopologicalSpace α}, f.IsOpen = g.IsOpen → f = g
  | ⟨a, _, _, _⟩, ⟨b, _, _, _⟩, rfl => rfl
#align topological_space_eq topologicalSpace_eq
-/

section

variable [TopologicalSpace α]

#print IsOpen /-
/-- `is_open s` means that `s` is open in the ambient topological space on `α` -/
def IsOpen (s : Set α) : Prop :=
  TopologicalSpace.IsOpen ‹_› s
#align is_open IsOpen
-/

#print isOpen_univ /-
@[simp]
theorem isOpen_univ : IsOpen (univ : Set α) :=
  TopologicalSpace.isOpen_univ _
#align is_open_univ isOpen_univ
-/

/- warning: is_open.inter -> IsOpen.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} [_inst_1 : TopologicalSpace.{u1} α], (IsOpen.{u1} α _inst_1 s₁) -> (IsOpen.{u1} α _inst_1 s₂) -> (IsOpen.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂))
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} [_inst_1 : TopologicalSpace.{u1} α], (IsOpen.{u1} α _inst_1 s₁) -> (IsOpen.{u1} α _inst_1 s₂) -> (IsOpen.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s₂))
Case conversion may be inaccurate. Consider using '#align is_open.inter IsOpen.interₓ'. -/
theorem IsOpen.inter (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s₁ ∩ s₂) :=
  TopologicalSpace.isOpen_inter _ s₁ s₂ h₁ h₂
#align is_open.inter IsOpen.inter

#print isOpen_unionₛ /-
theorem isOpen_unionₛ {s : Set (Set α)} (h : ∀ t ∈ s, IsOpen t) : IsOpen (⋃₀ s) :=
  TopologicalSpace.isOpen_unionₛ _ s h
#align is_open_sUnion isOpen_unionₛ
-/

end

#print topologicalSpace_eq_iff /-
theorem topologicalSpace_eq_iff {t t' : TopologicalSpace α} :
    t = t' ↔ ∀ s, @IsOpen α t s ↔ @IsOpen α t' s :=
  ⟨fun h s => h ▸ Iff.rfl, fun h => by
    ext
    exact h _⟩
#align topological_space_eq_iff topologicalSpace_eq_iff
-/

#print isOpen_fold /-
theorem isOpen_fold {s : Set α} {t : TopologicalSpace α} : t.IsOpen s = @IsOpen α t s :=
  rfl
#align is_open_fold isOpen_fold
-/

variable [TopologicalSpace α]

#print isOpen_unionᵢ /-
theorem isOpen_unionᵢ {f : ι → Set α} (h : ∀ i, IsOpen (f i)) : IsOpen (⋃ i, f i) :=
  isOpen_unionₛ <| by rintro _ ⟨i, rfl⟩ <;> exact h i
#align is_open_Union isOpen_unionᵢ
-/

#print isOpen_bunionᵢ /-
theorem isOpen_bunionᵢ {s : Set β} {f : β → Set α} (h : ∀ i ∈ s, IsOpen (f i)) :
    IsOpen (⋃ i ∈ s, f i) :=
  isOpen_unionᵢ fun i => isOpen_unionᵢ fun hi => h i hi
#align is_open_bUnion isOpen_bunionᵢ
-/

/- warning: is_open.union -> IsOpen.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} [_inst_1 : TopologicalSpace.{u1} α], (IsOpen.{u1} α _inst_1 s₁) -> (IsOpen.{u1} α _inst_1 s₂) -> (IsOpen.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂))
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} [_inst_1 : TopologicalSpace.{u1} α], (IsOpen.{u1} α _inst_1 s₁) -> (IsOpen.{u1} α _inst_1 s₂) -> (IsOpen.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂))
Case conversion may be inaccurate. Consider using '#align is_open.union IsOpen.unionₓ'. -/
theorem IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s₁ ∪ s₂) := by
  rw [union_eq_Union] <;> exact isOpen_unionᵢ (Bool.forall_bool.2 ⟨h₂, h₁⟩)
#align is_open.union IsOpen.union

#print isOpen_empty /-
@[simp]
theorem isOpen_empty : IsOpen (∅ : Set α) := by
  rw [← sUnion_empty] <;> exact isOpen_unionₛ fun a => False.elim
#align is_open_empty isOpen_empty
-/

#print isOpen_interₛ /-
theorem isOpen_interₛ {s : Set (Set α)} (hs : s.Finite) : (∀ t ∈ s, IsOpen t) → IsOpen (⋂₀ s) :=
  Finite.induction_on hs (fun _ => by rw [sInter_empty] <;> exact isOpen_univ)
    fun a s has hs ih h => by
    rw [sInter_insert] <;>
      exact IsOpen.inter (h _ <| mem_insert _ _) (ih fun t => h t ∘ mem_insert_of_mem _)
#align is_open_sInter isOpen_interₛ
-/

#print isOpen_binterᵢ /-
theorem isOpen_binterᵢ {s : Set β} {f : β → Set α} (hs : s.Finite) :
    (∀ i ∈ s, IsOpen (f i)) → IsOpen (⋂ i ∈ s, f i) :=
  Finite.induction_on hs (fun _ => by rw [bInter_empty] <;> exact isOpen_univ)
    fun a s has hs ih h => by
    rw [bInter_insert] <;>
      exact IsOpen.inter (h a (mem_insert _ _)) (ih fun i hi => h i (mem_insert_of_mem _ hi))
#align is_open_bInter isOpen_binterᵢ
-/

/- warning: is_open_Inter -> isOpen_interᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Finite.{succ u2} β] {s : β -> (Set.{u1} α)}, (forall (i : β), IsOpen.{u1} α _inst_1 (s i)) -> (IsOpen.{u1} α _inst_1 (Set.interᵢ.{u1, succ u2} α β (fun (i : β) => s i)))
but is expected to have type
  forall {α : Type.{u1}} {β : Sort.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Finite.{u2} β] {s : β -> (Set.{u1} α)}, (forall (i : β), IsOpen.{u1} α _inst_1 (s i)) -> (IsOpen.{u1} α _inst_1 (Set.interᵢ.{u1, u2} α β (fun (i : β) => s i)))
Case conversion may be inaccurate. Consider using '#align is_open_Inter isOpen_interᵢₓ'. -/
theorem isOpen_interᵢ [Finite β] {s : β → Set α} (h : ∀ i, IsOpen (s i)) : IsOpen (⋂ i, s i) :=
  suffices IsOpen (⋂ (i : β) (hi : i ∈ @univ β), s i) by simpa
  isOpen_binterᵢ finite_univ fun i _ => h i
#align is_open_Inter isOpen_interᵢ

#print isOpen_interᵢ_prop /-
theorem isOpen_interᵢ_prop {p : Prop} {s : p → Set α} (h : ∀ h : p, IsOpen (s h)) :
    IsOpen (interᵢ s) := by by_cases p <;> simp [*]
#align is_open_Inter_prop isOpen_interᵢ_prop
-/

#print isOpen_binterᵢ_finset /-
theorem isOpen_binterᵢ_finset {s : Finset β} {f : β → Set α} (h : ∀ i ∈ s, IsOpen (f i)) :
    IsOpen (⋂ i ∈ s, f i) :=
  isOpen_binterᵢ (toFinite _) h
#align is_open_bInter_finset isOpen_binterᵢ_finset
-/

#print isOpen_const /-
theorem isOpen_const {p : Prop} : IsOpen { a : α | p } :=
  by_cases (fun this : p => by simp only [this] <;> exact isOpen_univ) fun this : ¬p => by
    simp only [this] <;> exact isOpen_empty
#align is_open_const isOpen_const
-/

#print IsOpen.and /-
theorem IsOpen.and : IsOpen { a | p₁ a } → IsOpen { a | p₂ a } → IsOpen { a | p₁ a ∧ p₂ a } :=
  IsOpen.inter
#align is_open.and IsOpen.and
-/

#print IsClosed /-
/-- A set is closed if its complement is open -/
class IsClosed (s : Set α) : Prop where
  is_open_compl : IsOpen (sᶜ)
#align is_closed IsClosed
-/

/- warning: is_open_compl_iff -> isOpen_compl_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Iff (IsOpen.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (IsClosed.{u1} α _inst_1 s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Iff (IsOpen.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (IsClosed.{u1} α _inst_1 s)
Case conversion may be inaccurate. Consider using '#align is_open_compl_iff isOpen_compl_iffₓ'. -/
@[simp]
theorem isOpen_compl_iff {s : Set α} : IsOpen (sᶜ) ↔ IsClosed s :=
  ⟨fun h => ⟨h⟩, fun h => h.is_open_compl⟩
#align is_open_compl_iff isOpen_compl_iff

#print isClosed_empty /-
@[simp]
theorem isClosed_empty : IsClosed (∅ : Set α) :=
  by
  rw [← isOpen_compl_iff, compl_empty]
  exact isOpen_univ
#align is_closed_empty isClosed_empty
-/

#print isClosed_univ /-
@[simp]
theorem isClosed_univ : IsClosed (univ : Set α) :=
  by
  rw [← isOpen_compl_iff, compl_univ]
  exact isOpen_empty
#align is_closed_univ isClosed_univ
-/

/- warning: is_closed.union -> IsClosed.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} [_inst_1 : TopologicalSpace.{u1} α], (IsClosed.{u1} α _inst_1 s₁) -> (IsClosed.{u1} α _inst_1 s₂) -> (IsClosed.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂))
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} [_inst_1 : TopologicalSpace.{u1} α], (IsClosed.{u1} α _inst_1 s₁) -> (IsClosed.{u1} α _inst_1 s₂) -> (IsClosed.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂))
Case conversion may be inaccurate. Consider using '#align is_closed.union IsClosed.unionₓ'. -/
theorem IsClosed.union : IsClosed s₁ → IsClosed s₂ → IsClosed (s₁ ∪ s₂) := fun h₁ h₂ =>
  by
  rw [← isOpen_compl_iff] at *
  rw [compl_union]
  exact IsOpen.inter h₁ h₂
#align is_closed.union IsClosed.union

#print isClosed_interₛ /-
theorem isClosed_interₛ {s : Set (Set α)} : (∀ t ∈ s, IsClosed t) → IsClosed (⋂₀ s) := by
  simpa only [← isOpen_compl_iff, compl_sInter, sUnion_image] using isOpen_bunionᵢ
#align is_closed_sInter isClosed_interₛ
-/

#print isClosed_interᵢ /-
theorem isClosed_interᵢ {f : ι → Set α} (h : ∀ i, IsClosed (f i)) : IsClosed (⋂ i, f i) :=
  isClosed_interₛ fun t ⟨i, (HEq : f i = t)⟩ => HEq ▸ h i
#align is_closed_Inter isClosed_interᵢ
-/

#print isClosed_binterᵢ /-
theorem isClosed_binterᵢ {s : Set β} {f : β → Set α} (h : ∀ i ∈ s, IsClosed (f i)) :
    IsClosed (⋂ i ∈ s, f i) :=
  isClosed_interᵢ fun i => isClosed_interᵢ <| h i
#align is_closed_bInter isClosed_binterᵢ
-/

/- warning: is_closed_compl_iff -> isClosed_compl_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Iff (IsClosed.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (IsOpen.{u1} α _inst_1 s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Iff (IsClosed.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (IsOpen.{u1} α _inst_1 s)
Case conversion may be inaccurate. Consider using '#align is_closed_compl_iff isClosed_compl_iffₓ'. -/
@[simp]
theorem isClosed_compl_iff {s : Set α} : IsClosed (sᶜ) ↔ IsOpen s := by
  rw [← isOpen_compl_iff, compl_compl]
#align is_closed_compl_iff isClosed_compl_iff

/- warning: is_open.is_closed_compl -> IsOpen.isClosed_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (IsClosed.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (IsClosed.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))
Case conversion may be inaccurate. Consider using '#align is_open.is_closed_compl IsOpen.isClosed_complₓ'. -/
theorem IsOpen.isClosed_compl {s : Set α} (hs : IsOpen s) : IsClosed (sᶜ) :=
  isClosed_compl_iff.2 hs
#align is_open.is_closed_compl IsOpen.isClosed_compl

/- warning: is_open.sdiff -> IsOpen.sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (IsClosed.{u1} α _inst_1 t) -> (IsOpen.{u1} α _inst_1 (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (IsClosed.{u1} α _inst_1 t) -> (IsOpen.{u1} α _inst_1 (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align is_open.sdiff IsOpen.sdiffₓ'. -/
theorem IsOpen.sdiff {s t : Set α} (h₁ : IsOpen s) (h₂ : IsClosed t) : IsOpen (s \ t) :=
  IsOpen.inter h₁ <| isOpen_compl_iff.mpr h₂
#align is_open.sdiff IsOpen.sdiff

/- warning: is_closed.inter -> IsClosed.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} [_inst_1 : TopologicalSpace.{u1} α], (IsClosed.{u1} α _inst_1 s₁) -> (IsClosed.{u1} α _inst_1 s₂) -> (IsClosed.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂))
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} [_inst_1 : TopologicalSpace.{u1} α], (IsClosed.{u1} α _inst_1 s₁) -> (IsClosed.{u1} α _inst_1 s₂) -> (IsClosed.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s₂))
Case conversion may be inaccurate. Consider using '#align is_closed.inter IsClosed.interₓ'. -/
theorem IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : IsClosed (s₁ ∩ s₂) :=
  by
  rw [← isOpen_compl_iff] at *
  rw [compl_inter]
  exact IsOpen.union h₁ h₂
#align is_closed.inter IsClosed.inter

/- warning: is_closed.sdiff -> IsClosed.sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsClosed.{u1} α _inst_1 s) -> (IsOpen.{u1} α _inst_1 t) -> (IsClosed.{u1} α _inst_1 (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsClosed.{u1} α _inst_1 s) -> (IsOpen.{u1} α _inst_1 t) -> (IsClosed.{u1} α _inst_1 (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align is_closed.sdiff IsClosed.sdiffₓ'. -/
theorem IsClosed.sdiff {s t : Set α} (h₁ : IsClosed s) (h₂ : IsOpen t) : IsClosed (s \ t) :=
  IsClosed.inter h₁ (isClosed_compl_iff.mpr h₂)
#align is_closed.sdiff IsClosed.sdiff

#print isClosed_bunionᵢ /-
theorem isClosed_bunionᵢ {s : Set β} {f : β → Set α} (hs : s.Finite) :
    (∀ i ∈ s, IsClosed (f i)) → IsClosed (⋃ i ∈ s, f i) :=
  Finite.induction_on hs (fun _ => by rw [bUnion_empty] <;> exact isClosed_empty)
    fun a s has hs ih h => by
    rw [bUnion_insert] <;>
      exact IsClosed.union (h a (mem_insert _ _)) (ih fun i hi => h i (mem_insert_of_mem _ hi))
#align is_closed_bUnion isClosed_bunionᵢ
-/

/- warning: is_closed_Union -> isClosed_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Finite.{succ u2} β] {s : β -> (Set.{u1} α)}, (forall (i : β), IsClosed.{u1} α _inst_1 (s i)) -> (IsClosed.{u1} α _inst_1 (Set.unionᵢ.{u1, succ u2} α β (fun (i : β) => s i)))
but is expected to have type
  forall {α : Type.{u1}} {β : Sort.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Finite.{u2} β] {s : β -> (Set.{u1} α)}, (forall (i : β), IsClosed.{u1} α _inst_1 (s i)) -> (IsClosed.{u1} α _inst_1 (Set.unionᵢ.{u1, u2} α β (fun (i : β) => s i)))
Case conversion may be inaccurate. Consider using '#align is_closed_Union isClosed_unionᵢₓ'. -/
theorem isClosed_unionᵢ [Finite β] {s : β → Set α} (h : ∀ i, IsClosed (s i)) :
    IsClosed (⋃ i, s i) :=
  suffices IsClosed (⋃ (i : β) (hi : i ∈ @univ β), s i) by convert this <;> simp [Set.ext_iff]
  isClosed_bunionᵢ finite_univ fun i _ => h i
#align is_closed_Union isClosed_unionᵢ

#print isClosed_unionᵢ_prop /-
theorem isClosed_unionᵢ_prop {p : Prop} {s : p → Set α} (h : ∀ h : p, IsClosed (s h)) :
    IsClosed (unionᵢ s) := by by_cases p <;> simp [*]
#align is_closed_Union_prop isClosed_unionᵢ_prop
-/

#print isClosed_imp /-
theorem isClosed_imp {p q : α → Prop} (hp : IsOpen { x | p x }) (hq : IsClosed { x | q x }) :
    IsClosed { x | p x → q x } :=
  by
  have : { x | p x → q x } = { x | p x }ᶜ ∪ { x | q x } := Set.ext fun x => imp_iff_not_or
  rw [this] <;> exact IsClosed.union (is_closed_compl_iff.mpr hp) hq
#align is_closed_imp isClosed_imp
-/

#print IsClosed.not /-
theorem IsClosed.not : IsClosed { a | p a } → IsOpen { a | ¬p a } :=
  isOpen_compl_iff.mpr
#align is_closed.not IsClosed.not
-/

/-!
### Interior of a set
-/


#print interior /-
/-- The interior of a set `s` is the largest open subset of `s`. -/
def interior (s : Set α) : Set α :=
  ⋃₀ { t | IsOpen t ∧ t ⊆ s }
#align interior interior
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (t «expr ⊆ » s) -/
theorem mem_interior {s : Set α} {x : α} :
    x ∈ interior s ↔ ∃ (t : _)(_ : t ⊆ s), IsOpen t ∧ x ∈ t := by
  simp only [interior, mem_sUnion, mem_set_of_eq, exists_prop, and_assoc', and_left_comm]
#align mem_interior mem_interiorₓ

#print isOpen_interior /-
@[simp]
theorem isOpen_interior {s : Set α} : IsOpen (interior s) :=
  isOpen_unionₛ fun t ⟨h₁, h₂⟩ => h₁
#align is_open_interior isOpen_interior
-/

#print interior_subset /-
theorem interior_subset {s : Set α} : interior s ⊆ s :=
  sUnion_subset fun t ⟨h₁, h₂⟩ => h₂
#align interior_subset interior_subset
-/

#print interior_maximal /-
theorem interior_maximal {s t : Set α} (h₁ : t ⊆ s) (h₂ : IsOpen t) : t ⊆ interior s :=
  subset_unionₛ_of_mem ⟨h₂, h₁⟩
#align interior_maximal interior_maximal
-/

#print IsOpen.interior_eq /-
theorem IsOpen.interior_eq {s : Set α} (h : IsOpen s) : interior s = s :=
  Subset.antisymm interior_subset (interior_maximal (Subset.refl s) h)
#align is_open.interior_eq IsOpen.interior_eq
-/

#print interior_eq_iff_isOpen /-
theorem interior_eq_iff_isOpen {s : Set α} : interior s = s ↔ IsOpen s :=
  ⟨fun h => h ▸ isOpen_interior, IsOpen.interior_eq⟩
#align interior_eq_iff_is_open interior_eq_iff_isOpen
-/

#print subset_interior_iff_isOpen /-
theorem subset_interior_iff_isOpen {s : Set α} : s ⊆ interior s ↔ IsOpen s := by
  simp only [interior_eq_iff_is_open.symm, subset.antisymm_iff, interior_subset, true_and_iff]
#align subset_interior_iff_is_open subset_interior_iff_isOpen
-/

#print IsOpen.subset_interior_iff /-
theorem IsOpen.subset_interior_iff {s t : Set α} (h₁ : IsOpen s) : s ⊆ interior t ↔ s ⊆ t :=
  ⟨fun h => Subset.trans h interior_subset, fun h₂ => interior_maximal h₂ h₁⟩
#align is_open.subset_interior_iff IsOpen.subset_interior_iff
-/

#print subset_interior_iff /-
theorem subset_interior_iff {s t : Set α} : t ⊆ interior s ↔ ∃ U, IsOpen U ∧ t ⊆ U ∧ U ⊆ s :=
  ⟨fun h => ⟨interior s, isOpen_interior, h, interior_subset⟩, fun ⟨U, hU, htU, hUs⟩ =>
    htU.trans (interior_maximal hUs hU)⟩
#align subset_interior_iff subset_interior_iff
-/

#print interior_mono /-
@[mono]
theorem interior_mono {s t : Set α} (h : s ⊆ t) : interior s ⊆ interior t :=
  interior_maximal (Subset.trans interior_subset h) isOpen_interior
#align interior_mono interior_mono
-/

#print interior_empty /-
@[simp]
theorem interior_empty : interior (∅ : Set α) = ∅ :=
  isOpen_empty.interior_eq
#align interior_empty interior_empty
-/

#print interior_univ /-
@[simp]
theorem interior_univ : interior (univ : Set α) = univ :=
  isOpen_univ.interior_eq
#align interior_univ interior_univ
-/

#print interior_eq_univ /-
@[simp]
theorem interior_eq_univ {s : Set α} : interior s = univ ↔ s = univ :=
  ⟨fun h => univ_subset_iff.mp <| h.symm.trans_le interior_subset, fun h => h.symm ▸ interior_univ⟩
#align interior_eq_univ interior_eq_univ
-/

#print interior_interior /-
@[simp]
theorem interior_interior {s : Set α} : interior (interior s) = interior s :=
  isOpen_interior.interior_eq
#align interior_interior interior_interior
-/

/- warning: interior_inter -> interior_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (interior.{u1} α _inst_1 s) (interior.{u1} α _inst_1 t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (interior.{u1} α _inst_1 s) (interior.{u1} α _inst_1 t))
Case conversion may be inaccurate. Consider using '#align interior_inter interior_interₓ'. -/
@[simp]
theorem interior_inter {s t : Set α} : interior (s ∩ t) = interior s ∩ interior t :=
  Subset.antisymm
    (subset_inter (interior_mono <| inter_subset_left s t)
      (interior_mono <| inter_subset_right s t))
    (interior_maximal (inter_subset_inter interior_subset interior_subset) <|
      IsOpen.inter isOpen_interior isOpen_interior)
#align interior_inter interior_inter

/- warning: finset.interior_Inter -> Finset.interior_interᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Type.{u2}} (s : Finset.{u2} ι) (f : ι -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) => f i)))) (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) => interior.{u1} α _inst_1 (f i))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {ι : Type.{u1}} (s : Finset.{u1} ι) (f : ι -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (interior.{u2} α _inst_1 (Set.interᵢ.{u2, succ u1} α ι (fun (i : ι) => Set.interᵢ.{u2, 0} α (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) (fun (H : Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) => f i)))) (Set.interᵢ.{u2, succ u1} α ι (fun (i : ι) => Set.interᵢ.{u2, 0} α (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) (fun (H : Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) => interior.{u2} α _inst_1 (f i))))
Case conversion may be inaccurate. Consider using '#align finset.interior_Inter Finset.interior_interᵢₓ'. -/
@[simp]
theorem Finset.interior_interᵢ {ι : Type _} (s : Finset ι) (f : ι → Set α) :
    interior (⋂ i ∈ s, f i) = ⋂ i ∈ s, interior (f i) := by
  classical
    refine' s.induction_on (by simp) _
    intro i s h₁ h₂
    simp [h₂]
#align finset.interior_Inter Finset.interior_interᵢ

/- warning: interior_Inter -> interior_interᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Type.{u2}} [_inst_2 : Finite.{succ u2} ι] (f : ι -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => f i))) (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => interior.{u1} α _inst_1 (f i)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {ι : Type.{u1}} [_inst_2 : Finite.{succ u1} ι] (f : ι -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (interior.{u2} α _inst_1 (Set.interᵢ.{u2, succ u1} α ι (fun (i : ι) => f i))) (Set.interᵢ.{u2, succ u1} α ι (fun (i : ι) => interior.{u2} α _inst_1 (f i)))
Case conversion may be inaccurate. Consider using '#align interior_Inter interior_interᵢₓ'. -/
@[simp]
theorem interior_interᵢ {ι : Type _} [Finite ι] (f : ι → Set α) :
    interior (⋂ i, f i) = ⋂ i, interior (f i) :=
  by
  cases nonempty_fintype ι
  convert finset.univ.interior_Inter f <;> simp
#align interior_Inter interior_interᵢ

/- warning: interior_union_is_closed_of_interior_empty -> interior_union_isClosed_of_interior_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsClosed.{u1} α _inst_1 s) -> (Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) -> (Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (interior.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsClosed.{u1} α _inst_1 s) -> (Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) -> (Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (interior.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align interior_union_is_closed_of_interior_empty interior_union_isClosed_of_interior_emptyₓ'. -/
theorem interior_union_isClosed_of_interior_empty {s t : Set α} (h₁ : IsClosed s)
    (h₂ : interior t = ∅) : interior (s ∪ t) = interior s :=
  have : interior (s ∪ t) ⊆ s := fun x ⟨u, ⟨(hu₁ : IsOpen u), (hu₂ : u ⊆ s ∪ t)⟩, (hx₁ : x ∈ u)⟩ =>
    by_contradiction fun hx₂ : x ∉ s =>
      have : u \ s ⊆ t := fun x ⟨h₁, h₂⟩ => Or.resolve_left (hu₂ h₁) h₂
      have : u \ s ⊆ interior t := by rwa [(IsOpen.sdiff hu₁ h₁).subset_interior_iff]
      have : u \ s ⊆ ∅ := by rwa [h₂] at this
      this ⟨hx₁, hx₂⟩
  Subset.antisymm (interior_maximal this isOpen_interior) (interior_mono <| subset_union_left _ _)
#align interior_union_is_closed_of_interior_empty interior_union_isClosed_of_interior_empty

/- warning: is_open_iff_forall_mem_open -> isOpen_iff_forall_mem_open is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : TopologicalSpace.{u1} α], Iff (IsOpen.{u1} α _inst_1 s) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) => And (IsOpen.{u1} α _inst_1 t) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t)))))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : TopologicalSpace.{u1} α], Iff (IsOpen.{u1} α _inst_1 s) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s) (And (IsOpen.{u1} α _inst_1 t) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t)))))
Case conversion may be inaccurate. Consider using '#align is_open_iff_forall_mem_open isOpen_iff_forall_mem_openₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (t «expr ⊆ » s) -/
theorem isOpen_iff_forall_mem_open : IsOpen s ↔ ∀ x ∈ s, ∃ (t : _)(_ : t ⊆ s), IsOpen t ∧ x ∈ t :=
  by rw [← subset_interior_iff_isOpen] <;> simp only [subset_def, mem_interior]
#align is_open_iff_forall_mem_open isOpen_iff_forall_mem_open

#print interior_interᵢ_subset /-
theorem interior_interᵢ_subset (s : ι → Set α) : interior (⋂ i, s i) ⊆ ⋂ i, interior (s i) :=
  subset_Inter fun i => interior_mono <| interᵢ_subset _ _
#align interior_Inter_subset interior_interᵢ_subset
-/

/- warning: interior_Inter₂_subset -> interior_Inter₂_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : TopologicalSpace.{u1} α] (p : ι -> Sort.{u3}) (s : forall (i : ι), (p i) -> (Set.{u1} α)), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (interior.{u1} α _inst_1 (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (p i) (fun (j : p i) => s i j)))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (p i) (fun (j : p i) => interior.{u1} α _inst_1 (s i j))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : TopologicalSpace.{u2} α] (p : ι -> Sort.{u1}) (s : forall (i : ι), (p i) -> (Set.{u2} α)), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (interior.{u2} α _inst_1 (Set.interᵢ.{u2, u3} α ι (fun (i : ι) => Set.interᵢ.{u2, u1} α (p i) (fun (j : p i) => s i j)))) (Set.interᵢ.{u2, u3} α ι (fun (i : ι) => Set.interᵢ.{u2, u1} α (p i) (fun (j : p i) => interior.{u2} α _inst_1 (s i j))))
Case conversion may be inaccurate. Consider using '#align interior_Inter₂_subset interior_Inter₂_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem interior_Inter₂_subset (p : ι → Sort _) (s : ∀ i, p i → Set α) :
    interior (⋂ (i) (j), s i j) ⊆ ⋂ (i) (j), interior (s i j) :=
  (interior_interᵢ_subset _).trans <| Inter_mono fun i => interior_interᵢ_subset _
#align interior_Inter₂_subset interior_Inter₂_subset

#print interior_interₛ_subset /-
theorem interior_interₛ_subset (S : Set (Set α)) : interior (⋂₀ S) ⊆ ⋂ s ∈ S, interior s :=
  calc
    interior (⋂₀ S) = interior (⋂ s ∈ S, s) := by rw [sInter_eq_bInter]
    _ ⊆ ⋂ s ∈ S, interior s := interior_Inter₂_subset _ _
    
#align interior_sInter_subset interior_interₛ_subset
-/

/-!
### Closure of a set
-/


#print closure /-
/-- The closure of `s` is the smallest closed set containing `s`. -/
def closure (s : Set α) : Set α :=
  ⋂₀ { t | IsClosed t ∧ s ⊆ t }
#align closure closure
-/

#print isClosed_closure /-
@[simp]
theorem isClosed_closure {s : Set α} : IsClosed (closure s) :=
  isClosed_interₛ fun t ⟨h₁, h₂⟩ => h₁
#align is_closed_closure isClosed_closure
-/

#print subset_closure /-
theorem subset_closure {s : Set α} : s ⊆ closure s :=
  subset_sInter fun t ⟨h₁, h₂⟩ => h₂
#align subset_closure subset_closure
-/

#print not_mem_of_not_mem_closure /-
theorem not_mem_of_not_mem_closure {s : Set α} {P : α} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)
#align not_mem_of_not_mem_closure not_mem_of_not_mem_closure
-/

#print closure_minimal /-
theorem closure_minimal {s t : Set α} (h₁ : s ⊆ t) (h₂ : IsClosed t) : closure s ⊆ t :=
  interₛ_subset_of_mem ⟨h₂, h₁⟩
#align closure_minimal closure_minimal
-/

/- warning: disjoint.closure_left -> Disjoint.closure_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (IsOpen.{u1} α _inst_1 t) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (closure.{u1} α _inst_1 s) t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t) -> (IsOpen.{u1} α _inst_1 t) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (closure.{u1} α _inst_1 s) t)
Case conversion may be inaccurate. Consider using '#align disjoint.closure_left Disjoint.closure_leftₓ'. -/
theorem Disjoint.closure_left {s t : Set α} (hd : Disjoint s t) (ht : IsOpen t) :
    Disjoint (closure s) t :=
  disjoint_compl_left.mono_left <| closure_minimal hd.subset_compl_right ht.is_closed_compl
#align disjoint.closure_left Disjoint.closure_left

/- warning: disjoint.closure_right -> Disjoint.closure_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (IsOpen.{u1} α _inst_1 s) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (closure.{u1} α _inst_1 t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t) -> (IsOpen.{u1} α _inst_1 s) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s (closure.{u1} α _inst_1 t))
Case conversion may be inaccurate. Consider using '#align disjoint.closure_right Disjoint.closure_rightₓ'. -/
theorem Disjoint.closure_right {s t : Set α} (hd : Disjoint s t) (hs : IsOpen s) :
    Disjoint s (closure t) :=
  (hd.symm.closure_left hs).symm
#align disjoint.closure_right Disjoint.closure_right

#print IsClosed.closure_eq /-
theorem IsClosed.closure_eq {s : Set α} (h : IsClosed s) : closure s = s :=
  Subset.antisymm (closure_minimal (Subset.refl s) h) subset_closure
#align is_closed.closure_eq IsClosed.closure_eq
-/

#print IsClosed.closure_subset /-
theorem IsClosed.closure_subset {s : Set α} (hs : IsClosed s) : closure s ⊆ s :=
  closure_minimal (Subset.refl _) hs
#align is_closed.closure_subset IsClosed.closure_subset
-/

#print IsClosed.closure_subset_iff /-
theorem IsClosed.closure_subset_iff {s t : Set α} (h₁ : IsClosed t) : closure s ⊆ t ↔ s ⊆ t :=
  ⟨Subset.trans subset_closure, fun h => closure_minimal h h₁⟩
#align is_closed.closure_subset_iff IsClosed.closure_subset_iff
-/

#print IsClosed.mem_iff_closure_subset /-
theorem IsClosed.mem_iff_closure_subset {s : Set α} (hs : IsClosed s) {x : α} :
    x ∈ s ↔ closure ({x} : Set α) ⊆ s :=
  (hs.closure_subset_iff.trans Set.singleton_subset_iff).symm
#align is_closed.mem_iff_closure_subset IsClosed.mem_iff_closure_subset
-/

#print closure_mono /-
@[mono]
theorem closure_mono {s t : Set α} (h : s ⊆ t) : closure s ⊆ closure t :=
  closure_minimal (Subset.trans h subset_closure) isClosed_closure
#align closure_mono closure_mono
-/

/- warning: monotone_closure -> monotone_closure is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_2 : TopologicalSpace.{u1} α], Monotone.{u1, u1} (Set.{u1} α) (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (closure.{u1} α _inst_2)
but is expected to have type
  forall (α : Type.{u1}) [_inst_2 : TopologicalSpace.{u1} α], Monotone.{u1, u1} (Set.{u1} α) (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (closure.{u1} α _inst_2)
Case conversion may be inaccurate. Consider using '#align monotone_closure monotone_closureₓ'. -/
theorem monotone_closure (α : Type _) [TopologicalSpace α] : Monotone (@closure α _) := fun _ _ =>
  closure_mono
#align monotone_closure monotone_closure

/- warning: diff_subset_closure_iff -> diff_subset_closure_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) (closure.{u1} α _inst_1 t)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (closure.{u1} α _inst_1 t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) (closure.{u1} α _inst_1 t)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (closure.{u1} α _inst_1 t))
Case conversion may be inaccurate. Consider using '#align diff_subset_closure_iff diff_subset_closure_iffₓ'. -/
theorem diff_subset_closure_iff {s t : Set α} : s \ t ⊆ closure t ↔ s ⊆ closure t := by
  rw [diff_subset_iff, union_eq_self_of_subset_left subset_closure]
#align diff_subset_closure_iff diff_subset_closure_iff

/- warning: closure_inter_subset_inter_closure -> closure_inter_subset_inter_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (closure.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (closure.{u1} α _inst_1 s) (closure.{u1} α _inst_1 t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (closure.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (closure.{u1} α _inst_1 s) (closure.{u1} α _inst_1 t))
Case conversion may be inaccurate. Consider using '#align closure_inter_subset_inter_closure closure_inter_subset_inter_closureₓ'. -/
theorem closure_inter_subset_inter_closure (s t : Set α) :
    closure (s ∩ t) ⊆ closure s ∩ closure t :=
  (monotone_closure α).map_inf_le s t
#align closure_inter_subset_inter_closure closure_inter_subset_inter_closure

#print isClosed_of_closure_subset /-
theorem isClosed_of_closure_subset {s : Set α} (h : closure s ⊆ s) : IsClosed s := by
  rw [subset.antisymm subset_closure h] <;> exact isClosed_closure
#align is_closed_of_closure_subset isClosed_of_closure_subset
-/

#print closure_eq_iff_isClosed /-
theorem closure_eq_iff_isClosed {s : Set α} : closure s = s ↔ IsClosed s :=
  ⟨fun h => h ▸ isClosed_closure, IsClosed.closure_eq⟩
#align closure_eq_iff_is_closed closure_eq_iff_isClosed
-/

#print closure_subset_iff_isClosed /-
theorem closure_subset_iff_isClosed {s : Set α} : closure s ⊆ s ↔ IsClosed s :=
  ⟨isClosed_of_closure_subset, IsClosed.closure_subset⟩
#align closure_subset_iff_is_closed closure_subset_iff_isClosed
-/

#print closure_empty /-
@[simp]
theorem closure_empty : closure (∅ : Set α) = ∅ :=
  isClosed_empty.closure_eq
#align closure_empty closure_empty
-/

#print closure_empty_iff /-
@[simp]
theorem closure_empty_iff (s : Set α) : closure s = ∅ ↔ s = ∅ :=
  ⟨subset_eq_empty subset_closure, fun h => h.symm ▸ closure_empty⟩
#align closure_empty_iff closure_empty_iff
-/

#print closure_nonempty_iff /-
@[simp]
theorem closure_nonempty_iff {s : Set α} : (closure s).Nonempty ↔ s.Nonempty := by
  simp only [nonempty_iff_ne_empty, Ne.def, closure_empty_iff]
#align closure_nonempty_iff closure_nonempty_iff
-/

alias closure_nonempty_iff ↔ Set.Nonempty.of_closure Set.Nonempty.closure
#align set.nonempty.of_closure Set.Nonempty.of_closure
#align set.nonempty.closure Set.Nonempty.closure

#print closure_univ /-
@[simp]
theorem closure_univ : closure (univ : Set α) = univ :=
  isClosed_univ.closure_eq
#align closure_univ closure_univ
-/

#print closure_closure /-
@[simp]
theorem closure_closure {s : Set α} : closure (closure s) = closure s :=
  isClosed_closure.closure_eq
#align closure_closure closure_closure
-/

/- warning: closure_union -> closure_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (closure.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (closure.{u1} α _inst_1 s) (closure.{u1} α _inst_1 t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (closure.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (closure.{u1} α _inst_1 s) (closure.{u1} α _inst_1 t))
Case conversion may be inaccurate. Consider using '#align closure_union closure_unionₓ'. -/
@[simp]
theorem closure_union {s t : Set α} : closure (s ∪ t) = closure s ∪ closure t :=
  Subset.antisymm
    (closure_minimal (union_subset_union subset_closure subset_closure) <|
      IsClosed.union isClosed_closure isClosed_closure)
    ((monotone_closure α).le_map_sup s t)
#align closure_union closure_union

/- warning: finset.closure_bUnion -> Finset.closure_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Type.{u2}} (s : Finset.{u2} ι) (f : ι -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (closure.{u1} α _inst_1 (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) => f i)))) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) => closure.{u1} α _inst_1 (f i))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {ι : Type.{u1}} (s : Finset.{u1} ι) (f : ι -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (closure.{u2} α _inst_1 (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) (fun (H : Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) => f i)))) (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) (fun (H : Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) => closure.{u2} α _inst_1 (f i))))
Case conversion may be inaccurate. Consider using '#align finset.closure_bUnion Finset.closure_bunionᵢₓ'. -/
@[simp]
theorem Finset.closure_bunionᵢ {ι : Type _} (s : Finset ι) (f : ι → Set α) :
    closure (⋃ i ∈ s, f i) = ⋃ i ∈ s, closure (f i) := by
  classical
    refine' s.induction_on (by simp) _
    intro i s h₁ h₂
    simp [h₂]
#align finset.closure_bUnion Finset.closure_bunionᵢ

/- warning: closure_Union -> closure_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Type.{u2}} [_inst_2 : Finite.{succ u2} ι] (f : ι -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (closure.{u1} α _inst_1 (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => f i))) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => closure.{u1} α _inst_1 (f i)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {ι : Type.{u1}} [_inst_2 : Finite.{succ u1} ι] (f : ι -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (closure.{u2} α _inst_1 (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => f i))) (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => closure.{u2} α _inst_1 (f i)))
Case conversion may be inaccurate. Consider using '#align closure_Union closure_unionᵢₓ'. -/
@[simp]
theorem closure_unionᵢ {ι : Type _} [Finite ι] (f : ι → Set α) :
    closure (⋃ i, f i) = ⋃ i, closure (f i) :=
  by
  cases nonempty_fintype ι
  convert finset.univ.closure_bUnion f <;> simp
#align closure_Union closure_unionᵢ

#print interior_subset_closure /-
theorem interior_subset_closure {s : Set α} : interior s ⊆ closure s :=
  Subset.trans interior_subset subset_closure
#align interior_subset_closure interior_subset_closure
-/

/- warning: closure_eq_compl_interior_compl -> closure_eq_compl_interior_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (closure.{u1} α _inst_1 s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (interior.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (closure.{u1} α _inst_1 s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (interior.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)))
Case conversion may be inaccurate. Consider using '#align closure_eq_compl_interior_compl closure_eq_compl_interior_complₓ'. -/
theorem closure_eq_compl_interior_compl {s : Set α} : closure s = interior (sᶜ)ᶜ :=
  by
  rw [interior, closure, compl_sUnion, compl_image_set_of]
  simp only [compl_subset_compl, isOpen_compl_iff]
#align closure_eq_compl_interior_compl closure_eq_compl_interior_compl

/- warning: interior_compl -> interior_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (closure.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (closure.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align interior_compl interior_complₓ'. -/
@[simp]
theorem interior_compl {s : Set α} : interior (sᶜ) = closure sᶜ := by
  simp [closure_eq_compl_interior_compl]
#align interior_compl interior_compl

/- warning: closure_compl -> closure_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (closure.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (interior.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (closure.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (interior.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align closure_compl closure_complₓ'. -/
@[simp]
theorem closure_compl {s : Set α} : closure (sᶜ) = interior sᶜ := by
  simp [closure_eq_compl_interior_compl]
#align closure_compl closure_compl

/- warning: mem_closure_iff -> mem_closure_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {a : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (closure.{u1} α _inst_1 s)) (forall (o : Set.{u1} α), (IsOpen.{u1} α _inst_1 o) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a o) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) o s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {a : α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (closure.{u1} α _inst_1 s)) (forall (o : Set.{u1} α), (IsOpen.{u1} α _inst_1 o) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a o) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) o s)))
Case conversion may be inaccurate. Consider using '#align mem_closure_iff mem_closure_iffₓ'. -/
theorem mem_closure_iff {s : Set α} {a : α} :
    a ∈ closure s ↔ ∀ o, IsOpen o → a ∈ o → (o ∩ s).Nonempty :=
  ⟨fun h o oo ao =>
    by_contradiction fun os =>
      have : s ⊆ oᶜ := fun x xs xo => os ⟨x, xo, xs⟩
      closure_minimal this (isClosed_compl_iff.2 oo) h ao,
    fun H c ⟨h₁, h₂⟩ =>
    by_contradiction fun nc =>
      let ⟨x, hc, hs⟩ := H _ h₁.is_open_compl nc
      hc (h₂ hs)⟩
#align mem_closure_iff mem_closure_iff

/- warning: closure_inter_open_nonempty_iff -> closure_inter_open_nonempty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 t) -> (Iff (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (closure.{u1} α _inst_1 s) t)) (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 t) -> (Iff (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (closure.{u1} α _inst_1 s) t)) (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)))
Case conversion may be inaccurate. Consider using '#align closure_inter_open_nonempty_iff closure_inter_open_nonempty_iffₓ'. -/
theorem closure_inter_open_nonempty_iff {s t : Set α} (h : IsOpen t) :
    (closure s ∩ t).Nonempty ↔ (s ∩ t).Nonempty :=
  ⟨fun ⟨x, hxcs, hxt⟩ => inter_comm t s ▸ mem_closure_iff.1 hxcs t h hxt, fun h =>
    h.mono <| inf_le_inf_right t subset_closure⟩
#align closure_inter_open_nonempty_iff closure_inter_open_nonempty_iff

/- warning: filter.le_lift'_closure -> Filter.le_lift'_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (l : Filter.{u1} α), LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) l (Filter.lift'.{u1, u1} α α l (closure.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (l : Filter.{u1} α), LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) l (Filter.lift'.{u1, u1} α α l (closure.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align filter.le_lift'_closure Filter.le_lift'_closureₓ'. -/
theorem Filter.le_lift'_closure (l : Filter α) : l ≤ l.lift' closure :=
  le_lift'.2 fun s hs => mem_of_superset hs subset_closure
#align filter.le_lift'_closure Filter.le_lift'_closure

#print Filter.HasBasis.lift'_closure /-
theorem Filter.HasBasis.lift'_closure {l : Filter α} {p : ι → Prop} {s : ι → Set α}
    (h : l.HasBasis p s) : (l.lift' closure).HasBasis p fun i => closure (s i) :=
  h.lift' (monotone_closure α)
#align filter.has_basis.lift'_closure Filter.HasBasis.lift'_closure
-/

#print Filter.HasBasis.lift'_closure_eq_self /-
theorem Filter.HasBasis.lift'_closure_eq_self {l : Filter α} {p : ι → Prop} {s : ι → Set α}
    (h : l.HasBasis p s) (hc : ∀ i, p i → IsClosed (s i)) : l.lift' closure = l :=
  le_antisymm (h.ge_iff.2 fun i hi => (hc i hi).closure_eq ▸ mem_lift' (h.mem_of_mem hi))
    l.le_lift'_closure
#align filter.has_basis.lift'_closure_eq_self Filter.HasBasis.lift'_closure_eq_self
-/

/- warning: filter.lift'_closure_eq_bot -> Filter.lift'_closure_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {l : Filter.{u1} α}, Iff (Eq.{succ u1} (Filter.{u1} α) (Filter.lift'.{u1, u1} α α l (closure.{u1} α _inst_1)) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) (Eq.{succ u1} (Filter.{u1} α) l (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {l : Filter.{u1} α}, Iff (Eq.{succ u1} (Filter.{u1} α) (Filter.lift'.{u1, u1} α α l (closure.{u1} α _inst_1)) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) (Eq.{succ u1} (Filter.{u1} α) l (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))
Case conversion may be inaccurate. Consider using '#align filter.lift'_closure_eq_bot Filter.lift'_closure_eq_botₓ'. -/
@[simp]
theorem Filter.lift'_closure_eq_bot {l : Filter α} : l.lift' closure = ⊥ ↔ l = ⊥ :=
  ⟨fun h => bot_unique <| h ▸ l.le_lift'_closure, fun h =>
    h.symm ▸ by rw [lift'_bot (monotone_closure _), closure_empty, principal_empty]⟩
#align filter.lift'_closure_eq_bot Filter.lift'_closure_eq_bot

#print Dense /-
/-- A set is dense in a topological space if every point belongs to its closure. -/
def Dense (s : Set α) : Prop :=
  ∀ x, x ∈ closure s
#align dense Dense
-/

#print dense_iff_closure_eq /-
theorem dense_iff_closure_eq {s : Set α} : Dense s ↔ closure s = univ :=
  eq_univ_iff_forall.symm
#align dense_iff_closure_eq dense_iff_closure_eq
-/

#print Dense.closure_eq /-
theorem Dense.closure_eq {s : Set α} (h : Dense s) : closure s = univ :=
  dense_iff_closure_eq.mp h
#align dense.closure_eq Dense.closure_eq
-/

/- warning: interior_eq_empty_iff_dense_compl -> interior_eq_empty_iff_dense_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Dense.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Dense.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))
Case conversion may be inaccurate. Consider using '#align interior_eq_empty_iff_dense_compl interior_eq_empty_iff_dense_complₓ'. -/
theorem interior_eq_empty_iff_dense_compl {s : Set α} : interior s = ∅ ↔ Dense (sᶜ) := by
  rw [dense_iff_closure_eq, closure_compl, compl_univ_iff]
#align interior_eq_empty_iff_dense_compl interior_eq_empty_iff_dense_compl

/- warning: dense.interior_compl -> Dense.interior_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, (Dense.{u1} α _inst_1 s) -> (Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, (Dense.{u1} α _inst_1 s) -> (Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align dense.interior_compl Dense.interior_complₓ'. -/
theorem Dense.interior_compl {s : Set α} (h : Dense s) : interior (sᶜ) = ∅ :=
  interior_eq_empty_iff_dense_compl.2 <| by rwa [compl_compl]
#align dense.interior_compl Dense.interior_compl

#print dense_closure /-
/-- The closure of a set `s` is dense if and only if `s` is dense. -/
@[simp]
theorem dense_closure {s : Set α} : Dense (closure s) ↔ Dense s := by
  rw [Dense, Dense, closure_closure]
#align dense_closure dense_closure
-/

alias dense_closure ↔ Dense.of_closure Dense.closure
#align dense.of_closure Dense.of_closure
#align dense.closure Dense.closure

#print dense_univ /-
@[simp]
theorem dense_univ : Dense (univ : Set α) := fun x => subset_closure trivial
#align dense_univ dense_univ
-/

/- warning: dense_iff_inter_open -> dense_iff_inter_open is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Iff (Dense.{u1} α _inst_1 s) (forall (U : Set.{u1} α), (IsOpen.{u1} α _inst_1 U) -> (Set.Nonempty.{u1} α U) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) U s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Iff (Dense.{u1} α _inst_1 s) (forall (U : Set.{u1} α), (IsOpen.{u1} α _inst_1 U) -> (Set.Nonempty.{u1} α U) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) U s)))
Case conversion may be inaccurate. Consider using '#align dense_iff_inter_open dense_iff_inter_openₓ'. -/
/-- A set is dense if and only if it has a nonempty intersection with each nonempty open set. -/
theorem dense_iff_inter_open {s : Set α} :
    Dense s ↔ ∀ U, IsOpen U → U.Nonempty → (U ∩ s).Nonempty :=
  by
  constructor <;> intro h
  · rintro U U_op ⟨x, x_in⟩
    exact mem_closure_iff.1 (by simp only [h.closure_eq]) U U_op x_in
  · intro x
    rw [mem_closure_iff]
    intro U U_op x_in
    exact h U U_op ⟨_, x_in⟩
#align dense_iff_inter_open dense_iff_inter_open

/- warning: dense.inter_open_nonempty -> Dense.inter_open_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, (Dense.{u1} α _inst_1 s) -> (forall (U : Set.{u1} α), (IsOpen.{u1} α _inst_1 U) -> (Set.Nonempty.{u1} α U) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) U s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, (Dense.{u1} α _inst_1 s) -> (forall (U : Set.{u1} α), (IsOpen.{u1} α _inst_1 U) -> (Set.Nonempty.{u1} α U) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) U s)))
Case conversion may be inaccurate. Consider using '#align dense.inter_open_nonempty Dense.inter_open_nonemptyₓ'. -/
alias dense_iff_inter_open ↔ Dense.inter_open_nonempty _
#align dense.inter_open_nonempty Dense.inter_open_nonempty

/- warning: dense.exists_mem_open -> Dense.exists_mem_open is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, (Dense.{u1} α _inst_1 s) -> (forall {U : Set.{u1} α}, (IsOpen.{u1} α _inst_1 U) -> (Set.Nonempty.{u1} α U) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x U))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, (Dense.{u1} α _inst_1 s) -> (forall {U : Set.{u1} α}, (IsOpen.{u1} α _inst_1 U) -> (Set.Nonempty.{u1} α U) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x U))))
Case conversion may be inaccurate. Consider using '#align dense.exists_mem_open Dense.exists_mem_openₓ'. -/
theorem Dense.exists_mem_open {s : Set α} (hs : Dense s) {U : Set α} (ho : IsOpen U)
    (hne : U.Nonempty) : ∃ x ∈ s, x ∈ U :=
  let ⟨x, hx⟩ := hs.inter_open_nonempty U ho hne
  ⟨x, hx.2, hx.1⟩
#align dense.exists_mem_open Dense.exists_mem_open

#print Dense.nonempty_iff /-
theorem Dense.nonempty_iff {s : Set α} (hs : Dense s) : s.Nonempty ↔ Nonempty α :=
  ⟨fun ⟨x, hx⟩ => ⟨x⟩, fun ⟨x⟩ =>
    let ⟨y, hy⟩ := hs.inter_open_nonempty _ isOpen_univ ⟨x, trivial⟩
    ⟨y, hy.2⟩⟩
#align dense.nonempty_iff Dense.nonempty_iff
-/

#print Dense.nonempty /-
theorem Dense.nonempty [h : Nonempty α] {s : Set α} (hs : Dense s) : s.Nonempty :=
  hs.nonempty_iff.2 h
#align dense.nonempty Dense.nonempty
-/

#print Dense.mono /-
@[mono]
theorem Dense.mono {s₁ s₂ : Set α} (h : s₁ ⊆ s₂) (hd : Dense s₁) : Dense s₂ := fun x =>
  closure_mono h (hd x)
#align dense.mono Dense.mono
-/

/- warning: dense_compl_singleton_iff_not_open -> dense_compl_singleton_iff_not_open is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α}, Iff (Dense.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))) (Not (IsOpen.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α}, Iff (Dense.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x))) (Not (IsOpen.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)))
Case conversion may be inaccurate. Consider using '#align dense_compl_singleton_iff_not_open dense_compl_singleton_iff_not_openₓ'. -/
/-- Complement to a singleton is dense if and only if the singleton is not an open set. -/
theorem dense_compl_singleton_iff_not_open {x : α} : Dense ({x}ᶜ : Set α) ↔ ¬IsOpen ({x} : Set α) :=
  by
  fconstructor
  · intro hd ho
    exact (hd.inter_open_nonempty _ ho (singleton_nonempty _)).ne_empty (inter_compl_self _)
  · refine' fun ho => dense_iff_inter_open.2 fun U hU hne => inter_compl_nonempty_iff.2 fun hUx => _
    obtain rfl : U = {x}
    exact eq_singleton_iff_nonempty_unique_mem.2 ⟨hne, hUx⟩
    exact ho hU
#align dense_compl_singleton_iff_not_open dense_compl_singleton_iff_not_open

/-!
### Frontier of a set
-/


#print frontier /-
/-- The frontier of a set is the set of points between the closure and interior. -/
def frontier (s : Set α) : Set α :=
  closure s \ interior s
#align frontier frontier
-/

/- warning: closure_diff_interior -> closure_diff_interior is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (closure.{u1} α _inst_1 s) (interior.{u1} α _inst_1 s)) (frontier.{u1} α _inst_1 s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (closure.{u1} α _inst_1 s) (interior.{u1} α _inst_1 s)) (frontier.{u1} α _inst_1 s)
Case conversion may be inaccurate. Consider using '#align closure_diff_interior closure_diff_interiorₓ'. -/
@[simp]
theorem closure_diff_interior (s : Set α) : closure s \ interior s = frontier s :=
  rfl
#align closure_diff_interior closure_diff_interior

/- warning: closure_diff_frontier -> closure_diff_frontier is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (closure.{u1} α _inst_1 s) (frontier.{u1} α _inst_1 s)) (interior.{u1} α _inst_1 s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (closure.{u1} α _inst_1 s) (frontier.{u1} α _inst_1 s)) (interior.{u1} α _inst_1 s)
Case conversion may be inaccurate. Consider using '#align closure_diff_frontier closure_diff_frontierₓ'. -/
@[simp]
theorem closure_diff_frontier (s : Set α) : closure s \ frontier s = interior s := by
  rw [frontier, diff_diff_right_self, inter_eq_self_of_subset_right interior_subset_closure]
#align closure_diff_frontier closure_diff_frontier

/- warning: self_diff_frontier -> self_diff_frontier is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (frontier.{u1} α _inst_1 s)) (interior.{u1} α _inst_1 s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (frontier.{u1} α _inst_1 s)) (interior.{u1} α _inst_1 s)
Case conversion may be inaccurate. Consider using '#align self_diff_frontier self_diff_frontierₓ'. -/
@[simp]
theorem self_diff_frontier (s : Set α) : s \ frontier s = interior s := by
  rw [frontier, diff_diff_right, diff_eq_empty.2 subset_closure,
    inter_eq_self_of_subset_right interior_subset, empty_union]
#align self_diff_frontier self_diff_frontier

/- warning: frontier_eq_closure_inter_closure -> frontier_eq_closure_inter_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (frontier.{u1} α _inst_1 s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (closure.{u1} α _inst_1 s) (closure.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (frontier.{u1} α _inst_1 s) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (closure.{u1} α _inst_1 s) (closure.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)))
Case conversion may be inaccurate. Consider using '#align frontier_eq_closure_inter_closure frontier_eq_closure_inter_closureₓ'. -/
theorem frontier_eq_closure_inter_closure {s : Set α} : frontier s = closure s ∩ closure (sᶜ) := by
  rw [closure_compl, frontier, diff_eq]
#align frontier_eq_closure_inter_closure frontier_eq_closure_inter_closure

#print frontier_subset_closure /-
theorem frontier_subset_closure {s : Set α} : frontier s ⊆ closure s :=
  diff_subset _ _
#align frontier_subset_closure frontier_subset_closure
-/

#print IsClosed.frontier_subset /-
theorem IsClosed.frontier_subset (hs : IsClosed s) : frontier s ⊆ s :=
  frontier_subset_closure.trans hs.closure_eq.Subset
#align is_closed.frontier_subset IsClosed.frontier_subset
-/

#print frontier_closure_subset /-
theorem frontier_closure_subset {s : Set α} : frontier (closure s) ⊆ frontier s :=
  diff_subset_diff closure_closure.Subset <| interior_mono subset_closure
#align frontier_closure_subset frontier_closure_subset
-/

#print frontier_interior_subset /-
theorem frontier_interior_subset {s : Set α} : frontier (interior s) ⊆ frontier s :=
  diff_subset_diff (closure_mono interior_subset) interior_interior.symm.Subset
#align frontier_interior_subset frontier_interior_subset
-/

/- warning: frontier_compl -> frontier_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (frontier.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (frontier.{u1} α _inst_1 s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (frontier.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (frontier.{u1} α _inst_1 s)
Case conversion may be inaccurate. Consider using '#align frontier_compl frontier_complₓ'. -/
/-- The complement of a set has the same frontier as the original set. -/
@[simp]
theorem frontier_compl (s : Set α) : frontier (sᶜ) = frontier s := by
  simp only [frontier_eq_closure_inter_closure, compl_compl, inter_comm]
#align frontier_compl frontier_compl

#print frontier_univ /-
@[simp]
theorem frontier_univ : frontier (univ : Set α) = ∅ := by simp [frontier]
#align frontier_univ frontier_univ
-/

#print frontier_empty /-
@[simp]
theorem frontier_empty : frontier (∅ : Set α) = ∅ := by simp [frontier]
#align frontier_empty frontier_empty
-/

/- warning: frontier_inter_subset -> frontier_inter_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (frontier.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (frontier.{u1} α _inst_1 s) (closure.{u1} α _inst_1 t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (closure.{u1} α _inst_1 s) (frontier.{u1} α _inst_1 t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (frontier.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (frontier.{u1} α _inst_1 s) (closure.{u1} α _inst_1 t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (closure.{u1} α _inst_1 s) (frontier.{u1} α _inst_1 t)))
Case conversion may be inaccurate. Consider using '#align frontier_inter_subset frontier_inter_subsetₓ'. -/
theorem frontier_inter_subset (s t : Set α) :
    frontier (s ∩ t) ⊆ frontier s ∩ closure t ∪ closure s ∩ frontier t :=
  by
  simp only [frontier_eq_closure_inter_closure, compl_inter, closure_union]
  convert inter_subset_inter_left _ (closure_inter_subset_inter_closure s t)
  simp only [inter_distrib_left, inter_distrib_right, inter_assoc]
  congr 2
  apply inter_comm
#align frontier_inter_subset frontier_inter_subset

/- warning: frontier_union_subset -> frontier_union_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (frontier.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (frontier.{u1} α _inst_1 s) (closure.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (closure.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (frontier.{u1} α _inst_1 t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (frontier.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (frontier.{u1} α _inst_1 s) (closure.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (closure.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (frontier.{u1} α _inst_1 t)))
Case conversion may be inaccurate. Consider using '#align frontier_union_subset frontier_union_subsetₓ'. -/
theorem frontier_union_subset (s t : Set α) :
    frontier (s ∪ t) ⊆ frontier s ∩ closure (tᶜ) ∪ closure (sᶜ) ∩ frontier t := by
  simpa only [frontier_compl, ← compl_union] using frontier_inter_subset (sᶜ) (tᶜ)
#align frontier_union_subset frontier_union_subset

/- warning: is_closed.frontier_eq -> IsClosed.frontier_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, (IsClosed.{u1} α _inst_1 s) -> (Eq.{succ u1} (Set.{u1} α) (frontier.{u1} α _inst_1 s) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (interior.{u1} α _inst_1 s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, (IsClosed.{u1} α _inst_1 s) -> (Eq.{succ u1} (Set.{u1} α) (frontier.{u1} α _inst_1 s) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (interior.{u1} α _inst_1 s)))
Case conversion may be inaccurate. Consider using '#align is_closed.frontier_eq IsClosed.frontier_eqₓ'. -/
theorem IsClosed.frontier_eq {s : Set α} (hs : IsClosed s) : frontier s = s \ interior s := by
  rw [frontier, hs.closure_eq]
#align is_closed.frontier_eq IsClosed.frontier_eq

/- warning: is_open.frontier_eq -> IsOpen.frontier_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (Eq.{succ u1} (Set.{u1} α) (frontier.{u1} α _inst_1 s) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (closure.{u1} α _inst_1 s) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (Eq.{succ u1} (Set.{u1} α) (frontier.{u1} α _inst_1 s) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (closure.{u1} α _inst_1 s) s))
Case conversion may be inaccurate. Consider using '#align is_open.frontier_eq IsOpen.frontier_eqₓ'. -/
theorem IsOpen.frontier_eq {s : Set α} (hs : IsOpen s) : frontier s = closure s \ s := by
  rw [frontier, hs.interior_eq]
#align is_open.frontier_eq IsOpen.frontier_eq

/- warning: is_open.inter_frontier_eq -> IsOpen.inter_frontier_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (frontier.{u1} α _inst_1 s)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (frontier.{u1} α _inst_1 s)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align is_open.inter_frontier_eq IsOpen.inter_frontier_eqₓ'. -/
theorem IsOpen.inter_frontier_eq {s : Set α} (hs : IsOpen s) : s ∩ frontier s = ∅ := by
  rw [hs.frontier_eq, inter_diff_self]
#align is_open.inter_frontier_eq IsOpen.inter_frontier_eq

#print isClosed_frontier /-
/-- The frontier of a set is closed. -/
theorem isClosed_frontier {s : Set α} : IsClosed (frontier s) := by
  rw [frontier_eq_closure_inter_closure] <;> exact IsClosed.inter isClosed_closure isClosed_closure
#align is_closed_frontier isClosed_frontier
-/

#print interior_frontier /-
/-- The frontier of a closed set has no interior point. -/
theorem interior_frontier {s : Set α} (h : IsClosed s) : interior (frontier s) = ∅ :=
  by
  have A : frontier s = s \ interior s := h.frontier_eq
  have B : interior (frontier s) ⊆ interior s := by rw [A] <;> exact interior_mono (diff_subset _ _)
  have C : interior (frontier s) ⊆ frontier s := interior_subset
  have : interior (frontier s) ⊆ interior s ∩ (s \ interior s) :=
    subset_inter B (by simpa [A] using C)
  rwa [inter_diff_self, subset_empty_iff] at this
#align interior_frontier interior_frontier
-/

/- warning: closure_eq_interior_union_frontier -> closure_eq_interior_union_frontier is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (closure.{u1} α _inst_1 s) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (interior.{u1} α _inst_1 s) (frontier.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (closure.{u1} α _inst_1 s) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (interior.{u1} α _inst_1 s) (frontier.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align closure_eq_interior_union_frontier closure_eq_interior_union_frontierₓ'. -/
theorem closure_eq_interior_union_frontier (s : Set α) : closure s = interior s ∪ frontier s :=
  (union_diff_cancel interior_subset_closure).symm
#align closure_eq_interior_union_frontier closure_eq_interior_union_frontier

/- warning: closure_eq_self_union_frontier -> closure_eq_self_union_frontier is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (closure.{u1} α _inst_1 s) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s (frontier.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (closure.{u1} α _inst_1 s) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s (frontier.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align closure_eq_self_union_frontier closure_eq_self_union_frontierₓ'. -/
theorem closure_eq_self_union_frontier (s : Set α) : closure s = s ∪ frontier s :=
  (union_diff_cancel' interior_subset subset_closure).symm
#align closure_eq_self_union_frontier closure_eq_self_union_frontier

/- warning: disjoint.frontier_left -> Disjoint.frontier_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : TopologicalSpace.{u1} α], (IsOpen.{u1} α _inst_1 t) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (frontier.{u1} α _inst_1 s) t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : TopologicalSpace.{u1} α], (IsOpen.{u1} α _inst_1 t) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (frontier.{u1} α _inst_1 s) t)
Case conversion may be inaccurate. Consider using '#align disjoint.frontier_left Disjoint.frontier_leftₓ'. -/
theorem Disjoint.frontier_left (ht : IsOpen t) (hd : Disjoint s t) : Disjoint (frontier s) t :=
  subset_compl_iff_disjoint_right.1 <|
    frontier_subset_closure.trans <| closure_minimal (disjoint_left.1 hd) <| isClosed_compl_iff.2 ht
#align disjoint.frontier_left Disjoint.frontier_left

/- warning: disjoint.frontier_right -> Disjoint.frontier_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : TopologicalSpace.{u1} α], (IsOpen.{u1} α _inst_1 s) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (frontier.{u1} α _inst_1 t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : TopologicalSpace.{u1} α], (IsOpen.{u1} α _inst_1 s) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s (frontier.{u1} α _inst_1 t))
Case conversion may be inaccurate. Consider using '#align disjoint.frontier_right Disjoint.frontier_rightₓ'. -/
theorem Disjoint.frontier_right (hs : IsOpen s) (hd : Disjoint s t) : Disjoint s (frontier t) :=
  (hd.symm.frontier_left hs).symm
#align disjoint.frontier_right Disjoint.frontier_right

/- warning: frontier_eq_inter_compl_interior -> frontier_eq_inter_compl_interior is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (frontier.{u1} α _inst_1 s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (interior.{u1} α _inst_1 s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (interior.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (frontier.{u1} α _inst_1 s) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (interior.{u1} α _inst_1 s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (interior.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))))
Case conversion may be inaccurate. Consider using '#align frontier_eq_inter_compl_interior frontier_eq_inter_compl_interiorₓ'. -/
theorem frontier_eq_inter_compl_interior {s : Set α} : frontier s = interior sᶜ ∩ interior (sᶜ)ᶜ :=
  by
  rw [← frontier_compl, ← closure_compl]
  rfl
#align frontier_eq_inter_compl_interior frontier_eq_inter_compl_interior

/- warning: compl_frontier_eq_union_interior -> compl_frontier_eq_union_interior is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (frontier.{u1} α _inst_1 s)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (interior.{u1} α _inst_1 s) (interior.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (frontier.{u1} α _inst_1 s)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (interior.{u1} α _inst_1 s) (interior.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)))
Case conversion may be inaccurate. Consider using '#align compl_frontier_eq_union_interior compl_frontier_eq_union_interiorₓ'. -/
theorem compl_frontier_eq_union_interior {s : Set α} : frontier sᶜ = interior s ∪ interior (sᶜ) :=
  by
  rw [frontier_eq_inter_compl_interior]
  simp only [compl_inter, compl_compl]
#align compl_frontier_eq_union_interior compl_frontier_eq_union_interior

/-!
### Neighborhoods
-/


#print nhds /-
/-- A set is called a neighborhood of `a` if it contains an open set around `a`. The set of all
neighborhoods of `a` forms a filter, the neighborhood filter at `a`, is here defined as the
infimum over the principal filters of all open sets containing `a`. -/
irreducible_def nhds (a : α) : Filter α :=
  ⨅ s ∈ { s : Set α | a ∈ s ∧ IsOpen s }, 𝓟 s
#align nhds nhds
-/

-- mathport name: nhds
scoped[TopologicalSpace] notation "𝓝" => nhds

#print nhdsWithin /-
/-- The "neighborhood within" filter. Elements of `𝓝[s] a` are sets containing the
intersection of `s` and a neighborhood of `a`. -/
def nhdsWithin (a : α) (s : Set α) : Filter α :=
  𝓝 a ⊓ 𝓟 s
#align nhds_within nhdsWithin
-/

-- mathport name: nhds_within
scoped[TopologicalSpace] notation "𝓝[" s "] " x:100 => nhdsWithin x s

-- mathport name: nhds_within.ne
scoped[TopologicalSpace] notation "𝓝[≠] " x:100 => nhdsWithin x ({x}ᶜ)

-- mathport name: nhds_within.ge
scoped[TopologicalSpace] notation "𝓝[≥] " x:100 => nhdsWithin x (Set.Ici x)

-- mathport name: nhds_within.le
scoped[TopologicalSpace] notation "𝓝[≤] " x:100 => nhdsWithin x (Set.Iic x)

-- mathport name: nhds_within.gt
scoped[TopologicalSpace] notation "𝓝[>] " x:100 => nhdsWithin x (Set.Ioi x)

-- mathport name: nhds_within.lt
scoped[TopologicalSpace] notation "𝓝[<] " x:100 => nhdsWithin x (Set.Iio x)

/- warning: nhds_def -> nhds_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α), Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α _inst_1 a) (infᵢ.{u1, succ u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Set.{u1} α) (fun (s : Set.{u1} α) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (IsOpen.{u1} α _inst_1 s)))) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (IsOpen.{u1} α _inst_1 s)))) => Filter.principal.{u1} α s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α), Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α _inst_1 a) (infᵢ.{u1, succ u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (Set.{u1} α) (fun (s : Set.{u1} α) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (IsOpen.{u1} α _inst_1 s)))) (fun (H : Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (IsOpen.{u1} α _inst_1 s)))) => Filter.principal.{u1} α s)))
Case conversion may be inaccurate. Consider using '#align nhds_def nhds_defₓ'. -/
theorem nhds_def (a : α) : 𝓝 a = ⨅ s ∈ { s : Set α | a ∈ s ∧ IsOpen s }, 𝓟 s := by rw [nhds]
#align nhds_def nhds_def

/- warning: nhds_def' -> nhds_def' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α), Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α _inst_1 a) (infᵢ.{u1, succ u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Set.{u1} α) (fun (s : Set.{u1} α) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (IsOpen.{u1} α _inst_1 s) (fun (hs : IsOpen.{u1} α _inst_1 s) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (ha : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Filter.principal.{u1} α s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α), Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α _inst_1 a) (infᵢ.{u1, succ u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (Set.{u1} α) (fun (s : Set.{u1} α) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (IsOpen.{u1} α _inst_1 s) (fun (hs : IsOpen.{u1} α _inst_1 s) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (ha : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => Filter.principal.{u1} α s))))
Case conversion may be inaccurate. Consider using '#align nhds_def' nhds_def'ₓ'. -/
theorem nhds_def' (a : α) : 𝓝 a = ⨅ (s : Set α) (hs : IsOpen s) (ha : a ∈ s), 𝓟 s := by
  simp only [nhds_def, mem_set_of_eq, and_comm' (a ∈ _), infᵢ_and]
#align nhds_def' nhds_def'

#print nhds_basis_opens /-
/-- The open sets containing `a` are a basis for the neighborhood filter. See `nhds_basis_opens'`
for a variant using open neighborhoods instead. -/
theorem nhds_basis_opens (a : α) : (𝓝 a).HasBasis (fun s : Set α => a ∈ s ∧ IsOpen s) fun s => s :=
  by
  rw [nhds_def]
  exact
    has_basis_binfi_principal
      (fun s ⟨has, hs⟩ t ⟨hat, ht⟩ =>
        ⟨s ∩ t, ⟨⟨has, hat⟩, IsOpen.inter hs ht⟩, ⟨inter_subset_left _ _, inter_subset_right _ _⟩⟩)
      ⟨univ, ⟨mem_univ a, isOpen_univ⟩⟩
#align nhds_basis_opens nhds_basis_opens
-/

/- warning: nhds_basis_closeds -> nhds_basis_closeds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α), Filter.HasBasis.{u1, succ u1} α (Set.{u1} α) (nhds.{u1} α _inst_1 a) (fun (s : Set.{u1} α) => And (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) (IsClosed.{u1} α _inst_1 s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α), Filter.HasBasis.{u1, succ u1} α (Set.{u1} α) (nhds.{u1} α _inst_1 a) (fun (s : Set.{u1} α) => And (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)) (IsClosed.{u1} α _inst_1 s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align nhds_basis_closeds nhds_basis_closedsₓ'. -/
theorem nhds_basis_closeds (a : α) : (𝓝 a).HasBasis (fun s : Set α => a ∉ s ∧ IsClosed s) compl :=
  ⟨fun t =>
    (nhds_basis_opens a).mem_iff.trans <|
      compl_surjective.exists.trans <| by simp only [isOpen_compl_iff, mem_compl_iff]⟩
#align nhds_basis_closeds nhds_basis_closeds

/- warning: le_nhds_iff -> le_nhds_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : Filter.{u1} α} {a : α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (nhds.{u1} α _inst_1 a)) (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (IsOpen.{u1} α _inst_1 s) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : Filter.{u1} α} {a : α}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (nhds.{u1} α _inst_1 a)) (forall (s : Set.{u1} α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (IsOpen.{u1} α _inst_1 s) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f))
Case conversion may be inaccurate. Consider using '#align le_nhds_iff le_nhds_iffₓ'. -/
/-- A filter lies below the neighborhood filter at `a` iff it contains every open set around `a`. -/
theorem le_nhds_iff {f a} : f ≤ 𝓝 a ↔ ∀ s : Set α, a ∈ s → IsOpen s → s ∈ f := by simp [nhds_def]
#align le_nhds_iff le_nhds_iff

/- warning: nhds_le_of_le -> nhds_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : Filter.{u1} α} {a : α} {s : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (IsOpen.{u1} α _inst_1 s) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (Filter.principal.{u1} α s) f) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (nhds.{u1} α _inst_1 a) f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : Filter.{u1} α} {a : α} {s : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (IsOpen.{u1} α _inst_1 s) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Filter.principal.{u1} α s) f) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (nhds.{u1} α _inst_1 a) f)
Case conversion may be inaccurate. Consider using '#align nhds_le_of_le nhds_le_of_leₓ'. -/
/-- To show a filter is above the neighborhood filter at `a`, it suffices to show that it is above
the principal filter of some open set `s` containing `a`. -/
theorem nhds_le_of_le {f a} {s : Set α} (h : a ∈ s) (o : IsOpen s) (sf : 𝓟 s ≤ f) : 𝓝 a ≤ f := by
  rw [nhds_def] <;> exact infᵢ_le_of_le s (infᵢ_le_of_le ⟨h, o⟩ sf)
#align nhds_le_of_le nhds_le_of_le

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (t «expr ⊆ » s) -/
theorem mem_nhds_iff {a : α} {s : Set α} : s ∈ 𝓝 a ↔ ∃ (t : _)(_ : t ⊆ s), IsOpen t ∧ a ∈ t :=
  (nhds_basis_opens a).mem_iff.trans
    ⟨fun ⟨t, ⟨hat, ht⟩, hts⟩ => ⟨t, hts, ht, hat⟩, fun ⟨t, hts, ht, hat⟩ => ⟨t, ⟨hat, ht⟩, hts⟩⟩
#align mem_nhds_iff mem_nhds_iffₓ

#print eventually_nhds_iff /-
/-- A predicate is true in a neighborhood of `a` iff it is true for all the points in an open set
containing `a`. -/
theorem eventually_nhds_iff {a : α} {p : α → Prop} :
    (∀ᶠ x in 𝓝 a, p x) ↔ ∃ t : Set α, (∀ x ∈ t, p x) ∧ IsOpen t ∧ a ∈ t :=
  mem_nhds_iff.trans <| by simp only [subset_def, exists_prop, mem_set_of_eq]
#align eventually_nhds_iff eventually_nhds_iff
-/

/- warning: map_nhds -> map_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {f : α -> β}, Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β f (nhds.{u1} α _inst_1 a)) (infᵢ.{u2, succ u1} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) (Set.{u1} α) (fun (s : Set.{u1} α) => infᵢ.{u2, 0} (Filter.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))) (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (IsOpen.{u1} α _inst_1 s)))) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (IsOpen.{u1} α _inst_1 s)))) => Filter.principal.{u2} β (Set.image.{u1, u2} α β f s))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {f : α -> β}, Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β f (nhds.{u1} α _inst_1 a)) (infᵢ.{u2, succ u1} (Filter.{u2} β) (ConditionallyCompleteLattice.toInfSet.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β))) (Set.{u1} α) (fun (s : Set.{u1} α) => infᵢ.{u2, 0} (Filter.{u2} β) (ConditionallyCompleteLattice.toInfSet.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.instCompleteLatticeFilter.{u2} β))) (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (IsOpen.{u1} α _inst_1 s)))) (fun (H : Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (IsOpen.{u1} α _inst_1 s)))) => Filter.principal.{u2} β (Set.image.{u1, u2} α β f s))))
Case conversion may be inaccurate. Consider using '#align map_nhds map_nhdsₓ'. -/
theorem map_nhds {a : α} {f : α → β} :
    map f (𝓝 a) = ⨅ s ∈ { s : Set α | a ∈ s ∧ IsOpen s }, 𝓟 (image f s) :=
  ((nhds_basis_opens a).map f).eq_binfi
#align map_nhds map_nhds

#print mem_of_mem_nhds /-
theorem mem_of_mem_nhds {a : α} {s : Set α} : s ∈ 𝓝 a → a ∈ s := fun H =>
  let ⟨t, ht, _, hs⟩ := mem_nhds_iff.1 H
  ht hs
#align mem_of_mem_nhds mem_of_mem_nhds
-/

#print Filter.Eventually.self_of_nhds /-
/-- If a predicate is true in a neighborhood of `a`, then it is true for `a`. -/
theorem Filter.Eventually.self_of_nhds {p : α → Prop} {a : α} (h : ∀ᶠ y in 𝓝 a, p y) : p a :=
  mem_of_mem_nhds h
#align filter.eventually.self_of_nhds Filter.Eventually.self_of_nhds
-/

#print IsOpen.mem_nhds /-
theorem IsOpen.mem_nhds {a : α} {s : Set α} (hs : IsOpen s) (ha : a ∈ s) : s ∈ 𝓝 a :=
  mem_nhds_iff.2 ⟨s, Subset.refl _, hs, ha⟩
#align is_open.mem_nhds IsOpen.mem_nhds
-/

#print IsOpen.mem_nhds_iff /-
theorem IsOpen.mem_nhds_iff {a : α} {s : Set α} (hs : IsOpen s) : s ∈ 𝓝 a ↔ a ∈ s :=
  ⟨mem_of_mem_nhds, fun ha => mem_nhds_iff.2 ⟨s, Subset.refl _, hs, ha⟩⟩
#align is_open.mem_nhds_iff IsOpen.mem_nhds_iff
-/

/- warning: is_closed.compl_mem_nhds -> IsClosed.compl_mem_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {s : Set.{u1} α}, (IsClosed.{u1} α _inst_1 s) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (nhds.{u1} α _inst_1 a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {s : Set.{u1} α}, (IsClosed.{u1} α _inst_1 s) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) (nhds.{u1} α _inst_1 a))
Case conversion may be inaccurate. Consider using '#align is_closed.compl_mem_nhds IsClosed.compl_mem_nhdsₓ'. -/
theorem IsClosed.compl_mem_nhds {a : α} {s : Set α} (hs : IsClosed s) (ha : a ∉ s) : sᶜ ∈ 𝓝 a :=
  hs.is_open_compl.mem_nhds (mem_compl ha)
#align is_closed.compl_mem_nhds IsClosed.compl_mem_nhds

#print IsOpen.eventually_mem /-
theorem IsOpen.eventually_mem {a : α} {s : Set α} (hs : IsOpen s) (ha : a ∈ s) :
    ∀ᶠ x in 𝓝 a, x ∈ s :=
  IsOpen.mem_nhds hs ha
#align is_open.eventually_mem IsOpen.eventually_mem
-/

#print nhds_basis_opens' /-
/-- The open neighborhoods of `a` are a basis for the neighborhood filter. See `nhds_basis_opens`
for a variant using open sets around `a` instead. -/
theorem nhds_basis_opens' (a : α) :
    (𝓝 a).HasBasis (fun s : Set α => s ∈ 𝓝 a ∧ IsOpen s) fun x => x :=
  by
  convert nhds_basis_opens a
  ext s
  exact and_congr_left_iff.2 IsOpen.mem_nhds_iff
#align nhds_basis_opens' nhds_basis_opens'
-/

#print exists_open_set_nhds /-
/-- If `U` is a neighborhood of each point of a set `s` then it is a neighborhood of `s`:
it contains an open set containing `s`. -/
theorem exists_open_set_nhds {s U : Set α} (h : ∀ x ∈ s, U ∈ 𝓝 x) :
    ∃ V : Set α, s ⊆ V ∧ IsOpen V ∧ V ⊆ U :=
  by
  have := fun x hx => (nhds_basis_opens x).mem_iff.1 (h x hx)
  choose! Z hZ hZU using this; choose hZmem hZo using hZ
  exact
    ⟨⋃ x ∈ s, Z x, fun x hx => mem_bUnion hx (hZmem x hx), isOpen_bunionᵢ hZo, Union₂_subset hZU⟩
#align exists_open_set_nhds exists_open_set_nhds
-/

/- warning: exists_open_set_nhds' -> exists_open_set_nhds' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {U : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U (supᵢ.{u1, succ u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) α (fun (x : α) => supᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => nhds.{u1} α _inst_1 x)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (V : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s V) (And (IsOpen.{u1} α _inst_1 V) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) V U))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {U : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) U (supᵢ.{u1, succ u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toSupSet.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) α (fun (x : α) => supᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toSupSet.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) => nhds.{u1} α _inst_1 x)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (V : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s V) (And (IsOpen.{u1} α _inst_1 V) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) V U))))
Case conversion may be inaccurate. Consider using '#align exists_open_set_nhds' exists_open_set_nhds'ₓ'. -/
/-- If `U` is a neighborhood of each point of a set `s` then it is a neighborhood of s:
it contains an open set containing `s`. -/
theorem exists_open_set_nhds' {s U : Set α} (h : U ∈ ⨆ x ∈ s, 𝓝 x) :
    ∃ V : Set α, s ⊆ V ∧ IsOpen V ∧ V ⊆ U :=
  exists_open_set_nhds (by simpa using h)
#align exists_open_set_nhds' exists_open_set_nhds'

#print Filter.Eventually.eventually_nhds /-
/-- If a predicate is true in a neighbourhood of `a`, then for `y` sufficiently close
to `a` this predicate is true in a neighbourhood of `y`. -/
theorem Filter.Eventually.eventually_nhds {p : α → Prop} {a : α} (h : ∀ᶠ y in 𝓝 a, p y) :
    ∀ᶠ y in 𝓝 a, ∀ᶠ x in 𝓝 y, p x :=
  let ⟨t, htp, hto, ha⟩ := eventually_nhds_iff.1 h
  eventually_nhds_iff.2 ⟨t, fun x hx => eventually_nhds_iff.2 ⟨t, htp, hto, hx⟩, hto, ha⟩
#align filter.eventually.eventually_nhds Filter.Eventually.eventually_nhds
-/

#print eventually_eventually_nhds /-
@[simp]
theorem eventually_eventually_nhds {p : α → Prop} {a : α} :
    (∀ᶠ y in 𝓝 a, ∀ᶠ x in 𝓝 y, p x) ↔ ∀ᶠ x in 𝓝 a, p x :=
  ⟨fun h => h.self_of_nhds, fun h => h.eventually_nhds⟩
#align eventually_eventually_nhds eventually_eventually_nhds
-/

#print frequently_frequently_nhds /-
@[simp]
theorem frequently_frequently_nhds {p : α → Prop} {a : α} :
    (∃ᶠ y in 𝓝 a, ∃ᶠ x in 𝓝 y, p x) ↔ ∃ᶠ x in 𝓝 a, p x :=
  by
  rw [← not_iff_not]
  simp_rw [not_frequently]
  exact eventually_eventually_nhds
#align frequently_frequently_nhds frequently_frequently_nhds
-/

#print eventually_mem_nhds /-
@[simp]
theorem eventually_mem_nhds {s : Set α} {a : α} : (∀ᶠ x in 𝓝 a, s ∈ 𝓝 x) ↔ s ∈ 𝓝 a :=
  eventually_eventually_nhds
#align eventually_mem_nhds eventually_mem_nhds
-/

#print nhds_bind_nhds /-
@[simp]
theorem nhds_bind_nhds : (𝓝 a).bind 𝓝 = 𝓝 a :=
  Filter.ext fun s => eventually_eventually_nhds
#align nhds_bind_nhds nhds_bind_nhds
-/

#print eventually_eventuallyEq_nhds /-
@[simp]
theorem eventually_eventuallyEq_nhds {f g : α → β} {a : α} :
    (∀ᶠ y in 𝓝 a, f =ᶠ[𝓝 y] g) ↔ f =ᶠ[𝓝 a] g :=
  eventually_eventually_nhds
#align eventually_eventually_eq_nhds eventually_eventuallyEq_nhds
-/

#print Filter.EventuallyEq.eq_of_nhds /-
theorem Filter.EventuallyEq.eq_of_nhds {f g : α → β} {a : α} (h : f =ᶠ[𝓝 a] g) : f a = g a :=
  h.self_of_nhds
#align filter.eventually_eq.eq_of_nhds Filter.EventuallyEq.eq_of_nhds
-/

#print eventually_eventuallyLe_nhds /-
@[simp]
theorem eventually_eventuallyLe_nhds [LE β] {f g : α → β} {a : α} :
    (∀ᶠ y in 𝓝 a, f ≤ᶠ[𝓝 y] g) ↔ f ≤ᶠ[𝓝 a] g :=
  eventually_eventually_nhds
#align eventually_eventually_le_nhds eventually_eventuallyLe_nhds
-/

#print Filter.EventuallyEq.eventuallyEq_nhds /-
/-- If two functions are equal in a neighbourhood of `a`, then for `y` sufficiently close
to `a` these functions are equal in a neighbourhood of `y`. -/
theorem Filter.EventuallyEq.eventuallyEq_nhds {f g : α → β} {a : α} (h : f =ᶠ[𝓝 a] g) :
    ∀ᶠ y in 𝓝 a, f =ᶠ[𝓝 y] g :=
  h.eventually_nhds
#align filter.eventually_eq.eventually_eq_nhds Filter.EventuallyEq.eventuallyEq_nhds
-/

#print Filter.EventuallyLe.eventuallyLe_nhds /-
/-- If `f x ≤ g x` in a neighbourhood of `a`, then for `y` sufficiently close to `a` we have
`f x ≤ g x` in a neighbourhood of `y`. -/
theorem Filter.EventuallyLe.eventuallyLe_nhds [LE β] {f g : α → β} {a : α} (h : f ≤ᶠ[𝓝 a] g) :
    ∀ᶠ y in 𝓝 a, f ≤ᶠ[𝓝 y] g :=
  h.eventually_nhds
#align filter.eventually_le.eventually_le_nhds Filter.EventuallyLe.eventuallyLe_nhds
-/

#print all_mem_nhds /-
theorem all_mem_nhds (x : α) (P : Set α → Prop) (hP : ∀ s t, s ⊆ t → P s → P t) :
    (∀ s ∈ 𝓝 x, P s) ↔ ∀ s, IsOpen s → x ∈ s → P s :=
  ((nhds_basis_opens x).forall_iff hP).trans <| by simp only [and_comm' (x ∈ _), and_imp]
#align all_mem_nhds all_mem_nhds
-/

#print all_mem_nhds_filter /-
theorem all_mem_nhds_filter (x : α) (f : Set α → Set β) (hf : ∀ s t, s ⊆ t → f s ⊆ f t)
    (l : Filter β) : (∀ s ∈ 𝓝 x, f s ∈ l) ↔ ∀ s, IsOpen s → x ∈ s → f s ∈ l :=
  all_mem_nhds _ _ fun s t ssubt h => mem_of_superset h (hf s t ssubt)
#align all_mem_nhds_filter all_mem_nhds_filter
-/

#print tendsto_nhds /-
theorem tendsto_nhds {f : β → α} {l : Filter β} {a : α} :
    Tendsto f l (𝓝 a) ↔ ∀ s, IsOpen s → a ∈ s → f ⁻¹' s ∈ l :=
  all_mem_nhds_filter _ _ (fun s t h => preimage_mono h) _
#align tendsto_nhds tendsto_nhds
-/

#print tendsto_atTop_nhds /-
theorem tendsto_atTop_nhds [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} :
    Tendsto f atTop (𝓝 a) ↔ ∀ U : Set α, a ∈ U → IsOpen U → ∃ N, ∀ n, N ≤ n → f n ∈ U :=
  (atTop_basis.tendsto_iff (nhds_basis_opens a)).trans <| by
    simp only [and_imp, exists_prop, true_and_iff, mem_Ici, ge_iff_le]
#align tendsto_at_top_nhds tendsto_atTop_nhds
-/

#print tendsto_const_nhds /-
theorem tendsto_const_nhds {a : α} {f : Filter β} : Tendsto (fun b : β => a) f (𝓝 a) :=
  tendsto_nhds.mpr fun s hs ha => univ_mem' fun _ => ha
#align tendsto_const_nhds tendsto_const_nhds
-/

/- warning: tendsto_at_top_of_eventually_const -> tendsto_atTop_of_eventually_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Type.{u2}} [_inst_2 : SemilatticeSup.{u2} ι] [_inst_3 : Nonempty.{succ u2} ι] {x : α} {u : ι -> α} {i₀ : ι}, (forall (i : ι), (GE.ge.{u2} ι (Preorder.toLE.{u2} ι (PartialOrder.toPreorder.{u2} ι (SemilatticeSup.toPartialOrder.{u2} ι _inst_2))) i i₀) -> (Eq.{succ u1} α (u i) x)) -> (Filter.Tendsto.{u2, u1} ι α u (Filter.atTop.{u2} ι (PartialOrder.toPreorder.{u2} ι (SemilatticeSup.toPartialOrder.{u2} ι _inst_2))) (nhds.{u1} α _inst_1 x))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {ι : Type.{u1}} [_inst_2 : SemilatticeSup.{u1} ι] [_inst_3 : Nonempty.{succ u1} ι] {x : α} {u : ι -> α} {i₀ : ι}, (forall (i : ι), (GE.ge.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι (SemilatticeSup.toPartialOrder.{u1} ι _inst_2))) i i₀) -> (Eq.{succ u2} α (u i) x)) -> (Filter.Tendsto.{u1, u2} ι α u (Filter.atTop.{u1} ι (PartialOrder.toPreorder.{u1} ι (SemilatticeSup.toPartialOrder.{u1} ι _inst_2))) (nhds.{u2} α _inst_1 x))
Case conversion may be inaccurate. Consider using '#align tendsto_at_top_of_eventually_const tendsto_atTop_of_eventually_constₓ'. -/
theorem tendsto_atTop_of_eventually_const {ι : Type _} [SemilatticeSup ι] [Nonempty ι] {x : α}
    {u : ι → α} {i₀ : ι} (h : ∀ i ≥ i₀, u i = x) : Tendsto u atTop (𝓝 x) :=
  Tendsto.congr' (EventuallyEq.symm (eventually_atTop.mpr ⟨i₀, h⟩)) tendsto_const_nhds
#align tendsto_at_top_of_eventually_const tendsto_atTop_of_eventually_const

/- warning: tendsto_at_bot_of_eventually_const -> tendsto_atBot_of_eventually_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Type.{u2}} [_inst_2 : SemilatticeInf.{u2} ι] [_inst_3 : Nonempty.{succ u2} ι] {x : α} {u : ι -> α} {i₀ : ι}, (forall (i : ι), (LE.le.{u2} ι (Preorder.toLE.{u2} ι (PartialOrder.toPreorder.{u2} ι (SemilatticeInf.toPartialOrder.{u2} ι _inst_2))) i i₀) -> (Eq.{succ u1} α (u i) x)) -> (Filter.Tendsto.{u2, u1} ι α u (Filter.atBot.{u2} ι (PartialOrder.toPreorder.{u2} ι (SemilatticeInf.toPartialOrder.{u2} ι _inst_2))) (nhds.{u1} α _inst_1 x))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {ι : Type.{u1}} [_inst_2 : SemilatticeInf.{u1} ι] [_inst_3 : Nonempty.{succ u1} ι] {x : α} {u : ι -> α} {i₀ : ι}, (forall (i : ι), (LE.le.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι _inst_2))) i i₀) -> (Eq.{succ u2} α (u i) x)) -> (Filter.Tendsto.{u1, u2} ι α u (Filter.atBot.{u1} ι (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι _inst_2))) (nhds.{u2} α _inst_1 x))
Case conversion may be inaccurate. Consider using '#align tendsto_at_bot_of_eventually_const tendsto_atBot_of_eventually_constₓ'. -/
theorem tendsto_atBot_of_eventually_const {ι : Type _} [SemilatticeInf ι] [Nonempty ι] {x : α}
    {u : ι → α} {i₀ : ι} (h : ∀ i ≤ i₀, u i = x) : Tendsto u atBot (𝓝 x) :=
  Tendsto.congr' (EventuallyEq.symm (eventually_atBot.mpr ⟨i₀, h⟩)) tendsto_const_nhds
#align tendsto_at_bot_of_eventually_const tendsto_atBot_of_eventually_const

/- warning: pure_le_nhds -> pure_le_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], LE.le.{u1} (α -> (Filter.{u1} α)) (Pi.hasLe.{u1, u1} α (fun (ᾰ : α) => Filter.{u1} α) (fun (i : α) => Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)))) (Pure.pure.{u1, u1} (fun {α : Type.{u1}} => Filter.{u1} α) Filter.hasPure.{u1} α) (nhds.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], LE.le.{u1} (α -> (Filter.{u1} α)) (Pi.hasLe.{u1, u1} α (fun (ᾰ : α) => Filter.{u1} α) (fun (i : α) => Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α)))) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} α) (nhds.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align pure_le_nhds pure_le_nhdsₓ'. -/
theorem pure_le_nhds : pure ≤ (𝓝 : α → Filter α) := fun a s hs => mem_pure.2 <| mem_of_mem_nhds hs
#align pure_le_nhds pure_le_nhds

/- warning: tendsto_pure_nhds -> tendsto_pure_nhds is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_2 : TopologicalSpace.{u1} β] (f : α -> β) (a : α), Filter.Tendsto.{u2, u1} α β f (Pure.pure.{u2, u2} Filter.{u2} Filter.hasPure.{u2} α a) (nhds.{u1} β _inst_2 (f a))
but is expected to have type
  forall {β : Type.{u2}} {α : Type.{u1}} [_inst_2 : TopologicalSpace.{u2} β] (f : α -> β) (a : α), Filter.Tendsto.{u1, u2} α β f (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} α a) (nhds.{u2} β _inst_2 (f a))
Case conversion may be inaccurate. Consider using '#align tendsto_pure_nhds tendsto_pure_nhdsₓ'. -/
theorem tendsto_pure_nhds {α : Type _} [TopologicalSpace β] (f : α → β) (a : α) :
    Tendsto f (pure a) (𝓝 (f a)) :=
  (tendsto_pure_pure f a).mono_right (pure_le_nhds _)
#align tendsto_pure_nhds tendsto_pure_nhds

/- warning: order_top.tendsto_at_top_nhds -> OrderTop.tendsto_atTop_nhds is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_2 : PartialOrder.{u2} α] [_inst_3 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_2))] [_inst_4 : TopologicalSpace.{u1} β] (f : α -> β), Filter.Tendsto.{u2, u1} α β f (Filter.atTop.{u2} α (PartialOrder.toPreorder.{u2} α _inst_2)) (nhds.{u1} β _inst_4 (f (Top.top.{u2} α (OrderTop.toHasTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_2)) _inst_3))))
but is expected to have type
  forall {β : Type.{u2}} {α : Type.{u1}} [_inst_2 : PartialOrder.{u1} α] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : TopologicalSpace.{u2} β] (f : α -> β), Filter.Tendsto.{u1, u2} α β f (Filter.atTop.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (nhds.{u2} β _inst_4 (f (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) _inst_3))))
Case conversion may be inaccurate. Consider using '#align order_top.tendsto_at_top_nhds OrderTop.tendsto_atTop_nhdsₓ'. -/
theorem OrderTop.tendsto_atTop_nhds {α : Type _} [PartialOrder α] [OrderTop α] [TopologicalSpace β]
    (f : α → β) : Tendsto f atTop (𝓝 <| f ⊤) :=
  (tendsto_atTop_pure f).mono_right (pure_le_nhds _)
#align order_top.tendsto_at_top_nhds OrderTop.tendsto_atTop_nhds

#print nhds_neBot /-
@[simp]
instance nhds_neBot {a : α} : NeBot (𝓝 a) :=
  neBot_of_le (pure_le_nhds a)
#align nhds_ne_bot nhds_neBot
-/

/-!
### Cluster points

In this section we define [cluster points](https://en.wikipedia.org/wiki/Limit_point)
(also known as limit points and accumulation points) of a filter and of a sequence.
-/


#print ClusterPt /-
/-- A point `x` is a cluster point of a filter `F` if `𝓝 x ⊓ F ≠ ⊥`. Also known as
an accumulation point or a limit point, but beware that terminology varies. This
is *not* the same as asking `𝓝[≠] x ⊓ F ≠ ⊥`. See `mem_closure_iff_cluster_pt` in particular. -/
def ClusterPt (x : α) (F : Filter α) : Prop :=
  NeBot (𝓝 x ⊓ F)
#align cluster_pt ClusterPt
-/

/- warning: cluster_pt.ne_bot -> ClusterPt.neBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {F : Filter.{u1} α}, (ClusterPt.{u1} α _inst_1 x F) -> (Filter.NeBot.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) (nhds.{u1} α _inst_1 x) F))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {F : Filter.{u1} α}, (ClusterPt.{u1} α _inst_1 x F) -> (Filter.NeBot.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) (nhds.{u1} α _inst_1 x) F))
Case conversion may be inaccurate. Consider using '#align cluster_pt.ne_bot ClusterPt.neBotₓ'. -/
theorem ClusterPt.neBot {x : α} {F : Filter α} (h : ClusterPt x F) : NeBot (𝓝 x ⊓ F) :=
  h
#align cluster_pt.ne_bot ClusterPt.neBot

/- warning: filter.has_basis.cluster_pt_iff -> Filter.HasBasis.clusterPt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} [_inst_1 : TopologicalSpace.{u1} α] {ιa : Sort.{u2}} {ιF : Sort.{u3}} {pa : ιa -> Prop} {sa : ιa -> (Set.{u1} α)} {pF : ιF -> Prop} {sF : ιF -> (Set.{u1} α)} {F : Filter.{u1} α}, (Filter.HasBasis.{u1, u2} α ιa (nhds.{u1} α _inst_1 a) pa sa) -> (Filter.HasBasis.{u1, u3} α ιF F pF sF) -> (Iff (ClusterPt.{u1} α _inst_1 a F) (forall {{i : ιa}}, (pa i) -> (forall {{j : ιF}}, (pF j) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (sa i) (sF j))))))
but is expected to have type
  forall {α : Type.{u3}} {a : α} [_inst_1 : TopologicalSpace.{u3} α] {ιa : Sort.{u2}} {ιF : Sort.{u1}} {pa : ιa -> Prop} {sa : ιa -> (Set.{u3} α)} {pF : ιF -> Prop} {sF : ιF -> (Set.{u3} α)} {F : Filter.{u3} α}, (Filter.HasBasis.{u3, u2} α ιa (nhds.{u3} α _inst_1 a) pa sa) -> (Filter.HasBasis.{u3, u1} α ιF F pF sF) -> (Iff (ClusterPt.{u3} α _inst_1 a F) (forall {{i : ιa}}, (pa i) -> (forall {{j : ιF}}, (pF j) -> (Set.Nonempty.{u3} α (Inter.inter.{u3} (Set.{u3} α) (Set.instInterSet.{u3} α) (sa i) (sF j))))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.cluster_pt_iff Filter.HasBasis.clusterPt_iffₓ'. -/
theorem Filter.HasBasis.clusterPt_iff {ιa ιF} {pa : ιa → Prop} {sa : ιa → Set α} {pF : ιF → Prop}
    {sF : ιF → Set α} {F : Filter α} (ha : (𝓝 a).HasBasis pa sa) (hF : F.HasBasis pF sF) :
    ClusterPt a F ↔ ∀ ⦃i⦄ (hi : pa i) ⦃j⦄ (hj : pF j), (sa i ∩ sF j).Nonempty :=
  ha.inf_basis_ne_bot_iff hF
#align filter.has_basis.cluster_pt_iff Filter.HasBasis.clusterPt_iff

/- warning: cluster_pt_iff -> clusterPt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {F : Filter.{u1} α}, Iff (ClusterPt.{u1} α _inst_1 x F) (forall {{U : Set.{u1} α}}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U (nhds.{u1} α _inst_1 x)) -> (forall {{V : Set.{u1} α}}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) V F) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) U V))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {F : Filter.{u1} α}, Iff (ClusterPt.{u1} α _inst_1 x F) (forall {{U : Set.{u1} α}}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) U (nhds.{u1} α _inst_1 x)) -> (forall {{V : Set.{u1} α}}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) V F) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) U V))))
Case conversion may be inaccurate. Consider using '#align cluster_pt_iff clusterPt_iffₓ'. -/
theorem clusterPt_iff {x : α} {F : Filter α} :
    ClusterPt x F ↔ ∀ ⦃U : Set α⦄ (hU : U ∈ 𝓝 x) ⦃V⦄ (hV : V ∈ F), (U ∩ V).Nonempty :=
  inf_ne_bot_iff
#align cluster_pt_iff clusterPt_iff

/- warning: cluster_pt_principal_iff -> clusterPt_principal_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α}, Iff (ClusterPt.{u1} α _inst_1 x (Filter.principal.{u1} α s)) (forall (U : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U (nhds.{u1} α _inst_1 x)) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) U s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α}, Iff (ClusterPt.{u1} α _inst_1 x (Filter.principal.{u1} α s)) (forall (U : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) U (nhds.{u1} α _inst_1 x)) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) U s)))
Case conversion may be inaccurate. Consider using '#align cluster_pt_principal_iff clusterPt_principal_iffₓ'. -/
/-- `x` is a cluster point of a set `s` if every neighbourhood of `x` meets `s` on a nonempty
set. See also `mem_closure_iff_cluster_pt`. -/
theorem clusterPt_principal_iff {x : α} {s : Set α} :
    ClusterPt x (𝓟 s) ↔ ∀ U ∈ 𝓝 x, (U ∩ s).Nonempty :=
  inf_principal_ne_bot_iff
#align cluster_pt_principal_iff clusterPt_principal_iff

#print clusterPt_principal_iff_frequently /-
theorem clusterPt_principal_iff_frequently {x : α} {s : Set α} :
    ClusterPt x (𝓟 s) ↔ ∃ᶠ y in 𝓝 x, y ∈ s := by
  simp only [clusterPt_principal_iff, frequently_iff, Set.Nonempty, exists_prop, mem_inter_iff]
#align cluster_pt_principal_iff_frequently clusterPt_principal_iff_frequently
-/

/- warning: cluster_pt.of_le_nhds -> ClusterPt.of_le_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {f : Filter.{u1} α}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (nhds.{u1} α _inst_1 x)) -> (forall [_inst_2 : Filter.NeBot.{u1} α f], ClusterPt.{u1} α _inst_1 x f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {f : Filter.{u1} α}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (nhds.{u1} α _inst_1 x)) -> (forall [_inst_2 : Filter.NeBot.{u1} α f], ClusterPt.{u1} α _inst_1 x f)
Case conversion may be inaccurate. Consider using '#align cluster_pt.of_le_nhds ClusterPt.of_le_nhdsₓ'. -/
theorem ClusterPt.of_le_nhds {x : α} {f : Filter α} (H : f ≤ 𝓝 x) [NeBot f] : ClusterPt x f := by
  rwa [ClusterPt, inf_eq_right.mpr H]
#align cluster_pt.of_le_nhds ClusterPt.of_le_nhds

/- warning: cluster_pt.of_le_nhds' -> ClusterPt.of_le_nhds' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {f : Filter.{u1} α}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (nhds.{u1} α _inst_1 x)) -> (Filter.NeBot.{u1} α f) -> (ClusterPt.{u1} α _inst_1 x f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {f : Filter.{u1} α}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (nhds.{u1} α _inst_1 x)) -> (Filter.NeBot.{u1} α f) -> (ClusterPt.{u1} α _inst_1 x f)
Case conversion may be inaccurate. Consider using '#align cluster_pt.of_le_nhds' ClusterPt.of_le_nhds'ₓ'. -/
theorem ClusterPt.of_le_nhds' {x : α} {f : Filter α} (H : f ≤ 𝓝 x) (hf : NeBot f) : ClusterPt x f :=
  ClusterPt.of_le_nhds H
#align cluster_pt.of_le_nhds' ClusterPt.of_le_nhds'

/- warning: cluster_pt.of_nhds_le -> ClusterPt.of_nhds_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {f : Filter.{u1} α}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (nhds.{u1} α _inst_1 x) f) -> (ClusterPt.{u1} α _inst_1 x f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {f : Filter.{u1} α}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (nhds.{u1} α _inst_1 x) f) -> (ClusterPt.{u1} α _inst_1 x f)
Case conversion may be inaccurate. Consider using '#align cluster_pt.of_nhds_le ClusterPt.of_nhds_leₓ'. -/
theorem ClusterPt.of_nhds_le {x : α} {f : Filter α} (H : 𝓝 x ≤ f) : ClusterPt x f := by
  simp only [ClusterPt, inf_eq_left.mpr H, nhds_neBot]
#align cluster_pt.of_nhds_le ClusterPt.of_nhds_le

/- warning: cluster_pt.mono -> ClusterPt.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {f : Filter.{u1} α} {g : Filter.{u1} α}, (ClusterPt.{u1} α _inst_1 x f) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f g) -> (ClusterPt.{u1} α _inst_1 x g)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {f : Filter.{u1} α} {g : Filter.{u1} α}, (ClusterPt.{u1} α _inst_1 x f) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f g) -> (ClusterPt.{u1} α _inst_1 x g)
Case conversion may be inaccurate. Consider using '#align cluster_pt.mono ClusterPt.monoₓ'. -/
theorem ClusterPt.mono {x : α} {f g : Filter α} (H : ClusterPt x f) (h : f ≤ g) : ClusterPt x g :=
  ⟨ne_bot_of_le_ne_bot H.Ne <| inf_le_inf_left _ h⟩
#align cluster_pt.mono ClusterPt.mono

/- warning: cluster_pt.of_inf_left -> ClusterPt.of_inf_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {f : Filter.{u1} α} {g : Filter.{u1} α}, (ClusterPt.{u1} α _inst_1 x (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f g)) -> (ClusterPt.{u1} α _inst_1 x f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {f : Filter.{u1} α} {g : Filter.{u1} α}, (ClusterPt.{u1} α _inst_1 x (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f g)) -> (ClusterPt.{u1} α _inst_1 x f)
Case conversion may be inaccurate. Consider using '#align cluster_pt.of_inf_left ClusterPt.of_inf_leftₓ'. -/
theorem ClusterPt.of_inf_left {x : α} {f g : Filter α} (H : ClusterPt x <| f ⊓ g) : ClusterPt x f :=
  H.mono inf_le_left
#align cluster_pt.of_inf_left ClusterPt.of_inf_left

/- warning: cluster_pt.of_inf_right -> ClusterPt.of_inf_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {f : Filter.{u1} α} {g : Filter.{u1} α}, (ClusterPt.{u1} α _inst_1 x (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f g)) -> (ClusterPt.{u1} α _inst_1 x g)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {f : Filter.{u1} α} {g : Filter.{u1} α}, (ClusterPt.{u1} α _inst_1 x (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) f g)) -> (ClusterPt.{u1} α _inst_1 x g)
Case conversion may be inaccurate. Consider using '#align cluster_pt.of_inf_right ClusterPt.of_inf_rightₓ'. -/
theorem ClusterPt.of_inf_right {x : α} {f g : Filter α} (H : ClusterPt x <| f ⊓ g) :
    ClusterPt x g :=
  H.mono inf_le_right
#align cluster_pt.of_inf_right ClusterPt.of_inf_right

/- warning: ultrafilter.cluster_pt_iff -> Ultrafilter.clusterPt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {f : Ultrafilter.{u1} α}, Iff (ClusterPt.{u1} α _inst_1 x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) f)) (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) f) (nhds.{u1} α _inst_1 x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {f : Ultrafilter.{u1} α}, Iff (ClusterPt.{u1} α _inst_1 x (Ultrafilter.toFilter.{u1} α f)) (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Ultrafilter.toFilter.{u1} α f) (nhds.{u1} α _inst_1 x))
Case conversion may be inaccurate. Consider using '#align ultrafilter.cluster_pt_iff Ultrafilter.clusterPt_iffₓ'. -/
theorem Ultrafilter.clusterPt_iff {x : α} {f : Ultrafilter α} : ClusterPt x f ↔ ↑f ≤ 𝓝 x :=
  ⟨f.le_of_inf_ne_bot', fun h => ClusterPt.of_le_nhds h⟩
#align ultrafilter.cluster_pt_iff Ultrafilter.clusterPt_iff

#print MapClusterPt /-
/-- A point `x` is a cluster point of a sequence `u` along a filter `F` if it is a cluster point
of `map u F`. -/
def MapClusterPt {ι : Type _} (x : α) (F : Filter ι) (u : ι → α) : Prop :=
  ClusterPt x (map u F)
#align map_cluster_pt MapClusterPt
-/

/- warning: map_cluster_pt_iff -> mapClusterPt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Type.{u2}} (x : α) (F : Filter.{u2} ι) (u : ι -> α), Iff (MapClusterPt.{u1, u2} α _inst_1 ι x F u) (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α _inst_1 x)) -> (Filter.Frequently.{u2} ι (fun (a : ι) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (u a) s) F))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {ι : Type.{u1}} (x : α) (F : Filter.{u1} ι) (u : ι -> α), Iff (MapClusterPt.{u2, u1} α _inst_1 ι x F u) (forall (s : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s (nhds.{u2} α _inst_1 x)) -> (Filter.Frequently.{u1} ι (fun (a : ι) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (u a) s) F))
Case conversion may be inaccurate. Consider using '#align map_cluster_pt_iff mapClusterPt_iffₓ'. -/
theorem mapClusterPt_iff {ι : Type _} (x : α) (F : Filter ι) (u : ι → α) :
    MapClusterPt x F u ↔ ∀ s ∈ 𝓝 x, ∃ᶠ a in F, u a ∈ s :=
  by
  simp_rw [MapClusterPt, ClusterPt, inf_ne_bot_iff_frequently_left, frequently_map]
  rfl
#align map_cluster_pt_iff mapClusterPt_iff

/- warning: map_cluster_pt_of_comp -> mapClusterPt_of_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Type.{u2}} {δ : Type.{u3}} {F : Filter.{u2} ι} {φ : δ -> ι} {p : Filter.{u3} δ} {x : α} {u : ι -> α} [_inst_2 : Filter.NeBot.{u3} δ p], (Filter.Tendsto.{u3, u2} δ ι φ p F) -> (Filter.Tendsto.{u3, u1} δ α (Function.comp.{succ u3, succ u2, succ u1} δ ι α u φ) p (nhds.{u1} α _inst_1 x)) -> (MapClusterPt.{u1, u2} α _inst_1 ι x F u)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {ι : Type.{u2}} {δ : Type.{u1}} {F : Filter.{u2} ι} {φ : δ -> ι} {p : Filter.{u1} δ} {x : α} {u : ι -> α} [_inst_2 : Filter.NeBot.{u1} δ p], (Filter.Tendsto.{u1, u2} δ ι φ p F) -> (Filter.Tendsto.{u1, u3} δ α (Function.comp.{succ u1, succ u2, succ u3} δ ι α u φ) p (nhds.{u3} α _inst_1 x)) -> (MapClusterPt.{u3, u2} α _inst_1 ι x F u)
Case conversion may be inaccurate. Consider using '#align map_cluster_pt_of_comp mapClusterPt_of_compₓ'. -/
theorem mapClusterPt_of_comp {ι δ : Type _} {F : Filter ι} {φ : δ → ι} {p : Filter δ} {x : α}
    {u : ι → α} [NeBot p] (h : Tendsto φ p F) (H : Tendsto (u ∘ φ) p (𝓝 x)) : MapClusterPt x F u :=
  by
  have :=
    calc
      map (u ∘ φ) p = map u (map φ p) := map_map
      _ ≤ map u F := map_mono h
      
  have : map (u ∘ φ) p ≤ 𝓝 x ⊓ map u F := le_inf H this
  exact ne_bot_of_le this
#align map_cluster_pt_of_comp mapClusterPt_of_comp

#print AccPt /-
/-- A point `x` is an accumulation point of a filter `F` if `𝓝[≠] x ⊓ F ≠ ⊥`.-/
def AccPt (x : α) (F : Filter α) : Prop :=
  NeBot (𝓝[≠] x ⊓ F)
#align acc_pt AccPt
-/

/- warning: acc_iff_cluster -> acc_iff_cluster is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (x : α) (F : Filter.{u1} α), Iff (AccPt.{u1} α _inst_1 x F) (ClusterPt.{u1} α _inst_1 x (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) (Filter.principal.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))) F))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (x : α) (F : Filter.{u1} α), Iff (AccPt.{u1} α _inst_1 x F) (ClusterPt.{u1} α _inst_1 x (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) (Filter.principal.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x))) F))
Case conversion may be inaccurate. Consider using '#align acc_iff_cluster acc_iff_clusterₓ'. -/
theorem acc_iff_cluster (x : α) (F : Filter α) : AccPt x F ↔ ClusterPt x (𝓟 ({x}ᶜ) ⊓ F) := by
  rw [AccPt, nhdsWithin, ClusterPt, inf_assoc]
#align acc_iff_cluster acc_iff_cluster

/- warning: acc_principal_iff_cluster -> acc_principal_iff_cluster is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (x : α) (C : Set.{u1} α), Iff (AccPt.{u1} α _inst_1 x (Filter.principal.{u1} α C)) (ClusterPt.{u1} α _inst_1 x (Filter.principal.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) C (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (x : α) (C : Set.{u1} α), Iff (AccPt.{u1} α _inst_1 x (Filter.principal.{u1} α C)) (ClusterPt.{u1} α _inst_1 x (Filter.principal.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) C (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x))))
Case conversion may be inaccurate. Consider using '#align acc_principal_iff_cluster acc_principal_iff_clusterₓ'. -/
/-- `x` is an accumulation point of a set `C` iff it is a cluster point of `C ∖ {x}`.-/
theorem acc_principal_iff_cluster (x : α) (C : Set α) : AccPt x (𝓟 C) ↔ ClusterPt x (𝓟 (C \ {x})) :=
  by rw [acc_iff_cluster, inf_principal, inter_comm] <;> rfl
#align acc_principal_iff_cluster acc_principal_iff_cluster

/- warning: acc_pt_iff_nhds -> accPt_iff_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (x : α) (C : Set.{u1} α), Iff (AccPt.{u1} α _inst_1 x (Filter.principal.{u1} α C)) (forall (U : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U (nhds.{u1} α _inst_1 x)) -> (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) U C)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) U C)) => Ne.{succ u1} α y x))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (x : α) (C : Set.{u1} α), Iff (AccPt.{u1} α _inst_1 x (Filter.principal.{u1} α C)) (forall (U : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) U (nhds.{u1} α _inst_1 x)) -> (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) U C)) (Ne.{succ u1} α y x))))
Case conversion may be inaccurate. Consider using '#align acc_pt_iff_nhds accPt_iff_nhdsₓ'. -/
/-- `x` is an accumulation point of a set `C` iff every neighborhood
of `x` contains a point of `C` other than `x`. -/
theorem accPt_iff_nhds (x : α) (C : Set α) : AccPt x (𝓟 C) ↔ ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ C, y ≠ x := by
  simp [acc_principal_iff_cluster, clusterPt_principal_iff, Set.Nonempty, exists_prop, and_assoc',
    and_comm' ¬_ = x]
#align acc_pt_iff_nhds accPt_iff_nhds

#print accPt_iff_frequently /-
/-- `x` is an accumulation point of a set `C` iff
there are points near `x` in `C` and different from `x`.-/
theorem accPt_iff_frequently (x : α) (C : Set α) : AccPt x (𝓟 C) ↔ ∃ᶠ y in 𝓝 x, y ≠ x ∧ y ∈ C := by
  simp [acc_principal_iff_cluster, clusterPt_principal_iff_frequently, and_comm']
#align acc_pt_iff_frequently accPt_iff_frequently
-/

/- warning: acc_pt.mono -> AccPt.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {F : Filter.{u1} α} {G : Filter.{u1} α}, (AccPt.{u1} α _inst_1 x F) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) F G) -> (AccPt.{u1} α _inst_1 x G)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {F : Filter.{u1} α} {G : Filter.{u1} α}, (AccPt.{u1} α _inst_1 x F) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) F G) -> (AccPt.{u1} α _inst_1 x G)
Case conversion may be inaccurate. Consider using '#align acc_pt.mono AccPt.monoₓ'. -/
/-- If `x` is an accumulation point of `F` and `F ≤ G`, then
`x` is an accumulation point of `D. -/
theorem AccPt.mono {x : α} {F G : Filter α} (h : AccPt x F) (hFG : F ≤ G) : AccPt x G :=
  ⟨ne_bot_of_le_ne_bot h.Ne (inf_le_inf_left _ hFG)⟩
#align acc_pt.mono AccPt.mono

/-!
### Interior, closure and frontier in terms of neighborhoods
-/


#print interior_eq_nhds' /-
theorem interior_eq_nhds' {s : Set α} : interior s = { a | s ∈ 𝓝 a } :=
  Set.ext fun x => by simp only [mem_interior, mem_nhds_iff, mem_set_of_eq]
#align interior_eq_nhds' interior_eq_nhds'
-/

/- warning: interior_eq_nhds -> interior_eq_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 s) (setOf.{u1} α (fun (a : α) => LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (nhds.{u1} α _inst_1 a) (Filter.principal.{u1} α s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 s) (setOf.{u1} α (fun (a : α) => LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (nhds.{u1} α _inst_1 a) (Filter.principal.{u1} α s)))
Case conversion may be inaccurate. Consider using '#align interior_eq_nhds interior_eq_nhdsₓ'. -/
theorem interior_eq_nhds {s : Set α} : interior s = { a | 𝓝 a ≤ 𝓟 s } :=
  interior_eq_nhds'.trans <| by simp only [le_principal_iff]
#align interior_eq_nhds interior_eq_nhds

#print mem_interior_iff_mem_nhds /-
theorem mem_interior_iff_mem_nhds {s : Set α} {a : α} : a ∈ interior s ↔ s ∈ 𝓝 a := by
  rw [interior_eq_nhds', mem_set_of_eq]
#align mem_interior_iff_mem_nhds mem_interior_iff_mem_nhds
-/

#print interior_mem_nhds /-
@[simp]
theorem interior_mem_nhds {s : Set α} {a : α} : interior s ∈ 𝓝 a ↔ s ∈ 𝓝 a :=
  ⟨fun h => mem_of_superset h interior_subset, fun h =>
    IsOpen.mem_nhds isOpen_interior (mem_interior_iff_mem_nhds.2 h)⟩
#align interior_mem_nhds interior_mem_nhds
-/

#print interior_setOf_eq /-
theorem interior_setOf_eq {p : α → Prop} : interior { x | p x } = { x | ∀ᶠ y in 𝓝 x, p y } :=
  interior_eq_nhds'
#align interior_set_of_eq interior_setOf_eq
-/

#print isOpen_setOf_eventually_nhds /-
theorem isOpen_setOf_eventually_nhds {p : α → Prop} : IsOpen { x | ∀ᶠ y in 𝓝 x, p y } := by
  simp only [← interior_setOf_eq, isOpen_interior]
#align is_open_set_of_eventually_nhds isOpen_setOf_eventually_nhds
-/

#print subset_interior_iff_nhds /-
theorem subset_interior_iff_nhds {s V : Set α} : s ⊆ interior V ↔ ∀ x ∈ s, V ∈ 𝓝 x :=
  show (∀ x, x ∈ s → x ∈ _) ↔ _ by simp_rw [mem_interior_iff_mem_nhds]
#align subset_interior_iff_nhds subset_interior_iff_nhds
-/

/- warning: is_open_iff_nhds -> isOpen_iff_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Iff (IsOpen.{u1} α _inst_1 s) (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (nhds.{u1} α _inst_1 a) (Filter.principal.{u1} α s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Iff (IsOpen.{u1} α _inst_1 s) (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (nhds.{u1} α _inst_1 a) (Filter.principal.{u1} α s)))
Case conversion may be inaccurate. Consider using '#align is_open_iff_nhds isOpen_iff_nhdsₓ'. -/
theorem isOpen_iff_nhds {s : Set α} : IsOpen s ↔ ∀ a ∈ s, 𝓝 a ≤ 𝓟 s :=
  calc
    IsOpen s ↔ s ⊆ interior s := subset_interior_iff_isOpen.symm
    _ ↔ ∀ a ∈ s, 𝓝 a ≤ 𝓟 s := by rw [interior_eq_nhds] <;> rfl
    
#align is_open_iff_nhds isOpen_iff_nhds

#print isOpen_iff_mem_nhds /-
theorem isOpen_iff_mem_nhds {s : Set α} : IsOpen s ↔ ∀ a ∈ s, s ∈ 𝓝 a :=
  isOpen_iff_nhds.trans <| forall_congr' fun _ => imp_congr_right fun _ => le_principal_iff
#align is_open_iff_mem_nhds isOpen_iff_mem_nhds
-/

#print isOpen_iff_eventually /-
/-- A set `s` is open iff for every point `x` in `s` and every `y` close to `x`, `y` is in `s`. -/
theorem isOpen_iff_eventually {s : Set α} : IsOpen s ↔ ∀ x, x ∈ s → ∀ᶠ y in 𝓝 x, y ∈ s :=
  isOpen_iff_mem_nhds
#align is_open_iff_eventually isOpen_iff_eventually
-/

/- warning: is_open_iff_ultrafilter -> isOpen_iff_ultrafilter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Iff (IsOpen.{u1} α _inst_1 s) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (l : Ultrafilter.{u1} α), (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) l) (nhds.{u1} α _inst_1 x)) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Ultrafilter.{u1} α) (Ultrafilter.hasMem.{u1} α) s l)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Iff (IsOpen.{u1} α _inst_1 s) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (l : Ultrafilter.{u1} α), (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Ultrafilter.toFilter.{u1} α l) (nhds.{u1} α _inst_1 x)) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Ultrafilter.{u1} α) (Ultrafilter.instMembershipSetUltrafilter.{u1} α) s l)))
Case conversion may be inaccurate. Consider using '#align is_open_iff_ultrafilter isOpen_iff_ultrafilterₓ'. -/
theorem isOpen_iff_ultrafilter {s : Set α} :
    IsOpen s ↔ ∀ x ∈ s, ∀ (l : Ultrafilter α), ↑l ≤ 𝓝 x → s ∈ l := by
  simp_rw [isOpen_iff_mem_nhds, ← mem_iff_ultrafilter]
#align is_open_iff_ultrafilter isOpen_iff_ultrafilter

#print isOpen_singleton_iff_nhds_eq_pure /-
theorem isOpen_singleton_iff_nhds_eq_pure (a : α) : IsOpen ({a} : Set α) ↔ 𝓝 a = pure a :=
  by
  constructor
  · intro h
    apply le_antisymm _ (pure_le_nhds a)
    rw [le_pure_iff]
    exact h.mem_nhds (mem_singleton a)
  · intro h
    simp [isOpen_iff_nhds, h]
#align is_open_singleton_iff_nhds_eq_pure isOpen_singleton_iff_nhds_eq_pure
-/

/- warning: is_open_singleton_iff_punctured_nhds -> isOpen_singleton_iff_punctured_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} α] (a : α), Iff (IsOpen.{u1} α _inst_2 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) (Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_2 a (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a))) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} α] (a : α), Iff (IsOpen.{u1} α _inst_2 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) (Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_2 a (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a))) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))
Case conversion may be inaccurate. Consider using '#align is_open_singleton_iff_punctured_nhds isOpen_singleton_iff_punctured_nhdsₓ'. -/
theorem isOpen_singleton_iff_punctured_nhds {α : Type _} [TopologicalSpace α] (a : α) :
    IsOpen ({a} : Set α) ↔ 𝓝[≠] a = ⊥ := by
  rw [isOpen_singleton_iff_nhds_eq_pure, nhdsWithin, ← mem_iff_inf_principal_compl, ← le_pure_iff,
    nhds_ne_bot.le_pure_iff]
#align is_open_singleton_iff_punctured_nhds isOpen_singleton_iff_punctured_nhds

#print mem_closure_iff_frequently /-
theorem mem_closure_iff_frequently {s : Set α} {a : α} : a ∈ closure s ↔ ∃ᶠ x in 𝓝 a, x ∈ s := by
  rw [Filter.Frequently, Filter.Eventually, ← mem_interior_iff_mem_nhds,
      closure_eq_compl_interior_compl] <;>
    rfl
#align mem_closure_iff_frequently mem_closure_iff_frequently
-/

alias mem_closure_iff_frequently ↔ _ Filter.Frequently.mem_closure
#align filter.frequently.mem_closure Filter.Frequently.mem_closure

#print isClosed_iff_frequently /-
/-- A set `s` is closed iff for every point `x`, if there is a point `y` close to `x` that belongs
to `s` then `x` is in `s`. -/
theorem isClosed_iff_frequently {s : Set α} : IsClosed s ↔ ∀ x, (∃ᶠ y in 𝓝 x, y ∈ s) → x ∈ s :=
  by
  rw [← closure_subset_iff_isClosed]
  apply forall_congr' fun x => _
  rw [mem_closure_iff_frequently]
#align is_closed_iff_frequently isClosed_iff_frequently
-/

#print isClosed_setOf_clusterPt /-
/-- The set of cluster points of a filter is closed. In particular, the set of limit points
of a sequence is closed. -/
theorem isClosed_setOf_clusterPt {f : Filter α} : IsClosed { x | ClusterPt x f } :=
  by
  simp only [ClusterPt, inf_ne_bot_iff_frequently_left, set_of_forall, imp_iff_not_or]
  refine' isClosed_interᵢ fun p => IsClosed.union _ _ <;> apply isClosed_compl_iff.2
  exacts[isOpen_setOf_eventually_nhds, isOpen_const]
#align is_closed_set_of_cluster_pt isClosed_setOf_clusterPt
-/

#print mem_closure_iff_clusterPt /-
theorem mem_closure_iff_clusterPt {s : Set α} {a : α} : a ∈ closure s ↔ ClusterPt a (𝓟 s) :=
  mem_closure_iff_frequently.trans clusterPt_principal_iff_frequently.symm
#align mem_closure_iff_cluster_pt mem_closure_iff_clusterPt
-/

/- warning: mem_closure_iff_nhds_ne_bot -> mem_closure_iff_nhds_neBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (closure.{u1} α _inst_1 s)) (Ne.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) (nhds.{u1} α _inst_1 a) (Filter.principal.{u1} α s)) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} {a : α} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (closure.{u1} α _inst_1 s)) (Ne.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) (nhds.{u1} α _inst_1 a) (Filter.principal.{u1} α s)) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))
Case conversion may be inaccurate. Consider using '#align mem_closure_iff_nhds_ne_bot mem_closure_iff_nhds_neBotₓ'. -/
theorem mem_closure_iff_nhds_neBot {s : Set α} : a ∈ closure s ↔ 𝓝 a ⊓ 𝓟 s ≠ ⊥ :=
  mem_closure_iff_clusterPt.trans neBot_iff
#align mem_closure_iff_nhds_ne_bot mem_closure_iff_nhds_neBot

#print mem_closure_iff_nhdsWithin_neBot /-
theorem mem_closure_iff_nhdsWithin_neBot {s : Set α} {x : α} : x ∈ closure s ↔ NeBot (𝓝[s] x) :=
  mem_closure_iff_clusterPt
#align mem_closure_iff_nhds_within_ne_bot mem_closure_iff_nhdsWithin_neBot
-/

/- warning: dense_compl_singleton -> dense_compl_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (x : α) [_inst_2 : Filter.NeBot.{u1} α (nhdsWithin.{u1} α _inst_1 x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)))], Dense.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (x : α) [_inst_2 : Filter.NeBot.{u1} α (nhdsWithin.{u1} α _inst_1 x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)))], Dense.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x))
Case conversion may be inaccurate. Consider using '#align dense_compl_singleton dense_compl_singletonₓ'. -/
/-- If `x` is not an isolated point of a topological space, then `{x}ᶜ` is dense in the whole
space. -/
theorem dense_compl_singleton (x : α) [NeBot (𝓝[≠] x)] : Dense ({x}ᶜ : Set α) :=
  by
  intro y
  rcases eq_or_ne y x with (rfl | hne)
  · rwa [mem_closure_iff_nhdsWithin_neBot]
  · exact subset_closure hne
#align dense_compl_singleton dense_compl_singleton

/- warning: closure_compl_singleton -> closure_compl_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (x : α) [_inst_2 : Filter.NeBot.{u1} α (nhdsWithin.{u1} α _inst_1 x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)))], Eq.{succ u1} (Set.{u1} α) (closure.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (x : α) [_inst_2 : Filter.NeBot.{u1} α (nhdsWithin.{u1} α _inst_1 x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)))], Eq.{succ u1} (Set.{u1} α) (closure.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x))) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align closure_compl_singleton closure_compl_singletonₓ'. -/
/-- If `x` is not an isolated point of a topological space, then the closure of `{x}ᶜ` is the whole
space. -/
@[simp]
theorem closure_compl_singleton (x : α) [NeBot (𝓝[≠] x)] : closure ({x}ᶜ) = (univ : Set α) :=
  (dense_compl_singleton x).closure_eq
#align closure_compl_singleton closure_compl_singleton

/- warning: interior_singleton -> interior_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (x : α) [_inst_2 : Filter.NeBot.{u1} α (nhdsWithin.{u1} α _inst_1 x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)))], Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (x : α) [_inst_2 : Filter.NeBot.{u1} α (nhdsWithin.{u1} α _inst_1 x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)))], Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align interior_singleton interior_singletonₓ'. -/
/-- If `x` is not an isolated point of a topological space, then the interior of `{x}` is empty. -/
@[simp]
theorem interior_singleton (x : α) [NeBot (𝓝[≠] x)] : interior {x} = (∅ : Set α) :=
  interior_eq_empty_iff_dense_compl.2 (dense_compl_singleton x)
#align interior_singleton interior_singleton

/- warning: not_is_open_singleton -> not_isOpen_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (x : α) [_inst_2 : Filter.NeBot.{u1} α (nhdsWithin.{u1} α _inst_1 x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)))], Not (IsOpen.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (x : α) [_inst_2 : Filter.NeBot.{u1} α (nhdsWithin.{u1} α _inst_1 x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)))], Not (IsOpen.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x))
Case conversion may be inaccurate. Consider using '#align not_is_open_singleton not_isOpen_singletonₓ'. -/
theorem not_isOpen_singleton (x : α) [NeBot (𝓝[≠] x)] : ¬IsOpen ({x} : Set α) :=
  dense_compl_singleton_iff_not_open.1 (dense_compl_singleton x)
#align not_is_open_singleton not_isOpen_singleton

#print closure_eq_cluster_pts /-
theorem closure_eq_cluster_pts {s : Set α} : closure s = { a | ClusterPt a (𝓟 s) } :=
  Set.ext fun x => mem_closure_iff_clusterPt
#align closure_eq_cluster_pts closure_eq_cluster_pts
-/

/- warning: mem_closure_iff_nhds -> mem_closure_iff_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {a : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (closure.{u1} α _inst_1 s)) (forall (t : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t (nhds.{u1} α _inst_1 a)) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {a : α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (closure.{u1} α _inst_1 s)) (forall (t : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t (nhds.{u1} α _inst_1 a)) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s)))
Case conversion may be inaccurate. Consider using '#align mem_closure_iff_nhds mem_closure_iff_nhdsₓ'. -/
theorem mem_closure_iff_nhds {s : Set α} {a : α} : a ∈ closure s ↔ ∀ t ∈ 𝓝 a, (t ∩ s).Nonempty :=
  mem_closure_iff_clusterPt.trans clusterPt_principal_iff
#align mem_closure_iff_nhds mem_closure_iff_nhds

#print mem_closure_iff_nhds' /-
theorem mem_closure_iff_nhds' {s : Set α} {a : α} : a ∈ closure s ↔ ∀ t ∈ 𝓝 a, ∃ y : s, ↑y ∈ t := by
  simp only [mem_closure_iff_nhds, Set.inter_nonempty_iff_exists_right, SetCoe.exists,
    Subtype.coe_mk]
#align mem_closure_iff_nhds' mem_closure_iff_nhds'
-/

#print mem_closure_iff_comap_neBot /-
theorem mem_closure_iff_comap_neBot {A : Set α} {x : α} :
    x ∈ closure A ↔ NeBot (comap (coe : A → α) (𝓝 x)) := by
  simp_rw [mem_closure_iff_nhds, comap_ne_bot_iff, Set.inter_nonempty_iff_exists_right,
    SetCoe.exists, Subtype.coe_mk]
#align mem_closure_iff_comap_ne_bot mem_closure_iff_comap_neBot
-/

/- warning: mem_closure_iff_nhds_basis' -> mem_closure_iff_nhds_basis' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι (nhds.{u1} α _inst_1 a) p s) -> (forall {t : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (closure.{u1} α _inst_1 t)) (forall (i : ι), (p i) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (s i) t))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι (nhds.{u1} α _inst_1 a) p s) -> (forall {t : Set.{u1} α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (closure.{u1} α _inst_1 t)) (forall (i : ι), (p i) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (s i) t))))
Case conversion may be inaccurate. Consider using '#align mem_closure_iff_nhds_basis' mem_closure_iff_nhds_basis'ₓ'. -/
theorem mem_closure_iff_nhds_basis' {a : α} {p : ι → Prop} {s : ι → Set α} (h : (𝓝 a).HasBasis p s)
    {t : Set α} : a ∈ closure t ↔ ∀ i, p i → (s i ∩ t).Nonempty :=
  mem_closure_iff_clusterPt.trans <|
    (h.cluster_pt_iff (hasBasis_principal _)).trans <| by simp only [exists_prop, forall_const]
#align mem_closure_iff_nhds_basis' mem_closure_iff_nhds_basis'

/- warning: mem_closure_iff_nhds_basis -> mem_closure_iff_nhds_basis is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι (nhds.{u1} α _inst_1 a) p s) -> (forall {t : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (closure.{u1} α _inst_1 t)) (forall (i : ι), (p i) -> (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (s i))))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {a : α} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι (nhds.{u1} α _inst_1 a) p s) -> (forall {t : Set.{u1} α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (closure.{u1} α _inst_1 t)) (forall (i : ι), (p i) -> (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (s i))))))
Case conversion may be inaccurate. Consider using '#align mem_closure_iff_nhds_basis mem_closure_iff_nhds_basisₓ'. -/
theorem mem_closure_iff_nhds_basis {a : α} {p : ι → Prop} {s : ι → Set α} (h : (𝓝 a).HasBasis p s)
    {t : Set α} : a ∈ closure t ↔ ∀ i, p i → ∃ y ∈ t, y ∈ s i :=
  (mem_closure_iff_nhds_basis' h).trans <| by
    simp only [Set.Nonempty, mem_inter_iff, exists_prop, and_comm']
#align mem_closure_iff_nhds_basis mem_closure_iff_nhds_basis

/- warning: mem_closure_iff_ultrafilter -> mem_closure_iff_ultrafilter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {x : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α _inst_1 s)) (Exists.{succ u1} (Ultrafilter.{u1} α) (fun (u : Ultrafilter.{u1} α) => And (Membership.Mem.{u1, u1} (Set.{u1} α) (Ultrafilter.{u1} α) (Ultrafilter.hasMem.{u1} α) s u) (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) u) (nhds.{u1} α _inst_1 x))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {x : α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (closure.{u1} α _inst_1 s)) (Exists.{succ u1} (Ultrafilter.{u1} α) (fun (u : Ultrafilter.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Ultrafilter.{u1} α) (Ultrafilter.instMembershipSetUltrafilter.{u1} α) s u) (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Ultrafilter.toFilter.{u1} α u) (nhds.{u1} α _inst_1 x))))
Case conversion may be inaccurate. Consider using '#align mem_closure_iff_ultrafilter mem_closure_iff_ultrafilterₓ'. -/
/-- `x` belongs to the closure of `s` if and only if some ultrafilter
  supported on `s` converges to `x`. -/
theorem mem_closure_iff_ultrafilter {s : Set α} {x : α} :
    x ∈ closure s ↔ ∃ u : Ultrafilter α, s ∈ u ∧ ↑u ≤ 𝓝 x := by
  simp [closure_eq_cluster_pts, ClusterPt, ← exists_ultrafilter_iff, and_comm]
#align mem_closure_iff_ultrafilter mem_closure_iff_ultrafilter

#print isClosed_iff_clusterPt /-
theorem isClosed_iff_clusterPt {s : Set α} : IsClosed s ↔ ∀ a, ClusterPt a (𝓟 s) → a ∈ s :=
  calc
    IsClosed s ↔ closure s ⊆ s := closure_subset_iff_isClosed.symm
    _ ↔ ∀ a, ClusterPt a (𝓟 s) → a ∈ s := by simp only [subset_def, mem_closure_iff_clusterPt]
    
#align is_closed_iff_cluster_pt isClosed_iff_clusterPt
-/

/- warning: is_closed_iff_nhds -> isClosed_iff_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Iff (IsClosed.{u1} α _inst_1 s) (forall (x : α), (forall (U : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U (nhds.{u1} α _inst_1 x)) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) U s))) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, Iff (IsClosed.{u1} α _inst_1 s) (forall (x : α), (forall (U : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) U (nhds.{u1} α _inst_1 x)) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) U s))) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))
Case conversion may be inaccurate. Consider using '#align is_closed_iff_nhds isClosed_iff_nhdsₓ'. -/
theorem isClosed_iff_nhds {s : Set α} : IsClosed s ↔ ∀ x, (∀ U ∈ 𝓝 x, (U ∩ s).Nonempty) → x ∈ s :=
  by simp_rw [isClosed_iff_clusterPt, ClusterPt, inf_principal_ne_bot_iff]
#align is_closed_iff_nhds isClosed_iff_nhds

/- warning: is_closed.interior_union_left -> IsClosed.interior_union_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsClosed.{u1} α _inst_1 s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (interior.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s (interior.{u1} α _inst_1 t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsClosed.{u1} α _inst_1 s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (interior.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s (interior.{u1} α _inst_1 t)))
Case conversion may be inaccurate. Consider using '#align is_closed.interior_union_left IsClosed.interior_union_leftₓ'. -/
theorem IsClosed.interior_union_left {s t : Set α} (h : IsClosed s) :
    interior (s ∪ t) ⊆ s ∪ interior t := fun a ⟨u, ⟨⟨hu₁, hu₂⟩, ha⟩⟩ =>
  (Classical.em (a ∈ s)).imp_right fun h =>
    mem_interior.mpr
      ⟨u ∩ sᶜ, fun x hx => (hu₂ hx.1).resolve_left hx.2, IsOpen.inter hu₁ IsClosed.isOpen_compl,
        ⟨ha, h⟩⟩
#align is_closed.interior_union_left IsClosed.interior_union_left

/- warning: is_closed.interior_union_right -> IsClosed.interior_union_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsClosed.{u1} α _inst_1 t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (interior.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (interior.{u1} α _inst_1 s) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsClosed.{u1} α _inst_1 t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (interior.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (interior.{u1} α _inst_1 s) t))
Case conversion may be inaccurate. Consider using '#align is_closed.interior_union_right IsClosed.interior_union_rightₓ'. -/
theorem IsClosed.interior_union_right {s t : Set α} (h : IsClosed t) :
    interior (s ∪ t) ⊆ interior s ∪ t := by simpa only [union_comm] using h.interior_union_left
#align is_closed.interior_union_right IsClosed.interior_union_right

/- warning: is_open.inter_closure -> IsOpen.inter_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (closure.{u1} α _inst_1 t)) (closure.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (closure.{u1} α _inst_1 t)) (closure.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)))
Case conversion may be inaccurate. Consider using '#align is_open.inter_closure IsOpen.inter_closureₓ'. -/
theorem IsOpen.inter_closure {s t : Set α} (h : IsOpen s) : s ∩ closure t ⊆ closure (s ∩ t) :=
  compl_subset_compl.mp <| by
    simpa only [← interior_compl, compl_inter] using IsClosed.interior_union_left h.is_closed_compl
#align is_open.inter_closure IsOpen.inter_closure

/- warning: is_open.closure_inter -> IsOpen.closure_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (closure.{u1} α _inst_1 s) t) (closure.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (closure.{u1} α _inst_1 s) t) (closure.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)))
Case conversion may be inaccurate. Consider using '#align is_open.closure_inter IsOpen.closure_interₓ'. -/
theorem IsOpen.closure_inter {s t : Set α} (h : IsOpen t) : closure s ∩ t ⊆ closure (s ∩ t) := by
  simpa only [inter_comm] using h.inter_closure
#align is_open.closure_inter IsOpen.closure_inter

/- warning: dense.open_subset_closure_inter -> Dense.open_subset_closure_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Dense.{u1} α _inst_1 s) -> (IsOpen.{u1} α _inst_1 t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t (closure.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Dense.{u1} α _inst_1 s) -> (IsOpen.{u1} α _inst_1 t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t (closure.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s)))
Case conversion may be inaccurate. Consider using '#align dense.open_subset_closure_inter Dense.open_subset_closure_interₓ'. -/
theorem Dense.open_subset_closure_inter {s t : Set α} (hs : Dense s) (ht : IsOpen t) :
    t ⊆ closure (t ∩ s) :=
  calc
    t = t ∩ closure s := by rw [hs.closure_eq, inter_univ]
    _ ⊆ closure (t ∩ s) := ht.inter_closure
    
#align dense.open_subset_closure_inter Dense.open_subset_closure_inter

/- warning: mem_closure_of_mem_closure_union -> mem_closure_of_mem_closure_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂))) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s₁) (nhds.{u1} α _inst_1 x)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α _inst_1 s₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (closure.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂))) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s₁) (nhds.{u1} α _inst_1 x)) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (closure.{u1} α _inst_1 s₂))
Case conversion may be inaccurate. Consider using '#align mem_closure_of_mem_closure_union mem_closure_of_mem_closure_unionₓ'. -/
theorem mem_closure_of_mem_closure_union {s₁ s₂ : Set α} {x : α} (h : x ∈ closure (s₁ ∪ s₂))
    (h₁ : s₁ᶜ ∈ 𝓝 x) : x ∈ closure s₂ :=
  by
  rw [mem_closure_iff_nhds_neBot] at *
  rwa [←
    calc
      𝓝 x ⊓ principal (s₁ ∪ s₂) = 𝓝 x ⊓ (principal s₁ ⊔ principal s₂) := by rw [sup_principal]
      _ = 𝓝 x ⊓ principal s₁ ⊔ 𝓝 x ⊓ principal s₂ := inf_sup_left
      _ = ⊥ ⊔ 𝓝 x ⊓ principal s₂ := by rw [inf_principal_eq_bot.mpr h₁]
      _ = 𝓝 x ⊓ principal s₂ := bot_sup_eq
      ]
#align mem_closure_of_mem_closure_union mem_closure_of_mem_closure_union

/- warning: dense.inter_of_open_left -> Dense.inter_of_open_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Dense.{u1} α _inst_1 s) -> (Dense.{u1} α _inst_1 t) -> (IsOpen.{u1} α _inst_1 s) -> (Dense.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Dense.{u1} α _inst_1 s) -> (Dense.{u1} α _inst_1 t) -> (IsOpen.{u1} α _inst_1 s) -> (Dense.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align dense.inter_of_open_left Dense.inter_of_open_leftₓ'. -/
/-- The intersection of an open dense set with a dense set is a dense set. -/
theorem Dense.inter_of_open_left {s t : Set α} (hs : Dense s) (ht : Dense t) (hso : IsOpen s) :
    Dense (s ∩ t) := fun x =>
  closure_minimal hso.inter_closure isClosed_closure <| by simp [hs.closure_eq, ht.closure_eq]
#align dense.inter_of_open_left Dense.inter_of_open_left

/- warning: dense.inter_of_open_right -> Dense.inter_of_open_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Dense.{u1} α _inst_1 s) -> (Dense.{u1} α _inst_1 t) -> (IsOpen.{u1} α _inst_1 t) -> (Dense.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Dense.{u1} α _inst_1 s) -> (Dense.{u1} α _inst_1 t) -> (IsOpen.{u1} α _inst_1 t) -> (Dense.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align dense.inter_of_open_right Dense.inter_of_open_rightₓ'. -/
/-- The intersection of a dense set with an open dense set is a dense set. -/
theorem Dense.inter_of_open_right {s t : Set α} (hs : Dense s) (ht : Dense t) (hto : IsOpen t) :
    Dense (s ∩ t) :=
  inter_comm t s ▸ ht.inter_of_open_left hs hto
#align dense.inter_of_open_right Dense.inter_of_open_right

/- warning: dense.inter_nhds_nonempty -> Dense.inter_nhds_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Dense.{u1} α _inst_1 s) -> (forall {x : α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t (nhds.{u1} α _inst_1 x)) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Dense.{u1} α _inst_1 s) -> (forall {x : α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t (nhds.{u1} α _inst_1 x)) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)))
Case conversion may be inaccurate. Consider using '#align dense.inter_nhds_nonempty Dense.inter_nhds_nonemptyₓ'. -/
theorem Dense.inter_nhds_nonempty {s t : Set α} (hs : Dense s) {x : α} (ht : t ∈ 𝓝 x) :
    (s ∩ t).Nonempty :=
  let ⟨U, hsub, ho, hx⟩ := mem_nhds_iff.1 ht
  (hs.inter_open_nonempty U ho ⟨x, hx⟩).mono fun y hy => ⟨hy.2, hsub hy.1⟩
#align dense.inter_nhds_nonempty Dense.inter_nhds_nonempty

/- warning: closure_diff -> closure_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (closure.{u1} α _inst_1 s) (closure.{u1} α _inst_1 t)) (closure.{u1} α _inst_1 (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (closure.{u1} α _inst_1 s) (closure.{u1} α _inst_1 t)) (closure.{u1} α _inst_1 (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align closure_diff closure_diffₓ'. -/
theorem closure_diff {s t : Set α} : closure s \ closure t ⊆ closure (s \ t) :=
  calc
    closure s \ closure t = closure tᶜ ∩ closure s := by simp only [diff_eq, inter_comm]
    _ ⊆ closure (closure tᶜ ∩ s) := (isOpen_compl_iff.mpr <| isClosed_closure).inter_closure
    _ = closure (s \ closure t) := by simp only [diff_eq, inter_comm]
    _ ⊆ closure (s \ t) := closure_mono <| diff_subset_diff (Subset.refl s) subset_closure
    
#align closure_diff closure_diff

#print Filter.Frequently.mem_of_closed /-
theorem Filter.Frequently.mem_of_closed {a : α} {s : Set α} (h : ∃ᶠ x in 𝓝 a, x ∈ s)
    (hs : IsClosed s) : a ∈ s :=
  hs.closure_subset h.mem_closure
#align filter.frequently.mem_of_closed Filter.Frequently.mem_of_closed
-/

#print IsClosed.mem_of_frequently_of_tendsto /-
theorem IsClosed.mem_of_frequently_of_tendsto {f : β → α} {b : Filter β} {a : α} {s : Set α}
    (hs : IsClosed s) (h : ∃ᶠ x in b, f x ∈ s) (hf : Tendsto f b (𝓝 a)) : a ∈ s :=
  (hf.Frequently <| show ∃ᶠ x in b, (fun y => y ∈ s) (f x) from h).mem_of_closed hs
#align is_closed.mem_of_frequently_of_tendsto IsClosed.mem_of_frequently_of_tendsto
-/

#print IsClosed.mem_of_tendsto /-
theorem IsClosed.mem_of_tendsto {f : β → α} {b : Filter β} {a : α} {s : Set α} [NeBot b]
    (hs : IsClosed s) (hf : Tendsto f b (𝓝 a)) (h : ∀ᶠ x in b, f x ∈ s) : a ∈ s :=
  hs.mem_of_frequently_of_tendsto h.Frequently hf
#align is_closed.mem_of_tendsto IsClosed.mem_of_tendsto
-/

#print mem_closure_of_frequently_of_tendsto /-
theorem mem_closure_of_frequently_of_tendsto {f : β → α} {b : Filter β} {a : α} {s : Set α}
    (h : ∃ᶠ x in b, f x ∈ s) (hf : Tendsto f b (𝓝 a)) : a ∈ closure s :=
  Filter.Frequently.mem_closure <| hf.Frequently h
#align mem_closure_of_frequently_of_tendsto mem_closure_of_frequently_of_tendsto
-/

#print mem_closure_of_tendsto /-
theorem mem_closure_of_tendsto {f : β → α} {b : Filter β} {a : α} {s : Set α} [NeBot b]
    (hf : Tendsto f b (𝓝 a)) (h : ∀ᶠ x in b, f x ∈ s) : a ∈ closure s :=
  mem_closure_of_frequently_of_tendsto h.Frequently hf
#align mem_closure_of_tendsto mem_closure_of_tendsto
-/

/- warning: tendsto_inf_principal_nhds_iff_of_forall_eq -> tendsto_inf_principal_nhds_iff_of_forall_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {f : β -> α} {l : Filter.{u2} β} {s : Set.{u2} β} {a : α}, (forall (x : β), (Not (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s)) -> (Eq.{succ u1} α (f x) a)) -> (Iff (Filter.Tendsto.{u2, u1} β α f (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) l (Filter.principal.{u2} β s)) (nhds.{u1} α _inst_1 a)) (Filter.Tendsto.{u2, u1} β α f l (nhds.{u1} α _inst_1 a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {f : β -> α} {l : Filter.{u2} β} {s : Set.{u2} β} {a : α}, (forall (x : β), (Not (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s)) -> (Eq.{succ u1} α (f x) a)) -> (Iff (Filter.Tendsto.{u2, u1} β α f (HasInf.inf.{u2} (Filter.{u2} β) (Filter.instHasInfFilter.{u2} β) l (Filter.principal.{u2} β s)) (nhds.{u1} α _inst_1 a)) (Filter.Tendsto.{u2, u1} β α f l (nhds.{u1} α _inst_1 a)))
Case conversion may be inaccurate. Consider using '#align tendsto_inf_principal_nhds_iff_of_forall_eq tendsto_inf_principal_nhds_iff_of_forall_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x «expr ∉ » s) -/
/-- Suppose that `f` sends the complement to `s` to a single point `a`, and `l` is some filter.
Then `f` tends to `a` along `l` restricted to `s` if and only if it tends to `a` along `l`. -/
theorem tendsto_inf_principal_nhds_iff_of_forall_eq {f : β → α} {l : Filter β} {s : Set β} {a : α}
    (h : ∀ (x) (_ : x ∉ s), f x = a) : Tendsto f (l ⊓ 𝓟 s) (𝓝 a) ↔ Tendsto f l (𝓝 a) :=
  by
  rw [tendsto_iff_comap, tendsto_iff_comap]
  replace h : 𝓟 (sᶜ) ≤ comap f (𝓝 a)
  · rintro U ⟨t, ht, htU⟩ x hx
    have : f x ∈ t := (h x hx).symm ▸ mem_of_mem_nhds ht
    exact htU this
  refine' ⟨fun h' => _, le_trans inf_le_left⟩
  have := sup_le h' h
  rw [sup_inf_right, sup_principal, union_compl_self, principal_univ, inf_top_eq, sup_le_iff] at
    this
  exact this.1
#align tendsto_inf_principal_nhds_iff_of_forall_eq tendsto_inf_principal_nhds_iff_of_forall_eq

/-!
### Limits of filters in topological spaces
-/


section lim

#print lim /-
/-- If `f` is a filter, then `Lim f` is a limit of the filter, if it exists. -/
noncomputable def lim [Nonempty α] (f : Filter α) : α :=
  epsilon fun a => f ≤ 𝓝 a
#align Lim lim
-/

/-- If `f` is a filter satisfying `ne_bot f`, then `Lim' f` is a limit of the filter, if it exists.
-/
def lim' (f : Filter α) [NeBot f] : α :=
  @lim _ _ (nonempty_of_neBot f) f
#align Lim' lim'

#print Ultrafilter.lim /-
/--
If `F` is an ultrafilter, then `filter.ultrafilter.Lim F` is a limit of the filter, if it exists.
Note that dot notation `F.Lim` can be used for `F : ultrafilter α`.
-/
def Ultrafilter.lim : Ultrafilter α → α := fun F => lim' F
#align ultrafilter.Lim Ultrafilter.lim
-/

/- warning: lim clashes with Lim -> lim
warning: lim -> lim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : TopologicalSpace.{u} α] [_inst_2 : Nonempty.{succ u} α], (Filter.{v} β) -> (β -> α) -> α
but is expected to have type
  forall {α : Type.{u}} [β : TopologicalSpace.{u} α] [_inst_1 : Nonempty.{succ u} α], (Filter.{u} α) -> α
Case conversion may be inaccurate. Consider using '#align lim limₓ'. -/
/-- If `f` is a filter in `β` and `g : β → α` is a function, then `lim f` is a limit of `g` at `f`,
if it exists. -/
noncomputable def lim [Nonempty α] (f : Filter β) (g : β → α) : α :=
  lim (f.map g)
#align lim lim

/- warning: le_nhds_Lim -> le_nhds_lim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : Filter.{u1} α} (h : Exists.{succ u1} α (fun (a : α) => LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (nhds.{u1} α _inst_1 a))), LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (nhds.{u1} α _inst_1 (lim.{u1} α _inst_1 (nonempty_of_exists.{succ u1} α (fun (a : α) => LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f (nhds.{u1} α _inst_1 a)) h) f))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : Filter.{u1} α} (h : Exists.{succ u1} α (fun (a : α) => LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (nhds.{u1} α _inst_1 a))), LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (nhds.{u1} α _inst_1 (lim.{u1} α _inst_1 (nonempty_of_exists.{succ u1} α (fun (a : α) => LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f (nhds.{u1} α _inst_1 a)) h) f))
Case conversion may be inaccurate. Consider using '#align le_nhds_Lim le_nhds_limₓ'. -/
/-- If a filter `f` is majorated by some `𝓝 a`, then it is majorated by `𝓝 (Lim f)`. We formulate
this lemma with a `[nonempty α]` argument of `Lim` derived from `h` to make it useful for types
without a `[nonempty α]` instance. Because of the built-in proof irrelevance, Lean will unify
this instance with any other instance. -/
theorem le_nhds_lim {f : Filter α} (h : ∃ a, f ≤ 𝓝 a) : f ≤ 𝓝 (@lim _ _ (nonempty_of_exists h) f) :=
  epsilon_spec h
#align le_nhds_Lim le_nhds_lim

#print tendsto_nhds_limUnder /-
/-- If `g` tends to some `𝓝 a` along `f`, then it tends to `𝓝 (lim f g)`. We formulate
this lemma with a `[nonempty α]` argument of `lim` derived from `h` to make it useful for types
without a `[nonempty α]` instance. Because of the built-in proof irrelevance, Lean will unify
this instance with any other instance. -/
theorem tendsto_nhds_limUnder {f : Filter β} {g : β → α} (h : ∃ a, Tendsto g f (𝓝 a)) :
    Tendsto g f (𝓝 <| @lim _ _ _ (nonempty_of_exists h) f g) :=
  le_nhds_lim h
#align tendsto_nhds_lim tendsto_nhds_limUnder
-/

end lim

end TopologicalSpace

/-!
### Continuity
-/


section Continuous

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

open TopologicalSpace

#print Continuous /-
/-- A function between topological spaces is continuous if the preimage
  of every open set is open. Registered as a structure to make sure it is not unfolded by Lean. -/
structure Continuous (f : α → β) : Prop where
  is_open_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
#align continuous Continuous
-/

/- warning: continuous_def -> continuous_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, Iff (Continuous.{u1, u2} α β _inst_1 _inst_2 f) (forall (s : Set.{u2} β), (IsOpen.{u2} β _inst_2 s) -> (IsOpen.{u1} α _inst_1 (Set.preimage.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, Iff (Continuous.{u2, u1} α β _inst_1 _inst_2 f) (forall (s : Set.{u1} β), (IsOpen.{u1} β _inst_2 s) -> (IsOpen.{u2} α _inst_1 (Set.preimage.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align continuous_def continuous_defₓ'. -/
theorem continuous_def {f : α → β} : Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  ⟨fun hf s hs => hf.is_open_preimage s hs, fun h => ⟨h⟩⟩
#align continuous_def continuous_def

/- warning: is_open.preimage -> IsOpen.preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (forall {s : Set.{u2} β}, (IsOpen.{u2} β _inst_2 s) -> (IsOpen.{u1} α _inst_1 (Set.preimage.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (forall {s : Set.{u1} β}, (IsOpen.{u1} β _inst_2 s) -> (IsOpen.{u2} α _inst_1 (Set.preimage.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align is_open.preimage IsOpen.preimageₓ'. -/
theorem IsOpen.preimage {f : α → β} (hf : Continuous f) {s : Set β} (h : IsOpen s) :
    IsOpen (f ⁻¹' s) :=
  hf.is_open_preimage s h
#align is_open.preimage IsOpen.preimage

/- warning: continuous.congr -> Continuous.congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β}, (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (x : α), Eq.{succ u2} β (f x) (g x)) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {g : α -> β}, (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (forall (x : α), Eq.{succ u1} β (f x) (g x)) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 g)
Case conversion may be inaccurate. Consider using '#align continuous.congr Continuous.congrₓ'. -/
theorem Continuous.congr {f g : α → β} (h : Continuous f) (h' : ∀ x, f x = g x) : Continuous g :=
  by
  convert h
  ext
  rw [h']
#align continuous.congr Continuous.congr

#print ContinuousAt /-
/-- A function between topological spaces is continuous at a point `x₀`
if `f x` tends to `f x₀` when `x` tends to `x₀`. -/
def ContinuousAt (f : α → β) (x : α) :=
  Tendsto f (𝓝 x) (𝓝 (f x))
#align continuous_at ContinuousAt
-/

/- warning: continuous_at.tendsto -> ContinuousAt.tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {x : α}, (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f x) -> (Filter.Tendsto.{u1, u2} α β f (nhds.{u1} α _inst_1 x) (nhds.{u2} β _inst_2 (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {x : α}, (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 f x) -> (Filter.Tendsto.{u2, u1} α β f (nhds.{u2} α _inst_1 x) (nhds.{u1} β _inst_2 (f x)))
Case conversion may be inaccurate. Consider using '#align continuous_at.tendsto ContinuousAt.tendstoₓ'. -/
theorem ContinuousAt.tendsto {f : α → β} {x : α} (h : ContinuousAt f x) :
    Tendsto f (𝓝 x) (𝓝 (f x)) :=
  h
#align continuous_at.tendsto ContinuousAt.tendsto

/- warning: continuous_at_def -> continuousAt_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {x : α}, Iff (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f x) (forall (A : Set.{u2} β), (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) A (nhds.{u2} β _inst_2 (f x))) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (Set.preimage.{u1, u2} α β f A) (nhds.{u1} α _inst_1 x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {x : α}, Iff (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 f x) (forall (A : Set.{u1} β), (Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) A (nhds.{u1} β _inst_2 (f x))) -> (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) (Set.preimage.{u2, u1} α β f A) (nhds.{u2} α _inst_1 x)))
Case conversion may be inaccurate. Consider using '#align continuous_at_def continuousAt_defₓ'. -/
theorem continuousAt_def {f : α → β} {x : α} : ContinuousAt f x ↔ ∀ A ∈ 𝓝 (f x), f ⁻¹' A ∈ 𝓝 x :=
  Iff.rfl
#align continuous_at_def continuousAt_def

/- warning: continuous_at_congr -> continuousAt_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} {x : α}, (Filter.EventuallyEq.{u1, u2} α β (nhds.{u1} α _inst_1 x) f g) -> (Iff (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f x) (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 g x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {g : α -> β} {x : α}, (Filter.EventuallyEq.{u2, u1} α β (nhds.{u2} α _inst_1 x) f g) -> (Iff (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 f x) (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 g x))
Case conversion may be inaccurate. Consider using '#align continuous_at_congr continuousAt_congrₓ'. -/
theorem continuousAt_congr {f g : α → β} {x : α} (h : f =ᶠ[𝓝 x] g) :
    ContinuousAt f x ↔ ContinuousAt g x := by
  simp only [ContinuousAt, tendsto_congr' h, h.eq_of_nhds]
#align continuous_at_congr continuousAt_congr

/- warning: continuous_at.congr -> ContinuousAt.congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} {x : α}, (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f x) -> (Filter.EventuallyEq.{u1, u2} α β (nhds.{u1} α _inst_1 x) f g) -> (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 g x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {g : α -> β} {x : α}, (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 f x) -> (Filter.EventuallyEq.{u2, u1} α β (nhds.{u2} α _inst_1 x) f g) -> (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 g x)
Case conversion may be inaccurate. Consider using '#align continuous_at.congr ContinuousAt.congrₓ'. -/
theorem ContinuousAt.congr {f g : α → β} {x : α} (hf : ContinuousAt f x) (h : f =ᶠ[𝓝 x] g) :
    ContinuousAt g x :=
  (continuousAt_congr h).1 hf
#align continuous_at.congr ContinuousAt.congr

#print ContinuousAt.preimage_mem_nhds /-
theorem ContinuousAt.preimage_mem_nhds {f : α → β} {x : α} {t : Set β} (h : ContinuousAt f x)
    (ht : t ∈ 𝓝 (f x)) : f ⁻¹' t ∈ 𝓝 x :=
  h ht
#align continuous_at.preimage_mem_nhds ContinuousAt.preimage_mem_nhds
-/

#print eventuallyEq_zero_nhds /-
theorem eventuallyEq_zero_nhds {M₀} [Zero M₀] {a : α} {f : α → M₀} :
    f =ᶠ[𝓝 a] 0 ↔ a ∉ closure (Function.support f) := by
  rw [← mem_compl_iff, ← interior_compl, mem_interior_iff_mem_nhds, Function.compl_support] <;> rfl
#align eventually_eq_zero_nhds eventuallyEq_zero_nhds
-/

/- warning: cluster_pt.map -> ClusterPt.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {x : α} {la : Filter.{u1} α} {lb : Filter.{u2} β}, (ClusterPt.{u1} α _inst_1 x la) -> (forall {f : α -> β}, (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f x) -> (Filter.Tendsto.{u1, u2} α β f la lb) -> (ClusterPt.{u2} β _inst_2 (f x) lb))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {x : α} {la : Filter.{u2} α} {lb : Filter.{u1} β}, (ClusterPt.{u2} α _inst_1 x la) -> (forall {f : α -> β}, (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 f x) -> (Filter.Tendsto.{u2, u1} α β f la lb) -> (ClusterPt.{u1} β _inst_2 (f x) lb))
Case conversion may be inaccurate. Consider using '#align cluster_pt.map ClusterPt.mapₓ'. -/
theorem ClusterPt.map {x : α} {la : Filter α} {lb : Filter β} (H : ClusterPt x la) {f : α → β}
    (hfc : ContinuousAt f x) (hf : Tendsto f la lb) : ClusterPt (f x) lb :=
  ⟨ne_bot_of_le_ne_bot ((map_neBot_iff f).2 H).Ne <| hfc.Tendsto.inf hf⟩
#align cluster_pt.map ClusterPt.map

#print preimage_interior_subset_interior_preimage /-
/-- See also `interior_preimage_subset_preimage_interior`. -/
theorem preimage_interior_subset_interior_preimage {f : α → β} {s : Set β} (hf : Continuous f) :
    f ⁻¹' interior s ⊆ interior (f ⁻¹' s) :=
  interior_maximal (preimage_mono interior_subset) (isOpen_interior.Preimage hf)
#align preimage_interior_subset_interior_preimage preimage_interior_subset_interior_preimage
-/

#print continuous_id /-
theorem continuous_id : Continuous (id : α → α) :=
  continuous_def.2 fun s h => h
#align continuous_id continuous_id
-/

/- warning: continuous.comp -> Continuous.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {g : β -> γ} {f : α -> β}, (Continuous.{u2, u3} β γ _inst_2 _inst_3 g) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (Continuous.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] {g : β -> γ} {f : α -> β}, (Continuous.{u3, u2} β γ _inst_2 _inst_3 g) -> (Continuous.{u1, u3} α β _inst_1 _inst_2 f) -> (Continuous.{u1, u2} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u3, succ u2} α β γ g f))
Case conversion may be inaccurate. Consider using '#align continuous.comp Continuous.compₓ'. -/
theorem Continuous.comp {g : β → γ} {f : α → β} (hg : Continuous g) (hf : Continuous f) :
    Continuous (g ∘ f) :=
  continuous_def.2 fun s h => (h.Preimage hg).Preimage hf
#align continuous.comp Continuous.comp

#print Continuous.iterate /-
theorem Continuous.iterate {f : α → α} (h : Continuous f) (n : ℕ) : Continuous (f^[n]) :=
  Nat.recOn n continuous_id fun n ihn => ihn.comp h
#align continuous.iterate Continuous.iterate
-/

/- warning: continuous_at.comp -> ContinuousAt.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {g : β -> γ} {f : α -> β} {x : α}, (ContinuousAt.{u2, u3} β γ _inst_2 _inst_3 g (f x)) -> (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f x) -> (ContinuousAt.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) x)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] {g : β -> γ} {f : α -> β} {x : α}, (ContinuousAt.{u3, u2} β γ _inst_2 _inst_3 g (f x)) -> (ContinuousAt.{u1, u3} α β _inst_1 _inst_2 f x) -> (ContinuousAt.{u1, u2} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u3, succ u2} α β γ g f) x)
Case conversion may be inaccurate. Consider using '#align continuous_at.comp ContinuousAt.compₓ'. -/
theorem ContinuousAt.comp {g : β → γ} {f : α → β} {x : α} (hg : ContinuousAt g (f x))
    (hf : ContinuousAt f x) : ContinuousAt (g ∘ f) x :=
  hg.comp hf
#align continuous_at.comp ContinuousAt.comp

/- warning: continuous.tendsto -> Continuous.tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (x : α), Filter.Tendsto.{u1, u2} α β f (nhds.{u1} α _inst_1 x) (nhds.{u2} β _inst_2 (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (forall (x : α), Filter.Tendsto.{u2, u1} α β f (nhds.{u2} α _inst_1 x) (nhds.{u1} β _inst_2 (f x)))
Case conversion may be inaccurate. Consider using '#align continuous.tendsto Continuous.tendstoₓ'. -/
theorem Continuous.tendsto {f : α → β} (hf : Continuous f) (x) : Tendsto f (𝓝 x) (𝓝 (f x)) :=
  ((nhds_basis_opens x).tendsto_iff <| nhds_basis_opens <| f x).2 fun t ⟨hxt, ht⟩ =>
    ⟨f ⁻¹' t, ⟨hxt, ht.Preimage hf⟩, Subset.refl _⟩
#align continuous.tendsto Continuous.tendsto

/- warning: continuous.tendsto' -> Continuous.tendsto' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (x : α) (y : β), (Eq.{succ u2} β (f x) y) -> (Filter.Tendsto.{u1, u2} α β f (nhds.{u1} α _inst_1 x) (nhds.{u2} β _inst_2 y)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (forall (x : α) (y : β), (Eq.{succ u1} β (f x) y) -> (Filter.Tendsto.{u2, u1} α β f (nhds.{u2} α _inst_1 x) (nhds.{u1} β _inst_2 y)))
Case conversion may be inaccurate. Consider using '#align continuous.tendsto' Continuous.tendsto'ₓ'. -/
/-- A version of `continuous.tendsto` that allows one to specify a simpler form of the limit.
E.g., one can write `continuous_exp.tendsto' 0 1 exp_zero`. -/
theorem Continuous.tendsto' {f : α → β} (hf : Continuous f) (x : α) (y : β) (h : f x = y) :
    Tendsto f (𝓝 x) (𝓝 y) :=
  h ▸ hf.Tendsto x
#align continuous.tendsto' Continuous.tendsto'

/- warning: continuous.continuous_at -> Continuous.continuousAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {x : α}, (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {x : α}, (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 f x)
Case conversion may be inaccurate. Consider using '#align continuous.continuous_at Continuous.continuousAtₓ'. -/
theorem Continuous.continuousAt {f : α → β} {x : α} (h : Continuous f) : ContinuousAt f x :=
  h.Tendsto x
#align continuous.continuous_at Continuous.continuousAt

/- warning: continuous_iff_continuous_at -> continuous_iff_continuousAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, Iff (Continuous.{u1, u2} α β _inst_1 _inst_2 f) (forall (x : α), ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, Iff (Continuous.{u2, u1} α β _inst_1 _inst_2 f) (forall (x : α), ContinuousAt.{u2, u1} α β _inst_1 _inst_2 f x)
Case conversion may be inaccurate. Consider using '#align continuous_iff_continuous_at continuous_iff_continuousAtₓ'. -/
theorem continuous_iff_continuousAt {f : α → β} : Continuous f ↔ ∀ x, ContinuousAt f x :=
  ⟨Continuous.tendsto, fun hf : ∀ x, Tendsto f (𝓝 x) (𝓝 (f x)) =>
    continuous_def.2 fun s => fun hs : IsOpen s =>
      have : ∀ a, f a ∈ s → s ∈ 𝓝 (f a) := fun a ha => IsOpen.mem_nhds hs ha
      show IsOpen (f ⁻¹' s) from
        isOpen_iff_nhds.2 fun a ha => le_principal_iff.2 <| hf _ (this a ha)⟩
#align continuous_iff_continuous_at continuous_iff_continuousAt

/- warning: continuous_at_const -> continuousAt_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {x : α} {b : β}, ContinuousAt.{u1, u2} α β _inst_1 _inst_2 (fun (a : α) => b) x
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {x : α} {b : β}, ContinuousAt.{u2, u1} α β _inst_1 _inst_2 (fun (a : α) => b) x
Case conversion may be inaccurate. Consider using '#align continuous_at_const continuousAt_constₓ'. -/
theorem continuousAt_const {x : α} {b : β} : ContinuousAt (fun a : α => b) x :=
  tendsto_const_nhds
#align continuous_at_const continuousAt_const

/- warning: continuous_const -> continuous_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {b : β}, Continuous.{u1, u2} α β _inst_1 _inst_2 (fun (a : α) => b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {b : β}, Continuous.{u2, u1} α β _inst_1 _inst_2 (fun (a : α) => b)
Case conversion may be inaccurate. Consider using '#align continuous_const continuous_constₓ'. -/
theorem continuous_const {b : β} : Continuous fun a : α => b :=
  continuous_iff_continuousAt.mpr fun a => continuousAt_const
#align continuous_const continuous_const

/- warning: filter.eventually_eq.continuous_at -> Filter.EventuallyEq.continuousAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {x : α} {f : α -> β} {y : β}, (Filter.EventuallyEq.{u1, u2} α β (nhds.{u1} α _inst_1 x) f (fun (_x : α) => y)) -> (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {x : α} {f : α -> β} {y : β}, (Filter.EventuallyEq.{u2, u1} α β (nhds.{u2} α _inst_1 x) f (fun (_x : α) => y)) -> (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 f x)
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq.continuous_at Filter.EventuallyEq.continuousAtₓ'. -/
theorem Filter.EventuallyEq.continuousAt {x : α} {f : α → β} {y : β} (h : f =ᶠ[𝓝 x] fun _ => y) :
    ContinuousAt f x :=
  (continuousAt_congr h).2 tendsto_const_nhds
#align filter.eventually_eq.continuous_at Filter.EventuallyEq.continuousAt

#print continuous_of_const /-
theorem continuous_of_const {f : α → β} (h : ∀ x y, f x = f y) : Continuous f :=
  continuous_iff_continuousAt.mpr fun x =>
    Filter.EventuallyEq.continuousAt <| eventually_of_forall fun y => h y x
#align continuous_of_const continuous_of_const
-/

#print continuousAt_id /-
theorem continuousAt_id {x : α} : ContinuousAt id x :=
  continuous_id.ContinuousAt
#align continuous_at_id continuousAt_id
-/

#print ContinuousAt.iterate /-
theorem ContinuousAt.iterate {f : α → α} {x : α} (hf : ContinuousAt f x) (hx : f x = x) (n : ℕ) :
    ContinuousAt (f^[n]) x :=
  Nat.recOn n continuousAt_id fun n ihn =>
    show ContinuousAt (f^[n] ∘ f) x from ContinuousAt.comp (hx.symm ▸ ihn) hf
#align continuous_at.iterate ContinuousAt.iterate
-/

/- warning: continuous_iff_is_closed -> continuous_iff_isClosed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, Iff (Continuous.{u1, u2} α β _inst_1 _inst_2 f) (forall (s : Set.{u2} β), (IsClosed.{u2} β _inst_2 s) -> (IsClosed.{u1} α _inst_1 (Set.preimage.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, Iff (Continuous.{u2, u1} α β _inst_1 _inst_2 f) (forall (s : Set.{u1} β), (IsClosed.{u1} β _inst_2 s) -> (IsClosed.{u2} α _inst_1 (Set.preimage.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align continuous_iff_is_closed continuous_iff_isClosedₓ'. -/
theorem continuous_iff_isClosed {f : α → β} : Continuous f ↔ ∀ s, IsClosed s → IsClosed (f ⁻¹' s) :=
  ⟨fun hf s hs => by simpa using (continuous_def.1 hf (sᶜ) hs.is_open_compl).is_closed_compl,
    fun hf =>
    continuous_def.2 fun s => by rw [← isClosed_compl_iff, ← isClosed_compl_iff] <;> exact hf _⟩
#align continuous_iff_is_closed continuous_iff_isClosed

/- warning: is_closed.preimage -> IsClosed.preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (forall {s : Set.{u2} β}, (IsClosed.{u2} β _inst_2 s) -> (IsClosed.{u1} α _inst_1 (Set.preimage.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (forall {s : Set.{u1} β}, (IsClosed.{u1} β _inst_2 s) -> (IsClosed.{u2} α _inst_1 (Set.preimage.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align is_closed.preimage IsClosed.preimageₓ'. -/
theorem IsClosed.preimage {f : α → β} (hf : Continuous f) {s : Set β} (h : IsClosed s) :
    IsClosed (f ⁻¹' s) :=
  continuous_iff_isClosed.mp hf s h
#align is_closed.preimage IsClosed.preimage

/- warning: mem_closure_image -> mem_closure_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {x : α} {s : Set.{u1} α}, (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f x) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α _inst_1 s)) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) (closure.{u2} β _inst_2 (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {x : α} {s : Set.{u2} α}, (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 f x) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (closure.{u2} α _inst_1 s)) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f x) (closure.{u1} β _inst_2 (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align mem_closure_image mem_closure_imageₓ'. -/
theorem mem_closure_image {f : α → β} {x : α} {s : Set α} (hf : ContinuousAt f x)
    (hx : x ∈ closure s) : f x ∈ closure (f '' s) :=
  mem_closure_of_frequently_of_tendsto
    ((mem_closure_iff_frequently.1 hx).mono fun x => mem_image_of_mem _) hf
#align mem_closure_image mem_closure_image

/- warning: continuous_at_iff_ultrafilter -> continuousAt_iff_ultrafilter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {x : α}, Iff (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f x) (forall (g : Ultrafilter.{u1} α), (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) g) (nhds.{u1} α _inst_1 x)) -> (Filter.Tendsto.{u1, u2} α β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) g) (nhds.{u2} β _inst_2 (f x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {x : α}, Iff (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 f x) (forall (g : Ultrafilter.{u2} α), (LE.le.{u2} (Filter.{u2} α) (Preorder.toLE.{u2} (Filter.{u2} α) (PartialOrder.toPreorder.{u2} (Filter.{u2} α) (Filter.instPartialOrderFilter.{u2} α))) (Ultrafilter.toFilter.{u2} α g) (nhds.{u2} α _inst_1 x)) -> (Filter.Tendsto.{u2, u1} α β f (Ultrafilter.toFilter.{u2} α g) (nhds.{u1} β _inst_2 (f x))))
Case conversion may be inaccurate. Consider using '#align continuous_at_iff_ultrafilter continuousAt_iff_ultrafilterₓ'. -/
theorem continuousAt_iff_ultrafilter {f : α → β} {x} :
    ContinuousAt f x ↔ ∀ g : Ultrafilter α, ↑g ≤ 𝓝 x → Tendsto f g (𝓝 (f x)) :=
  tendsto_iff_ultrafilter f (𝓝 x) (𝓝 (f x))
#align continuous_at_iff_ultrafilter continuousAt_iff_ultrafilter

/- warning: continuous_iff_ultrafilter -> continuous_iff_ultrafilter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, Iff (Continuous.{u1, u2} α β _inst_1 _inst_2 f) (forall (x : α) (g : Ultrafilter.{u1} α), (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) g) (nhds.{u1} α _inst_1 x)) -> (Filter.Tendsto.{u1, u2} α β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} α) (Filter.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} α) (Filter.{u1} α) (Ultrafilter.Filter.hasCoeT.{u1} α))) g) (nhds.{u2} β _inst_2 (f x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, Iff (Continuous.{u2, u1} α β _inst_1 _inst_2 f) (forall (x : α) (g : Ultrafilter.{u2} α), (LE.le.{u2} (Filter.{u2} α) (Preorder.toLE.{u2} (Filter.{u2} α) (PartialOrder.toPreorder.{u2} (Filter.{u2} α) (Filter.instPartialOrderFilter.{u2} α))) (Ultrafilter.toFilter.{u2} α g) (nhds.{u2} α _inst_1 x)) -> (Filter.Tendsto.{u2, u1} α β f (Ultrafilter.toFilter.{u2} α g) (nhds.{u1} β _inst_2 (f x))))
Case conversion may be inaccurate. Consider using '#align continuous_iff_ultrafilter continuous_iff_ultrafilterₓ'. -/
theorem continuous_iff_ultrafilter {f : α → β} :
    Continuous f ↔ ∀ (x) (g : Ultrafilter α), ↑g ≤ 𝓝 x → Tendsto f g (𝓝 (f x)) := by
  simp only [continuous_iff_continuousAt, continuousAt_iff_ultrafilter]
#align continuous_iff_ultrafilter continuous_iff_ultrafilter

/- warning: continuous.closure_preimage_subset -> Continuous.closure_preimage_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (t : Set.{u2} β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (closure.{u1} α _inst_1 (Set.preimage.{u1, u2} α β f t)) (Set.preimage.{u1, u2} α β f (closure.{u2} β _inst_2 t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (forall (t : Set.{u1} β), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (closure.{u2} α _inst_1 (Set.preimage.{u2, u1} α β f t)) (Set.preimage.{u2, u1} α β f (closure.{u1} β _inst_2 t)))
Case conversion may be inaccurate. Consider using '#align continuous.closure_preimage_subset Continuous.closure_preimage_subsetₓ'. -/
theorem Continuous.closure_preimage_subset {f : α → β} (hf : Continuous f) (t : Set β) :
    closure (f ⁻¹' t) ⊆ f ⁻¹' closure t :=
  by
  rw [← (is_closed_closure.preimage hf).closure_eq]
  exact closure_mono (preimage_mono subset_closure)
#align continuous.closure_preimage_subset Continuous.closure_preimage_subset

/- warning: continuous.frontier_preimage_subset -> Continuous.frontier_preimage_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (t : Set.{u2} β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (frontier.{u1} α _inst_1 (Set.preimage.{u1, u2} α β f t)) (Set.preimage.{u1, u2} α β f (frontier.{u2} β _inst_2 t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (forall (t : Set.{u1} β), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (frontier.{u2} α _inst_1 (Set.preimage.{u2, u1} α β f t)) (Set.preimage.{u2, u1} α β f (frontier.{u1} β _inst_2 t)))
Case conversion may be inaccurate. Consider using '#align continuous.frontier_preimage_subset Continuous.frontier_preimage_subsetₓ'. -/
theorem Continuous.frontier_preimage_subset {f : α → β} (hf : Continuous f) (t : Set β) :
    frontier (f ⁻¹' t) ⊆ f ⁻¹' frontier t :=
  diff_subset_diff (hf.closure_preimage_subset t) (preimage_interior_subset_interior_preimage hf)
#align continuous.frontier_preimage_subset Continuous.frontier_preimage_subset

/- warning: set.maps_to.closure -> Set.MapsTo.closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.MapsTo.{u1, u2} α β f s t) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (Set.MapsTo.{u1, u2} α β f (closure.{u1} α _inst_1 s) (closure.{u2} β _inst_2 t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.MapsTo.{u2, u1} α β f s t) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (Set.MapsTo.{u2, u1} α β f (closure.{u2} α _inst_1 s) (closure.{u1} β _inst_2 t))
Case conversion may be inaccurate. Consider using '#align set.maps_to.closure Set.MapsTo.closureₓ'. -/
/-- If a continuous map `f` maps `s` to `t`, then it maps `closure s` to `closure t`. -/
theorem Set.MapsTo.closure {s : Set α} {t : Set β} {f : α → β} (h : MapsTo f s t)
    (hc : Continuous f) : MapsTo f (closure s) (closure t) :=
  by
  simp only [maps_to, mem_closure_iff_clusterPt]
  exact fun x hx => hx.map hc.continuous_at (tendsto_principal_principal.2 h)
#align set.maps_to.closure Set.MapsTo.closure

/- warning: image_closure_subset_closure_image -> image_closure_subset_closure_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{u1, u2} α β f (closure.{u1} α _inst_1 s)) (closure.{u2} β _inst_2 (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α}, (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.image.{u2, u1} α β f (closure.{u2} α _inst_1 s)) (closure.{u1} β _inst_2 (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align image_closure_subset_closure_image image_closure_subset_closure_imageₓ'. -/
theorem image_closure_subset_closure_image {f : α → β} {s : Set α} (h : Continuous f) :
    f '' closure s ⊆ closure (f '' s) :=
  ((mapsTo_image f s).closure h).image_subset
#align image_closure_subset_closure_image image_closure_subset_closure_image

/- warning: closure_subset_preimage_closure_image -> closure_subset_preimage_closure_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (closure.{u1} α _inst_1 s) (Set.preimage.{u1, u2} α β f (closure.{u2} β _inst_2 (Set.image.{u1, u2} α β f s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α}, (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (closure.{u2} α _inst_1 s) (Set.preimage.{u2, u1} α β f (closure.{u1} β _inst_2 (Set.image.{u2, u1} α β f s))))
Case conversion may be inaccurate. Consider using '#align closure_subset_preimage_closure_image closure_subset_preimage_closure_imageₓ'. -/
theorem closure_subset_preimage_closure_image {f : α → β} {s : Set α} (h : Continuous f) :
    closure s ⊆ f ⁻¹' closure (f '' s) :=
  by
  rw [← Set.image_subset_iff]
  exact image_closure_subset_closure_image h
#align closure_subset_preimage_closure_image closure_subset_preimage_closure_image

/- warning: map_mem_closure -> map_mem_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β} {a : α}, (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (closure.{u1} α _inst_1 s)) -> (Set.MapsTo.{u1, u2} α β f s t) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f a) (closure.{u2} β _inst_2 t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β} {a : α}, (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (closure.{u2} α _inst_1 s)) -> (Set.MapsTo.{u2, u1} α β f s t) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f a) (closure.{u1} β _inst_2 t))
Case conversion may be inaccurate. Consider using '#align map_mem_closure map_mem_closureₓ'. -/
theorem map_mem_closure {s : Set α} {t : Set β} {f : α → β} {a : α} (hf : Continuous f)
    (ha : a ∈ closure s) (ht : MapsTo f s t) : f a ∈ closure t :=
  ht.closure hf ha
#align map_mem_closure map_mem_closure

/- warning: set.maps_to.closure_left -> Set.MapsTo.closure_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.MapsTo.{u1, u2} α β f s t) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (IsClosed.{u2} β _inst_2 t) -> (Set.MapsTo.{u1, u2} α β f (closure.{u1} α _inst_1 s) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, (Set.MapsTo.{u2, u1} α β f s t) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (IsClosed.{u1} β _inst_2 t) -> (Set.MapsTo.{u2, u1} α β f (closure.{u2} α _inst_1 s) t)
Case conversion may be inaccurate. Consider using '#align set.maps_to.closure_left Set.MapsTo.closure_leftₓ'. -/
/-- If a continuous map `f` maps `s` to a closed set `t`, then it maps `closure s` to `t`. -/
theorem Set.MapsTo.closure_left {s : Set α} {t : Set β} {f : α → β} (h : MapsTo f s t)
    (hc : Continuous f) (ht : IsClosed t) : MapsTo f (closure s) t :=
  ht.closure_eq ▸ h.closure hc
#align set.maps_to.closure_left Set.MapsTo.closure_left

/-!
### Function with dense range
-/


section DenseRange

variable {κ ι : Type _} (f : κ → β) (g : β → γ)

#print DenseRange /-
/-- `f : ι → β` has dense range if its range (image) is a dense subset of β. -/
def DenseRange :=
  Dense (range f)
#align dense_range DenseRange
-/

variable {f}

#print Function.Surjective.denseRange /-
/-- A surjective map has dense range. -/
theorem Function.Surjective.denseRange (hf : Function.Surjective f) : DenseRange f := fun x => by
  simp [hf.range_eq]
#align function.surjective.dense_range Function.Surjective.denseRange
-/

#print denseRange_id /-
theorem denseRange_id : DenseRange (id : α → α) :=
  Function.Surjective.denseRange Function.surjective_id
#align dense_range_id denseRange_id
-/

/- warning: dense_range_iff_closure_range -> denseRange_iff_closure_range is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {κ : Type.{u2}} {f : κ -> β}, Iff (DenseRange.{u1, u2} β _inst_2 κ f) (Eq.{succ u1} (Set.{u1} β) (closure.{u1} β _inst_2 (Set.range.{u1, succ u2} β κ f)) (Set.univ.{u1} β))
but is expected to have type
  forall {β : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} β] {κ : Type.{u1}} {f : κ -> β}, Iff (DenseRange.{u2, u1} β _inst_2 κ f) (Eq.{succ u2} (Set.{u2} β) (closure.{u2} β _inst_2 (Set.range.{u2, succ u1} β κ f)) (Set.univ.{u2} β))
Case conversion may be inaccurate. Consider using '#align dense_range_iff_closure_range denseRange_iff_closure_rangeₓ'. -/
theorem denseRange_iff_closure_range : DenseRange f ↔ closure (range f) = univ :=
  dense_iff_closure_eq
#align dense_range_iff_closure_range denseRange_iff_closure_range

/- warning: dense_range.closure_range -> DenseRange.closure_range is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {κ : Type.{u2}} {f : κ -> β}, (DenseRange.{u1, u2} β _inst_2 κ f) -> (Eq.{succ u1} (Set.{u1} β) (closure.{u1} β _inst_2 (Set.range.{u1, succ u2} β κ f)) (Set.univ.{u1} β))
but is expected to have type
  forall {β : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} β] {κ : Type.{u1}} {f : κ -> β}, (DenseRange.{u2, u1} β _inst_2 κ f) -> (Eq.{succ u2} (Set.{u2} β) (closure.{u2} β _inst_2 (Set.range.{u2, succ u1} β κ f)) (Set.univ.{u2} β))
Case conversion may be inaccurate. Consider using '#align dense_range.closure_range DenseRange.closure_rangeₓ'. -/
theorem DenseRange.closure_range (h : DenseRange f) : closure (range f) = univ :=
  h.closure_eq
#align dense_range.closure_range DenseRange.closure_range

#print Dense.denseRange_val /-
theorem Dense.denseRange_val {s : Set α} (h : Dense s) : DenseRange (coe : s → α) := by
  simpa only [DenseRange, Subtype.range_coe_subtype]
#align dense.dense_range_coe Dense.denseRange_val
-/

/- warning: continuous.range_subset_closure_image_dense -> Continuous.range_subset_closure_image_dense is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (forall {s : Set.{u1} α}, (Dense.{u1} α _inst_1 s) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.range.{u2, succ u1} β α f) (closure.{u2} β _inst_2 (Set.image.{u1, u2} α β f s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, (Continuous.{u2, u1} α β _inst_1 _inst_2 f) -> (forall {s : Set.{u2} α}, (Dense.{u2} α _inst_1 s) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.range.{u1, succ u2} β α f) (closure.{u1} β _inst_2 (Set.image.{u2, u1} α β f s))))
Case conversion may be inaccurate. Consider using '#align continuous.range_subset_closure_image_dense Continuous.range_subset_closure_image_denseₓ'. -/
theorem Continuous.range_subset_closure_image_dense {f : α → β} (hf : Continuous f) {s : Set α}
    (hs : Dense s) : range f ⊆ closure (f '' s) :=
  by
  rw [← image_univ, ← hs.closure_eq]
  exact image_closure_subset_closure_image hf
#align continuous.range_subset_closure_image_dense Continuous.range_subset_closure_image_dense

#print DenseRange.dense_image /-
/-- The image of a dense set under a continuous map with dense range is a dense set. -/
theorem DenseRange.dense_image {f : α → β} (hf' : DenseRange f) (hf : Continuous f) {s : Set α}
    (hs : Dense s) : Dense (f '' s) :=
  (hf'.mono <| hf.range_subset_closure_image_dense hs).of_closure
#align dense_range.dense_image DenseRange.dense_image
-/

/- warning: dense_range.subset_closure_image_preimage_of_is_open -> DenseRange.subset_closure_image_preimage_of_isOpen is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {κ : Type.{u2}} {f : κ -> β}, (DenseRange.{u1, u2} β _inst_2 κ f) -> (forall {s : Set.{u1} β}, (IsOpen.{u1} β _inst_2 s) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.hasSubset.{u1} β) s (closure.{u1} β _inst_2 (Set.image.{u2, u1} κ β f (Set.preimage.{u2, u1} κ β f s)))))
but is expected to have type
  forall {β : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} β] {κ : Type.{u1}} {f : κ -> β}, (DenseRange.{u2, u1} β _inst_2 κ f) -> (forall {s : Set.{u2} β}, (IsOpen.{u2} β _inst_2 s) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) s (closure.{u2} β _inst_2 (Set.image.{u1, u2} κ β f (Set.preimage.{u1, u2} κ β f s)))))
Case conversion may be inaccurate. Consider using '#align dense_range.subset_closure_image_preimage_of_is_open DenseRange.subset_closure_image_preimage_of_isOpenₓ'. -/
/-- If `f` has dense range and `s` is an open set in the codomain of `f`, then the image of the
preimage of `s` under `f` is dense in `s`. -/
theorem DenseRange.subset_closure_image_preimage_of_isOpen (hf : DenseRange f) {s : Set β}
    (hs : IsOpen s) : s ⊆ closure (f '' (f ⁻¹' s)) :=
  by
  rw [image_preimage_eq_inter_range]
  exact hf.open_subset_closure_inter hs
#align dense_range.subset_closure_image_preimage_of_is_open DenseRange.subset_closure_image_preimage_of_isOpen

#print DenseRange.dense_of_mapsTo /-
/-- If a continuous map with dense range maps a dense set to a subset of `t`, then `t` is a dense
set. -/
theorem DenseRange.dense_of_mapsTo {f : α → β} (hf' : DenseRange f) (hf : Continuous f) {s : Set α}
    (hs : Dense s) {t : Set β} (ht : MapsTo f s t) : Dense t :=
  (hf'.dense_image hf hs).mono ht.image_subset
#align dense_range.dense_of_maps_to DenseRange.dense_of_mapsTo
-/

/- warning: dense_range.comp -> DenseRange.comp is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {γ : Type.{u2}} [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u2} γ] {κ : Type.{u3}} {g : β -> γ} {f : κ -> β}, (DenseRange.{u2, u1} γ _inst_3 β g) -> (DenseRange.{u1, u3} β _inst_2 κ f) -> (Continuous.{u1, u2} β γ _inst_2 _inst_3 g) -> (DenseRange.{u2, u3} γ _inst_3 κ (Function.comp.{succ u3, succ u1, succ u2} κ β γ g f))
but is expected to have type
  forall {β : Type.{u2}} {γ : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {κ : Type.{u1}} {g : β -> γ} {f : κ -> β}, (DenseRange.{u3, u2} γ _inst_3 β g) -> (DenseRange.{u2, u1} β _inst_2 κ f) -> (Continuous.{u2, u3} β γ _inst_2 _inst_3 g) -> (DenseRange.{u3, u1} γ _inst_3 κ (Function.comp.{succ u1, succ u2, succ u3} κ β γ g f))
Case conversion may be inaccurate. Consider using '#align dense_range.comp DenseRange.compₓ'. -/
/-- Composition of a continuous map with dense range and a function with dense range has dense
range. -/
theorem DenseRange.comp {g : β → γ} {f : κ → β} (hg : DenseRange g) (hf : DenseRange f)
    (cg : Continuous g) : DenseRange (g ∘ f) :=
  by
  rw [DenseRange, range_comp]
  exact hg.dense_image cg hf
#align dense_range.comp DenseRange.comp

/- warning: dense_range.nonempty_iff -> DenseRange.nonempty_iff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {κ : Type.{u2}} {f : κ -> β}, (DenseRange.{u1, u2} β _inst_2 κ f) -> (Iff (Nonempty.{succ u2} κ) (Nonempty.{succ u1} β))
but is expected to have type
  forall {β : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} β] {κ : Type.{u1}} {f : κ -> β}, (DenseRange.{u2, u1} β _inst_2 κ f) -> (Iff (Nonempty.{succ u1} κ) (Nonempty.{succ u2} β))
Case conversion may be inaccurate. Consider using '#align dense_range.nonempty_iff DenseRange.nonempty_iffₓ'. -/
theorem DenseRange.nonempty_iff (hf : DenseRange f) : Nonempty κ ↔ Nonempty β :=
  range_nonempty_iff_nonempty.symm.trans hf.nonempty_iff
#align dense_range.nonempty_iff DenseRange.nonempty_iff

/- warning: dense_range.nonempty -> DenseRange.nonempty is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {κ : Type.{u2}} {f : κ -> β} [h : Nonempty.{succ u1} β], (DenseRange.{u1, u2} β _inst_2 κ f) -> (Nonempty.{succ u2} κ)
but is expected to have type
  forall {β : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} β] {κ : Type.{u1}} {f : κ -> β} [h : Nonempty.{succ u2} β], (DenseRange.{u2, u1} β _inst_2 κ f) -> (Nonempty.{succ u1} κ)
Case conversion may be inaccurate. Consider using '#align dense_range.nonempty DenseRange.nonemptyₓ'. -/
theorem DenseRange.nonempty [h : Nonempty β] (hf : DenseRange f) : Nonempty κ :=
  hf.nonempty_iff.mpr h
#align dense_range.nonempty DenseRange.nonempty

#print DenseRange.some /-
/-- Given a function `f : α → β` with dense range and `b : β`, returns some `a : α`. -/
def DenseRange.some (hf : DenseRange f) (b : β) : κ :=
  Classical.choice <| hf.nonempty_iff.mpr ⟨b⟩
#align dense_range.some DenseRange.some
-/

/- warning: dense_range.exists_mem_open -> DenseRange.exists_mem_open is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {κ : Type.{u2}} {f : κ -> β}, (DenseRange.{u1, u2} β _inst_2 κ f) -> (forall {s : Set.{u1} β}, (IsOpen.{u1} β _inst_2 s) -> (Set.Nonempty.{u1} β s) -> (Exists.{succ u2} κ (fun (a : κ) => Membership.Mem.{u1, u1} β (Set.{u1} β) (Set.hasMem.{u1} β) (f a) s)))
but is expected to have type
  forall {β : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} β] {κ : Type.{u1}} {f : κ -> β}, (DenseRange.{u2, u1} β _inst_2 κ f) -> (forall {s : Set.{u2} β}, (IsOpen.{u2} β _inst_2 s) -> (Set.Nonempty.{u2} β s) -> (Exists.{succ u1} κ (fun (a : κ) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) (f a) s)))
Case conversion may be inaccurate. Consider using '#align dense_range.exists_mem_open DenseRange.exists_mem_openₓ'. -/
theorem DenseRange.exists_mem_open (hf : DenseRange f) {s : Set β} (ho : IsOpen s)
    (hs : s.Nonempty) : ∃ a, f a ∈ s :=
  exists_range_iff.1 <| hf.exists_mem_open ho hs
#align dense_range.exists_mem_open DenseRange.exists_mem_open

/- warning: dense_range.mem_nhds -> DenseRange.mem_nhds is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {κ : Type.{u2}} {f : κ -> β}, (DenseRange.{u1, u2} β _inst_2 κ f) -> (forall {b : β} {U : Set.{u1} β}, (Membership.Mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (Filter.hasMem.{u1} β) U (nhds.{u1} β _inst_2 b)) -> (Exists.{succ u2} κ (fun (a : κ) => Membership.Mem.{u1, u1} β (Set.{u1} β) (Set.hasMem.{u1} β) (f a) U)))
but is expected to have type
  forall {β : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} β] {κ : Type.{u1}} {f : κ -> β}, (DenseRange.{u2, u1} β _inst_2 κ f) -> (forall {b : β} {U : Set.{u2} β}, (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) U (nhds.{u2} β _inst_2 b)) -> (Exists.{succ u1} κ (fun (a : κ) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) (f a) U)))
Case conversion may be inaccurate. Consider using '#align dense_range.mem_nhds DenseRange.mem_nhdsₓ'. -/
theorem DenseRange.mem_nhds {f : κ → β} (h : DenseRange f) {b : β} {U : Set β} (U_in : U ∈ 𝓝 b) :
    ∃ a, f a ∈ U :=
  let ⟨a, ha⟩ := h.exists_mem_open isOpen_interior ⟨b, mem_interior_iff_mem_nhds.2 U_in⟩
  ⟨a, interior_subset ha⟩
#align dense_range.mem_nhds DenseRange.mem_nhds

end DenseRange

end Continuous

library_note "continuity lemma statement"/--
The library contains many lemmas stating that functions/operations are continuous. There are many
ways to formulate the continuity of operations. Some are more convenient than others.
Note: for the most part this note also applies to other properties
(`measurable`, `differentiable`, `continuous_on`, ...).

### The traditional way
As an example, let's look at addition `(+) : M → M → M`. We can state that this is continuous
in different definitionally equal ways (omitting some typing information)
* `continuous (λ p, p.1 + p.2)`;
* `continuous (function.uncurry (+))`;
* `continuous ↿(+)`. (`↿` is notation for recursively uncurrying a function)

However, lemmas with this conclusion are not nice to use in practice because
1. They confuse the elaborator. The following two examples fail, because of limitations in the
  elaboration process.
  ```
  variables {M : Type*} [has_add M] [topological_space M] [has_continuous_add M]
  example : continuous (λ x : M, x + x) :=
  continuous_add.comp _

  example : continuous (λ x : M, x + x) :=
  continuous_add.comp (continuous_id.prod_mk continuous_id)
  ```
  The second is a valid proof, which is accepted if you write it as
  `continuous_add.comp (continuous_id.prod_mk continuous_id : _)`

2. If the operation has more than 2 arguments, they are impractical to use, because in your
  application the arguments in the domain might be in a different order or associated differently.

### The convenient way
A much more convenient way to write continuity lemmas is like `continuous.add`:
```
continuous.add {f g : X → M} (hf : continuous f) (hg : continuous g) : continuous (λ x, f x + g x)
```
The conclusion can be `continuous (f + g)`, which is definitionally equal.
This has the following advantages
* It supports projection notation, so is shorter to write.
* `continuous.add _ _` is recognized correctly by the elaborator and gives useful new goals.
* It works generally, since the domain is a variable.

As an example for an unary operation, we have `continuous.neg`.
```
continuous.neg {f : α → G} (hf : continuous f) : continuous (λ x, -f x)
```
For unary functions, the elaborator is not confused when applying the traditional lemma
(like `continuous_neg`), but it's still convenient to have the short version available (compare
`hf.neg.neg.neg` with `continuous_neg.comp $ continuous_neg.comp $ continuous_neg.comp hf`).

As a harder example, consider an operation of the following type:
```
def strans {x : F} (γ γ' : path x x) (t₀ : I) : path x x
```
The precise definition is not important, only its type.
The correct continuity principle for this operation is something like this:
```
{f : X → F} {γ γ' : ∀ x, path (f x) (f x)} {t₀ s : X → I}
  (hγ : continuous ↿γ) (hγ' : continuous ↿γ')
  (ht : continuous t₀) (hs : continuous s) :
  continuous (λ x, strans (γ x) (γ' x) (t x) (s x))
```
Note that *all* arguments of `strans` are indexed over `X`, even the basepoint `x`, and the last
argument `s` that arises since `path x x` has a coercion to `I → F`. The paths `γ` and `γ'` (which
are unary functions from `I`) become binary functions in the continuity lemma.

### Summary
* Make sure that your continuity lemmas are stated in the most general way, and in a convenient
  form. That means that:
  - The conclusion has a variable `X` as domain (not something like `Y × Z`);
  - Wherever possible, all point arguments `c : Y` are replaced by functions `c : X → Y`;
  - All `n`-ary function arguments are replaced by `n+1`-ary functions
    (`f : Y → Z` becomes `f : X → Y → Z`);
  - All (relevant) arguments have continuity assumptions, and perhaps there are additional
    assumptions needed to make the operation continuous;
  - The function in the conclusion is fully applied.
* These remarks are mostly about the format of the *conclusion* of a continuity lemma.
  In assumptions it's fine to state that a function with more than 1 argument is continuous using
  `↿` or `function.uncurry`.

### Functions with discontinuities

In some cases, you want to work with discontinuous functions, and in certain expressions they are
still continuous. For example, consider the fractional part of a number, `fract : ℝ → ℝ`.
In this case, you want to add conditions to when a function involving `fract` is continuous, so you
get something like this: (assumption `hf` could be weakened, but the important thing is the shape
of the conclusion)
```
lemma continuous_on.comp_fract {X Y : Type*} [topological_space X] [topological_space Y]
  {f : X → ℝ → Y} {g : X → ℝ} (hf : continuous ↿f) (hg : continuous g) (h : ∀ s, f s 0 = f s 1) :
  continuous (λ x, f x (fract (g x)))
```
With `continuous_at` you can be even more precise about what to prove in case of discontinuities,
see e.g. `continuous_at.comp_div_cases`.
-/


