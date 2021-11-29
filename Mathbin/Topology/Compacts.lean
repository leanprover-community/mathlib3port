import Mathbin.Topology.Homeomorph

/-!
# Compact sets

## Summary

We define the subtype of compact sets in a topological space.

## Main Definitions

- `closeds α` is the type of closed subsets of a topological space `α`.
- `compacts α` is the type of compact subsets of a topological space `α`.
- `nonempty_compacts α` is the type of non-empty compact subsets.
- `positive_compacts α` is the type of compact subsets with non-empty interior.
-/


open Set

variable (α : Type _) {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

namespace TopologicalSpace

/-- The type of closed subsets of a topological space. -/
def closeds :=
  { s : Set α // IsClosed s }

/-- The type of closed subsets is inhabited, with default element the empty set. -/
instance : Inhabited (closeds α) :=
  ⟨⟨∅, is_closed_empty⟩⟩

/-- The compact sets of a topological space. See also `nonempty_compacts`. -/
def compacts : Type _ :=
  { s : Set α // IsCompact s }

/-- The type of non-empty compact subsets of a topological space. The
non-emptiness will be useful in metric spaces, as we will be able to put
a distance (and not merely an edistance) on this space. -/
def nonempty_compacts :=
  { s : Set α // s.nonempty ∧ IsCompact s }

/-- In an inhabited space, the type of nonempty compact subsets is also inhabited, with
default element the singleton set containing the default element. -/
instance nonempty_compacts_inhabited [Inhabited α] : Inhabited (nonempty_compacts α) :=
  ⟨⟨{default α}, singleton_nonempty (default α), is_compact_singleton⟩⟩

/-- The compact sets with nonempty interior of a topological space. See also `compacts` and
  `nonempty_compacts`. -/
@[nolint has_inhabited_instance]
def positive_compacts : Type _ :=
  { s : Set α // IsCompact s ∧ (Interior s).Nonempty }

/-- In a nonempty compact space, `set.univ` is a member of `positive_compacts`, the compact sets
with nonempty interior. -/
def positive_compacts_univ {α : Type _} [TopologicalSpace α] [CompactSpace α] [Nonempty α] : positive_compacts α :=
  ⟨Set.Univ, compact_univ,
    by 
      simp ⟩

@[simp]
theorem positive_compacts_univ_val (α : Type _) [TopologicalSpace α] [CompactSpace α] [Nonempty α] :
  (positive_compacts_univ : positive_compacts α).val = univ :=
  rfl

variable {α}

namespace Compacts

instance : SemilatticeSup (compacts α) :=
  Subtype.semilatticeSup fun K₁ K₂ => IsCompact.union

instance : OrderBot (compacts α) :=
  Subtype.orderBot is_compact_empty

instance [T2Space α] : SemilatticeInf (compacts α) :=
  Subtype.semilatticeInf fun K₁ K₂ => IsCompact.inter

instance [T2Space α] : Lattice (compacts α) :=
  Subtype.lattice (fun K₁ K₂ => IsCompact.union) fun K₁ K₂ => IsCompact.inter

@[simp]
theorem bot_val : (⊥ : compacts α).1 = ∅ :=
  rfl

@[simp]
theorem sup_val {K₁ K₂ : compacts α} : (K₁⊔K₂).1 = K₁.1 ∪ K₂.1 :=
  rfl

@[ext]
protected theorem ext {K₁ K₂ : compacts α} (h : K₁.1 = K₂.1) : K₁ = K₂ :=
  Subtype.eq h

@[simp]
theorem finset_sup_val {β} {K : β → compacts α} {s : Finset β} : (s.sup K).1 = s.sup fun x => (K x).1 :=
  Finset.sup_coe _ _

instance : Inhabited (compacts α) :=
  ⟨⊥⟩

/-- The image of a compact set under a continuous function. -/
protected def map (f : α → β) (hf : Continuous f) (K : compacts α) : compacts β :=
  ⟨f '' K.1, K.2.Image hf⟩

@[simp]
theorem map_val {f : α → β} (hf : Continuous f) (K : compacts α) : (K.map f hf).1 = f '' K.1 :=
  rfl

/-- A homeomorphism induces an equivalence on compact sets, by taking the image. -/
@[simp]
protected def Equiv (f : α ≃ₜ β) : compacts α ≃ compacts β :=
  { toFun := compacts.map f f.continuous, invFun := compacts.map _ f.symm.continuous,
    left_inv :=
      by 
        intro K 
        ext1 
        simp only [map_val, ←image_comp, f.symm_comp_self, image_id],
    right_inv :=
      by 
        intro K 
        ext1 
        simp only [map_val, ←image_comp, f.self_comp_symm, image_id] }

/-- The image of a compact set under a homeomorphism can also be expressed as a preimage. -/
theorem equiv_to_fun_val (f : α ≃ₜ β) (K : compacts α) : (compacts.equiv f K).1 = f.symm ⁻¹' K.1 :=
  congr_funₓ (image_eq_preimage_of_inverse f.left_inv f.right_inv) K.1

end Compacts

section NonemptyCompacts

open TopologicalSpace Set

variable {α}

instance nonempty_compacts.to_compact_space {p : nonempty_compacts α} : CompactSpace p.val :=
  ⟨is_compact_iff_is_compact_univ.1 p.property.2⟩

instance nonempty_compacts.to_nonempty {p : nonempty_compacts α} : Nonempty p.val :=
  p.property.1.to_subtype

/-- Associate to a nonempty compact subset the corresponding closed subset -/
def nonempty_compacts.to_closeds [T2Space α] : nonempty_compacts α → closeds α :=
  Set.inclusion$ fun s hs => hs.2.IsClosed

end NonemptyCompacts

section PositiveCompacts

variable (α)

/-- In a nonempty locally compact space, there exists a compact set with nonempty interior. -/
instance nonempty_positive_compacts [LocallyCompactSpace α] [Nonempty α] : Nonempty (positive_compacts α) :=
  by 
    inhabit α 
    rcases exists_compact_subset is_open_univ (mem_univ (default α)) with ⟨K, hK⟩
    exact ⟨⟨K, hK.1, ⟨_, hK.2.1⟩⟩⟩

end PositiveCompacts

end TopologicalSpace

