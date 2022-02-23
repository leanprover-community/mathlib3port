/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import Mathbin.Topology.Homeomorph

/-!
# Compact sets

We define a few types of sets in a topological space.

## Main Definitions

For a topological space `α`,
- `closeds α`: The type of closed sets.
- `compacts α`: The type of compact sets.
- `nonempty_compacts α`: The type of non-empty compact sets.
- `positive_compacts α`: The type of compact sets with non-empty interior.
-/


open Set

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]

namespace TopologicalSpace

/-! ### Closed sets -/


/-- The type of closed subsets of a topological space. -/
structure Closeds (α : Type _) [TopologicalSpace α] where
  Carrier : Set α
  closed' : IsClosed carrier

namespace Closeds

variable {α}

instance : SetLike (Closeds α) α where
  coe := Closeds.Carrier
  coe_injective' := fun s t h => by
    cases s
    cases t
    congr

theorem closed (s : Closeds α) : IsClosed (s : Set α) :=
  s.closed'

@[ext]
protected theorem ext {s t : Closeds α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Set α) h : (mk s h : Set α) = s :=
  rfl

instance : HasSup (Closeds α) :=
  ⟨fun s t => ⟨s ∪ t, s.closed.union t.closed⟩⟩

instance : HasInf (Closeds α) :=
  ⟨fun s t => ⟨s ∩ t, s.closed.inter t.closed⟩⟩

instance : HasTop (Closeds α) :=
  ⟨⟨Univ, is_closed_univ⟩⟩

instance : HasBot (Closeds α) :=
  ⟨⟨∅, is_closed_empty⟩⟩

instance : Lattice (Closeds α) :=
  SetLike.coe_injective.Lattice _ (fun _ _ => rfl) fun _ _ => rfl

instance : BoundedOrder (Closeds α) :=
  BoundedOrder.lift (coe : _ → Set α) (fun _ _ => id) rfl rfl

/-- The type of closed sets is inhabited, with default element the empty set. -/
instance : Inhabited (Closeds α) :=
  ⟨⊥⟩

@[simp]
theorem coe_sup (s t : Closeds α) : (↑(s⊔t) : Set α) = s ∪ t :=
  rfl

@[simp]
theorem coe_inf (s t : Closeds α) : (↑(s⊓t) : Set α) = s ∩ t :=
  rfl

@[simp]
theorem coe_top : (↑(⊤ : Closeds α) : Set α) = univ :=
  rfl

@[simp]
theorem coe_bot : (↑(⊥ : Closeds α) : Set α) = ∅ :=
  rfl

end Closeds

/-! ### Compact sets -/


/-- The type of compact sets of a topological space. -/
structure Compacts (α : Type _) [TopologicalSpace α] where
  Carrier : Set α
  compact' : IsCompact carrier

namespace Compacts

instance : SetLike (Compacts α) α where
  coe := Compacts.Carrier
  coe_injective' := fun s t h => by
    cases s
    cases t
    congr

theorem compact (s : Compacts α) : IsCompact (s : Set α) :=
  s.compact'

@[ext]
protected theorem ext {s t : Compacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Set α) h : (mk s h : Set α) = s :=
  rfl

instance : HasSup (Compacts α) :=
  ⟨fun s t => ⟨s ∪ t, s.compact.union t.compact⟩⟩

instance [T2Space α] : HasInf (Compacts α) :=
  ⟨fun s t => ⟨s ∩ t, s.compact.inter t.compact⟩⟩

instance [CompactSpace α] : HasTop (Compacts α) :=
  ⟨⟨Univ, compact_univ⟩⟩

instance : HasBot (Compacts α) :=
  ⟨⟨∅, is_compact_empty⟩⟩

instance : SemilatticeSup (Compacts α) :=
  SetLike.coe_injective.SemilatticeSup _ fun _ _ => rfl

instance [T2Space α] : Lattice (Compacts α) :=
  SetLike.coe_injective.Lattice _ (fun _ _ => rfl) fun _ _ => rfl

instance : OrderBot (Compacts α) :=
  OrderBot.lift (coe : _ → Set α) (fun _ _ => id) rfl

instance [CompactSpace α] : BoundedOrder (Compacts α) :=
  BoundedOrder.lift (coe : _ → Set α) (fun _ _ => id) rfl rfl

/-- The type of compact sets is inhabited, with default element the empty set. -/
instance : Inhabited (Compacts α) :=
  ⟨⊥⟩

@[simp]
theorem coe_sup (s t : Compacts α) : (↑(s⊔t) : Set α) = s ∪ t :=
  rfl

@[simp]
theorem coe_inf [T2Space α] (s t : Compacts α) : (↑(s⊓t) : Set α) = s ∩ t :=
  rfl

@[simp]
theorem coe_top [CompactSpace α] : (↑(⊤ : Compacts α) : Set α) = univ :=
  rfl

@[simp]
theorem coe_bot : (↑(⊥ : Compacts α) : Set α) = ∅ :=
  rfl

@[simp]
theorem coe_finset_sup {ι : Type _} {s : Finset ι} {f : ι → Compacts α} : (↑(s.sup f) : Set α) = s.sup fun i => f i :=
  by
  classical
  refine' Finset.induction_on s rfl fun a s _ h => _
  simp_rw [Finset.sup_insert, coe_sup, sup_eq_union]
  congr

/-- The image of a compact set under a continuous function. -/
protected def map (f : α → β) (hf : Continuous f) (K : Compacts α) : Compacts β :=
  ⟨f '' K.1, K.2.Image hf⟩

@[simp]
theorem coe_map {f : α → β} (hf : Continuous f) (s : Compacts α) : (s.map f hf : Set β) = f '' s :=
  rfl

/-- A homeomorphism induces an equivalence on compact sets, by taking the image. -/
@[simp]
protected def equiv (f : α ≃ₜ β) : Compacts α ≃ Compacts β where
  toFun := Compacts.map f f.Continuous
  invFun := Compacts.map _ f.symm.Continuous
  left_inv := fun s => by
    ext1
    simp only [coe_map, ← image_comp, f.symm_comp_self, image_id]
  right_inv := fun s => by
    ext1
    simp only [coe_map, ← image_comp, f.self_comp_symm, image_id]

/-- The image of a compact set under a homeomorphism can also be expressed as a preimage. -/
theorem equiv_to_fun_val (f : α ≃ₜ β) (K : Compacts α) : (Compacts.equiv f K).1 = f.symm ⁻¹' K.1 :=
  congr_funₓ (image_eq_preimage_of_inverse f.left_inv f.right_inv) K.1

end Compacts

/-! ### Nonempty compact sets -/


/-- The type of nonempty compact sets of a topological space. -/
structure NonemptyCompacts (α : Type _) [TopologicalSpace α] extends Compacts α where
  nonempty' : carrier.Nonempty

namespace NonemptyCompacts

instance : SetLike (NonemptyCompacts α) α where
  coe := fun s => s.Carrier
  coe_injective' := fun s t h => by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

theorem compact (s : NonemptyCompacts α) : IsCompact (s : Set α) :=
  s.compact'

protected theorem nonempty (s : NonemptyCompacts α) : (s : Set α).Nonempty :=
  s.nonempty'

/-- Reinterpret a nonempty compact as a closed set. -/
def toCloseds [T2Space α] (s : NonemptyCompacts α) : Closeds α :=
  ⟨s, s.compact.IsClosed⟩

@[ext]
protected theorem ext {s t : NonemptyCompacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Compacts α) h : (mk s h : Set α) = s :=
  rfl

instance : HasSup (NonemptyCompacts α) :=
  ⟨fun s t => ⟨s.toCompacts⊔t.toCompacts, s.Nonempty.mono <| subset_union_left _ _⟩⟩

instance [CompactSpace α] [Nonempty α] : HasTop (NonemptyCompacts α) :=
  ⟨⟨⊤, univ_nonempty⟩⟩

instance : SemilatticeSup (NonemptyCompacts α) :=
  SetLike.coe_injective.SemilatticeSup _ fun _ _ => rfl

instance [CompactSpace α] [Nonempty α] : OrderTop (NonemptyCompacts α) :=
  OrderTop.lift (coe : _ → Set α) (fun _ _ => id) rfl

@[simp]
theorem coe_sup (s t : NonemptyCompacts α) : (↑(s⊔t) : Set α) = s ∪ t :=
  rfl

@[simp]
theorem coe_top [CompactSpace α] [Nonempty α] : (↑(⊤ : NonemptyCompacts α) : Set α) = univ :=
  rfl

/-- In an inhabited space, the type of nonempty compact subsets is also inhabited, with
default element the singleton set containing the default element. -/
instance [Inhabited α] : Inhabited (NonemptyCompacts α) :=
  ⟨{ Carrier := {default}, compact' := is_compact_singleton, nonempty' := singleton_nonempty _ }⟩

instance to_compact_space {s : NonemptyCompacts α} : CompactSpace s :=
  ⟨is_compact_iff_is_compact_univ.1 s.compact⟩

instance to_nonempty {s : NonemptyCompacts α} : Nonempty s :=
  s.Nonempty.to_subtype

end NonemptyCompacts

/-! ### Positive compact sets -/


/-- The type of compact sets nonempty interior of a topological space. See also `compacts` and
`nonempty_compacts` -/
structure PositiveCompacts (α : Type _) [TopologicalSpace α] extends Compacts α where
  interior_nonempty' : (Interior carrier).Nonempty

namespace PositiveCompacts

instance : SetLike (PositiveCompacts α) α where
  coe := fun s => s.Carrier
  coe_injective' := fun s t h => by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

theorem compact (s : PositiveCompacts α) : IsCompact (s : Set α) :=
  s.compact'

theorem interior_nonempty (s : PositiveCompacts α) : (Interior (s : Set α)).Nonempty :=
  s.interior_nonempty'

/-- Reinterpret a positive compact as a nonempty compact. -/
def toNonemptyCompacts (s : PositiveCompacts α) : NonemptyCompacts α :=
  ⟨s.toCompacts, s.interior_nonempty.mono interior_subset⟩

@[ext]
protected theorem ext {s t : PositiveCompacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Compacts α) h : (mk s h : Set α) = s :=
  rfl

instance : HasSup (PositiveCompacts α) :=
  ⟨fun s t => ⟨s.toCompacts⊔t.toCompacts, s.interior_nonempty.mono <| interior_mono <| subset_union_left _ _⟩⟩

instance [CompactSpace α] [Nonempty α] : HasTop (PositiveCompacts α) :=
  ⟨⟨⊤, interior_univ.symm.subst univ_nonempty⟩⟩

instance : SemilatticeSup (PositiveCompacts α) :=
  SetLike.coe_injective.SemilatticeSup _ fun _ _ => rfl

instance [CompactSpace α] [Nonempty α] : OrderTop (PositiveCompacts α) :=
  OrderTop.lift (coe : _ → Set α) (fun _ _ => id) rfl

@[simp]
theorem coe_sup (s t : PositiveCompacts α) : (↑(s⊔t) : Set α) = s ∪ t :=
  rfl

@[simp]
theorem coe_top [CompactSpace α] [Nonempty α] : (↑(⊤ : PositiveCompacts α) : Set α) = univ :=
  rfl

instance [CompactSpace α] [Nonempty α] : Inhabited (PositiveCompacts α) :=
  ⟨⊤⟩

/-- In a nonempty locally compact space, there exists a compact set with nonempty interior. -/
instance [LocallyCompactSpace α] [Nonempty α] : Nonempty (PositiveCompacts α) :=
  let ⟨s, hs⟩ := exists_compact_subset is_open_univ <| mem_univ (Classical.arbitrary α)
  ⟨{ Carrier := s, compact' := hs.1, interior_nonempty' := ⟨_, hs.2.1⟩ }⟩

end PositiveCompacts

end TopologicalSpace

