/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Topology.Basic
import Mathbin.Order.OmegaCompletePartialOrder

/-!
# Scott Topological Spaces

A type of topological spaces whose notion
of continuity is equivalent to continuity in ωCPOs.

## Reference

 * https://ncatlab.org/nlab/show/Scott+topology

-/


open Set OmegaCompletePartialOrder

open Classical

universe u

namespace ScottCat

/-- `x` is an `ω`-Sup of a chain `c` if it is the least upper bound of the range of `c`. -/
def IsωSup {α : Type u} [Preorder α] (c : Chain α) (x : α) : Prop :=
  (∀ i, c i ≤ x) ∧ ∀ y, (∀ i, c i ≤ y) → x ≤ y
#align Scott.is_ωSup ScottCat.IsωSup

theorem is_ωSup_iff_is_lub {α : Type u} [Preorder α] {c : Chain α} {x : α} : IsωSup c x ↔ IsLub (range c) x := by
  simp [is_ωSup, IsLub, IsLeast, upperBounds, lowerBounds]
#align Scott.is_ωSup_iff_is_lub ScottCat.is_ωSup_iff_is_lub

variable (α : Type u) [OmegaCompletePartialOrder α]

/-- The characteristic function of open sets is monotone and preserves
the limits of chains. -/
def IsOpen (s : Set α) : Prop :=
  Continuous' fun x => x ∈ s
#align Scott.is_open ScottCat.IsOpen

theorem is_open_univ : IsOpen α univ :=
  ⟨fun x y h hx => mem_univ _, by
    convert @CompleteLattice.top_continuous α Prop _ _
    exact rfl⟩
#align Scott.is_open_univ ScottCat.is_open_univ

theorem IsOpen.inter (s t : Set α) : IsOpen α s → IsOpen α t → IsOpen α (s ∩ t) :=
  CompleteLattice.inf_continuous'
#align Scott.is_open.inter ScottCat.IsOpen.inter

theorem is_open_sUnion (s : Set (Set α)) (hs : ∀ t ∈ s, IsOpen α t) : IsOpen α (⋃₀s) := by
  simp only [IsOpen] at hs⊢
  convert CompleteLattice.Sup_continuous' (setOf ⁻¹' s) _
  · ext1 x
    simp only [Sup_apply, set_of_bijective.surjective.exists, exists_prop, mem_preimage, SetCoe.exists, supr_Prop_eq,
      mem_set_of_eq, Subtype.coe_mk, mem_sUnion]
    
  · intro p hp
    convert hs (setOf p) (mem_preimage.1 hp)
    simp only [mem_set_of_eq]
    
#align Scott.is_open_sUnion ScottCat.is_open_sUnion

end ScottCat

/-- A Scott topological space is defined on preorders
such that their open sets, seen as a function `α → Prop`,
preserves the joins of ω-chains  -/
@[reducible]
def ScottCat (α : Type u) :=
  α
#align Scott ScottCat

instance ScottCat.topologicalSpace (α : Type u) [OmegaCompletePartialOrder α] : TopologicalSpace (ScottCat α) where
  IsOpen := ScottCat.IsOpen α
  is_open_univ := ScottCat.is_open_univ α
  is_open_inter := ScottCat.IsOpen.inter α
  is_open_sUnion := ScottCat.is_open_sUnion α
#align Scott.topological_space ScottCat.topologicalSpace

section notBelow

variable {α : Type _} [OmegaCompletePartialOrder α] (y : ScottCat α)

/-- `not_below` is an open set in `Scott α` used
to prove the monotonicity of continuous functions -/
def notBelow :=
  { x | ¬x ≤ y }
#align not_below notBelow

theorem not_below_is_open : IsOpen (notBelow y) := by
  have h : Monotone (notBelow y) := by
    intro x y' h
    simp only [notBelow, setOf, le_Prop_eq]
    intro h₀ h₁
    apply h₀ (le_trans h h₁)
  exists h
  rintro c
  apply eq_of_forall_ge_iff
  intro z
  rw [ωSup_le_iff]
  simp only [ωSup_le_iff, notBelow, mem_set_of_eq, le_Prop_eq, OrderHom.coe_fun_mk, chain.map_coe, Function.comp_apply,
    exists_imp, not_forall]
#align not_below_is_open not_below_is_open

end notBelow

open ScottCat hiding IsOpen

open OmegaCompletePartialOrder

theorem is_ωSup_ωSup {α} [OmegaCompletePartialOrder α] (c : Chain α) : IsωSup c (ωSup c) := by
  constructor
  · apply le_ωSup
    
  · apply ωSup_le
    
#align is_ωSup_ωSup is_ωSup_ωSup

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:564:11: unsupported: specialize non-hyp -/
theorem Scott_continuous_of_continuous {α β} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
    (f : ScottCat α → ScottCat β) (hf : Continuous f) : OmegaCompletePartialOrder.Continuous' f := by
  simp only [continuous_def, (· ⁻¹' ·)] at hf
  have h : Monotone f := by
    intro x y h
    cases' hf { x | ¬x ≤ f y } (not_below_is_open _) with hf hf'
    clear hf'
    specialize hf h
    simp only [preimage, mem_set_of_eq, le_Prop_eq] at hf
    by_contra H
    apply hf H le_rfl
  exists h
  intro c
  apply eq_of_forall_ge_iff
  intro z
  specialize «./././Mathport/Syntax/Translate/Tactic/Lean3.lean:564:11: unsupported: specialize non-hyp»
  cases hf
  specialize hf_h c
  simp only [notBelow, OrderHom.coe_fun_mk, eq_iff_iff, mem_set_of_eq] at hf_h
  rw [← not_iff_not]
  simp only [ωSup_le_iff, hf_h, ωSup, supr, Sup, CompleteLattice.sup, CompleteSemilatticeSup.sup, exists_prop,
    mem_range, OrderHom.coe_fun_mk, chain.map_coe, Function.comp_apply, eq_iff_iff, not_forall]
  tauto
#align Scott_continuous_of_continuous Scott_continuous_of_continuous

theorem continuous_of_Scott_continuous {α β} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
    (f : ScottCat α → ScottCat β) (hf : OmegaCompletePartialOrder.Continuous' f) : Continuous f := by
  rw [continuous_def]
  intro s hs
  change continuous' (s ∘ f)
  cases' hs with hs hs'
  cases' hf with hf hf'
  apply continuous.of_bundled
  apply continuous_comp _ _ hf' hs'
#align continuous_of_Scott_continuous continuous_of_Scott_continuous

