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


open OmegaCompletePartialOrder

open Classical

universe u

namespace Scott

/-- `x` is an `ω`-Sup of a chain `c` if it is the least upper bound of the range of `c`. -/
def IsωSup {α : Type u} [Preorderₓ α] (c : Chain α) (x : α) : Prop :=
  (∀ i, c i ≤ x) ∧ ∀ y, (∀ i, c i ≤ y) → x ≤ y

theorem is_ωSup_iff_is_lub {α : Type u} [Preorderₓ α] {c : Chain α} {x : α} : IsωSup c x ↔ IsLub (Set.Range c) x := by
  simp [is_ωSup, IsLub, IsLeast, UpperBounds, LowerBounds]

variable (α : Type u) [OmegaCompletePartialOrder α]

/-- The characteristic function of open sets is monotone and preserves
the limits of chains. -/
def IsOpen (s : Set α) : Prop :=
  Continuous' fun x => x ∈ s

theorem is_open_univ : IsOpen α Set.Univ :=
  ⟨fun x y h => by
    simp only [Set.mem_univ] <;> rfl', by
    convert @CompleteLattice.top_continuous α Prop _ _ <;> ext <;> simp ⟩

theorem IsOpen.inter (s t : Set α) : IsOpen α s → IsOpen α t → IsOpen α (s ∩ t) :=
  CompleteLattice.inf_continuous'

theorem is_open_sUnion (s : Set (Set α)) (hs : ∀, ∀ t ∈ s, ∀, IsOpen α t) : IsOpen α (⋃₀s) := by
  simp only [IsOpen] at hs⊢
  convert CompleteLattice.Sup_continuous' (SetOf ⁻¹' s) _
  · ext1 x
    simp only [Sup_apply, set.set_of_bijective.surjective.exists, exists_prop, Set.mem_preimage, SetCoe.exists,
      supr_Prop_eq, Set.mem_set_of_eq, Subtype.coe_mk]
    
  · intro p hp
    convert hs (SetOf p) (Set.mem_preimage.1 hp)
    simp only [Set.mem_set_of_eq]
    

end Scott

/-- A Scott topological space is defined on preorders
such that their open sets, seen as a function `α → Prop`,
preserves the joins of ω-chains  -/
@[reducible]
def Scott (α : Type u) :=
  α

instance Scott.topologicalSpace (α : Type u) [OmegaCompletePartialOrder α] : TopologicalSpace (Scott α) where
  IsOpen := Scott.IsOpen α
  is_open_univ := Scott.is_open_univ α
  is_open_inter := Scott.IsOpen.inter α
  is_open_sUnion := Scott.is_open_sUnion α

section NotBelow

variable {α : Type _} [OmegaCompletePartialOrder α] (y : Scott α)

/-- `not_below` is an open set in `Scott α` used
to prove the monotonicity of continuous functions -/
def NotBelow :=
  { x | ¬x ≤ y }

theorem not_below_is_open : IsOpen (NotBelow y) := by
  have h : Monotone (NotBelow y) := by
    intro x y' h
    simp only [NotBelow, SetOf, le_Prop_eq]
    intro h₀ h₁
    apply h₀ (le_transₓ h h₁)
  exists h
  rintro c
  apply eq_of_forall_ge_iff
  intro z
  rw [ωSup_le_iff]
  simp only [ωSup_le_iff, NotBelow, Set.mem_set_of_eq, le_Prop_eq, OrderHom.coe_fun_mk, chain.map_coe,
    Function.comp_app, exists_imp_distrib, not_forall]

end NotBelow

open Scott hiding IsOpen

open OmegaCompletePartialOrder

theorem is_ωSup_ωSup {α} [OmegaCompletePartialOrder α] (c : Chain α) : IsωSup c (ωSup c) := by
  constructor
  · apply le_ωSup
    
  · apply ωSup_le
    

-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:492:11: unsupported: specialize non-hyp
theorem Scott_continuous_of_continuous {α β} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
    (f : Scott α → Scott β) (hf : Continuous f) : OmegaCompletePartialOrder.Continuous' f := by
  simp only [continuous_def, (· ⁻¹' ·)] at hf
  have h : Monotone f := by
    intro x y h
    cases' hf { x | ¬x ≤ f y } (not_below_is_open _) with hf hf'
    clear hf'
    specialize hf h
    simp only [Set.Preimage, SetOf, (· ∈ ·), Set.Mem, le_Prop_eq] at hf
    by_contra H
    apply hf H (le_reflₓ (f y))
  exists h
  intro c
  apply eq_of_forall_ge_iff
  intro z
  specialize [anonymous]
  cases hf
  specialize hf_h c
  simp only [NotBelow, OrderHom.coe_fun_mk, eq_iff_iff, Set.mem_set_of_eq] at hf_h
  rw [← not_iff_not]
  simp only [ωSup_le_iff, hf_h, ωSup, supr, Sup, CompleteLattice.supₓ, CompleteSemilatticeSup.sup, exists_prop,
    Set.mem_range, OrderHom.coe_fun_mk, chain.map_coe, Function.comp_app, eq_iff_iff, not_forall]
  tauto

theorem continuous_of_Scott_continuous {α β} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
    (f : Scott α → Scott β) (hf : OmegaCompletePartialOrder.Continuous' f) : Continuous f := by
  rw [continuous_def]
  intro s hs
  change continuous' (s ∘ f)
  cases' hs with hs hs'
  cases' hf with hf hf'
  apply continuous.of_bundled
  apply continuous_comp _ _ hf' hs'

