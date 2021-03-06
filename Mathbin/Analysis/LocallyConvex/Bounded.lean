/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathbin.Analysis.LocallyConvex.Basic
import Mathbin.Topology.Bornology.Basic
import Mathbin.Topology.Algebra.UniformGroup
import Mathbin.Analysis.LocallyConvex.BalancedCoreHull

/-!
# Von Neumann Boundedness

This file defines natural or von Neumann bounded sets and proves elementary properties.

## Main declarations

* `bornology.is_vonN_bounded`: A set `s` is von Neumann-bounded if every neighborhood of zero
absorbs `s`.
* `bornology.vonN_bornology`: The bornology made of the von Neumann-bounded sets.

## Main results

* `bornology.is_vonN_bounded_of_topological_space_le`: A coarser topology admits more
von Neumann-bounded sets.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

-/


variable {ð E Î¹ : Type _}

open Filter

open TopologicalSpace Pointwise

namespace Bornology

section SemiNormedRing

section Zero

variable (ð)

variable [SemiNormedRing ð] [HasSmul ð E] [Zero E]

variable [TopologicalSpace E]

/-- A set `s` is von Neumann bounded if every neighborhood of 0 absorbs `s`. -/
def IsVonNBounded (s : Set E) : Prop :=
  â â¦Vâ¦, V â ð (0 : E) â Absorbs ð V s

variable (E)

@[simp]
theorem is_vonN_bounded_empty : IsVonNBounded ð (â : Set E) := fun _ _ => absorbs_empty

variable {ð E}

theorem is_vonN_bounded_iff (s : Set E) : IsVonNBounded ð s â â, â V â ð (0 : E), â, Absorbs ð V s :=
  Iff.rfl

theorem _root_.filter.has_basis.is_vonN_bounded_basis_iff {q : Î¹ â Prop} {s : Î¹ â Set E} {A : Set E}
    (h : (ð (0 : E)).HasBasis q s) : IsVonNBounded ð A â â (i) (hi : q i), Absorbs ð (s i) A := by
  refine' â¨fun hA i hi => hA (h.mem_of_mem hi), fun hA V hV => _â©
  rcases h.mem_iff.mp hV with â¨i, hi, hVâ©
  exact (hA i hi).mono_left hV

/-- Subsets of bounded sets are bounded. -/
theorem IsVonNBounded.subset {sâ sâ : Set E} (h : sâ â sâ) (hsâ : IsVonNBounded ð sâ) : IsVonNBounded ð sâ :=
  fun V hV => (hsâ hV).mono_right h

/-- The union of two bounded sets is bounded. -/
theorem IsVonNBounded.union {sâ sâ : Set E} (hsâ : IsVonNBounded ð sâ) (hsâ : IsVonNBounded ð sâ) :
    IsVonNBounded ð (sâ âª sâ) := fun V hV => (hsâ hV).union (hsâ hV)

end Zero

end SemiNormedRing

section MultipleTopologies

variable [SemiNormedRing ð] [AddCommGroupâ E] [Module ð E]

/-- If a topology `t'` is coarser than `t`, then any set `s` that is bounded with respect to
`t` is bounded with respect to `t'`. -/
theorem IsVonNBounded.of_topological_space_le {t t' : TopologicalSpace E} (h : t â¤ t') {s : Set E}
    (hs : @IsVonNBounded ð E _ _ _ t s) : @IsVonNBounded ð E _ _ _ t' s := fun V hV =>
  hs <| (le_iff_nhds t t').mp h 0 hV

end MultipleTopologies

section Image

variable {ðâ ðâ F : Type _} [NormedDivisionRing ðâ] [NormedDivisionRing ðâ] [AddCommGroupâ E] [Module ðâ E]
  [AddCommGroupâ F] [Module ðâ F] [TopologicalSpace E] [TopologicalSpace F]

/-- A continuous linear image of a bounded set is bounded. -/
theorem IsVonNBounded.image {Ï : ðâ â+* ðâ} [RingHomSurjective Ï] [RingHomIsometric Ï] {s : Set E}
    (hs : IsVonNBounded ðâ s) (f : E âSL[Ï] F) : IsVonNBounded ðâ (f '' s) := by
  let Ï' := RingEquiv.ofBijective Ï â¨Ï.injective, Ï.is_surjectiveâ©
  have Ï_iso : Isometry Ï := AddMonoidHomClass.isometry_of_norm Ï fun x => RingHomIsometric.is_iso
  have Ï'_symm_iso : Isometry Ï'.symm := Ï_iso.right_inv Ï'.right_inv
  have f_tendsto_zero := f.continuous.tendsto 0
  rw [map_zero] at f_tendsto_zero
  intro V hV
  rcases hs (f_tendsto_zero hV) with â¨r, hrpos, hrâ©
  refine' â¨r, hrpos, fun a ha => _â©
  rw [â Ï'.apply_symm_apply a]
  have hanz : a â  0 := norm_pos_iff.mp (hrpos.trans_le ha)
  have : Ï'.symm a â  0 := (RingHom.map_ne_zero Ï'.symm.to_ring_hom).mpr hanz
  change _ â Ï _ â¢ _
  rw [Set.image_subset_iff, preimage_smul_setââ _ _ _ f this.is_unit]
  refine' hr (Ï'.symm a) _
  rwa [Ï'_symm_iso.norm_map_of_map_zero (map_zero _)]

end Image

section NormedField

variable [NormedField ð] [AddCommGroupâ E] [Module ð E]

variable [TopologicalSpace E] [HasContinuousSmul ð E]

/-- Singletons are bounded. -/
theorem is_vonN_bounded_singleton (x : E) : IsVonNBounded ð ({x} : Set E) := fun V hV =>
  (absorbent_nhds_zero hV).Absorbs

/-- The union of all bounded set is the whole space. -/
theorem is_vonN_bounded_covers : ââSetOf (IsVonNBounded ð) = (Set.Univ : Set E) :=
  Set.eq_univ_iff_forall.mpr fun x => Set.mem_sUnion.mpr â¨{x}, is_vonN_bounded_singleton _, Set.mem_singleton _â©

variable (ð E)

/-- The von Neumann bornology defined by the von Neumann bounded sets.

Note that this is not registered as an instance, in order to avoid diamonds with the
metric bornology.-/
-- See note [reducible non-instances]
@[reducible]
def vonNBornology : Bornology E :=
  Bornology.ofBounded (SetOf (IsVonNBounded ð)) (is_vonN_bounded_empty ð E) (fun _ hs _ ht => hs.Subset ht)
    (fun _ hs _ => hs.union) is_vonN_bounded_singleton

variable {E}

@[simp]
theorem is_bounded_iff_is_vonN_bounded {s : Set E} : @IsBounded _ (vonNBornology ð E) s â IsVonNBounded ð s :=
  is_bounded_of_bounded_iff _

end NormedField

end Bornology

section UniformAddGroup

variable [NondiscreteNormedField ð] [AddCommGroupâ E] [Module ð E]

variable [UniformSpace E] [UniformAddGroup E] [HasContinuousSmul ð E]

variable [T3Space E]

theorem TotallyBounded.is_vonN_bounded {s : Set E} (hs : TotallyBounded s) : Bornology.IsVonNBounded ð s := by
  rw [totally_bounded_iff_subset_finite_Union_nhds_zero] at hs
  intro U hU
  have h : Filter.Tendsto (fun x : E Ã E => x.fst + x.snd) (ð (0, 0)) (ð ((0 : E) + (0 : E))) := tendsto_add
  rw [add_zeroâ] at h
  have h' := (nhds_basis_closed_balanced ð E).Prod (nhds_basis_closed_balanced ð E)
  simp_rw [â nhds_prod_eq, id.def] at h'
  rcases h.basis_left h' U hU with â¨x, hx, h''â©
  rcases hs x.snd hx.2.1 with â¨t, ht, hsâ©
  refine' Absorbs.mono_right _ hs
  rw [ht.absorbs_Union]
  have hx_fstsnd : x.fst + x.snd â U := by
    intro z hz
    rcases set.mem_add.mp hz with â¨z1, z2, hz1, hz2, hzâ©
    have hz' : (z1, z2) â x.fst ÃË¢ x.snd := â¨hz1, hz2â©
    simpa only [â hz] using h'' hz'
  refine' fun y hy => Absorbs.mono_left _ hx_fstsnd
  rw [â Set.singleton_vadd, vadd_eq_add]
  exact (absorbent_nhds_zero hx.1.1).Absorbs.add hx.2.2.2.absorbs_self

end UniformAddGroup

