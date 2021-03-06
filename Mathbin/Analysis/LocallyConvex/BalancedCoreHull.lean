/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathbin.Analysis.LocallyConvex.Basic
import Mathbin.Order.Closure

/-!
# Balanced Core and Balanced Hull

## Main definitions

* `balanced_core`: The largest balanced subset of a set `s`.
* `balanced_hull`: The smallest balanced superset of a set `s`.

## Main statements

* `balanced_core_eq_Inter`: Characterization of the balanced core as an intersection over subsets.
* `nhds_basis_closed_balanced`: The closed balanced sets form a basis of the neighborhood filter.

## Implementation details

The balanced core and hull are implemented differently: for the core we take the obvious definition
of the union over all balanced sets that are contained in `s`, whereas for the hull, we take the
union over `r â¢ s`, for `r` the scalars with `â¥râ¥ â¤ 1`. We show that `balanced_hull` has the
defining properties of a hull in `balanced.hull_minimal` and `subset_balanced_hull`.
For the core we need slightly stronger assumptions to obtain a characterization as an intersection,
this is `balanced_core_eq_Inter`.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

balanced
-/


open Set

open Pointwise TopologicalSpace Filter

variable {ð E Î¹ : Type _}

section BalancedHull

section SemiNormedRing

variable [SemiNormedRing ð]

section HasSmul

variable (ð) [HasSmul ð E] {s t : Set E} {x : E}

/-- The largest balanced subset of `s`.-/
def BalancedCore (s : Set E) :=
  ââ{ t : Set E | Balanced ð t â§ t â s }

/-- Helper definition to prove `balanced_core_eq_Inter`-/
def BalancedCoreAux (s : Set E) :=
  â (r : ð) (hr : 1 â¤ â¥râ¥), r â¢ s

/-- The smallest balanced superset of `s`.-/
def BalancedHull (s : Set E) :=
  â (r : ð) (hr : â¥râ¥ â¤ 1), r â¢ s

variable {ð}

theorem balanced_core_subset (s : Set E) : BalancedCore ð s â s :=
  sUnion_subset fun t ht => ht.2

theorem balanced_core_empty : BalancedCore ð (â : Set E) = â :=
  eq_empty_of_subset_empty (balanced_core_subset _)

theorem mem_balanced_core_iff : x â BalancedCore ð s â â t, Balanced ð t â§ t â s â§ x â t := by
  simp_rw [BalancedCore, mem_sUnion, mem_set_of_eq, exists_prop, and_assoc]

theorem smul_balanced_core_subset (s : Set E) {a : ð} (ha : â¥aâ¥ â¤ 1) : a â¢ BalancedCore ð s â BalancedCore ð s := by
  rintro x â¨y, hy, rflâ©
  rw [mem_balanced_core_iff] at hy
  rcases hy with â¨t, ht1, ht2, hyâ©
  exact â¨t, â¨ht1, ht2â©, ht1 a ha (smul_mem_smul_set hy)â©

theorem balanced_core_balanced (s : Set E) : Balanced ð (BalancedCore ð s) := fun _ => smul_balanced_core_subset s

/-- The balanced core of `t` is maximal in the sense that it contains any balanced subset
`s` of `t`.-/
theorem Balanced.subset_core_of_subset (hs : Balanced ð s) (h : s â t) : s â BalancedCore ð t :=
  subset_sUnion_of_mem â¨hs, hâ©

theorem mem_balanced_core_aux_iff : x â BalancedCoreAux ð s â â r : ð, 1 â¤ â¥râ¥ â x â r â¢ s :=
  mem_Interâ

theorem mem_balanced_hull_iff : x â BalancedHull ð s â â (r : ð)(hr : â¥râ¥ â¤ 1), x â r â¢ s :=
  mem_Unionâ

/-- The balanced hull of `s` is minimal in the sense that it is contained in any balanced superset
`t` of `s`. -/
theorem Balanced.hull_subset_of_subset (ht : Balanced ð t) (h : s â t) : BalancedHull ð s â t := fun x hx => by
  obtain â¨r, hr, y, hy, rflâ© := mem_balanced_hull_iff.1 hx
  exact ht.smul_mem hr (h hy)

end HasSmul

section Module

variable [AddCommGroupâ E] [Module ð E] {s : Set E}

theorem balanced_core_zero_mem (hs : (0 : E) â s) : (0 : E) â BalancedCore ð s :=
  mem_balanced_core_iff.2 â¨0, balanced_zero, zero_subset.2 hs, zero_mem_zeroâ©

theorem balanced_core_nonempty_iff : (BalancedCore ð s).Nonempty â (0 : E) â s :=
  â¨fun h =>
    zero_subset.1 <|
      (zero_smul_set h).Superset.trans <|
        (balanced_core_balanced s (0 : ð) <| norm_zero.trans_le zero_le_one).trans <| balanced_core_subset _,
    fun h => â¨0, balanced_core_zero_mem hâ©â©

variable (ð)

theorem subset_balanced_hull [NormOneClass ð] {s : Set E} : s â BalancedHull ð s := fun _ hx =>
  mem_balanced_hull_iff.2 â¨1, norm_one.le, _, hx, one_smul _ _â©

variable {ð}

theorem BalancedHull.balanced (s : Set E) : Balanced ð (BalancedHull ð s) := by
  intro a ha
  simp_rw [BalancedHull, smul_set_Unionâ, subset_def, mem_Unionâ]
  rintro x â¨r, hr, hxâ©
  rw [â smul_assoc] at hx
  exact â¨a â¢ r, (SemiNormedRing.norm_mul _ _).trans (mul_le_one ha (norm_nonneg r) hr), hxâ©

end Module

end SemiNormedRing

section NormedField

variable [NormedField ð] [AddCommGroupâ E] [Module ð E] {s t : Set E}

@[simp]
theorem balanced_core_aux_empty : BalancedCoreAux ð (â : Set E) = â := by
  simp_rw [BalancedCoreAux, Interâ_eq_empty_iff, smul_set_empty]
  exact fun _ => â¨1, norm_one.ge, not_mem_empty _â©

theorem balanced_core_aux_subset (s : Set E) : BalancedCoreAux ð s â s := fun x hx => by
  simpa only [â one_smul] using mem_balanced_core_aux_iff.1 hx 1 norm_one.ge

theorem balanced_core_aux_balanced (h0 : (0 : E) â BalancedCoreAux ð s) : Balanced ð (BalancedCoreAux ð s) := by
  rintro a ha x â¨y, hy, rflâ©
  obtain rfl | h := eq_or_ne a 0
  Â· rwa [zero_smul]
    
  rw [mem_balanced_core_aux_iff] at hyâ¢
  intro r hr
  have h'' : 1 â¤ â¥aâ»Â¹ â¢ râ¥ := by
    rw [norm_smul, norm_inv]
    exact one_le_mul_of_one_le_of_one_le (one_le_inv (norm_pos_iff.mpr h) ha) hr
  have h' := hy (aâ»Â¹ â¢ r) h''
  rwa [smul_assoc, mem_inv_smul_set_iffâ h] at h'

theorem balanced_core_aux_maximal (h : t â s) (ht : Balanced ð t) : t â BalancedCoreAux ð s := by
  refine' fun x hx => mem_balanced_core_aux_iff.2 fun r hr => _
  rw [mem_smul_set_iff_inv_smul_memâ (norm_pos_iff.mp <| zero_lt_one.trans_le hr)]
  refine' h (ht.smul_mem _ hx)
  rw [norm_inv]
  exact inv_le_one hr

theorem balanced_core_subset_balanced_core_aux : BalancedCore ð s â BalancedCoreAux ð s :=
  balanced_core_aux_maximal (balanced_core_subset s) (balanced_core_balanced s)

theorem balanced_core_eq_Inter (hs : (0 : E) â s) : BalancedCore ð s = â (r : ð) (hr : 1 â¤ â¥râ¥), r â¢ s := by
  refine' balanced_core_subset_balanced_core_aux.antisymm _
  refine' (balanced_core_aux_balanced _).subset_core_of_subset (balanced_core_aux_subset s)
  exact balanced_core_subset_balanced_core_aux (balanced_core_zero_mem hs)

theorem subset_balanced_core (ht : (0 : E) â t) (hst : â (a : ð) (ha : â¥aâ¥ â¤ 1), a â¢ s â t) : s â BalancedCore ð t := by
  rw [balanced_core_eq_Inter ht]
  refine' subset_Interâ fun a ha => _
  rw [â smul_inv_smulâ (norm_pos_iff.mp <| zero_lt_one.trans_le ha) s]
  refine' smul_set_mono (hst _ _)
  rw [norm_inv]
  exact inv_le_one ha

end NormedField

end BalancedHull

/-! ### Topological properties -/


section Topology

variable [NondiscreteNormedField ð] [AddCommGroupâ E] [Module ð E] [TopologicalSpace E] [HasContinuousSmul ð E]
  {U : Set E}

protected theorem IsClosed.balanced_core (hU : IsClosed U) : IsClosed (BalancedCore ð U) := by
  by_cases' h : (0 : E) â U
  Â· rw [balanced_core_eq_Inter h]
    refine' is_closed_Inter fun a => _
    refine' is_closed_Inter fun ha => _
    have ha' := lt_of_lt_of_leâ zero_lt_one ha
    rw [norm_pos_iff] at ha'
    refine' is_closed_map_smul_of_ne_zero ha' U hU
    
  convert is_closed_empty
  contrapose! h
  exact balanced_core_nonempty_iff.mp (set.ne_empty_iff_nonempty.mp h)

theorem balanced_core_mem_nhds_zero (hU : U â ð (0 : E)) : BalancedCore ð U â ð (0 : E) := by
  -- Getting neighborhoods of the origin for `0 : ð` and `0 : E`
  obtain â¨r, V, hr, hV, hrVUâ© :
    â (r : â)(V : Set E), 0 < r â§ V â ð (0 : E) â§ â (c : ð) (y : E), â¥câ¥ < r â y â V â c â¢ y â U := by
    have h : Filter.Tendsto (fun x : ð Ã E => x.fst â¢ x.snd) (ð (0, 0)) (ð 0) :=
      continuous_smul.tendsto' (0, 0) _ (smul_zero _)
    simpa only [Prod.exists', Prod.forall', and_imp, And.assoc, â exists_prop] using
      h.basis_left (normed_group.nhds_zero_basis_norm_lt.prod_nhds (ð _).basis_sets) U hU
  rcases NormedField.exists_norm_lt ð hr with â¨y, hyâ, hyrâ©
  rw [norm_pos_iff] at hyâ
  have : y â¢ V â ð (0 : E) := (set_smul_mem_nhds_zero_iff hyâ).mpr hV
  -- It remains to show that `y â¢ V â balanced_core ð U`
  refine' Filter.mem_of_superset this ((subset_balanced_core (mem_of_mem_nhds hU)) fun a ha => _)
  rw [smul_smul]
  rintro _ â¨z, hz, rflâ©
  refine' hrVU _ _ _ hz
  rw [norm_mul, â one_mulâ r]
  exact mul_lt_mul' ha hyr (norm_nonneg y) one_pos

variable (ð E)

theorem nhds_basis_closed_balanced [T3Space E] :
    (ð (0 : E)).HasBasis (fun s : Set E => s â ð (0 : E) â§ IsClosed s â§ Balanced ð s) id := by
  refine' (closed_nhds_basis 0).to_has_basis (fun s hs => _) fun s hs => â¨s, â¨hs.1, hs.2.1â©, rfl.subsetâ©
  refine' â¨BalancedCore ð s, â¨balanced_core_mem_nhds_zero hs.1, _â©, balanced_core_subset sâ©
  exact â¨hs.2.BalancedCore, balanced_core_balanced sâ©

end Topology

