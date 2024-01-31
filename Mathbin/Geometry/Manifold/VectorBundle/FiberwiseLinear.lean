/-
Copyright (c) 2022 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Geometry.Manifold.ContMdiff

#align_import geometry.manifold.vector_bundle.fiberwise_linear from "leanprover-community/mathlib"@"30faa0c3618ce1472bf6305ae0e3fa56affa3f95"

/-! # The groupoid of smooth, fiberwise-linear maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains preliminaries for the definition of a smooth vector bundle: an associated
`structure_groupoid`, the groupoid of `smooth_fiberwise_linear` functions.
-/


noncomputable section

open Set TopologicalSpace

open scoped Manifold Topology

/-! ### The groupoid of smooth, fiberwise-linear maps -/


variable {𝕜 B F : Type _} [TopologicalSpace B]

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace FiberwiseLinear

variable {φ φ' : B → F ≃L[𝕜] F} {U U' : Set B}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FiberwiseLinear.partialHomeomorph /-
/-- For `B` a topological space and `F` a `𝕜`-normed space, a map from `U : set B` to `F ≃L[𝕜] F`
determines a local homeomorphism from `B × F` to itself by its action fiberwise. -/
def partialHomeomorph (φ : B → F ≃L[𝕜] F) (hU : IsOpen U)
    (hφ : ContinuousOn (fun x => φ x : B → F →L[𝕜] F) U)
    (h2φ : ContinuousOn (fun x => (φ x).symm : B → F →L[𝕜] F) U) : PartialHomeomorph (B × F) (B × F)
    where
  toFun x := (x.1, φ x.1 x.2)
  invFun x := (x.1, (φ x.1).symm x.2)
  source := U ×ˢ univ
  target := U ×ˢ univ
  map_source' x hx := mk_mem_prod hx.1 (mem_univ _)
  map_target' x hx := mk_mem_prod hx.1 (mem_univ _)
  left_inv' x _ := Prod.ext rfl (ContinuousLinearEquiv.symm_apply_apply _ _)
  right_inv' x _ := Prod.ext rfl (ContinuousLinearEquiv.apply_symm_apply _ _)
  open_source := hU.Prod isOpen_univ
  open_target := hU.Prod isOpen_univ
  continuous_toFun :=
    haveI : ContinuousOn (fun p : B × F => ((φ p.1 : F →L[𝕜] F), p.2)) (U ×ˢ univ) :=
      hφ.prod_map continuousOn_id
    continuous_on_fst.prod (is_bounded_bilinear_map_apply.continuous.comp_continuous_on this)
  continuous_invFun :=
    haveI : ContinuousOn (fun p : B × F => (((φ p.1).symm : F →L[𝕜] F), p.2)) (U ×ˢ univ) :=
      h2φ.prod_map continuousOn_id
    continuous_on_fst.prod (is_bounded_bilinear_map_apply.continuous.comp_continuous_on this)
#align fiberwise_linear.local_homeomorph FiberwiseLinear.partialHomeomorph
-/

#print FiberwiseLinear.trans_partialHomeomorph_apply /-
/-- Compute the composition of two local homeomorphisms induced by fiberwise linear
equivalences. -/
theorem trans_partialHomeomorph_apply (hU : IsOpen U)
    (hφ : ContinuousOn (fun x => φ x : B → F →L[𝕜] F) U)
    (h2φ : ContinuousOn (fun x => (φ x).symm : B → F →L[𝕜] F) U) (hU' : IsOpen U')
    (hφ' : ContinuousOn (fun x => φ' x : B → F →L[𝕜] F) U')
    (h2φ' : ContinuousOn (fun x => (φ' x).symm : B → F →L[𝕜] F) U') (b : B) (v : F) :
    (FiberwiseLinear.partialHomeomorph φ hU hφ h2φ ≫ₕ
          FiberwiseLinear.partialHomeomorph φ' hU' hφ' h2φ')
        ⟨b, v⟩ =
      ⟨b, φ' b (φ b v)⟩ :=
  rfl
#align fiberwise_linear.trans_local_homeomorph_apply FiberwiseLinear.trans_partialHomeomorph_apply
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FiberwiseLinear.source_trans_partialHomeomorph /-
/-- Compute the source of the composition of two local homeomorphisms induced by fiberwise linear
equivalences. -/
theorem source_trans_partialHomeomorph (hU : IsOpen U)
    (hφ : ContinuousOn (fun x => φ x : B → F →L[𝕜] F) U)
    (h2φ : ContinuousOn (fun x => (φ x).symm : B → F →L[𝕜] F) U) (hU' : IsOpen U')
    (hφ' : ContinuousOn (fun x => φ' x : B → F →L[𝕜] F) U')
    (h2φ' : ContinuousOn (fun x => (φ' x).symm : B → F →L[𝕜] F) U') :
    (FiberwiseLinear.partialHomeomorph φ hU hφ h2φ ≫ₕ
          FiberwiseLinear.partialHomeomorph φ' hU' hφ' h2φ').source =
      (U ∩ U') ×ˢ univ :=
  by dsimp only [FiberwiseLinear.partialHomeomorph]; mfld_set_tac
#align fiberwise_linear.source_trans_local_homeomorph FiberwiseLinear.source_trans_partialHomeomorph
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FiberwiseLinear.target_trans_partialHomeomorph /-
/-- Compute the target of the composition of two local homeomorphisms induced by fiberwise linear
equivalences. -/
theorem target_trans_partialHomeomorph (hU : IsOpen U)
    (hφ : ContinuousOn (fun x => φ x : B → F →L[𝕜] F) U)
    (h2φ : ContinuousOn (fun x => (φ x).symm : B → F →L[𝕜] F) U) (hU' : IsOpen U')
    (hφ' : ContinuousOn (fun x => φ' x : B → F →L[𝕜] F) U')
    (h2φ' : ContinuousOn (fun x => (φ' x).symm : B → F →L[𝕜] F) U') :
    (FiberwiseLinear.partialHomeomorph φ hU hφ h2φ ≫ₕ
          FiberwiseLinear.partialHomeomorph φ' hU' hφ' h2φ').target =
      (U ∩ U') ×ˢ univ :=
  by dsimp only [FiberwiseLinear.partialHomeomorph]; mfld_set_tac
#align fiberwise_linear.target_trans_local_homeomorph FiberwiseLinear.target_trans_partialHomeomorph
-/

end FiberwiseLinear

variable {EB : Type _} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type _}
  [TopologicalSpace HB] [ChartedSpace HB B] {IB : ModelWithCorners 𝕜 EB HB}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SmoothFiberwiseLinear.locality_aux₁ /-
/-- Let `e` be a local homeomorphism of `B × F`.  Suppose that at every point `p` in the source of
`e`, there is some neighbourhood `s` of `p` on which `e` is equal to a bi-smooth fiberwise linear
local homeomorphism.
Then the source of `e` is of the form `U ×ˢ univ`, for some set `U` in `B`, and, at any point `x` in
`U`, admits a neighbourhood `u` of `x` such that `e` is equal on `u ×ˢ univ` to some bi-smooth
fiberwise linear local homeomorphism. -/
theorem SmoothFiberwiseLinear.locality_aux₁ (e : PartialHomeomorph (B × F) (B × F))
    (h :
      ∀ p ∈ e.source,
        ∃ s : Set (B × F),
          IsOpen s ∧
            p ∈ s ∧
              ∃ (φ : B → F ≃L[𝕜] F) (u : Set B) (hu : IsOpen u) (hφ :
                SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun x => (φ x : F →L[𝕜] F)) u) (h2φ :
                SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun x => ((φ x).symm : F →L[𝕜] F)) u),
                (e.restr s).EqOnSource
                  (FiberwiseLinear.partialHomeomorph φ hu hφ.ContinuousOn h2φ.ContinuousOn)) :
    ∃ (U : Set B) (hU : e.source = U ×ˢ univ),
      ∀ x ∈ U,
        ∃ (φ : B → F ≃L[𝕜] F) (u : Set B) (hu : IsOpen u) (huU : u ⊆ U) (hux : x ∈ u) (hφ :
          SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun x => (φ x : F →L[𝕜] F)) u) (h2φ :
          SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun x => ((φ x).symm : F →L[𝕜] F)) u),
          (e.restr (u ×ˢ univ)).EqOnSource
            (FiberwiseLinear.partialHomeomorph φ hu hφ.ContinuousOn h2φ.ContinuousOn) :=
  by
  rw [SetCoe.forall'] at h 
  -- choose s hs hsp φ u hu hφ h2φ heφ using h,
  -- the following 2 lines should be `choose s hs hsp φ u hu hφ h2φ heφ using h,`
  -- `choose` produces a proof term that takes a long time to type-check by the kernel (it seems)
  -- porting note: todo: try using `choose` again in Lean 4
  simp only [Classical.skolem, ← exists_prop] at h 
  rcases h with ⟨s, hs, hsp, φ, u, hu, hφ, h2φ, heφ⟩
  have hesu : ∀ p : e.source, e.source ∩ s p = u p ×ˢ univ :=
    by
    intro p
    rw [← e.restr_source' (s _) (hs _)]
    exact (heφ p).1
  have hu' : ∀ p : e.source, (p : B × F).fst ∈ u p :=
    by
    intro p
    have : (p : B × F) ∈ e.source ∩ s p := ⟨p.prop, hsp p⟩
    simpa only [hesu, mem_prod, mem_univ, and_true_iff] using this
  have heu : ∀ p : e.source, ∀ q : B × F, q.fst ∈ u p → q ∈ e.source :=
    by
    intro p q hq
    have : q ∈ u p ×ˢ (univ : Set F) := ⟨hq, trivial⟩
    rw [← hesu p] at this 
    exact this.1
  have he : e.source = (Prod.fst '' e.source) ×ˢ (univ : Set F) :=
    by
    apply HasSubset.Subset.antisymm
    · intro p hp
      exact ⟨⟨p, hp, rfl⟩, trivial⟩
    · rintro ⟨x, v⟩ ⟨⟨p, hp, rfl : p.fst = x⟩, -⟩
      exact heu ⟨p, hp⟩ (p.fst, v) (hu' ⟨p, hp⟩)
  refine' ⟨Prod.fst '' e.source, he, _⟩
  rintro x ⟨p, hp, rfl⟩
  refine' ⟨φ ⟨p, hp⟩, u ⟨p, hp⟩, hu ⟨p, hp⟩, _, hu' _, hφ ⟨p, hp⟩, h2φ ⟨p, hp⟩, _⟩
  · intro y hy; refine' ⟨(y, 0), heu ⟨p, hp⟩ ⟨_, _⟩ hy, rfl⟩
  · rw [← hesu, e.restr_source_inter]; exact heφ ⟨p, hp⟩
#align smooth_fiberwise_linear.locality_aux₁ SmoothFiberwiseLinear.locality_aux₁
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr (_, _)]] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SmoothFiberwiseLinear.locality_aux₂ /-
/-- Let `e` be a local homeomorphism of `B × F` whose source is `U ×ˢ univ`, for some set `U` in
`B`, and which, at any point `x` in `U`, admits a neighbourhood `u` of `x` such that `e` is equal on
`u ×ˢ univ` to some bi-smooth fiberwise linear local homeomorphism.  Then `e` itself is equal to
some bi-smooth fiberwise linear local homeomorphism.

This is the key mathematical point of the `locality` condition in the construction of the
`structure_groupoid` of bi-smooth fiberwise linear local homeomorphisms.  The proof is by gluing
together the various bi-smooth fiberwise linear local homeomorphism which exist locally.

The `U` in the conclusion is the same `U` as in the hypothesis. We state it like this, because this
is exactly what we need for `smooth_fiberwise_linear`. -/
theorem SmoothFiberwiseLinear.locality_aux₂ (e : PartialHomeomorph (B × F) (B × F)) (U : Set B)
    (hU : e.source = U ×ˢ univ)
    (h :
      ∀ x ∈ U,
        ∃ (φ : B → F ≃L[𝕜] F) (u : Set B) (hu : IsOpen u) (hUu : u ⊆ U) (hux : x ∈ u) (hφ :
          SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun x => (φ x : F →L[𝕜] F)) u) (h2φ :
          SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun x => ((φ x).symm : F →L[𝕜] F)) u),
          (e.restr (u ×ˢ univ)).EqOnSource
            (FiberwiseLinear.partialHomeomorph φ hu hφ.ContinuousOn h2φ.ContinuousOn)) :
    ∃ (Φ : B → F ≃L[𝕜] F) (U : Set B) (hU₀ : IsOpen U) (hΦ :
      SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun x => (Φ x : F →L[𝕜] F)) U) (h2Φ :
      SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun x => ((Φ x).symm : F →L[𝕜] F)) U),
      e.EqOnSource (FiberwiseLinear.partialHomeomorph Φ hU₀ hΦ.ContinuousOn h2Φ.ContinuousOn) :=
  by classical
#align smooth_fiberwise_linear.locality_aux₂ SmoothFiberwiseLinear.locality_aux₂
-/

-- using rw on the next line seems to cause a timeout in kernel type-checking
variable (F B IB)

#print smoothFiberwiseLinear /-
/-- For `B` a manifold and `F` a normed space, the groupoid on `B × F` consisting of local
homeomorphisms which are bi-smooth and fiberwise linear, and induce the identity on `B`.
When a (topological) vector bundle is smooth, then the composition of charts associated
to the vector bundle belong to this groupoid. -/
def smoothFiberwiseLinear : StructureGroupoid (B × F)
    where
  members :=
    ⋃ (φ : B → F ≃L[𝕜] F) (U : Set B) (hU : IsOpen U) (hφ :
      SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun x => φ x : B → F →L[𝕜] F) U) (h2φ :
      SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun x => (φ x).symm : B → F →L[𝕜] F) U),
      {e | e.EqOnSource (FiberwiseLinear.partialHomeomorph φ hU hφ.ContinuousOn h2φ.ContinuousOn)}
  trans' := by
    simp_rw [mem_Union]
    rintro e e' ⟨φ, U, hU, hφ, h2φ, heφ⟩ ⟨φ', U', hU', hφ', h2φ', heφ'⟩
    refine'
      ⟨fun b => (φ b).trans (φ' b), _, hU.inter hU', _, _, Setoid.trans (heφ.trans' heφ') ⟨_, _⟩⟩
    · show
        SmoothOn IB 𝓘(𝕜, F →L[𝕜] F)
          (fun x : B => (φ' x).toContinuousLinearMap ∘L (φ x).toContinuousLinearMap) (U ∩ U')
      exact (hφ'.mono <| inter_subset_right _ _).clm_comp (hφ.mono <| inter_subset_left _ _)
    · show
        SmoothOn IB 𝓘(𝕜, F →L[𝕜] F)
          (fun x : B => (φ x).symm.toContinuousLinearMap ∘L (φ' x).symm.toContinuousLinearMap)
          (U ∩ U')
      exact (h2φ.mono <| inter_subset_left _ _).clm_comp (h2φ'.mono <| inter_subset_right _ _)
    · apply FiberwiseLinear.source_trans_partialHomeomorph
    · rintro ⟨b, v⟩ hb; apply FiberwiseLinear.trans_partialHomeomorph_apply
  symm' := by
    simp_rw [mem_Union]
    rintro e ⟨φ, U, hU, hφ, h2φ, heφ⟩
    refine' ⟨fun b => (φ b).symm, U, hU, h2φ, _, heφ.symm'⟩
    simp_rw [ContinuousLinearEquiv.symm_symm]
    exact hφ
  id_mem' := by
    simp_rw [mem_Union]
    refine' ⟨fun b => ContinuousLinearEquiv.refl 𝕜 F, univ, isOpen_univ, _, _, ⟨_, fun b hb => _⟩⟩
    · apply contMDiffOn_const
    · apply contMDiffOn_const
    ·
      simp only [FiberwiseLinear.partialHomeomorph, PartialHomeomorph.refl_partialEquiv,
        PartialEquiv.refl_source, univ_prod_univ]
    ·
      simp only [FiberwiseLinear.partialHomeomorph, PartialHomeomorph.refl_apply, Prod.mk.eta,
        id.def, ContinuousLinearEquiv.coe_refl', PartialHomeomorph.mk_coe, PartialEquiv.coe_mk]
  locality' :=
    by
    -- the hard work has been extracted to `locality_aux₁` and `locality_aux₂`
    simp_rw [mem_Union]
    intro e he
    obtain ⟨U, hU, h⟩ := SmoothFiberwiseLinear.locality_aux₁ e he
    exact SmoothFiberwiseLinear.locality_aux₂ e U hU h
  eq_on_source' := by
    simp_rw [mem_Union]
    rintro e e' ⟨φ, U, hU, hφ, h2φ, heφ⟩ hee'
    exact ⟨φ, U, hU, hφ, h2φ, Setoid.trans hee' heφ⟩
#align smooth_fiberwise_linear smoothFiberwiseLinear
-/

#print mem_smoothFiberwiseLinear_iff /-
@[simp]
theorem mem_smoothFiberwiseLinear_iff (e : PartialHomeomorph (B × F) (B × F)) :
    e ∈ smoothFiberwiseLinear B F IB ↔
      ∃ (φ : B → F ≃L[𝕜] F) (U : Set B) (hU : IsOpen U) (hφ :
        SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun x => φ x : B → F →L[𝕜] F) U) (h2φ :
        SmoothOn IB 𝓘(𝕜, F →L[𝕜] F) (fun x => (φ x).symm : B → F →L[𝕜] F) U),
        e.EqOnSource (FiberwiseLinear.partialHomeomorph φ hU hφ.ContinuousOn h2φ.ContinuousOn) :=
  show e ∈ Set.iUnion _ ↔ _ by simp only [mem_Union]; rfl
#align mem_smooth_fiberwise_linear_iff mem_smoothFiberwiseLinear_iff
-/

