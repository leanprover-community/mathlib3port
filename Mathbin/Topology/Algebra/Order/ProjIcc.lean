/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot
-/
import Mathbin.Data.Set.Intervals.ProjIcc
import Mathbin.Topology.Order.Basic

#align_import topology.algebra.order.proj_Icc from "leanprover-community/mathlib"@"50832daea47b195a48b5b33b1c8b2162c48c3afc"

/-!
# Projection onto a closed interval

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that the projection `set.proj_Icc f a b h` is a quotient map, and use it
to show that `Icc_extend h f` is continuous if and only if `f` is continuous.
-/


open Set Filter

open scoped Filter Topology

variable {α β γ : Type _} [LinearOrder α] [TopologicalSpace γ] {a b c : α} {h : a ≤ b}

#print Filter.Tendsto.IccExtend' /-
theorem Filter.Tendsto.IccExtend' (f : γ → Icc a b → β) {z : γ} {l : Filter α} {l' : Filter β}
    (hf : Tendsto (↿f) (𝓝 z ×ᶠ l.map (projIcc a b h)) l') :
    Tendsto (↿(IccExtend h ∘ f)) (𝓝 z ×ᶠ l) l' :=
  show Tendsto (↿f ∘ Prod.map id (projIcc a b h)) (𝓝 z ×ᶠ l) l' from
    hf.comp <| tendsto_id.Prod_map tendsto_map
#align filter.tendsto.Icc_extend Filter.Tendsto.IccExtend'
-/

variable [TopologicalSpace α] [OrderTopology α] [TopologicalSpace β]

#print continuous_projIcc /-
@[continuity]
theorem continuous_projIcc : Continuous (projIcc a b h) :=
  (continuous_const.max <| continuous_const.min continuous_id).subtype_mk _
#align continuous_proj_Icc continuous_projIcc
-/

#print quotientMap_projIcc /-
theorem quotientMap_projIcc : QuotientMap (projIcc a b h) :=
  quotientMap_iff.2
    ⟨projIcc_surjective h, fun s =>
      ⟨fun hs => hs.Preimage continuous_projIcc, fun hs => ⟨_, hs, by ext; simp⟩⟩⟩
#align quotient_map_proj_Icc quotientMap_projIcc
-/

#print continuous_IccExtend_iff /-
@[simp]
theorem continuous_IccExtend_iff {f : Icc a b → β} : Continuous (IccExtend h f) ↔ Continuous f :=
  quotientMap_projIcc.continuous_iff.symm
#align continuous_Icc_extend_iff continuous_IccExtend_iff
-/

#print Continuous.IccExtend /-
/-- See Note [continuity lemma statement]. -/
theorem Continuous.IccExtend {f : γ → Icc a b → β} {g : γ → α} (hf : Continuous ↿f)
    (hg : Continuous g) : Continuous fun a => IccExtend h (f a) (g a) :=
  hf.comp <| continuous_id.prod_mk <| continuous_projIcc.comp hg
#align continuous.Icc_extend Continuous.IccExtend
-/

#print Continuous.Icc_extend' /-
/-- A useful special case of `continuous.Icc_extend`. -/
@[continuity]
theorem Continuous.Icc_extend' {f : Icc a b → β} (hf : Continuous f) : Continuous (IccExtend h f) :=
  hf.comp continuous_projIcc
#align continuous.Icc_extend' Continuous.Icc_extend'
-/

#print ContinuousAt.IccExtend /-
theorem ContinuousAt.IccExtend {x : γ} (f : γ → Icc a b → β) {g : γ → α}
    (hf : ContinuousAt (↿f) (x, projIcc a b h (g x))) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => IccExtend h (f a) (g a)) x :=
  show ContinuousAt (↿f ∘ fun x => (x, projIcc a b h (g x))) x from
    ContinuousAt.comp hf <| continuousAt_id.Prod <| continuous_projIcc.ContinuousAt.comp hg
#align continuous_at.Icc_extend ContinuousAt.IccExtend
-/

