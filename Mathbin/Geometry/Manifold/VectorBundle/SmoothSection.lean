/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn
-/
import Geometry.Manifold.ContMdiffMfderiv
import Topology.ContinuousFunction.Basic
import Geometry.Manifold.Algebra.LieGroup

#align_import geometry.manifold.vector_bundle.smooth_section from "leanprover-community/mathlib"@"1a51edf13debfcbe223fa06b1cb353b9ed9751cc"

/-!
# Smooth sections

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the type `cont_mdiff_section` of `n` times continuously differentiable
sections of a smooth vector bundle over a manifold `M` and prove that it's a module.
-/


open Bundle Filter Function

open scoped Bundle Manifold

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type _}
  [TopologicalSpace H] {H' : Type _} [TopologicalSpace H'] (I : ModelWithCorners 𝕜 E H)
  (I' : ModelWithCorners 𝕜 E' H') {M : Type _} [TopologicalSpace M] [ChartedSpace H M] {M' : Type _}
  [TopologicalSpace M'] [ChartedSpace H' M'] {E'' : Type _} [NormedAddCommGroup E'']
  [NormedSpace 𝕜 E''] {H'' : Type _} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type _} [TopologicalSpace M''] [ChartedSpace H'' M''] [SmoothManifoldWithCorners I M]

variable (F : Type _) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : ℕ∞)
  (V : M → Type _) [TopologicalSpace (TotalSpace F V)]
  -- `V` vector bundle
  [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)]

variable [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [SmoothVectorBundle F V I]

#print ContMDiffSection /-
/-- Bundled `n` times continuously differentiable sections of a vector bundle. -/
@[protect_proj]
structure ContMDiffSection where
  toFun : ∀ x, V x
  contMDiff_toFun : ContMDiff I (I.Prod 𝓘(𝕜, F)) n fun x => (total_space.mk' F) x (to_fun x)
#align cont_mdiff_section ContMDiffSection
-/

#print SmoothSection /-
/-- Bundled smooth sections of a vector bundle. -/
@[reducible]
def SmoothSection :=
  ContMDiffSection I F ⊤ V
#align smooth_section SmoothSection
-/

scoped[Manifold] notation "Cₛ^" n "⟮" I "; " F ", " V "⟯" => ContMDiffSection I F n V

namespace ContMDiffSection

variable {I} {I'} {n} {F} {V}

instance : CoeFun Cₛ^n⟮I; F, V⟯ fun s => ∀ x, V x :=
  ⟨ContMDiffSection.toFun⟩

variable {s t : Cₛ^n⟮I; F, V⟯}

#print ContMDiffSection.coeFn_mk /-
@[simp]
theorem coeFn_mk (s : ∀ x, V x)
    (hs : ContMDiff I (I.Prod 𝓘(𝕜, F)) n fun x => TotalSpace.mk x (s x)) :
    (mk s hs : ∀ x, V x) = s :=
  rfl
#align cont_mdiff_section.coe_fn_mk ContMDiffSection.coeFn_mk
-/

#print ContMDiffSection.contMDiff /-
protected theorem contMDiff (s : Cₛ^n⟮I; F, V⟯) :
    ContMDiff I (I.Prod 𝓘(𝕜, F)) n fun x => (total_space.mk' F) x (s x : V x) :=
  s.contMDiff_toFun
#align cont_mdiff_section.cont_mdiff ContMDiffSection.contMDiff
-/

#print ContMDiffSection.smooth /-
protected theorem smooth (s : Cₛ^∞⟮I; F, V⟯) :
    Smooth I (I.Prod 𝓘(𝕜, F)) fun x => (total_space.mk' F) x (s x : V x) :=
  s.contMDiff_toFun
#align cont_mdiff_section.smooth ContMDiffSection.smooth
-/

#print ContMDiffSection.mdifferentiable' /-
protected theorem mdifferentiable' (s : Cₛ^n⟮I; F, V⟯) (hn : 1 ≤ n) :
    MDifferentiable I (I.Prod 𝓘(𝕜, F)) fun x => (total_space.mk' F) x (s x : V x) :=
  s.ContMDiff.MDifferentiable hn
#align cont_mdiff_section.mdifferentiable' ContMDiffSection.mdifferentiable'
-/

#print ContMDiffSection.mdifferentiable /-
protected theorem mdifferentiable (s : Cₛ^∞⟮I; F, V⟯) :
    MDifferentiable I (I.Prod 𝓘(𝕜, F)) fun x => (total_space.mk' F) x (s x : V x) :=
  s.ContMDiff.MDifferentiable le_top
#align cont_mdiff_section.mdifferentiable ContMDiffSection.mdifferentiable
-/

#print ContMDiffSection.mdifferentiableAt /-
protected theorem mdifferentiableAt (s : Cₛ^∞⟮I; F, V⟯) {x} :
    MDifferentiableAt I (I.Prod 𝓘(𝕜, F)) (fun x => (total_space.mk' F) x (s x : V x)) x :=
  s.MDifferentiable x
#align cont_mdiff_section.mdifferentiable_at ContMDiffSection.mdifferentiableAt
-/

#print ContMDiffSection.coe_inj /-
theorem coe_inj ⦃s t : Cₛ^n⟮I; F, V⟯⦄ (h : (s : ∀ x, V x) = t) : s = t := by
  cases s <;> cases t <;> cases h <;> rfl
#align cont_mdiff_section.coe_inj ContMDiffSection.coe_inj
-/

#print ContMDiffSection.coe_injective /-
theorem coe_injective : Injective (coeFn : Cₛ^n⟮I; F, V⟯ → ∀ x, V x) :=
  coe_inj
#align cont_mdiff_section.coe_injective ContMDiffSection.coe_injective
-/

#print ContMDiffSection.ext /-
@[ext]
theorem ext (h : ∀ x, s x = t x) : s = t := by cases s <;> cases t <;> congr <;> exact funext h
#align cont_mdiff_section.ext ContMDiffSection.ext
-/

#print ContMDiffSection.instAdd /-
instance instAdd : Add Cₛ^n⟮I; F, V⟯ :=
  by
  refine' ⟨fun s t => ⟨s + t, _⟩⟩
  intro x₀
  have hs := s.cont_mdiff x₀
  have ht := t.cont_mdiff x₀
  rw [cont_mdiff_at_section] at hs ht ⊢
  set e := trivialization_at F V x₀
  refine' (hs.add ht).congr_of_eventuallyEq _
  refine' eventually_of_mem (e.open_base_set.mem_nhds <| mem_base_set_trivialization_at F V x₀) _
  intro x hx
  apply (e.linear 𝕜 hx).1
#align cont_mdiff_section.has_add ContMDiffSection.instAdd
-/

#print ContMDiffSection.coe_add /-
@[simp]
theorem coe_add (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s + t) = s + t :=
  rfl
#align cont_mdiff_section.coe_add ContMDiffSection.coe_add
-/

#print ContMDiffSection.instSub /-
instance instSub : Sub Cₛ^n⟮I; F, V⟯ :=
  by
  refine' ⟨fun s t => ⟨s - t, _⟩⟩
  intro x₀
  have hs := s.cont_mdiff x₀
  have ht := t.cont_mdiff x₀
  rw [cont_mdiff_at_section] at hs ht ⊢
  set e := trivialization_at F V x₀
  refine' (hs.sub ht).congr_of_eventuallyEq _
  refine' eventually_of_mem (e.open_base_set.mem_nhds <| mem_base_set_trivialization_at F V x₀) _
  intro x hx
  apply (e.linear 𝕜 hx).map_sub
#align cont_mdiff_section.has_sub ContMDiffSection.instSub
-/

#print ContMDiffSection.coe_sub /-
@[simp]
theorem coe_sub (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s - t) = s - t :=
  rfl
#align cont_mdiff_section.coe_sub ContMDiffSection.coe_sub
-/

#print ContMDiffSection.instZero /-
instance instZero : Zero Cₛ^n⟮I; F, V⟯ :=
  ⟨⟨fun x => 0, (smooth_zeroSection 𝕜 V).of_le le_top⟩⟩
#align cont_mdiff_section.has_zero ContMDiffSection.instZero
-/

#print ContMDiffSection.inhabited /-
instance inhabited : Inhabited Cₛ^n⟮I; F, V⟯ :=
  ⟨0⟩
#align cont_mdiff_section.inhabited ContMDiffSection.inhabited
-/

#print ContMDiffSection.coe_zero /-
@[simp]
theorem coe_zero : ⇑(0 : Cₛ^n⟮I; F, V⟯) = 0 :=
  rfl
#align cont_mdiff_section.coe_zero ContMDiffSection.coe_zero
-/

#print ContMDiffSection.instSMul /-
instance instSMul : SMul 𝕜 Cₛ^n⟮I; F, V⟯ :=
  by
  refine' ⟨fun c s => ⟨c • s, _⟩⟩
  intro x₀
  have hs := s.cont_mdiff x₀
  rw [cont_mdiff_at_section] at hs ⊢
  set e := trivialization_at F V x₀
  refine' (cont_mdiff_at_const.smul hs).congr_of_eventuallyEq _
  · exact c
  refine' eventually_of_mem (e.open_base_set.mem_nhds <| mem_base_set_trivialization_at F V x₀) _
  intro x hx
  apply (e.linear 𝕜 hx).2
#align cont_mdiff_section.has_smul ContMDiffSection.instSMul
-/

#print ContMDiffSection.coe_smul /-
@[simp]
theorem coe_smul (r : 𝕜) (s : Cₛ^n⟮I; F, V⟯) : ⇑(r • s : Cₛ^n⟮I; F, V⟯) = r • s :=
  rfl
#align cont_mdiff_section.coe_smul ContMDiffSection.coe_smul
-/

#print ContMDiffSection.instNeg /-
instance instNeg : Neg Cₛ^n⟮I; F, V⟯ :=
  by
  refine' ⟨fun s => ⟨-s, _⟩⟩
  intro x₀
  have hs := s.cont_mdiff x₀
  rw [cont_mdiff_at_section] at hs ⊢
  set e := trivialization_at F V x₀
  refine' hs.neg.congr_of_eventually_eq _
  refine' eventually_of_mem (e.open_base_set.mem_nhds <| mem_base_set_trivialization_at F V x₀) _
  intro x hx
  apply (e.linear 𝕜 hx).map_neg
#align cont_mdiff_section.has_neg ContMDiffSection.instNeg
-/

#print ContMDiffSection.coe_neg /-
@[simp]
theorem coe_neg (s : Cₛ^n⟮I; F, V⟯) : ⇑(-s : Cₛ^n⟮I; F, V⟯) = -s :=
  rfl
#align cont_mdiff_section.coe_neg ContMDiffSection.coe_neg
-/

#print ContMDiffSection.instNSMul /-
instance instNSMul : SMul ℕ Cₛ^n⟮I; F, V⟯ :=
  ⟨nsmulRec⟩
#align cont_mdiff_section.has_nsmul ContMDiffSection.instNSMul
-/

#print ContMDiffSection.coe_nsmul /-
@[simp]
theorem coe_nsmul (s : Cₛ^n⟮I; F, V⟯) (k : ℕ) : ⇑(k • s : Cₛ^n⟮I; F, V⟯) = k • s :=
  by
  induction' k with k ih
  · simp_rw [zero_smul]; rfl
  simp_rw [succ_nsmul, ← ih]; rfl
#align cont_mdiff_section.coe_nsmul ContMDiffSection.coe_nsmul
-/

#print ContMDiffSection.instZSMul /-
instance instZSMul : SMul ℤ Cₛ^n⟮I; F, V⟯ :=
  ⟨zsmulRec⟩
#align cont_mdiff_section.has_zsmul ContMDiffSection.instZSMul
-/

#print ContMDiffSection.coe_zsmul /-
@[simp]
theorem coe_zsmul (s : Cₛ^n⟮I; F, V⟯) (z : ℤ) : ⇑(z • s : Cₛ^n⟮I; F, V⟯) = z • s :=
  by
  cases' z with n n
  refine' (coe_nsmul s n).trans _
  simp only [Int.ofNat_eq_coe, coe_nat_zsmul]
  refine' (congr_arg Neg.neg (coe_nsmul s (n + 1))).trans _
  simp only [negSucc_zsmul, neg_inj]
#align cont_mdiff_section.coe_zsmul ContMDiffSection.coe_zsmul
-/

#print ContMDiffSection.instAddCommGroup /-
instance instAddCommGroup : AddCommGroup Cₛ^n⟮I; F, V⟯ :=
  coe_injective.AddCommGroup _ coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul
#align cont_mdiff_section.add_comm_group ContMDiffSection.instAddCommGroup
-/

variable (I F V n)

#print ContMDiffSection.coeAddHom /-
/-- The additive morphism from smooth sections to dependent maps. -/
def coeAddHom : Cₛ^n⟮I; F, V⟯ →+ ∀ x, V x
    where
  toFun := coeFn
  map_zero' := coe_zero
  map_add' := coe_add
#align cont_mdiff_section.coe_add_hom ContMDiffSection.coeAddHom
-/

variable {I F V n}

#print ContMDiffSection.instModule /-
instance instModule : Module 𝕜 Cₛ^n⟮I; F, V⟯ :=
  coe_injective.Module 𝕜 (coeAddHom I F n V) coe_smul
#align cont_mdiff_section.module ContMDiffSection.instModule
-/

end ContMDiffSection

