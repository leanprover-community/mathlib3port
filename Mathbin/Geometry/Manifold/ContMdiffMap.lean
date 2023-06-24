/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri

! This file was ported from Lean 3 source module geometry.manifold.cont_mdiff_map
! leanprover-community/mathlib commit 86c29aefdba50b3f33e86e52e3b2f51a0d8f0282
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Geometry.Manifold.ContMdiff
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Smooth bundled map

In this file we define the type `cont_mdiff_map` of `n` times continuously differentiable
bundled maps.
-/


variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type _}
  [TopologicalSpace H] {H' : Type _} [TopologicalSpace H'] (I : ModelWithCorners 𝕜 E H)
  (I' : ModelWithCorners 𝕜 E' H') (M : Type _) [TopologicalSpace M] [ChartedSpace H M] (M' : Type _)
  [TopologicalSpace M'] [ChartedSpace H' M'] {E'' : Type _} [NormedAddCommGroup E'']
  [NormedSpace 𝕜 E''] {H'' : Type _} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type _} [TopologicalSpace M''] [ChartedSpace H'' M'']
  -- declare a manifold `N` over the pair `(F, G)`.
  {F : Type _}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type _} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type _} [TopologicalSpace N] [ChartedSpace G N] (n : ℕ∞)

#print ContMDiffMap /-
/-- Bundled `n` times continuously differentiable maps. -/
def ContMDiffMap :=
  { f : M → M' // ContMDiff I I' n f }
#align cont_mdiff_map ContMDiffMap
-/

#print SmoothMap /-
/-- Bundled smooth maps. -/
@[reducible]
def SmoothMap :=
  ContMDiffMap I I' M M' ⊤
#align smooth_map SmoothMap
-/

scoped[Manifold] notation "C^" n "⟮" I ", " M "; " I' ", " M' "⟯" => ContMDiffMap I I' M M' n

scoped[Manifold]
  notation "C^" n "⟮" I ", " M "; " k "⟯" => ContMDiffMap I (modelWithCornersSelf k k) M k n

open scoped Manifold

namespace ContMDiffMap

variable {I} {I'} {M} {M'} {n}

#print ContMDiffMap.funLike /-
instance funLike : FunLike C^n⟮I, M; I', M'⟯ M fun _ => M'
    where
  coe := Subtype.val
  coe_injective' := Subtype.coe_injective
#align cont_mdiff_map.fun_like ContMDiffMap.funLike
-/

#print ContMDiffMap.contMDiff /-
protected theorem contMDiff (f : C^n⟮I, M; I', M'⟯) : ContMDiff I I' n f :=
  f.Prop
#align cont_mdiff_map.cont_mdiff ContMDiffMap.contMDiff
-/

#print ContMDiffMap.smooth /-
protected theorem smooth (f : C^∞⟮I, M; I', M'⟯) : Smooth I I' f :=
  f.Prop
#align cont_mdiff_map.smooth ContMDiffMap.smooth
-/

instance : Coe C^n⟮I, M; I', M'⟯ C(M, M') :=
  ⟨fun f => ⟨f, f.ContMDiff.Continuous⟩⟩

attribute [to_additive_ignore_args 21] ContMDiffMap ContMDiffMap.funLike
  ContMDiffMap.ContinuousMap.hasCoe

variable {f g : C^n⟮I, M; I', M'⟯}

#print ContMDiffMap.coeFn_mk /-
@[simp]
theorem coeFn_mk (f : M → M') (hf : ContMDiff I I' n f) :
    ((Subtype.mk f hf : C^n⟮I, M; I', M'⟯) : M → M') = f :=
  rfl
#align cont_mdiff_map.coe_fn_mk ContMDiffMap.coeFn_mk
-/

#print ContMDiffMap.coe_injective /-
theorem coe_injective ⦃f g : C^n⟮I, M; I', M'⟯⦄ (h : (f : M → M') = g) : f = g := by
  cases f <;> cases g <;> cases h <;> rfl
#align cont_mdiff_map.coe_inj ContMDiffMap.coe_injective
-/

#print ContMDiffMap.ext /-
@[ext]
theorem ext (h : ∀ x, f x = g x) : f = g := by cases f <;> cases g <;> congr <;> exact funext h
#align cont_mdiff_map.ext ContMDiffMap.ext
-/

instance : ContinuousMapClass C^n⟮I, M; I', M'⟯ M M'
    where
  coe f := ⇑f
  coe_injective' := coe_injective
  map_continuous f := f.ContMDiff.Continuous

#print ContMDiffMap.id /-
/-- The identity as a smooth map. -/
def id : C^n⟮I, M; I, M⟯ :=
  ⟨id, contMDiff_id⟩
#align cont_mdiff_map.id ContMDiffMap.id
-/

#print ContMDiffMap.comp /-
/-- The composition of smooth maps, as a smooth map. -/
def comp (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) : C^n⟮I, M; I'', M''⟯
    where
  val a := f (g a)
  property := f.ContMDiff.comp g.ContMDiff
#align cont_mdiff_map.comp ContMDiffMap.comp
-/

#print ContMDiffMap.comp_apply /-
@[simp]
theorem comp_apply (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) (x : M) :
    f.comp g x = f (g x) :=
  rfl
#align cont_mdiff_map.comp_apply ContMDiffMap.comp_apply
-/

instance [Inhabited M'] : Inhabited C^n⟮I, M; I', M'⟯ :=
  ⟨⟨fun _ => default, contMDiff_const⟩⟩

#print ContMDiffMap.const /-
/-- Constant map as a smooth map -/
def const (y : M') : C^n⟮I, M; I', M'⟯ :=
  ⟨fun x => y, contMDiff_const⟩
#align cont_mdiff_map.const ContMDiffMap.const
-/

#print ContMDiffMap.fst /-
/-- The first projection of a product, as a smooth map. -/
def fst : C^n⟮I.Prod I', M × M'; I, M⟯ :=
  ⟨Prod.fst, contMDiff_fst⟩
#align cont_mdiff_map.fst ContMDiffMap.fst
-/

#print ContMDiffMap.snd /-
/-- The second projection of a product, as a smooth map. -/
def snd : C^n⟮I.Prod I', M × M'; I', M'⟯ :=
  ⟨Prod.snd, contMDiff_snd⟩
#align cont_mdiff_map.snd ContMDiffMap.snd
-/

#print ContMDiffMap.prodMk /-
/-- Given two smooth maps `f` and `g`, this is the smooth map `x ↦ (f x, g x)`. -/
def prodMk (f : C^n⟮J, N; I, M⟯) (g : C^n⟮J, N; I', M'⟯) : C^n⟮J, N; I.Prod I', M × M'⟯ :=
  ⟨fun x => (f x, g x), f.2.prod_mk g.2⟩
#align cont_mdiff_map.prod_mk ContMDiffMap.prodMk
-/

end ContMDiffMap

#print ContinuousLinearMap.hasCoeToContMDiffMap /-
instance ContinuousLinearMap.hasCoeToContMDiffMap :
    Coe (E →L[𝕜] E') C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, E'), E'⟯ :=
  ⟨fun f => ⟨f.toFun, f.ContMDiff⟩⟩
#align continuous_linear_map.has_coe_to_cont_mdiff_map ContinuousLinearMap.hasCoeToContMDiffMap
-/

