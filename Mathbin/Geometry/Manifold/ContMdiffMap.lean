/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri

! This file was ported from Lean 3 source module geometry.manifold.cont_mdiff_map
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Geometry.Manifold.ContMdiffMfderiv
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
  {M'' : Type _} [TopologicalSpace M''] [ChartedSpace H'' M''] (n : ℕ∞)

/-- Bundled `n` times continuously differentiable maps. -/
@[protect_proj]
structure ContMdiffMap where
  toFun : M → M'
  contMdiff_toFun : ContMdiff I I' n to_fun
#align cont_mdiff_map ContMdiffMap

/-- Bundled smooth maps. -/
@[reducible]
def SmoothMap :=
  ContMdiffMap I I' M M' ⊤
#align smooth_map SmoothMap

-- mathport name: cont_mdiff_map
scoped[Manifold] notation "C^" n "⟮" I ", " M "; " I' ", " M' "⟯" => ContMdiffMap I I' M M' n

-- mathport name: cont_mdiff_map.self
scoped[Manifold]
  notation "C^" n "⟮" I ", " M "; " k "⟯" => ContMdiffMap I (modelWithCornersSelf k k) M k n

open Manifold

namespace ContMdiffMap

variable {I} {I'} {M} {M'} {n}

instance : CoeFun C^n⟮I, M; I', M'⟯ fun _ => M → M' :=
  ⟨ContMdiffMap.toFun⟩

instance : Coe C^n⟮I, M; I', M'⟯ C(M, M') :=
  ⟨fun f => ⟨f, f.contMdiff_toFun.Continuous⟩⟩

attribute [to_additive_ignore_args 21]
  ContMdiffMap ContMdiffMap.hasCoeToFun ContMdiffMap.ContinuousMap.hasCoe

variable {f g : C^n⟮I, M; I', M'⟯}

@[simp]
theorem coeFn_mk (f : M → M') (hf : ContMdiff I I' n f) : (mk f hf : M → M') = f :=
  rfl
#align cont_mdiff_map.coe_fn_mk ContMdiffMap.coeFn_mk

protected theorem contMdiff (f : C^n⟮I, M; I', M'⟯) : ContMdiff I I' n f :=
  f.contMdiff_toFun
#align cont_mdiff_map.cont_mdiff ContMdiffMap.contMdiff

protected theorem smooth (f : C^∞⟮I, M; I', M'⟯) : Smooth I I' f :=
  f.contMdiff_toFun
#align cont_mdiff_map.smooth ContMdiffMap.smooth

protected theorem mdifferentiable' (f : C^n⟮I, M; I', M'⟯) (hn : 1 ≤ n) : Mdifferentiable I I' f :=
  f.ContMdiff.Mdifferentiable hn
#align cont_mdiff_map.mdifferentiable' ContMdiffMap.mdifferentiable'

protected theorem mdifferentiable (f : C^∞⟮I, M; I', M'⟯) : Mdifferentiable I I' f :=
  f.ContMdiff.Mdifferentiable le_top
#align cont_mdiff_map.mdifferentiable ContMdiffMap.mdifferentiable

protected theorem mdifferentiableAt (f : C^∞⟮I, M; I', M'⟯) {x} : MdifferentiableAt I I' f x :=
  f.Mdifferentiable x
#align cont_mdiff_map.mdifferentiable_at ContMdiffMap.mdifferentiableAt

theorem coe_inj ⦃f g : C^n⟮I, M; I', M'⟯⦄ (h : (f : M → M') = g) : f = g := by
  cases f <;> cases g <;> cases h <;> rfl
#align cont_mdiff_map.coe_inj ContMdiffMap.coe_inj

@[ext]
theorem ext (h : ∀ x, f x = g x) : f = g := by cases f <;> cases g <;> congr <;> exact funext h
#align cont_mdiff_map.ext ContMdiffMap.ext

/-- The identity as a smooth map. -/
def id : C^n⟮I, M; I, M⟯ :=
  ⟨id, contMdiff_id⟩
#align cont_mdiff_map.id ContMdiffMap.id

/-- The composition of smooth maps, as a smooth map. -/
def comp (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) : C^n⟮I, M; I'', M''⟯
    where
  toFun a := f (g a)
  contMdiff_toFun := f.contMdiff_toFun.comp g.contMdiff_toFun
#align cont_mdiff_map.comp ContMdiffMap.comp

@[simp]
theorem comp_apply (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) (x : M) :
    f.comp g x = f (g x) :=
  rfl
#align cont_mdiff_map.comp_apply ContMdiffMap.comp_apply

instance [Inhabited M'] : Inhabited C^n⟮I, M; I', M'⟯ :=
  ⟨⟨fun _ => default, contMdiff_const⟩⟩

/-- Constant map as a smooth map -/
def const (y : M') : C^n⟮I, M; I', M'⟯ :=
  ⟨fun x => y, contMdiff_const⟩
#align cont_mdiff_map.const ContMdiffMap.const

end ContMdiffMap

instance ContinuousLinearMap.hasCoeToContMdiffMap :
    Coe (E →L[𝕜] E') C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, E'), E'⟯ :=
  ⟨fun f => ⟨f.toFun, f.ContMdiff⟩⟩
#align continuous_linear_map.has_coe_to_cont_mdiff_map ContinuousLinearMap.hasCoeToContMdiffMap

