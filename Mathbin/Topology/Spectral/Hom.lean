/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module topology.spectral.hom
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Spectral maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines spectral maps. A map is spectral when it's continuous and the preimage of a
compact open set is compact open.

## Main declarations

* `is_spectral_map`: Predicate for a map to be spectral.
* `spectral_map`: Bundled spectral maps.
* `spectral_map_class`: Typeclass for a type to be a type of spectral maps.

## TODO

Once we have `spectral_space`, `is_spectral_map` should move to `topology.spectral.basic`.
-/


open Function OrderDual

variable {F α β γ δ : Type _}

section Unbundled

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] {f : α → β} {s : Set β}

#print IsSpectralMap /-
/-- A function between topological spaces is spectral if it is continuous and the preimage of every
compact open set is compact open. -/
structure IsSpectralMap (f : α → β) extends Continuous f : Prop where
  isCompact_preimage_of_isOpen ⦃s : Set β⦄ : IsOpen s → IsCompact s → IsCompact (f ⁻¹' s)
#align is_spectral_map IsSpectralMap
-/

/- warning: is_compact.preimage_of_is_open -> IsCompact.preimage_of_isOpen is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u2} β}, (IsSpectralMap.{u1, u2} α β _inst_1 _inst_2 f) -> (IsCompact.{u2} β _inst_2 s) -> (IsOpen.{u2} β _inst_2 s) -> (IsCompact.{u1} α _inst_1 (Set.preimage.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u1} β}, (IsSpectralMap.{u2, u1} α β _inst_1 _inst_2 f) -> (IsCompact.{u1} β _inst_2 s) -> (IsOpen.{u1} β _inst_2 s) -> (IsCompact.{u2} α _inst_1 (Set.preimage.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align is_compact.preimage_of_is_open IsCompact.preimage_of_isOpenₓ'. -/
theorem IsCompact.preimage_of_isOpen (hf : IsSpectralMap f) (h₀ : IsCompact s) (h₁ : IsOpen s) :
    IsCompact (f ⁻¹' s) :=
  hf.isCompact_preimage_of_isOpen h₁ h₀
#align is_compact.preimage_of_is_open IsCompact.preimage_of_isOpen

/- warning: is_spectral_map.continuous -> IsSpectralMap.continuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, (IsSpectralMap.{u1, u2} α β _inst_1 _inst_2 f) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, (IsSpectralMap.{u2, u1} α β _inst_1 _inst_2 f) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align is_spectral_map.continuous IsSpectralMap.continuousₓ'. -/
theorem IsSpectralMap.continuous {f : α → β} (hf : IsSpectralMap f) : Continuous f :=
  hf.to_continuous
#align is_spectral_map.continuous IsSpectralMap.continuous

#print isSpectralMap_id /-
theorem isSpectralMap_id : IsSpectralMap (@id α) :=
  ⟨continuous_id, fun s _ => id⟩
#align is_spectral_map_id isSpectralMap_id
-/

/- warning: is_spectral_map.comp -> IsSpectralMap.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : β -> γ} {g : α -> β}, (IsSpectralMap.{u2, u3} β γ _inst_2 _inst_3 f) -> (IsSpectralMap.{u1, u2} α β _inst_1 _inst_2 g) -> (IsSpectralMap.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ f g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] {f : β -> γ} {g : α -> β}, (IsSpectralMap.{u3, u2} β γ _inst_2 _inst_3 f) -> (IsSpectralMap.{u1, u3} α β _inst_1 _inst_2 g) -> (IsSpectralMap.{u1, u2} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u3, succ u2} α β γ f g))
Case conversion may be inaccurate. Consider using '#align is_spectral_map.comp IsSpectralMap.compₓ'. -/
theorem IsSpectralMap.comp {f : β → γ} {g : α → β} (hf : IsSpectralMap f) (hg : IsSpectralMap g) :
    IsSpectralMap (f ∘ g) :=
  ⟨hf.Continuous.comp hg.Continuous, fun s hs₀ hs₁ =>
    (hs₁.preimage_of_isOpen hf hs₀).preimage_of_isOpen hg (hs₀.Preimage hf.Continuous)⟩
#align is_spectral_map.comp IsSpectralMap.comp

end Unbundled

#print SpectralMap /-
/-- The type of spectral maps from `α` to `β`. -/
structure SpectralMap (α β : Type _) [TopologicalSpace α] [TopologicalSpace β] where
  toFun : α → β
  spectral' : IsSpectralMap to_fun
#align spectral_map SpectralMap
-/

section

#print SpectralMapClass /-
/-- `spectral_map_class F α β` states that `F` is a type of spectral maps.

You should extend this class when you extend `spectral_map`. -/
class SpectralMapClass (F : Type _) (α β : outParam <| Type _) [TopologicalSpace α]
  [TopologicalSpace β] extends FunLike F α fun _ => β where
  map_spectral (f : F) : IsSpectralMap f
#align spectral_map_class SpectralMapClass
-/

end

export SpectralMapClass (map_spectral)

attribute [simp] map_spectral

#print SpectralMapClass.toContinuousMapClass /-
-- See note [lower instance priority]
instance (priority := 100) SpectralMapClass.toContinuousMapClass [TopologicalSpace α]
    [TopologicalSpace β] [SpectralMapClass F α β] : ContinuousMapClass F α β :=
  { ‹SpectralMapClass F α β› with map_continuous := fun f => (map_spectral f).Continuous }
#align spectral_map_class.to_continuous_map_class SpectralMapClass.toContinuousMapClass
-/

instance [TopologicalSpace α] [TopologicalSpace β] [SpectralMapClass F α β] :
    CoeTC F (SpectralMap α β) :=
  ⟨fun f => ⟨_, map_spectral f⟩⟩

/-! ### Spectral maps -/


namespace SpectralMap

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

#print SpectralMap.toContinuousMap /-
/-- Reinterpret a `spectral_map` as a `continuous_map`. -/
def toContinuousMap (f : SpectralMap α β) : ContinuousMap α β :=
  ⟨_, f.spectral'.Continuous⟩
#align spectral_map.to_continuous_map SpectralMap.toContinuousMap
-/

instance : SpectralMapClass (SpectralMap α β) α β
    where
  coe := SpectralMap.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
  map_spectral f := f.spectral'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (SpectralMap α β) fun _ => α → β :=
  FunLike.hasCoeToFun

/- warning: spectral_map.to_fun_eq_coe -> SpectralMap.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : SpectralMap.{u1, u2} α β _inst_1 _inst_2}, Eq.{max (succ u1) (succ u2)} (α -> β) (SpectralMap.toFun.{u1, u2} α β _inst_1 _inst_2 f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SpectralMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SpectralMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : SpectralMap.{u2, u1} α β _inst_1 _inst_2}, Eq.{max (succ u2) (succ u1)} (α -> β) (SpectralMap.toFun.{u2, u1} α β _inst_1 _inst_2 f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (SpectralMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => β) _x) (SpectralMapClass.toFunLike.{max u2 u1, u2, u1} (SpectralMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SpectralMap.instSpectralMapClassSpectralMap.{u2, u1} α β _inst_1 _inst_2)) f)
Case conversion may be inaccurate. Consider using '#align spectral_map.to_fun_eq_coe SpectralMap.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe {f : SpectralMap α β} : f.toFun = (f : α → β) :=
  rfl
#align spectral_map.to_fun_eq_coe SpectralMap.toFun_eq_coe

/- warning: spectral_map.ext -> SpectralMap.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : SpectralMap.{u1, u2} α β _inst_1 _inst_2} {g : SpectralMap.{u1, u2} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SpectralMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SpectralMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SpectralMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SpectralMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a)) -> (Eq.{max (succ u1) (succ u2)} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : SpectralMap.{u2, u1} α β _inst_1 _inst_2} {g : SpectralMap.{u2, u1} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (SpectralMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => β) _x) (SpectralMapClass.toFunLike.{max u2 u1, u2, u1} (SpectralMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SpectralMap.instSpectralMapClassSpectralMap.{u2, u1} α β _inst_1 _inst_2)) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (SpectralMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => β) _x) (SpectralMapClass.toFunLike.{max u2 u1, u2, u1} (SpectralMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SpectralMap.instSpectralMapClassSpectralMap.{u2, u1} α β _inst_1 _inst_2)) g a)) -> (Eq.{max (succ u2) (succ u1)} (SpectralMap.{u2, u1} α β _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align spectral_map.ext SpectralMap.extₓ'. -/
@[ext]
theorem ext {f g : SpectralMap α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align spectral_map.ext SpectralMap.ext

/- warning: spectral_map.copy -> SpectralMap.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : SpectralMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SpectralMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SpectralMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (SpectralMap.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : SpectralMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => β) _x) (SpectralMapClass.toFunLike.{max u1 u2, u1, u2} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SpectralMap.instSpectralMapClassSpectralMap.{u1, u2} α β _inst_1 _inst_2)) f)) -> (SpectralMap.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align spectral_map.copy SpectralMap.copyₓ'. -/
/-- Copy of a `spectral_map` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : SpectralMap α β) (f' : α → β) (h : f' = f) : SpectralMap α β :=
  ⟨f', h.symm.subst f.spectral'⟩
#align spectral_map.copy SpectralMap.copy

/- warning: spectral_map.coe_copy -> SpectralMap.coe_copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : SpectralMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SpectralMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SpectralMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SpectralMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SpectralMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (SpectralMap.copy.{u1, u2} α β _inst_1 _inst_2 f f' h)) f'
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : SpectralMap.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (SpectralMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => β) _x) (SpectralMapClass.toFunLike.{max u2 u1, u2, u1} (SpectralMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SpectralMap.instSpectralMapClassSpectralMap.{u2, u1} α β _inst_1 _inst_2)) f)), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (SpectralMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => β) _x) (SpectralMapClass.toFunLike.{max u2 u1, u2, u1} (SpectralMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SpectralMap.instSpectralMapClassSpectralMap.{u2, u1} α β _inst_1 _inst_2)) (SpectralMap.copy.{u2, u1} α β _inst_1 _inst_2 f f' h)) f'
Case conversion may be inaccurate. Consider using '#align spectral_map.coe_copy SpectralMap.coe_copyₓ'. -/
@[simp]
theorem coe_copy (f : SpectralMap α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align spectral_map.coe_copy SpectralMap.coe_copy

/- warning: spectral_map.copy_eq -> SpectralMap.copy_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : SpectralMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SpectralMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SpectralMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) (SpectralMap.copy.{u1, u2} α β _inst_1 _inst_2 f f' h) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : SpectralMap.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (SpectralMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => β) _x) (SpectralMapClass.toFunLike.{max u2 u1, u2, u1} (SpectralMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SpectralMap.instSpectralMapClassSpectralMap.{u2, u1} α β _inst_1 _inst_2)) f)), Eq.{max (succ u2) (succ u1)} (SpectralMap.{u2, u1} α β _inst_1 _inst_2) (SpectralMap.copy.{u2, u1} α β _inst_1 _inst_2 f f' h) f
Case conversion may be inaccurate. Consider using '#align spectral_map.copy_eq SpectralMap.copy_eqₓ'. -/
theorem copy_eq (f : SpectralMap α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align spectral_map.copy_eq SpectralMap.copy_eq

variable (α)

#print SpectralMap.id /-
/-- `id` as a `spectral_map`. -/
protected def id : SpectralMap α α :=
  ⟨id, isSpectralMap_id⟩
#align spectral_map.id SpectralMap.id
-/

instance : Inhabited (SpectralMap α α) :=
  ⟨SpectralMap.id α⟩

/- warning: spectral_map.coe_id -> SpectralMap.coe_id is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (α -> α) (coeFn.{succ u1, succ u1} (SpectralMap.{u1, u1} α α _inst_1 _inst_1) (fun (_x : SpectralMap.{u1, u1} α α _inst_1 _inst_1) => α -> α) (SpectralMap.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (SpectralMap.id.{u1} α _inst_1)) (id.{succ u1} α)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (SpectralMap.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => α) _x) (SpectralMapClass.toFunLike.{u1, u1, u1} (SpectralMap.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (SpectralMap.instSpectralMapClassSpectralMap.{u1, u1} α α _inst_1 _inst_1)) (SpectralMap.id.{u1} α _inst_1)) (id.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align spectral_map.coe_id SpectralMap.coe_idₓ'. -/
@[simp]
theorem coe_id : ⇑(SpectralMap.id α) = id :=
  rfl
#align spectral_map.coe_id SpectralMap.coe_id

variable {α}

/- warning: spectral_map.id_apply -> SpectralMap.id_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (SpectralMap.{u1, u1} α α _inst_1 _inst_1) (fun (_x : SpectralMap.{u1, u1} α α _inst_1 _inst_1) => α -> α) (SpectralMap.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (SpectralMap.id.{u1} α _inst_1) a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (SpectralMap.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => α) _x) (SpectralMapClass.toFunLike.{u1, u1, u1} (SpectralMap.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (SpectralMap.instSpectralMapClassSpectralMap.{u1, u1} α α _inst_1 _inst_1)) (SpectralMap.id.{u1} α _inst_1) a) a
Case conversion may be inaccurate. Consider using '#align spectral_map.id_apply SpectralMap.id_applyₓ'. -/
@[simp]
theorem id_apply (a : α) : SpectralMap.id α a = a :=
  rfl
#align spectral_map.id_apply SpectralMap.id_apply

#print SpectralMap.comp /-
/-- Composition of `spectral_map`s as a `spectral_map`. -/
def comp (f : SpectralMap β γ) (g : SpectralMap α β) : SpectralMap α γ :=
  ⟨f.toContinuousMap.comp g.toContinuousMap, f.spectral'.comp g.spectral'⟩
#align spectral_map.comp SpectralMap.comp
-/

/- warning: spectral_map.coe_comp -> SpectralMap.coe_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (f : SpectralMap.{u2, u3} β γ _inst_2 _inst_3) (g : SpectralMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} ((fun (_x : SpectralMap.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (SpectralMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g)) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (SpectralMap.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : SpectralMap.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (SpectralMap.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (SpectralMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SpectralMap.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : SpectralMap.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (SpectralMap.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SpectralMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SpectralMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (f : SpectralMap.{u3, u2} β γ _inst_2 _inst_3) (g : SpectralMap.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (forall (a : α), (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => γ) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (SpectralMap.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => γ) _x) (SpectralMapClass.toFunLike.{max u1 u2, u1, u2} (SpectralMap.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (SpectralMap.instSpectralMapClassSpectralMap.{u1, u2} α γ _inst_1 _inst_3)) (SpectralMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u3, succ u2} α β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (SpectralMap.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : β) => γ) _x) (SpectralMapClass.toFunLike.{max u3 u2, u3, u2} (SpectralMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (SpectralMap.instSpectralMapClassSpectralMap.{u3, u2} β γ _inst_2 _inst_3)) f) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (SpectralMap.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => β) _x) (SpectralMapClass.toFunLike.{max u1 u3, u1, u3} (SpectralMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SpectralMap.instSpectralMapClassSpectralMap.{u1, u3} α β _inst_1 _inst_2)) g))
Case conversion may be inaccurate. Consider using '#align spectral_map.coe_comp SpectralMap.coe_compₓ'. -/
@[simp]
theorem coe_comp (f : SpectralMap β γ) (g : SpectralMap α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
#align spectral_map.coe_comp SpectralMap.coe_comp

/- warning: spectral_map.comp_apply -> SpectralMap.comp_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (f : SpectralMap.{u2, u3} β γ _inst_2 _inst_3) (g : SpectralMap.{u1, u2} α β _inst_1 _inst_2) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (SpectralMap.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : SpectralMap.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (SpectralMap.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (SpectralMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SpectralMap.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : SpectralMap.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (SpectralMap.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SpectralMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SpectralMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (f : SpectralMap.{u3, u2} β γ _inst_2 _inst_3) (g : SpectralMap.{u1, u3} α β _inst_1 _inst_2) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => γ) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (SpectralMap.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => γ) _x) (SpectralMapClass.toFunLike.{max u1 u2, u1, u2} (SpectralMap.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (SpectralMap.instSpectralMapClassSpectralMap.{u1, u2} α γ _inst_1 _inst_3)) (SpectralMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g) a) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (SpectralMap.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : β) => γ) _x) (SpectralMapClass.toFunLike.{max u3 u2, u3, u2} (SpectralMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (SpectralMap.instSpectralMapClassSpectralMap.{u3, u2} β γ _inst_2 _inst_3)) f (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (SpectralMap.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => β) _x) (SpectralMapClass.toFunLike.{max u1 u3, u1, u3} (SpectralMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SpectralMap.instSpectralMapClassSpectralMap.{u1, u3} α β _inst_1 _inst_2)) g a))
Case conversion may be inaccurate. Consider using '#align spectral_map.comp_apply SpectralMap.comp_applyₓ'. -/
@[simp]
theorem comp_apply (f : SpectralMap β γ) (g : SpectralMap α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align spectral_map.comp_apply SpectralMap.comp_apply

/- warning: spectral_map.coe_comp_continuous_map -> SpectralMap.coe_comp_continuousMap' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (f : SpectralMap.{u2, u3} β γ _inst_2 _inst_3) (g : SpectralMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) ((fun (a : Sort.{max (succ u1) (succ u3)}) (b : Sort.{max (succ u1) (succ u3)}) [self : HasLiftT.{max (succ u1) (succ u3), max (succ u1) (succ u3)} a b] => self.0) (SpectralMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (HasLiftT.mk.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (SpectralMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (CoeTCₓ.coe.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (SpectralMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.hasCoeT.{max u1 u3, u1, u3} (SpectralMap.{u1, u3} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (SpectralMapClass.toContinuousMapClass.{max u1 u3, u1, u3} (SpectralMap.{u1, u3} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (SpectralMap.spectralMapClass.{u1, u3} α γ _inst_1 _inst_3))))) (SpectralMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g)) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 ((fun (a : Sort.{max (succ u2) (succ u3)}) (b : Sort.{max (succ u2) (succ u3)}) [self : HasLiftT.{max (succ u2) (succ u3), max (succ u2) (succ u3)} a b] => self.0) (SpectralMap.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (HasLiftT.mk.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SpectralMap.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (CoeTCₓ.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SpectralMap.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.hasCoeT.{max u2 u3, u2, u3} (SpectralMap.{u2, u3} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (SpectralMapClass.toContinuousMapClass.{max u2 u3, u2, u3} (SpectralMap.{u2, u3} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (SpectralMap.spectralMapClass.{u2, u3} β γ _inst_2 _inst_3))))) f) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (SpectralMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasCoeT.{max u1 u2, u1, u2} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SpectralMapClass.toContinuousMapClass.{max u1 u2, u1, u2} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SpectralMap.spectralMapClass.{u1, u2} α β _inst_1 _inst_2))))) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (f : SpectralMap.{u3, u2} β γ _inst_2 _inst_3) (g : SpectralMap.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α γ _inst_1 _inst_3) (ContinuousMap.mk.{u1, u2} α γ _inst_1 _inst_3 (FunLike.coe.{succ (max u1 u2), succ u1, succ u2} (SpectralMap.{u1, u2} α γ _inst_1 _inst_3) α (fun (a : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => γ) a) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (SpectralMap.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (SpectralMapClass.toContinuousMapClass.{max u1 u2, u1, u2} (SpectralMap.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (SpectralMap.instSpectralMapClassSpectralMap.{u1, u2} α γ _inst_1 _inst_3))) (SpectralMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g)) (ContinuousMapClass.map_continuous.{max u1 u2, u1, u2} (SpectralMap.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (SpectralMapClass.toContinuousMapClass.{max u1 u2, u1, u2} (SpectralMap.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (SpectralMap.instSpectralMapClassSpectralMap.{u1, u2} α γ _inst_1 _inst_3)) (SpectralMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g))) (ContinuousMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 (ContinuousMap.mk.{u3, u2} β γ _inst_2 _inst_3 (FunLike.coe.{succ (max u3 u2), succ u3, succ u2} (SpectralMap.{u3, u2} β γ _inst_2 _inst_3) β (fun (a : β) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : β) => γ) a) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (SpectralMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (SpectralMapClass.toContinuousMapClass.{max u3 u2, u3, u2} (SpectralMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (SpectralMap.instSpectralMapClassSpectralMap.{u3, u2} β γ _inst_2 _inst_3))) f) (ContinuousMapClass.map_continuous.{max u3 u2, u3, u2} (SpectralMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (SpectralMapClass.toContinuousMapClass.{max u3 u2, u3, u2} (SpectralMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (SpectralMap.instSpectralMapClassSpectralMap.{u3, u2} β γ _inst_2 _inst_3)) f)) (ContinuousMap.mk.{u1, u3} α β _inst_1 _inst_2 (FunLike.coe.{succ (max u1 u3), succ u1, succ u3} (SpectralMap.{u1, u3} α β _inst_1 _inst_2) α (fun (a : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) a) (ContinuousMapClass.toFunLike.{max u1 u3, u1, u3} (SpectralMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SpectralMapClass.toContinuousMapClass.{max u1 u3, u1, u3} (SpectralMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SpectralMap.instSpectralMapClassSpectralMap.{u1, u3} α β _inst_1 _inst_2))) g) (ContinuousMapClass.map_continuous.{max u1 u3, u1, u3} (SpectralMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SpectralMapClass.toContinuousMapClass.{max u1 u3, u1, u3} (SpectralMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SpectralMap.instSpectralMapClassSpectralMap.{u1, u3} α β _inst_1 _inst_2)) g)))
Case conversion may be inaccurate. Consider using '#align spectral_map.coe_comp_continuous_map SpectralMap.coe_comp_continuousMap'ₓ'. -/
@[simp]
theorem coe_comp_continuousMap' (f : SpectralMap β γ) (g : SpectralMap α β) :
    (f.comp g : ContinuousMap α γ) = (f : ContinuousMap β γ).comp g :=
  rfl
#align spectral_map.coe_comp_continuous_map SpectralMap.coe_comp_continuousMap'

/- warning: spectral_map.comp_assoc -> SpectralMap.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] (f : SpectralMap.{u3, u4} γ δ _inst_3 _inst_4) (g : SpectralMap.{u2, u3} β γ _inst_2 _inst_3) (h : SpectralMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u4)} (SpectralMap.{u1, u4} α δ _inst_1 _inst_4) (SpectralMap.comp.{u1, u2, u4} α β δ _inst_1 _inst_2 _inst_4 (SpectralMap.comp.{u2, u3, u4} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (SpectralMap.comp.{u1, u3, u4} α γ δ _inst_1 _inst_3 _inst_4 f (SpectralMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g h))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u4} γ] [_inst_4 : TopologicalSpace.{u3} δ] (f : SpectralMap.{u4, u3} γ δ _inst_3 _inst_4) (g : SpectralMap.{u2, u4} β γ _inst_2 _inst_3) (h : SpectralMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (SpectralMap.{u1, u3} α δ _inst_1 _inst_4) (SpectralMap.comp.{u1, u2, u3} α β δ _inst_1 _inst_2 _inst_4 (SpectralMap.comp.{u2, u4, u3} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (SpectralMap.comp.{u1, u4, u3} α γ δ _inst_1 _inst_3 _inst_4 f (SpectralMap.comp.{u1, u2, u4} α β γ _inst_1 _inst_2 _inst_3 g h))
Case conversion may be inaccurate. Consider using '#align spectral_map.comp_assoc SpectralMap.comp_assocₓ'. -/
@[simp]
theorem comp_assoc (f : SpectralMap γ δ) (g : SpectralMap β γ) (h : SpectralMap α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align spectral_map.comp_assoc SpectralMap.comp_assoc

/- warning: spectral_map.comp_id -> SpectralMap.comp_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : SpectralMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) (SpectralMap.comp.{u1, u1, u2} α α β _inst_1 _inst_1 _inst_2 f (SpectralMap.id.{u1} α _inst_1)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : SpectralMap.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (SpectralMap.{u2, u1} α β _inst_1 _inst_2) (SpectralMap.comp.{u2, u2, u1} α α β _inst_1 _inst_1 _inst_2 f (SpectralMap.id.{u2} α _inst_1)) f
Case conversion may be inaccurate. Consider using '#align spectral_map.comp_id SpectralMap.comp_idₓ'. -/
@[simp]
theorem comp_id (f : SpectralMap α β) : f.comp (SpectralMap.id α) = f :=
  ext fun a => rfl
#align spectral_map.comp_id SpectralMap.comp_id

/- warning: spectral_map.id_comp -> SpectralMap.id_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : SpectralMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) (SpectralMap.comp.{u1, u2, u2} α β β _inst_1 _inst_2 _inst_2 (SpectralMap.id.{u2} β _inst_2) f) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : SpectralMap.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (SpectralMap.{u2, u1} α β _inst_1 _inst_2) (SpectralMap.comp.{u2, u1, u1} α β β _inst_1 _inst_2 _inst_2 (SpectralMap.id.{u1} β _inst_2) f) f
Case conversion may be inaccurate. Consider using '#align spectral_map.id_comp SpectralMap.id_compₓ'. -/
@[simp]
theorem id_comp (f : SpectralMap α β) : (SpectralMap.id β).comp f = f :=
  ext fun a => rfl
#align spectral_map.id_comp SpectralMap.id_comp

/- warning: spectral_map.cancel_right -> SpectralMap.cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {g₁ : SpectralMap.{u2, u3} β γ _inst_2 _inst_3} {g₂ : SpectralMap.{u2, u3} β γ _inst_2 _inst_3} {f : SpectralMap.{u1, u2} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SpectralMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SpectralMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (Iff (Eq.{max (succ u1) (succ u3)} (SpectralMap.{u1, u3} α γ _inst_1 _inst_3) (SpectralMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (SpectralMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u2) (succ u3)} (SpectralMap.{u2, u3} β γ _inst_2 _inst_3) g₁ g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] {g₁ : SpectralMap.{u3, u2} β γ _inst_2 _inst_3} {g₂ : SpectralMap.{u3, u2} β γ _inst_2 _inst_3} {f : SpectralMap.{u1, u3} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u3} α β (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (SpectralMap.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : α) => β) _x) (SpectralMapClass.toFunLike.{max u1 u3, u1, u3} (SpectralMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SpectralMap.instSpectralMapClassSpectralMap.{u1, u3} α β _inst_1 _inst_2)) f)) -> (Iff (Eq.{max (succ u1) (succ u2)} (SpectralMap.{u1, u2} α γ _inst_1 _inst_3) (SpectralMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (SpectralMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u3) (succ u2)} (SpectralMap.{u3, u2} β γ _inst_2 _inst_3) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align spectral_map.cancel_right SpectralMap.cancel_rightₓ'. -/
theorem cancel_right {g₁ g₂ : SpectralMap β γ} {f : SpectralMap α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align spectral_map.cancel_right SpectralMap.cancel_right

/- warning: spectral_map.cancel_left -> SpectralMap.cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {g : SpectralMap.{u2, u3} β γ _inst_2 _inst_3} {f₁ : SpectralMap.{u1, u2} α β _inst_1 _inst_2} {f₂ : SpectralMap.{u1, u2} α β _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u3} β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SpectralMap.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : SpectralMap.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (SpectralMap.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) g)) -> (Iff (Eq.{max (succ u1) (succ u3)} (SpectralMap.{u1, u3} α γ _inst_1 _inst_3) (SpectralMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₁) (SpectralMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u2)} (SpectralMap.{u1, u2} α β _inst_1 _inst_2) f₁ f₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] {g : SpectralMap.{u3, u2} β γ _inst_2 _inst_3} {f₁ : SpectralMap.{u1, u3} α β _inst_1 _inst_2} {f₂ : SpectralMap.{u1, u3} α β _inst_1 _inst_2}, (Function.Injective.{succ u3, succ u2} β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (SpectralMap.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.Spectral.Hom._hyg.348 : β) => γ) _x) (SpectralMapClass.toFunLike.{max u3 u2, u3, u2} (SpectralMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (SpectralMap.instSpectralMapClassSpectralMap.{u3, u2} β γ _inst_2 _inst_3)) g)) -> (Iff (Eq.{max (succ u1) (succ u2)} (SpectralMap.{u1, u2} α γ _inst_1 _inst_3) (SpectralMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₁) (SpectralMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u3)} (SpectralMap.{u1, u3} α β _inst_1 _inst_2) f₁ f₂))
Case conversion may be inaccurate. Consider using '#align spectral_map.cancel_left SpectralMap.cancel_leftₓ'. -/
theorem cancel_left {g : SpectralMap β γ} {f₁ f₂ : SpectralMap α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align spectral_map.cancel_left SpectralMap.cancel_left

end SpectralMap

