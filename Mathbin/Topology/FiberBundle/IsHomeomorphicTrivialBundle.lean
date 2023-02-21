/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.fiber_bundle.is_homeomorphic_trivial_bundle
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Homeomorph

/-!
# Maps equivariantly-homeomorphic to projection in a product

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the definition `is_homeomorphic_trivial_fiber_bundle F p`, a Prop saying that a
map `p : Z → B` between topological spaces is a "trivial fiber bundle" in the sense that there
exists a homeomorphism `h : Z ≃ₜ B × F` such that `proj x = (h x).1`.  This is an abstraction which
is occasionally convenient in showing that a map is open, a quotient map, etc.

This material was formerly linked to the main definition of fibre bundles, but after a series of
refactors, there is no longer a direct connection.
-/


variable {B : Type _} (F : Type _) {Z : Type _} [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace Z]

#print IsHomeomorphicTrivialFiberBundle /-
/-- A trivial fiber bundle with fiber `F` over a base `B` is a space `Z`
projecting on `B` for which there exists a homeomorphism to `B × F` that sends `proj`
to `prod.fst`. -/
def IsHomeomorphicTrivialFiberBundle (proj : Z → B) : Prop :=
  ∃ e : Z ≃ₜ B × F, ∀ x, (e x).1 = proj x
#align is_homeomorphic_trivial_fiber_bundle IsHomeomorphicTrivialFiberBundle
-/

namespace IsHomeomorphicTrivialFiberBundle

variable {F} {proj : Z → B}

/- warning: is_homeomorphic_trivial_fiber_bundle.proj_eq -> IsHomeomorphicTrivialFiberBundle.proj_eq is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {F : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} B] [_inst_2 : TopologicalSpace.{u2} F] [_inst_3 : TopologicalSpace.{u3} Z] {proj : Z -> B}, (IsHomeomorphicTrivialFiberBundle.{u1, u2, u3} B F Z _inst_1 _inst_2 _inst_3 proj) -> (Exists.{max (succ u3) (succ (max u1 u2))} (Homeomorph.{u3, max u1 u2} Z (Prod.{u1, u2} B F) _inst_3 (Prod.topologicalSpace.{u1, u2} B F _inst_1 _inst_2)) (fun (e : Homeomorph.{u3, max u1 u2} Z (Prod.{u1, u2} B F) _inst_3 (Prod.topologicalSpace.{u1, u2} B F _inst_1 _inst_2)) => Eq.{max (succ u3) (succ u1)} (Z -> B) proj (Function.comp.{succ u3, max (succ u1) (succ u2), succ u1} Z (Prod.{u1, u2} B F) B (Prod.fst.{u1, u2} B F) (coeFn.{max (succ u3) (succ (max u1 u2)), max (succ u3) (succ (max u1 u2))} (Homeomorph.{u3, max u1 u2} Z (Prod.{u1, u2} B F) _inst_3 (Prod.topologicalSpace.{u1, u2} B F _inst_1 _inst_2)) (fun (_x : Homeomorph.{u3, max u1 u2} Z (Prod.{u1, u2} B F) _inst_3 (Prod.topologicalSpace.{u1, u2} B F _inst_1 _inst_2)) => Z -> (Prod.{u1, u2} B F)) (Homeomorph.hasCoeToFun.{u3, max u1 u2} Z (Prod.{u1, u2} B F) _inst_3 (Prod.topologicalSpace.{u1, u2} B F _inst_1 _inst_2)) e))))
but is expected to have type
  forall {B : Type.{u3}} {F : Type.{u2}} {Z : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} B] [_inst_2 : TopologicalSpace.{u2} F] [_inst_3 : TopologicalSpace.{u1} Z] {proj : Z -> B}, (IsHomeomorphicTrivialFiberBundle.{u3, u2, u1} B F Z _inst_1 _inst_2 _inst_3 proj) -> (Exists.{max (max (succ u3) (succ u2)) (succ u1)} (Homeomorph.{u1, max u2 u3} Z (Prod.{u3, u2} B F) _inst_3 (instTopologicalSpaceProd.{u3, u2} B F _inst_1 _inst_2)) (fun (e : Homeomorph.{u1, max u2 u3} Z (Prod.{u3, u2} B F) _inst_3 (instTopologicalSpaceProd.{u3, u2} B F _inst_1 _inst_2)) => Eq.{max (succ u3) (succ u1)} (Z -> B) proj (Function.comp.{succ u1, max (succ u2) (succ u3), succ u3} Z (Prod.{u3, u2} B F) B (Prod.fst.{u3, u2} B F) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u1, max (succ u3) (succ u2)} (Homeomorph.{u1, max u2 u3} Z (Prod.{u3, u2} B F) _inst_3 (instTopologicalSpaceProd.{u3, u2} B F _inst_1 _inst_2)) Z (fun (_x : Z) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Z) => Prod.{u3, u2} B F) _x) (EmbeddingLike.toFunLike.{max (max (succ u3) (succ u2)) (succ u1), succ u1, max (succ u3) (succ u2)} (Homeomorph.{u1, max u2 u3} Z (Prod.{u3, u2} B F) _inst_3 (instTopologicalSpaceProd.{u3, u2} B F _inst_1 _inst_2)) Z (Prod.{u3, u2} B F) (EquivLike.toEmbeddingLike.{max (max (succ u3) (succ u2)) (succ u1), succ u1, max (succ u3) (succ u2)} (Homeomorph.{u1, max u2 u3} Z (Prod.{u3, u2} B F) _inst_3 (instTopologicalSpaceProd.{u3, u2} B F _inst_1 _inst_2)) Z (Prod.{u3, u2} B F) (Homeomorph.instEquivLikeHomeomorph.{u1, max u3 u2} Z (Prod.{u3, u2} B F) _inst_3 (instTopologicalSpaceProd.{u3, u2} B F _inst_1 _inst_2)))) e))))
Case conversion may be inaccurate. Consider using '#align is_homeomorphic_trivial_fiber_bundle.proj_eq IsHomeomorphicTrivialFiberBundle.proj_eqₓ'. -/
protected theorem proj_eq (h : IsHomeomorphicTrivialFiberBundle F proj) :
    ∃ e : Z ≃ₜ B × F, proj = Prod.fst ∘ e :=
  ⟨h.some, (funext h.choose_spec).symm⟩
#align is_homeomorphic_trivial_fiber_bundle.proj_eq IsHomeomorphicTrivialFiberBundle.proj_eq

/- warning: is_homeomorphic_trivial_fiber_bundle.surjective_proj -> IsHomeomorphicTrivialFiberBundle.surjective_proj is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {F : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} B] [_inst_2 : TopologicalSpace.{u2} F] [_inst_3 : TopologicalSpace.{u3} Z] {proj : Z -> B} [_inst_4 : Nonempty.{succ u2} F], (IsHomeomorphicTrivialFiberBundle.{u1, u2, u3} B F Z _inst_1 _inst_2 _inst_3 proj) -> (Function.Surjective.{succ u3, succ u1} Z B proj)
but is expected to have type
  forall {B : Type.{u2}} {F : Type.{u3}} {Z : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} B] [_inst_2 : TopologicalSpace.{u3} F] [_inst_3 : TopologicalSpace.{u1} Z] {proj : Z -> B} [_inst_4 : Nonempty.{succ u3} F], (IsHomeomorphicTrivialFiberBundle.{u2, u3, u1} B F Z _inst_1 _inst_2 _inst_3 proj) -> (Function.Surjective.{succ u1, succ u2} Z B proj)
Case conversion may be inaccurate. Consider using '#align is_homeomorphic_trivial_fiber_bundle.surjective_proj IsHomeomorphicTrivialFiberBundle.surjective_projₓ'. -/
/-- The projection from a trivial fiber bundle to its base is surjective. -/
protected theorem surjective_proj [Nonempty F] (h : IsHomeomorphicTrivialFiberBundle F proj) :
    Function.Surjective proj := by
  obtain ⟨e, rfl⟩ := h.proj_eq
  exact prod.fst_surjective.comp e.surjective
#align is_homeomorphic_trivial_fiber_bundle.surjective_proj IsHomeomorphicTrivialFiberBundle.surjective_proj

/- warning: is_homeomorphic_trivial_fiber_bundle.continuous_proj -> IsHomeomorphicTrivialFiberBundle.continuous_proj is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {F : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} B] [_inst_2 : TopologicalSpace.{u2} F] [_inst_3 : TopologicalSpace.{u3} Z] {proj : Z -> B}, (IsHomeomorphicTrivialFiberBundle.{u1, u2, u3} B F Z _inst_1 _inst_2 _inst_3 proj) -> (Continuous.{u3, u1} Z B _inst_3 _inst_1 proj)
but is expected to have type
  forall {B : Type.{u3}} {F : Type.{u2}} {Z : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} B] [_inst_2 : TopologicalSpace.{u2} F] [_inst_3 : TopologicalSpace.{u1} Z] {proj : Z -> B}, (IsHomeomorphicTrivialFiberBundle.{u3, u2, u1} B F Z _inst_1 _inst_2 _inst_3 proj) -> (Continuous.{u1, u3} Z B _inst_3 _inst_1 proj)
Case conversion may be inaccurate. Consider using '#align is_homeomorphic_trivial_fiber_bundle.continuous_proj IsHomeomorphicTrivialFiberBundle.continuous_projₓ'. -/
/-- The projection from a trivial fiber bundle to its base is continuous. -/
protected theorem continuous_proj (h : IsHomeomorphicTrivialFiberBundle F proj) : Continuous proj :=
  by
  obtain ⟨e, rfl⟩ := h.proj_eq
  exact continuous_fst.comp e.continuous
#align is_homeomorphic_trivial_fiber_bundle.continuous_proj IsHomeomorphicTrivialFiberBundle.continuous_proj

/- warning: is_homeomorphic_trivial_fiber_bundle.is_open_map_proj -> IsHomeomorphicTrivialFiberBundle.isOpenMap_proj is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {F : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} B] [_inst_2 : TopologicalSpace.{u2} F] [_inst_3 : TopologicalSpace.{u3} Z] {proj : Z -> B}, (IsHomeomorphicTrivialFiberBundle.{u1, u2, u3} B F Z _inst_1 _inst_2 _inst_3 proj) -> (IsOpenMap.{u3, u1} Z B _inst_3 _inst_1 proj)
but is expected to have type
  forall {B : Type.{u3}} {F : Type.{u2}} {Z : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} B] [_inst_2 : TopologicalSpace.{u2} F] [_inst_3 : TopologicalSpace.{u1} Z] {proj : Z -> B}, (IsHomeomorphicTrivialFiberBundle.{u3, u2, u1} B F Z _inst_1 _inst_2 _inst_3 proj) -> (IsOpenMap.{u1, u3} Z B _inst_3 _inst_1 proj)
Case conversion may be inaccurate. Consider using '#align is_homeomorphic_trivial_fiber_bundle.is_open_map_proj IsHomeomorphicTrivialFiberBundle.isOpenMap_projₓ'. -/
/-- The projection from a trivial fiber bundle to its base is open. -/
protected theorem isOpenMap_proj (h : IsHomeomorphicTrivialFiberBundle F proj) : IsOpenMap proj :=
  by
  obtain ⟨e, rfl⟩ := h.proj_eq
  exact is_open_map_fst.comp e.is_open_map
#align is_homeomorphic_trivial_fiber_bundle.is_open_map_proj IsHomeomorphicTrivialFiberBundle.isOpenMap_proj

/- warning: is_homeomorphic_trivial_fiber_bundle.quotient_map_proj -> IsHomeomorphicTrivialFiberBundle.quotientMap_proj is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {F : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} B] [_inst_2 : TopologicalSpace.{u2} F] [_inst_3 : TopologicalSpace.{u3} Z] {proj : Z -> B} [_inst_4 : Nonempty.{succ u2} F], (IsHomeomorphicTrivialFiberBundle.{u1, u2, u3} B F Z _inst_1 _inst_2 _inst_3 proj) -> (QuotientMap.{u3, u1} Z B _inst_3 _inst_1 proj)
but is expected to have type
  forall {B : Type.{u2}} {F : Type.{u3}} {Z : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} B] [_inst_2 : TopologicalSpace.{u3} F] [_inst_3 : TopologicalSpace.{u1} Z] {proj : Z -> B} [_inst_4 : Nonempty.{succ u3} F], (IsHomeomorphicTrivialFiberBundle.{u2, u3, u1} B F Z _inst_1 _inst_2 _inst_3 proj) -> (QuotientMap.{u1, u2} Z B _inst_3 _inst_1 proj)
Case conversion may be inaccurate. Consider using '#align is_homeomorphic_trivial_fiber_bundle.quotient_map_proj IsHomeomorphicTrivialFiberBundle.quotientMap_projₓ'. -/
/-- The projection from a trivial fiber bundle to its base is open. -/
protected theorem quotientMap_proj [Nonempty F] (h : IsHomeomorphicTrivialFiberBundle F proj) :
    QuotientMap proj :=
  h.isOpenMap_proj.to_quotientMap h.continuous_proj h.surjective_proj
#align is_homeomorphic_trivial_fiber_bundle.quotient_map_proj IsHomeomorphicTrivialFiberBundle.quotientMap_proj

end IsHomeomorphicTrivialFiberBundle

/- warning: is_homeomorphic_trivial_fiber_bundle_fst -> isHomeomorphicTrivialFiberBundle_fst is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} (F : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} B] [_inst_2 : TopologicalSpace.{u2} F], IsHomeomorphicTrivialFiberBundle.{u1, u2, max u1 u2} B F (Prod.{u1, u2} B F) _inst_1 _inst_2 (Prod.topologicalSpace.{u1, u2} B F _inst_1 _inst_2) (Prod.fst.{u1, u2} B F)
but is expected to have type
  forall {B : Type.{u2}} (F : Type.{u1}) [_inst_1 : TopologicalSpace.{u2} B] [_inst_2 : TopologicalSpace.{u1} F], IsHomeomorphicTrivialFiberBundle.{u2, u1, max u2 u1} B F (Prod.{u2, u1} B F) _inst_1 _inst_2 (instTopologicalSpaceProd.{u2, u1} B F _inst_1 _inst_2) (Prod.fst.{u2, u1} B F)
Case conversion may be inaccurate. Consider using '#align is_homeomorphic_trivial_fiber_bundle_fst isHomeomorphicTrivialFiberBundle_fstₓ'. -/
/-- The first projection in a product is a trivial fiber bundle. -/
theorem isHomeomorphicTrivialFiberBundle_fst :
    IsHomeomorphicTrivialFiberBundle F (Prod.fst : B × F → B) :=
  ⟨Homeomorph.refl _, fun x => rfl⟩
#align is_homeomorphic_trivial_fiber_bundle_fst isHomeomorphicTrivialFiberBundle_fst

/- warning: is_homeomorphic_trivial_fiber_bundle_snd -> isHomeomorphicTrivialFiberBundle_snd is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} (F : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} B] [_inst_2 : TopologicalSpace.{u2} F], IsHomeomorphicTrivialFiberBundle.{u1, u2, max u2 u1} B F (Prod.{u2, u1} F B) _inst_1 _inst_2 (Prod.topologicalSpace.{u2, u1} F B _inst_2 _inst_1) (Prod.snd.{u2, u1} F B)
but is expected to have type
  forall {B : Type.{u2}} (F : Type.{u1}) [_inst_1 : TopologicalSpace.{u2} B] [_inst_2 : TopologicalSpace.{u1} F], IsHomeomorphicTrivialFiberBundle.{u2, u1, max u2 u1} B F (Prod.{u1, u2} F B) _inst_1 _inst_2 (instTopologicalSpaceProd.{u1, u2} F B _inst_2 _inst_1) (Prod.snd.{u1, u2} F B)
Case conversion may be inaccurate. Consider using '#align is_homeomorphic_trivial_fiber_bundle_snd isHomeomorphicTrivialFiberBundle_sndₓ'. -/
/-- The second projection in a product is a trivial fiber bundle. -/
theorem isHomeomorphicTrivialFiberBundle_snd :
    IsHomeomorphicTrivialFiberBundle F (Prod.snd : F × B → B) :=
  ⟨Homeomorph.prodComm _ _, fun x => rfl⟩
#align is_homeomorphic_trivial_fiber_bundle_snd isHomeomorphicTrivialFiberBundle_snd

