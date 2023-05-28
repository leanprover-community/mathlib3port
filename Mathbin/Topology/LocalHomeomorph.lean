/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.local_homeomorph
! leanprover-community/mathlib commit 23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Equiv.LocalEquiv
import Mathbin.Topology.Sets.Opens

/-!
# Local homeomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines homeomorphisms between open subsets of topological spaces. An element `e` of
`local_homeomorph α β` is an extension of `local_equiv α β`, i.e., it is a pair of functions
`e.to_fun` and `e.inv_fun`, inverse of each other on the sets `e.source` and `e.target`.
Additionally, we require that these sets are open, and that the functions are continuous on them.
Equivalently, they are homeomorphisms there.

As in equivs, we register a coercion to functions, and we use `e x` and `e.symm x` throughout
instead of `e.to_fun x` and `e.inv_fun x`.

## Main definitions

`homeomorph.to_local_homeomorph`: associating a local homeomorphism to a homeomorphism, with
                                  source = target = univ
`local_homeomorph.symm`  : the inverse of a local homeomorphism
`local_homeomorph.trans` : the composition of two local homeomorphisms
`local_homeomorph.refl`  : the identity local homeomorphism
`local_homeomorph.of_set`: the identity on a set `s`
`eq_on_source`           : equivalence relation describing the "right" notion of equality for local
                           homeomorphisms

## Implementation notes

Most statements are copied from their local_equiv versions, although some care is required
especially when restricting to subsets, as these should be open subsets.

For design notes, see `local_equiv.lean`.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `local_equiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.
-/


open Function Set Filter

open TopologicalSpace (SecondCountableTopology)

open Topology

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _} [TopologicalSpace α]
  [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

#print LocalHomeomorph /-
/-- local homeomorphisms, defined on open subsets of the space -/
@[nolint has_nonempty_instance]
structure LocalHomeomorph (α : Type _) (β : Type _) [TopologicalSpace α]
  [TopologicalSpace β] extends LocalEquiv α β where
  open_source : IsOpen source
  open_target : IsOpen target
  continuous_toFun : ContinuousOn to_fun source
  continuous_invFun : ContinuousOn inv_fun target
#align local_homeomorph LocalHomeomorph
-/

namespace LocalHomeomorph

variable (e : LocalHomeomorph α β) (e' : LocalHomeomorph β γ)

instance : CoeFun (LocalHomeomorph α β) fun _ => α → β :=
  ⟨fun e => e.toFun⟩

#print LocalHomeomorph.symm /-
/-- The inverse of a local homeomorphism -/
protected def symm : LocalHomeomorph β α :=
  { e.toLocalEquiv.symm with
    open_source := e.open_target
    open_target := e.open_source
    continuous_toFun := e.continuous_invFun
    continuous_invFun := e.continuous_toFun }
#align local_homeomorph.symm LocalHomeomorph.symm
-/

#print LocalHomeomorph.Simps.apply /-
/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (e : LocalHomeomorph α β) : α → β :=
  e
#align local_homeomorph.simps.apply LocalHomeomorph.Simps.apply
-/

#print LocalHomeomorph.Simps.symm_apply /-
/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : LocalHomeomorph α β) : β → α :=
  e.symm
#align local_homeomorph.simps.symm_apply LocalHomeomorph.Simps.symm_apply
-/

initialize_simps_projections LocalHomeomorph (to_local_equiv_to_fun → apply,
  to_local_equiv_inv_fun → symm_apply, toLocalEquiv_source → source, toLocalEquiv_target → target,
  -toLocalEquiv)

/- warning: local_homeomorph.continuous_on -> LocalHomeomorph.continuousOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), ContinuousOn.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), ContinuousOn.{u2, u1} α β _inst_1 _inst_2 (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.continuous_on LocalHomeomorph.continuousOnₓ'. -/
protected theorem continuousOn : ContinuousOn e e.source :=
  e.continuous_toFun
#align local_homeomorph.continuous_on LocalHomeomorph.continuousOn

#print LocalHomeomorph.continuousOn_symm /-
theorem continuousOn_symm : ContinuousOn e.symm e.target :=
  e.continuous_invFun
#align local_homeomorph.continuous_on_symm LocalHomeomorph.continuousOn_symm
-/

/- warning: local_homeomorph.mk_coe -> LocalHomeomorph.mk_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalEquiv.{u1, u2} α β) (a : IsOpen.{u1} α _inst_1 (LocalEquiv.source.{u1, u2} α β e)) (b : IsOpen.{u2} β _inst_2 (LocalEquiv.target.{u1, u2} α β e)) (c : ContinuousOn.{u1, u2} α β _inst_1 _inst_2 (LocalEquiv.toFun.{u1, u2} α β e) (LocalEquiv.source.{u1, u2} α β e)) (d : ContinuousOn.{u2, u1} β α _inst_2 _inst_1 (LocalEquiv.invFun.{u1, u2} α β e) (LocalEquiv.target.{u1, u2} α β e)), Eq.{max (succ u1) (succ u2)} ((fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.mk.{u1, u2} α β _inst_1 _inst_2 e a b c d)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.mk.{u1, u2} α β _inst_1 _inst_2 e a b c d)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalEquiv.{u2, u1} α β) (a : IsOpen.{u2} α _inst_1 (LocalEquiv.source.{u2, u1} α β e)) (b : IsOpen.{u1} β _inst_2 (LocalEquiv.target.{u2, u1} α β e)) (c : ContinuousOn.{u2, u1} α β _inst_1 _inst_2 (LocalEquiv.toFun.{u2, u1} α β e) (LocalEquiv.source.{u2, u1} α β e)) (d : ContinuousOn.{u1, u2} β α _inst_2 _inst_1 (LocalEquiv.invFun.{u2, u1} α β e) (LocalEquiv.target.{u2, u1} α β e)), Eq.{max (succ u2) (succ u1)} (α -> β) (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 (LocalHomeomorph.mk.{u2, u1} α β _inst_1 _inst_2 e a b c d)) (LocalEquiv.toFun.{u2, u1} α β e)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.mk_coe LocalHomeomorph.mk_coeₓ'. -/
@[simp, mfld_simps]
theorem mk_coe (e : LocalEquiv α β) (a b c d) : (LocalHomeomorph.mk e a b c d : α → β) = e :=
  rfl
#align local_homeomorph.mk_coe LocalHomeomorph.mk_coe

/- warning: local_homeomorph.mk_coe_symm -> LocalHomeomorph.mk_coe_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalEquiv.{u1, u2} α β) (a : IsOpen.{u1} α _inst_1 (LocalEquiv.source.{u1, u2} α β e)) (b : IsOpen.{u2} β _inst_2 (LocalEquiv.target.{u1, u2} α β e)) (c : ContinuousOn.{u1, u2} α β _inst_1 _inst_2 (LocalEquiv.toFun.{u1, u2} α β e) (LocalEquiv.source.{u1, u2} α β e)) (d : ContinuousOn.{u2, u1} β α _inst_2 _inst_1 (LocalEquiv.invFun.{u1, u2} α β e) (LocalEquiv.target.{u1, u2} α β e)), Eq.{max (succ u2) (succ u1)} ((fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 (LocalHomeomorph.mk.{u1, u2} α β _inst_1 _inst_2 e a b c d))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 (LocalHomeomorph.mk.{u1, u2} α β _inst_1 _inst_2 e a b c d))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalEquiv.{u2, u1} α β) (a : IsOpen.{u2} α _inst_1 (LocalEquiv.source.{u2, u1} α β e)) (b : IsOpen.{u1} β _inst_2 (LocalEquiv.target.{u2, u1} α β e)) (c : ContinuousOn.{u2, u1} α β _inst_1 _inst_2 (LocalEquiv.toFun.{u2, u1} α β e) (LocalEquiv.source.{u2, u1} α β e)) (d : ContinuousOn.{u1, u2} β α _inst_2 _inst_1 (LocalEquiv.invFun.{u2, u1} α β e) (LocalEquiv.target.{u2, u1} α β e)), Eq.{max (succ u2) (succ u1)} (β -> α) (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 (LocalHomeomorph.mk.{u2, u1} α β _inst_1 _inst_2 e a b c d))) (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.mk_coe_symm LocalHomeomorph.mk_coe_symmₓ'. -/
@[simp, mfld_simps]
theorem mk_coe_symm (e : LocalEquiv α β) (a b c d) :
    ((LocalHomeomorph.mk e a b c d).symm : β → α) = e.symm :=
  rfl
#align local_homeomorph.mk_coe_symm LocalHomeomorph.mk_coe_symm

/- warning: local_homeomorph.to_local_equiv_injective -> LocalHomeomorph.toLocalEquiv_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Function.Injective.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalEquiv.{u1, u2} α β) (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β], Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalEquiv.{u2, u1} α β) (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.to_local_equiv_injective LocalHomeomorph.toLocalEquiv_injectiveₓ'. -/
theorem toLocalEquiv_injective : Injective (toLocalEquiv : LocalHomeomorph α β → LocalEquiv α β)
  | ⟨e, h₁, h₂, h₃, h₄⟩, ⟨e', h₁', h₂', h₃', h₄'⟩, rfl => rfl
#align local_homeomorph.to_local_equiv_injective LocalHomeomorph.toLocalEquiv_injective

/- warning: local_homeomorph.to_fun_eq_coe -> LocalHomeomorph.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (α -> β) (LocalEquiv.toFun.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (α -> β) (LocalEquiv.toFun.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.to_fun_eq_coe LocalHomeomorph.toFun_eq_coeₓ'. -/
/- Register a few simp lemmas to make sure that `simp` puts the application of a local
homeomorphism in its normal form, i.e., in terms of its coercion to a function. -/
@[simp, mfld_simps]
theorem toFun_eq_coe (e : LocalHomeomorph α β) : e.toFun = e :=
  rfl
#align local_homeomorph.to_fun_eq_coe LocalHomeomorph.toFun_eq_coe

/- warning: local_homeomorph.inv_fun_eq_coe -> LocalHomeomorph.invFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (β -> α) (LocalEquiv.invFun.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (β -> α) (LocalEquiv.invFun.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.inv_fun_eq_coe LocalHomeomorph.invFun_eq_coeₓ'. -/
@[simp, mfld_simps]
theorem invFun_eq_coe (e : LocalHomeomorph α β) : e.invFun = e.symm :=
  rfl
#align local_homeomorph.inv_fun_eq_coe LocalHomeomorph.invFun_eq_coe

/- warning: local_homeomorph.coe_coe -> LocalHomeomorph.coe_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} ((fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (α -> β) (LocalEquiv.toFun.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.coe_coe LocalHomeomorph.coe_coeₓ'. -/
@[simp, mfld_simps]
theorem coe_coe : (e.toLocalEquiv : α → β) = e :=
  rfl
#align local_homeomorph.coe_coe LocalHomeomorph.coe_coe

/- warning: local_homeomorph.coe_coe_symm -> LocalHomeomorph.coe_coe_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} ((fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.symm.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (β -> α) (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.coe_coe_symm LocalHomeomorph.coe_coe_symmₓ'. -/
@[simp, mfld_simps]
theorem coe_coe_symm : (e.toLocalEquiv.symm : β → α) = e.symm :=
  rfl
#align local_homeomorph.coe_coe_symm LocalHomeomorph.coe_coe_symm

/- warning: local_homeomorph.map_source -> LocalHomeomorph.map_source is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.map_source LocalHomeomorph.map_sourceₓ'. -/
@[simp, mfld_simps]
theorem map_source {x : α} (h : x ∈ e.source) : e x ∈ e.target :=
  e.map_source' h
#align local_homeomorph.map_source LocalHomeomorph.map_source

#print LocalHomeomorph.map_target /-
@[simp, mfld_simps]
theorem map_target {x : β} (h : x ∈ e.target) : e.symm x ∈ e.source :=
  e.map_target' h
#align local_homeomorph.map_target LocalHomeomorph.map_target
-/

/- warning: local_homeomorph.left_inv -> LocalHomeomorph.left_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Eq.{succ u1} α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x)) x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Eq.{succ u2} α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e) (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x)) x)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.left_inv LocalHomeomorph.left_invₓ'. -/
@[simp, mfld_simps]
theorem left_inv {x : α} (h : x ∈ e.source) : e.symm (e x) = x :=
  e.left_inv' h
#align local_homeomorph.left_inv LocalHomeomorph.left_inv

#print LocalHomeomorph.right_inv /-
@[simp, mfld_simps]
theorem right_inv {x : β} (h : x ∈ e.target) : e (e.symm x) = x :=
  e.right_inv' h
#align local_homeomorph.right_inv LocalHomeomorph.right_inv
-/

/- warning: local_homeomorph.eq_symm_apply -> LocalHomeomorph.eq_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : α} {y : β}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Iff (Eq.{succ u1} α x (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) y)) (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x) y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : α} {y : β}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Iff (Eq.{succ u2} α x (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e) y)) (Eq.{succ u1} β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x) y))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eq_symm_apply LocalHomeomorph.eq_symm_applyₓ'. -/
theorem eq_symm_apply {x : α} {y : β} (hx : x ∈ e.source) (hy : y ∈ e.target) :
    x = e.symm y ↔ e x = y :=
  e.toLocalEquiv.eq_symm_apply hx hy
#align local_homeomorph.eq_symm_apply LocalHomeomorph.eq_symm_apply

/- warning: local_homeomorph.maps_to -> LocalHomeomorph.mapsTo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), Set.MapsTo.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), Set.MapsTo.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.maps_to LocalHomeomorph.mapsToₓ'. -/
protected theorem mapsTo : MapsTo e e.source e.target := fun x => e.map_source
#align local_homeomorph.maps_to LocalHomeomorph.mapsTo

#print LocalHomeomorph.symm_mapsTo /-
protected theorem symm_mapsTo : MapsTo e.symm e.target e.source :=
  e.symm.MapsTo
#align local_homeomorph.symm_maps_to LocalHomeomorph.symm_mapsTo
-/

/- warning: local_homeomorph.left_inv_on -> LocalHomeomorph.leftInvOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), Set.LeftInvOn.{u1, u2} α β (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), Set.LeftInvOn.{u2, u1} α β (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.left_inv_on LocalHomeomorph.leftInvOnₓ'. -/
protected theorem leftInvOn : LeftInvOn e.symm e e.source := fun x => e.left_inv
#align local_homeomorph.left_inv_on LocalHomeomorph.leftInvOn

/- warning: local_homeomorph.right_inv_on -> LocalHomeomorph.rightInvOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), Set.RightInvOn.{u1, u2} α β (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), Set.RightInvOn.{u2, u1} α β (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.right_inv_on LocalHomeomorph.rightInvOnₓ'. -/
protected theorem rightInvOn : RightInvOn e.symm e e.target := fun x => e.right_inv
#align local_homeomorph.right_inv_on LocalHomeomorph.rightInvOn

/- warning: local_homeomorph.inv_on -> LocalHomeomorph.invOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), Set.InvOn.{u1, u2} α β (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), Set.InvOn.{u2, u1} α β (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.inv_on LocalHomeomorph.invOnₓ'. -/
protected theorem invOn : InvOn e.symm e e.source e.target :=
  ⟨e.LeftInvOn, e.RightInvOn⟩
#align local_homeomorph.inv_on LocalHomeomorph.invOn

/- warning: local_homeomorph.inj_on -> LocalHomeomorph.injOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), Set.InjOn.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), Set.InjOn.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.inj_on LocalHomeomorph.injOnₓ'. -/
protected theorem injOn : InjOn e e.source :=
  e.LeftInvOn.InjOn
#align local_homeomorph.inj_on LocalHomeomorph.injOn

/- warning: local_homeomorph.bij_on -> LocalHomeomorph.bijOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), Set.BijOn.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), Set.BijOn.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.bij_on LocalHomeomorph.bijOnₓ'. -/
protected theorem bijOn : BijOn e e.source e.target :=
  e.InvOn.BijOn e.MapsTo e.symm_mapsTo
#align local_homeomorph.bij_on LocalHomeomorph.bijOn

/- warning: local_homeomorph.surj_on -> LocalHomeomorph.surjOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), Set.SurjOn.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), Set.SurjOn.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.surj_on LocalHomeomorph.surjOnₓ'. -/
protected theorem surjOn : SurjOn e e.source e.target :=
  e.BijOn.SurjOn
#align local_homeomorph.surj_on LocalHomeomorph.surjOn

#print Homeomorph.toLocalHomeomorph /-
/-- A homeomorphism induces a local homeomorphism on the whole space -/
@[simps (config := { mfld_cfg with simpRhs := true })]
def Homeomorph.toLocalHomeomorph (e : α ≃ₜ β) : LocalHomeomorph α β :=
  { e.toEquiv.toLocalEquiv with
    open_source := isOpen_univ
    open_target := isOpen_univ
    continuous_toFun := by erw [← continuous_iff_continuousOn_univ]; exact e.continuous_to_fun
    continuous_invFun := by erw [← continuous_iff_continuousOn_univ]; exact e.continuous_inv_fun }
#align homeomorph.to_local_homeomorph Homeomorph.toLocalHomeomorph
-/

#print LocalHomeomorph.replaceEquiv /-
/-- Replace `to_local_equiv` field to provide better definitional equalities. -/
def replaceEquiv (e : LocalHomeomorph α β) (e' : LocalEquiv α β) (h : e.toLocalEquiv = e') :
    LocalHomeomorph α β where
  toLocalEquiv := e'
  open_source := h ▸ e.open_source
  open_target := h ▸ e.open_target
  continuous_toFun := h ▸ e.continuous_toFun
  continuous_invFun := h ▸ e.continuous_invFun
#align local_homeomorph.replace_equiv LocalHomeomorph.replaceEquiv
-/

/- warning: local_homeomorph.replace_equiv_eq_self -> LocalHomeomorph.replaceEquiv_eq_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalEquiv.{u1, u2} α β) (h : Eq.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e) e'), Eq.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.replaceEquiv.{u1, u2} α β _inst_1 _inst_2 e e' h) e
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (e' : LocalEquiv.{u2, u1} α β) (h : Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e) e'), Eq.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalHomeomorph.replaceEquiv.{u2, u1} α β _inst_1 _inst_2 e e' h) e
Case conversion may be inaccurate. Consider using '#align local_homeomorph.replace_equiv_eq_self LocalHomeomorph.replaceEquiv_eq_selfₓ'. -/
theorem replaceEquiv_eq_self (e : LocalHomeomorph α β) (e' : LocalEquiv α β)
    (h : e.toLocalEquiv = e') : e.replaceEquiv e' h = e := by cases e; subst e'; rfl
#align local_homeomorph.replace_equiv_eq_self LocalHomeomorph.replaceEquiv_eq_self

/- warning: local_homeomorph.source_preimage_target -> LocalHomeomorph.source_preimage_target is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.source_preimage_target LocalHomeomorph.source_preimage_targetₓ'. -/
theorem source_preimage_target : e.source ⊆ e ⁻¹' e.target :=
  e.MapsTo
#align local_homeomorph.source_preimage_target LocalHomeomorph.source_preimage_target

/- warning: local_homeomorph.eq_of_local_equiv_eq -> LocalHomeomorph.eq_of_localEquiv_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2}, (Eq.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e) (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e')) -> (Eq.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) e e')
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2}, (Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e) (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e')) -> (Eq.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) e e')
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eq_of_local_equiv_eq LocalHomeomorph.eq_of_localEquiv_eqₓ'. -/
theorem eq_of_localEquiv_eq {e e' : LocalHomeomorph α β} (h : e.toLocalEquiv = e'.toLocalEquiv) :
    e = e' := by cases e; cases e'; cases h; rfl
#align local_homeomorph.eq_of_local_equiv_eq LocalHomeomorph.eq_of_localEquiv_eq

/- warning: local_homeomorph.eventually_left_inverse -> LocalHomeomorph.eventually_left_inverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Filter.Eventually.{u1} α (fun (y : α) => Eq.{succ u1} α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e y)) y) (nhds.{u1} α _inst_1 x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Filter.Eventually.{u2} α (fun (y : α) => Eq.{succ u2} α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e) (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e y)) y) (nhds.{u2} α _inst_1 x))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eventually_left_inverse LocalHomeomorph.eventually_left_inverseₓ'. -/
theorem eventually_left_inverse (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) :
    ∀ᶠ y in 𝓝 x, e.symm (e y) = y :=
  (e.open_source.eventually_mem hx).mono e.left_inv'
#align local_homeomorph.eventually_left_inverse LocalHomeomorph.eventually_left_inverse

/- warning: local_homeomorph.eventually_left_inverse' -> LocalHomeomorph.eventually_left_inverse' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : β}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Filter.Eventually.{u1} α (fun (y : α) => Eq.{succ u1} α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e y)) y) (nhds.{u1} α _inst_1 (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : β}, (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Filter.Eventually.{u2} α (fun (y : α) => Eq.{succ u2} α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e) (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e y)) y) (nhds.{u2} α _inst_1 (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e) x)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eventually_left_inverse' LocalHomeomorph.eventually_left_inverse'ₓ'. -/
theorem eventually_left_inverse' (e : LocalHomeomorph α β) {x} (hx : x ∈ e.target) :
    ∀ᶠ y in 𝓝 (e.symm x), e.symm (e y) = y :=
  e.eventually_left_inverse (e.map_target hx)
#align local_homeomorph.eventually_left_inverse' LocalHomeomorph.eventually_left_inverse'

/- warning: local_homeomorph.eventually_right_inverse -> LocalHomeomorph.eventually_right_inverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : β}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Filter.Eventually.{u2} β (fun (y : β) => Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) y)) y) (nhds.{u2} β _inst_2 x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : β}, (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Filter.Eventually.{u1} β (fun (y : β) => Eq.{succ u1} β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e) y)) y) (nhds.{u1} β _inst_2 x))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eventually_right_inverse LocalHomeomorph.eventually_right_inverseₓ'. -/
theorem eventually_right_inverse (e : LocalHomeomorph α β) {x} (hx : x ∈ e.target) :
    ∀ᶠ y in 𝓝 x, e (e.symm y) = y :=
  (e.open_target.eventually_mem hx).mono e.right_inv'
#align local_homeomorph.eventually_right_inverse LocalHomeomorph.eventually_right_inverse

/- warning: local_homeomorph.eventually_right_inverse' -> LocalHomeomorph.eventually_right_inverse' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Filter.Eventually.{u2} β (fun (y : β) => Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) y)) y) (nhds.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Filter.Eventually.{u1} β (fun (y : β) => Eq.{succ u1} β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e) y)) y) (nhds.{u1} β _inst_2 (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eventually_right_inverse' LocalHomeomorph.eventually_right_inverse'ₓ'. -/
theorem eventually_right_inverse' (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) :
    ∀ᶠ y in 𝓝 (e x), e (e.symm y) = y :=
  e.eventually_right_inverse (e.map_source hx)
#align local_homeomorph.eventually_right_inverse' LocalHomeomorph.eventually_right_inverse'

/- warning: local_homeomorph.eventually_ne_nhds_within -> LocalHomeomorph.eventually_ne_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Filter.Eventually.{u1} α (fun (x' : α) => Ne.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x') (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x)) (nhdsWithin.{u1} α _inst_1 x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Filter.Eventually.{u2} α (fun (x' : α) => Ne.{succ u1} β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x') (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x)) (nhdsWithin.{u2} α _inst_1 x (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) x))))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eventually_ne_nhds_within LocalHomeomorph.eventually_ne_nhdsWithinₓ'. -/
theorem eventually_ne_nhdsWithin (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) :
    ∀ᶠ x' in 𝓝[≠] x, e x' ≠ e x :=
  eventually_nhdsWithin_iff.2 <|
    (e.eventually_left_inverse hx).mono fun x' hx' =>
      mt fun h => by rw [mem_singleton_iff, ← e.left_inv hx, ← h, hx']
#align local_homeomorph.eventually_ne_nhds_within LocalHomeomorph.eventually_ne_nhdsWithin

/- warning: local_homeomorph.nhds_within_source_inter -> LocalHomeomorph.nhdsWithin_source_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (forall (s : Set.{u1} α), Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 x (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)) (nhdsWithin.{u1} α _inst_1 x s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (forall (s : Set.{u2} α), Eq.{succ u2} (Filter.{u2} α) (nhdsWithin.{u2} α _inst_1 x (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s)) (nhdsWithin.{u2} α _inst_1 x s))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.nhds_within_source_inter LocalHomeomorph.nhdsWithin_source_interₓ'. -/
theorem nhdsWithin_source_inter {x} (hx : x ∈ e.source) (s : Set α) : 𝓝[e.source ∩ s] x = 𝓝[s] x :=
  nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds e.open_source hx)
#align local_homeomorph.nhds_within_source_inter LocalHomeomorph.nhdsWithin_source_inter

/- warning: local_homeomorph.nhds_within_target_inter -> LocalHomeomorph.nhdsWithin_target_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : β}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (forall (s : Set.{u2} β), Eq.{succ u2} (Filter.{u2} β) (nhdsWithin.{u2} β _inst_2 x (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)) (nhdsWithin.{u2} β _inst_2 x s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : β}, (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (forall (s : Set.{u2} β), Eq.{succ u2} (Filter.{u2} β) (nhdsWithin.{u2} β _inst_2 x (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)) (nhdsWithin.{u2} β _inst_2 x s))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.nhds_within_target_inter LocalHomeomorph.nhdsWithin_target_interₓ'. -/
theorem nhdsWithin_target_inter {x} (hx : x ∈ e.target) (s : Set β) : 𝓝[e.target ∩ s] x = 𝓝[s] x :=
  e.symm.nhdsWithin_source_inter hx s
#align local_homeomorph.nhds_within_target_inter LocalHomeomorph.nhdsWithin_target_inter

/- warning: local_homeomorph.image_eq_target_inter_inv_preimage -> LocalHomeomorph.image_eq_target_inter_inv_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {s : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {s : Set.{u2} α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) s) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) s)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.image_eq_target_inter_inv_preimage LocalHomeomorph.image_eq_target_inter_inv_preimageₓ'. -/
theorem image_eq_target_inter_inv_preimage {s : Set α} (h : s ⊆ e.source) :
    e '' s = e.target ∩ e.symm ⁻¹' s :=
  e.toLocalEquiv.image_eq_target_inter_inv_preimage h
#align local_homeomorph.image_eq_target_inter_inv_preimage LocalHomeomorph.image_eq_target_inter_inv_preimage

/- warning: local_homeomorph.image_source_inter_eq' -> LocalHomeomorph.image_source_inter_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) s))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.image_source_inter_eq' LocalHomeomorph.image_source_inter_eq'ₓ'. -/
theorem image_source_inter_eq' (s : Set α) : e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' s :=
  e.toLocalEquiv.image_source_inter_eq' s
#align local_homeomorph.image_source_inter_eq' LocalHomeomorph.image_source_inter_eq'

/- warning: local_homeomorph.image_source_inter_eq -> LocalHomeomorph.image_source_inter_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.image_source_inter_eq LocalHomeomorph.image_source_inter_eqₓ'. -/
theorem image_source_inter_eq (s : Set α) :
    e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' (e.source ∩ s) :=
  e.toLocalEquiv.image_source_inter_eq s
#align local_homeomorph.image_source_inter_eq LocalHomeomorph.image_source_inter_eq

/- warning: local_homeomorph.symm_image_eq_source_inter_preimage -> LocalHomeomorph.symm_image_eq_source_inter_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {s : Set.{u2} β}, (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) s (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {s : Set.{u2} β}, (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) s (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α (LocalHomeomorph.toFun'.{u2, u1} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) s) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (LocalHomeomorph.toFun'.{u1, u2} α β _inst_1 _inst_2 e) s)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.symm_image_eq_source_inter_preimage LocalHomeomorph.symm_image_eq_source_inter_preimageₓ'. -/
theorem symm_image_eq_source_inter_preimage {s : Set β} (h : s ⊆ e.target) :
    e.symm '' s = e.source ∩ e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h
#align local_homeomorph.symm_image_eq_source_inter_preimage LocalHomeomorph.symm_image_eq_source_inter_preimage

/- warning: local_homeomorph.symm_image_target_inter_eq -> LocalHomeomorph.symm_image_target_inter_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α (LocalHomeomorph.toFun'.{u2, u1} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (LocalHomeomorph.toFun'.{u1, u2} α β _inst_1 _inst_2 e) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.symm_image_target_inter_eq LocalHomeomorph.symm_image_target_inter_eqₓ'. -/
theorem symm_image_target_inter_eq (s : Set β) :
    e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' (e.target ∩ s) :=
  e.symm.image_source_inter_eq _
#align local_homeomorph.symm_image_target_inter_eq LocalHomeomorph.symm_image_target_inter_eq

/- warning: local_homeomorph.source_inter_preimage_inv_preimage -> LocalHomeomorph.source_inter_preimage_inv_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) s))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (Set.preimage.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) s))) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.source_inter_preimage_inv_preimage LocalHomeomorph.source_inter_preimage_inv_preimageₓ'. -/
theorem source_inter_preimage_inv_preimage (s : Set α) :
    e.source ∩ e ⁻¹' (e.symm ⁻¹' s) = e.source ∩ s :=
  e.toLocalEquiv.source_inter_preimage_inv_preimage s
#align local_homeomorph.source_inter_preimage_inv_preimage LocalHomeomorph.source_inter_preimage_inv_preimage

/- warning: local_homeomorph.target_inter_inv_preimage_preimage -> LocalHomeomorph.target_inter_inv_preimage_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s))) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} β α (LocalHomeomorph.toFun'.{u2, u1} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (LocalHomeomorph.toFun'.{u1, u2} α β _inst_1 _inst_2 e) s))) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.target_inter_inv_preimage_preimage LocalHomeomorph.target_inter_inv_preimage_preimageₓ'. -/
theorem target_inter_inv_preimage_preimage (s : Set β) :
    e.target ∩ e.symm ⁻¹' (e ⁻¹' s) = e.target ∩ s :=
  e.symm.source_inter_preimage_inv_preimage _
#align local_homeomorph.target_inter_inv_preimage_preimage LocalHomeomorph.target_inter_inv_preimage_preimage

/- warning: local_homeomorph.source_inter_preimage_target_inter -> LocalHomeomorph.source_inter_preimage_target_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (LocalHomeomorph.toFun'.{u1, u2} α β _inst_1 _inst_2 e) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (LocalHomeomorph.toFun'.{u1, u2} α β _inst_1 _inst_2 e) s))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.source_inter_preimage_target_inter LocalHomeomorph.source_inter_preimage_target_interₓ'. -/
theorem source_inter_preimage_target_inter (s : Set β) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.toLocalEquiv.source_inter_preimage_target_inter s
#align local_homeomorph.source_inter_preimage_target_inter LocalHomeomorph.source_inter_preimage_target_inter

/- warning: local_homeomorph.image_source_eq_target -> LocalHomeomorph.image_source_eq_target is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.image_source_eq_target LocalHomeomorph.image_source_eq_targetₓ'. -/
theorem image_source_eq_target (e : LocalHomeomorph α β) : e '' e.source = e.target :=
  e.toLocalEquiv.image_source_eq_target
#align local_homeomorph.image_source_eq_target LocalHomeomorph.image_source_eq_target

/- warning: local_homeomorph.symm_image_target_eq_source -> LocalHomeomorph.symm_image_target_eq_source is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u2} (Set.{u2} α) (Set.image.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.symm_image_target_eq_source LocalHomeomorph.symm_image_target_eq_sourceₓ'. -/
theorem symm_image_target_eq_source (e : LocalHomeomorph α β) : e.symm '' e.target = e.source :=
  e.symm.image_source_eq_target
#align local_homeomorph.symm_image_target_eq_source LocalHomeomorph.symm_image_target_eq_source

/- warning: local_homeomorph.ext -> LocalHomeomorph.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), (forall (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e' x)) -> (forall (x : β), Eq.{succ u1} α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) x) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e') x)) -> (Eq.{succ u1} (Set.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e'))) -> (Eq.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) e e')
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), (forall (x : α), Eq.{succ u1} β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x) (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e' x)) -> (forall (x : β), Eq.{succ u2} α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e) x) (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e') x)) -> (Eq.{succ u2} (Set.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e'))) -> (Eq.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) e e')
Case conversion may be inaccurate. Consider using '#align local_homeomorph.ext LocalHomeomorph.extₓ'. -/
/-- Two local homeomorphisms are equal when they have equal `to_fun`, `inv_fun` and `source`.
It is not sufficient to have equal `to_fun` and `source`, as this only determines `inv_fun` on
the target. This would only be true for a weaker notion of equality, arguably the right one,
called `eq_on_source`. -/
@[ext]
protected theorem ext (e' : LocalHomeomorph α β) (h : ∀ x, e x = e' x)
    (hinv : ∀ x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' :=
  eq_of_localEquiv_eq (LocalEquiv.ext h hinv hs)
#align local_homeomorph.ext LocalHomeomorph.ext

/- warning: local_homeomorph.ext_iff -> LocalHomeomorph.ext_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2}, Iff (Eq.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) e e') (And (forall (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e' x)) (And (forall (x : β), Eq.{succ u1} α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) x) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e') x)) (Eq.{succ u1} (Set.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e')))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2}, Iff (Eq.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) e e') (And (forall (x : α), Eq.{succ u1} β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x) (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e' x)) (And (forall (x : β), Eq.{succ u2} α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e) x) (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e') x)) (Eq.{succ u2} (Set.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e')))))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.ext_iff LocalHomeomorph.ext_iffₓ'. -/
protected theorem ext_iff {e e' : LocalHomeomorph α β} :
    e = e' ↔ (∀ x, e x = e' x) ∧ (∀ x, e.symm x = e'.symm x) ∧ e.source = e'.source :=
  ⟨by rintro rfl; exact ⟨fun x => rfl, fun x => rfl, rfl⟩, fun h => e.ext e' h.1 h.2.1 h.2.2⟩
#align local_homeomorph.ext_iff LocalHomeomorph.ext_iff

/- warning: local_homeomorph.symm_to_local_equiv -> LocalHomeomorph.symm_toLocalEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (LocalHomeomorph.toLocalEquiv.{u2, u1} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.symm.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u1, u2} β α) (LocalHomeomorph.toLocalEquiv.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) (LocalEquiv.symm.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.symm_to_local_equiv LocalHomeomorph.symm_toLocalEquivₓ'. -/
@[simp, mfld_simps]
theorem symm_toLocalEquiv : e.symm.toLocalEquiv = e.toLocalEquiv.symm :=
  rfl
#align local_homeomorph.symm_to_local_equiv LocalHomeomorph.symm_toLocalEquiv

#print LocalHomeomorph.symm_source /-
-- The following lemmas are already simp via local_equiv
theorem symm_source : e.symm.source = e.target :=
  rfl
#align local_homeomorph.symm_source LocalHomeomorph.symm_source
-/

/- warning: local_homeomorph.symm_target -> LocalHomeomorph.symm_target is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u1} (Set.{u1} α) (LocalEquiv.target.{u2, u1} β α (LocalHomeomorph.toLocalEquiv.{u2, u1} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e))) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u2} (Set.{u2} α) (LocalEquiv.target.{u1, u2} β α (LocalHomeomorph.toLocalEquiv.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e))) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.symm_target LocalHomeomorph.symm_targetₓ'. -/
theorem symm_target : e.symm.target = e.source :=
  rfl
#align local_homeomorph.symm_target LocalHomeomorph.symm_target

/- warning: local_homeomorph.symm_symm -> LocalHomeomorph.symm_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.symm.{u2, u1} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) e
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalHomeomorph.symm.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) e
Case conversion may be inaccurate. Consider using '#align local_homeomorph.symm_symm LocalHomeomorph.symm_symmₓ'. -/
@[simp, mfld_simps]
theorem symm_symm : e.symm.symm = e :=
  eq_of_localEquiv_eq <| by simp
#align local_homeomorph.symm_symm LocalHomeomorph.symm_symm

/- warning: local_homeomorph.continuous_at -> LocalHomeomorph.continuousAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (ContinuousAt.{u2, u1} α β _inst_1 _inst_2 (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) x)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.continuous_at LocalHomeomorph.continuousAtₓ'. -/
/-- A local homeomorphism is continuous at any point of its source -/
protected theorem continuousAt {x : α} (h : x ∈ e.source) : ContinuousAt e x :=
  (e.ContinuousOn x h).ContinuousAt (e.open_source.mem_nhds h)
#align local_homeomorph.continuous_at LocalHomeomorph.continuousAt

#print LocalHomeomorph.continuousAt_symm /-
/-- A local homeomorphism inverse is continuous at any point of its target -/
theorem continuousAt_symm {x : β} (h : x ∈ e.target) : ContinuousAt e.symm x :=
  e.symm.ContinuousAt h
#align local_homeomorph.continuous_at_symm LocalHomeomorph.continuousAt_symm
-/

/- warning: local_homeomorph.tendsto_symm -> LocalHomeomorph.tendsto_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Filter.Tendsto.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (nhds.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x)) (nhds.{u1} α _inst_1 x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Filter.Tendsto.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) (nhds.{u1} β _inst_2 (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x)) (nhds.{u2} α _inst_1 x))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.tendsto_symm LocalHomeomorph.tendsto_symmₓ'. -/
theorem tendsto_symm {x} (hx : x ∈ e.source) : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
  simpa only [ContinuousAt, e.left_inv hx] using e.continuous_at_symm (e.map_source hx)
#align local_homeomorph.tendsto_symm LocalHomeomorph.tendsto_symm

/- warning: local_homeomorph.map_nhds_eq -> LocalHomeomorph.map_nhds_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (nhds.{u1} α _inst_1 x)) (nhds.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Eq.{succ u1} (Filter.{u1} β) (Filter.map.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (nhds.{u2} α _inst_1 x)) (nhds.{u1} β _inst_2 (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.map_nhds_eq LocalHomeomorph.map_nhds_eqₓ'. -/
theorem map_nhds_eq {x} (hx : x ∈ e.source) : map e (𝓝 x) = 𝓝 (e x) :=
  le_antisymm (e.ContinuousAt hx) <|
    le_map_of_right_inverse (e.eventually_right_inverse' hx) (e.tendsto_symm hx)
#align local_homeomorph.map_nhds_eq LocalHomeomorph.map_nhds_eq

/- warning: local_homeomorph.symm_map_nhds_eq -> LocalHomeomorph.symm_map_nhds_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Eq.{succ u1} (Filter.{u1} α) (Filter.map.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (nhds.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x))) (nhds.{u1} α _inst_1 x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Eq.{succ u2} (Filter.{u2} α) (Filter.map.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) (nhds.{u1} β _inst_2 (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x))) (nhds.{u2} α _inst_1 x))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.symm_map_nhds_eq LocalHomeomorph.symm_map_nhds_eqₓ'. -/
theorem symm_map_nhds_eq {x} (hx : x ∈ e.source) : map e.symm (𝓝 (e x)) = 𝓝 x :=
  (e.symm.map_nhds_eq <| e.map_source hx).trans <| by rw [e.left_inv hx]
#align local_homeomorph.symm_map_nhds_eq LocalHomeomorph.symm_map_nhds_eq

/- warning: local_homeomorph.image_mem_nhds -> LocalHomeomorph.image_mem_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (forall {s : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α _inst_1 x)) -> (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s) (nhds.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (forall {s : Set.{u2} α}, (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s (nhds.{u2} α _inst_1 x)) -> (Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) (Set.image.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) s) (nhds.{u1} β _inst_2 (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x))))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.image_mem_nhds LocalHomeomorph.image_mem_nhdsₓ'. -/
theorem image_mem_nhds {x} (hx : x ∈ e.source) {s : Set α} (hs : s ∈ 𝓝 x) : e '' s ∈ 𝓝 (e x) :=
  e.map_nhds_eq hx ▸ Filter.image_mem_map hs
#align local_homeomorph.image_mem_nhds LocalHomeomorph.image_mem_nhds

/- warning: local_homeomorph.map_nhds_within_eq -> LocalHomeomorph.map_nhdsWithin_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (forall (s : Set.{u1} α), Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (nhdsWithin.{u1} α _inst_1 x s)) (nhdsWithin.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (forall (s : Set.{u2} α), Eq.{succ u1} (Filter.{u1} β) (Filter.map.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (nhdsWithin.{u2} α _inst_1 x s)) (nhdsWithin.{u1} β _inst_2 (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x) (Set.image.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s))))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.map_nhds_within_eq LocalHomeomorph.map_nhdsWithin_eqₓ'. -/
theorem map_nhdsWithin_eq (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) (s : Set α) :
    map e (𝓝[s] x) = 𝓝[e '' (e.source ∩ s)] e x :=
  calc
    map e (𝓝[s] x) = map e (𝓝[e.source ∩ s] x) :=
      congr_arg (map e) (e.nhdsWithin_source_inter hx _).symm
    _ = 𝓝[e '' (e.source ∩ s)] e x :=
      (e.LeftInvOn.mono <| inter_subset_left _ _).map_nhdsWithin_eq (e.left_inv hx)
        (e.continuousAt_symm (e.map_source hx)).ContinuousWithinAt
        (e.ContinuousAt hx).ContinuousWithinAt
    
#align local_homeomorph.map_nhds_within_eq LocalHomeomorph.map_nhdsWithin_eq

/- warning: local_homeomorph.map_nhds_within_preimage_eq -> LocalHomeomorph.map_nhdsWithin_preimage_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (forall (s : Set.{u2} β), Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (nhdsWithin.{u1} α _inst_1 x (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s))) (nhdsWithin.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (forall (s : Set.{u1} β), Eq.{succ u1} (Filter.{u1} β) (Filter.map.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (nhdsWithin.{u2} α _inst_1 x (Set.preimage.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) s))) (nhdsWithin.{u1} β _inst_2 (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x) s))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.map_nhds_within_preimage_eq LocalHomeomorph.map_nhdsWithin_preimage_eqₓ'. -/
theorem map_nhdsWithin_preimage_eq (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) (s : Set β) :
    map e (𝓝[e ⁻¹' s] x) = 𝓝[s] e x := by
  rw [e.map_nhds_within_eq hx, e.image_source_inter_eq', e.target_inter_inv_preimage_preimage,
    e.nhds_within_target_inter (e.map_source hx)]
#align local_homeomorph.map_nhds_within_preimage_eq LocalHomeomorph.map_nhdsWithin_preimage_eq

/- warning: local_homeomorph.eventually_nhds -> LocalHomeomorph.eventually_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : α} (p : β -> Prop), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Iff (Filter.Eventually.{u2} β (fun (y : β) => p y) (nhds.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x))) (Filter.Eventually.{u1} α (fun (x : α) => p (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x)) (nhds.{u1} α _inst_1 x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : α} (p : β -> Prop), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Iff (Filter.Eventually.{u1} β (fun (y : β) => p y) (nhds.{u1} β _inst_2 (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x))) (Filter.Eventually.{u2} α (fun (x : α) => p (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x)) (nhds.{u2} α _inst_1 x)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eventually_nhds LocalHomeomorph.eventually_nhdsₓ'. -/
theorem eventually_nhds (e : LocalHomeomorph α β) {x : α} (p : β → Prop) (hx : x ∈ e.source) :
    (∀ᶠ y in 𝓝 (e x), p y) ↔ ∀ᶠ x in 𝓝 x, p (e x) :=
  Iff.trans (by rw [e.map_nhds_eq hx]) eventually_map
#align local_homeomorph.eventually_nhds LocalHomeomorph.eventually_nhds

/- warning: local_homeomorph.eventually_nhds' -> LocalHomeomorph.eventually_nhds' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : α} (p : α -> Prop), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Iff (Filter.Eventually.{u2} β (fun (y : β) => p (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) y)) (nhds.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x))) (Filter.Eventually.{u1} α (fun (x : α) => p x) (nhds.{u1} α _inst_1 x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : α} (p : α -> Prop), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Iff (Filter.Eventually.{u1} β (fun (y : β) => p (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e) y)) (nhds.{u1} β _inst_2 (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x))) (Filter.Eventually.{u2} α (fun (x : α) => p x) (nhds.{u2} α _inst_1 x)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eventually_nhds' LocalHomeomorph.eventually_nhds'ₓ'. -/
theorem eventually_nhds' (e : LocalHomeomorph α β) {x : α} (p : α → Prop) (hx : x ∈ e.source) :
    (∀ᶠ y in 𝓝 (e x), p (e.symm y)) ↔ ∀ᶠ x in 𝓝 x, p x :=
  by
  rw [e.eventually_nhds _ hx]
  refine' eventually_congr ((e.eventually_left_inverse hx).mono fun y hy => _)
  rw [hy]
#align local_homeomorph.eventually_nhds' LocalHomeomorph.eventually_nhds'

/- warning: local_homeomorph.eventually_nhds_within -> LocalHomeomorph.eventually_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : α} (p : β -> Prop) {s : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Iff (Filter.Eventually.{u2} β (fun (y : β) => p y) (nhdsWithin.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) s))) (Filter.Eventually.{u1} α (fun (x : α) => p (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x)) (nhdsWithin.{u1} α _inst_1 x s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : α} (p : β -> Prop) {s : Set.{u2} α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Iff (Filter.Eventually.{u1} β (fun (y : β) => p y) (nhdsWithin.{u1} β _inst_2 (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x) (Set.preimage.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) s))) (Filter.Eventually.{u2} α (fun (x : α) => p (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x)) (nhdsWithin.{u2} α _inst_1 x s)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eventually_nhds_within LocalHomeomorph.eventually_nhdsWithinₓ'. -/
theorem eventually_nhdsWithin (e : LocalHomeomorph α β) {x : α} (p : β → Prop) {s : Set α}
    (hx : x ∈ e.source) : (∀ᶠ y in 𝓝[e.symm ⁻¹' s] e x, p y) ↔ ∀ᶠ x in 𝓝[s] x, p (e x) :=
  by
  refine' Iff.trans _ eventually_map
  rw [e.map_nhds_within_eq hx, e.image_source_inter_eq', e.nhds_within_target_inter (e.maps_to hx)]
#align local_homeomorph.eventually_nhds_within LocalHomeomorph.eventually_nhdsWithin

/- warning: local_homeomorph.eventually_nhds_within' -> LocalHomeomorph.eventually_nhdsWithin' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {x : α} (p : α -> Prop) {s : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Iff (Filter.Eventually.{u2} β (fun (y : β) => p (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) y)) (nhdsWithin.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) s))) (Filter.Eventually.{u1} α (fun (x : α) => p x) (nhdsWithin.{u1} α _inst_1 x s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {x : α} (p : α -> Prop) {s : Set.{u2} α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Iff (Filter.Eventually.{u1} β (fun (y : β) => p (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e) y)) (nhdsWithin.{u1} β _inst_2 (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x) (Set.preimage.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) s))) (Filter.Eventually.{u2} α (fun (x : α) => p x) (nhdsWithin.{u2} α _inst_1 x s)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eventually_nhds_within' LocalHomeomorph.eventually_nhdsWithin'ₓ'. -/
theorem eventually_nhdsWithin' (e : LocalHomeomorph α β) {x : α} (p : α → Prop) {s : Set α}
    (hx : x ∈ e.source) : (∀ᶠ y in 𝓝[e.symm ⁻¹' s] e x, p (e.symm y)) ↔ ∀ᶠ x in 𝓝[s] x, p x :=
  by
  rw [e.eventually_nhds_within _ hx]
  refine'
    eventually_congr
      ((eventually_nhdsWithin_of_eventually_nhds <| e.eventually_left_inverse hx).mono fun y hy =>
        _)
  rw [hy]
#align local_homeomorph.eventually_nhds_within' LocalHomeomorph.eventually_nhdsWithin'

/- warning: local_homeomorph.preimage_eventually_eq_target_inter_preimage_inter -> LocalHomeomorph.preimage_eventuallyEq_target_inter_preimage_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u3} γ} {x : α} {f : α -> γ}, (ContinuousWithinAt.{u1, u3} α γ _inst_1 _inst_3 f s x) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Membership.Mem.{u3, u3} (Set.{u3} γ) (Filter.{u3} γ) (Filter.hasMem.{u3} γ) t (nhds.{u3} γ _inst_3 (f x))) -> (Filter.EventuallyEq.{u2, 0} β Prop (nhds.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x)) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) s) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Set.preimage.{u1, u3} α γ f t)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] {e : LocalHomeomorph.{u3, u2} α β _inst_1 _inst_2} {s : Set.{u3} α} {t : Set.{u1} γ} {x : α} {f : α -> γ}, (ContinuousWithinAt.{u3, u1} α γ _inst_1 _inst_3 f s x) -> (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (LocalEquiv.source.{u3, u2} α β (LocalHomeomorph.toLocalEquiv.{u3, u2} α β _inst_1 _inst_2 e))) -> (Membership.mem.{u1, u1} (Set.{u1} γ) (Filter.{u1} γ) (instMembershipSetFilter.{u1} γ) t (nhds.{u1} γ _inst_3 (f x))) -> (Filter.EventuallyEq.{u2, 0} β Prop (nhds.{u2} β _inst_2 (LocalHomeomorph.toFun'.{u3, u2} α β _inst_1 _inst_2 e x)) (Set.preimage.{u2, u3} β α (LocalHomeomorph.toFun'.{u2, u3} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u3, u2} α β _inst_1 _inst_2 e)) s) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (LocalEquiv.target.{u3, u2} α β (LocalHomeomorph.toLocalEquiv.{u3, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u3} β α (LocalHomeomorph.toFun'.{u2, u3} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u3, u2} α β _inst_1 _inst_2 e)) (Inter.inter.{u3} (Set.{u3} α) (Set.instInterSet.{u3} α) s (Set.preimage.{u3, u1} α γ f t)))))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.preimage_eventually_eq_target_inter_preimage_inter LocalHomeomorph.preimage_eventuallyEq_target_inter_preimage_interₓ'. -/
/-- This lemma is useful in the manifold library in the case that `e` is a chart. It states that
  locally around `e x` the set `e.symm ⁻¹' s` is the same as the set intersected with the target
  of `e` and some other neighborhood of `f x` (which will be the source of a chart on `γ`).  -/
theorem preimage_eventuallyEq_target_inter_preimage_inter {e : LocalHomeomorph α β} {s : Set α}
    {t : Set γ} {x : α} {f : α → γ} (hf : ContinuousWithinAt f s x) (hxe : x ∈ e.source)
    (ht : t ∈ 𝓝 (f x)) : e.symm ⁻¹' s =ᶠ[𝓝 (e x)] (e.target ∩ e.symm ⁻¹' (s ∩ f ⁻¹' t) : Set β) :=
  by
  rw [eventually_eq_set, e.eventually_nhds _ hxe]
  filter_upwards [e.open_source.mem_nhds hxe,
    mem_nhds_within_iff_eventually.mp (hf.preimage_mem_nhds_within ht)]
  intro y hy hyu
  simp_rw [mem_inter_iff, mem_preimage, mem_inter_iff, e.maps_to hy, true_and_iff, iff_self_and,
    e.left_inv hy, iff_true_intro hyu]
#align local_homeomorph.preimage_eventually_eq_target_inter_preimage_inter LocalHomeomorph.preimage_eventuallyEq_target_inter_preimage_inter

/- warning: local_homeomorph.preimage_open_of_open -> LocalHomeomorph.preimage_open_of_open is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {s : Set.{u2} β}, (IsOpen.{u2} β _inst_2 s) -> (IsOpen.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {s : Set.{u2} β}, (IsOpen.{u2} β _inst_2 s) -> (IsOpen.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (LocalHomeomorph.toFun'.{u1, u2} α β _inst_1 _inst_2 e) s)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.preimage_open_of_open LocalHomeomorph.preimage_open_of_openₓ'. -/
theorem preimage_open_of_open {s : Set β} (hs : IsOpen s) : IsOpen (e.source ∩ e ⁻¹' s) :=
  e.ContinuousOn.preimage_open_of_open e.open_source hs
#align local_homeomorph.preimage_open_of_open LocalHomeomorph.preimage_open_of_open

/-!
### `local_homeomorph.is_image` relation

We say that `t : set β` is an image of `s : set α` under a local homeomorphism `e` if any of the
following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).

This definition is a restatement of `local_equiv.is_image` for local homeomorphisms. In this section
we transfer API about `local_equiv.is_image` to local homeomorphisms and add a few
`local_homeomorph`-specific lemmas like `local_homeomorph.is_image.closure`.
-/


#print LocalHomeomorph.IsImage /-
/-- We say that `t : set β` is an image of `s : set α` under a local homeomorphism `e` if any of the
following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
-/
def IsImage (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)
#align local_homeomorph.is_image LocalHomeomorph.IsImage
-/

namespace IsImage

variable {e} {s : Set α} {t : Set β} {x : α} {y : β}

/- warning: local_homeomorph.is_image.to_local_equiv -> LocalHomeomorph.IsImage.toLocalEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (LocalEquiv.IsImage.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e) s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (LocalEquiv.IsImage.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e) s t)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.to_local_equiv LocalHomeomorph.IsImage.toLocalEquivₓ'. -/
theorem toLocalEquiv (h : e.IsImage s t) : e.toLocalEquiv.IsImage s t :=
  h
#align local_homeomorph.is_image.to_local_equiv LocalHomeomorph.IsImage.toLocalEquiv

/- warning: local_homeomorph.is_image.apply_mem_iff -> LocalHomeomorph.IsImage.apply_mem_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β} {x : α}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x) t) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β} {x : α}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Iff (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x) t) (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.apply_mem_iff LocalHomeomorph.IsImage.apply_mem_iffₓ'. -/
theorem apply_mem_iff (h : e.IsImage s t) (hx : x ∈ e.source) : e x ∈ t ↔ x ∈ s :=
  h hx
#align local_homeomorph.is_image.apply_mem_iff LocalHomeomorph.IsImage.apply_mem_iff

/- warning: local_homeomorph.is_image.symm -> LocalHomeomorph.IsImage.symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u2, u1} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) t s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e) t s)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.symm LocalHomeomorph.IsImage.symmₓ'. -/
protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
  h.toLocalEquiv.symm
#align local_homeomorph.is_image.symm LocalHomeomorph.IsImage.symm

/- warning: local_homeomorph.is_image.symm_apply_mem_iff -> LocalHomeomorph.IsImage.symm_apply_mem_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β} {y : β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) y) s) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β} {y : β}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Iff (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e) y) s) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y t))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.symm_apply_mem_iff LocalHomeomorph.IsImage.symm_apply_mem_iffₓ'. -/
theorem symm_apply_mem_iff (h : e.IsImage s t) (hy : y ∈ e.target) : e.symm y ∈ s ↔ y ∈ t :=
  h.symm hy
#align local_homeomorph.is_image.symm_apply_mem_iff LocalHomeomorph.IsImage.symm_apply_mem_iff

#print LocalHomeomorph.IsImage.symm_iff /-
@[simp]
theorem symm_iff : e.symm.IsImage t s ↔ e.IsImage s t :=
  ⟨fun h => h.symm, fun h => h.symm⟩
#align local_homeomorph.is_image.symm_iff LocalHomeomorph.IsImage.symm_iff
-/

/- warning: local_homeomorph.is_image.maps_to -> LocalHomeomorph.IsImage.mapsTo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (Set.MapsTo.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (Set.MapsTo.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) t))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.maps_to LocalHomeomorph.IsImage.mapsToₓ'. -/
protected theorem mapsTo (h : e.IsImage s t) : MapsTo e (e.source ∩ s) (e.target ∩ t) :=
  h.toLocalEquiv.MapsTo
#align local_homeomorph.is_image.maps_to LocalHomeomorph.IsImage.mapsTo

/- warning: local_homeomorph.is_image.symm_maps_to -> LocalHomeomorph.IsImage.symm_mapsTo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (Set.MapsTo.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (Set.MapsTo.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) t) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.symm_maps_to LocalHomeomorph.IsImage.symm_mapsToₓ'. -/
theorem symm_mapsTo (h : e.IsImage s t) : MapsTo e.symm (e.target ∩ t) (e.source ∩ s) :=
  h.symm.MapsTo
#align local_homeomorph.is_image.symm_maps_to LocalHomeomorph.IsImage.symm_mapsTo

/- warning: local_homeomorph.is_image.image_eq -> LocalHomeomorph.IsImage.image_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) t))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.image_eq LocalHomeomorph.IsImage.image_eqₓ'. -/
theorem image_eq (h : e.IsImage s t) : e '' (e.source ∩ s) = e.target ∩ t :=
  h.toLocalEquiv.image_eq
#align local_homeomorph.is_image.image_eq LocalHomeomorph.IsImage.image_eq

/- warning: local_homeomorph.is_image.symm_image_eq -> LocalHomeomorph.IsImage.symm_image_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (Eq.{succ u2} (Set.{u2} α) (Set.image.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) t)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.symm_image_eq LocalHomeomorph.IsImage.symm_image_eqₓ'. -/
theorem symm_image_eq (h : e.IsImage s t) : e.symm '' (e.target ∩ t) = e.source ∩ s :=
  h.symm.image_eq
#align local_homeomorph.is_image.symm_image_eq LocalHomeomorph.IsImage.symm_image_eq

/- warning: local_homeomorph.is_image.iff_preimage_eq -> LocalHomeomorph.IsImage.iff_preimage_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, Iff (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, Iff (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) t)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.iff_preimage_eq LocalHomeomorph.IsImage.iff_preimage_eqₓ'. -/
theorem iff_preimage_eq : e.IsImage s t ↔ e.source ∩ e ⁻¹' t = e.source ∩ s :=
  LocalEquiv.IsImage.iff_preimage_eq
#align local_homeomorph.is_image.iff_preimage_eq LocalHomeomorph.IsImage.iff_preimage_eq

/- warning: local_homeomorph.is_image.preimage_eq -> LocalHomeomorph.IsImage.preimage_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) t)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.preimage_eq LocalHomeomorph.IsImage.preimage_eqₓ'. -/
/- warning: local_homeomorph.is_image.of_preimage_eq -> LocalHomeomorph.IsImage.of_preimage_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)) -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) t)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s)) -> (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.of_preimage_eq LocalHomeomorph.IsImage.of_preimage_eqₓ'. -/
alias iff_preimage_eq ↔ preimage_eq of_preimage_eq
#align local_homeomorph.is_image.preimage_eq LocalHomeomorph.IsImage.preimage_eq
#align local_homeomorph.is_image.of_preimage_eq LocalHomeomorph.IsImage.of_preimage_eq

/- warning: local_homeomorph.is_image.iff_symm_preimage_eq -> LocalHomeomorph.IsImage.iff_symm_preimage_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, Iff (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) (Eq.{succ u2} (Set.{u2} β) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) s)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, Iff (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) (Eq.{succ u1} (Set.{u1} β) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) s)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) t))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.iff_symm_preimage_eq LocalHomeomorph.IsImage.iff_symm_preimage_eqₓ'. -/
theorem iff_symm_preimage_eq : e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' s = e.target ∩ t :=
  symm_iff.symm.trans iff_preimage_eq
#align local_homeomorph.is_image.iff_symm_preimage_eq LocalHomeomorph.IsImage.iff_symm_preimage_eq

/- warning: local_homeomorph.is_image.symm_preimage_eq -> LocalHomeomorph.IsImage.symm_preimage_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (Eq.{succ u2} (Set.{u2} β) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) s)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (Eq.{succ u1} (Set.{u1} β) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) s)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) t))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.symm_preimage_eq LocalHomeomorph.IsImage.symm_preimage_eqₓ'. -/
/- warning: local_homeomorph.is_image.of_symm_preimage_eq -> LocalHomeomorph.IsImage.of_symm_preimage_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (Eq.{succ u2} (Set.{u2} β) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) s)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) t)) -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (Eq.{succ u1} (Set.{u1} β) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) s)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) t)) -> (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.of_symm_preimage_eq LocalHomeomorph.IsImage.of_symm_preimage_eqₓ'. -/
alias iff_symm_preimage_eq ↔ symm_preimage_eq of_symm_preimage_eq
#align local_homeomorph.is_image.symm_preimage_eq LocalHomeomorph.IsImage.symm_preimage_eq
#align local_homeomorph.is_image.of_symm_preimage_eq LocalHomeomorph.IsImage.of_symm_preimage_eq

/- warning: local_homeomorph.is_image.iff_symm_preimage_eq' -> LocalHomeomorph.IsImage.iff_symm_preimage_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, Iff (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) (Eq.{succ u2} (Set.{u2} β) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s))) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, Iff (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) (Eq.{succ u1} (Set.{u1} β) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s))) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) t))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.iff_symm_preimage_eq' LocalHomeomorph.IsImage.iff_symm_preimage_eq'ₓ'. -/
theorem iff_symm_preimage_eq' :
    e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' (e.source ∩ s) = e.target ∩ t := by
  rw [iff_symm_preimage_eq, ← image_source_inter_eq, ← image_source_inter_eq']
#align local_homeomorph.is_image.iff_symm_preimage_eq' LocalHomeomorph.IsImage.iff_symm_preimage_eq'

/- warning: local_homeomorph.is_image.symm_preimage_eq' -> LocalHomeomorph.IsImage.symm_preimage_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (Eq.{succ u2} (Set.{u2} β) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s))) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (Eq.{succ u1} (Set.{u1} β) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s))) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) t))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.symm_preimage_eq' LocalHomeomorph.IsImage.symm_preimage_eq'ₓ'. -/
/- warning: local_homeomorph.is_image.of_symm_preimage_eq' -> LocalHomeomorph.IsImage.of_symm_preimage_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (Eq.{succ u2} (Set.{u2} β) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s))) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) t)) -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (Eq.{succ u1} (Set.{u1} β) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s))) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) t)) -> (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.of_symm_preimage_eq' LocalHomeomorph.IsImage.of_symm_preimage_eq'ₓ'. -/
alias iff_symm_preimage_eq' ↔ symm_preimage_eq' of_symm_preimage_eq'
#align local_homeomorph.is_image.symm_preimage_eq' LocalHomeomorph.IsImage.symm_preimage_eq'
#align local_homeomorph.is_image.of_symm_preimage_eq' LocalHomeomorph.IsImage.of_symm_preimage_eq'

/- warning: local_homeomorph.is_image.iff_preimage_eq' -> LocalHomeomorph.IsImage.iff_preimage_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, Iff (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) t))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, Iff (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) t))) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.iff_preimage_eq' LocalHomeomorph.IsImage.iff_preimage_eq'ₓ'. -/
theorem iff_preimage_eq' : e.IsImage s t ↔ e.source ∩ e ⁻¹' (e.target ∩ t) = e.source ∩ s :=
  symm_iff.symm.trans iff_symm_preimage_eq'
#align local_homeomorph.is_image.iff_preimage_eq' LocalHomeomorph.IsImage.iff_preimage_eq'

/- warning: local_homeomorph.is_image.preimage_eq' -> LocalHomeomorph.IsImage.preimage_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) t))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) t))) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.preimage_eq' LocalHomeomorph.IsImage.preimage_eq'ₓ'. -/
/- warning: local_homeomorph.is_image.of_preimage_eq' -> LocalHomeomorph.IsImage.of_preimage_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) t))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)) -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) t))) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s)) -> (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.of_preimage_eq' LocalHomeomorph.IsImage.of_preimage_eq'ₓ'. -/
alias iff_preimage_eq' ↔ preimage_eq' of_preimage_eq'
#align local_homeomorph.is_image.preimage_eq' LocalHomeomorph.IsImage.preimage_eq'
#align local_homeomorph.is_image.of_preimage_eq' LocalHomeomorph.IsImage.of_preimage_eq'

/- warning: local_homeomorph.is_image.of_image_eq -> LocalHomeomorph.IsImage.of_image_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) t)) -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (LocalHomeomorph.toFun'.{u1, u2} α β _inst_1 _inst_2 e) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) t)) -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.of_image_eq LocalHomeomorph.IsImage.of_image_eqₓ'. -/
theorem of_image_eq (h : e '' (e.source ∩ s) = e.target ∩ t) : e.IsImage s t :=
  LocalEquiv.IsImage.of_image_eq h
#align local_homeomorph.is_image.of_image_eq LocalHomeomorph.IsImage.of_image_eq

/- warning: local_homeomorph.is_image.of_symm_image_eq -> LocalHomeomorph.IsImage.of_symm_image_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)) -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (Eq.{succ u2} (Set.{u2} α) (Set.image.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) t)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s)) -> (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.of_symm_image_eq LocalHomeomorph.IsImage.of_symm_image_eqₓ'. -/
theorem of_symm_image_eq (h : e.symm '' (e.target ∩ t) = e.source ∩ s) : e.IsImage s t :=
  LocalEquiv.IsImage.of_symm_image_eq h
#align local_homeomorph.is_image.of_symm_image_eq LocalHomeomorph.IsImage.of_symm_image_eq

/- warning: local_homeomorph.is_image.compl -> LocalHomeomorph.IsImage.compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)) t))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.compl LocalHomeomorph.IsImage.complₓ'. -/
protected theorem compl (h : e.IsImage s t) : e.IsImage (sᶜ) (tᶜ) := fun x hx => not_congr (h hx)
#align local_homeomorph.is_image.compl LocalHomeomorph.IsImage.compl

/- warning: local_homeomorph.is_image.inter -> LocalHomeomorph.IsImage.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β} {s' : Set.{u1} α} {t' : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s' t') -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s s') (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t t'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β} {s' : Set.{u2} α} {t' : Set.{u1} β}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s' t') -> (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s s') (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) t t'))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.inter LocalHomeomorph.IsImage.interₓ'. -/
protected theorem inter {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∩ s') (t ∩ t') := fun x hx => and_congr (h hx) (h' hx)
#align local_homeomorph.is_image.inter LocalHomeomorph.IsImage.inter

/- warning: local_homeomorph.is_image.union -> LocalHomeomorph.IsImage.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β} {s' : Set.{u1} α} {t' : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s' t') -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s s') (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) t t'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β} {s' : Set.{u2} α} {t' : Set.{u1} β}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s' t') -> (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s s') (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) t t'))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.union LocalHomeomorph.IsImage.unionₓ'. -/
protected theorem union {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∪ s') (t ∪ t') := fun x hx => or_congr (h hx) (h' hx)
#align local_homeomorph.is_image.union LocalHomeomorph.IsImage.union

/- warning: local_homeomorph.is_image.diff -> LocalHomeomorph.IsImage.diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β} {s' : Set.{u1} α} {t' : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s' t') -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s s') (SDiff.sdiff.{u2} (Set.{u2} β) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) t t'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β} {s' : Set.{u2} α} {t' : Set.{u1} β}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s' t') -> (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) s s') (SDiff.sdiff.{u1} (Set.{u1} β) (Set.instSDiffSet.{u1} β) t t'))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.diff LocalHomeomorph.IsImage.diffₓ'. -/
protected theorem diff {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s \ s') (t \ t') :=
  h.inter h'.compl
#align local_homeomorph.is_image.diff LocalHomeomorph.IsImage.diff

/- warning: local_homeomorph.is_image.left_inv_on_piecewise -> LocalHomeomorph.IsImage.leftInvOn_piecewise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β} {e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} [_inst_5 : forall (i : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s)] [_inst_6 : forall (i : β), Decidable (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i t)], (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e' s t) -> (Set.LeftInvOn.{u1, u2} α β (Set.piecewise.{u2, succ u1} β (fun (ᾰ : β) => α) t (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e')) (fun (j : β) => _inst_6 j)) (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e') (fun (j : α) => _inst_5 j)) (Set.ite.{u1} α s (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e'))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β} {e' : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} [_inst_5 : forall (i : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s)] [_inst_6 : forall (i : β), Decidable (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) i t)], (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e' s t) -> (Set.LeftInvOn.{u2, u1} α β (Set.piecewise.{u1, succ u2} β (fun (ᾰ : β) => α) t (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e')) (fun (j : β) => _inst_6 j)) (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) s (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e') (fun (j : α) => _inst_5 j)) (Set.ite.{u2} α s (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e'))))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.left_inv_on_piecewise LocalHomeomorph.IsImage.leftInvOn_piecewiseₓ'. -/
theorem leftInvOn_piecewise {e' : LocalHomeomorph α β} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : e.IsImage s t) (h' : e'.IsImage s t) :
    LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source) :=
  h.toLocalEquiv.leftInvOn_piecewise h'
#align local_homeomorph.is_image.left_inv_on_piecewise LocalHomeomorph.IsImage.leftInvOn_piecewise

/- warning: local_homeomorph.is_image.inter_eq_of_inter_eq_of_eq_on -> LocalHomeomorph.IsImage.inter_eq_of_inter_eq_of_eqOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β} {e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e' s t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e')) s)) -> (Set.EqOn.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e') (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)) -> (Eq.{succ u2} (Set.{u2} β) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) t) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e')) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β} {e' : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e' s t) -> (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e')) s)) -> (Set.EqOn.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e') (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s)) -> (Eq.{succ u1} (Set.{u1} β) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) t) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e')) t))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.inter_eq_of_inter_eq_of_eq_on LocalHomeomorph.IsImage.inter_eq_of_inter_eq_of_eqOnₓ'. -/
theorem inter_eq_of_inter_eq_of_eqOn {e' : LocalHomeomorph α β} (h : e.IsImage s t)
    (h' : e'.IsImage s t) (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    e.target ∩ t = e'.target ∩ t :=
  h.toLocalEquiv.inter_eq_of_inter_eq_of_eqOn h' hs Heq
#align local_homeomorph.is_image.inter_eq_of_inter_eq_of_eq_on LocalHomeomorph.IsImage.inter_eq_of_inter_eq_of_eqOn

/- warning: local_homeomorph.is_image.symm_eq_on_of_inter_eq_of_eq_on -> LocalHomeomorph.IsImage.symm_eqOn_of_inter_eq_of_eqOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β} {e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e')) s)) -> (Set.EqOn.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e') (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)) -> (Set.EqOn.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e')) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β} {e' : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e')) s)) -> (Set.EqOn.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e') (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s)) -> (Set.EqOn.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e')) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) t))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.symm_eq_on_of_inter_eq_of_eq_on LocalHomeomorph.IsImage.symm_eqOn_of_inter_eq_of_eqOnₓ'. -/
theorem symm_eqOn_of_inter_eq_of_eqOn {e' : LocalHomeomorph α β} (h : e.IsImage s t)
    (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    EqOn e.symm e'.symm (e.target ∩ t) :=
  h.toLocalEquiv.symm_eq_on_of_inter_eq_of_eqOn hs Heq
#align local_homeomorph.is_image.symm_eq_on_of_inter_eq_of_eq_on LocalHomeomorph.IsImage.symm_eqOn_of_inter_eq_of_eqOn

/- warning: local_homeomorph.is_image.map_nhds_within_eq -> LocalHomeomorph.IsImage.map_nhdsWithin_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β} {x : α}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (nhdsWithin.{u1} α _inst_1 x s)) (nhdsWithin.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β} {x : α}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Eq.{succ u1} (Filter.{u1} β) (Filter.map.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (nhdsWithin.{u2} α _inst_1 x s)) (nhdsWithin.{u1} β _inst_2 (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x) t))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.map_nhds_within_eq LocalHomeomorph.IsImage.map_nhdsWithin_eqₓ'. -/
theorem map_nhdsWithin_eq (h : e.IsImage s t) (hx : x ∈ e.source) : map e (𝓝[s] x) = 𝓝[t] e x := by
  rw [e.map_nhds_within_eq hx, h.image_eq, e.nhds_within_target_inter (e.map_source hx)]
#align local_homeomorph.is_image.map_nhds_within_eq LocalHomeomorph.IsImage.map_nhdsWithin_eq

/- warning: local_homeomorph.is_image.closure -> LocalHomeomorph.IsImage.closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e (closure.{u1} α _inst_1 s) (closure.{u2} β _inst_2 t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e (closure.{u2} α _inst_1 s) (closure.{u1} β _inst_2 t))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.closure LocalHomeomorph.IsImage.closureₓ'. -/
protected theorem closure (h : e.IsImage s t) : e.IsImage (closure s) (closure t) := fun x hx => by
  simp only [mem_closure_iff_nhdsWithin_neBot, ← h.map_nhds_within_eq hx, map_ne_bot_iff]
#align local_homeomorph.is_image.closure LocalHomeomorph.IsImage.closure

/- warning: local_homeomorph.is_image.interior -> LocalHomeomorph.IsImage.interior is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e (interior.{u1} α _inst_1 s) (interior.{u2} β _inst_2 t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e (interior.{u2} α _inst_1 s) (interior.{u1} β _inst_2 t))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.interior LocalHomeomorph.IsImage.interiorₓ'. -/
protected theorem interior (h : e.IsImage s t) : e.IsImage (interior s) (interior t) := by
  simpa only [closure_compl, compl_compl] using h.compl.closure.compl
#align local_homeomorph.is_image.interior LocalHomeomorph.IsImage.interior

/- warning: local_homeomorph.is_image.frontier -> LocalHomeomorph.IsImage.frontier is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e (frontier.{u1} α _inst_1 s) (frontier.{u2} β _inst_2 t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e (frontier.{u2} α _inst_1 s) (frontier.{u1} β _inst_2 t))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.frontier LocalHomeomorph.IsImage.frontierₓ'. -/
protected theorem frontier (h : e.IsImage s t) : e.IsImage (frontier s) (frontier t) :=
  h.closure.diffₓ h.interior
#align local_homeomorph.is_image.frontier LocalHomeomorph.IsImage.frontier

/- warning: local_homeomorph.is_image.is_open_iff -> LocalHomeomorph.IsImage.isOpen_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (Iff (IsOpen.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)) (IsOpen.{u2} β _inst_2 (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e s t) -> (Iff (IsOpen.{u2} α _inst_1 (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s)) (IsOpen.{u1} β _inst_2 (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) t)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.is_open_iff LocalHomeomorph.IsImage.isOpen_iffₓ'. -/
theorem isOpen_iff (h : e.IsImage s t) : IsOpen (e.source ∩ s) ↔ IsOpen (e.target ∩ t) :=
  ⟨fun hs => h.symm_preimage_eq' ▸ e.symm.preimage_open_of_open hs, fun hs =>
    h.preimage_eq' ▸ e.preimage_open_of_open hs⟩
#align local_homeomorph.is_image.is_open_iff LocalHomeomorph.IsImage.isOpen_iff

/- warning: local_homeomorph.is_image.restr -> LocalHomeomorph.IsImage.restr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (IsOpen.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)) -> (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (IsOpen.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)) -> (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image.restr LocalHomeomorph.IsImage.restrₓ'. -/
/-- Restrict a `local_homeomorph` to a pair of corresponding open sets. -/
@[simps toLocalEquiv]
def restr (h : e.IsImage s t) (hs : IsOpen (e.source ∩ s)) : LocalHomeomorph α β
    where
  toLocalEquiv := h.toLocalEquiv.restr
  open_source := hs
  open_target := h.isOpen_iff.1 hs
  continuous_toFun := e.ContinuousOn.mono (inter_subset_left _ _)
  continuous_invFun := e.symm.ContinuousOn.mono (inter_subset_left _ _)
#align local_homeomorph.is_image.restr LocalHomeomorph.IsImage.restr

end IsImage

/- warning: local_homeomorph.is_image_source_target -> LocalHomeomorph.isImage_source_target is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image_source_target LocalHomeomorph.isImage_source_targetₓ'. -/
theorem isImage_source_target : e.IsImage e.source e.target :=
  e.toLocalEquiv.isImage_source_target
#align local_homeomorph.is_image_source_target LocalHomeomorph.isImage_source_target

/- warning: local_homeomorph.is_image_source_target_of_disjoint -> LocalHomeomorph.isImage_source_target_of_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e'))) -> (Disjoint.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e'))) -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e')) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e')))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e'))) -> (Disjoint.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} β) (Preorder.toLE.{u1} (Set.{u1} β) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))))) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e'))) -> (LocalHomeomorph.IsImage.{u2, u1} α β _inst_1 _inst_2 e (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e')) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e')))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.is_image_source_target_of_disjoint LocalHomeomorph.isImage_source_target_of_disjointₓ'. -/
theorem isImage_source_target_of_disjoint (e' : LocalHomeomorph α β)
    (hs : Disjoint e.source e'.source) (ht : Disjoint e.target e'.target) :
    e.IsImage e'.source e'.target :=
  e.toLocalEquiv.isImage_source_target_of_disjoint e'.toLocalEquiv hs ht
#align local_homeomorph.is_image_source_target_of_disjoint LocalHomeomorph.isImage_source_target_of_disjoint

/- warning: local_homeomorph.preimage_interior -> LocalHomeomorph.preimage_interior is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (interior.{u2} β _inst_2 s))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (interior.{u1} α _inst_1 (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (LocalHomeomorph.toFun'.{u1, u2} α β _inst_1 _inst_2 e) (interior.{u2} β _inst_2 s))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (interior.{u1} α _inst_1 (Set.preimage.{u1, u2} α β (LocalHomeomorph.toFun'.{u1, u2} α β _inst_1 _inst_2 e) s)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.preimage_interior LocalHomeomorph.preimage_interiorₓ'. -/
/-- Preimage of interior or interior of preimage coincide for local homeomorphisms, when restricted
to the source. -/
theorem preimage_interior (s : Set β) :
    e.source ∩ e ⁻¹' interior s = e.source ∩ interior (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).interior.preimage_eq
#align local_homeomorph.preimage_interior LocalHomeomorph.preimage_interior

/- warning: local_homeomorph.preimage_closure -> LocalHomeomorph.preimage_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (closure.{u2} β _inst_2 s))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (closure.{u1} α _inst_1 (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (LocalHomeomorph.toFun'.{u1, u2} α β _inst_1 _inst_2 e) (closure.{u2} β _inst_2 s))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (closure.{u1} α _inst_1 (Set.preimage.{u1, u2} α β (LocalHomeomorph.toFun'.{u1, u2} α β _inst_1 _inst_2 e) s)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.preimage_closure LocalHomeomorph.preimage_closureₓ'. -/
theorem preimage_closure (s : Set β) : e.source ∩ e ⁻¹' closure s = e.source ∩ closure (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).closure.preimage_eq
#align local_homeomorph.preimage_closure LocalHomeomorph.preimage_closure

/- warning: local_homeomorph.preimage_frontier -> LocalHomeomorph.preimage_frontier is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (frontier.{u2} β _inst_2 s))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (frontier.{u1} α _inst_1 (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (LocalHomeomorph.toFun'.{u1, u2} α β _inst_1 _inst_2 e) (frontier.{u2} β _inst_2 s))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (frontier.{u1} α _inst_1 (Set.preimage.{u1, u2} α β (LocalHomeomorph.toFun'.{u1, u2} α β _inst_1 _inst_2 e) s)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.preimage_frontier LocalHomeomorph.preimage_frontierₓ'. -/
theorem preimage_frontier (s : Set β) :
    e.source ∩ e ⁻¹' frontier s = e.source ∩ frontier (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).frontier.preimage_eq
#align local_homeomorph.preimage_frontier LocalHomeomorph.preimage_frontier

/- warning: local_homeomorph.preimage_open_of_open_symm -> LocalHomeomorph.preimage_open_of_open_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {s : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (IsOpen.{u2} β _inst_2 (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {s : Set.{u2} α}, (IsOpen.{u2} α _inst_1 s) -> (IsOpen.{u1} β _inst_2 (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) s)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.preimage_open_of_open_symm LocalHomeomorph.preimage_open_of_open_symmₓ'. -/
theorem preimage_open_of_open_symm {s : Set α} (hs : IsOpen s) : IsOpen (e.target ∩ e.symm ⁻¹' s) :=
  e.symm.ContinuousOn.preimage_open_of_open e.open_target hs
#align local_homeomorph.preimage_open_of_open_symm LocalHomeomorph.preimage_open_of_open_symm

/- warning: local_homeomorph.image_open_of_open -> LocalHomeomorph.image_open_of_open is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {s : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (IsOpen.{u2} β _inst_2 (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {s : Set.{u2} α}, (IsOpen.{u2} α _inst_1 s) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (IsOpen.{u1} β _inst_2 (Set.image.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) s))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.image_open_of_open LocalHomeomorph.image_open_of_openₓ'. -/
/-- The image of an open set in the source is open. -/
theorem image_open_of_open {s : Set α} (hs : IsOpen s) (h : s ⊆ e.source) : IsOpen (e '' s) :=
  by
  have : e '' s = e.target ∩ e.symm ⁻¹' s := e.to_local_equiv.image_eq_target_inter_inv_preimage h
  rw [this]
  exact e.continuous_on_symm.preimage_open_of_open e.open_target hs
#align local_homeomorph.image_open_of_open LocalHomeomorph.image_open_of_open

/- warning: local_homeomorph.image_open_of_open' -> LocalHomeomorph.image_open_of_open' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {s : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (IsOpen.{u2} β _inst_2 (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {s : Set.{u2} α}, (IsOpen.{u2} α _inst_1 s) -> (IsOpen.{u1} β _inst_2 (Set.image.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.image_open_of_open' LocalHomeomorph.image_open_of_open'ₓ'. -/
/-- The image of the restriction of an open set to the source is open. -/
theorem image_open_of_open' {s : Set α} (hs : IsOpen s) : IsOpen (e '' (e.source ∩ s)) :=
  image_open_of_open _ (IsOpen.inter e.open_source hs) (inter_subset_left _ _)
#align local_homeomorph.image_open_of_open' LocalHomeomorph.image_open_of_open'

#print LocalHomeomorph.ofContinuousOpenRestrict /-
/-- A `local_equiv` with continuous open forward map and an open source is a `local_homeomorph`. -/
def ofContinuousOpenRestrict (e : LocalEquiv α β) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.restrict e)) (hs : IsOpen e.source) : LocalHomeomorph α β
    where
  toLocalEquiv := e
  open_source := hs
  open_target := by simpa only [range_restrict, e.image_source_eq_target] using ho.is_open_range
  continuous_toFun := hc
  continuous_invFun := e.image_source_eq_target ▸ ho.continuousOn_image_of_leftInvOn e.LeftInvOn
#align local_homeomorph.of_continuous_open_restrict LocalHomeomorph.ofContinuousOpenRestrict
-/

#print LocalHomeomorph.ofContinuousOpen /-
/-- A `local_equiv` with continuous open forward map and an open source is a `local_homeomorph`. -/
def ofContinuousOpen (e : LocalEquiv α β) (hc : ContinuousOn e e.source) (ho : IsOpenMap e)
    (hs : IsOpen e.source) : LocalHomeomorph α β :=
  ofContinuousOpenRestrict e hc (ho.restrict hs) hs
#align local_homeomorph.of_continuous_open LocalHomeomorph.ofContinuousOpen
-/

#print LocalHomeomorph.restrOpen /-
/-- Restricting a local homeomorphism `e` to `e.source ∩ s` when `s` is open. This is sometimes hard
to use because of the openness assumption, but it has the advantage that when it can
be used then its local_equiv is defeq to local_equiv.restr -/
protected def restrOpen (s : Set α) (hs : IsOpen s) : LocalHomeomorph α β :=
  (@IsImage.of_symm_preimage_eq α β _ _ e s (e.symm ⁻¹' s) rfl).restr
    (IsOpen.inter e.open_source hs)
#align local_homeomorph.restr_open LocalHomeomorph.restrOpen
-/

/- warning: local_homeomorph.restr_open_to_local_equiv -> LocalHomeomorph.restrOpen_toLocalEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α) (hs : IsOpen.{u1} α _inst_1 s), Eq.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 (LocalHomeomorph.restrOpen.{u1, u2} α β _inst_1 _inst_2 e s hs)) (LocalEquiv.restr.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α) (hs : IsOpen.{u2} α _inst_1 s), Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 (LocalHomeomorph.restrOpen.{u2, u1} α β _inst_1 _inst_2 e s hs)) (LocalEquiv.restr.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e) s)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.restr_open_to_local_equiv LocalHomeomorph.restrOpen_toLocalEquivₓ'. -/
@[simp, mfld_simps]
theorem restrOpen_toLocalEquiv (s : Set α) (hs : IsOpen s) :
    (e.restrOpen s hs).toLocalEquiv = e.toLocalEquiv.restr s :=
  rfl
#align local_homeomorph.restr_open_to_local_equiv LocalHomeomorph.restrOpen_toLocalEquiv

/- warning: local_homeomorph.restr_open_source -> LocalHomeomorph.restrOpen_source is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α) (hs : IsOpen.{u1} α _inst_1 s), Eq.{succ u1} (Set.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 (LocalHomeomorph.restrOpen.{u1, u2} α β _inst_1 _inst_2 e s hs))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α) (hs : IsOpen.{u2} α _inst_1 s), Eq.{succ u2} (Set.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 (LocalHomeomorph.restrOpen.{u2, u1} α β _inst_1 _inst_2 e s hs))) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.restr_open_source LocalHomeomorph.restrOpen_sourceₓ'. -/
-- Already simp via local_equiv
theorem restrOpen_source (s : Set α) (hs : IsOpen s) : (e.restrOpen s hs).source = e.source ∩ s :=
  rfl
#align local_homeomorph.restr_open_source LocalHomeomorph.restrOpen_source

#print LocalHomeomorph.restr /-
/-- Restricting a local homeomorphism `e` to `e.source ∩ interior s`. We use the interior to make
sure that the restriction is well defined whatever the set s, since local homeomorphisms are by
definition defined on open sets. In applications where `s` is open, this coincides with the
restriction of local equivalences -/
@[simps (config := mfld_cfg) apply symm_apply, simps (config := { attrs := [] }) source target]
protected def restr (s : Set α) : LocalHomeomorph α β :=
  e.restrOpen (interior s) isOpen_interior
#align local_homeomorph.restr LocalHomeomorph.restr
-/

/- warning: local_homeomorph.restr_to_local_equiv -> LocalHomeomorph.restr_toLocalEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), Eq.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 (LocalHomeomorph.restr.{u1, u2} α β _inst_1 _inst_2 e s)) (LocalEquiv.restr.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e) (interior.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α), Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 (LocalHomeomorph.restr.{u2, u1} α β _inst_1 _inst_2 e s)) (LocalEquiv.restr.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e) (interior.{u2} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.restr_to_local_equiv LocalHomeomorph.restr_toLocalEquivₓ'. -/
@[simp, mfld_simps]
theorem restr_toLocalEquiv (s : Set α) :
    (e.restr s).toLocalEquiv = e.toLocalEquiv.restr (interior s) :=
  rfl
#align local_homeomorph.restr_to_local_equiv LocalHomeomorph.restr_toLocalEquiv

/- warning: local_homeomorph.restr_source' -> LocalHomeomorph.restr_source' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), (IsOpen.{u1} α _inst_1 s) -> (Eq.{succ u1} (Set.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 (LocalHomeomorph.restr.{u1, u2} α β _inst_1 _inst_2 e s))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α), (IsOpen.{u2} α _inst_1 s) -> (Eq.{succ u2} (Set.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 (LocalHomeomorph.restr.{u2, u1} α β _inst_1 _inst_2 e s))) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.restr_source' LocalHomeomorph.restr_source'ₓ'. -/
theorem restr_source' (s : Set α) (hs : IsOpen s) : (e.restr s).source = e.source ∩ s := by
  rw [e.restr_source, hs.interior_eq]
#align local_homeomorph.restr_source' LocalHomeomorph.restr_source'

/- warning: local_homeomorph.restr_to_local_equiv' -> LocalHomeomorph.restr_toLocalEquiv' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), (IsOpen.{u1} α _inst_1 s) -> (Eq.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 (LocalHomeomorph.restr.{u1, u2} α β _inst_1 _inst_2 e s)) (LocalEquiv.restr.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α), (IsOpen.{u2} α _inst_1 s) -> (Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 (LocalHomeomorph.restr.{u2, u1} α β _inst_1 _inst_2 e s)) (LocalEquiv.restr.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e) s))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.restr_to_local_equiv' LocalHomeomorph.restr_toLocalEquiv'ₓ'. -/
theorem restr_toLocalEquiv' (s : Set α) (hs : IsOpen s) :
    (e.restr s).toLocalEquiv = e.toLocalEquiv.restr s := by
  rw [e.restr_to_local_equiv, hs.interior_eq]
#align local_homeomorph.restr_to_local_equiv' LocalHomeomorph.restr_toLocalEquiv'

/- warning: local_homeomorph.restr_eq_of_source_subset -> LocalHomeomorph.restr_eq_of_source_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {s : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s) -> (Eq.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.restr.{u1, u2} α β _inst_1 _inst_2 e s) e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {s : Set.{u2} α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s) -> (Eq.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalHomeomorph.restr.{u2, u1} α β _inst_1 _inst_2 e s) e)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.restr_eq_of_source_subset LocalHomeomorph.restr_eq_of_source_subsetₓ'. -/
theorem restr_eq_of_source_subset {e : LocalHomeomorph α β} {s : Set α} (h : e.source ⊆ s) :
    e.restr s = e := by
  apply eq_of_local_equiv_eq
  rw [restr_to_local_equiv]
  apply LocalEquiv.restr_eq_of_source_subset
  exact interior_maximal h e.open_source
#align local_homeomorph.restr_eq_of_source_subset LocalHomeomorph.restr_eq_of_source_subset

/- warning: local_homeomorph.restr_univ -> LocalHomeomorph.restr_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2}, Eq.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.restr.{u1, u2} α β _inst_1 _inst_2 e (Set.univ.{u1} α)) e
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2}, Eq.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalHomeomorph.restr.{u2, u1} α β _inst_1 _inst_2 e (Set.univ.{u2} α)) e
Case conversion may be inaccurate. Consider using '#align local_homeomorph.restr_univ LocalHomeomorph.restr_univₓ'. -/
@[simp, mfld_simps]
theorem restr_univ {e : LocalHomeomorph α β} : e.restr univ = e :=
  restr_eq_of_source_subset (subset_univ _)
#align local_homeomorph.restr_univ LocalHomeomorph.restr_univ

/- warning: local_homeomorph.restr_source_inter -> LocalHomeomorph.restr_source_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), Eq.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.restr.{u1, u2} α β _inst_1 _inst_2 e (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s)) (LocalHomeomorph.restr.{u1, u2} α β _inst_1 _inst_2 e s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α), Eq.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalHomeomorph.restr.{u2, u1} α β _inst_1 _inst_2 e (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s)) (LocalHomeomorph.restr.{u2, u1} α β _inst_1 _inst_2 e s)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.restr_source_inter LocalHomeomorph.restr_source_interₓ'. -/
theorem restr_source_inter (s : Set α) : e.restr (e.source ∩ s) = e.restr s :=
  by
  refine' LocalHomeomorph.ext _ _ (fun x => rfl) (fun x => rfl) _
  simp [e.open_source.interior_eq, ← inter_assoc]
#align local_homeomorph.restr_source_inter LocalHomeomorph.restr_source_inter

#print LocalHomeomorph.refl /-
/-- The identity on the whole space as a local homeomorphism. -/
@[simps (config := mfld_cfg) apply, simps (config := { attrs := [] }) source target]
protected def refl (α : Type _) [TopologicalSpace α] : LocalHomeomorph α α :=
  (Homeomorph.refl α).toLocalHomeomorph
#align local_homeomorph.refl LocalHomeomorph.refl
-/

#print LocalHomeomorph.refl_localEquiv /-
@[simp, mfld_simps]
theorem refl_localEquiv : (LocalHomeomorph.refl α).toLocalEquiv = LocalEquiv.refl α :=
  rfl
#align local_homeomorph.refl_local_equiv LocalHomeomorph.refl_localEquiv
-/

#print LocalHomeomorph.refl_symm /-
@[simp, mfld_simps]
theorem refl_symm : (LocalHomeomorph.refl α).symm = LocalHomeomorph.refl α :=
  rfl
#align local_homeomorph.refl_symm LocalHomeomorph.refl_symm
-/

section

variable {s : Set α} (hs : IsOpen s)

#print LocalHomeomorph.ofSet /-
/-- The identity local equiv on a set `s` -/
@[simps (config := mfld_cfg) apply, simps (config := { attrs := [] }) source target]
def ofSet (s : Set α) (hs : IsOpen s) : LocalHomeomorph α α :=
  { LocalEquiv.ofSet s with
    open_source := hs
    open_target := hs
    continuous_toFun := continuous_id.ContinuousOn
    continuous_invFun := continuous_id.ContinuousOn }
#align local_homeomorph.of_set LocalHomeomorph.ofSet
-/

#print LocalHomeomorph.ofSet_toLocalEquiv /-
@[simp, mfld_simps]
theorem ofSet_toLocalEquiv : (ofSet s hs).toLocalEquiv = LocalEquiv.ofSet s :=
  rfl
#align local_homeomorph.of_set_to_local_equiv LocalHomeomorph.ofSet_toLocalEquiv
-/

#print LocalHomeomorph.ofSet_symm /-
@[simp, mfld_simps]
theorem ofSet_symm : (ofSet s hs).symm = ofSet s hs :=
  rfl
#align local_homeomorph.of_set_symm LocalHomeomorph.ofSet_symm
-/

#print LocalHomeomorph.ofSet_univ_eq_refl /-
@[simp, mfld_simps]
theorem ofSet_univ_eq_refl : ofSet univ isOpen_univ = LocalHomeomorph.refl α := by ext <;> simp
#align local_homeomorph.of_set_univ_eq_refl LocalHomeomorph.ofSet_univ_eq_refl
-/

end

#print LocalHomeomorph.trans' /-
/-- Composition of two local homeomorphisms when the target of the first and the source of
the second coincide. -/
protected def trans' (h : e.target = e'.source) : LocalHomeomorph α γ :=
  {
    LocalEquiv.trans' e.toLocalEquiv e'.toLocalEquiv
      h with
    open_source := e.open_source
    open_target := e'.open_target
    continuous_toFun := by
      apply e'.continuous_to_fun.comp e.continuous_to_fun
      rw [← h]
      exact e.to_local_equiv.source_subset_preimage_target
    continuous_invFun := by
      apply e.continuous_inv_fun.comp e'.continuous_inv_fun
      rw [h]
      exact e'.to_local_equiv.target_subset_preimage_source }
#align local_homeomorph.trans' LocalHomeomorph.trans'
-/

#print LocalHomeomorph.trans /-
/-- Composing two local homeomorphisms, by restricting to the maximal domain where their
composition is well defined. -/
protected def trans : LocalHomeomorph α γ :=
  LocalHomeomorph.trans' (e.symm.restrOpen e'.source e'.open_source).symm
    (e'.restrOpen e.target e.open_target) (by simp [inter_comm])
#align local_homeomorph.trans LocalHomeomorph.trans
-/

/- warning: local_homeomorph.trans_to_local_equiv -> LocalHomeomorph.trans_toLocalEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3), Eq.{max (succ u1) (succ u3)} (LocalEquiv.{u1, u3} α γ) (LocalHomeomorph.toLocalEquiv.{u1, u3} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e e')) (LocalEquiv.trans.{u1, u2, u3} α β γ (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e) (LocalHomeomorph.toLocalEquiv.{u2, u3} β γ _inst_2 _inst_3 e'))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u2} γ] (e : LocalHomeomorph.{u3, u1} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u2} β γ _inst_2 _inst_3), Eq.{max (succ u3) (succ u2)} (LocalEquiv.{u3, u2} α γ) (LocalHomeomorph.toLocalEquiv.{u3, u2} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u3, u1, u2} α β γ _inst_1 _inst_2 _inst_3 e e')) (LocalEquiv.trans.{u3, u1, u2} α β γ (LocalHomeomorph.toLocalEquiv.{u3, u1} α β _inst_1 _inst_2 e) (LocalHomeomorph.toLocalEquiv.{u1, u2} β γ _inst_2 _inst_3 e'))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.trans_to_local_equiv LocalHomeomorph.trans_toLocalEquivₓ'. -/
@[simp, mfld_simps]
theorem trans_toLocalEquiv : (e.trans e').toLocalEquiv = e.toLocalEquiv.trans e'.toLocalEquiv :=
  rfl
#align local_homeomorph.trans_to_local_equiv LocalHomeomorph.trans_toLocalEquiv

/- warning: local_homeomorph.coe_trans -> LocalHomeomorph.coe_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3), Eq.{max (succ u1) (succ u3)} ((fun (_x : LocalHomeomorph.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e e')) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (LocalHomeomorph.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : LocalHomeomorph.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (LocalHomeomorph.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e e')) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (LocalHomeomorph.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) e') (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u2} γ] (e : LocalHomeomorph.{u3, u1} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u2} β γ _inst_2 _inst_3), Eq.{max (succ u3) (succ u2)} (α -> γ) (LocalHomeomorph.toFun'.{u3, u2} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u3, u1, u2} α β γ _inst_1 _inst_2 _inst_3 e e')) (Function.comp.{succ u3, succ u1, succ u2} α β γ (LocalHomeomorph.toFun'.{u1, u2} β γ _inst_2 _inst_3 e') (LocalHomeomorph.toFun'.{u3, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.coe_trans LocalHomeomorph.coe_transₓ'. -/
@[simp, mfld_simps]
theorem coe_trans : (e.trans e' : α → γ) = e' ∘ e :=
  rfl
#align local_homeomorph.coe_trans LocalHomeomorph.coe_trans

/- warning: local_homeomorph.coe_trans_symm -> LocalHomeomorph.coe_trans_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3), Eq.{max (succ u3) (succ u1)} ((fun (_x : LocalHomeomorph.{u3, u1} γ α _inst_3 _inst_1) => γ -> α) (LocalHomeomorph.symm.{u1, u3} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e e'))) (coeFn.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (LocalHomeomorph.{u3, u1} γ α _inst_3 _inst_1) (fun (_x : LocalHomeomorph.{u3, u1} γ α _inst_3 _inst_1) => γ -> α) (LocalHomeomorph.hasCoeToFun.{u3, u1} γ α _inst_3 _inst_1) (LocalHomeomorph.symm.{u1, u3} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e e'))) (Function.comp.{succ u3, succ u2, succ u1} γ β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (LocalHomeomorph.{u3, u2} γ β _inst_3 _inst_2) (fun (_x : LocalHomeomorph.{u3, u2} γ β _inst_3 _inst_2) => γ -> β) (LocalHomeomorph.hasCoeToFun.{u3, u2} γ β _inst_3 _inst_2) (LocalHomeomorph.symm.{u2, u3} β γ _inst_2 _inst_3 e')))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u2} γ] (e : LocalHomeomorph.{u3, u1} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u2} β γ _inst_2 _inst_3), Eq.{max (succ u3) (succ u2)} (γ -> α) (LocalHomeomorph.toFun'.{u2, u3} γ α _inst_3 _inst_1 (LocalHomeomorph.symm.{u3, u2} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u3, u1, u2} α β γ _inst_1 _inst_2 _inst_3 e e'))) (Function.comp.{succ u2, succ u1, succ u3} γ β α (LocalHomeomorph.toFun'.{u1, u3} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u3, u1} α β _inst_1 _inst_2 e)) (LocalHomeomorph.toFun'.{u2, u1} γ β _inst_3 _inst_2 (LocalHomeomorph.symm.{u1, u2} β γ _inst_2 _inst_3 e')))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.coe_trans_symm LocalHomeomorph.coe_trans_symmₓ'. -/
@[simp, mfld_simps]
theorem coe_trans_symm : ((e.trans e').symm : γ → α) = e.symm ∘ e'.symm :=
  rfl
#align local_homeomorph.coe_trans_symm LocalHomeomorph.coe_trans_symm

/- warning: local_homeomorph.trans_apply -> LocalHomeomorph.trans_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3) {x : α}, Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (LocalHomeomorph.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : LocalHomeomorph.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (LocalHomeomorph.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e e') x) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (LocalHomeomorph.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) e' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u3} β γ _inst_2 _inst_3) {x : α}, Eq.{succ u3} γ (LocalHomeomorph.toFun'.{u2, u3} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u2, u1, u3} α β γ _inst_1 _inst_2 _inst_3 e e') x) (LocalHomeomorph.toFun'.{u1, u3} β γ _inst_2 _inst_3 e' (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e x))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.trans_apply LocalHomeomorph.trans_applyₓ'. -/
theorem trans_apply {x : α} : (e.trans e') x = e' (e x) :=
  rfl
#align local_homeomorph.trans_apply LocalHomeomorph.trans_apply

/- warning: local_homeomorph.trans_symm_eq_symm_trans_symm -> LocalHomeomorph.trans_symm_eq_symm_trans_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3), Eq.{max (succ u3) (succ u1)} (LocalHomeomorph.{u3, u1} γ α _inst_3 _inst_1) (LocalHomeomorph.symm.{u1, u3} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e e')) (LocalHomeomorph.trans.{u3, u2, u1} γ β α _inst_3 _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u3} β γ _inst_2 _inst_3 e') (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u2} γ] (e : LocalHomeomorph.{u3, u1} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u2} β γ _inst_2 _inst_3), Eq.{max (succ u3) (succ u2)} (LocalHomeomorph.{u2, u3} γ α _inst_3 _inst_1) (LocalHomeomorph.symm.{u3, u2} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u3, u1, u2} α β γ _inst_1 _inst_2 _inst_3 e e')) (LocalHomeomorph.trans.{u2, u1, u3} γ β α _inst_3 _inst_2 _inst_1 (LocalHomeomorph.symm.{u1, u2} β γ _inst_2 _inst_3 e') (LocalHomeomorph.symm.{u3, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.trans_symm_eq_symm_trans_symm LocalHomeomorph.trans_symm_eq_symm_trans_symmₓ'. -/
theorem trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm := by
  cases e <;> cases e' <;> rfl
#align local_homeomorph.trans_symm_eq_symm_trans_symm LocalHomeomorph.trans_symm_eq_symm_trans_symm

/- warning: local_homeomorph.trans_source -> LocalHomeomorph.trans_source is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3), Eq.{succ u1} (Set.{u1} α) (LocalEquiv.source.{u1, u3} α γ (LocalHomeomorph.toLocalEquiv.{u1, u3} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e e'))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (LocalEquiv.source.{u2, u3} β γ (LocalHomeomorph.toLocalEquiv.{u2, u3} β γ _inst_2 _inst_3 e'))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u2} γ] (e : LocalHomeomorph.{u3, u1} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u2} β γ _inst_2 _inst_3), Eq.{succ u3} (Set.{u3} α) (LocalEquiv.source.{u3, u2} α γ (LocalHomeomorph.toLocalEquiv.{u3, u2} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u3, u1, u2} α β γ _inst_1 _inst_2 _inst_3 e e'))) (Inter.inter.{u3} (Set.{u3} α) (Set.instInterSet.{u3} α) (LocalEquiv.source.{u3, u1} α β (LocalHomeomorph.toLocalEquiv.{u3, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u3, u1} α β (LocalHomeomorph.toFun'.{u3, u1} α β _inst_1 _inst_2 e) (LocalEquiv.source.{u1, u2} β γ (LocalHomeomorph.toLocalEquiv.{u1, u2} β γ _inst_2 _inst_3 e'))))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.trans_source LocalHomeomorph.trans_sourceₓ'. -/
/- This could be considered as a simp lemma, but there are many situations where it makes something
simple into something more complicated. -/
theorem trans_source : (e.trans e').source = e.source ∩ e ⁻¹' e'.source :=
  LocalEquiv.trans_source e.toLocalEquiv e'.toLocalEquiv
#align local_homeomorph.trans_source LocalHomeomorph.trans_source

/- warning: local_homeomorph.trans_source' -> LocalHomeomorph.trans_source' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3), Eq.{succ u1} (Set.{u1} α) (LocalEquiv.source.{u1, u3} α γ (LocalHomeomorph.toLocalEquiv.{u1, u3} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e e'))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u2, u3} β γ (LocalHomeomorph.toLocalEquiv.{u2, u3} β γ _inst_2 _inst_3 e')))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u2} γ] (e : LocalHomeomorph.{u3, u1} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u2} β γ _inst_2 _inst_3), Eq.{succ u3} (Set.{u3} α) (LocalEquiv.source.{u3, u2} α γ (LocalHomeomorph.toLocalEquiv.{u3, u2} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u3, u1, u2} α β γ _inst_1 _inst_2 _inst_3 e e'))) (Inter.inter.{u3} (Set.{u3} α) (Set.instInterSet.{u3} α) (LocalEquiv.source.{u3, u1} α β (LocalHomeomorph.toLocalEquiv.{u3, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u3, u1} α β (LocalHomeomorph.toFun'.{u3, u1} α β _inst_1 _inst_2 e) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u3, u1} α β (LocalHomeomorph.toLocalEquiv.{u3, u1} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u1, u2} β γ (LocalHomeomorph.toLocalEquiv.{u1, u2} β γ _inst_2 _inst_3 e')))))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.trans_source' LocalHomeomorph.trans_source'ₓ'. -/
theorem trans_source' : (e.trans e').source = e.source ∩ e ⁻¹' (e.target ∩ e'.source) :=
  LocalEquiv.trans_source' e.toLocalEquiv e'.toLocalEquiv
#align local_homeomorph.trans_source' LocalHomeomorph.trans_source'

/- warning: local_homeomorph.trans_source'' -> LocalHomeomorph.trans_source'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3), Eq.{succ u1} (Set.{u1} α) (LocalEquiv.source.{u1, u3} α γ (LocalHomeomorph.toLocalEquiv.{u1, u3} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e e'))) (Set.image.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u2, u3} β γ (LocalHomeomorph.toLocalEquiv.{u2, u3} β γ _inst_2 _inst_3 e'))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u2} γ] (e : LocalHomeomorph.{u3, u1} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u2} β γ _inst_2 _inst_3), Eq.{succ u3} (Set.{u3} α) (LocalEquiv.source.{u3, u2} α γ (LocalHomeomorph.toLocalEquiv.{u3, u2} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u3, u1, u2} α β γ _inst_1 _inst_2 _inst_3 e e'))) (Set.image.{u1, u3} β α (LocalHomeomorph.toFun'.{u1, u3} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u3, u1} α β _inst_1 _inst_2 e)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u3, u1} α β (LocalHomeomorph.toLocalEquiv.{u3, u1} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u1, u2} β γ (LocalHomeomorph.toLocalEquiv.{u1, u2} β γ _inst_2 _inst_3 e'))))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.trans_source'' LocalHomeomorph.trans_source''ₓ'. -/
theorem trans_source'' : (e.trans e').source = e.symm '' (e.target ∩ e'.source) :=
  LocalEquiv.trans_source'' e.toLocalEquiv e'.toLocalEquiv
#align local_homeomorph.trans_source'' LocalHomeomorph.trans_source''

/- warning: local_homeomorph.image_trans_source -> LocalHomeomorph.image_trans_source is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (LocalEquiv.source.{u1, u3} α γ (LocalHomeomorph.toLocalEquiv.{u1, u3} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e e')))) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u2, u3} β γ (LocalHomeomorph.toLocalEquiv.{u2, u3} β γ _inst_2 _inst_3 e')))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] (e : LocalHomeomorph.{u2, u3} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u3, u1} β γ _inst_2 _inst_3), Eq.{succ u3} (Set.{u3} β) (Set.image.{u2, u3} α β (LocalHomeomorph.toFun'.{u2, u3} α β _inst_1 _inst_2 e) (LocalEquiv.source.{u2, u1} α γ (LocalHomeomorph.toLocalEquiv.{u2, u1} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u2, u3, u1} α β γ _inst_1 _inst_2 _inst_3 e e')))) (Inter.inter.{u3} (Set.{u3} β) (Set.instInterSet.{u3} β) (LocalEquiv.target.{u2, u3} α β (LocalHomeomorph.toLocalEquiv.{u2, u3} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u3, u1} β γ (LocalHomeomorph.toLocalEquiv.{u3, u1} β γ _inst_2 _inst_3 e')))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.image_trans_source LocalHomeomorph.image_trans_sourceₓ'. -/
theorem image_trans_source : e '' (e.trans e').source = e.target ∩ e'.source :=
  LocalEquiv.image_trans_source e.toLocalEquiv e'.toLocalEquiv
#align local_homeomorph.image_trans_source LocalHomeomorph.image_trans_source

/- warning: local_homeomorph.trans_target -> LocalHomeomorph.trans_target is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3), Eq.{succ u3} (Set.{u3} γ) (LocalEquiv.target.{u1, u3} α γ (LocalHomeomorph.toLocalEquiv.{u1, u3} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e e'))) (Inter.inter.{u3} (Set.{u3} γ) (Set.hasInter.{u3} γ) (LocalEquiv.target.{u2, u3} β γ (LocalHomeomorph.toLocalEquiv.{u2, u3} β γ _inst_2 _inst_3 e')) (Set.preimage.{u3, u2} γ β (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (LocalHomeomorph.{u3, u2} γ β _inst_3 _inst_2) (fun (_x : LocalHomeomorph.{u3, u2} γ β _inst_3 _inst_2) => γ -> β) (LocalHomeomorph.hasCoeToFun.{u3, u2} γ β _inst_3 _inst_2) (LocalHomeomorph.symm.{u2, u3} β γ _inst_2 _inst_3 e')) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u3} β γ _inst_2 _inst_3), Eq.{succ u3} (Set.{u3} γ) (LocalEquiv.target.{u2, u3} α γ (LocalHomeomorph.toLocalEquiv.{u2, u3} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u2, u1, u3} α β γ _inst_1 _inst_2 _inst_3 e e'))) (Inter.inter.{u3} (Set.{u3} γ) (Set.instInterSet.{u3} γ) (LocalEquiv.target.{u1, u3} β γ (LocalHomeomorph.toLocalEquiv.{u1, u3} β γ _inst_2 _inst_3 e')) (Set.preimage.{u3, u1} γ β (LocalHomeomorph.toFun'.{u3, u1} γ β _inst_3 _inst_2 (LocalHomeomorph.symm.{u1, u3} β γ _inst_2 _inst_3 e')) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.trans_target LocalHomeomorph.trans_targetₓ'. -/
theorem trans_target : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' e.target :=
  rfl
#align local_homeomorph.trans_target LocalHomeomorph.trans_target

/- warning: local_homeomorph.trans_target' -> LocalHomeomorph.trans_target' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3), Eq.{succ u3} (Set.{u3} γ) (LocalEquiv.target.{u1, u3} α γ (LocalHomeomorph.toLocalEquiv.{u1, u3} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e e'))) (Inter.inter.{u3} (Set.{u3} γ) (Set.hasInter.{u3} γ) (LocalEquiv.target.{u2, u3} β γ (LocalHomeomorph.toLocalEquiv.{u2, u3} β γ _inst_2 _inst_3 e')) (Set.preimage.{u3, u2} γ β (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (LocalHomeomorph.{u3, u2} γ β _inst_3 _inst_2) (fun (_x : LocalHomeomorph.{u3, u2} γ β _inst_3 _inst_2) => γ -> β) (LocalHomeomorph.hasCoeToFun.{u3, u2} γ β _inst_3 _inst_2) (LocalHomeomorph.symm.{u2, u3} β γ _inst_2 _inst_3 e')) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.source.{u2, u3} β γ (LocalHomeomorph.toLocalEquiv.{u2, u3} β γ _inst_2 _inst_3 e')) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u3} β γ _inst_2 _inst_3), Eq.{succ u3} (Set.{u3} γ) (LocalEquiv.target.{u2, u3} α γ (LocalHomeomorph.toLocalEquiv.{u2, u3} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u2, u1, u3} α β γ _inst_1 _inst_2 _inst_3 e e'))) (Inter.inter.{u3} (Set.{u3} γ) (Set.instInterSet.{u3} γ) (LocalEquiv.target.{u1, u3} β γ (LocalHomeomorph.toLocalEquiv.{u1, u3} β γ _inst_2 _inst_3 e')) (Set.preimage.{u3, u1} γ β (LocalHomeomorph.toFun'.{u3, u1} γ β _inst_3 _inst_2 (LocalHomeomorph.symm.{u1, u3} β γ _inst_2 _inst_3 e')) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.source.{u1, u3} β γ (LocalHomeomorph.toLocalEquiv.{u1, u3} β γ _inst_2 _inst_3 e')) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)))))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.trans_target' LocalHomeomorph.trans_target'ₓ'. -/
theorem trans_target' : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' (e'.source ∩ e.target) :=
  trans_source' e'.symm e.symm
#align local_homeomorph.trans_target' LocalHomeomorph.trans_target'

/- warning: local_homeomorph.trans_target'' -> LocalHomeomorph.trans_target'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3), Eq.{succ u3} (Set.{u3} γ) (LocalEquiv.target.{u1, u3} α γ (LocalHomeomorph.toLocalEquiv.{u1, u3} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e e'))) (Set.image.{u2, u3} β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (LocalHomeomorph.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) e') (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.source.{u2, u3} β γ (LocalHomeomorph.toLocalEquiv.{u2, u3} β γ _inst_2 _inst_3 e')) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u3} β γ _inst_2 _inst_3), Eq.{succ u3} (Set.{u3} γ) (LocalEquiv.target.{u2, u3} α γ (LocalHomeomorph.toLocalEquiv.{u2, u3} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u2, u1, u3} α β γ _inst_1 _inst_2 _inst_3 e e'))) (Set.image.{u1, u3} β γ (LocalHomeomorph.toFun'.{u1, u3} β γ _inst_2 _inst_3 e') (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.source.{u1, u3} β γ (LocalHomeomorph.toLocalEquiv.{u1, u3} β γ _inst_2 _inst_3 e')) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.trans_target'' LocalHomeomorph.trans_target''ₓ'. -/
theorem trans_target'' : (e.trans e').target = e' '' (e'.source ∩ e.target) :=
  trans_source'' e'.symm e.symm
#align local_homeomorph.trans_target'' LocalHomeomorph.trans_target''

/- warning: local_homeomorph.inv_image_trans_target -> LocalHomeomorph.inv_image_trans_target is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3), Eq.{succ u2} (Set.{u2} β) (Set.image.{u3, u2} γ β (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (LocalHomeomorph.{u3, u2} γ β _inst_3 _inst_2) (fun (_x : LocalHomeomorph.{u3, u2} γ β _inst_3 _inst_2) => γ -> β) (LocalHomeomorph.hasCoeToFun.{u3, u2} γ β _inst_3 _inst_2) (LocalHomeomorph.symm.{u2, u3} β γ _inst_2 _inst_3 e')) (LocalEquiv.target.{u1, u3} α γ (LocalHomeomorph.toLocalEquiv.{u1, u3} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e e')))) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.source.{u2, u3} β γ (LocalHomeomorph.toLocalEquiv.{u2, u3} β γ _inst_2 _inst_3 e')) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (e : LocalHomeomorph.{u1, u3} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u3, u2} β γ _inst_2 _inst_3), Eq.{succ u3} (Set.{u3} β) (Set.image.{u2, u3} γ β (LocalHomeomorph.toFun'.{u2, u3} γ β _inst_3 _inst_2 (LocalHomeomorph.symm.{u3, u2} β γ _inst_2 _inst_3 e')) (LocalEquiv.target.{u1, u2} α γ (LocalHomeomorph.toLocalEquiv.{u1, u2} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 e e')))) (Inter.inter.{u3} (Set.{u3} β) (Set.instInterSet.{u3} β) (LocalEquiv.source.{u3, u2} β γ (LocalHomeomorph.toLocalEquiv.{u3, u2} β γ _inst_2 _inst_3 e')) (LocalEquiv.target.{u1, u3} α β (LocalHomeomorph.toLocalEquiv.{u1, u3} α β _inst_1 _inst_2 e)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.inv_image_trans_target LocalHomeomorph.inv_image_trans_targetₓ'. -/
theorem inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source ∩ e.target :=
  image_trans_source e'.symm e.symm
#align local_homeomorph.inv_image_trans_target LocalHomeomorph.inv_image_trans_target

/- warning: local_homeomorph.trans_assoc -> LocalHomeomorph.trans_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3) (e'' : LocalHomeomorph.{u3, u4} γ δ _inst_3 _inst_4), Eq.{max (succ u1) (succ u4)} (LocalHomeomorph.{u1, u4} α δ _inst_1 _inst_4) (LocalHomeomorph.trans.{u1, u3, u4} α γ δ _inst_1 _inst_3 _inst_4 (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e e') e'') (LocalHomeomorph.trans.{u1, u2, u4} α β δ _inst_1 _inst_2 _inst_4 e (LocalHomeomorph.trans.{u2, u3, u4} β γ δ _inst_2 _inst_3 _inst_4 e' e''))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u4}} {δ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u4} γ] [_inst_4 : TopologicalSpace.{u3} δ] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u4} β γ _inst_2 _inst_3) (e'' : LocalHomeomorph.{u4, u3} γ δ _inst_3 _inst_4), Eq.{max (succ u2) (succ u3)} (LocalHomeomorph.{u2, u3} α δ _inst_1 _inst_4) (LocalHomeomorph.trans.{u2, u4, u3} α γ δ _inst_1 _inst_3 _inst_4 (LocalHomeomorph.trans.{u2, u1, u4} α β γ _inst_1 _inst_2 _inst_3 e e') e'') (LocalHomeomorph.trans.{u2, u1, u3} α β δ _inst_1 _inst_2 _inst_4 e (LocalHomeomorph.trans.{u1, u4, u3} β γ δ _inst_2 _inst_3 _inst_4 e' e''))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.trans_assoc LocalHomeomorph.trans_assocₓ'. -/
theorem trans_assoc (e'' : LocalHomeomorph γ δ) : (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  eq_of_localEquiv_eq <| LocalEquiv.trans_assoc e.toLocalEquiv e'.toLocalEquiv e''.toLocalEquiv
#align local_homeomorph.trans_assoc LocalHomeomorph.trans_assoc

/- warning: local_homeomorph.trans_refl -> LocalHomeomorph.trans_refl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.trans.{u1, u2, u2} α β β _inst_1 _inst_2 _inst_2 e (LocalHomeomorph.refl.{u2} β _inst_2)) e
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalHomeomorph.trans.{u2, u1, u1} α β β _inst_1 _inst_2 _inst_2 e (LocalHomeomorph.refl.{u1} β _inst_2)) e
Case conversion may be inaccurate. Consider using '#align local_homeomorph.trans_refl LocalHomeomorph.trans_reflₓ'. -/
@[simp, mfld_simps]
theorem trans_refl : e.trans (LocalHomeomorph.refl β) = e :=
  eq_of_localEquiv_eq <| LocalEquiv.trans_refl e.toLocalEquiv
#align local_homeomorph.trans_refl LocalHomeomorph.trans_refl

/- warning: local_homeomorph.refl_trans -> LocalHomeomorph.refl_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.trans.{u1, u1, u2} α α β _inst_1 _inst_1 _inst_2 (LocalHomeomorph.refl.{u1} α _inst_1) e) e
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalHomeomorph.trans.{u2, u2, u1} α α β _inst_1 _inst_1 _inst_2 (LocalHomeomorph.refl.{u2} α _inst_1) e) e
Case conversion may be inaccurate. Consider using '#align local_homeomorph.refl_trans LocalHomeomorph.refl_transₓ'. -/
@[simp, mfld_simps]
theorem refl_trans : (LocalHomeomorph.refl α).trans e = e :=
  eq_of_localEquiv_eq <| LocalEquiv.refl_trans e.toLocalEquiv
#align local_homeomorph.refl_trans LocalHomeomorph.refl_trans

#print LocalHomeomorph.trans_ofSet /-
theorem trans_ofSet {s : Set β} (hs : IsOpen s) : e.trans (ofSet s hs) = e.restr (e ⁻¹' s) :=
  (LocalHomeomorph.ext _ _ (fun x => rfl) fun x => rfl) <| by
    simp [LocalEquiv.trans_source, (e.preimage_interior _).symm, hs.interior_eq]
#align local_homeomorph.trans_of_set LocalHomeomorph.trans_ofSet
-/

/- warning: local_homeomorph.trans_of_set' -> LocalHomeomorph.trans_of_set' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {s : Set.{u2} β} (hs : IsOpen.{u2} β _inst_2 s), Eq.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.trans.{u1, u2, u2} α β β _inst_1 _inst_2 _inst_2 e (LocalHomeomorph.ofSet.{u2} β _inst_2 s hs)) (LocalHomeomorph.restr.{u1, u2} α β _inst_1 _inst_2 e (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {s : Set.{u2} β} (hs : IsOpen.{u2} β _inst_2 s), Eq.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.trans.{u1, u2, u2} α β β _inst_1 _inst_2 _inst_2 e (LocalHomeomorph.ofSet.{u2} β _inst_2 s hs)) (LocalHomeomorph.restr.{u1, u2} α β _inst_1 _inst_2 e (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (LocalHomeomorph.toFun'.{u1, u2} α β _inst_1 _inst_2 e) s)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.trans_of_set' LocalHomeomorph.trans_of_set'ₓ'. -/
theorem trans_of_set' {s : Set β} (hs : IsOpen s) :
    e.trans (ofSet s hs) = e.restr (e.source ∩ e ⁻¹' s) := by rw [trans_of_set, restr_source_inter]
#align local_homeomorph.trans_of_set' LocalHomeomorph.trans_of_set'

/- warning: local_homeomorph.of_set_trans -> LocalHomeomorph.ofSet_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {s : Set.{u1} α} (hs : IsOpen.{u1} α _inst_1 s), Eq.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.trans.{u1, u1, u2} α α β _inst_1 _inst_1 _inst_2 (LocalHomeomorph.ofSet.{u1} α _inst_1 s hs) e) (LocalHomeomorph.restr.{u1, u2} α β _inst_1 _inst_2 e s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {s : Set.{u2} α} (hs : IsOpen.{u2} α _inst_1 s), Eq.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalHomeomorph.trans.{u2, u2, u1} α α β _inst_1 _inst_1 _inst_2 (LocalHomeomorph.ofSet.{u2} α _inst_1 s hs) e) (LocalHomeomorph.restr.{u2, u1} α β _inst_1 _inst_2 e s)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.of_set_trans LocalHomeomorph.ofSet_transₓ'. -/
theorem ofSet_trans {s : Set α} (hs : IsOpen s) : (ofSet s hs).trans e = e.restr s :=
  (LocalHomeomorph.ext _ _ (fun x => rfl) fun x => rfl) <| by
    simp [LocalEquiv.trans_source, hs.interior_eq, inter_comm]
#align local_homeomorph.of_set_trans LocalHomeomorph.ofSet_trans

/- warning: local_homeomorph.of_set_trans' -> LocalHomeomorph.ofSet_trans' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {s : Set.{u1} α} (hs : IsOpen.{u1} α _inst_1 s), Eq.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.trans.{u1, u1, u2} α α β _inst_1 _inst_1 _inst_2 (LocalHomeomorph.ofSet.{u1} α _inst_1 s hs) e) (LocalHomeomorph.restr.{u1, u2} α β _inst_1 _inst_2 e (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {s : Set.{u2} α} (hs : IsOpen.{u2} α _inst_1 s), Eq.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalHomeomorph.trans.{u2, u2, u1} α α β _inst_1 _inst_1 _inst_2 (LocalHomeomorph.ofSet.{u2} α _inst_1 s hs) e) (LocalHomeomorph.restr.{u2, u1} α β _inst_1 _inst_2 e (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) s))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.of_set_trans' LocalHomeomorph.ofSet_trans'ₓ'. -/
theorem ofSet_trans' {s : Set α} (hs : IsOpen s) : (ofSet s hs).trans e = e.restr (e.source ∩ s) :=
  by rw [of_set_trans, restr_source_inter]
#align local_homeomorph.of_set_trans' LocalHomeomorph.ofSet_trans'

/- warning: local_homeomorph.of_set_trans_of_set -> LocalHomeomorph.ofSet_trans_ofSet is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} (hs : IsOpen.{u1} α _inst_1 s) {s' : Set.{u1} α} (hs' : IsOpen.{u1} α _inst_1 s'), Eq.{succ u1} (LocalHomeomorph.{u1, u1} α α _inst_1 _inst_1) (LocalHomeomorph.trans.{u1, u1, u1} α α α _inst_1 _inst_1 _inst_1 (LocalHomeomorph.ofSet.{u1} α _inst_1 s hs) (LocalHomeomorph.ofSet.{u1} α _inst_1 s' hs')) (LocalHomeomorph.ofSet.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s s') (IsOpen.inter.{u1} α s s' _inst_1 hs hs'))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} (hs : IsOpen.{u1} α _inst_1 s) {s' : Set.{u1} α} (hs' : IsOpen.{u1} α _inst_1 s'), Eq.{succ u1} (LocalHomeomorph.{u1, u1} α α _inst_1 _inst_1) (LocalHomeomorph.trans.{u1, u1, u1} α α α _inst_1 _inst_1 _inst_1 (LocalHomeomorph.ofSet.{u1} α _inst_1 s hs) (LocalHomeomorph.ofSet.{u1} α _inst_1 s' hs')) (LocalHomeomorph.ofSet.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s s') (IsOpen.inter.{u1} α s s' _inst_1 hs hs'))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.of_set_trans_of_set LocalHomeomorph.ofSet_trans_ofSetₓ'. -/
@[simp, mfld_simps]
theorem ofSet_trans_ofSet {s : Set α} (hs : IsOpen s) {s' : Set α} (hs' : IsOpen s') :
    (ofSet s hs).trans (ofSet s' hs') = ofSet (s ∩ s') (IsOpen.inter hs hs') :=
  by
  rw [(of_set s hs).trans_ofSet hs']
  ext <;> simp [hs'.interior_eq]
#align local_homeomorph.of_set_trans_of_set LocalHomeomorph.ofSet_trans_ofSet

/- warning: local_homeomorph.restr_trans -> LocalHomeomorph.restr_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3) (s : Set.{u1} α), Eq.{max (succ u1) (succ u3)} (LocalHomeomorph.{u1, u3} α γ _inst_1 _inst_3) (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (LocalHomeomorph.restr.{u1, u2} α β _inst_1 _inst_2 e s) e') (LocalHomeomorph.restr.{u1, u3} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e e') s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u2} γ] (e : LocalHomeomorph.{u3, u1} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u2} β γ _inst_2 _inst_3) (s : Set.{u3} α), Eq.{max (succ u3) (succ u2)} (LocalHomeomorph.{u3, u2} α γ _inst_1 _inst_3) (LocalHomeomorph.trans.{u3, u1, u2} α β γ _inst_1 _inst_2 _inst_3 (LocalHomeomorph.restr.{u3, u1} α β _inst_1 _inst_2 e s) e') (LocalHomeomorph.restr.{u3, u2} α γ _inst_1 _inst_3 (LocalHomeomorph.trans.{u3, u1, u2} α β γ _inst_1 _inst_2 _inst_3 e e') s)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.restr_trans LocalHomeomorph.restr_transₓ'. -/
theorem restr_trans (s : Set α) : (e.restr s).trans e' = (e.trans e').restr s :=
  eq_of_localEquiv_eq <| LocalEquiv.restr_trans e.toLocalEquiv e'.toLocalEquiv (interior s)
#align local_homeomorph.restr_trans LocalHomeomorph.restr_trans

#print LocalHomeomorph.transHomeomorph /-
/-- Postcompose a local homeomorphism with an homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps (config := { fullyApplied := false })]
def transHomeomorph (e' : β ≃ₜ γ) : LocalHomeomorph α γ
    where
  toLocalEquiv := e.toLocalEquiv.transEquiv e'.toEquiv
  open_source := e.open_source
  open_target := e.open_target.Preimage e'.symm.Continuous
  continuous_toFun := e'.Continuous.comp_continuousOn e.ContinuousOn
  continuous_invFun := e.symm.ContinuousOn.comp e'.symm.Continuous.ContinuousOn fun x h => h
#align local_homeomorph.trans_homeomorph LocalHomeomorph.transHomeomorph
-/

/- warning: local_homeomorph.trans_equiv_eq_trans -> LocalHomeomorph.trans_equiv_eq_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : Homeomorph.{u2, u3} β γ _inst_2 _inst_3), Eq.{max (succ u1) (succ u3)} (LocalHomeomorph.{u1, u3} α γ _inst_1 _inst_3) (LocalHomeomorph.transHomeomorph.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e e') (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e (Homeomorph.toLocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3 e'))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (e : LocalHomeomorph.{u1, u3} α β _inst_1 _inst_2) (e' : Homeomorph.{u3, u2} β γ _inst_2 _inst_3), Eq.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α γ _inst_1 _inst_3) (LocalHomeomorph.transHomeomorph.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 e e') (LocalHomeomorph.trans.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 e (Homeomorph.toLocalHomeomorph.{u3, u2} β γ _inst_2 _inst_3 e'))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.trans_equiv_eq_trans LocalHomeomorph.trans_equiv_eq_transₓ'. -/
theorem trans_equiv_eq_trans (e' : β ≃ₜ γ) : e.transHomeomorph e' = e.trans e'.toLocalHomeomorph :=
  toLocalEquiv_injective <| LocalEquiv.transEquiv_eq_trans _ _
#align local_homeomorph.trans_equiv_eq_trans LocalHomeomorph.trans_equiv_eq_trans

#print Homeomorph.transLocalHomeomorph /-
/-- Precompose a local homeomorphism with an homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps (config := { fullyApplied := false })]
def Homeomorph.transLocalHomeomorph (e : α ≃ₜ β) : LocalHomeomorph α γ
    where
  toLocalEquiv := e.toEquiv.transLocalEquiv e'.toLocalEquiv
  open_source := e'.open_source.Preimage e.Continuous
  open_target := e'.open_target
  continuous_toFun := e'.ContinuousOn.comp e.Continuous.ContinuousOn fun x h => h
  continuous_invFun := e.symm.Continuous.comp_continuousOn e'.symm.ContinuousOn
#align homeomorph.trans_local_homeomorph Homeomorph.transLocalHomeomorph
-/

/- warning: homeomorph.trans_local_homeomorph_eq_trans -> Homeomorph.transLocalHomeomorph_eq_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e' : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3) (e : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (LocalHomeomorph.{u1, u3} α γ _inst_1 _inst_3) (Homeomorph.transLocalHomeomorph.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e' e) (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (Homeomorph.toLocalHomeomorph.{u1, u2} α β _inst_1 _inst_2 e) e')
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] (e' : LocalHomeomorph.{u2, u1} β γ _inst_2 _inst_3) (e : Homeomorph.{u3, u2} α β _inst_1 _inst_2), Eq.{max (succ u3) (succ u1)} (LocalHomeomorph.{u3, u1} α γ _inst_1 _inst_3) (Homeomorph.transLocalHomeomorph.{u3, u2, u1} α β γ _inst_1 _inst_2 _inst_3 e' e) (LocalHomeomorph.trans.{u3, u2, u1} α β γ _inst_1 _inst_2 _inst_3 (Homeomorph.toLocalHomeomorph.{u3, u2} α β _inst_1 _inst_2 e) e')
Case conversion may be inaccurate. Consider using '#align homeomorph.trans_local_homeomorph_eq_trans Homeomorph.transLocalHomeomorph_eq_transₓ'. -/
theorem Homeomorph.transLocalHomeomorph_eq_trans (e : α ≃ₜ β) :
    e.transLocalHomeomorph e' = e.toLocalHomeomorph.trans e' :=
  toLocalEquiv_injective <| Equiv.transLocalEquiv_eq_trans _ _
#align homeomorph.trans_local_homeomorph_eq_trans Homeomorph.transLocalHomeomorph_eq_trans

#print LocalHomeomorph.EqOnSource /-
/-- `eq_on_source e e'` means that `e` and `e'` have the same source, and coincide there. They
should really be considered the same local equiv. -/
def EqOnSource (e e' : LocalHomeomorph α β) : Prop :=
  e.source = e'.source ∧ EqOn e e' e.source
#align local_homeomorph.eq_on_source LocalHomeomorph.EqOnSource
-/

/- warning: local_homeomorph.eq_on_source_iff -> LocalHomeomorph.eqOnSource_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), Iff (LocalHomeomorph.EqOnSource.{u1, u2} α β _inst_1 _inst_2 e e') (LocalEquiv.EqOnSource.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e) (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), Iff (LocalHomeomorph.EqOnSource.{u2, u1} α β _inst_1 _inst_2 e e') (LocalEquiv.EqOnSource.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e) (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e'))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eq_on_source_iff LocalHomeomorph.eqOnSource_iffₓ'. -/
theorem eqOnSource_iff (e e' : LocalHomeomorph α β) :
    EqOnSource e e' ↔ LocalEquiv.EqOnSource e.toLocalEquiv e'.toLocalEquiv :=
  Iff.rfl
#align local_homeomorph.eq_on_source_iff LocalHomeomorph.eqOnSource_iff

/-- `eq_on_source` is an equivalence relation -/
instance : Setoid (LocalHomeomorph α β)
    where
  R := EqOnSource
  iseqv :=
    ⟨fun e => (@LocalEquiv.eqOnSourceSetoid α β).iseqv.1 e.toLocalEquiv, fun e e' h =>
      (@LocalEquiv.eqOnSourceSetoid α β).iseqv.2.1 ((eqOnSource_iff e e').1 h), fun e e' e'' h h' =>
      (@LocalEquiv.eqOnSourceSetoid α β).iseqv.2.2 ((eqOnSource_iff e e').1 h)
        ((eqOnSource_iff e' e'').1 h')⟩

/- warning: local_homeomorph.eq_on_source_refl -> LocalHomeomorph.eqOnSource_refl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.setoid.{u1, u2} α β _inst_1 _inst_2)) e e
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (instHasEquiv.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalHomeomorph.eqOnSourceSetoid.{u2, u1} α β _inst_1 _inst_2)) e e
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eq_on_source_refl LocalHomeomorph.eqOnSource_reflₓ'. -/
theorem eqOnSource_refl : e ≈ e :=
  Setoid.refl _
#align local_homeomorph.eq_on_source_refl LocalHomeomorph.eqOnSource_refl

/- warning: local_homeomorph.eq_on_source.symm' -> LocalHomeomorph.EqOnSource.symm' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2}, (HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.setoid.{u1, u2} α β _inst_1 _inst_2)) e e') -> (HasEquivₓ.Equiv.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (setoidHasEquiv.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.setoid.{u2, u1} β α _inst_2 _inst_1)) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2}, (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (instHasEquiv.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalHomeomorph.eqOnSourceSetoid.{u2, u1} α β _inst_1 _inst_2)) e e') -> (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalHomeomorph.{u1, u2} β α _inst_2 _inst_1) (instHasEquiv.{max (succ u2) (succ u1)} (LocalHomeomorph.{u1, u2} β α _inst_2 _inst_1) (LocalHomeomorph.eqOnSourceSetoid.{u1, u2} β α _inst_2 _inst_1)) (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e) (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e'))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eq_on_source.symm' LocalHomeomorph.EqOnSource.symm'ₓ'. -/
/-- If two local homeomorphisms are equivalent, so are their inverses -/
theorem EqOnSource.symm' {e e' : LocalHomeomorph α β} (h : e ≈ e') : e.symm ≈ e'.symm :=
  LocalEquiv.EqOnSource.symm' h
#align local_homeomorph.eq_on_source.symm' LocalHomeomorph.EqOnSource.symm'

/- warning: local_homeomorph.eq_on_source.source_eq -> LocalHomeomorph.EqOnSource.source_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2}, (HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.setoid.{u1, u2} α β _inst_1 _inst_2)) e e') -> (Eq.{succ u1} (Set.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e')))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2}, (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (instHasEquiv.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalHomeomorph.eqOnSourceSetoid.{u2, u1} α β _inst_1 _inst_2)) e e') -> (Eq.{succ u2} (Set.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e')))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eq_on_source.source_eq LocalHomeomorph.EqOnSource.source_eqₓ'. -/
/-- Two equivalent local homeomorphisms have the same source -/
theorem EqOnSource.source_eq {e e' : LocalHomeomorph α β} (h : e ≈ e') : e.source = e'.source :=
  h.1
#align local_homeomorph.eq_on_source.source_eq LocalHomeomorph.EqOnSource.source_eq

/- warning: local_homeomorph.eq_on_source.target_eq -> LocalHomeomorph.EqOnSource.target_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2}, (HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.setoid.{u1, u2} α β _inst_1 _inst_2)) e e') -> (Eq.{succ u2} (Set.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e')))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2}, (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (instHasEquiv.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalHomeomorph.eqOnSourceSetoid.{u2, u1} α β _inst_1 _inst_2)) e e') -> (Eq.{succ u1} (Set.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e')))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eq_on_source.target_eq LocalHomeomorph.EqOnSource.target_eqₓ'. -/
/-- Two equivalent local homeomorphisms have the same target -/
theorem EqOnSource.target_eq {e e' : LocalHomeomorph α β} (h : e ≈ e') : e.target = e'.target :=
  h.symm'.1
#align local_homeomorph.eq_on_source.target_eq LocalHomeomorph.EqOnSource.target_eq

/- warning: local_homeomorph.eq_on_source.eq_on -> LocalHomeomorph.EqOnSource.eqOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2}, (HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.setoid.{u1, u2} α β _inst_1 _inst_2)) e e') -> (Set.EqOn.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e') (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2}, (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (instHasEquiv.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalHomeomorph.eqOnSourceSetoid.{u2, u1} α β _inst_1 _inst_2)) e e') -> (Set.EqOn.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e') (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eq_on_source.eq_on LocalHomeomorph.EqOnSource.eqOnₓ'. -/
/-- Two equivalent local homeomorphisms have coinciding `to_fun` on the source -/
theorem EqOnSource.eqOn {e e' : LocalHomeomorph α β} (h : e ≈ e') : EqOn e e' e.source :=
  h.2
#align local_homeomorph.eq_on_source.eq_on LocalHomeomorph.EqOnSource.eqOn

/- warning: local_homeomorph.eq_on_source.symm_eq_on_target -> LocalHomeomorph.EqOnSource.symm_eqOn_target is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2}, (HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.setoid.{u1, u2} α β _inst_1 _inst_2)) e e') -> (Set.EqOn.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e')) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2}, (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (instHasEquiv.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalHomeomorph.eqOnSourceSetoid.{u2, u1} α β _inst_1 _inst_2)) e e') -> (Set.EqOn.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e')) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eq_on_source.symm_eq_on_target LocalHomeomorph.EqOnSource.symm_eqOn_targetₓ'. -/
/-- Two equivalent local homeomorphisms have coinciding `inv_fun` on the target -/
theorem EqOnSource.symm_eqOn_target {e e' : LocalHomeomorph α β} (h : e ≈ e') :
    EqOn e.symm e'.symm e.target :=
  h.symm'.2
#align local_homeomorph.eq_on_source.symm_eq_on_target LocalHomeomorph.EqOnSource.symm_eqOn_target

/- warning: local_homeomorph.eq_on_source.trans' -> LocalHomeomorph.EqOnSource.trans' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {f : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3} {f' : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3}, (HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.setoid.{u1, u2} α β _inst_1 _inst_2)) e e') -> (HasEquivₓ.Equiv.{max (succ u2) (succ u3)} (LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3) (setoidHasEquiv.{max (succ u2) (succ u3)} (LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3) (LocalHomeomorph.setoid.{u2, u3} β γ _inst_2 _inst_3)) f f') -> (HasEquivₓ.Equiv.{max (succ u1) (succ u3)} (LocalHomeomorph.{u1, u3} α γ _inst_1 _inst_3) (setoidHasEquiv.{max (succ u1) (succ u3)} (LocalHomeomorph.{u1, u3} α γ _inst_1 _inst_3) (LocalHomeomorph.setoid.{u1, u3} α γ _inst_1 _inst_3)) (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e f) (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e' f'))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] {e : LocalHomeomorph.{u3, u2} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u3, u2} α β _inst_1 _inst_2} {f : LocalHomeomorph.{u2, u1} β γ _inst_2 _inst_3} {f' : LocalHomeomorph.{u2, u1} β γ _inst_2 _inst_3}, (HasEquiv.Equiv.{max (succ u3) (succ u2), 0} (LocalHomeomorph.{u3, u2} α β _inst_1 _inst_2) (instHasEquiv.{max (succ u3) (succ u2)} (LocalHomeomorph.{u3, u2} α β _inst_1 _inst_2) (LocalHomeomorph.eqOnSourceSetoid.{u3, u2} α β _inst_1 _inst_2)) e e') -> (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalHomeomorph.{u2, u1} β γ _inst_2 _inst_3) (instHasEquiv.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β γ _inst_2 _inst_3) (LocalHomeomorph.eqOnSourceSetoid.{u2, u1} β γ _inst_2 _inst_3)) f f') -> (HasEquiv.Equiv.{max (succ u3) (succ u1), 0} (LocalHomeomorph.{u3, u1} α γ _inst_1 _inst_3) (instHasEquiv.{max (succ u3) (succ u1)} (LocalHomeomorph.{u3, u1} α γ _inst_1 _inst_3) (LocalHomeomorph.eqOnSourceSetoid.{u3, u1} α γ _inst_1 _inst_3)) (LocalHomeomorph.trans.{u3, u2, u1} α β γ _inst_1 _inst_2 _inst_3 e f) (LocalHomeomorph.trans.{u3, u2, u1} α β γ _inst_1 _inst_2 _inst_3 e' f'))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eq_on_source.trans' LocalHomeomorph.EqOnSource.trans'ₓ'. -/
/-- Composition of local homeomorphisms respects equivalence -/
theorem EqOnSource.trans' {e e' : LocalHomeomorph α β} {f f' : LocalHomeomorph β γ} (he : e ≈ e')
    (hf : f ≈ f') : e.trans f ≈ e'.trans f' :=
  LocalEquiv.EqOnSource.trans' he hf
#align local_homeomorph.eq_on_source.trans' LocalHomeomorph.EqOnSource.trans'

/- warning: local_homeomorph.eq_on_source.restr -> LocalHomeomorph.EqOnSource.restr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2}, (HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.setoid.{u1, u2} α β _inst_1 _inst_2)) e e') -> (forall (s : Set.{u1} α), HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.setoid.{u1, u2} α β _inst_1 _inst_2)) (LocalHomeomorph.restr.{u1, u2} α β _inst_1 _inst_2 e s) (LocalHomeomorph.restr.{u1, u2} α β _inst_1 _inst_2 e' s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2}, (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (instHasEquiv.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalHomeomorph.eqOnSourceSetoid.{u2, u1} α β _inst_1 _inst_2)) e e') -> (forall (s : Set.{u2} α), HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (instHasEquiv.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalHomeomorph.eqOnSourceSetoid.{u2, u1} α β _inst_1 _inst_2)) (LocalHomeomorph.restr.{u2, u1} α β _inst_1 _inst_2 e s) (LocalHomeomorph.restr.{u2, u1} α β _inst_1 _inst_2 e' s))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eq_on_source.restr LocalHomeomorph.EqOnSource.restrₓ'. -/
/-- Restriction of local homeomorphisms respects equivalence -/
theorem EqOnSource.restr {e e' : LocalHomeomorph α β} (he : e ≈ e') (s : Set α) :
    e.restr s ≈ e'.restr s :=
  LocalEquiv.EqOnSource.restr he _
#align local_homeomorph.eq_on_source.restr LocalHomeomorph.EqOnSource.restr

/- warning: local_homeomorph.set.eq_on.restr_eq_on_source -> LocalHomeomorph.Set.EqOn.restr_eqOn_source is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2}, (Set.EqOn.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e') (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e')))) -> (HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.setoid.{u1, u2} α β _inst_1 _inst_2)) (LocalHomeomorph.restr.{u1, u2} α β _inst_1 _inst_2 e (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e'))) (LocalHomeomorph.restr.{u1, u2} α β _inst_1 _inst_2 e' (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2}, (Set.EqOn.{u2, u1} α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e') (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e')))) -> (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (instHasEquiv.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalHomeomorph.eqOnSourceSetoid.{u2, u1} α β _inst_1 _inst_2)) (LocalHomeomorph.restr.{u2, u1} α β _inst_1 _inst_2 e (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e'))) (LocalHomeomorph.restr.{u2, u1} α β _inst_1 _inst_2 e' (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.set.eq_on.restr_eq_on_source LocalHomeomorph.Set.EqOn.restr_eqOn_sourceₓ'. -/
theorem Set.EqOn.restr_eqOn_source {e e' : LocalHomeomorph α β}
    (h : EqOn e e' (e.source ∩ e'.source)) : e.restr e'.source ≈ e'.restr e.source :=
  by
  constructor
  · rw [e'.restr_source' _ e.open_source]
    rw [e.restr_source' _ e'.open_source]
    exact Set.inter_comm _ _
  · rw [e.restr_source' _ e'.open_source]
    refine' (eq_on.trans _ h).trans _ <;> simp only [mfld_simps]
#align local_homeomorph.set.eq_on.restr_eq_on_source LocalHomeomorph.Set.EqOn.restr_eqOn_source

/- warning: local_homeomorph.trans_self_symm -> LocalHomeomorph.trans_self_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), HasEquivₓ.Equiv.{succ u1} (LocalHomeomorph.{u1, u1} α α _inst_1 _inst_1) (setoidHasEquiv.{succ u1} (LocalHomeomorph.{u1, u1} α α _inst_1 _inst_1) (LocalHomeomorph.setoid.{u1, u1} α α _inst_1 _inst_1)) (LocalHomeomorph.trans.{u1, u2, u1} α β α _inst_1 _inst_2 _inst_1 e (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (LocalHomeomorph.ofSet.{u1} α _inst_1 (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalHomeomorph.open_source.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), HasEquiv.Equiv.{succ u2, 0} (LocalHomeomorph.{u2, u2} α α _inst_1 _inst_1) (instHasEquiv.{succ u2} (LocalHomeomorph.{u2, u2} α α _inst_1 _inst_1) (LocalHomeomorph.eqOnSourceSetoid.{u2, u2} α α _inst_1 _inst_1)) (LocalHomeomorph.trans.{u2, u1, u2} α β α _inst_1 _inst_2 _inst_1 e (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) (LocalHomeomorph.ofSet.{u2} α _inst_1 (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (LocalHomeomorph.open_source.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.trans_self_symm LocalHomeomorph.trans_self_symmₓ'. -/
/-- Composition of a local homeomorphism and its inverse is equivalent to the restriction of the
identity to the source -/
theorem trans_self_symm : e.trans e.symm ≈ LocalHomeomorph.ofSet e.source e.open_source :=
  LocalEquiv.trans_self_symm _
#align local_homeomorph.trans_self_symm LocalHomeomorph.trans_self_symm

/- warning: local_homeomorph.trans_symm_self -> LocalHomeomorph.trans_symm_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), HasEquivₓ.Equiv.{succ u2} (LocalHomeomorph.{u2, u2} β β _inst_2 _inst_2) (setoidHasEquiv.{succ u2} (LocalHomeomorph.{u2, u2} β β _inst_2 _inst_2) (LocalHomeomorph.setoid.{u2, u2} β β _inst_2 _inst_2)) (LocalHomeomorph.trans.{u2, u1, u2} β α β _inst_2 _inst_1 _inst_2 (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) e) (LocalHomeomorph.ofSet.{u2} β _inst_2 (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalHomeomorph.open_target.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), HasEquiv.Equiv.{succ u2, 0} (LocalHomeomorph.{u2, u2} β β _inst_2 _inst_2) (instHasEquiv.{succ u2} (LocalHomeomorph.{u2, u2} β β _inst_2 _inst_2) (LocalHomeomorph.eqOnSourceSetoid.{u2, u2} β β _inst_2 _inst_2)) (LocalHomeomorph.trans.{u2, u1, u2} β α β _inst_2 _inst_1 _inst_2 (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) e) (LocalHomeomorph.ofSet.{u2} β _inst_2 (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalHomeomorph.open_target.{u1, u2} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.trans_symm_self LocalHomeomorph.trans_symm_selfₓ'. -/
theorem trans_symm_self : e.symm.trans e ≈ LocalHomeomorph.ofSet e.target e.open_target :=
  e.symm.trans_self_symm
#align local_homeomorph.trans_symm_self LocalHomeomorph.trans_symm_self

/- warning: local_homeomorph.eq_of_eq_on_source_univ -> LocalHomeomorph.eq_of_eq_on_source_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2}, (HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (LocalHomeomorph.setoid.{u1, u2} α β _inst_1 _inst_2)) e e') -> (Eq.{succ u1} (Set.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.univ.{u1} α)) -> (Eq.{succ u2} (Set.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.univ.{u2} β)) -> (Eq.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) e e')
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2} {e' : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2}, (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (instHasEquiv.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (LocalHomeomorph.eqOnSourceSetoid.{u2, u1} α β _inst_1 _inst_2)) e e') -> (Eq.{succ u2} (Set.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.univ.{u2} α)) -> (Eq.{succ u1} (Set.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.univ.{u1} β)) -> (Eq.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) e e')
Case conversion may be inaccurate. Consider using '#align local_homeomorph.eq_of_eq_on_source_univ LocalHomeomorph.eq_of_eq_on_source_univₓ'. -/
theorem eq_of_eq_on_source_univ {e e' : LocalHomeomorph α β} (h : e ≈ e') (s : e.source = univ)
    (t : e.target = univ) : e = e' :=
  eq_of_localEquiv_eq <| LocalEquiv.eq_of_eq_on_source_univ _ _ h s t
#align local_homeomorph.eq_of_eq_on_source_univ LocalHomeomorph.eq_of_eq_on_source_univ

section Prod

/- warning: local_homeomorph.prod -> LocalHomeomorph.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ], (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) -> (LocalHomeomorph.{u3, u4} γ δ _inst_3 _inst_4) -> (LocalHomeomorph.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ], (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) -> (LocalHomeomorph.{u3, u4} γ δ _inst_3 _inst_4) -> (LocalHomeomorph.{max u3 u1, max u4 u2} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (instTopologicalSpaceProd.{u1, u3} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u2, u4} β δ _inst_2 _inst_4))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.prod LocalHomeomorph.prodₓ'. -/
/-- The product of two local homeomorphisms, as a local homeomorphism on the product space. -/
@[simps (config := mfld_cfg) toLocalEquiv apply,
  simps (config := { attrs := [] }) source target symm_apply]
def prod (e : LocalHomeomorph α β) (e' : LocalHomeomorph γ δ) : LocalHomeomorph (α × γ) (β × δ)
    where
  open_source := e.open_source.Prod e'.open_source
  open_target := e.open_target.Prod e'.open_target
  continuous_toFun := e.ContinuousOn.Prod_map e'.ContinuousOn
  continuous_invFun := e.continuousOn_symm.Prod_map e'.continuousOn_symm
  toLocalEquiv := e.toLocalEquiv.Prod e'.toLocalEquiv
#align local_homeomorph.prod LocalHomeomorph.prod

/- warning: local_homeomorph.prod_symm -> LocalHomeomorph.prod_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u3, u4} γ δ _inst_3 _inst_4), Eq.{max (succ (max u2 u4)) (succ (max u1 u3))} (LocalHomeomorph.{max u2 u4, max u1 u3} (Prod.{u2, u4} β δ) (Prod.{u1, u3} α γ) (Prod.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3)) (LocalHomeomorph.symm.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4) (LocalHomeomorph.prod.{u1, u2, u3, u4} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 e e')) (LocalHomeomorph.prod.{u2, u1, u4, u3} β α δ γ _inst_2 _inst_1 _inst_4 _inst_3 (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) (LocalHomeomorph.symm.{u3, u4} γ δ _inst_3 _inst_4 e'))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u4} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.{u1} δ] (e : LocalHomeomorph.{u4, u3} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u2, u1} γ δ _inst_3 _inst_4), Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (LocalHomeomorph.{max u3 u1, max u4 u2} (Prod.{u3, u1} β δ) (Prod.{u4, u2} α γ) (instTopologicalSpaceProd.{u3, u1} β δ _inst_2 _inst_4) (instTopologicalSpaceProd.{u4, u2} α γ _inst_1 _inst_3)) (LocalHomeomorph.symm.{max u4 u2, max u3 u1} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (instTopologicalSpaceProd.{u4, u2} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u3, u1} β δ _inst_2 _inst_4) (LocalHomeomorph.prod.{u4, u3, u2, u1} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 e e')) (LocalHomeomorph.prod.{u3, u4, u1, u2} β α δ γ _inst_2 _inst_1 _inst_4 _inst_3 (LocalHomeomorph.symm.{u4, u3} α β _inst_1 _inst_2 e) (LocalHomeomorph.symm.{u2, u1} γ δ _inst_3 _inst_4 e'))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.prod_symm LocalHomeomorph.prod_symmₓ'. -/
@[simp, mfld_simps]
theorem prod_symm (e : LocalHomeomorph α β) (e' : LocalHomeomorph γ δ) :
    (e.Prod e').symm = e.symm.Prod e'.symm :=
  rfl
#align local_homeomorph.prod_symm LocalHomeomorph.prod_symm

/- warning: local_homeomorph.refl_prod_refl -> LocalHomeomorph.refl_prod_refl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_5 : TopologicalSpace.{u1} α] [_inst_6 : TopologicalSpace.{u2} β], Eq.{succ (max u1 u2)} (LocalHomeomorph.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_5 _inst_6) (Prod.topologicalSpace.{u1, u2} α β _inst_5 _inst_6)) (LocalHomeomorph.prod.{u1, u1, u2, u2} α α β β _inst_5 _inst_5 _inst_6 _inst_6 (LocalHomeomorph.refl.{u1} α _inst_5) (LocalHomeomorph.refl.{u2} β _inst_6)) (LocalHomeomorph.refl.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_5 _inst_6))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_5 : TopologicalSpace.{u2} α] [_inst_6 : TopologicalSpace.{u1} β], Eq.{max (succ u2) (succ u1)} (LocalHomeomorph.{max u1 u2, max u1 u2} (Prod.{u2, u1} α β) (Prod.{u2, u1} α β) (instTopologicalSpaceProd.{u2, u1} α β _inst_5 _inst_6) (instTopologicalSpaceProd.{u2, u1} α β _inst_5 _inst_6)) (LocalHomeomorph.prod.{u2, u2, u1, u1} α α β β _inst_5 _inst_5 _inst_6 _inst_6 (LocalHomeomorph.refl.{u2} α _inst_5) (LocalHomeomorph.refl.{u1} β _inst_6)) (LocalHomeomorph.refl.{max u1 u2} (Prod.{u2, u1} α β) (instTopologicalSpaceProd.{u2, u1} α β _inst_5 _inst_6))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.refl_prod_refl LocalHomeomorph.refl_prod_reflₓ'. -/
@[simp]
theorem refl_prod_refl {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] :
    (LocalHomeomorph.refl α).Prod (LocalHomeomorph.refl β) = LocalHomeomorph.refl (α × β) := by
  ext1 ⟨x, y⟩; · rfl; · rintro ⟨x, y⟩; rfl; exact univ_prod_univ
#align local_homeomorph.refl_prod_refl LocalHomeomorph.refl_prod_refl

/- warning: local_homeomorph.prod_trans -> LocalHomeomorph.prod_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] {η : Type.{u5}} {ε : Type.{u6}} [_inst_5 : TopologicalSpace.{u5} η] [_inst_6 : TopologicalSpace.{u6} ε] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (f : LocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3) (e' : LocalHomeomorph.{u4, u5} δ η _inst_4 _inst_5) (f' : LocalHomeomorph.{u5, u6} η ε _inst_5 _inst_6), Eq.{max (succ (max u1 u4)) (succ (max u3 u6))} (LocalHomeomorph.{max u1 u4, max u3 u6} (Prod.{u1, u4} α δ) (Prod.{u3, u6} γ ε) (Prod.topologicalSpace.{u1, u4} α δ _inst_1 _inst_4) (Prod.topologicalSpace.{u3, u6} γ ε _inst_3 _inst_6)) (LocalHomeomorph.trans.{max u1 u4, max u2 u5, max u3 u6} (Prod.{u1, u4} α δ) (Prod.{u2, u5} β η) (Prod.{u3, u6} γ ε) (Prod.topologicalSpace.{u1, u4} α δ _inst_1 _inst_4) (Prod.topologicalSpace.{u2, u5} β η _inst_2 _inst_5) (Prod.topologicalSpace.{u3, u6} γ ε _inst_3 _inst_6) (LocalHomeomorph.prod.{u1, u2, u4, u5} α β δ η _inst_1 _inst_2 _inst_4 _inst_5 e e') (LocalHomeomorph.prod.{u2, u3, u5, u6} β γ η ε _inst_2 _inst_3 _inst_5 _inst_6 f f')) (LocalHomeomorph.prod.{u1, u3, u4, u6} α γ δ ε _inst_1 _inst_3 _inst_4 _inst_6 (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e f) (LocalHomeomorph.trans.{u4, u5, u6} δ η ε _inst_4 _inst_5 _inst_6 e' f'))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u4} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.{u1} δ] {η : Type.{u6}} {ε : Type.{u5}} [_inst_5 : TopologicalSpace.{u6} η] [_inst_6 : TopologicalSpace.{u5} ε] (e : LocalHomeomorph.{u4, u3} α β _inst_1 _inst_2) (f : LocalHomeomorph.{u3, u2} β γ _inst_2 _inst_3) (e' : LocalHomeomorph.{u1, u6} δ η _inst_4 _inst_5) (f' : LocalHomeomorph.{u6, u5} η ε _inst_5 _inst_6), Eq.{max (max (max (succ u4) (succ u2)) (succ u1)) (succ u5)} (LocalHomeomorph.{max u4 u1, max u2 u5} (Prod.{u4, u1} α δ) (Prod.{u2, u5} γ ε) (instTopologicalSpaceProd.{u4, u1} α δ _inst_1 _inst_4) (instTopologicalSpaceProd.{u2, u5} γ ε _inst_3 _inst_6)) (LocalHomeomorph.trans.{max u4 u1, max u3 u6, max u2 u5} (Prod.{u4, u1} α δ) (Prod.{u3, u6} β η) (Prod.{u2, u5} γ ε) (instTopologicalSpaceProd.{u4, u1} α δ _inst_1 _inst_4) (instTopologicalSpaceProd.{u3, u6} β η _inst_2 _inst_5) (instTopologicalSpaceProd.{u2, u5} γ ε _inst_3 _inst_6) (LocalHomeomorph.prod.{u4, u3, u1, u6} α β δ η _inst_1 _inst_2 _inst_4 _inst_5 e e') (LocalHomeomorph.prod.{u3, u2, u6, u5} β γ η ε _inst_2 _inst_3 _inst_5 _inst_6 f f')) (LocalHomeomorph.prod.{u4, u2, u1, u5} α γ δ ε _inst_1 _inst_3 _inst_4 _inst_6 (LocalHomeomorph.trans.{u4, u3, u2} α β γ _inst_1 _inst_2 _inst_3 e f) (LocalHomeomorph.trans.{u1, u6, u5} δ η ε _inst_4 _inst_5 _inst_6 e' f'))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.prod_trans LocalHomeomorph.prod_transₓ'. -/
@[simp, mfld_simps]
theorem prod_trans {η : Type _} {ε : Type _} [TopologicalSpace η] [TopologicalSpace ε]
    (e : LocalHomeomorph α β) (f : LocalHomeomorph β γ) (e' : LocalHomeomorph δ η)
    (f' : LocalHomeomorph η ε) : (e.Prod e').trans (f.Prod f') = (e.trans f).Prod (e'.trans f') :=
  LocalHomeomorph.eq_of_localEquiv_eq <| by
    dsimp only [trans_to_local_equiv, prod_to_local_equiv] <;> apply LocalEquiv.prod_trans
#align local_homeomorph.prod_trans LocalHomeomorph.prod_trans

/- warning: local_homeomorph.prod_eq_prod_of_nonempty -> LocalHomeomorph.prod_eq_prod_of_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] {e₁ : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {e₁' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {e₂ : LocalHomeomorph.{u3, u4} γ δ _inst_3 _inst_4} {e₂' : LocalHomeomorph.{u3, u4} γ δ _inst_3 _inst_4}, (Set.Nonempty.{max u1 u3} (Prod.{u1, u3} α γ) (LocalEquiv.source.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (LocalHomeomorph.toLocalEquiv.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4) (LocalHomeomorph.prod.{u1, u2, u3, u4} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 e₁ e₂)))) -> (Iff (Eq.{max (succ (max u1 u3)) (succ (max u2 u4))} (LocalHomeomorph.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4)) (LocalHomeomorph.prod.{u1, u2, u3, u4} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 e₁ e₂) (LocalHomeomorph.prod.{u1, u2, u3, u4} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 e₁' e₂')) (And (Eq.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) e₁ e₁') (Eq.{max (succ u3) (succ u4)} (LocalHomeomorph.{u3, u4} γ δ _inst_3 _inst_4) e₂ e₂')))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u4} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.{u1} δ] {e₁ : LocalHomeomorph.{u4, u3} α β _inst_1 _inst_2} {e₁' : LocalHomeomorph.{u4, u3} α β _inst_1 _inst_2} {e₂ : LocalHomeomorph.{u2, u1} γ δ _inst_3 _inst_4} {e₂' : LocalHomeomorph.{u2, u1} γ δ _inst_3 _inst_4}, (Set.Nonempty.{max u4 u2} (Prod.{u4, u2} α γ) (LocalEquiv.source.{max u4 u2, max u3 u1} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (LocalHomeomorph.toLocalEquiv.{max u4 u2, max u3 u1} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (instTopologicalSpaceProd.{u4, u2} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u3, u1} β δ _inst_2 _inst_4) (LocalHomeomorph.prod.{u4, u3, u2, u1} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 e₁ e₂)))) -> (Iff (Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (LocalHomeomorph.{max u2 u4, max u1 u3} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (instTopologicalSpaceProd.{u4, u2} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u3, u1} β δ _inst_2 _inst_4)) (LocalHomeomorph.prod.{u4, u3, u2, u1} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 e₁ e₂) (LocalHomeomorph.prod.{u4, u3, u2, u1} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 e₁' e₂')) (And (Eq.{max (succ u4) (succ u3)} (LocalHomeomorph.{u4, u3} α β _inst_1 _inst_2) e₁ e₁') (Eq.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} γ δ _inst_3 _inst_4) e₂ e₂')))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.prod_eq_prod_of_nonempty LocalHomeomorph.prod_eq_prod_of_nonemptyₓ'. -/
theorem prod_eq_prod_of_nonempty {e₁ e₁' : LocalHomeomorph α β} {e₂ e₂' : LocalHomeomorph γ δ}
    (h : (e₁.Prod e₂).source.Nonempty) : e₁.Prod e₂ = e₁'.Prod e₂' ↔ e₁ = e₁' ∧ e₂ = e₂' :=
  by
  obtain ⟨⟨x, y⟩, -⟩ := id h
  haveI : Nonempty α := ⟨x⟩
  haveI : Nonempty β := ⟨e₁ x⟩
  haveI : Nonempty γ := ⟨y⟩
  haveI : Nonempty δ := ⟨e₂ y⟩
  simp_rw [LocalHomeomorph.ext_iff, prod_apply, prod_symm_apply, prod_source, Prod.ext_iff,
    Set.prod_eq_prod_iff_of_nonempty h, forall_and, Prod.forall, forall_const, forall_forall_const,
    and_assoc', and_left_comm]
#align local_homeomorph.prod_eq_prod_of_nonempty LocalHomeomorph.prod_eq_prod_of_nonempty

/- warning: local_homeomorph.prod_eq_prod_of_nonempty' -> LocalHomeomorph.prod_eq_prod_of_nonempty' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] {e₁ : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {e₁' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2} {e₂ : LocalHomeomorph.{u3, u4} γ δ _inst_3 _inst_4} {e₂' : LocalHomeomorph.{u3, u4} γ δ _inst_3 _inst_4}, (Set.Nonempty.{max u1 u3} (Prod.{u1, u3} α γ) (LocalEquiv.source.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (LocalHomeomorph.toLocalEquiv.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4) (LocalHomeomorph.prod.{u1, u2, u3, u4} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 e₁' e₂')))) -> (Iff (Eq.{max (succ (max u1 u3)) (succ (max u2 u4))} (LocalHomeomorph.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4)) (LocalHomeomorph.prod.{u1, u2, u3, u4} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 e₁ e₂) (LocalHomeomorph.prod.{u1, u2, u3, u4} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 e₁' e₂')) (And (Eq.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) e₁ e₁') (Eq.{max (succ u3) (succ u4)} (LocalHomeomorph.{u3, u4} γ δ _inst_3 _inst_4) e₂ e₂')))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u4} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.{u1} δ] {e₁ : LocalHomeomorph.{u4, u3} α β _inst_1 _inst_2} {e₁' : LocalHomeomorph.{u4, u3} α β _inst_1 _inst_2} {e₂ : LocalHomeomorph.{u2, u1} γ δ _inst_3 _inst_4} {e₂' : LocalHomeomorph.{u2, u1} γ δ _inst_3 _inst_4}, (Set.Nonempty.{max u4 u2} (Prod.{u4, u2} α γ) (LocalEquiv.source.{max u4 u2, max u3 u1} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (LocalHomeomorph.toLocalEquiv.{max u4 u2, max u3 u1} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (instTopologicalSpaceProd.{u4, u2} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u3, u1} β δ _inst_2 _inst_4) (LocalHomeomorph.prod.{u4, u3, u2, u1} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 e₁' e₂')))) -> (Iff (Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (LocalHomeomorph.{max u2 u4, max u1 u3} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (instTopologicalSpaceProd.{u4, u2} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u3, u1} β δ _inst_2 _inst_4)) (LocalHomeomorph.prod.{u4, u3, u2, u1} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 e₁ e₂) (LocalHomeomorph.prod.{u4, u3, u2, u1} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 e₁' e₂')) (And (Eq.{max (succ u4) (succ u3)} (LocalHomeomorph.{u4, u3} α β _inst_1 _inst_2) e₁ e₁') (Eq.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} γ δ _inst_3 _inst_4) e₂ e₂')))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.prod_eq_prod_of_nonempty' LocalHomeomorph.prod_eq_prod_of_nonempty'ₓ'. -/
theorem prod_eq_prod_of_nonempty' {e₁ e₁' : LocalHomeomorph α β} {e₂ e₂' : LocalHomeomorph γ δ}
    (h : (e₁'.Prod e₂').source.Nonempty) : e₁.Prod e₂ = e₁'.Prod e₂' ↔ e₁ = e₁' ∧ e₂ = e₂' := by
  rw [eq_comm, prod_eq_prod_of_nonempty h, eq_comm, @eq_comm _ e₂']
#align local_homeomorph.prod_eq_prod_of_nonempty' LocalHomeomorph.prod_eq_prod_of_nonempty'

end Prod

section Piecewise

/- warning: local_homeomorph.piecewise -> LocalHomeomorph.piecewise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α) (t : Set.{u2} β) [_inst_5 : forall (x : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)] [_inst_6 : forall (y : β), Decidable (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y t)], (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e' s t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (frontier.{u1} α _inst_1 s)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e')) (frontier.{u1} α _inst_1 s))) -> (Set.EqOn.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e') (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (frontier.{u1} α _inst_1 s))) -> (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α) (t : Set.{u2} β) [_inst_5 : forall (x : α), Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)] [_inst_6 : forall (y : β), Decidable (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) y t)], (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e s t) -> (LocalHomeomorph.IsImage.{u1, u2} α β _inst_1 _inst_2 e' s t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (frontier.{u1} α _inst_1 s)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e')) (frontier.{u1} α _inst_1 s))) -> (Set.EqOn.{u1, u2} α β (LocalHomeomorph.toFun'.{u1, u2} α β _inst_1 _inst_2 e) (LocalHomeomorph.toFun'.{u1, u2} α β _inst_1 _inst_2 e') (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (frontier.{u1} α _inst_1 s))) -> (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.piecewise LocalHomeomorph.piecewiseₓ'. -/
/-- Combine two `local_homeomorph`s using `set.piecewise`. The source of the new `local_homeomorph`
is `s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly for target.  The
function sends `e.source ∩ s` to `e.target ∩ t` using `e` and `e'.source \ s` to `e'.target \ t`
using `e'`, and similarly for the inverse function. To ensure that the maps `to_fun` and `inv_fun`
are inverse of each other on the new `source` and `target`, the definition assumes that the sets `s`
and `t` are related both by `e.is_image` and `e'.is_image`. To ensure that the new maps are
continuous on `source`/`target`, it also assumes that `e.source` and `e'.source` meet `frontier s`
on the same set and `e x = e' x` on this intersection. -/
@[simps (config := { fullyApplied := false }) toLocalEquiv apply]
def piecewise (e e' : LocalHomeomorph α β) (s : Set α) (t : Set β) [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Heq : EqOn e e' (e.source ∩ frontier s)) : LocalHomeomorph α β
    where
  toLocalEquiv := e.toLocalEquiv.piecewise e'.toLocalEquiv s t H H'
  open_source := e.open_source.ite e'.open_source Hs
  open_target :=
    e.open_target.ite e'.open_target <| H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq
  continuous_toFun := continuousOn_piecewise_ite e.ContinuousOn e'.ContinuousOn Hs Heq
  continuous_invFun :=
    continuousOn_piecewise_ite e.continuousOn_symm e'.continuousOn_symm
      (H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq)
      (H.frontier.symm_eq_on_of_inter_eq_of_eqOn Hs Heq)
#align local_homeomorph.piecewise LocalHomeomorph.piecewise

/- warning: local_homeomorph.symm_piecewise -> LocalHomeomorph.symm_piecewise is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align local_homeomorph.symm_piecewise LocalHomeomorph.symm_piecewiseₓ'. -/
@[simp]
theorem symm_piecewise (e e' : LocalHomeomorph α β) {s : Set α} {t : Set β} [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Heq : EqOn e e' (e.source ∩ frontier s)) :
    (e.piecewise e' s t H H' Hs Heq).symm =
      e.symm.piecewise e'.symm t s H.symm H'.symm
        (H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq)
        (H.frontier.symm_eq_on_of_inter_eq_of_eqOn Hs Heq) :=
  rfl
#align local_homeomorph.symm_piecewise LocalHomeomorph.symm_piecewise

/- warning: local_homeomorph.disjoint_union -> LocalHomeomorph.disjointUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) [_inst_5 : forall (x : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)))] [_inst_6 : forall (y : β), Decidable (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)))], (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e'))) -> (Disjoint.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e'))) -> (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) [_inst_5 : forall (x : α), Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)))] [_inst_6 : forall (y : β), Decidable (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) y (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)))], (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e'))) -> (Disjoint.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} β) (Preorder.toLE.{u2} (Set.{u2} β) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))))) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e'))) -> (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.disjoint_union LocalHomeomorph.disjointUnionₓ'. -/
/-- Combine two `local_homeomorph`s with disjoint sources and disjoint targets. We reuse
`local_homeomorph.piecewise` then override `to_local_equiv` to `local_equiv.disjoint_union`.
This way we have better definitional equalities for `source` and `target`. -/
def disjointUnion (e e' : LocalHomeomorph α β) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] (Hs : Disjoint e.source e'.source)
    (Ht : Disjoint e.target e'.target) : LocalHomeomorph α β :=
  (e.piecewise e' e.source e.target e.isImage_source_target
        (e'.isImage_source_target_of_disjoint e Hs.symm Ht.symm)
        (by rw [e.open_source.inter_frontier_eq, (Hs.symm.frontier_right e'.open_source).inter_eq])
        (by rw [e.open_source.inter_frontier_eq]; exact eq_on_empty _ _)).replaceEquiv
    (e.toLocalEquiv.disjointUnion e'.toLocalEquiv Hs Ht)
    (LocalEquiv.disjointUnion_eq_piecewise _ _ _ _).symm
#align local_homeomorph.disjoint_union LocalHomeomorph.disjointUnion

end Piecewise

section Pi

variable {ι : Type _} [Fintype ι] {Xi Yi : ι → Type _} [∀ i, TopologicalSpace (Xi i)]
  [∀ i, TopologicalSpace (Yi i)] (ei : ∀ i, LocalHomeomorph (Xi i) (Yi i))

#print LocalHomeomorph.pi /-
/-- The product of a finite family of `local_homeomorph`s. -/
@[simps toLocalEquiv]
def pi : LocalHomeomorph (∀ i, Xi i) (∀ i, Yi i)
    where
  toLocalEquiv := LocalEquiv.pi fun i => (ei i).toLocalEquiv
  open_source := isOpen_set_pi finite_univ fun i hi => (ei i).open_source
  open_target := isOpen_set_pi finite_univ fun i hi => (ei i).open_target
  continuous_toFun :=
    continuousOn_pi.2 fun i =>
      (ei i).ContinuousOn.comp (continuous_apply _).ContinuousOn fun f hf => hf i trivial
  continuous_invFun :=
    continuousOn_pi.2 fun i =>
      (ei i).continuousOn_symm.comp (continuous_apply _).ContinuousOn fun f hf => hf i trivial
#align local_homeomorph.pi LocalHomeomorph.pi
-/

end Pi

section Continuity

/- warning: local_homeomorph.continuous_within_at_iff_continuous_within_at_comp_right -> LocalHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {f : β -> γ} {s : Set.{u2} β} {x : β}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Iff (ContinuousWithinAt.{u2, u3} β γ _inst_2 _inst_3 f s x) (ContinuousWithinAt.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] (e : LocalHomeomorph.{u2, u3} α β _inst_1 _inst_2) {f : β -> γ} {s : Set.{u3} β} {x : β}, (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) x (LocalEquiv.target.{u2, u3} α β (LocalHomeomorph.toLocalEquiv.{u2, u3} α β _inst_1 _inst_2 e))) -> (Iff (ContinuousWithinAt.{u3, u1} β γ _inst_2 _inst_3 f s x) (ContinuousWithinAt.{u2, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u2, succ u3, succ u1} α β γ f (LocalHomeomorph.toFun'.{u2, u3} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u3} α β (LocalHomeomorph.toFun'.{u2, u3} α β _inst_1 _inst_2 e) s) (LocalHomeomorph.toFun'.{u3, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u3} α β _inst_1 _inst_2 e) x)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.continuous_within_at_iff_continuous_within_at_comp_right LocalHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_rightₓ'. -/
/-- Continuity within a set at a point can be read under right composition with a local
homeomorphism, if the point is in its target -/
theorem continuousWithinAt_iff_continuousWithinAt_comp_right {f : β → γ} {s : Set β} {x : β}
    (h : x ∈ e.target) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (f ∘ e) (e ⁻¹' s) (e.symm x) := by
  simp_rw [ContinuousWithinAt, ← @tendsto_map'_iff _ _ _ _ e,
    e.map_nhds_within_preimage_eq (e.map_target h), (· ∘ ·), e.right_inv h]
#align local_homeomorph.continuous_within_at_iff_continuous_within_at_comp_right LocalHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_right

/- warning: local_homeomorph.continuous_at_iff_continuous_at_comp_right -> LocalHomeomorph.continuousAt_iff_continuousAt_comp_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {f : β -> γ} {x : β}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Iff (ContinuousAt.{u2, u3} β γ _inst_2 _inst_3 f x) (ContinuousAt.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e) x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] (e : LocalHomeomorph.{u2, u3} α β _inst_1 _inst_2) {f : β -> γ} {x : β}, (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) x (LocalEquiv.target.{u2, u3} α β (LocalHomeomorph.toLocalEquiv.{u2, u3} α β _inst_1 _inst_2 e))) -> (Iff (ContinuousAt.{u3, u1} β γ _inst_2 _inst_3 f x) (ContinuousAt.{u2, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u2, succ u3, succ u1} α β γ f (LocalHomeomorph.toFun'.{u2, u3} α β _inst_1 _inst_2 e)) (LocalHomeomorph.toFun'.{u3, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u3} α β _inst_1 _inst_2 e) x)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.continuous_at_iff_continuous_at_comp_right LocalHomeomorph.continuousAt_iff_continuousAt_comp_rightₓ'. -/
/-- Continuity at a point can be read under right composition with a local homeomorphism, if the
point is in its target -/
theorem continuousAt_iff_continuousAt_comp_right {f : β → γ} {x : β} (h : x ∈ e.target) :
    ContinuousAt f x ↔ ContinuousAt (f ∘ e) (e.symm x) := by
  rw [← continuousWithinAt_univ, e.continuous_within_at_iff_continuous_within_at_comp_right h,
    preimage_univ, continuousWithinAt_univ]
#align local_homeomorph.continuous_at_iff_continuous_at_comp_right LocalHomeomorph.continuousAt_iff_continuousAt_comp_right

/- warning: local_homeomorph.continuous_on_iff_continuous_on_comp_right -> LocalHomeomorph.continuousOn_iff_continuousOn_comp_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {f : β -> γ} {s : Set.{u2} β}, (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) s (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Iff (ContinuousOn.{u2, u3} β γ _inst_2 _inst_3 f s) (ContinuousOn.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] (e : LocalHomeomorph.{u2, u3} α β _inst_1 _inst_2) {f : β -> γ} {s : Set.{u3} β}, (HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet.{u3} β) s (LocalEquiv.target.{u2, u3} α β (LocalHomeomorph.toLocalEquiv.{u2, u3} α β _inst_1 _inst_2 e))) -> (Iff (ContinuousOn.{u3, u1} β γ _inst_2 _inst_3 f s) (ContinuousOn.{u2, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u2, succ u3, succ u1} α β γ f (LocalHomeomorph.toFun'.{u2, u3} α β _inst_1 _inst_2 e)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u3} α β (LocalHomeomorph.toLocalEquiv.{u2, u3} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u3} α β (LocalHomeomorph.toFun'.{u2, u3} α β _inst_1 _inst_2 e) s))))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.continuous_on_iff_continuous_on_comp_right LocalHomeomorph.continuousOn_iff_continuousOn_comp_rightₓ'. -/
/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the right is continuous on the corresponding set. -/
theorem continuousOn_iff_continuousOn_comp_right {f : β → γ} {s : Set β} (h : s ⊆ e.target) :
    ContinuousOn f s ↔ ContinuousOn (f ∘ e) (e.source ∩ e ⁻¹' s) :=
  by
  simp only [← e.symm_image_eq_source_inter_preimage h, ContinuousOn, ball_image_iff]
  refine' forall₂_congr fun x hx => _
  rw [e.continuous_within_at_iff_continuous_within_at_comp_right (h hx),
    e.symm_image_eq_source_inter_preimage h, inter_comm, continuousWithinAt_inter]
  exact IsOpen.mem_nhds e.open_source (e.map_target (h hx))
#align local_homeomorph.continuous_on_iff_continuous_on_comp_right LocalHomeomorph.continuousOn_iff_continuousOn_comp_right

/- warning: local_homeomorph.continuous_within_at_iff_continuous_within_at_comp_left -> LocalHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {f : γ -> α} {s : Set.{u3} γ} {x : γ}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (f x) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) -> (Membership.Mem.{u3, u3} (Set.{u3} γ) (Filter.{u3} γ) (Filter.hasMem.{u3} γ) (Set.preimage.{u3, u1} γ α f (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) (nhdsWithin.{u3} γ _inst_3 x s)) -> (Iff (ContinuousWithinAt.{u3, u1} γ α _inst_3 _inst_1 f s x) (ContinuousWithinAt.{u3, u2} γ β _inst_3 _inst_2 (Function.comp.{succ u3, succ u1, succ u2} γ α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) f) s x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {f : γ -> α} {s : Set.{u3} γ} {x : γ}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (f x) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) -> (Membership.mem.{u3, u3} (Set.{u3} γ) (Filter.{u3} γ) (instMembershipSetFilter.{u3} γ) (Set.preimage.{u3, u2} γ α f (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) (nhdsWithin.{u3} γ _inst_3 x s)) -> (Iff (ContinuousWithinAt.{u3, u2} γ α _inst_3 _inst_1 f s x) (ContinuousWithinAt.{u3, u1} γ β _inst_3 _inst_2 (Function.comp.{succ u3, succ u2, succ u1} γ α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) f) s x))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.continuous_within_at_iff_continuous_within_at_comp_left LocalHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_leftₓ'. -/
/-- Continuity within a set at a point can be read under left composition with a local
homeomorphism if a neighborhood of the initial point is sent to the source of the local
homeomorphism-/
theorem continuousWithinAt_iff_continuousWithinAt_comp_left {f : γ → α} {s : Set γ} {x : γ}
    (hx : f x ∈ e.source) (h : f ⁻¹' e.source ∈ 𝓝[s] x) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (e ∘ f) s x :=
  by
  refine' ⟨(e.continuous_at hx).comp_continuousWithinAt, fun fe_cont => _⟩
  rw [← continuousWithinAt_inter' h] at fe_cont⊢
  have : ContinuousWithinAt (e.symm ∘ e ∘ f) (s ∩ f ⁻¹' e.source) x :=
    haveI : ContinuousWithinAt e.symm univ (e (f x)) :=
      (e.continuous_at_symm (e.map_source hx)).ContinuousWithinAt
    ContinuousWithinAt.comp this fe_cont (subset_univ _)
  exact this.congr (fun y hy => by simp [e.left_inv hy.2]) (by simp [e.left_inv hx])
#align local_homeomorph.continuous_within_at_iff_continuous_within_at_comp_left LocalHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_left

/- warning: local_homeomorph.continuous_at_iff_continuous_at_comp_left -> LocalHomeomorph.continuousAt_iff_continuousAt_comp_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {f : γ -> α} {x : γ}, (Membership.Mem.{u3, u3} (Set.{u3} γ) (Filter.{u3} γ) (Filter.hasMem.{u3} γ) (Set.preimage.{u3, u1} γ α f (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) (nhds.{u3} γ _inst_3 x)) -> (Iff (ContinuousAt.{u3, u1} γ α _inst_3 _inst_1 f x) (ContinuousAt.{u3, u2} γ β _inst_3 _inst_2 (Function.comp.{succ u3, succ u1, succ u2} γ α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) f) x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {f : γ -> α} {x : γ}, (Membership.mem.{u3, u3} (Set.{u3} γ) (Filter.{u3} γ) (instMembershipSetFilter.{u3} γ) (Set.preimage.{u3, u2} γ α f (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) (nhds.{u3} γ _inst_3 x)) -> (Iff (ContinuousAt.{u3, u2} γ α _inst_3 _inst_1 f x) (ContinuousAt.{u3, u1} γ β _inst_3 _inst_2 (Function.comp.{succ u3, succ u2, succ u1} γ α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) f) x))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.continuous_at_iff_continuous_at_comp_left LocalHomeomorph.continuousAt_iff_continuousAt_comp_leftₓ'. -/
/-- Continuity at a point can be read under left composition with a local homeomorphism if a
neighborhood of the initial point is sent to the source of the local homeomorphism-/
theorem continuousAt_iff_continuousAt_comp_left {f : γ → α} {x : γ} (h : f ⁻¹' e.source ∈ 𝓝 x) :
    ContinuousAt f x ↔ ContinuousAt (e ∘ f) x :=
  by
  have hx : f x ∈ e.source := (mem_of_mem_nhds h : _)
  have h' : f ⁻¹' e.source ∈ 𝓝[univ] x := by rwa [nhdsWithin_univ]
  rw [← continuousWithinAt_univ, ← continuousWithinAt_univ,
    e.continuous_within_at_iff_continuous_within_at_comp_left hx h']
#align local_homeomorph.continuous_at_iff_continuous_at_comp_left LocalHomeomorph.continuousAt_iff_continuousAt_comp_left

/- warning: local_homeomorph.continuous_on_iff_continuous_on_comp_left -> LocalHomeomorph.continuousOn_iff_continuousOn_comp_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {f : γ -> α} {s : Set.{u3} γ}, (HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) s (Set.preimage.{u3, u1} γ α f (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)))) -> (Iff (ContinuousOn.{u3, u1} γ α _inst_3 _inst_1 f s) (ContinuousOn.{u3, u2} γ β _inst_3 _inst_2 (Function.comp.{succ u3, succ u1, succ u2} γ α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) f) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {f : γ -> α} {s : Set.{u3} γ}, (HasSubset.Subset.{u3} (Set.{u3} γ) (Set.instHasSubsetSet.{u3} γ) s (Set.preimage.{u3, u2} γ α f (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)))) -> (Iff (ContinuousOn.{u3, u2} γ α _inst_3 _inst_1 f s) (ContinuousOn.{u3, u1} γ β _inst_3 _inst_2 (Function.comp.{succ u3, succ u2, succ u1} γ α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) f) s))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.continuous_on_iff_continuous_on_comp_left LocalHomeomorph.continuousOn_iff_continuousOn_comp_leftₓ'. -/
/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the left is continuous on the corresponding set. -/
theorem continuousOn_iff_continuousOn_comp_left {f : γ → α} {s : Set γ} (h : s ⊆ f ⁻¹' e.source) :
    ContinuousOn f s ↔ ContinuousOn (e ∘ f) s :=
  forall₂_congr fun x hx =>
    e.continuousWithinAt_iff_continuousWithinAt_comp_left (h hx)
      (mem_of_superset self_mem_nhdsWithin h)
#align local_homeomorph.continuous_on_iff_continuous_on_comp_left LocalHomeomorph.continuousOn_iff_continuousOn_comp_left

/- warning: local_homeomorph.continuous_iff_continuous_comp_left -> LocalHomeomorph.continuous_iff_continuous_comp_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) {f : γ -> α}, (Eq.{succ u3} (Set.{u3} γ) (Set.preimage.{u3, u1} γ α f (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e))) (Set.univ.{u3} γ)) -> (Iff (Continuous.{u3, u1} γ α _inst_3 _inst_1 f) (Continuous.{u3, u2} γ β _inst_3 _inst_2 (Function.comp.{succ u3, succ u1, succ u2} γ α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) {f : γ -> α}, (Eq.{succ u3} (Set.{u3} γ) (Set.preimage.{u3, u2} γ α f (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e))) (Set.univ.{u3} γ)) -> (Iff (Continuous.{u3, u2} γ α _inst_3 _inst_1 f) (Continuous.{u3, u1} γ β _inst_3 _inst_2 (Function.comp.{succ u3, succ u2, succ u1} γ α β (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e) f)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.continuous_iff_continuous_comp_left LocalHomeomorph.continuous_iff_continuous_comp_leftₓ'. -/
/-- A function is continuous if and only if its composition with a local homeomorphism
on the left is continuous and its image is contained in the source. -/
theorem continuous_iff_continuous_comp_left {f : γ → α} (h : f ⁻¹' e.source = univ) :
    Continuous f ↔ Continuous (e ∘ f) :=
  by
  simp only [continuous_iff_continuousOn_univ]
  exact e.continuous_on_iff_continuous_on_comp_left (Eq.symm h).Subset
#align local_homeomorph.continuous_iff_continuous_comp_left LocalHomeomorph.continuous_iff_continuous_comp_left

end Continuity

#print LocalHomeomorph.homeomorphOfImageSubsetSource /-
/-- The homeomorphism obtained by restricting a `local_homeomorph` to a subset of the source. -/
@[simps]
def homeomorphOfImageSubsetSource {s : Set α} {t : Set β} (hs : s ⊆ e.source) (ht : e '' s = t) :
    s ≃ₜ t where
  toFun a := ⟨e a, (congr_arg ((· ∈ ·) (e a)) ht).mp ⟨a, a.2, rfl⟩⟩
  invFun b :=
    ⟨e.symm b,
      let ⟨a, ha1, ha2⟩ := (congr_arg ((· ∈ ·) ↑b) ht).mpr b.2
      ha2 ▸ (e.left_inv (hs ha1)).symm ▸ ha1⟩
  left_inv a := Subtype.ext (e.left_inv (hs a.2))
  right_inv b :=
    let ⟨a, ha1, ha2⟩ := (congr_arg ((· ∈ ·) ↑b) ht).mpr b.2
    Subtype.ext (e.right_inv (ha2 ▸ e.map_source (hs ha1)))
  continuous_toFun :=
    (continuousOn_iff_continuous_restrict.mp (e.ContinuousOn.mono hs)).subtype_mk _
  continuous_invFun :=
    (continuousOn_iff_continuous_restrict.mp
          (e.continuousOn_symm.mono fun b hb =>
            let ⟨a, ha1, ha2⟩ := show b ∈ e '' s from ht.symm ▸ hb
            ha2 ▸ e.map_source (hs ha1))).subtype_mk
      _
#align local_homeomorph.homeomorph_of_image_subset_source LocalHomeomorph.homeomorphOfImageSubsetSource
-/

#print LocalHomeomorph.toHomeomorphSourceTarget /-
/-- A local homeomrphism defines a homeomorphism between its source and target. -/
def toHomeomorphSourceTarget : e.source ≃ₜ e.target :=
  e.homeomorphOfImageSubsetSource subset_rfl e.image_source_eq_target
#align local_homeomorph.to_homeomorph_source_target LocalHomeomorph.toHomeomorphSourceTarget
-/

#print LocalHomeomorph.secondCountableTopology_source /-
theorem secondCountableTopology_source [SecondCountableTopology β] (e : LocalHomeomorph α β) :
    SecondCountableTopology e.source :=
  e.toHomeomorphSourceTarget.SecondCountableTopology
#align local_homeomorph.second_countable_topology_source LocalHomeomorph.secondCountableTopology_source
-/

#print LocalHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv /-
/-- If a local homeomorphism has source and target equal to univ, then it induces a homeomorphism
between the whole spaces, expressed in this definition. -/
@[simps (config := mfld_cfg) apply symm_apply]
def toHomeomorphOfSourceEqUnivTargetEqUniv (h : e.source = (univ : Set α)) (h' : e.target = univ) :
    α ≃ₜ β where
  toFun := e
  invFun := e.symm
  left_inv x := e.left_inv <| by rw [h]; exact mem_univ _
  right_inv x := e.right_inv <| by rw [h']; exact mem_univ _
  continuous_toFun := by
    rw [continuous_iff_continuousOn_univ]
    convert e.continuous_to_fun
    rw [h]
  continuous_invFun := by
    rw [continuous_iff_continuousOn_univ]
    convert e.continuous_inv_fun
    rw [h']
#align local_homeomorph.to_homeomorph_of_source_eq_univ_target_eq_univ LocalHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv
-/

/- warning: local_homeomorph.to_open_embedding -> LocalHomeomorph.to_openEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), (Eq.{succ u1} (Set.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (Set.univ.{u1} α)) -> (OpenEmbedding.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), (Eq.{succ u2} (Set.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (Set.univ.{u2} α)) -> (OpenEmbedding.{u2, u1} α β _inst_1 _inst_2 (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.to_open_embedding LocalHomeomorph.to_openEmbeddingₓ'. -/
/-- A local homeomorphism whose source is all of `α` defines an open embedding of `α` into `β`.  The
converse is also true; see `open_embedding.to_local_homeomorph`. -/
theorem to_openEmbedding (h : e.source = Set.univ) : OpenEmbedding e :=
  by
  apply openEmbedding_of_continuous_injective_open
  · apply continuous_iff_continuous_on_univ.mpr
    rw [← h]
    exact e.continuous_to_fun
  · apply set.injective_iff_inj_on_univ.mpr
    rw [← h]
    exact e.inj_on
  · intro U hU
    simpa only [h, subset_univ, mfld_simps] using e.image_open_of_open hU
#align local_homeomorph.to_open_embedding LocalHomeomorph.to_openEmbedding

end LocalHomeomorph

namespace Homeomorph

variable (e : α ≃ₜ β) (e' : β ≃ₜ γ)

#print Homeomorph.refl_toLocalHomeomorph /-
/- Register as simp lemmas that the fields of a local homeomorphism built from a homeomorphism
correspond to the fields of the original homeomorphism. -/
@[simp, mfld_simps]
theorem refl_toLocalHomeomorph : (Homeomorph.refl α).toLocalHomeomorph = LocalHomeomorph.refl α :=
  rfl
#align homeomorph.refl_to_local_homeomorph Homeomorph.refl_toLocalHomeomorph
-/

/- warning: homeomorph.symm_to_local_homeomorph -> Homeomorph.symm_toLocalHomeomorph is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (Homeomorph.toLocalHomeomorph.{u2, u1} β α _inst_2 _inst_1 (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 e)) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 (Homeomorph.toLocalHomeomorph.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (LocalHomeomorph.{u1, u2} β α _inst_2 _inst_1) (Homeomorph.toLocalHomeomorph.{u1, u2} β α _inst_2 _inst_1 (Homeomorph.symm.{u2, u1} α β _inst_1 _inst_2 e)) (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 (Homeomorph.toLocalHomeomorph.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align homeomorph.symm_to_local_homeomorph Homeomorph.symm_toLocalHomeomorphₓ'. -/
@[simp, mfld_simps]
theorem symm_toLocalHomeomorph : e.symm.toLocalHomeomorph = e.toLocalHomeomorph.symm :=
  rfl
#align homeomorph.symm_to_local_homeomorph Homeomorph.symm_toLocalHomeomorph

/- warning: homeomorph.trans_to_local_homeomorph -> Homeomorph.trans_toLocalHomeomorph is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (e : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (e' : Homeomorph.{u2, u3} β γ _inst_2 _inst_3), Eq.{max (succ u1) (succ u3)} (LocalHomeomorph.{u1, u3} α γ _inst_1 _inst_3) (Homeomorph.toLocalHomeomorph.{u1, u3} α γ _inst_1 _inst_3 (Homeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 e e')) (LocalHomeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (Homeomorph.toLocalHomeomorph.{u1, u2} α β _inst_1 _inst_2 e) (Homeomorph.toLocalHomeomorph.{u2, u3} β γ _inst_2 _inst_3 e'))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u2} γ] (e : Homeomorph.{u3, u1} α β _inst_1 _inst_2) (e' : Homeomorph.{u1, u2} β γ _inst_2 _inst_3), Eq.{max (succ u3) (succ u2)} (LocalHomeomorph.{u3, u2} α γ _inst_1 _inst_3) (Homeomorph.toLocalHomeomorph.{u3, u2} α γ _inst_1 _inst_3 (Homeomorph.trans.{u3, u1, u2} α β γ _inst_1 _inst_2 _inst_3 e e')) (LocalHomeomorph.trans.{u3, u1, u2} α β γ _inst_1 _inst_2 _inst_3 (Homeomorph.toLocalHomeomorph.{u3, u1} α β _inst_1 _inst_2 e) (Homeomorph.toLocalHomeomorph.{u1, u2} β γ _inst_2 _inst_3 e'))
Case conversion may be inaccurate. Consider using '#align homeomorph.trans_to_local_homeomorph Homeomorph.trans_toLocalHomeomorphₓ'. -/
@[simp, mfld_simps]
theorem trans_toLocalHomeomorph :
    (e.trans e').toLocalHomeomorph = e.toLocalHomeomorph.trans e'.toLocalHomeomorph :=
  LocalHomeomorph.eq_of_localEquiv_eq <| Equiv.trans_toLocalEquiv _ _
#align homeomorph.trans_to_local_homeomorph Homeomorph.trans_toLocalHomeomorph

end Homeomorph

namespace OpenEmbedding

variable (f : α → β) (h : OpenEmbedding f)

#print OpenEmbedding.toLocalHomeomorph /-
/-- An open embedding of `α` into `β`, with `α` nonempty, defines a local homeomorphism whose source
is all of `α`.  The converse is also true; see `local_homeomorph.to_open_embedding`. -/
@[simps (config := mfld_cfg) apply source target]
noncomputable def toLocalHomeomorph [Nonempty α] : LocalHomeomorph α β :=
  LocalHomeomorph.ofContinuousOpen ((h.toEmbedding.inj.InjOn univ).toLocalEquiv _ _)
    h.Continuous.ContinuousOn h.IsOpenMap isOpen_univ
#align open_embedding.to_local_homeomorph OpenEmbedding.toLocalHomeomorph
-/

/- warning: open_embedding.continuous_at_iff -> OpenEmbedding.continuousAt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> β} {g : β -> γ}, (OpenEmbedding.{u1, u2} α β _inst_1 _inst_2 f) -> (forall {x : α}, Iff (ContinuousAt.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) x) (ContinuousAt.{u2, u3} β γ _inst_2 _inst_3 g (f x)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> β} {g : β -> γ}, (OpenEmbedding.{u3, u2} α β _inst_1 _inst_2 f) -> (forall {x : α}, Iff (ContinuousAt.{u3, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u3, succ u2, succ u1} α β γ g f) x) (ContinuousAt.{u2, u1} β γ _inst_2 _inst_3 g (f x)))
Case conversion may be inaccurate. Consider using '#align open_embedding.continuous_at_iff OpenEmbedding.continuousAt_iffₓ'. -/
theorem continuousAt_iff {f : α → β} {g : β → γ} (hf : OpenEmbedding f) {x : α} :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) :=
  by
  haveI : Nonempty α := ⟨x⟩
  convert((hf.to_local_homeomorph f).continuousAt_iff_continuousAt_comp_right _).symm
  · apply (LocalHomeomorph.left_inv _ _).symm
    simp
  · simp
#align open_embedding.continuous_at_iff OpenEmbedding.continuousAt_iff

end OpenEmbedding

namespace TopologicalSpace.Opens

open TopologicalSpace

variable (s : Opens α) [Nonempty s]

#print TopologicalSpace.Opens.localHomeomorphSubtypeCoe /-
/-- The inclusion of an open subset `s` of a space `α` into `α` is a local homeomorphism from the
subtype `s` to `α`. -/
noncomputable def localHomeomorphSubtypeCoe : LocalHomeomorph s α :=
  OpenEmbedding.toLocalHomeomorph _ s.2.openEmbedding_subtype_val
#align topological_space.opens.local_homeomorph_subtype_coe TopologicalSpace.Opens.localHomeomorphSubtypeCoe
-/

#print TopologicalSpace.Opens.localHomeomorphSubtypeCoe_coe /-
@[simp, mfld_simps]
theorem localHomeomorphSubtypeCoe_coe : (s.localHomeomorphSubtypeCoe : s → α) = coe :=
  rfl
#align topological_space.opens.local_homeomorph_subtype_coe_coe TopologicalSpace.Opens.localHomeomorphSubtypeCoe_coe
-/

#print TopologicalSpace.Opens.localHomeomorphSubtypeCoe_source /-
@[simp, mfld_simps]
theorem localHomeomorphSubtypeCoe_source : s.localHomeomorphSubtypeCoe.source = Set.univ :=
  rfl
#align topological_space.opens.local_homeomorph_subtype_coe_source TopologicalSpace.Opens.localHomeomorphSubtypeCoe_source
-/

#print TopologicalSpace.Opens.localHomeomorphSubtypeCoe_target /-
@[simp, mfld_simps]
theorem localHomeomorphSubtypeCoe_target : s.localHomeomorphSubtypeCoe.target = s := by
  simp only [local_homeomorph_subtype_coe, Subtype.range_coe_subtype, mfld_simps]; rfl
#align topological_space.opens.local_homeomorph_subtype_coe_target TopologicalSpace.Opens.localHomeomorphSubtypeCoe_target
-/

end TopologicalSpace.Opens

namespace LocalHomeomorph

open TopologicalSpace

variable (e : LocalHomeomorph α β)

variable (s : Opens α) [Nonempty s]

#print LocalHomeomorph.subtypeRestr /-
/-- The restriction of a local homeomorphism `e` to an open subset `s` of the domain type produces a
local homeomorphism whose domain is the subtype `s`.-/
noncomputable def subtypeRestr : LocalHomeomorph s β :=
  s.localHomeomorphSubtypeCoe.trans e
#align local_homeomorph.subtype_restr LocalHomeomorph.subtypeRestr
-/

/- warning: local_homeomorph.subtype_restr_def -> LocalHomeomorph.subtypeRestr_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : TopologicalSpace.Opens.{u1} α _inst_1) [_inst_5 : Nonempty.{succ u1} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s)], Eq.{max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) x s) _inst_1) _inst_2) (LocalHomeomorph.subtypeRestr.{u1, u2} α β _inst_1 _inst_2 e s _inst_5) (LocalHomeomorph.trans.{u1, u1, u2} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s) α β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) x s) _inst_1) _inst_1 _inst_2 (TopologicalSpace.Opens.localHomeomorphSubtypeCoe.{u1} α _inst_1 s _inst_5) e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (s : TopologicalSpace.Opens.{u2} α _inst_1) [_inst_5 : Nonempty.{succ u2} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s))], Eq.{max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s)) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s) _inst_1) _inst_2) (LocalHomeomorph.subtypeRestr.{u2, u1} α β _inst_1 _inst_2 e s _inst_5) (LocalHomeomorph.trans.{u2, u2, u1} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s)) α β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s) _inst_1) _inst_1 _inst_2 (TopologicalSpace.Opens.localHomeomorphSubtypeCoe.{u2} α _inst_1 s _inst_5) e)
Case conversion may be inaccurate. Consider using '#align local_homeomorph.subtype_restr_def LocalHomeomorph.subtypeRestr_defₓ'. -/
theorem subtypeRestr_def : e.subtypeRestr s = s.localHomeomorphSubtypeCoe.trans e :=
  rfl
#align local_homeomorph.subtype_restr_def LocalHomeomorph.subtypeRestr_def

/- warning: local_homeomorph.subtype_restr_coe -> LocalHomeomorph.subtypeRestr_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : TopologicalSpace.Opens.{u1} α _inst_1) [_inst_5 : Nonempty.{succ u1} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s)], Eq.{max (succ u1) (succ u2)} ((fun (_x : LocalHomeomorph.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) x s) _inst_1) _inst_2) => (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s) -> β) (LocalHomeomorph.subtypeRestr.{u1, u2} α β _inst_1 _inst_2 e s _inst_5)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) x s) _inst_1) _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) x s) _inst_1) _inst_2) => (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s) -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) x s) _inst_1) _inst_2) (LocalHomeomorph.subtypeRestr.{u1, u2} α β _inst_1 _inst_2 e s _inst_5)) (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) s) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocalHomeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (s : TopologicalSpace.Opens.{u2} α _inst_1) [_inst_5 : Nonempty.{succ u2} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s))], Eq.{max (succ u2) (succ u1)} ((Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s)) -> β) (LocalHomeomorph.toFun'.{u2, u1} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s)) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s) _inst_1) _inst_2 (LocalHomeomorph.subtypeRestr.{u2, u1} α β _inst_1 _inst_2 e s _inst_5)) (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) (SetLike.coe.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1) s) (LocalHomeomorph.toFun'.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.subtype_restr_coe LocalHomeomorph.subtypeRestr_coeₓ'. -/
@[simp, mfld_simps]
theorem subtypeRestr_coe :
    ((e.subtypeRestr s : LocalHomeomorph s β) : s → β) = Set.restrict ↑s (e : α → β) :=
  rfl
#align local_homeomorph.subtype_restr_coe LocalHomeomorph.subtypeRestr_coe

/- warning: local_homeomorph.subtype_restr_source -> LocalHomeomorph.subtypeRestr_source is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (s : TopologicalSpace.Opens.{u1} α _inst_1) [_inst_5 : Nonempty.{succ u1} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s)], Eq.{succ u1} (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s)) (LocalEquiv.source.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s) β (LocalHomeomorph.toLocalEquiv.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) x s) _inst_1) _inst_2 (LocalHomeomorph.subtypeRestr.{u1, u2} α β _inst_1 _inst_2 e s _inst_5))) (Set.preimage.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) x s)))))) (LocalEquiv.source.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 e)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (s : TopologicalSpace.Opens.{u2} α _inst_1) [_inst_5 : Nonempty.{succ u2} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s))], Eq.{succ u2} (Set.{u2} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s))) (LocalEquiv.source.{u2, u1} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s)) β (LocalHomeomorph.toLocalEquiv.{u2, u1} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s)) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s) _inst_1) _inst_2 (LocalHomeomorph.subtypeRestr.{u2, u1} α β _inst_1 _inst_2 e s _inst_5))) (Set.preimage.{u2, u2} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s)) α (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (SetLike.coe.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1) s))) (LocalEquiv.source.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 e)))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.subtype_restr_source LocalHomeomorph.subtypeRestr_sourceₓ'. -/
@[simp, mfld_simps]
theorem subtypeRestr_source : (e.subtypeRestr s).source = coe ⁻¹' e.source := by
  simp only [subtype_restr_def, mfld_simps]
#align local_homeomorph.subtype_restr_source LocalHomeomorph.subtypeRestr_source

/- warning: local_homeomorph.subtype_restr_symm_trans_subtype_restr -> LocalHomeomorph.subtypeRestr_symm_trans_subtypeRestr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (s : TopologicalSpace.Opens.{u1} α _inst_1) [_inst_5 : Nonempty.{succ u1} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s)] (f : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2) (f' : LocalHomeomorph.{u1, u2} α β _inst_1 _inst_2), HasEquivₓ.Equiv.{succ u2} (LocalHomeomorph.{u2, u2} β β _inst_2 _inst_2) (setoidHasEquiv.{succ u2} (LocalHomeomorph.{u2, u2} β β _inst_2 _inst_2) (LocalHomeomorph.setoid.{u2, u2} β β _inst_2 _inst_2)) (LocalHomeomorph.trans.{u2, u1, u2} β (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s) β _inst_2 (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) x s) _inst_1) _inst_2 (LocalHomeomorph.symm.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (TopologicalSpace.Opens.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) x s) _inst_1) _inst_2 (LocalHomeomorph.subtypeRestr.{u1, u2} α β _inst_1 _inst_2 f s _inst_5)) (LocalHomeomorph.subtypeRestr.{u1, u2} α β _inst_1 _inst_2 f' s _inst_5)) (LocalHomeomorph.restr.{u2, u2} β β _inst_2 _inst_2 (LocalHomeomorph.trans.{u2, u1, u2} β α β _inst_2 _inst_1 _inst_2 (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 f) f') (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalHomeomorph.toLocalEquiv.{u1, u2} α β _inst_1 _inst_2 f)) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : LocalHomeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (LocalHomeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (LocalHomeomorph.symm.{u1, u2} α β _inst_1 _inst_2 f)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (s : TopologicalSpace.Opens.{u2} α _inst_1) [_inst_5 : Nonempty.{succ u2} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s))] (f : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2) (f' : LocalHomeomorph.{u2, u1} α β _inst_1 _inst_2), HasEquiv.Equiv.{succ u1, 0} (LocalHomeomorph.{u1, u1} β β _inst_2 _inst_2) (instHasEquiv.{succ u1} (LocalHomeomorph.{u1, u1} β β _inst_2 _inst_2) (LocalHomeomorph.eqOnSourceSetoid.{u1, u1} β β _inst_2 _inst_2)) (LocalHomeomorph.trans.{u1, u2, u1} β (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s)) β _inst_2 (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s) _inst_1) _inst_2 (LocalHomeomorph.symm.{u2, u1} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s)) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (TopologicalSpace.Opens.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) x s) _inst_1) _inst_2 (LocalHomeomorph.subtypeRestr.{u2, u1} α β _inst_1 _inst_2 f s _inst_5)) (LocalHomeomorph.subtypeRestr.{u2, u1} α β _inst_1 _inst_2 f' s _inst_5)) (LocalHomeomorph.restr.{u1, u1} β β _inst_2 _inst_2 (LocalHomeomorph.trans.{u1, u2, u1} β α β _inst_2 _inst_1 _inst_2 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 f) f') (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalHomeomorph.toLocalEquiv.{u2, u1} α β _inst_1 _inst_2 f)) (Set.preimage.{u1, u2} β α (LocalHomeomorph.toFun'.{u1, u2} β α _inst_2 _inst_1 (LocalHomeomorph.symm.{u2, u1} α β _inst_1 _inst_2 f)) (SetLike.coe.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1) s))))
Case conversion may be inaccurate. Consider using '#align local_homeomorph.subtype_restr_symm_trans_subtype_restr LocalHomeomorph.subtypeRestr_symm_trans_subtypeRestrₓ'. -/
/- This lemma characterizes the transition functions of an open subset in terms of the transition
functions of the original space. -/
theorem subtypeRestr_symm_trans_subtypeRestr (f f' : LocalHomeomorph α β) :
    (f.subtypeRestr s).symm.trans (f'.subtypeRestr s) ≈
      (f.symm.trans f').restr (f.target ∩ f.symm ⁻¹' s) :=
  by
  simp only [subtype_restr_def, trans_symm_eq_symm_trans_symm]
  have openness₁ : IsOpen (f.target ∩ f.symm ⁻¹' s) := f.preimage_open_of_open_symm s.2
  rw [← of_set_trans _ openness₁, ← trans_assoc, ← trans_assoc]
  refine' eq_on_source.trans' _ (eq_on_source_refl _)
  -- f' has been eliminated !!!
  have sets_identity : f.symm.source ∩ (f.target ∩ f.symm ⁻¹' s) = f.symm.source ∩ f.symm ⁻¹' s :=
    by mfld_set_tac
  have openness₂ : IsOpen (s : Set α) := s.2
  rw [of_set_trans', sets_identity, ← trans_of_set' _ openness₂, trans_assoc]
  refine' eq_on_source.trans' (eq_on_source_refl _) _
  -- f has been eliminated !!!
  refine' Setoid.trans (trans_symm_self s.local_homeomorph_subtype_coe) _
  simp only [mfld_simps]
#align local_homeomorph.subtype_restr_symm_trans_subtype_restr LocalHomeomorph.subtypeRestr_symm_trans_subtypeRestr

end LocalHomeomorph

