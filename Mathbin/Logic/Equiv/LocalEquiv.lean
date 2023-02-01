/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module logic.equiv.local_equiv
! leanprover-community/mathlib commit 59694bd07f0a39c5beccba34bd9f413a160782bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Function
import Mathbin.Logic.Equiv.Defs

/-!
# Local equivalences

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This files defines equivalences between subsets of given types.
An element `e` of `local_equiv α β` is made of two maps `e.to_fun` and `e.inv_fun` respectively
from α to β and from  β to α (just like equivs), which are inverse to each other on the subsets
`e.source` and `e.target` of respectively α and β.

They are designed in particular to define charts on manifolds.

The main functionality is `e.trans f`, which composes the two local equivalences by restricting
the source and target to the maximal set where the composition makes sense.

As for equivs, we register a coercion to functions and use it in our simp normal form: we write
`e x` and `e.symm y` instead of `e.to_fun x` and `e.inv_fun y`.

## Main definitions

`equiv.to_local_equiv`: associating a local equiv to an equiv, with source = target = univ
`local_equiv.symm`    : the inverse of a local equiv
`local_equiv.trans`   : the composition of two local equivs
`local_equiv.refl`    : the identity local equiv
`local_equiv.of_set`  : the identity on a set `s`
`eq_on_source`        : equivalence relation describing the "right" notion of equality for local
                        equivs (see below in implementation notes)

## Implementation notes

There are at least three possible implementations of local equivalences:
* equivs on subtypes
* pairs of functions taking values in `option α` and `option β`, equal to none where the local
equivalence is not defined
* pairs of functions defined everywhere, keeping the source and target as additional data

Each of these implementations has pros and cons.
* When dealing with subtypes, one still need to define additional API for composition and
restriction of domains. Checking that one always belongs to the right subtype makes things very
tedious, and leads quickly to DTT hell (as the subtype `u ∩ v` is not the "same" as `v ∩ u`, for
instance).
* With option-valued functions, the composition is very neat (it is just the usual composition, and
the domain is restricted automatically). These are implemented in `pequiv.lean`. For manifolds,
where one wants to discuss thoroughly the smoothness of the maps, this creates however a lot of
overhead as one would need to extend all classes of smoothness to option-valued maps.
* The local_equiv version as explained above is easier to use for manifolds. The drawback is that
there is extra useless data (the values of `to_fun` and `inv_fun` outside of `source` and `target`).
In particular, the equality notion between local equivs is not "the right one", i.e., coinciding
source and target and equality there. Moreover, there are no local equivs in this sense between
an empty type and a nonempty type. Since empty types are not that useful, and since one almost never
needs to talk about equal local equivs, this is not an issue in practice.
Still, we introduce an equivalence relation `eq_on_source` that captures this right notion of
equality, and show that many properties are invariant under this equivalence relation.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `local_equiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.

-/


/- failed to parenthesize: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
[PrettyPrinter.parenthesize.input] (Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr
     [(Command.docComment
       "/--"
       "The simpset `mfld_simps` records several simp lemmas that are\nespecially useful in manifolds. It is a subset of the whole set of simp lemmas, but it makes it\npossible to have quicker proofs (when used with `squeeze_simp` or `simp only`) while retaining\nreadability.\n\nThe typical use case is the following, in a file on manifolds:\nIf `simp [foo, bar]` is slow, replace it with `squeeze_simp [foo, bar] with mfld_simps` and paste\nits output. The list of lemmas should be reasonable (contrary to the output of\n`squeeze_simp [foo, bar]` which might contain tens of lemmas), and the outcome should be quick\nenough.\n -/")]
     "register_simp_attr"
     `mfld_simps)-/-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/--
    The simpset `mfld_simps` records several simp lemmas that are
    especially useful in manifolds. It is a subset of the whole set of simp lemmas, but it makes it
    possible to have quicker proofs (when used with `squeeze_simp` or `simp only`) while retaining
    readability.
    
    The typical use case is the following, in a file on manifolds:
    If `simp [foo, bar]` is slow, replace it with `squeeze_simp [foo, bar] with mfld_simps` and paste
    its output. The list of lemmas should be reasonable (contrary to the output of
    `squeeze_simp [foo, bar]` which might contain tens of lemmas), and the outcome should be quick
    enough.
     -/
  register_simp_attr
  mfld_simps

-- register in the simpset `mfld_simps` several lemmas that are often useful when dealing
-- with manifolds
attribute [mfld_simps]
  id.def Function.comp.left_id Set.mem_setOf_eq Set.image_eq_empty Set.univ_inter Set.preimage_univ Set.prod_mk_mem_set_prod_eq and_true_iff Set.mem_univ Set.mem_image_of_mem true_and_iff Set.mem_inter_iff Set.mem_preimage Function.comp_apply Set.inter_subset_left Set.mem_prod Set.range_id Set.range_prod_map and_self_iff Set.mem_range_self eq_self_iff_true forall_const forall_true_iff Set.inter_univ Set.preimage_id Function.comp.right_id not_false_iff and_imp Set.prod_inter_prod Set.univ_prod_univ true_or_iff or_true_iff Prod.map_mk Set.preimage_inter heq_iff_eq Equiv.sigmaEquivProd_apply Equiv.sigmaEquivProd_symm_apply Subtype.coe_mk Equiv.toFun_as_coe Equiv.invFun_as_coe

/- warning: mfld_cfg -> mfld_cfg is a dubious translation:
lean 3 declaration is
  SimpsCfg
but is expected to have type
  Simps.Config
Case conversion may be inaccurate. Consider using '#align mfld_cfg mfld_cfgₓ'. -/
/-- Common `@[simps]` configuration options used for manifold-related declarations. -/
def mfld_cfg : SimpsCfg where
  attrs := [`simp, `mfld_simps]
  fullyApplied := false
#align mfld_cfg mfld_cfg

namespace Tactic.Interactive

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      A very basic tactic to show that sets showing up in manifolds coincide or are included in
      one another. -/
    unsafe
  def
    mfld_set_tac
    : tactic Unit
    :=
      do
        let goal ← tactic.target
          match
            goal
            with
            | q( $ ( e₁ ) = $ ( e₂ ) ) => sorry
              | q( $ ( e₁ ) ⊆ $ ( e₂ ) ) => sorry
              | _ => tactic.fail "goal should be an equality or an inclusion"
#align tactic.interactive.mfld_set_tac tactic.interactive.mfld_set_tac

end Tactic.Interactive

open Function Set

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

#print LocalEquiv /-
/-- Local equivalence between subsets `source` and `target` of α and β respectively. The (global)
maps `to_fun : α → β` and `inv_fun : β → α` map `source` to `target` and conversely, and are inverse
to each other there. The values of `to_fun` outside of `source` and of `inv_fun` outside of `target`
are irrelevant. -/
structure LocalEquiv (α : Type _) (β : Type _) where
  toFun : α → β
  invFun : β → α
  source : Set α
  target : Set β
  map_source' : ∀ ⦃x⦄, x ∈ source → to_fun x ∈ target
  map_target' : ∀ ⦃x⦄, x ∈ target → inv_fun x ∈ source
  left_inv' : ∀ ⦃x⦄, x ∈ source → inv_fun (to_fun x) = x
  right_inv' : ∀ ⦃x⦄, x ∈ target → to_fun (inv_fun x) = x
#align local_equiv LocalEquiv
-/

namespace LocalEquiv

variable (e : LocalEquiv α β) (e' : LocalEquiv β γ)

instance [Inhabited α] [Inhabited β] : Inhabited (LocalEquiv α β) :=
  ⟨⟨const α default, const β default, ∅, ∅, mapsTo_empty _ _, mapsTo_empty _ _, eqOn_empty _ _,
      eqOn_empty _ _⟩⟩

#print LocalEquiv.symm /-
/-- The inverse of a local equiv -/
protected def symm : LocalEquiv β α where
  toFun := e.invFun
  invFun := e.toFun
  source := e.target
  target := e.source
  map_source' := e.map_target'
  map_target' := e.map_source'
  left_inv' := e.right_inv'
  right_inv' := e.left_inv'
#align local_equiv.symm LocalEquiv.symm
-/

instance : CoeFun (LocalEquiv α β) fun _ => α → β :=
  ⟨LocalEquiv.toFun⟩

#print LocalEquiv.Simps.symmApply /-
/-- See Note [custom simps projection] -/
def Simps.symmApply (e : LocalEquiv α β) : β → α :=
  e.symm
#align local_equiv.simps.symm_apply LocalEquiv.Simps.symmApply
-/

initialize_simps_projections LocalEquiv (toFun → apply, invFun → symm_apply)

/- warning: local_equiv.coe_mk clashes with [anonymous] -> [anonymous]
warning: local_equiv.coe_mk -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (g : β -> α) (s : Set.{u1} α) (t : Set.{u2} β) (ml : forall {{x : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) t)) (mr : forall {{x : β}}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (g x) s)) (il : forall {{x : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Eq.{succ u1} α (g (f x)) x)) (ir : forall {{x : β}}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) -> (Eq.{succ u2} β (f (g x)) x)), Eq.{max (succ u1) (succ u2)} ((fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.mk.{u1, u2} α β f g s t ml mr il ir)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) (LocalEquiv.mk.{u1, u2} α β f g s t ml mr il ir)) f
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (Nat -> α -> β) -> Nat -> (List.{u1} α) -> (List.{u2} β)
Case conversion may be inaccurate. Consider using '#align local_equiv.coe_mk [anonymous]ₓ'. -/
@[simp, mfld_simps]
theorem [anonymous] (f : α → β) (g s t ml mr il ir) :
    (LocalEquiv.mk f g s t ml mr il ir : α → β) = f :=
  rfl
#align local_equiv.coe_mk [anonymous]

/- warning: local_equiv.coe_symm_mk -> LocalEquiv.coe_symm_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (g : β -> α) (s : Set.{u1} α) (t : Set.{u2} β) (ml : forall {{x : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) t)) (mr : forall {{x : β}}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (g x) s)) (il : forall {{x : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Eq.{succ u1} α (g (f x)) x)) (ir : forall {{x : β}}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) -> (Eq.{succ u2} β (f (g x)) x)), Eq.{max (succ u2) (succ u1)} ((fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.symm.{u1, u2} α β (LocalEquiv.mk.{u1, u2} α β f g s t ml mr il ir))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β (LocalEquiv.mk.{u1, u2} α β f g s t ml mr il ir))) g
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (g : β -> α) (s : Set.{u2} α) (t : Set.{u1} β) (ml : forall {{x : α}}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f x) t)) (mr : forall {{x : β}}, (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x t) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (g x) s)) (il : forall {{x : α}}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Eq.{succ u2} α (g (f x)) x)) (ir : forall {{x : β}}, (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x t) -> (Eq.{succ u1} β (f (g x)) x)), Eq.{max (succ u2) (succ u1)} (β -> α) (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β (LocalEquiv.mk.{u2, u1} α β f g s t ml mr il ir))) g
Case conversion may be inaccurate. Consider using '#align local_equiv.coe_symm_mk LocalEquiv.coe_symm_mkₓ'. -/
@[simp, mfld_simps]
theorem coe_symm_mk (f : α → β) (g s t ml mr il ir) :
    ((LocalEquiv.mk f g s t ml mr il ir).symm : β → α) = g :=
  rfl
#align local_equiv.coe_symm_mk LocalEquiv.coe_symm_mk

/- warning: local_equiv.to_fun_as_coe clashes with [anonymous] -> [anonymous]
warning: local_equiv.to_fun_as_coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β), Eq.{max (succ u1) (succ u2)} (α -> β) (LocalEquiv.toFun.{u1, u2} α β e) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (Nat -> α -> β) -> Nat -> (List.{u1} α) -> (List.{u2} β)
Case conversion may be inaccurate. Consider using '#align local_equiv.to_fun_as_coe [anonymous]ₓ'. -/
@[simp, mfld_simps]
theorem [anonymous] : e.toFun = e :=
  rfl
#align local_equiv.to_fun_as_coe [anonymous]

/- warning: local_equiv.inv_fun_as_coe -> LocalEquiv.invFun_as_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β), Eq.{max (succ u2) (succ u1)} (β -> α) (LocalEquiv.invFun.{u1, u2} α β e) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β), Eq.{max (succ u2) (succ u1)} (β -> α) (LocalEquiv.invFun.{u2, u1} α β e) (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e))
Case conversion may be inaccurate. Consider using '#align local_equiv.inv_fun_as_coe LocalEquiv.invFun_as_coeₓ'. -/
@[simp, mfld_simps]
theorem invFun_as_coe : e.invFun = e.symm :=
  rfl
#align local_equiv.inv_fun_as_coe LocalEquiv.invFun_as_coe

/- warning: local_equiv.map_source -> LocalEquiv.map_source is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β e)) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e x) (LocalEquiv.target.{u1, u2} α β e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β) {x : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β e)) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (LocalEquiv.toFun.{u2, u1} α β e x) (LocalEquiv.target.{u2, u1} α β e))
Case conversion may be inaccurate. Consider using '#align local_equiv.map_source LocalEquiv.map_sourceₓ'. -/
@[simp, mfld_simps]
theorem map_source {x : α} (h : x ∈ e.source) : e x ∈ e.target :=
  e.map_source' h
#align local_equiv.map_source LocalEquiv.map_source

#print LocalEquiv.map_target /-
@[simp, mfld_simps]
theorem map_target {x : β} (h : x ∈ e.target) : e.symm x ∈ e.source :=
  e.map_target' h
#align local_equiv.map_target LocalEquiv.map_target
-/

/- warning: local_equiv.left_inv -> LocalEquiv.left_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β e)) -> (Eq.{succ u1} α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e x)) x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β) {x : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β e)) -> (Eq.{succ u2} α (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e) (LocalEquiv.toFun.{u2, u1} α β e x)) x)
Case conversion may be inaccurate. Consider using '#align local_equiv.left_inv LocalEquiv.left_invₓ'. -/
@[simp, mfld_simps]
theorem left_inv {x : α} (h : x ∈ e.source) : e.symm (e x) = x :=
  e.left_inv' h
#align local_equiv.left_inv LocalEquiv.left_inv

#print LocalEquiv.right_inv /-
@[simp, mfld_simps]
theorem right_inv {x : β} (h : x ∈ e.target) : e (e.symm x) = x :=
  e.right_inv' h
#align local_equiv.right_inv LocalEquiv.right_inv
-/

/- warning: local_equiv.eq_symm_apply -> LocalEquiv.eq_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) {x : α} {y : β}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β e)) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (LocalEquiv.target.{u1, u2} α β e)) -> (Iff (Eq.{succ u1} α x (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e) y)) (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e x) y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β) {x : α} {y : β}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β e)) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (LocalEquiv.target.{u2, u1} α β e)) -> (Iff (Eq.{succ u2} α x (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e) y)) (Eq.{succ u1} β (LocalEquiv.toFun.{u2, u1} α β e x) y))
Case conversion may be inaccurate. Consider using '#align local_equiv.eq_symm_apply LocalEquiv.eq_symm_applyₓ'. -/
theorem eq_symm_apply {x : α} {y : β} (hx : x ∈ e.source) (hy : y ∈ e.target) :
    x = e.symm y ↔ e x = y :=
  ⟨fun h => by rw [← e.right_inv hy, h], fun h => by rw [← e.left_inv hx, h]⟩
#align local_equiv.eq_symm_apply LocalEquiv.eq_symm_apply

/- warning: local_equiv.maps_to -> LocalEquiv.mapsTo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β), Set.MapsTo.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (LocalEquiv.source.{u1, u2} α β e) (LocalEquiv.target.{u1, u2} α β e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β), Set.MapsTo.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e) (LocalEquiv.source.{u2, u1} α β e) (LocalEquiv.target.{u2, u1} α β e)
Case conversion may be inaccurate. Consider using '#align local_equiv.maps_to LocalEquiv.mapsToₓ'. -/
protected theorem mapsTo : MapsTo e e.source e.target := fun x => e.map_source
#align local_equiv.maps_to LocalEquiv.mapsTo

#print LocalEquiv.symm_mapsTo /-
theorem symm_mapsTo : MapsTo e.symm e.target e.source :=
  e.symm.MapsTo
#align local_equiv.symm_maps_to LocalEquiv.symm_mapsTo
-/

/- warning: local_equiv.left_inv_on -> LocalEquiv.leftInvOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β), Set.LeftInvOn.{u1, u2} α β (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (LocalEquiv.source.{u1, u2} α β e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β), Set.LeftInvOn.{u2, u1} α β (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) (LocalEquiv.toFun.{u2, u1} α β e) (LocalEquiv.source.{u2, u1} α β e)
Case conversion may be inaccurate. Consider using '#align local_equiv.left_inv_on LocalEquiv.leftInvOnₓ'. -/
protected theorem leftInvOn : LeftInvOn e.symm e e.source := fun x => e.left_inv
#align local_equiv.left_inv_on LocalEquiv.leftInvOn

/- warning: local_equiv.right_inv_on -> LocalEquiv.rightInvOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β), Set.RightInvOn.{u1, u2} α β (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (LocalEquiv.target.{u1, u2} α β e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β), Set.RightInvOn.{u2, u1} α β (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) (LocalEquiv.toFun.{u2, u1} α β e) (LocalEquiv.target.{u2, u1} α β e)
Case conversion may be inaccurate. Consider using '#align local_equiv.right_inv_on LocalEquiv.rightInvOnₓ'. -/
protected theorem rightInvOn : RightInvOn e.symm e e.target := fun x => e.right_inv
#align local_equiv.right_inv_on LocalEquiv.rightInvOn

/- warning: local_equiv.inv_on -> LocalEquiv.invOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β), Set.InvOn.{u1, u2} α β (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (LocalEquiv.source.{u1, u2} α β e) (LocalEquiv.target.{u1, u2} α β e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β), Set.InvOn.{u2, u1} α β (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) (LocalEquiv.toFun.{u2, u1} α β e) (LocalEquiv.source.{u2, u1} α β e) (LocalEquiv.target.{u2, u1} α β e)
Case conversion may be inaccurate. Consider using '#align local_equiv.inv_on LocalEquiv.invOnₓ'. -/
protected theorem invOn : InvOn e.symm e e.source e.target :=
  ⟨e.LeftInvOn, e.RightInvOn⟩
#align local_equiv.inv_on LocalEquiv.invOn

/- warning: local_equiv.inj_on -> LocalEquiv.injOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β), Set.InjOn.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (LocalEquiv.source.{u1, u2} α β e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β), Set.InjOn.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e) (LocalEquiv.source.{u2, u1} α β e)
Case conversion may be inaccurate. Consider using '#align local_equiv.inj_on LocalEquiv.injOnₓ'. -/
protected theorem injOn : InjOn e e.source :=
  e.LeftInvOn.InjOn
#align local_equiv.inj_on LocalEquiv.injOn

/- warning: local_equiv.bij_on -> LocalEquiv.bijOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β), Set.BijOn.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (LocalEquiv.source.{u1, u2} α β e) (LocalEquiv.target.{u1, u2} α β e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β), Set.BijOn.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e) (LocalEquiv.source.{u2, u1} α β e) (LocalEquiv.target.{u2, u1} α β e)
Case conversion may be inaccurate. Consider using '#align local_equiv.bij_on LocalEquiv.bijOnₓ'. -/
protected theorem bijOn : BijOn e e.source e.target :=
  e.InvOn.BijOn e.MapsTo e.symm_mapsTo
#align local_equiv.bij_on LocalEquiv.bijOn

/- warning: local_equiv.surj_on -> LocalEquiv.surjOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β), Set.SurjOn.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (LocalEquiv.source.{u1, u2} α β e) (LocalEquiv.target.{u1, u2} α β e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β), Set.SurjOn.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e) (LocalEquiv.source.{u2, u1} α β e) (LocalEquiv.target.{u2, u1} α β e)
Case conversion may be inaccurate. Consider using '#align local_equiv.surj_on LocalEquiv.surjOnₓ'. -/
protected theorem surjOn : SurjOn e e.source e.target :=
  e.BijOn.SurjOn
#align local_equiv.surj_on LocalEquiv.surjOn

#print Equiv.toLocalEquiv /-
/-- Associating a local_equiv to an equiv-/
@[simps (config := mfld_cfg)]
def Equiv.toLocalEquiv (e : α ≃ β) : LocalEquiv α β
    where
  toFun := e
  invFun := e.symm
  source := univ
  target := univ
  map_source' x hx := mem_univ _
  map_target' y hy := mem_univ _
  left_inv' x hx := e.left_inv x
  right_inv' x hx := e.right_inv x
#align equiv.to_local_equiv Equiv.toLocalEquiv
-/

#print LocalEquiv.inhabitedOfEmpty /-
instance inhabitedOfEmpty [IsEmpty α] [IsEmpty β] : Inhabited (LocalEquiv α β) :=
  ⟨((Equiv.equivEmpty α).trans (Equiv.equivEmpty β).symm).toLocalEquiv⟩
#align local_equiv.inhabited_of_empty LocalEquiv.inhabitedOfEmpty
-/

#print LocalEquiv.copy /-
/-- Create a copy of a `local_equiv` providing better definitional equalities. -/
@[simps (config := { fullyApplied := false })]
def copy (e : LocalEquiv α β) (f : α → β) (hf : ⇑e = f) (g : β → α) (hg : ⇑e.symm = g) (s : Set α)
    (hs : e.source = s) (t : Set β) (ht : e.target = t) : LocalEquiv α β
    where
  toFun := f
  invFun := g
  source := s
  target := t
  map_source' x := ht ▸ hs ▸ hf ▸ e.map_source
  map_target' y := hs ▸ ht ▸ hg ▸ e.map_target
  left_inv' x := hs ▸ hf ▸ hg ▸ e.left_inv
  right_inv' x := ht ▸ hf ▸ hg ▸ e.right_inv
#align local_equiv.copy LocalEquiv.copy
-/

/- warning: local_equiv.copy_eq -> LocalEquiv.copy_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (f : α -> β) (hf : Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (e : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) f) (g : β -> α) (hg : Eq.{max (succ u2) (succ u1)} (β -> α) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) g) (s : Set.{u1} α) (hs : Eq.{succ u1} (Set.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s) (t : Set.{u2} β) (ht : Eq.{succ u2} (Set.{u2} β) (LocalEquiv.target.{u1, u2} α β e) t), Eq.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.copy.{u1, u2} α β e f hf g hg s hs t ht) e
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β) (f : α -> β) (hf : Eq.{max (succ u2) (succ u1)} (α -> β) (LocalEquiv.toFun.{u2, u1} α β e) f) (g : β -> α) (hg : Eq.{max (succ u2) (succ u1)} (β -> α) (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) g) (s : Set.{u2} α) (hs : Eq.{succ u2} (Set.{u2} α) (LocalEquiv.source.{u2, u1} α β e) s) (t : Set.{u1} β) (ht : Eq.{succ u1} (Set.{u1} β) (LocalEquiv.target.{u2, u1} α β e) t), Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalEquiv.copy.{u2, u1} α β e f hf g hg s hs t ht) e
Case conversion may be inaccurate. Consider using '#align local_equiv.copy_eq LocalEquiv.copy_eqₓ'. -/
theorem copy_eq (e : LocalEquiv α β) (f : α → β) (hf : ⇑e = f) (g : β → α) (hg : ⇑e.symm = g)
    (s : Set α) (hs : e.source = s) (t : Set β) (ht : e.target = t) :
    e.copy f hf g hg s hs t ht = e := by
  substs f g s t
  cases e
  rfl
#align local_equiv.copy_eq LocalEquiv.copy_eq

#print LocalEquiv.toEquiv /-
/-- Associating to a local_equiv an equiv between the source and the target -/
protected def toEquiv : Equiv e.source e.target
    where
  toFun x := ⟨e x, e.map_source x.Mem⟩
  invFun y := ⟨e.symm y, e.map_target y.Mem⟩
  left_inv := fun ⟨x, hx⟩ => Subtype.eq <| e.left_inv hx
  right_inv := fun ⟨y, hy⟩ => Subtype.eq <| e.right_inv hy
#align local_equiv.to_equiv LocalEquiv.toEquiv
-/

#print LocalEquiv.symm_source /-
@[simp, mfld_simps]
theorem symm_source : e.symm.source = e.target :=
  rfl
#align local_equiv.symm_source LocalEquiv.symm_source
-/

/- warning: local_equiv.symm_target -> LocalEquiv.symm_target is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β), Eq.{succ u1} (Set.{u1} α) (LocalEquiv.target.{u2, u1} β α (LocalEquiv.symm.{u1, u2} α β e)) (LocalEquiv.source.{u1, u2} α β e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β), Eq.{succ u2} (Set.{u2} α) (LocalEquiv.target.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) (LocalEquiv.source.{u2, u1} α β e)
Case conversion may be inaccurate. Consider using '#align local_equiv.symm_target LocalEquiv.symm_targetₓ'. -/
@[simp, mfld_simps]
theorem symm_target : e.symm.target = e.source :=
  rfl
#align local_equiv.symm_target LocalEquiv.symm_target

/- warning: local_equiv.symm_symm -> LocalEquiv.symm_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β), Eq.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.symm.{u2, u1} β α (LocalEquiv.symm.{u1, u2} α β e)) e
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β), Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalEquiv.symm.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) e
Case conversion may be inaccurate. Consider using '#align local_equiv.symm_symm LocalEquiv.symm_symmₓ'. -/
@[simp, mfld_simps]
theorem symm_symm : e.symm.symm = e := by
  cases e
  rfl
#align local_equiv.symm_symm LocalEquiv.symm_symm

#print LocalEquiv.image_source_eq_target /-
theorem image_source_eq_target : e '' e.source = e.target :=
  e.BijOn.image_eq
#align local_equiv.image_source_eq_target LocalEquiv.image_source_eq_target
-/

#print LocalEquiv.forall_mem_target /-
theorem forall_mem_target {p : β → Prop} : (∀ y ∈ e.target, p y) ↔ ∀ x ∈ e.source, p (e x) := by
  rw [← image_source_eq_target, ball_image_iff]
#align local_equiv.forall_mem_target LocalEquiv.forall_mem_target
-/

/- warning: local_equiv.exists_mem_target -> LocalEquiv.exists_mem_target is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) {p : β -> Prop}, Iff (Exists.{succ u2} β (fun (y : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (LocalEquiv.target.{u1, u2} α β e)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (LocalEquiv.target.{u1, u2} α β e)) => p y))) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β e)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β e)) => p (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) {p : β -> Prop}, Iff (Exists.{succ u2} β (fun (y : β) => And (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) y (LocalEquiv.target.{u1, u2} α β e)) (p y))) (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (LocalEquiv.source.{u1, u2} α β e)) (p (LocalEquiv.toFun.{u1, u2} α β e x))))
Case conversion may be inaccurate. Consider using '#align local_equiv.exists_mem_target LocalEquiv.exists_mem_targetₓ'. -/
theorem exists_mem_target {p : β → Prop} : (∃ y ∈ e.target, p y) ↔ ∃ x ∈ e.source, p (e x) := by
  rw [← image_source_eq_target, bex_image_iff]
#align local_equiv.exists_mem_target LocalEquiv.exists_mem_target

#print LocalEquiv.IsImage /-
/-- We say that `t : set β` is an image of `s : set α` under a local equivalence if
any of the following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
-/
def IsImage (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)
#align local_equiv.is_image LocalEquiv.IsImage
-/

namespace IsImage

variable {e} {s : Set α} {t : Set β} {x : α} {y : β}

/- warning: local_equiv.is_image.apply_mem_iff -> LocalEquiv.IsImage.apply_mem_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β} {x : α}, (LocalEquiv.IsImage.{u1, u2} α β e s t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β e)) -> (Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e x) t) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β} {x : α}, (LocalEquiv.IsImage.{u2, u1} α β e s t) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β e)) -> (Iff (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (LocalEquiv.toFun.{u2, u1} α β e x) t) (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s))
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.apply_mem_iff LocalEquiv.IsImage.apply_mem_iffₓ'. -/
theorem apply_mem_iff (h : e.IsImage s t) (hx : x ∈ e.source) : e x ∈ t ↔ x ∈ s :=
  h hx
#align local_equiv.is_image.apply_mem_iff LocalEquiv.IsImage.apply_mem_iff

/- warning: local_equiv.is_image.symm_apply_mem_iff -> LocalEquiv.IsImage.symm_apply_mem_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalEquiv.IsImage.{u1, u2} α β e s t) -> (forall {{y : β}}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (LocalEquiv.target.{u1, u2} α β e)) -> (Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e) y) s) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalEquiv.IsImage.{u2, u1} α β e s t) -> (forall {{y : β}}, (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (LocalEquiv.target.{u2, u1} α β e)) -> (Iff (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e) y) s) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y t)))
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.symm_apply_mem_iff LocalEquiv.IsImage.symm_apply_mem_iffₓ'. -/
theorem symm_apply_mem_iff (h : e.IsImage s t) : ∀ ⦃y⦄, y ∈ e.target → (e.symm y ∈ s ↔ y ∈ t) :=
  e.forall_mem_target.mpr fun x hx => by rw [e.left_inv hx, h hx]
#align local_equiv.is_image.symm_apply_mem_iff LocalEquiv.IsImage.symm_apply_mem_iff

/- warning: local_equiv.is_image.symm -> LocalEquiv.IsImage.symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalEquiv.IsImage.{u1, u2} α β e s t) -> (LocalEquiv.IsImage.{u2, u1} β α (LocalEquiv.symm.{u1, u2} α β e) t s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalEquiv.IsImage.{u2, u1} α β e s t) -> (LocalEquiv.IsImage.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e) t s)
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.symm LocalEquiv.IsImage.symmₓ'. -/
protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
  h.symm_apply_mem_iff
#align local_equiv.is_image.symm LocalEquiv.IsImage.symm

#print LocalEquiv.IsImage.symm_iff /-
@[simp]
theorem symm_iff : e.symm.IsImage t s ↔ e.IsImage s t :=
  ⟨fun h => h.symm, fun h => h.symm⟩
#align local_equiv.is_image.symm_iff LocalEquiv.IsImage.symm_iff
-/

/- warning: local_equiv.is_image.maps_to -> LocalEquiv.IsImage.mapsTo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalEquiv.IsImage.{u1, u2} α β e s t) -> (Set.MapsTo.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalEquiv.IsImage.{u2, u1} α β e s t) -> (Set.MapsTo.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) s) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β e) t))
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.maps_to LocalEquiv.IsImage.mapsToₓ'. -/
protected theorem mapsTo (h : e.IsImage s t) : MapsTo e (e.source ∩ s) (e.target ∩ t) := fun x hx =>
  ⟨e.MapsTo hx.1, (h hx.1).2 hx.2⟩
#align local_equiv.is_image.maps_to LocalEquiv.IsImage.mapsTo

/- warning: local_equiv.is_image.symm_maps_to -> LocalEquiv.IsImage.symm_mapsTo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalEquiv.IsImage.{u1, u2} α β e s t) -> (Set.MapsTo.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalEquiv.IsImage.{u2, u1} α β e s t) -> (Set.MapsTo.{u1, u2} β α (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β e) t) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) s))
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.symm_maps_to LocalEquiv.IsImage.symm_mapsToₓ'. -/
theorem symm_mapsTo (h : e.IsImage s t) : MapsTo e.symm (e.target ∩ t) (e.source ∩ s) :=
  h.symm.MapsTo
#align local_equiv.is_image.symm_maps_to LocalEquiv.IsImage.symm_mapsTo

#print LocalEquiv.IsImage.restr /-
/-- Restrict a `local_equiv` to a pair of corresponding sets. -/
@[simps (config := { fullyApplied := false })]
def restr (h : e.IsImage s t) : LocalEquiv α β
    where
  toFun := e
  invFun := e.symm
  source := e.source ∩ s
  target := e.target ∩ t
  map_source' := h.MapsTo
  map_target' := h.symm_mapsTo
  left_inv' := e.LeftInvOn.mono (inter_subset_left _ _)
  right_inv' := e.RightInvOn.mono (inter_subset_left _ _)
#align local_equiv.is_image.restr LocalEquiv.IsImage.restr
-/

/- warning: local_equiv.is_image.image_eq -> LocalEquiv.IsImage.image_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalEquiv.IsImage.{u1, u2} α β e s t) -> (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalEquiv.IsImage.{u2, u1} α β e s t) -> (Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) s)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β e) t))
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.image_eq LocalEquiv.IsImage.image_eqₓ'. -/
theorem image_eq (h : e.IsImage s t) : e '' (e.source ∩ s) = e.target ∩ t :=
  h.restr.image_source_eq_target
#align local_equiv.is_image.image_eq LocalEquiv.IsImage.image_eq

/- warning: local_equiv.is_image.symm_image_eq -> LocalEquiv.IsImage.symm_image_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalEquiv.IsImage.{u1, u2} α β e s t) -> (Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalEquiv.IsImage.{u2, u1} α β e s t) -> (Eq.{succ u2} (Set.{u2} α) (Set.image.{u1, u2} β α (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β e) t)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) s))
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.symm_image_eq LocalEquiv.IsImage.symm_image_eqₓ'. -/
theorem symm_image_eq (h : e.IsImage s t) : e.symm '' (e.target ∩ t) = e.source ∩ s :=
  h.symm.image_eq
#align local_equiv.is_image.symm_image_eq LocalEquiv.IsImage.symm_image_eq

/- warning: local_equiv.is_image.iff_preimage_eq -> LocalEquiv.IsImage.iff_preimage_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β}, Iff (LocalEquiv.IsImage.{u1, u2} α β e s t) (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β}, Iff (LocalEquiv.IsImage.{u2, u1} α β e s t) (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) (Set.preimage.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e) t)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) s))
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.iff_preimage_eq LocalEquiv.IsImage.iff_preimage_eqₓ'. -/
theorem iff_preimage_eq : e.IsImage s t ↔ e.source ∩ e ⁻¹' t = e.source ∩ s := by
  simp only [is_image, Set.ext_iff, mem_inter_iff, and_congr_right_iff, mem_preimage]
#align local_equiv.is_image.iff_preimage_eq LocalEquiv.IsImage.iff_preimage_eq

/- warning: local_equiv.is_image.preimage_eq -> LocalEquiv.IsImage.preimage_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalEquiv.IsImage.{u1, u2} α β e s t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalEquiv.IsImage.{u2, u1} α β e s t) -> (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) (Set.preimage.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e) t)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) s))
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.preimage_eq LocalEquiv.IsImage.preimage_eqₓ'. -/
/- warning: local_equiv.is_image.of_preimage_eq -> LocalEquiv.IsImage.of_preimage_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β}, (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s)) -> (LocalEquiv.IsImage.{u1, u2} α β e s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β}, (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) (Set.preimage.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e) t)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) s)) -> (LocalEquiv.IsImage.{u2, u1} α β e s t)
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.of_preimage_eq LocalEquiv.IsImage.of_preimage_eqₓ'. -/
alias iff_preimage_eq ↔ preimage_eq of_preimage_eq
#align local_equiv.is_image.preimage_eq LocalEquiv.IsImage.preimage_eq
#align local_equiv.is_image.of_preimage_eq LocalEquiv.IsImage.of_preimage_eq

/- warning: local_equiv.is_image.iff_symm_preimage_eq -> LocalEquiv.IsImage.iff_symm_preimage_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β}, Iff (LocalEquiv.IsImage.{u1, u2} α β e s t) (Eq.{succ u2} (Set.{u2} β) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) s)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β}, Iff (LocalEquiv.IsImage.{u2, u1} α β e s t) (Eq.{succ u1} (Set.{u1} β) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β e) (Set.preimage.{u1, u2} β α (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) s)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β e) t))
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.iff_symm_preimage_eq LocalEquiv.IsImage.iff_symm_preimage_eqₓ'. -/
theorem iff_symm_preimage_eq : e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' s = e.target ∩ t :=
  symm_iff.symm.trans iff_preimage_eq
#align local_equiv.is_image.iff_symm_preimage_eq LocalEquiv.IsImage.iff_symm_preimage_eq

/- warning: local_equiv.is_image.symm_preimage_eq -> LocalEquiv.IsImage.symm_preimage_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalEquiv.IsImage.{u1, u2} α β e s t) -> (Eq.{succ u2} (Set.{u2} β) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) s)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalEquiv.IsImage.{u2, u1} α β e s t) -> (Eq.{succ u1} (Set.{u1} β) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β e) (Set.preimage.{u1, u2} β α (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) s)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β e) t))
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.symm_preimage_eq LocalEquiv.IsImage.symm_preimage_eqₓ'. -/
/- warning: local_equiv.is_image.of_symm_preimage_eq -> LocalEquiv.IsImage.of_symm_preimage_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β}, (Eq.{succ u2} (Set.{u2} β) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) s)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) t)) -> (LocalEquiv.IsImage.{u1, u2} α β e s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β}, (Eq.{succ u1} (Set.{u1} β) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β e) (Set.preimage.{u1, u2} β α (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) s)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β e) t)) -> (LocalEquiv.IsImage.{u2, u1} α β e s t)
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.of_symm_preimage_eq LocalEquiv.IsImage.of_symm_preimage_eqₓ'. -/
alias iff_symm_preimage_eq ↔ symm_preimage_eq of_symm_preimage_eq
#align local_equiv.is_image.symm_preimage_eq LocalEquiv.IsImage.symm_preimage_eq
#align local_equiv.is_image.of_symm_preimage_eq LocalEquiv.IsImage.of_symm_preimage_eq

/- warning: local_equiv.is_image.of_image_eq -> LocalEquiv.IsImage.of_image_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β}, (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) t)) -> (LocalEquiv.IsImage.{u1, u2} α β e s t)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β}, (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (LocalEquiv.toFun.{u1, u2} α β e) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s)) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (LocalEquiv.target.{u1, u2} α β e) t)) -> (LocalEquiv.IsImage.{u1, u2} α β e s t)
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.of_image_eq LocalEquiv.IsImage.of_image_eqₓ'. -/
theorem of_image_eq (h : e '' (e.source ∩ s) = e.target ∩ t) : e.IsImage s t :=
  of_symm_preimage_eq <| Eq.trans (of_symm_preimage_eq rfl).image_eq.symm h
#align local_equiv.is_image.of_image_eq LocalEquiv.IsImage.of_image_eq

/- warning: local_equiv.is_image.of_symm_image_eq -> LocalEquiv.IsImage.of_symm_image_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β}, (Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s)) -> (LocalEquiv.IsImage.{u1, u2} α β e s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β}, (Eq.{succ u2} (Set.{u2} α) (Set.image.{u1, u2} β α (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β e) t)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) s)) -> (LocalEquiv.IsImage.{u2, u1} α β e s t)
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.of_symm_image_eq LocalEquiv.IsImage.of_symm_image_eqₓ'. -/
theorem of_symm_image_eq (h : e.symm '' (e.target ∩ t) = e.source ∩ s) : e.IsImage s t :=
  of_preimage_eq <| Eq.trans (of_preimage_eq rfl).symm_image_eq.symm h
#align local_equiv.is_image.of_symm_image_eq LocalEquiv.IsImage.of_symm_image_eq

/- warning: local_equiv.is_image.compl -> LocalEquiv.IsImage.compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β}, (LocalEquiv.IsImage.{u1, u2} α β e s t) -> (LocalEquiv.IsImage.{u1, u2} α β e (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β}, (LocalEquiv.IsImage.{u2, u1} α β e s t) -> (LocalEquiv.IsImage.{u2, u1} α β e (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)) t))
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.compl LocalEquiv.IsImage.complₓ'. -/
protected theorem compl (h : e.IsImage s t) : e.IsImage (sᶜ) (tᶜ) := fun x hx => not_congr (h hx)
#align local_equiv.is_image.compl LocalEquiv.IsImage.compl

/- warning: local_equiv.is_image.inter -> LocalEquiv.IsImage.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β} {s' : Set.{u1} α} {t' : Set.{u2} β}, (LocalEquiv.IsImage.{u1, u2} α β e s t) -> (LocalEquiv.IsImage.{u1, u2} α β e s' t') -> (LocalEquiv.IsImage.{u1, u2} α β e (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s s') (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t t'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β} {s' : Set.{u2} α} {t' : Set.{u1} β}, (LocalEquiv.IsImage.{u2, u1} α β e s t) -> (LocalEquiv.IsImage.{u2, u1} α β e s' t') -> (LocalEquiv.IsImage.{u2, u1} α β e (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s s') (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) t t'))
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.inter LocalEquiv.IsImage.interₓ'. -/
protected theorem inter {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∩ s') (t ∩ t') := fun x hx => and_congr (h hx) (h' hx)
#align local_equiv.is_image.inter LocalEquiv.IsImage.inter

/- warning: local_equiv.is_image.union -> LocalEquiv.IsImage.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β} {s' : Set.{u1} α} {t' : Set.{u2} β}, (LocalEquiv.IsImage.{u1, u2} α β e s t) -> (LocalEquiv.IsImage.{u1, u2} α β e s' t') -> (LocalEquiv.IsImage.{u1, u2} α β e (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s s') (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) t t'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β} {s' : Set.{u2} α} {t' : Set.{u1} β}, (LocalEquiv.IsImage.{u2, u1} α β e s t) -> (LocalEquiv.IsImage.{u2, u1} α β e s' t') -> (LocalEquiv.IsImage.{u2, u1} α β e (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s s') (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) t t'))
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.union LocalEquiv.IsImage.unionₓ'. -/
protected theorem union {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∪ s') (t ∪ t') := fun x hx => or_congr (h hx) (h' hx)
#align local_equiv.is_image.union LocalEquiv.IsImage.union

/- warning: local_equiv.is_image.diff -> LocalEquiv.IsImage.diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β} {s' : Set.{u1} α} {t' : Set.{u2} β}, (LocalEquiv.IsImage.{u1, u2} α β e s t) -> (LocalEquiv.IsImage.{u1, u2} α β e s' t') -> (LocalEquiv.IsImage.{u1, u2} α β e (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s s') (SDiff.sdiff.{u2} (Set.{u2} β) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) t t'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β} {s' : Set.{u2} α} {t' : Set.{u1} β}, (LocalEquiv.IsImage.{u2, u1} α β e s t) -> (LocalEquiv.IsImage.{u2, u1} α β e s' t') -> (LocalEquiv.IsImage.{u2, u1} α β e (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) s s') (SDiff.sdiff.{u1} (Set.{u1} β) (Set.instSDiffSet.{u1} β) t t'))
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.diff LocalEquiv.IsImage.diffₓ'. -/
protected theorem diff {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s \ s') (t \ t') :=
  h.inter h'.compl
#align local_equiv.is_image.diff LocalEquiv.IsImage.diff

/- warning: local_equiv.is_image.left_inv_on_piecewise -> LocalEquiv.IsImage.leftInvOn_piecewise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β} {e' : LocalEquiv.{u1, u2} α β} [_inst_1 : forall (i : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s)] [_inst_2 : forall (i : β), Decidable (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i t)], (LocalEquiv.IsImage.{u1, u2} α β e s t) -> (LocalEquiv.IsImage.{u1, u2} α β e' s t) -> (Set.LeftInvOn.{u1, u2} α β (Set.piecewise.{u2, succ u1} β (fun (ᾰ : β) => α) t (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e')) (fun (j : β) => _inst_2 j)) (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e') (fun (j : α) => _inst_1 j)) (Set.ite.{u1} α s (LocalEquiv.source.{u1, u2} α β e) (LocalEquiv.source.{u1, u2} α β e')))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β} {e' : LocalEquiv.{u2, u1} α β} [_inst_1 : forall (i : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s)] [_inst_2 : forall (i : β), Decidable (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) i t)], (LocalEquiv.IsImage.{u2, u1} α β e s t) -> (LocalEquiv.IsImage.{u2, u1} α β e' s t) -> (Set.LeftInvOn.{u2, u1} α β (Set.piecewise.{u1, succ u2} β (fun (ᾰ : β) => α) t (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e')) (fun (j : β) => _inst_2 j)) (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) s (LocalEquiv.toFun.{u2, u1} α β e) (LocalEquiv.toFun.{u2, u1} α β e') (fun (j : α) => _inst_1 j)) (Set.ite.{u2} α s (LocalEquiv.source.{u2, u1} α β e) (LocalEquiv.source.{u2, u1} α β e')))
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.left_inv_on_piecewise LocalEquiv.IsImage.leftInvOn_piecewiseₓ'. -/
theorem leftInvOn_piecewise {e' : LocalEquiv α β} [∀ i, Decidable (i ∈ s)] [∀ i, Decidable (i ∈ t)]
    (h : e.IsImage s t) (h' : e'.IsImage s t) :
    LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source) :=
  by
  rintro x (⟨he, hs⟩ | ⟨he, hs : x ∉ s⟩)
  · rw [piecewise_eq_of_mem _ _ _ hs, piecewise_eq_of_mem _ _ _ ((h he).2 hs), e.left_inv he]
  ·
    rw [piecewise_eq_of_not_mem _ _ _ hs, piecewise_eq_of_not_mem _ _ _ ((h'.compl he).2 hs),
      e'.left_inv he]
#align local_equiv.is_image.left_inv_on_piecewise LocalEquiv.IsImage.leftInvOn_piecewise

/- warning: local_equiv.is_image.inter_eq_of_inter_eq_of_eq_on -> LocalEquiv.IsImage.inter_eq_of_inter_eq_of_eqOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β} {e' : LocalEquiv.{u1, u2} α β}, (LocalEquiv.IsImage.{u1, u2} α β e s t) -> (LocalEquiv.IsImage.{u1, u2} α β e' s t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e') s)) -> (Set.EqOn.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e') (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s)) -> (Eq.{succ u2} (Set.{u2} β) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) t) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e') t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β} {e' : LocalEquiv.{u2, u1} α β}, (LocalEquiv.IsImage.{u2, u1} α β e s t) -> (LocalEquiv.IsImage.{u2, u1} α β e' s t) -> (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) s) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e') s)) -> (Set.EqOn.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e) (LocalEquiv.toFun.{u2, u1} α β e') (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) s)) -> (Eq.{succ u1} (Set.{u1} β) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β e) t) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β e') t))
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.inter_eq_of_inter_eq_of_eq_on LocalEquiv.IsImage.inter_eq_of_inter_eq_of_eqOnₓ'. -/
theorem inter_eq_of_inter_eq_of_eqOn {e' : LocalEquiv α β} (h : e.IsImage s t) (h' : e'.IsImage s t)
    (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    e.target ∩ t = e'.target ∩ t := by rw [← h.image_eq, ← h'.image_eq, ← hs, Heq.image_eq]
#align local_equiv.is_image.inter_eq_of_inter_eq_of_eq_on LocalEquiv.IsImage.inter_eq_of_inter_eq_of_eqOn

/- warning: local_equiv.is_image.symm_eq_on_of_inter_eq_of_eq_on -> LocalEquiv.IsImage.symm_eq_on_of_inter_eq_of_eqOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α} {t : Set.{u2} β} {e' : LocalEquiv.{u1, u2} α β}, (LocalEquiv.IsImage.{u1, u2} α β e s t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e') s)) -> (Set.EqOn.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e') (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s)) -> (Set.EqOn.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e')) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α} {t : Set.{u1} β} {e' : LocalEquiv.{u2, u1} α β}, (LocalEquiv.IsImage.{u2, u1} α β e s t) -> (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) s) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e') s)) -> (Set.EqOn.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e) (LocalEquiv.toFun.{u2, u1} α β e') (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) s)) -> (Set.EqOn.{u1, u2} β α (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e')) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β e) t))
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image.symm_eq_on_of_inter_eq_of_eq_on LocalEquiv.IsImage.symm_eq_on_of_inter_eq_of_eqOnₓ'. -/
theorem symm_eq_on_of_inter_eq_of_eqOn {e' : LocalEquiv α β} (h : e.IsImage s t)
    (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    EqOn e.symm e'.symm (e.target ∩ t) :=
  by
  rw [← h.image_eq]
  rintro y ⟨x, hx, rfl⟩
  have hx' := hx; rw [hs] at hx'
  rw [e.left_inv hx.1, Heq hx, e'.left_inv hx'.1]
#align local_equiv.is_image.symm_eq_on_of_inter_eq_of_eq_on LocalEquiv.IsImage.symm_eq_on_of_inter_eq_of_eqOn

end IsImage

/- warning: local_equiv.is_image_source_target -> LocalEquiv.isImage_source_target is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β), LocalEquiv.IsImage.{u1, u2} α β e (LocalEquiv.source.{u1, u2} α β e) (LocalEquiv.target.{u1, u2} α β e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β), LocalEquiv.IsImage.{u2, u1} α β e (LocalEquiv.source.{u2, u1} α β e) (LocalEquiv.target.{u2, u1} α β e)
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image_source_target LocalEquiv.isImage_source_targetₓ'. -/
theorem isImage_source_target : e.IsImage e.source e.target := fun x hx => by simp [hx]
#align local_equiv.is_image_source_target LocalEquiv.isImage_source_target

/- warning: local_equiv.is_image_source_target_of_disjoint -> LocalEquiv.isImage_source_target_of_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u1, u2} α β), (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (LocalEquiv.source.{u1, u2} α β e) (LocalEquiv.source.{u1, u2} α β e')) -> (Disjoint.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) (LocalEquiv.target.{u1, u2} α β e) (LocalEquiv.target.{u1, u2} α β e')) -> (LocalEquiv.IsImage.{u1, u2} α β e (LocalEquiv.source.{u1, u2} α β e') (LocalEquiv.target.{u1, u2} α β e'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β) (e' : LocalEquiv.{u2, u1} α β), (Disjoint.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))))))))) (BooleanAlgebra.toBoundedOrder.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))) (LocalEquiv.source.{u2, u1} α β e) (LocalEquiv.source.{u2, u1} α β e')) -> (Disjoint.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} β) (Preorder.toLE.{u1} (Set.{u1} β) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))) (LocalEquiv.target.{u2, u1} α β e) (LocalEquiv.target.{u2, u1} α β e')) -> (LocalEquiv.IsImage.{u2, u1} α β e (LocalEquiv.source.{u2, u1} α β e') (LocalEquiv.target.{u2, u1} α β e'))
Case conversion may be inaccurate. Consider using '#align local_equiv.is_image_source_target_of_disjoint LocalEquiv.isImage_source_target_of_disjointₓ'. -/
theorem isImage_source_target_of_disjoint (e' : LocalEquiv α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) : e.IsImage e'.source e'.target :=
  IsImage.of_image_eq <| by rw [hs.inter_eq, ht.inter_eq, image_empty]
#align local_equiv.is_image_source_target_of_disjoint LocalEquiv.isImage_source_target_of_disjoint

/- warning: local_equiv.image_source_inter_eq' -> LocalEquiv.image_source_inter_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β) (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) s)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β e) (Set.preimage.{u1, u2} β α (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) s))
Case conversion may be inaccurate. Consider using '#align local_equiv.image_source_inter_eq' LocalEquiv.image_source_inter_eq'ₓ'. -/
theorem image_source_inter_eq' (s : Set α) : e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' s := by
  rw [inter_comm, e.left_inv_on.image_inter', image_source_eq_target, inter_comm]
#align local_equiv.image_source_inter_eq' LocalEquiv.image_source_inter_eq'

/- warning: local_equiv.image_source_inter_eq -> LocalEquiv.image_source_inter_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β) (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) s)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β e) (Set.preimage.{u1, u2} β α (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) s)))
Case conversion may be inaccurate. Consider using '#align local_equiv.image_source_inter_eq LocalEquiv.image_source_inter_eqₓ'. -/
theorem image_source_inter_eq (s : Set α) :
    e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' (e.source ∩ s) := by
  rw [inter_comm, e.left_inv_on.image_inter, image_source_eq_target, inter_comm]
#align local_equiv.image_source_inter_eq LocalEquiv.image_source_inter_eq

/- warning: local_equiv.image_eq_target_inter_inv_preimage -> LocalEquiv.image_eq_target_inter_inv_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) {s : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (LocalEquiv.source.{u1, u2} α β e)) -> (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) s) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β) {s : Set.{u2} α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (LocalEquiv.source.{u2, u1} α β e)) -> (Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e) s) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β e) (Set.preimage.{u1, u2} β α (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) s)))
Case conversion may be inaccurate. Consider using '#align local_equiv.image_eq_target_inter_inv_preimage LocalEquiv.image_eq_target_inter_inv_preimageₓ'. -/
theorem image_eq_target_inter_inv_preimage {s : Set α} (h : s ⊆ e.source) :
    e '' s = e.target ∩ e.symm ⁻¹' s := by
  rw [← e.image_source_inter_eq', inter_eq_self_of_subset_right h]
#align local_equiv.image_eq_target_inter_inv_preimage LocalEquiv.image_eq_target_inter_inv_preimage

/- warning: local_equiv.symm_image_eq_source_inter_preimage -> LocalEquiv.symm_image_eq_source_inter_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) {s : Set.{u2} β}, (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) s (LocalEquiv.target.{u1, u2} α β e)) -> (Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) {s : Set.{u2} β}, (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) s (LocalEquiv.target.{u1, u2} α β e)) -> (Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α (LocalEquiv.toFun.{u2, u1} β α (LocalEquiv.symm.{u1, u2} α β e)) s) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (LocalEquiv.toFun.{u1, u2} α β e) s)))
Case conversion may be inaccurate. Consider using '#align local_equiv.symm_image_eq_source_inter_preimage LocalEquiv.symm_image_eq_source_inter_preimageₓ'. -/
theorem symm_image_eq_source_inter_preimage {s : Set β} (h : s ⊆ e.target) :
    e.symm '' s = e.source ∩ e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h
#align local_equiv.symm_image_eq_source_inter_preimage LocalEquiv.symm_image_eq_source_inter_preimage

/- warning: local_equiv.symm_image_target_inter_eq -> LocalEquiv.symm_image_target_inter_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) s)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α (LocalEquiv.toFun.{u2, u1} β α (LocalEquiv.symm.{u1, u2} α β e)) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (LocalEquiv.target.{u1, u2} α β e) s)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (LocalEquiv.toFun.{u1, u2} α β e) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (LocalEquiv.target.{u1, u2} α β e) s)))
Case conversion may be inaccurate. Consider using '#align local_equiv.symm_image_target_inter_eq LocalEquiv.symm_image_target_inter_eqₓ'. -/
theorem symm_image_target_inter_eq (s : Set β) :
    e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' (e.target ∩ s) :=
  e.symm.image_source_inter_eq _
#align local_equiv.symm_image_target_inter_eq LocalEquiv.symm_image_target_inter_eq

/- warning: local_equiv.symm_image_target_inter_eq' -> LocalEquiv.symm_image_target_inter_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) s)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α (LocalEquiv.toFun.{u2, u1} β α (LocalEquiv.symm.{u1, u2} α β e)) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (LocalEquiv.target.{u1, u2} α β e) s)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (LocalEquiv.toFun.{u1, u2} α β e) s))
Case conversion may be inaccurate. Consider using '#align local_equiv.symm_image_target_inter_eq' LocalEquiv.symm_image_target_inter_eq'ₓ'. -/
theorem symm_image_target_inter_eq' (s : Set β) : e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.symm.image_source_inter_eq' _
#align local_equiv.symm_image_target_inter_eq' LocalEquiv.symm_image_target_inter_eq'

/- warning: local_equiv.source_inter_preimage_inv_preimage -> LocalEquiv.source_inter_preimage_inv_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) s))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β) (s : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) (Set.preimage.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e) (Set.preimage.{u1, u2} β α (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) s))) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) s)
Case conversion may be inaccurate. Consider using '#align local_equiv.source_inter_preimage_inv_preimage LocalEquiv.source_inter_preimage_inv_preimageₓ'. -/
theorem source_inter_preimage_inv_preimage (s : Set α) :
    e.source ∩ e ⁻¹' (e.symm ⁻¹' s) = e.source ∩ s :=
  Set.ext fun x => and_congr_right_iff.2 fun hx => by simp only [mem_preimage, e.left_inv hx]
#align local_equiv.source_inter_preimage_inv_preimage LocalEquiv.source_inter_preimage_inv_preimage

/- warning: local_equiv.source_inter_preimage_target_inter -> LocalEquiv.source_inter_preimage_target_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) s))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (LocalEquiv.toFun.{u1, u2} α β e) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (LocalEquiv.target.{u1, u2} α β e) s))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (LocalEquiv.toFun.{u1, u2} α β e) s))
Case conversion may be inaccurate. Consider using '#align local_equiv.source_inter_preimage_target_inter LocalEquiv.source_inter_preimage_target_interₓ'. -/
theorem source_inter_preimage_target_inter (s : Set β) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  ext fun x => ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, e.map_source hx.1, hx.2⟩⟩
#align local_equiv.source_inter_preimage_target_inter LocalEquiv.source_inter_preimage_target_inter

/- warning: local_equiv.target_inter_inv_preimage_preimage -> LocalEquiv.target_inter_inv_preimage_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (s : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) s))) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (s : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (LocalEquiv.target.{u1, u2} α β e) (Set.preimage.{u2, u1} β α (LocalEquiv.toFun.{u2, u1} β α (LocalEquiv.symm.{u1, u2} α β e)) (Set.preimage.{u1, u2} α β (LocalEquiv.toFun.{u1, u2} α β e) s))) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (LocalEquiv.target.{u1, u2} α β e) s)
Case conversion may be inaccurate. Consider using '#align local_equiv.target_inter_inv_preimage_preimage LocalEquiv.target_inter_inv_preimage_preimageₓ'. -/
theorem target_inter_inv_preimage_preimage (s : Set β) :
    e.target ∩ e.symm ⁻¹' (e ⁻¹' s) = e.target ∩ s :=
  e.symm.source_inter_preimage_inv_preimage _
#align local_equiv.target_inter_inv_preimage_preimage LocalEquiv.target_inter_inv_preimage_preimage

/- warning: local_equiv.symm_image_image_of_subset_source -> LocalEquiv.symm_image_image_of_subset_source is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) {s : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (LocalEquiv.source.{u1, u2} α β e)) -> (Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) s)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β) {s : Set.{u2} α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (LocalEquiv.source.{u2, u1} α β e)) -> (Eq.{succ u2} (Set.{u2} α) (Set.image.{u1, u2} β α (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) (Set.image.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e) s)) s)
Case conversion may be inaccurate. Consider using '#align local_equiv.symm_image_image_of_subset_source LocalEquiv.symm_image_image_of_subset_sourceₓ'. -/
theorem symm_image_image_of_subset_source {s : Set α} (h : s ⊆ e.source) : e.symm '' (e '' s) = s :=
  (e.LeftInvOn.mono h).image_image
#align local_equiv.symm_image_image_of_subset_source LocalEquiv.symm_image_image_of_subset_source

#print LocalEquiv.image_symm_image_of_subset_target /-
theorem image_symm_image_of_subset_target {s : Set β} (h : s ⊆ e.target) : e '' (e.symm '' s) = s :=
  e.symm.symm_image_image_of_subset_source h
#align local_equiv.image_symm_image_of_subset_target LocalEquiv.image_symm_image_of_subset_target
-/

/- warning: local_equiv.source_subset_preimage_target -> LocalEquiv.source_subset_preimage_target is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (LocalEquiv.target.{u1, u2} α β e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) (Set.preimage.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e) (LocalEquiv.target.{u2, u1} α β e))
Case conversion may be inaccurate. Consider using '#align local_equiv.source_subset_preimage_target LocalEquiv.source_subset_preimage_targetₓ'. -/
theorem source_subset_preimage_target : e.source ⊆ e ⁻¹' e.target :=
  e.MapsTo
#align local_equiv.source_subset_preimage_target LocalEquiv.source_subset_preimage_target

/- warning: local_equiv.symm_image_target_eq_source -> LocalEquiv.symm_image_target_eq_source is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β), Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) (LocalEquiv.target.{u1, u2} α β e)) (LocalEquiv.source.{u1, u2} α β e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β), Eq.{succ u2} (Set.{u2} α) (Set.image.{u1, u2} β α (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) (LocalEquiv.target.{u2, u1} α β e)) (LocalEquiv.source.{u2, u1} α β e)
Case conversion may be inaccurate. Consider using '#align local_equiv.symm_image_target_eq_source LocalEquiv.symm_image_target_eq_sourceₓ'. -/
theorem symm_image_target_eq_source : e.symm '' e.target = e.source :=
  e.symm.image_source_eq_target
#align local_equiv.symm_image_target_eq_source LocalEquiv.symm_image_target_eq_source

#print LocalEquiv.target_subset_preimage_source /-
theorem target_subset_preimage_source : e.target ⊆ e.symm ⁻¹' e.source :=
  e.symm_mapsTo
#align local_equiv.target_subset_preimage_source LocalEquiv.target_subset_preimage_source
-/

/- warning: local_equiv.ext -> LocalEquiv.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {e' : LocalEquiv.{u1, u2} α β}, (forall (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e' x)) -> (forall (x : β), Eq.{succ u1} α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e) x) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e') x)) -> (Eq.{succ u1} (Set.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (LocalEquiv.source.{u1, u2} α β e')) -> (Eq.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) e e')
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {e' : LocalEquiv.{u2, u1} α β}, (forall (x : α), Eq.{succ u1} β (LocalEquiv.toFun.{u2, u1} α β e x) (LocalEquiv.toFun.{u2, u1} α β e' x)) -> (forall (x : β), Eq.{succ u2} α (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e) x) (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e') x)) -> (Eq.{succ u2} (Set.{u2} α) (LocalEquiv.source.{u2, u1} α β e) (LocalEquiv.source.{u2, u1} α β e')) -> (Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) e e')
Case conversion may be inaccurate. Consider using '#align local_equiv.ext LocalEquiv.extₓ'. -/
/-- Two local equivs that have the same `source`, same `to_fun` and same `inv_fun`, coincide. -/
@[ext]
protected theorem ext {e e' : LocalEquiv α β} (h : ∀ x, e x = e' x)
    (hsymm : ∀ x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' :=
  by
  have A : (e : α → β) = e' := by
    ext x
    exact h x
  have B : (e.symm : β → α) = e'.symm := by
    ext x
    exact hsymm x
  have I : e '' e.source = e.target := e.image_source_eq_target
  have I' : e' '' e'.source = e'.target := e'.image_source_eq_target
  rw [A, hs, I'] at I
  cases e <;> cases e'
  simp_all
#align local_equiv.ext LocalEquiv.ext

#print LocalEquiv.restr /-
/-- Restricting a local equivalence to e.source ∩ s -/
protected def restr (s : Set α) : LocalEquiv α β :=
  (@IsImage.of_symm_preimage_eq α β e s (e.symm ⁻¹' s) rfl).restr
#align local_equiv.restr LocalEquiv.restr
-/

/- warning: local_equiv.restr_coe -> LocalEquiv.restr_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (s : Set.{u1} α), Eq.{max (succ u1) (succ u2)} ((fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.restr.{u1, u2} α β e s)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) (LocalEquiv.restr.{u1, u2} α β e s)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β) (s : Set.{u2} α), Eq.{max (succ u2) (succ u1)} (α -> β) (LocalEquiv.toFun.{u2, u1} α β (LocalEquiv.restr.{u2, u1} α β e s)) (LocalEquiv.toFun.{u2, u1} α β e)
Case conversion may be inaccurate. Consider using '#align local_equiv.restr_coe LocalEquiv.restr_coeₓ'. -/
@[simp, mfld_simps]
theorem restr_coe (s : Set α) : (e.restr s : α → β) = e :=
  rfl
#align local_equiv.restr_coe LocalEquiv.restr_coe

/- warning: local_equiv.restr_coe_symm -> LocalEquiv.restr_coe_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (s : Set.{u1} α), Eq.{max (succ u2) (succ u1)} ((fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.symm.{u1, u2} α β (LocalEquiv.restr.{u1, u2} α β e s))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β (LocalEquiv.restr.{u1, u2} α β e s))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β) (s : Set.{u2} α), Eq.{max (succ u2) (succ u1)} (β -> α) (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β (LocalEquiv.restr.{u2, u1} α β e s))) (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e))
Case conversion may be inaccurate. Consider using '#align local_equiv.restr_coe_symm LocalEquiv.restr_coe_symmₓ'. -/
@[simp, mfld_simps]
theorem restr_coe_symm (s : Set α) : ((e.restr s).symm : β → α) = e.symm :=
  rfl
#align local_equiv.restr_coe_symm LocalEquiv.restr_coe_symm

/- warning: local_equiv.restr_source -> LocalEquiv.restr_source is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (LocalEquiv.source.{u1, u2} α β (LocalEquiv.restr.{u1, u2} α β e s)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β) (s : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (LocalEquiv.source.{u2, u1} α β (LocalEquiv.restr.{u2, u1} α β e s)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) s)
Case conversion may be inaccurate. Consider using '#align local_equiv.restr_source LocalEquiv.restr_sourceₓ'. -/
@[simp, mfld_simps]
theorem restr_source (s : Set α) : (e.restr s).source = e.source ∩ s :=
  rfl
#align local_equiv.restr_source LocalEquiv.restr_source

/- warning: local_equiv.restr_target -> LocalEquiv.restr_target is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (LocalEquiv.target.{u1, u2} α β (LocalEquiv.restr.{u1, u2} α β e s)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β) (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (LocalEquiv.target.{u2, u1} α β (LocalEquiv.restr.{u2, u1} α β e s)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u2, u1} α β e) (Set.preimage.{u1, u2} β α (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) s))
Case conversion may be inaccurate. Consider using '#align local_equiv.restr_target LocalEquiv.restr_targetₓ'. -/
@[simp, mfld_simps]
theorem restr_target (s : Set α) : (e.restr s).target = e.target ∩ e.symm ⁻¹' s :=
  rfl
#align local_equiv.restr_target LocalEquiv.restr_target

/- warning: local_equiv.restr_eq_of_source_subset -> LocalEquiv.restr_eq_of_source_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {s : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (LocalEquiv.source.{u1, u2} α β e) s) -> (Eq.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.restr.{u1, u2} α β e s) e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {s : Set.{u2} α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) s) -> (Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalEquiv.restr.{u2, u1} α β e s) e)
Case conversion may be inaccurate. Consider using '#align local_equiv.restr_eq_of_source_subset LocalEquiv.restr_eq_of_source_subsetₓ'. -/
theorem restr_eq_of_source_subset {e : LocalEquiv α β} {s : Set α} (h : e.source ⊆ s) :
    e.restr s = e :=
  LocalEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [inter_eq_self_of_subset_left h])
#align local_equiv.restr_eq_of_source_subset LocalEquiv.restr_eq_of_source_subset

/- warning: local_equiv.restr_univ -> LocalEquiv.restr_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β}, Eq.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.restr.{u1, u2} α β e (Set.univ.{u1} α)) e
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β}, Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalEquiv.restr.{u2, u1} α β e (Set.univ.{u2} α)) e
Case conversion may be inaccurate. Consider using '#align local_equiv.restr_univ LocalEquiv.restr_univₓ'. -/
@[simp, mfld_simps]
theorem restr_univ {e : LocalEquiv α β} : e.restr univ = e :=
  restr_eq_of_source_subset (subset_univ _)
#align local_equiv.restr_univ LocalEquiv.restr_univ

#print LocalEquiv.refl /-
/-- The identity local equiv -/
protected def refl (α : Type _) : LocalEquiv α α :=
  (Equiv.refl α).toLocalEquiv
#align local_equiv.refl LocalEquiv.refl
-/

#print LocalEquiv.refl_source /-
@[simp, mfld_simps]
theorem refl_source : (LocalEquiv.refl α).source = univ :=
  rfl
#align local_equiv.refl_source LocalEquiv.refl_source
-/

#print LocalEquiv.refl_target /-
@[simp, mfld_simps]
theorem refl_target : (LocalEquiv.refl α).target = univ :=
  rfl
#align local_equiv.refl_target LocalEquiv.refl_target
-/

#print LocalEquiv.refl_coe /-
@[simp, mfld_simps]
theorem refl_coe : (LocalEquiv.refl α : α → α) = id :=
  rfl
#align local_equiv.refl_coe LocalEquiv.refl_coe
-/

#print LocalEquiv.refl_symm /-
@[simp, mfld_simps]
theorem refl_symm : (LocalEquiv.refl α).symm = LocalEquiv.refl α :=
  rfl
#align local_equiv.refl_symm LocalEquiv.refl_symm
-/

#print LocalEquiv.refl_restr_source /-
@[simp, mfld_simps]
theorem refl_restr_source (s : Set α) : ((LocalEquiv.refl α).restr s).source = s := by simp
#align local_equiv.refl_restr_source LocalEquiv.refl_restr_source
-/

#print LocalEquiv.refl_restr_target /-
@[simp, mfld_simps]
theorem refl_restr_target (s : Set α) : ((LocalEquiv.refl α).restr s).target = s :=
  by
  change univ ∩ id ⁻¹' s = s
  simp
#align local_equiv.refl_restr_target LocalEquiv.refl_restr_target
-/

#print LocalEquiv.ofSet /-
/-- The identity local equiv on a set `s` -/
def ofSet (s : Set α) : LocalEquiv α α where
  toFun := id
  invFun := id
  source := s
  target := s
  map_source' x hx := hx
  map_target' x hx := hx
  left_inv' x hx := rfl
  right_inv' x hx := rfl
#align local_equiv.of_set LocalEquiv.ofSet
-/

#print LocalEquiv.ofSet_source /-
@[simp, mfld_simps]
theorem ofSet_source (s : Set α) : (LocalEquiv.ofSet s).source = s :=
  rfl
#align local_equiv.of_set_source LocalEquiv.ofSet_source
-/

#print LocalEquiv.ofSet_target /-
@[simp, mfld_simps]
theorem ofSet_target (s : Set α) : (LocalEquiv.ofSet s).target = s :=
  rfl
#align local_equiv.of_set_target LocalEquiv.ofSet_target
-/

#print LocalEquiv.ofSet_coe /-
@[simp, mfld_simps]
theorem ofSet_coe (s : Set α) : (LocalEquiv.ofSet s : α → α) = id :=
  rfl
#align local_equiv.of_set_coe LocalEquiv.ofSet_coe
-/

#print LocalEquiv.ofSet_symm /-
@[simp, mfld_simps]
theorem ofSet_symm (s : Set α) : (LocalEquiv.ofSet s).symm = LocalEquiv.ofSet s :=
  rfl
#align local_equiv.of_set_symm LocalEquiv.ofSet_symm
-/

#print LocalEquiv.trans' /-
/-- Composing two local equivs if the target of the first coincides with the source of the
second. -/
protected def trans' (e' : LocalEquiv β γ) (h : e.target = e'.source) : LocalEquiv α γ
    where
  toFun := e' ∘ e
  invFun := e.symm ∘ e'.symm
  source := e.source
  target := e'.target
  map_source' x hx := by simp [h.symm, hx]
  map_target' y hy := by simp [h, hy]
  left_inv' x hx := by simp [hx, h.symm]
  right_inv' y hy := by simp [hy, h]
#align local_equiv.trans' LocalEquiv.trans'
-/

#print LocalEquiv.trans /-
/-- Composing two local equivs, by restricting to the maximal domain where their composition
is well defined. -/
protected def trans : LocalEquiv α γ :=
  LocalEquiv.trans' (e.symm.restr e'.source).symm (e'.restr e.target) (inter_comm _ _)
#align local_equiv.trans LocalEquiv.trans
-/

/- warning: local_equiv.coe_trans -> LocalEquiv.coe_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u2, u3} β γ), Eq.{max (succ u1) (succ u3)} ((fun (_x : LocalEquiv.{u1, u3} α γ) => α -> γ) (LocalEquiv.trans.{u1, u2, u3} α β γ e e')) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (LocalEquiv.{u1, u3} α γ) (fun (_x : LocalEquiv.{u1, u3} α γ) => α -> γ) (LocalEquiv.hasCoeToFun.{u1, u3} α γ) (LocalEquiv.trans.{u1, u2, u3} α β γ e e')) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LocalEquiv.{u2, u3} β γ) (fun (_x : LocalEquiv.{u2, u3} β γ) => β -> γ) (LocalEquiv.hasCoeToFun.{u2, u3} β γ) e') (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (e : LocalEquiv.{u3, u1} α β) (e' : LocalEquiv.{u1, u2} β γ), Eq.{max (succ u3) (succ u2)} (α -> γ) (LocalEquiv.toFun.{u3, u2} α γ (LocalEquiv.trans.{u3, u1, u2} α β γ e e')) (Function.comp.{succ u3, succ u1, succ u2} α β γ (LocalEquiv.toFun.{u1, u2} β γ e') (LocalEquiv.toFun.{u3, u1} α β e))
Case conversion may be inaccurate. Consider using '#align local_equiv.coe_trans LocalEquiv.coe_transₓ'. -/
@[simp, mfld_simps]
theorem coe_trans : (e.trans e' : α → γ) = e' ∘ e :=
  rfl
#align local_equiv.coe_trans LocalEquiv.coe_trans

/- warning: local_equiv.coe_trans_symm -> LocalEquiv.coe_trans_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u2, u3} β γ), Eq.{max (succ u3) (succ u1)} ((fun (_x : LocalEquiv.{u3, u1} γ α) => γ -> α) (LocalEquiv.symm.{u1, u3} α γ (LocalEquiv.trans.{u1, u2, u3} α β γ e e'))) (coeFn.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (LocalEquiv.{u3, u1} γ α) (fun (_x : LocalEquiv.{u3, u1} γ α) => γ -> α) (LocalEquiv.hasCoeToFun.{u3, u1} γ α) (LocalEquiv.symm.{u1, u3} α γ (LocalEquiv.trans.{u1, u2, u3} α β γ e e'))) (Function.comp.{succ u3, succ u2, succ u1} γ β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (LocalEquiv.{u3, u2} γ β) (fun (_x : LocalEquiv.{u3, u2} γ β) => γ -> β) (LocalEquiv.hasCoeToFun.{u3, u2} γ β) (LocalEquiv.symm.{u2, u3} β γ e')))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (e : LocalEquiv.{u3, u1} α β) (e' : LocalEquiv.{u1, u2} β γ), Eq.{max (succ u3) (succ u2)} (γ -> α) (LocalEquiv.toFun.{u2, u3} γ α (LocalEquiv.symm.{u3, u2} α γ (LocalEquiv.trans.{u3, u1, u2} α β γ e e'))) (Function.comp.{succ u2, succ u1, succ u3} γ β α (LocalEquiv.toFun.{u1, u3} β α (LocalEquiv.symm.{u3, u1} α β e)) (LocalEquiv.toFun.{u2, u1} γ β (LocalEquiv.symm.{u1, u2} β γ e')))
Case conversion may be inaccurate. Consider using '#align local_equiv.coe_trans_symm LocalEquiv.coe_trans_symmₓ'. -/
@[simp, mfld_simps]
theorem coe_trans_symm : ((e.trans e').symm : γ → α) = e.symm ∘ e'.symm :=
  rfl
#align local_equiv.coe_trans_symm LocalEquiv.coe_trans_symm

/- warning: local_equiv.trans_apply -> LocalEquiv.trans_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u2, u3} β γ) {x : α}, Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (LocalEquiv.{u1, u3} α γ) (fun (_x : LocalEquiv.{u1, u3} α γ) => α -> γ) (LocalEquiv.hasCoeToFun.{u1, u3} α γ) (LocalEquiv.trans.{u1, u2, u3} α β γ e e') x) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LocalEquiv.{u2, u3} β γ) (fun (_x : LocalEquiv.{u2, u3} β γ) => β -> γ) (LocalEquiv.hasCoeToFun.{u2, u3} β γ) e' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} (e : LocalEquiv.{u2, u1} α β) (e' : LocalEquiv.{u1, u3} β γ) {x : α}, Eq.{succ u3} γ (LocalEquiv.toFun.{u2, u3} α γ (LocalEquiv.trans.{u2, u1, u3} α β γ e e') x) (LocalEquiv.toFun.{u1, u3} β γ e' (LocalEquiv.toFun.{u2, u1} α β e x))
Case conversion may be inaccurate. Consider using '#align local_equiv.trans_apply LocalEquiv.trans_applyₓ'. -/
theorem trans_apply {x : α} : (e.trans e') x = e' (e x) :=
  rfl
#align local_equiv.trans_apply LocalEquiv.trans_apply

/- warning: local_equiv.trans_symm_eq_symm_trans_symm -> LocalEquiv.trans_symm_eq_symm_trans_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u2, u3} β γ), Eq.{max (succ u3) (succ u1)} (LocalEquiv.{u3, u1} γ α) (LocalEquiv.symm.{u1, u3} α γ (LocalEquiv.trans.{u1, u2, u3} α β γ e e')) (LocalEquiv.trans.{u3, u2, u1} γ β α (LocalEquiv.symm.{u2, u3} β γ e') (LocalEquiv.symm.{u1, u2} α β e))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (e : LocalEquiv.{u3, u1} α β) (e' : LocalEquiv.{u1, u2} β γ), Eq.{max (succ u3) (succ u2)} (LocalEquiv.{u2, u3} γ α) (LocalEquiv.symm.{u3, u2} α γ (LocalEquiv.trans.{u3, u1, u2} α β γ e e')) (LocalEquiv.trans.{u2, u1, u3} γ β α (LocalEquiv.symm.{u1, u2} β γ e') (LocalEquiv.symm.{u3, u1} α β e))
Case conversion may be inaccurate. Consider using '#align local_equiv.trans_symm_eq_symm_trans_symm LocalEquiv.trans_symm_eq_symm_trans_symmₓ'. -/
theorem trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm := by
  cases e <;> cases e' <;> rfl
#align local_equiv.trans_symm_eq_symm_trans_symm LocalEquiv.trans_symm_eq_symm_trans_symm

/- warning: local_equiv.trans_source -> LocalEquiv.trans_source is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u2, u3} β γ), Eq.{succ u1} (Set.{u1} α) (LocalEquiv.source.{u1, u3} α γ (LocalEquiv.trans.{u1, u2, u3} α β γ e e')) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (LocalEquiv.source.{u2, u3} β γ e')))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (e : LocalEquiv.{u3, u1} α β) (e' : LocalEquiv.{u1, u2} β γ), Eq.{succ u3} (Set.{u3} α) (LocalEquiv.source.{u3, u2} α γ (LocalEquiv.trans.{u3, u1, u2} α β γ e e')) (Inter.inter.{u3} (Set.{u3} α) (Set.instInterSet.{u3} α) (LocalEquiv.source.{u3, u1} α β e) (Set.preimage.{u3, u1} α β (LocalEquiv.toFun.{u3, u1} α β e) (LocalEquiv.source.{u1, u2} β γ e')))
Case conversion may be inaccurate. Consider using '#align local_equiv.trans_source LocalEquiv.trans_sourceₓ'. -/
@[simp, mfld_simps]
theorem trans_source : (e.trans e').source = e.source ∩ e ⁻¹' e'.source :=
  rfl
#align local_equiv.trans_source LocalEquiv.trans_source

/- warning: local_equiv.trans_source' -> LocalEquiv.trans_source' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u2, u3} β γ), Eq.{succ u1} (Set.{u1} α) (LocalEquiv.source.{u1, u3} α γ (LocalEquiv.trans.{u1, u2, u3} α β γ e e')) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) (LocalEquiv.source.{u2, u3} β γ e'))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (e : LocalEquiv.{u3, u1} α β) (e' : LocalEquiv.{u1, u2} β γ), Eq.{succ u3} (Set.{u3} α) (LocalEquiv.source.{u3, u2} α γ (LocalEquiv.trans.{u3, u1, u2} α β γ e e')) (Inter.inter.{u3} (Set.{u3} α) (Set.instInterSet.{u3} α) (LocalEquiv.source.{u3, u1} α β e) (Set.preimage.{u3, u1} α β (LocalEquiv.toFun.{u3, u1} α β e) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u3, u1} α β e) (LocalEquiv.source.{u1, u2} β γ e'))))
Case conversion may be inaccurate. Consider using '#align local_equiv.trans_source' LocalEquiv.trans_source'ₓ'. -/
theorem trans_source' : (e.trans e').source = e.source ∩ e ⁻¹' (e.target ∩ e'.source) := by
  mfld_set_tac
#align local_equiv.trans_source' LocalEquiv.trans_source'

/- warning: local_equiv.trans_source'' -> LocalEquiv.trans_source'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u2, u3} β γ), Eq.{succ u1} (Set.{u1} α) (LocalEquiv.source.{u1, u3} α γ (LocalEquiv.trans.{u1, u2, u3} α β γ e e')) (Set.image.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) (LocalEquiv.source.{u2, u3} β γ e')))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (e : LocalEquiv.{u3, u1} α β) (e' : LocalEquiv.{u1, u2} β γ), Eq.{succ u3} (Set.{u3} α) (LocalEquiv.source.{u3, u2} α γ (LocalEquiv.trans.{u3, u1, u2} α β γ e e')) (Set.image.{u1, u3} β α (LocalEquiv.toFun.{u1, u3} β α (LocalEquiv.symm.{u3, u1} α β e)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.target.{u3, u1} α β e) (LocalEquiv.source.{u1, u2} β γ e')))
Case conversion may be inaccurate. Consider using '#align local_equiv.trans_source'' LocalEquiv.trans_source''ₓ'. -/
theorem trans_source'' : (e.trans e').source = e.symm '' (e.target ∩ e'.source) := by
  rw [e.trans_source', e.symm_image_target_inter_eq]
#align local_equiv.trans_source'' LocalEquiv.trans_source''

/- warning: local_equiv.image_trans_source -> LocalEquiv.image_trans_source is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u2, u3} β γ), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (LocalEquiv.source.{u1, u3} α γ (LocalEquiv.trans.{u1, u2, u3} α β γ e e'))) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.target.{u1, u2} α β e) (LocalEquiv.source.{u2, u3} β γ e'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} (e : LocalEquiv.{u2, u3} α β) (e' : LocalEquiv.{u3, u1} β γ), Eq.{succ u3} (Set.{u3} β) (Set.image.{u2, u3} α β (LocalEquiv.toFun.{u2, u3} α β e) (LocalEquiv.source.{u2, u1} α γ (LocalEquiv.trans.{u2, u3, u1} α β γ e e'))) (Inter.inter.{u3} (Set.{u3} β) (Set.instInterSet.{u3} β) (LocalEquiv.target.{u2, u3} α β e) (LocalEquiv.source.{u3, u1} β γ e'))
Case conversion may be inaccurate. Consider using '#align local_equiv.image_trans_source LocalEquiv.image_trans_sourceₓ'. -/
theorem image_trans_source : e '' (e.trans e').source = e.target ∩ e'.source :=
  (e.symm.restr e'.source).symm.image_source_eq_target
#align local_equiv.image_trans_source LocalEquiv.image_trans_source

/- warning: local_equiv.trans_target -> LocalEquiv.trans_target is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u2, u3} β γ), Eq.{succ u3} (Set.{u3} γ) (LocalEquiv.target.{u1, u3} α γ (LocalEquiv.trans.{u1, u2, u3} α β γ e e')) (Inter.inter.{u3} (Set.{u3} γ) (Set.hasInter.{u3} γ) (LocalEquiv.target.{u2, u3} β γ e') (Set.preimage.{u3, u2} γ β (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (LocalEquiv.{u3, u2} γ β) (fun (_x : LocalEquiv.{u3, u2} γ β) => γ -> β) (LocalEquiv.hasCoeToFun.{u3, u2} γ β) (LocalEquiv.symm.{u2, u3} β γ e')) (LocalEquiv.target.{u1, u2} α β e)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} (e : LocalEquiv.{u2, u1} α β) (e' : LocalEquiv.{u1, u3} β γ), Eq.{succ u3} (Set.{u3} γ) (LocalEquiv.target.{u2, u3} α γ (LocalEquiv.trans.{u2, u1, u3} α β γ e e')) (Inter.inter.{u3} (Set.{u3} γ) (Set.instInterSet.{u3} γ) (LocalEquiv.target.{u1, u3} β γ e') (Set.preimage.{u3, u1} γ β (LocalEquiv.toFun.{u3, u1} γ β (LocalEquiv.symm.{u1, u3} β γ e')) (LocalEquiv.target.{u2, u1} α β e)))
Case conversion may be inaccurate. Consider using '#align local_equiv.trans_target LocalEquiv.trans_targetₓ'. -/
@[simp, mfld_simps]
theorem trans_target : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' e.target :=
  rfl
#align local_equiv.trans_target LocalEquiv.trans_target

/- warning: local_equiv.trans_target' -> LocalEquiv.trans_target' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u2, u3} β γ), Eq.{succ u3} (Set.{u3} γ) (LocalEquiv.target.{u1, u3} α γ (LocalEquiv.trans.{u1, u2, u3} α β γ e e')) (Inter.inter.{u3} (Set.{u3} γ) (Set.hasInter.{u3} γ) (LocalEquiv.target.{u2, u3} β γ e') (Set.preimage.{u3, u2} γ β (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (LocalEquiv.{u3, u2} γ β) (fun (_x : LocalEquiv.{u3, u2} γ β) => γ -> β) (LocalEquiv.hasCoeToFun.{u3, u2} γ β) (LocalEquiv.symm.{u2, u3} β γ e')) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.source.{u2, u3} β γ e') (LocalEquiv.target.{u1, u2} α β e))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} (e : LocalEquiv.{u2, u1} α β) (e' : LocalEquiv.{u1, u3} β γ), Eq.{succ u3} (Set.{u3} γ) (LocalEquiv.target.{u2, u3} α γ (LocalEquiv.trans.{u2, u1, u3} α β γ e e')) (Inter.inter.{u3} (Set.{u3} γ) (Set.instInterSet.{u3} γ) (LocalEquiv.target.{u1, u3} β γ e') (Set.preimage.{u3, u1} γ β (LocalEquiv.toFun.{u3, u1} γ β (LocalEquiv.symm.{u1, u3} β γ e')) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.source.{u1, u3} β γ e') (LocalEquiv.target.{u2, u1} α β e))))
Case conversion may be inaccurate. Consider using '#align local_equiv.trans_target' LocalEquiv.trans_target'ₓ'. -/
theorem trans_target' : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' (e'.source ∩ e.target) :=
  trans_source' e'.symm e.symm
#align local_equiv.trans_target' LocalEquiv.trans_target'

/- warning: local_equiv.trans_target'' -> LocalEquiv.trans_target'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u2, u3} β γ), Eq.{succ u3} (Set.{u3} γ) (LocalEquiv.target.{u1, u3} α γ (LocalEquiv.trans.{u1, u2, u3} α β γ e e')) (Set.image.{u2, u3} β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LocalEquiv.{u2, u3} β γ) (fun (_x : LocalEquiv.{u2, u3} β γ) => β -> γ) (LocalEquiv.hasCoeToFun.{u2, u3} β γ) e') (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.source.{u2, u3} β γ e') (LocalEquiv.target.{u1, u2} α β e)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} (e : LocalEquiv.{u2, u1} α β) (e' : LocalEquiv.{u1, u3} β γ), Eq.{succ u3} (Set.{u3} γ) (LocalEquiv.target.{u2, u3} α γ (LocalEquiv.trans.{u2, u1, u3} α β γ e e')) (Set.image.{u1, u3} β γ (LocalEquiv.toFun.{u1, u3} β γ e') (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (LocalEquiv.source.{u1, u3} β γ e') (LocalEquiv.target.{u2, u1} α β e)))
Case conversion may be inaccurate. Consider using '#align local_equiv.trans_target'' LocalEquiv.trans_target''ₓ'. -/
theorem trans_target'' : (e.trans e').target = e' '' (e'.source ∩ e.target) :=
  trans_source'' e'.symm e.symm
#align local_equiv.trans_target'' LocalEquiv.trans_target''

/- warning: local_equiv.inv_image_trans_target -> LocalEquiv.inv_image_trans_target is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u2, u3} β γ), Eq.{succ u2} (Set.{u2} β) (Set.image.{u3, u2} γ β (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (LocalEquiv.{u3, u2} γ β) (fun (_x : LocalEquiv.{u3, u2} γ β) => γ -> β) (LocalEquiv.hasCoeToFun.{u3, u2} γ β) (LocalEquiv.symm.{u2, u3} β γ e')) (LocalEquiv.target.{u1, u3} α γ (LocalEquiv.trans.{u1, u2, u3} α β γ e e'))) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (LocalEquiv.source.{u2, u3} β γ e') (LocalEquiv.target.{u1, u2} α β e))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} (e : LocalEquiv.{u1, u3} α β) (e' : LocalEquiv.{u3, u2} β γ), Eq.{succ u3} (Set.{u3} β) (Set.image.{u2, u3} γ β (LocalEquiv.toFun.{u2, u3} γ β (LocalEquiv.symm.{u3, u2} β γ e')) (LocalEquiv.target.{u1, u2} α γ (LocalEquiv.trans.{u1, u3, u2} α β γ e e'))) (Inter.inter.{u3} (Set.{u3} β) (Set.instInterSet.{u3} β) (LocalEquiv.source.{u3, u2} β γ e') (LocalEquiv.target.{u1, u3} α β e))
Case conversion may be inaccurate. Consider using '#align local_equiv.inv_image_trans_target LocalEquiv.inv_image_trans_targetₓ'. -/
theorem inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source ∩ e.target :=
  image_trans_source e'.symm e.symm
#align local_equiv.inv_image_trans_target LocalEquiv.inv_image_trans_target

/- warning: local_equiv.trans_assoc -> LocalEquiv.trans_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u2, u3} β γ) (e'' : LocalEquiv.{u3, u4} γ δ), Eq.{max (succ u1) (succ u4)} (LocalEquiv.{u1, u4} α δ) (LocalEquiv.trans.{u1, u3, u4} α γ δ (LocalEquiv.trans.{u1, u2, u3} α β γ e e') e'') (LocalEquiv.trans.{u1, u2, u4} α β δ e (LocalEquiv.trans.{u2, u3, u4} β γ δ e' e''))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u4}} {δ : Type.{u3}} (e : LocalEquiv.{u2, u1} α β) (e' : LocalEquiv.{u1, u4} β γ) (e'' : LocalEquiv.{u4, u3} γ δ), Eq.{max (succ u2) (succ u3)} (LocalEquiv.{u2, u3} α δ) (LocalEquiv.trans.{u2, u4, u3} α γ δ (LocalEquiv.trans.{u2, u1, u4} α β γ e e') e'') (LocalEquiv.trans.{u2, u1, u3} α β δ e (LocalEquiv.trans.{u1, u4, u3} β γ δ e' e''))
Case conversion may be inaccurate. Consider using '#align local_equiv.trans_assoc LocalEquiv.trans_assocₓ'. -/
theorem trans_assoc (e'' : LocalEquiv γ δ) : (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  LocalEquiv.ext (fun x => rfl) (fun x => rfl)
    (by simp [trans_source, @preimage_comp α β γ, inter_assoc])
#align local_equiv.trans_assoc LocalEquiv.trans_assoc

/- warning: local_equiv.trans_refl -> LocalEquiv.trans_refl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β), Eq.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.trans.{u1, u2, u2} α β β e (LocalEquiv.refl.{u2} β)) e
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β), Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalEquiv.trans.{u2, u1, u1} α β β e (LocalEquiv.refl.{u1} β)) e
Case conversion may be inaccurate. Consider using '#align local_equiv.trans_refl LocalEquiv.trans_reflₓ'. -/
@[simp, mfld_simps]
theorem trans_refl : e.trans (LocalEquiv.refl β) = e :=
  LocalEquiv.ext (fun x => rfl) (fun x => rfl) (by simp [trans_source])
#align local_equiv.trans_refl LocalEquiv.trans_refl

/- warning: local_equiv.refl_trans -> LocalEquiv.refl_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β), Eq.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.trans.{u1, u1, u2} α α β (LocalEquiv.refl.{u1} α) e) e
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β), Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalEquiv.trans.{u2, u2, u1} α α β (LocalEquiv.refl.{u2} α) e) e
Case conversion may be inaccurate. Consider using '#align local_equiv.refl_trans LocalEquiv.refl_transₓ'. -/
@[simp, mfld_simps]
theorem refl_trans : (LocalEquiv.refl α).trans e = e :=
  LocalEquiv.ext (fun x => rfl) (fun x => rfl) (by simp [trans_source, preimage_id])
#align local_equiv.refl_trans LocalEquiv.refl_trans

#print LocalEquiv.trans_refl_restr /-
theorem trans_refl_restr (s : Set β) : e.trans ((LocalEquiv.refl β).restr s) = e.restr (e ⁻¹' s) :=
  LocalEquiv.ext (fun x => rfl) (fun x => rfl) (by simp [trans_source])
#align local_equiv.trans_refl_restr LocalEquiv.trans_refl_restr
-/

/- warning: local_equiv.trans_refl_restr' -> LocalEquiv.trans_refl_restr' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (s : Set.{u2} β), Eq.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.trans.{u1, u2, u2} α β β e (LocalEquiv.restr.{u2, u2} β β (LocalEquiv.refl.{u2} β) s)) (LocalEquiv.restr.{u1, u2} α β e (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (s : Set.{u2} β), Eq.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.trans.{u1, u2, u2} α β β e (LocalEquiv.restr.{u2, u2} β β (LocalEquiv.refl.{u2} β) s)) (LocalEquiv.restr.{u1, u2} α β e (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (LocalEquiv.toFun.{u1, u2} α β e) s)))
Case conversion may be inaccurate. Consider using '#align local_equiv.trans_refl_restr' LocalEquiv.trans_refl_restr'ₓ'. -/
theorem trans_refl_restr' (s : Set β) :
    e.trans ((LocalEquiv.refl β).restr s) = e.restr (e.source ∩ e ⁻¹' s) :=
  (LocalEquiv.ext (fun x => rfl) fun x => rfl) <|
    by
    simp [trans_source]
    rw [← inter_assoc, inter_self]
#align local_equiv.trans_refl_restr' LocalEquiv.trans_refl_restr'

/- warning: local_equiv.restr_trans -> LocalEquiv.restr_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u2, u3} β γ) (s : Set.{u1} α), Eq.{max (succ u1) (succ u3)} (LocalEquiv.{u1, u3} α γ) (LocalEquiv.trans.{u1, u2, u3} α β γ (LocalEquiv.restr.{u1, u2} α β e s) e') (LocalEquiv.restr.{u1, u3} α γ (LocalEquiv.trans.{u1, u2, u3} α β γ e e') s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (e : LocalEquiv.{u3, u1} α β) (e' : LocalEquiv.{u1, u2} β γ) (s : Set.{u3} α), Eq.{max (succ u3) (succ u2)} (LocalEquiv.{u3, u2} α γ) (LocalEquiv.trans.{u3, u1, u2} α β γ (LocalEquiv.restr.{u3, u1} α β e s) e') (LocalEquiv.restr.{u3, u2} α γ (LocalEquiv.trans.{u3, u1, u2} α β γ e e') s)
Case conversion may be inaccurate. Consider using '#align local_equiv.restr_trans LocalEquiv.restr_transₓ'. -/
theorem restr_trans (s : Set α) : (e.restr s).trans e' = (e.trans e').restr s :=
  (LocalEquiv.ext (fun x => rfl) fun x => rfl) <|
    by
    simp [trans_source, inter_comm]
    rwa [inter_assoc]
#align local_equiv.restr_trans LocalEquiv.restr_trans

/- warning: local_equiv.mem_symm_trans_source -> LocalEquiv.mem_symm_trans_source is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (e : LocalEquiv.{u1, u2} α β) {e' : LocalEquiv.{u1, u3} α γ} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β e)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u3} α γ e')) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e x) (LocalEquiv.source.{u2, u3} β γ (LocalEquiv.trans.{u2, u1, u3} β α γ (LocalEquiv.symm.{u1, u2} α β e) e')))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (e : LocalEquiv.{u3, u1} α β) {e' : LocalEquiv.{u3, u2} α γ} {x : α}, (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (LocalEquiv.source.{u3, u1} α β e)) -> (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (LocalEquiv.source.{u3, u2} α γ e')) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (LocalEquiv.toFun.{u3, u1} α β e x) (LocalEquiv.source.{u1, u2} β γ (LocalEquiv.trans.{u1, u3, u2} β α γ (LocalEquiv.symm.{u3, u1} α β e) e')))
Case conversion may be inaccurate. Consider using '#align local_equiv.mem_symm_trans_source LocalEquiv.mem_symm_trans_sourceₓ'. -/
/-- A lemma commonly useful when `e` and `e'` are charts of a manifold. -/
theorem mem_symm_trans_source {e' : LocalEquiv α γ} {x : α} (he : x ∈ e.source)
    (he' : x ∈ e'.source) : e x ∈ (e.symm.trans e').source :=
  ⟨e.MapsTo he, by rwa [mem_preimage, LocalEquiv.symm_symm, e.left_inv he]⟩
#align local_equiv.mem_symm_trans_source LocalEquiv.mem_symm_trans_source

#print LocalEquiv.transEquiv /-
/-- Postcompose a local equivalence with an equivalence.
We modify the source and target to have better definitional behavior. -/
@[simps]
def transEquiv (e' : β ≃ γ) : LocalEquiv α γ :=
  (e.trans e'.toLocalEquiv).copy _ rfl _ rfl e.source (inter_univ _) (e'.symm ⁻¹' e.target)
    (univ_inter _)
#align local_equiv.trans_equiv LocalEquiv.transEquiv
-/

/- warning: local_equiv.trans_equiv_eq_trans -> LocalEquiv.transEquiv_eq_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (e : LocalEquiv.{u1, u2} α β) (e' : Equiv.{succ u2, succ u3} β γ), Eq.{max (succ u1) (succ u3)} (LocalEquiv.{u1, u3} α γ) (LocalEquiv.transEquiv.{u1, u2, u3} α β γ e e') (LocalEquiv.trans.{u1, u2, u3} α β γ e (Equiv.toLocalEquiv.{u2, u3} β γ e'))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} (e : LocalEquiv.{u1, u3} α β) (e' : Equiv.{succ u3, succ u2} β γ), Eq.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α γ) (LocalEquiv.transEquiv.{u1, u3, u2} α β γ e e') (LocalEquiv.trans.{u1, u3, u2} α β γ e (Equiv.toLocalEquiv.{u3, u2} β γ e'))
Case conversion may be inaccurate. Consider using '#align local_equiv.trans_equiv_eq_trans LocalEquiv.transEquiv_eq_transₓ'. -/
theorem transEquiv_eq_trans (e' : β ≃ γ) : e.transEquiv e' = e.trans e'.toLocalEquiv :=
  copy_eq _ _ _ _ _ _ _ _ _
#align local_equiv.trans_equiv_eq_trans LocalEquiv.transEquiv_eq_trans

#print Equiv.transLocalEquiv /-
/-- Precompose a local equivalence with an equivalence.
We modify the source and target to have better definitional behavior. -/
@[simps]
def Equiv.transLocalEquiv (e : α ≃ β) : LocalEquiv α γ :=
  (e.toLocalEquiv.trans e').copy _ rfl _ rfl (e ⁻¹' e'.source) (univ_inter _) e'.target
    (inter_univ _)
#align equiv.trans_local_equiv Equiv.transLocalEquiv
-/

/- warning: equiv.trans_local_equiv_eq_trans -> Equiv.transLocalEquiv_eq_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (e' : LocalEquiv.{u2, u3} β γ) (e : Equiv.{succ u1, succ u2} α β), Eq.{max (succ u1) (succ u3)} (LocalEquiv.{u1, u3} α γ) (Equiv.transLocalEquiv.{u1, u2, u3} α β γ e' e) (LocalEquiv.trans.{u1, u2, u3} α β γ (Equiv.toLocalEquiv.{u1, u2} α β e) e')
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (e' : LocalEquiv.{u2, u1} β γ) (e : Equiv.{succ u3, succ u2} α β), Eq.{max (succ u3) (succ u1)} (LocalEquiv.{u3, u1} α γ) (Equiv.transLocalEquiv.{u3, u2, u1} α β γ e' e) (LocalEquiv.trans.{u3, u2, u1} α β γ (Equiv.toLocalEquiv.{u3, u2} α β e) e')
Case conversion may be inaccurate. Consider using '#align equiv.trans_local_equiv_eq_trans Equiv.transLocalEquiv_eq_transₓ'. -/
theorem Equiv.transLocalEquiv_eq_trans (e : α ≃ β) :
    e.transLocalEquiv e' = e.toLocalEquiv.trans e' :=
  copy_eq _ _ _ _ _ _ _ _ _
#align equiv.trans_local_equiv_eq_trans Equiv.transLocalEquiv_eq_trans

#print LocalEquiv.EqOnSource /-
/-- `eq_on_source e e'` means that `e` and `e'` have the same source, and coincide there. Then `e`
and `e'` should really be considered the same local equiv. -/
def EqOnSource (e e' : LocalEquiv α β) : Prop :=
  e.source = e'.source ∧ e.source.EqOn e e'
#align local_equiv.eq_on_source LocalEquiv.EqOnSource
-/

#print LocalEquiv.eqOnSourceSetoid /-
/-- `eq_on_source` is an equivalence relation -/
instance eqOnSourceSetoid : Setoid (LocalEquiv α β)
    where
  R := EqOnSource
  iseqv :=
    ⟨fun e => by simp [eq_on_source], fun e e' h =>
      by
      simp [eq_on_source, h.1.symm]
      exact fun x hx => (h.2 hx).symm, fun e e' e'' h h' =>
      ⟨by rwa [← h'.1, ← h.1], fun x hx => by
        rw [← h'.2, h.2 hx]
        rwa [← h.1]⟩⟩
#align local_equiv.eq_on_source_setoid LocalEquiv.eqOnSourceSetoid
-/

/- warning: local_equiv.eq_on_source_refl -> LocalEquiv.eqOnSource_refl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β), HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.eqOnSourceSetoid.{u1, u2} α β)) e e
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β), HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalEquiv.{u2, u1} α β) (instHasEquiv.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalEquiv.eqOnSourceSetoid.{u2, u1} α β)) e e
Case conversion may be inaccurate. Consider using '#align local_equiv.eq_on_source_refl LocalEquiv.eqOnSource_reflₓ'. -/
theorem eqOnSource_refl : e ≈ e :=
  Setoid.refl _
#align local_equiv.eq_on_source_refl LocalEquiv.eqOnSource_refl

/- warning: local_equiv.eq_on_source.source_eq -> LocalEquiv.EqOnSource.source_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {e' : LocalEquiv.{u1, u2} α β}, (HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.eqOnSourceSetoid.{u1, u2} α β)) e e') -> (Eq.{succ u1} (Set.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (LocalEquiv.source.{u1, u2} α β e'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {e' : LocalEquiv.{u2, u1} α β}, (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalEquiv.{u2, u1} α β) (instHasEquiv.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalEquiv.eqOnSourceSetoid.{u2, u1} α β)) e e') -> (Eq.{succ u2} (Set.{u2} α) (LocalEquiv.source.{u2, u1} α β e) (LocalEquiv.source.{u2, u1} α β e'))
Case conversion may be inaccurate. Consider using '#align local_equiv.eq_on_source.source_eq LocalEquiv.EqOnSource.source_eqₓ'. -/
/-- Two equivalent local equivs have the same source -/
theorem EqOnSource.source_eq {e e' : LocalEquiv α β} (h : e ≈ e') : e.source = e'.source :=
  h.1
#align local_equiv.eq_on_source.source_eq LocalEquiv.EqOnSource.source_eq

/- warning: local_equiv.eq_on_source.eq_on -> LocalEquiv.EqOnSource.eqOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {e' : LocalEquiv.{u1, u2} α β}, (HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.eqOnSourceSetoid.{u1, u2} α β)) e e') -> (Set.EqOn.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e') (LocalEquiv.source.{u1, u2} α β e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {e' : LocalEquiv.{u2, u1} α β}, (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalEquiv.{u2, u1} α β) (instHasEquiv.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalEquiv.eqOnSourceSetoid.{u2, u1} α β)) e e') -> (Set.EqOn.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e) (LocalEquiv.toFun.{u2, u1} α β e') (LocalEquiv.source.{u2, u1} α β e))
Case conversion may be inaccurate. Consider using '#align local_equiv.eq_on_source.eq_on LocalEquiv.EqOnSource.eqOnₓ'. -/
/-- Two equivalent local equivs coincide on the source -/
theorem EqOnSource.eqOn {e e' : LocalEquiv α β} (h : e ≈ e') : e.source.EqOn e e' :=
  h.2
#align local_equiv.eq_on_source.eq_on LocalEquiv.EqOnSource.eqOn

/- warning: local_equiv.eq_on_source.target_eq -> LocalEquiv.EqOnSource.target_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {e' : LocalEquiv.{u1, u2} α β}, (HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.eqOnSourceSetoid.{u1, u2} α β)) e e') -> (Eq.{succ u2} (Set.{u2} β) (LocalEquiv.target.{u1, u2} α β e) (LocalEquiv.target.{u1, u2} α β e'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {e' : LocalEquiv.{u2, u1} α β}, (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalEquiv.{u2, u1} α β) (instHasEquiv.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalEquiv.eqOnSourceSetoid.{u2, u1} α β)) e e') -> (Eq.{succ u1} (Set.{u1} β) (LocalEquiv.target.{u2, u1} α β e) (LocalEquiv.target.{u2, u1} α β e'))
Case conversion may be inaccurate. Consider using '#align local_equiv.eq_on_source.target_eq LocalEquiv.EqOnSource.target_eqₓ'. -/
/-- Two equivalent local equivs have the same target -/
theorem EqOnSource.target_eq {e e' : LocalEquiv α β} (h : e ≈ e') : e.target = e'.target := by
  simp only [← image_source_eq_target, ← h.source_eq, h.2.image_eq]
#align local_equiv.eq_on_source.target_eq LocalEquiv.EqOnSource.target_eq

/- warning: local_equiv.eq_on_source.symm' -> LocalEquiv.EqOnSource.symm' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {e' : LocalEquiv.{u1, u2} α β}, (HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.eqOnSourceSetoid.{u1, u2} α β)) e e') -> (HasEquivₓ.Equiv.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (setoidHasEquiv.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (LocalEquiv.eqOnSourceSetoid.{u2, u1} β α)) (LocalEquiv.symm.{u1, u2} α β e) (LocalEquiv.symm.{u1, u2} α β e'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {e' : LocalEquiv.{u2, u1} α β}, (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalEquiv.{u2, u1} α β) (instHasEquiv.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalEquiv.eqOnSourceSetoid.{u2, u1} α β)) e e') -> (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalEquiv.{u1, u2} β α) (instHasEquiv.{max (succ u2) (succ u1)} (LocalEquiv.{u1, u2} β α) (LocalEquiv.eqOnSourceSetoid.{u1, u2} β α)) (LocalEquiv.symm.{u2, u1} α β e) (LocalEquiv.symm.{u2, u1} α β e'))
Case conversion may be inaccurate. Consider using '#align local_equiv.eq_on_source.symm' LocalEquiv.EqOnSource.symm'ₓ'. -/
/-- If two local equivs are equivalent, so are their inverses. -/
theorem EqOnSource.symm' {e e' : LocalEquiv α β} (h : e ≈ e') : e.symm ≈ e'.symm :=
  by
  refine' ⟨h.target_eq, eq_on_of_left_inv_on_of_right_inv_on e.left_inv_on _ _⟩ <;>
    simp only [symm_source, h.target_eq, h.source_eq, e'.symm_maps_to]
  exact e'.right_inv_on.congr_right e'.symm_maps_to (h.source_eq ▸ h.eq_on.symm)
#align local_equiv.eq_on_source.symm' LocalEquiv.EqOnSource.symm'

/- warning: local_equiv.eq_on_source.symm_eq_on -> LocalEquiv.EqOnSource.symm_eqOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {e' : LocalEquiv.{u1, u2} α β}, (HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.eqOnSourceSetoid.{u1, u2} α β)) e e') -> (Set.EqOn.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e)) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e')) (LocalEquiv.target.{u1, u2} α β e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {e' : LocalEquiv.{u2, u1} α β}, (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalEquiv.{u2, u1} α β) (instHasEquiv.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalEquiv.eqOnSourceSetoid.{u2, u1} α β)) e e') -> (Set.EqOn.{u1, u2} β α (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e)) (LocalEquiv.toFun.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e')) (LocalEquiv.target.{u2, u1} α β e))
Case conversion may be inaccurate. Consider using '#align local_equiv.eq_on_source.symm_eq_on LocalEquiv.EqOnSource.symm_eqOnₓ'. -/
/-- Two equivalent local equivs have coinciding inverses on the target -/
theorem EqOnSource.symm_eqOn {e e' : LocalEquiv α β} (h : e ≈ e') : EqOn e.symm e'.symm e.target :=
  h.symm'.EqOn
#align local_equiv.eq_on_source.symm_eq_on LocalEquiv.EqOnSource.symm_eqOn

/- warning: local_equiv.eq_on_source.trans' -> LocalEquiv.EqOnSource.trans' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {e : LocalEquiv.{u1, u2} α β} {e' : LocalEquiv.{u1, u2} α β} {f : LocalEquiv.{u2, u3} β γ} {f' : LocalEquiv.{u2, u3} β γ}, (HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.eqOnSourceSetoid.{u1, u2} α β)) e e') -> (HasEquivₓ.Equiv.{max (succ u2) (succ u3)} (LocalEquiv.{u2, u3} β γ) (setoidHasEquiv.{max (succ u2) (succ u3)} (LocalEquiv.{u2, u3} β γ) (LocalEquiv.eqOnSourceSetoid.{u2, u3} β γ)) f f') -> (HasEquivₓ.Equiv.{max (succ u1) (succ u3)} (LocalEquiv.{u1, u3} α γ) (setoidHasEquiv.{max (succ u1) (succ u3)} (LocalEquiv.{u1, u3} α γ) (LocalEquiv.eqOnSourceSetoid.{u1, u3} α γ)) (LocalEquiv.trans.{u1, u2, u3} α β γ e f) (LocalEquiv.trans.{u1, u2, u3} α β γ e' f'))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {e : LocalEquiv.{u3, u2} α β} {e' : LocalEquiv.{u3, u2} α β} {f : LocalEquiv.{u2, u1} β γ} {f' : LocalEquiv.{u2, u1} β γ}, (HasEquiv.Equiv.{max (succ u3) (succ u2), 0} (LocalEquiv.{u3, u2} α β) (instHasEquiv.{max (succ u3) (succ u2)} (LocalEquiv.{u3, u2} α β) (LocalEquiv.eqOnSourceSetoid.{u3, u2} α β)) e e') -> (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalEquiv.{u2, u1} β γ) (instHasEquiv.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β γ) (LocalEquiv.eqOnSourceSetoid.{u2, u1} β γ)) f f') -> (HasEquiv.Equiv.{max (succ u3) (succ u1), 0} (LocalEquiv.{u3, u1} α γ) (instHasEquiv.{max (succ u3) (succ u1)} (LocalEquiv.{u3, u1} α γ) (LocalEquiv.eqOnSourceSetoid.{u3, u1} α γ)) (LocalEquiv.trans.{u3, u2, u1} α β γ e f) (LocalEquiv.trans.{u3, u2, u1} α β γ e' f'))
Case conversion may be inaccurate. Consider using '#align local_equiv.eq_on_source.trans' LocalEquiv.EqOnSource.trans'ₓ'. -/
/-- Composition of local equivs respects equivalence -/
theorem EqOnSource.trans' {e e' : LocalEquiv α β} {f f' : LocalEquiv β γ} (he : e ≈ e')
    (hf : f ≈ f') : e.trans f ≈ e'.trans f' :=
  by
  constructor
  · rw [trans_source'', trans_source'', ← he.target_eq, ← hf.1]
    exact (he.symm'.eq_on.mono <| inter_subset_left _ _).image_eq
  · intro x hx
    rw [trans_source] at hx
    simp [(he.2 hx.1).symm, hf.2 hx.2]
#align local_equiv.eq_on_source.trans' LocalEquiv.EqOnSource.trans'

/- warning: local_equiv.eq_on_source.restr -> LocalEquiv.EqOnSource.restr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {e' : LocalEquiv.{u1, u2} α β}, (HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.eqOnSourceSetoid.{u1, u2} α β)) e e') -> (forall (s : Set.{u1} α), HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.eqOnSourceSetoid.{u1, u2} α β)) (LocalEquiv.restr.{u1, u2} α β e s) (LocalEquiv.restr.{u1, u2} α β e' s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {e' : LocalEquiv.{u2, u1} α β}, (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalEquiv.{u2, u1} α β) (instHasEquiv.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalEquiv.eqOnSourceSetoid.{u2, u1} α β)) e e') -> (forall (s : Set.{u2} α), HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalEquiv.{u2, u1} α β) (instHasEquiv.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalEquiv.eqOnSourceSetoid.{u2, u1} α β)) (LocalEquiv.restr.{u2, u1} α β e s) (LocalEquiv.restr.{u2, u1} α β e' s))
Case conversion may be inaccurate. Consider using '#align local_equiv.eq_on_source.restr LocalEquiv.EqOnSource.restrₓ'. -/
/-- Restriction of local equivs respects equivalence -/
theorem EqOnSource.restr {e e' : LocalEquiv α β} (he : e ≈ e') (s : Set α) :
    e.restr s ≈ e'.restr s := by
  constructor
  · simp [he.1]
  · intro x hx
    simp only [mem_inter_iff, restr_source] at hx
    exact he.2 hx.1
#align local_equiv.eq_on_source.restr LocalEquiv.EqOnSource.restr

/- warning: local_equiv.eq_on_source.source_inter_preimage_eq -> LocalEquiv.EqOnSource.source_inter_preimage_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {e : LocalEquiv.{u1, u2} α β} {e' : LocalEquiv.{u1, u2} α β}, (HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.eqOnSourceSetoid.{u1, u2} α β)) e e') -> (forall (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e) s)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (LocalEquiv.source.{u1, u2} α β e') (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e') s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {e : LocalEquiv.{u2, u1} α β} {e' : LocalEquiv.{u2, u1} α β}, (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalEquiv.{u2, u1} α β) (instHasEquiv.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalEquiv.eqOnSourceSetoid.{u2, u1} α β)) e e') -> (forall (s : Set.{u1} β), Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e) (Set.preimage.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e) s)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (LocalEquiv.source.{u2, u1} α β e') (Set.preimage.{u2, u1} α β (LocalEquiv.toFun.{u2, u1} α β e') s)))
Case conversion may be inaccurate. Consider using '#align local_equiv.eq_on_source.source_inter_preimage_eq LocalEquiv.EqOnSource.source_inter_preimage_eqₓ'. -/
/-- Preimages are respected by equivalence -/
theorem EqOnSource.source_inter_preimage_eq {e e' : LocalEquiv α β} (he : e ≈ e') (s : Set β) :
    e.source ∩ e ⁻¹' s = e'.source ∩ e' ⁻¹' s := by rw [he.eq_on.inter_preimage_eq, he.source_eq]
#align local_equiv.eq_on_source.source_inter_preimage_eq LocalEquiv.EqOnSource.source_inter_preimage_eq

/- warning: local_equiv.trans_self_symm -> LocalEquiv.trans_self_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β), HasEquivₓ.Equiv.{succ u1} (LocalEquiv.{u1, u1} α α) (setoidHasEquiv.{succ u1} (LocalEquiv.{u1, u1} α α) (LocalEquiv.eqOnSourceSetoid.{u1, u1} α α)) (LocalEquiv.trans.{u1, u2, u1} α β α e (LocalEquiv.symm.{u1, u2} α β e)) (LocalEquiv.ofSet.{u1} α (LocalEquiv.source.{u1, u2} α β e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β), HasEquiv.Equiv.{succ u2, 0} (LocalEquiv.{u2, u2} α α) (instHasEquiv.{succ u2} (LocalEquiv.{u2, u2} α α) (LocalEquiv.eqOnSourceSetoid.{u2, u2} α α)) (LocalEquiv.trans.{u2, u1, u2} α β α e (LocalEquiv.symm.{u2, u1} α β e)) (LocalEquiv.ofSet.{u2} α (LocalEquiv.source.{u2, u1} α β e))
Case conversion may be inaccurate. Consider using '#align local_equiv.trans_self_symm LocalEquiv.trans_self_symmₓ'. -/
/-- Composition of a local equiv and its inverse is equivalent to the restriction of the identity
to the source -/
theorem trans_self_symm : e.trans e.symm ≈ LocalEquiv.ofSet e.source :=
  by
  have A : (e.trans e.symm).source = e.source := by mfld_set_tac
  refine' ⟨by simp [A], fun x hx => _⟩
  rw [A] at hx
  simp only [hx, mfld_simps]
#align local_equiv.trans_self_symm LocalEquiv.trans_self_symm

#print LocalEquiv.trans_symm_self /-
/-- Composition of the inverse of a local equiv and this local equiv is equivalent to the
restriction of the identity to the target -/
theorem trans_symm_self : e.symm.trans e ≈ LocalEquiv.ofSet e.target :=
  trans_self_symm e.symm
#align local_equiv.trans_symm_self LocalEquiv.trans_symm_self
-/

/- warning: local_equiv.eq_of_eq_on_source_univ -> LocalEquiv.eq_of_eq_on_source_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u1, u2} α β), (HasEquivₓ.Equiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (setoidHasEquiv.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.eqOnSourceSetoid.{u1, u2} α β)) e e') -> (Eq.{succ u1} (Set.{u1} α) (LocalEquiv.source.{u1, u2} α β e) (Set.univ.{u1} α)) -> (Eq.{succ u2} (Set.{u2} β) (LocalEquiv.target.{u1, u2} α β e) (Set.univ.{u2} β)) -> (Eq.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) e e')
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β) (e' : LocalEquiv.{u2, u1} α β), (HasEquiv.Equiv.{max (succ u2) (succ u1), 0} (LocalEquiv.{u2, u1} α β) (instHasEquiv.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalEquiv.eqOnSourceSetoid.{u2, u1} α β)) e e') -> (Eq.{succ u2} (Set.{u2} α) (LocalEquiv.source.{u2, u1} α β e) (Set.univ.{u2} α)) -> (Eq.{succ u1} (Set.{u1} β) (LocalEquiv.target.{u2, u1} α β e) (Set.univ.{u1} β)) -> (Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) e e')
Case conversion may be inaccurate. Consider using '#align local_equiv.eq_of_eq_on_source_univ LocalEquiv.eq_of_eq_on_source_univₓ'. -/
/-- Two equivalent local equivs are equal when the source and target are univ -/
theorem eq_of_eq_on_source_univ (e e' : LocalEquiv α β) (h : e ≈ e') (s : e.source = univ)
    (t : e.target = univ) : e = e' :=
  by
  apply LocalEquiv.ext (fun x => _) (fun x => _) h.1
  · apply h.2
    rw [s]
    exact mem_univ _
  · apply h.symm'.2
    rw [symm_source, t]
    exact mem_univ _
#align local_equiv.eq_of_eq_on_source_univ LocalEquiv.eq_of_eq_on_source_univ

section Prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LocalEquiv.prod /-
/-- The product of two local equivs, as a local equiv on the product. -/
def prod (e : LocalEquiv α β) (e' : LocalEquiv γ δ) : LocalEquiv (α × γ) (β × δ)
    where
  source := e.source ×ˢ e'.source
  target := e.target ×ˢ e'.target
  toFun p := (e p.1, e' p.2)
  invFun p := (e.symm p.1, e'.symm p.2)
  map_source' p hp := by
    simp at hp
    simp [hp]
  map_target' p hp := by
    simp at hp
    simp [map_target, hp]
  left_inv' p hp := by
    simp at hp
    simp [hp]
  right_inv' p hp := by
    simp at hp
    simp [hp]
#align local_equiv.prod LocalEquiv.prod
-/

/- warning: local_equiv.prod_source -> LocalEquiv.prod_source is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u3, u4} γ δ), Eq.{succ (max u1 u3)} (Set.{max u1 u3} (Prod.{u1, u3} α γ)) (LocalEquiv.source.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (LocalEquiv.prod.{u1, u2, u3, u4} α β γ δ e e')) (Set.prod.{u1, u3} α γ (LocalEquiv.source.{u1, u2} α β e) (LocalEquiv.source.{u3, u4} γ δ e'))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} (e : LocalEquiv.{u4, u3} α β) (e' : LocalEquiv.{u2, u1} γ δ), Eq.{max (succ u4) (succ u2)} (Set.{max u4 u2} (Prod.{u4, u2} α γ)) (LocalEquiv.source.{max u4 u2, max u3 u1} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (LocalEquiv.prod.{u4, u3, u2, u1} α β γ δ e e')) (Set.prod.{u4, u2} α γ (LocalEquiv.source.{u4, u3} α β e) (LocalEquiv.source.{u2, u1} γ δ e'))
Case conversion may be inaccurate. Consider using '#align local_equiv.prod_source LocalEquiv.prod_sourceₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, mfld_simps]
theorem prod_source (e : LocalEquiv α β) (e' : LocalEquiv γ δ) :
    (e.Prod e').source = e.source ×ˢ e'.source :=
  rfl
#align local_equiv.prod_source LocalEquiv.prod_source

/- warning: local_equiv.prod_target -> LocalEquiv.prod_target is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u3, u4} γ δ), Eq.{succ (max u2 u4)} (Set.{max u2 u4} (Prod.{u2, u4} β δ)) (LocalEquiv.target.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (LocalEquiv.prod.{u1, u2, u3, u4} α β γ δ e e')) (Set.prod.{u2, u4} β δ (LocalEquiv.target.{u1, u2} α β e) (LocalEquiv.target.{u3, u4} γ δ e'))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} (e : LocalEquiv.{u4, u3} α β) (e' : LocalEquiv.{u2, u1} γ δ), Eq.{max (succ u3) (succ u1)} (Set.{max u3 u1} (Prod.{u3, u1} β δ)) (LocalEquiv.target.{max u4 u2, max u3 u1} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (LocalEquiv.prod.{u4, u3, u2, u1} α β γ δ e e')) (Set.prod.{u3, u1} β δ (LocalEquiv.target.{u4, u3} α β e) (LocalEquiv.target.{u2, u1} γ δ e'))
Case conversion may be inaccurate. Consider using '#align local_equiv.prod_target LocalEquiv.prod_targetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, mfld_simps]
theorem prod_target (e : LocalEquiv α β) (e' : LocalEquiv γ δ) :
    (e.Prod e').target = e.target ×ˢ e'.target :=
  rfl
#align local_equiv.prod_target LocalEquiv.prod_target

/- warning: local_equiv.prod_coe -> LocalEquiv.prod_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u3, u4} γ δ), Eq.{max (max (succ u1) (succ u3)) (succ u2) (succ u4)} ((fun (_x : LocalEquiv.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ)) => (Prod.{u1, u3} α γ) -> (Prod.{u2, u4} β δ)) (LocalEquiv.prod.{u1, u2, u3, u4} α β γ δ e e')) (coeFn.{max (succ (max u1 u3)) (succ (max u2 u4)), max (succ (max u1 u3)) (succ (max u2 u4))} (LocalEquiv.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ)) (fun (_x : LocalEquiv.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ)) => (Prod.{u1, u3} α γ) -> (Prod.{u2, u4} β δ)) (LocalEquiv.hasCoeToFun.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ)) (LocalEquiv.prod.{u1, u2, u3, u4} α β γ δ e e')) (fun (p : Prod.{u1, u3} α γ) => Prod.mk.{u2, u4} β δ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (fun (_x : LocalEquiv.{u1, u2} α β) => α -> β) (LocalEquiv.hasCoeToFun.{u1, u2} α β) e (Prod.fst.{u1, u3} α γ p)) (coeFn.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (LocalEquiv.{u3, u4} γ δ) (fun (_x : LocalEquiv.{u3, u4} γ δ) => γ -> δ) (LocalEquiv.hasCoeToFun.{u3, u4} γ δ) e' (Prod.snd.{u1, u3} α γ p)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} (e : LocalEquiv.{u4, u3} α β) (e' : LocalEquiv.{u2, u1} γ δ), Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} ((Prod.{u4, u2} α γ) -> (Prod.{u3, u1} β δ)) (LocalEquiv.toFun.{max u4 u2, max u3 u1} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (LocalEquiv.prod.{u4, u3, u2, u1} α β γ δ e e')) (fun (p : Prod.{u4, u2} α γ) => Prod.mk.{u3, u1} β δ (LocalEquiv.toFun.{u4, u3} α β e (Prod.fst.{u4, u2} α γ p)) (LocalEquiv.toFun.{u2, u1} γ δ e' (Prod.snd.{u4, u2} α γ p)))
Case conversion may be inaccurate. Consider using '#align local_equiv.prod_coe LocalEquiv.prod_coeₓ'. -/
@[simp, mfld_simps]
theorem prod_coe (e : LocalEquiv α β) (e' : LocalEquiv γ δ) :
    (e.Prod e' : α × γ → β × δ) = fun p => (e p.1, e' p.2) :=
  rfl
#align local_equiv.prod_coe LocalEquiv.prod_coe

/- warning: local_equiv.prod_coe_symm -> LocalEquiv.prod_coe_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u3, u4} γ δ), Eq.{max (max (succ u2) (succ u4)) (succ u1) (succ u3)} ((fun (_x : LocalEquiv.{max u2 u4, max u1 u3} (Prod.{u2, u4} β δ) (Prod.{u1, u3} α γ)) => (Prod.{u2, u4} β δ) -> (Prod.{u1, u3} α γ)) (LocalEquiv.symm.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (LocalEquiv.prod.{u1, u2, u3, u4} α β γ δ e e'))) (coeFn.{max (succ (max u2 u4)) (succ (max u1 u3)), max (succ (max u2 u4)) (succ (max u1 u3))} (LocalEquiv.{max u2 u4, max u1 u3} (Prod.{u2, u4} β δ) (Prod.{u1, u3} α γ)) (fun (_x : LocalEquiv.{max u2 u4, max u1 u3} (Prod.{u2, u4} β δ) (Prod.{u1, u3} α γ)) => (Prod.{u2, u4} β δ) -> (Prod.{u1, u3} α γ)) (LocalEquiv.hasCoeToFun.{max u2 u4, max u1 u3} (Prod.{u2, u4} β δ) (Prod.{u1, u3} α γ)) (LocalEquiv.symm.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (LocalEquiv.prod.{u1, u2, u3, u4} α β γ δ e e'))) (fun (p : Prod.{u2, u4} β δ) => Prod.mk.{u1, u3} α γ (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (fun (_x : LocalEquiv.{u2, u1} β α) => β -> α) (LocalEquiv.hasCoeToFun.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β e) (Prod.fst.{u2, u4} β δ p)) (coeFn.{max (succ u4) (succ u3), max (succ u4) (succ u3)} (LocalEquiv.{u4, u3} δ γ) (fun (_x : LocalEquiv.{u4, u3} δ γ) => δ -> γ) (LocalEquiv.hasCoeToFun.{u4, u3} δ γ) (LocalEquiv.symm.{u3, u4} γ δ e') (Prod.snd.{u2, u4} β δ p)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} (e : LocalEquiv.{u4, u3} α β) (e' : LocalEquiv.{u2, u1} γ δ), Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} ((Prod.{u3, u1} β δ) -> (Prod.{u4, u2} α γ)) (LocalEquiv.toFun.{max u3 u1, max u4 u2} (Prod.{u3, u1} β δ) (Prod.{u4, u2} α γ) (LocalEquiv.symm.{max u4 u2, max u3 u1} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (LocalEquiv.prod.{u4, u3, u2, u1} α β γ δ e e'))) (fun (p : Prod.{u3, u1} β δ) => Prod.mk.{u4, u2} α γ (LocalEquiv.toFun.{u3, u4} β α (LocalEquiv.symm.{u4, u3} α β e) (Prod.fst.{u3, u1} β δ p)) (LocalEquiv.toFun.{u1, u2} δ γ (LocalEquiv.symm.{u2, u1} γ δ e') (Prod.snd.{u3, u1} β δ p)))
Case conversion may be inaccurate. Consider using '#align local_equiv.prod_coe_symm LocalEquiv.prod_coe_symmₓ'. -/
theorem prod_coe_symm (e : LocalEquiv α β) (e' : LocalEquiv γ δ) :
    ((e.Prod e').symm : β × δ → α × γ) = fun p => (e.symm p.1, e'.symm p.2) :=
  rfl
#align local_equiv.prod_coe_symm LocalEquiv.prod_coe_symm

/- warning: local_equiv.prod_symm -> LocalEquiv.prod_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u3, u4} γ δ), Eq.{max (succ (max u2 u4)) (succ (max u1 u3))} (LocalEquiv.{max u2 u4, max u1 u3} (Prod.{u2, u4} β δ) (Prod.{u1, u3} α γ)) (LocalEquiv.symm.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (LocalEquiv.prod.{u1, u2, u3, u4} α β γ δ e e')) (LocalEquiv.prod.{u2, u1, u4, u3} β α δ γ (LocalEquiv.symm.{u1, u2} α β e) (LocalEquiv.symm.{u3, u4} γ δ e'))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} (e : LocalEquiv.{u4, u3} α β) (e' : LocalEquiv.{u2, u1} γ δ), Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (LocalEquiv.{max u3 u1, max u4 u2} (Prod.{u3, u1} β δ) (Prod.{u4, u2} α γ)) (LocalEquiv.symm.{max u4 u2, max u3 u1} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (LocalEquiv.prod.{u4, u3, u2, u1} α β γ δ e e')) (LocalEquiv.prod.{u3, u4, u1, u2} β α δ γ (LocalEquiv.symm.{u4, u3} α β e) (LocalEquiv.symm.{u2, u1} γ δ e'))
Case conversion may be inaccurate. Consider using '#align local_equiv.prod_symm LocalEquiv.prod_symmₓ'. -/
@[simp, mfld_simps]
theorem prod_symm (e : LocalEquiv α β) (e' : LocalEquiv γ δ) :
    (e.Prod e').symm = e.symm.Prod e'.symm := by ext x <;> simp [prod_coe_symm]
#align local_equiv.prod_symm LocalEquiv.prod_symm

/- warning: local_equiv.refl_prod_refl -> LocalEquiv.refl_prod_refl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{succ (max u1 u2)} (LocalEquiv.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) (LocalEquiv.prod.{u1, u1, u2, u2} α α β β (LocalEquiv.refl.{u1} α) (LocalEquiv.refl.{u2} β)) (LocalEquiv.refl.{max u1 u2} (Prod.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u2) (succ u1)} (LocalEquiv.{max u1 u2, max u1 u2} (Prod.{u2, u1} α β) (Prod.{u2, u1} α β)) (LocalEquiv.prod.{u2, u2, u1, u1} α α β β (LocalEquiv.refl.{u2} α) (LocalEquiv.refl.{u1} β)) (LocalEquiv.refl.{max u1 u2} (Prod.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align local_equiv.refl_prod_refl LocalEquiv.refl_prod_reflₓ'. -/
@[simp, mfld_simps]
theorem refl_prod_refl : (LocalEquiv.refl α).Prod (LocalEquiv.refl β) = LocalEquiv.refl (α × β) :=
  by
  ext1 ⟨x, y⟩
  · rfl
  · rintro ⟨x, y⟩
    rfl
  exact univ_prod_univ
#align local_equiv.refl_prod_refl LocalEquiv.refl_prod_refl

/- warning: local_equiv.prod_trans -> LocalEquiv.prod_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {η : Type.{u5}} {ε : Type.{u6}} (e : LocalEquiv.{u1, u2} α β) (f : LocalEquiv.{u2, u3} β γ) (e' : LocalEquiv.{u4, u5} δ η) (f' : LocalEquiv.{u5, u6} η ε), Eq.{max (succ (max u1 u4)) (succ (max u3 u6))} (LocalEquiv.{max u1 u4, max u3 u6} (Prod.{u1, u4} α δ) (Prod.{u3, u6} γ ε)) (LocalEquiv.trans.{max u1 u4, max u2 u5, max u3 u6} (Prod.{u1, u4} α δ) (Prod.{u2, u5} β η) (Prod.{u3, u6} γ ε) (LocalEquiv.prod.{u1, u2, u4, u5} α β δ η e e') (LocalEquiv.prod.{u2, u3, u5, u6} β γ η ε f f')) (LocalEquiv.prod.{u1, u3, u4, u6} α γ δ ε (LocalEquiv.trans.{u1, u2, u3} α β γ e f) (LocalEquiv.trans.{u4, u5, u6} δ η ε e' f'))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} {η : Type.{u6}} {ε : Type.{u5}} (e : LocalEquiv.{u4, u3} α β) (f : LocalEquiv.{u3, u2} β γ) (e' : LocalEquiv.{u1, u6} δ η) (f' : LocalEquiv.{u6, u5} η ε), Eq.{max (max (max (succ u4) (succ u2)) (succ u1)) (succ u5)} (LocalEquiv.{max u4 u1, max u2 u5} (Prod.{u4, u1} α δ) (Prod.{u2, u5} γ ε)) (LocalEquiv.trans.{max u4 u1, max u3 u6, max u2 u5} (Prod.{u4, u1} α δ) (Prod.{u3, u6} β η) (Prod.{u2, u5} γ ε) (LocalEquiv.prod.{u4, u3, u1, u6} α β δ η e e') (LocalEquiv.prod.{u3, u2, u6, u5} β γ η ε f f')) (LocalEquiv.prod.{u4, u2, u1, u5} α γ δ ε (LocalEquiv.trans.{u4, u3, u2} α β γ e f) (LocalEquiv.trans.{u1, u6, u5} δ η ε e' f'))
Case conversion may be inaccurate. Consider using '#align local_equiv.prod_trans LocalEquiv.prod_transₓ'. -/
@[simp, mfld_simps]
theorem prod_trans {η : Type _} {ε : Type _} (e : LocalEquiv α β) (f : LocalEquiv β γ)
    (e' : LocalEquiv δ η) (f' : LocalEquiv η ε) :
    (e.Prod e').trans (f.Prod f') = (e.trans f).Prod (e'.trans f') := by
  ext x <;> simp [ext_iff] <;> tauto
#align local_equiv.prod_trans LocalEquiv.prod_trans

end Prod

#print LocalEquiv.piecewise /-
/-- Combine two `local_equiv`s using `set.piecewise`. The source of the new `local_equiv` is
`s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly for target.  The function
sends `e.source ∩ s` to `e.target ∩ t` using `e` and `e'.source \ s` to `e'.target \ t` using `e'`,
and similarly for the inverse function. The definition assumes `e.is_image s t` and
`e'.is_image s t`. -/
@[simps (config := { fullyApplied := false })]
def piecewise (e e' : LocalEquiv α β) (s : Set α) (t : Set β) [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t) : LocalEquiv α β
    where
  toFun := s.piecewise e e'
  invFun := t.piecewise e.symm e'.symm
  source := s.ite e.source e'.source
  target := t.ite e.target e'.target
  map_source' := H.MapsTo.piecewise_ite H'.compl.MapsTo
  map_target' := H.symm.MapsTo.piecewise_ite H'.symm.compl.MapsTo
  left_inv' := H.leftInvOn_piecewise H'
  right_inv' := H.symm.leftInvOn_piecewise H'.symm
#align local_equiv.piecewise LocalEquiv.piecewise
-/

/- warning: local_equiv.symm_piecewise -> LocalEquiv.symm_piecewise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u1, u2} α β) {s : Set.{u1} α} {t : Set.{u2} β} [_inst_1 : forall (x : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)] [_inst_2 : forall (y : β), Decidable (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y t)] (H : LocalEquiv.IsImage.{u1, u2} α β e s t) (H' : LocalEquiv.IsImage.{u1, u2} α β e' s t), Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (LocalEquiv.symm.{u1, u2} α β (LocalEquiv.piecewise.{u1, u2} α β e e' s t (fun (y : α) => _inst_1 y) (fun (x : β) => _inst_2 x) H H')) (LocalEquiv.piecewise.{u2, u1} β α (LocalEquiv.symm.{u1, u2} α β e) (LocalEquiv.symm.{u1, u2} α β e') t s (fun (x : β) => _inst_2 x) (fun (y : α) => _inst_1 y) (LocalEquiv.IsImage.symm.{u1, u2} α β e s t H) (LocalEquiv.IsImage.symm.{u1, u2} α β e' s t H'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β) (e' : LocalEquiv.{u2, u1} α β) {s : Set.{u2} α} {t : Set.{u1} β} [_inst_1 : forall (x : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)] [_inst_2 : forall (y : β), Decidable (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y t)] (H : LocalEquiv.IsImage.{u2, u1} α β e s t) (H' : LocalEquiv.IsImage.{u2, u1} α β e' s t), Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u1, u2} β α) (LocalEquiv.symm.{u2, u1} α β (LocalEquiv.piecewise.{u2, u1} α β e e' s t (fun (y : α) => _inst_1 y) (fun (x : β) => _inst_2 x) H H')) (LocalEquiv.piecewise.{u1, u2} β α (LocalEquiv.symm.{u2, u1} α β e) (LocalEquiv.symm.{u2, u1} α β e') t s (fun (x : β) => _inst_2 x) (fun (y : α) => _inst_1 y) (LocalEquiv.IsImage.symm.{u1, u2} α β e s t H) (LocalEquiv.IsImage.symm.{u1, u2} α β e' s t H'))
Case conversion may be inaccurate. Consider using '#align local_equiv.symm_piecewise LocalEquiv.symm_piecewiseₓ'. -/
theorem symm_piecewise (e e' : LocalEquiv α β) {s : Set α} {t : Set β} [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t) :
    (e.piecewise e' s t H H').symm = e.symm.piecewise e'.symm t s H.symm H'.symm :=
  rfl
#align local_equiv.symm_piecewise LocalEquiv.symm_piecewise

/- warning: local_equiv.disjoint_union -> LocalEquiv.disjointUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u1, u2} α β), (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (LocalEquiv.source.{u1, u2} α β e) (LocalEquiv.source.{u1, u2} α β e')) -> (Disjoint.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) (LocalEquiv.target.{u1, u2} α β e) (LocalEquiv.target.{u1, u2} α β e')) -> (forall [_inst_1 : forall (x : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β e))] [_inst_2 : forall (y : β), Decidable (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (LocalEquiv.target.{u1, u2} α β e))], LocalEquiv.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u1, u2} α β), (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) (LocalEquiv.source.{u1, u2} α β e) (LocalEquiv.source.{u1, u2} α β e')) -> (Disjoint.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} β) (Preorder.toLE.{u2} (Set.{u2} β) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β))))))))) (BooleanAlgebra.toBoundedOrder.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β))) (LocalEquiv.target.{u1, u2} α β e) (LocalEquiv.target.{u1, u2} α β e')) -> (forall [_inst_1 : forall (x : α), Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (LocalEquiv.source.{u1, u2} α β e))] [_inst_2 : forall (y : β), Decidable (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) y (LocalEquiv.target.{u1, u2} α β e))], LocalEquiv.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align local_equiv.disjoint_union LocalEquiv.disjointUnionₓ'. -/
/-- Combine two `local_equiv`s with disjoint sources and disjoint targets. We reuse
`local_equiv.piecewise`, then override `source` and `target` to ensure better definitional
equalities. -/
@[simps (config := { fullyApplied := false })]
def disjointUnion (e e' : LocalEquiv α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] : LocalEquiv α β :=
  (e.piecewise e' e.source e.target e.isImage_source_target <|
        e'.isImage_source_target_of_disjoint _ hs.symm ht.symm).copy
    _ rfl _ rfl (e.source ∪ e'.source) (ite_left _ _) (e.target ∪ e'.target) (ite_left _ _)
#align local_equiv.disjoint_union LocalEquiv.disjointUnion

/- warning: local_equiv.disjoint_union_eq_piecewise -> LocalEquiv.disjointUnion_eq_piecewise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : LocalEquiv.{u1, u2} α β) (e' : LocalEquiv.{u1, u2} α β) (hs : Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (LocalEquiv.source.{u1, u2} α β e) (LocalEquiv.source.{u1, u2} α β e')) (ht : Disjoint.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) (LocalEquiv.target.{u1, u2} α β e) (LocalEquiv.target.{u1, u2} α β e')) [_inst_1 : forall (x : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (LocalEquiv.source.{u1, u2} α β e))] [_inst_2 : forall (y : β), Decidable (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (LocalEquiv.target.{u1, u2} α β e))], Eq.{max (succ u1) (succ u2)} (LocalEquiv.{u1, u2} α β) (LocalEquiv.disjointUnion.{u1, u2} α β e e' hs ht (fun (x : α) => _inst_1 x) (fun (y : β) => _inst_2 y)) (LocalEquiv.piecewise.{u1, u2} α β e e' (LocalEquiv.source.{u1, u2} α β e) (LocalEquiv.target.{u1, u2} α β e) (fun (x : α) => _inst_1 x) (fun (y : β) => _inst_2 y) (LocalEquiv.isImage_source_target.{u1, u2} α β e) (LocalEquiv.isImage_source_target_of_disjoint.{u1, u2} α β e' e (Disjoint.symm.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (LocalEquiv.source.{u1, u2} α β e) (LocalEquiv.source.{u1, u2} α β e') hs) (Disjoint.symm.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) (LocalEquiv.target.{u1, u2} α β e) (LocalEquiv.target.{u1, u2} α β e') ht)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : LocalEquiv.{u2, u1} α β) (e' : LocalEquiv.{u2, u1} α β) (hs : Disjoint.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))))))))) (BooleanAlgebra.toBoundedOrder.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))) (LocalEquiv.source.{u2, u1} α β e) (LocalEquiv.source.{u2, u1} α β e')) (ht : Disjoint.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} β) (Preorder.toLE.{u1} (Set.{u1} β) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))) (LocalEquiv.target.{u2, u1} α β e) (LocalEquiv.target.{u2, u1} α β e')) [_inst_1 : forall (x : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (LocalEquiv.source.{u2, u1} α β e))] [_inst_2 : forall (y : β), Decidable (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (LocalEquiv.target.{u2, u1} α β e))], Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} α β) (LocalEquiv.disjointUnion.{u2, u1} α β e e' hs ht (fun (x : α) => _inst_1 x) (fun (y : β) => _inst_2 y)) (LocalEquiv.piecewise.{u2, u1} α β e e' (LocalEquiv.source.{u2, u1} α β e) (LocalEquiv.target.{u2, u1} α β e) (fun (x : α) => _inst_1 x) (fun (y : β) => _inst_2 y) (LocalEquiv.isImage_source_target.{u1, u2} α β e) (LocalEquiv.isImage_source_target_of_disjoint.{u1, u2} α β e' e (Disjoint.symm.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))))))))) (BooleanAlgebra.toBoundedOrder.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))) (LocalEquiv.source.{u2, u1} α β e) (LocalEquiv.source.{u2, u1} α β e') hs) (Disjoint.symm.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} β) (Preorder.toLE.{u1} (Set.{u1} β) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))) (LocalEquiv.target.{u2, u1} α β e) (LocalEquiv.target.{u2, u1} α β e') ht)))
Case conversion may be inaccurate. Consider using '#align local_equiv.disjoint_union_eq_piecewise LocalEquiv.disjointUnion_eq_piecewiseₓ'. -/
theorem disjointUnion_eq_piecewise (e e' : LocalEquiv α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] :
    e.disjointUnion e' hs ht =
      e.piecewise e' e.source e.target e.isImage_source_target
        (e'.isImage_source_target_of_disjoint _ hs.symm ht.symm) :=
  copy_eq _ _ _ _ _ _ _ _ _
#align local_equiv.disjoint_union_eq_piecewise LocalEquiv.disjointUnion_eq_piecewise

section Pi

variable {ι : Type _} {αi βi : ι → Type _} (ei : ∀ i, LocalEquiv (αi i) (βi i))

#print LocalEquiv.pi /-
/-- The product of a family of local equivs, as a local equiv on the pi type. -/
@[simps (config := mfld_cfg)]
protected def pi : LocalEquiv (∀ i, αi i) (∀ i, βi i)
    where
  toFun f i := ei i (f i)
  invFun f i := (ei i).symm (f i)
  source := pi univ fun i => (ei i).source
  target := pi univ fun i => (ei i).target
  map_source' f hf i hi := (ei i).map_source (hf i hi)
  map_target' f hf i hi := (ei i).map_target (hf i hi)
  left_inv' f hf := funext fun i => (ei i).left_inv (hf i trivial)
  right_inv' f hf := funext fun i => (ei i).right_inv (hf i trivial)
#align local_equiv.pi LocalEquiv.pi
-/

end Pi

end LocalEquiv

namespace Set

#print Set.BijOn.toLocalEquiv /-
-- All arguments are explicit to avoid missing information in the pretty printer output
/-- A bijection between two sets `s : set α` and `t : set β` provides a local equivalence
between `α` and `β`. -/
@[simps (config := { fullyApplied := false })]
noncomputable def BijOn.toLocalEquiv [Nonempty α] (f : α → β) (s : Set α) (t : Set β)
    (hf : BijOn f s t) : LocalEquiv α β where
  toFun := f
  invFun := invFunOn f s
  source := s
  target := t
  map_source' := hf.MapsTo
  map_target' := hf.SurjOn.mapsTo_invFunOn
  left_inv' := hf.invOn_invFunOn.1
  right_inv' := hf.invOn_invFunOn.2
#align set.bij_on.to_local_equiv Set.BijOn.toLocalEquiv
-/

#print Set.InjOn.toLocalEquiv /-
/-- A map injective on a subset of its domain provides a local equivalence. -/
@[simp, mfld_simps]
noncomputable def InjOn.toLocalEquiv [Nonempty α] (f : α → β) (s : Set α) (hf : InjOn f s) :
    LocalEquiv α β :=
  hf.bijOn_image.toLocalEquiv f s (f '' s)
#align set.inj_on.to_local_equiv Set.InjOn.toLocalEquiv
-/

end Set

namespace Equiv

/- equivs give rise to local_equiv. We set up simp lemmas to reduce most properties of the local
equiv to that of the equiv. -/
variable (e : α ≃ β) (e' : β ≃ γ)

#print Equiv.refl_toLocalEquiv /-
@[simp, mfld_simps]
theorem refl_toLocalEquiv : (Equiv.refl α).toLocalEquiv = LocalEquiv.refl α :=
  rfl
#align equiv.refl_to_local_equiv Equiv.refl_toLocalEquiv
-/

/- warning: equiv.symm_to_local_equiv -> Equiv.symm_toLocalEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.{succ u1, succ u2} α β), Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u2, u1} β α) (Equiv.toLocalEquiv.{u2, u1} β α (Equiv.symm.{succ u1, succ u2} α β e)) (LocalEquiv.symm.{u1, u2} α β (Equiv.toLocalEquiv.{u1, u2} α β e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : Equiv.{succ u2, succ u1} α β), Eq.{max (succ u2) (succ u1)} (LocalEquiv.{u1, u2} β α) (Equiv.toLocalEquiv.{u1, u2} β α (Equiv.symm.{succ u2, succ u1} α β e)) (LocalEquiv.symm.{u2, u1} α β (Equiv.toLocalEquiv.{u2, u1} α β e))
Case conversion may be inaccurate. Consider using '#align equiv.symm_to_local_equiv Equiv.symm_toLocalEquivₓ'. -/
@[simp, mfld_simps]
theorem symm_toLocalEquiv : e.symm.toLocalEquiv = e.toLocalEquiv.symm :=
  rfl
#align equiv.symm_to_local_equiv Equiv.symm_toLocalEquiv

/- warning: equiv.trans_to_local_equiv -> Equiv.trans_toLocalEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (e : Equiv.{succ u1, succ u2} α β) (e' : Equiv.{succ u2, succ u3} β γ), Eq.{max (succ u1) (succ u3)} (LocalEquiv.{u1, u3} α γ) (Equiv.toLocalEquiv.{u1, u3} α γ (Equiv.trans.{succ u1, succ u2, succ u3} α β γ e e')) (LocalEquiv.trans.{u1, u2, u3} α β γ (Equiv.toLocalEquiv.{u1, u2} α β e) (Equiv.toLocalEquiv.{u2, u3} β γ e'))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (e : Equiv.{succ u3, succ u1} α β) (e' : Equiv.{succ u1, succ u2} β γ), Eq.{max (succ u3) (succ u2)} (LocalEquiv.{u3, u2} α γ) (Equiv.toLocalEquiv.{u3, u2} α γ (Equiv.trans.{succ u3, succ u1, succ u2} α β γ e e')) (LocalEquiv.trans.{u3, u1, u2} α β γ (Equiv.toLocalEquiv.{u3, u1} α β e) (Equiv.toLocalEquiv.{u1, u2} β γ e'))
Case conversion may be inaccurate. Consider using '#align equiv.trans_to_local_equiv Equiv.trans_toLocalEquivₓ'. -/
@[simp, mfld_simps]
theorem trans_toLocalEquiv : (e.trans e').toLocalEquiv = e.toLocalEquiv.trans e'.toLocalEquiv :=
  LocalEquiv.ext (fun x => rfl) (fun x => rfl)
    (by simp [LocalEquiv.trans_source, Equiv.toLocalEquiv])
#align equiv.trans_to_local_equiv Equiv.trans_toLocalEquiv

end Equiv

