/-
Copyright (c) 2022 Antoine Labelle, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle, Rémi Bottinelli

! This file was ported from Lean 3 source module combinatorics.quiver.cast
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.Quiver.Basic
import Mathbin.Combinatorics.Quiver.Path

/-!

# Rewriting arrows and paths along vertex equalities

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This files defines `hom.cast` and `path.cast` (and associated lemmas) in order to allow
rewriting arrows and paths along equalities of their endpoints.

-/


universe v v₁ v₂ u u₁ u₂

variable {U : Type _} [Quiver.{u + 1} U]

namespace Quiver

/-!
### Rewriting arrows along equalities of vertices
-/


#print Quiver.Hom.cast /-
/-- Change the endpoints of an arrow using equalities. -/
def Hom.cast {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) : u' ⟶ v' :=
  Eq.ndrec (Eq.ndrec e hv) hu
#align quiver.hom.cast Quiver.Hom.cast
-/

/- warning: quiver.hom.cast_eq_cast -> Quiver.Hom.cast_eq_cast is a dubious translation:
lean 3 declaration is
  forall {U : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} U] {u : U} {v : U} {u' : U} {v' : U} (hu : Eq.{succ u2} U u u') (hv : Eq.{succ u2} U v v') (e : Quiver.Hom.{succ u1, u2} U _inst_1 u v), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u' v') (Quiver.Hom.cast.{u1, u2} U _inst_1 u v u' v' hu hv e) (cast.{succ u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u v) (Quiver.Hom.{succ u1, u2} U _inst_1 u' v') (Eq.mpr.{0} (Eq.{succ (succ u1)} Type.{u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u v) (Quiver.Hom.{succ u1, u2} U _inst_1 u' v')) (Eq.{succ (succ u1)} Type.{u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u' v) (Quiver.Hom.{succ u1, u2} U _inst_1 u' v')) (id_tag Tactic.IdTag.rw (Eq.{1} Prop (Eq.{succ (succ u1)} Type.{u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u v) (Quiver.Hom.{succ u1, u2} U _inst_1 u' v')) (Eq.{succ (succ u1)} Type.{u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u' v) (Quiver.Hom.{succ u1, u2} U _inst_1 u' v'))) (Eq.ndrec.{0, succ u2} U u (fun (_a : U) => Eq.{1} Prop (Eq.{succ (succ u1)} Type.{u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u v) (Quiver.Hom.{succ u1, u2} U _inst_1 u' v')) (Eq.{succ (succ u1)} Type.{u1} (Quiver.Hom.{succ u1, u2} U _inst_1 _a v) (Quiver.Hom.{succ u1, u2} U _inst_1 u' v'))) (rfl.{1} Prop (Eq.{succ (succ u1)} Type.{u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u v) (Quiver.Hom.{succ u1, u2} U _inst_1 u' v'))) u' hu)) (Eq.mpr.{0} (Eq.{succ (succ u1)} Type.{u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u' v) (Quiver.Hom.{succ u1, u2} U _inst_1 u' v')) (Eq.{succ (succ u1)} Type.{u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u' v') (Quiver.Hom.{succ u1, u2} U _inst_1 u' v')) (id_tag Tactic.IdTag.rw (Eq.{1} Prop (Eq.{succ (succ u1)} Type.{u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u' v) (Quiver.Hom.{succ u1, u2} U _inst_1 u' v')) (Eq.{succ (succ u1)} Type.{u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u' v') (Quiver.Hom.{succ u1, u2} U _inst_1 u' v'))) (Eq.ndrec.{0, succ u2} U v (fun (_a : U) => Eq.{1} Prop (Eq.{succ (succ u1)} Type.{u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u' v) (Quiver.Hom.{succ u1, u2} U _inst_1 u' v')) (Eq.{succ (succ u1)} Type.{u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u' _a) (Quiver.Hom.{succ u1, u2} U _inst_1 u' v'))) (rfl.{1} Prop (Eq.{succ (succ u1)} Type.{u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u' v) (Quiver.Hom.{succ u1, u2} U _inst_1 u' v'))) v' hv)) (rfl.{succ (succ u1)} Type.{u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u' v')))) e)
but is expected to have type
  forall {U : Type.{u1}} [_inst_1 : Quiver.{succ u2, u1} U] {u : U} {v : U} {u' : U} {v' : U} (hu : Eq.{succ u1} U u u') (hv : Eq.{succ u1} U v v') (e : Quiver.Hom.{succ u2, u1} U _inst_1 u v), Eq.{succ u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u' v') (Quiver.Hom.cast.{u2, u1} U _inst_1 u v u' v' hu hv e) (cast.{succ u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u v) (Quiver.Hom.{succ u2, u1} U _inst_1 u' v') (Eq.mpr.{0} (Eq.{succ (succ u2)} Type.{u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u v) (Quiver.Hom.{succ u2, u1} U _inst_1 u' v')) (Eq.{succ (succ u2)} Type.{u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u' v) (Quiver.Hom.{succ u2, u1} U _inst_1 u' v')) (id.{0} (Eq.{1} Prop (Eq.{succ (succ u2)} Type.{u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u v) (Quiver.Hom.{succ u2, u1} U _inst_1 u' v')) (Eq.{succ (succ u2)} Type.{u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u' v) (Quiver.Hom.{succ u2, u1} U _inst_1 u' v'))) (Eq.ndrec.{0, succ u1} U u (fun (_a : U) => Eq.{1} Prop (Eq.{succ (succ u2)} Type.{u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u v) (Quiver.Hom.{succ u2, u1} U _inst_1 u' v')) (Eq.{succ (succ u2)} Type.{u2} (Quiver.Hom.{succ u2, u1} U _inst_1 _a v) (Quiver.Hom.{succ u2, u1} U _inst_1 u' v'))) (Eq.refl.{1} Prop (Eq.{succ (succ u2)} Type.{u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u v) (Quiver.Hom.{succ u2, u1} U _inst_1 u' v'))) u' hu)) (Eq.mpr.{0} (Eq.{succ (succ u2)} Type.{u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u' v) (Quiver.Hom.{succ u2, u1} U _inst_1 u' v')) (Eq.{succ (succ u2)} Type.{u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u' v') (Quiver.Hom.{succ u2, u1} U _inst_1 u' v')) (id.{0} (Eq.{1} Prop (Eq.{succ (succ u2)} Type.{u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u' v) (Quiver.Hom.{succ u2, u1} U _inst_1 u' v')) (Eq.{succ (succ u2)} Type.{u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u' v') (Quiver.Hom.{succ u2, u1} U _inst_1 u' v'))) (Eq.ndrec.{0, succ u1} U v (fun (_a : U) => Eq.{1} Prop (Eq.{succ (succ u2)} Type.{u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u' v) (Quiver.Hom.{succ u2, u1} U _inst_1 u' v')) (Eq.{succ (succ u2)} Type.{u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u' _a) (Quiver.Hom.{succ u2, u1} U _inst_1 u' v'))) (Eq.refl.{1} Prop (Eq.{succ (succ u2)} Type.{u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u' v) (Quiver.Hom.{succ u2, u1} U _inst_1 u' v'))) v' hv)) (Eq.refl.{succ (succ u2)} Type.{u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u' v')))) e)
Case conversion may be inaccurate. Consider using '#align quiver.hom.cast_eq_cast Quiver.Hom.cast_eq_castₓ'. -/
theorem Hom.cast_eq_cast {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) :
    e.cast hu hv = cast (by rw [hu, hv]) e :=
  by
  subst_vars
  rfl
#align quiver.hom.cast_eq_cast Quiver.Hom.cast_eq_cast

/- warning: quiver.hom.cast_rfl_rfl -> Quiver.Hom.cast_rfl_rfl is a dubious translation:
lean 3 declaration is
  forall {U : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} U] {u : U} {v : U} (e : Quiver.Hom.{succ u1, u2} U _inst_1 u v), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u v) (Quiver.Hom.cast.{u1, u2} U _inst_1 u v u v (rfl.{succ u2} U u) (rfl.{succ u2} U v) e) e
but is expected to have type
  forall {U : Type.{u1}} [_inst_1 : Quiver.{succ u2, u1} U] {u : U} {v : U} (e : Quiver.Hom.{succ u2, u1} U _inst_1 u v), Eq.{succ u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u v) (Quiver.Hom.cast.{u2, u1} U _inst_1 u v u v (rfl.{succ u1} U u) (rfl.{succ u1} U v) e) e
Case conversion may be inaccurate. Consider using '#align quiver.hom.cast_rfl_rfl Quiver.Hom.cast_rfl_rflₓ'. -/
@[simp]
theorem Hom.cast_rfl_rfl {u v : U} (e : u ⟶ v) : e.cast rfl rfl = e :=
  rfl
#align quiver.hom.cast_rfl_rfl Quiver.Hom.cast_rfl_rfl

/- warning: quiver.hom.cast_cast -> Quiver.Hom.cast_cast is a dubious translation:
lean 3 declaration is
  forall {U : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} U] {u : U} {v : U} {u' : U} {v' : U} {u'' : U} {v'' : U} (e : Quiver.Hom.{succ u1, u2} U _inst_1 u v) (hu : Eq.{succ u2} U u u') (hv : Eq.{succ u2} U v v') (hu' : Eq.{succ u2} U u' u'') (hv' : Eq.{succ u2} U v' v''), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u'' v'') (Quiver.Hom.cast.{u1, u2} U _inst_1 u' v' u'' v'' hu' hv' (Quiver.Hom.cast.{u1, u2} U _inst_1 u v u' v' hu hv e)) (Quiver.Hom.cast.{u1, u2} U _inst_1 u v u'' v'' (Eq.trans.{succ u2} U u u' u'' hu hu') (Eq.trans.{succ u2} U v v' v'' hv hv') e)
but is expected to have type
  forall {U : Type.{u1}} [_inst_1 : Quiver.{succ u2, u1} U] {u : U} {v : U} {u' : U} {v' : U} {u'' : U} {v'' : U} (e : Quiver.Hom.{succ u2, u1} U _inst_1 u v) (hu : Eq.{succ u1} U u u') (hv : Eq.{succ u1} U v v') (hu' : Eq.{succ u1} U u' u'') (hv' : Eq.{succ u1} U v' v''), Eq.{succ u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u'' v'') (Quiver.Hom.cast.{u2, u1} U _inst_1 u' v' u'' v'' hu' hv' (Quiver.Hom.cast.{u2, u1} U _inst_1 u v u' v' hu hv e)) (Quiver.Hom.cast.{u2, u1} U _inst_1 u v u'' v'' (Eq.trans.{succ u1} U u u' u'' hu hu') (Eq.trans.{succ u1} U v v' v'' hv hv') e)
Case conversion may be inaccurate. Consider using '#align quiver.hom.cast_cast Quiver.Hom.cast_castₓ'. -/
@[simp]
theorem Hom.cast_cast {u v u' v' u'' v'' : U} (e : u ⟶ v) (hu : u = u') (hv : v = v')
    (hu' : u' = u'') (hv' : v' = v'') :
    (e.cast hu hv).cast hu' hv' = e.cast (hu.trans hu') (hv.trans hv') :=
  by
  subst_vars
  rfl
#align quiver.hom.cast_cast Quiver.Hom.cast_cast

/- warning: quiver.hom.cast_heq -> Quiver.Hom.cast_heq is a dubious translation:
lean 3 declaration is
  forall {U : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} U] {u : U} {v : U} {u' : U} {v' : U} (hu : Eq.{succ u2} U u u') (hv : Eq.{succ u2} U v v') (e : Quiver.Hom.{succ u1, u2} U _inst_1 u v), HEq.{succ u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u' v') (Quiver.Hom.cast.{u1, u2} U _inst_1 u v u' v' hu hv e) (Quiver.Hom.{succ u1, u2} U _inst_1 u v) e
but is expected to have type
  forall {U : Type.{u1}} [_inst_1 : Quiver.{succ u2, u1} U] {u : U} {v : U} {u' : U} {v' : U} (hu : Eq.{succ u1} U u u') (hv : Eq.{succ u1} U v v') (e : Quiver.Hom.{succ u2, u1} U _inst_1 u v), HEq.{succ u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u' v') (Quiver.Hom.cast.{u2, u1} U _inst_1 u v u' v' hu hv e) (Quiver.Hom.{succ u2, u1} U _inst_1 u v) e
Case conversion may be inaccurate. Consider using '#align quiver.hom.cast_heq Quiver.Hom.cast_heqₓ'. -/
theorem Hom.cast_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) :
    HEq (e.cast hu hv) e := by
  subst_vars
  rfl
#align quiver.hom.cast_heq Quiver.Hom.cast_heq

/- warning: quiver.hom.cast_eq_iff_heq -> Quiver.Hom.cast_eq_iff_heq is a dubious translation:
lean 3 declaration is
  forall {U : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} U] {u : U} {v : U} {u' : U} {v' : U} (hu : Eq.{succ u2} U u u') (hv : Eq.{succ u2} U v v') (e : Quiver.Hom.{succ u1, u2} U _inst_1 u v) (e' : Quiver.Hom.{succ u1, u2} U _inst_1 u' v'), Iff (Eq.{succ u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u' v') (Quiver.Hom.cast.{u1, u2} U _inst_1 u v u' v' hu hv e) e') (HEq.{succ u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u v) e (Quiver.Hom.{succ u1, u2} U _inst_1 u' v') e')
but is expected to have type
  forall {U : Type.{u1}} [_inst_1 : Quiver.{succ u2, u1} U] {u : U} {v : U} {u' : U} {v' : U} (hu : Eq.{succ u1} U u u') (hv : Eq.{succ u1} U v v') (e : Quiver.Hom.{succ u2, u1} U _inst_1 u v) (e' : Quiver.Hom.{succ u2, u1} U _inst_1 u' v'), Iff (Eq.{succ u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u' v') (Quiver.Hom.cast.{u2, u1} U _inst_1 u v u' v' hu hv e) e') (HEq.{succ u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u v) e (Quiver.Hom.{succ u2, u1} U _inst_1 u' v') e')
Case conversion may be inaccurate. Consider using '#align quiver.hom.cast_eq_iff_heq Quiver.Hom.cast_eq_iff_heqₓ'. -/
theorem Hom.cast_eq_iff_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) (e' : u' ⟶ v') :
    e.cast hu hv = e' ↔ HEq e e' := by
  rw [Hom.cast_eq_cast]
  exact cast_eq_iff_heq
#align quiver.hom.cast_eq_iff_heq Quiver.Hom.cast_eq_iff_heq

/- warning: quiver.hom.eq_cast_iff_heq -> Quiver.Hom.eq_cast_iff_heq is a dubious translation:
lean 3 declaration is
  forall {U : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} U] {u : U} {v : U} {u' : U} {v' : U} (hu : Eq.{succ u2} U u u') (hv : Eq.{succ u2} U v v') (e : Quiver.Hom.{succ u1, u2} U _inst_1 u v) (e' : Quiver.Hom.{succ u1, u2} U _inst_1 u' v'), Iff (Eq.{succ u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u' v') e' (Quiver.Hom.cast.{u1, u2} U _inst_1 u v u' v' hu hv e)) (HEq.{succ u1} (Quiver.Hom.{succ u1, u2} U _inst_1 u' v') e' (Quiver.Hom.{succ u1, u2} U _inst_1 u v) e)
but is expected to have type
  forall {U : Type.{u1}} [_inst_1 : Quiver.{succ u2, u1} U] {u : U} {v : U} {u' : U} {v' : U} (hu : Eq.{succ u1} U u u') (hv : Eq.{succ u1} U v v') (e : Quiver.Hom.{succ u2, u1} U _inst_1 u v) (e' : Quiver.Hom.{succ u2, u1} U _inst_1 u' v'), Iff (Eq.{succ u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u' v') e' (Quiver.Hom.cast.{u2, u1} U _inst_1 u v u' v' hu hv e)) (HEq.{succ u2} (Quiver.Hom.{succ u2, u1} U _inst_1 u' v') e' (Quiver.Hom.{succ u2, u1} U _inst_1 u v) e)
Case conversion may be inaccurate. Consider using '#align quiver.hom.eq_cast_iff_heq Quiver.Hom.eq_cast_iff_heqₓ'. -/
theorem Hom.eq_cast_iff_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) (e' : u' ⟶ v') :
    e' = e.cast hu hv ↔ HEq e' e :=
  by
  rw [eq_comm, Hom.cast_eq_iff_heq]
  exact ⟨HEq.symm, HEq.symm⟩
#align quiver.hom.eq_cast_iff_heq Quiver.Hom.eq_cast_iff_heq

/-!
### Rewriting paths along equalities of vertices
-/


open Path

#print Quiver.Path.cast /-
/-- Change the endpoints of a path using equalities. -/
def Path.cast {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v) : Path u' v' :=
  Eq.ndrec (Eq.ndrec p hv) hu
#align quiver.path.cast Quiver.Path.cast
-/

/- warning: quiver.path.cast_eq_cast -> Quiver.Path.cast_eq_cast is a dubious translation:
lean 3 declaration is
  forall {U : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} U] {u : U} {v : U} {u' : U} {v' : U} (hu : Eq.{succ u2} U u u') (hv : Eq.{succ u2} U v v') (p : Quiver.Path.{succ u1, u2} U _inst_1 u v), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u' v') (Quiver.Path.cast.{u1, u2} U _inst_1 u v u' v' hu hv p) (cast.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u v) (Quiver.Path.{succ u1, u2} U _inst_1 u' v') (Eq.mpr.{0} (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u v) (Quiver.Path.{succ u1, u2} U _inst_1 u' v')) (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u' v) (Quiver.Path.{succ u1, u2} U _inst_1 u' v')) (id_tag Tactic.IdTag.rw (Eq.{1} Prop (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u v) (Quiver.Path.{succ u1, u2} U _inst_1 u' v')) (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u' v) (Quiver.Path.{succ u1, u2} U _inst_1 u' v'))) (Eq.ndrec.{0, succ u2} U u (fun (_a : U) => Eq.{1} Prop (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u v) (Quiver.Path.{succ u1, u2} U _inst_1 u' v')) (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 _a v) (Quiver.Path.{succ u1, u2} U _inst_1 u' v'))) (rfl.{1} Prop (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u v) (Quiver.Path.{succ u1, u2} U _inst_1 u' v'))) u' hu)) (Eq.mpr.{0} (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u' v) (Quiver.Path.{succ u1, u2} U _inst_1 u' v')) (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u' v') (Quiver.Path.{succ u1, u2} U _inst_1 u' v')) (id_tag Tactic.IdTag.rw (Eq.{1} Prop (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u' v) (Quiver.Path.{succ u1, u2} U _inst_1 u' v')) (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u' v') (Quiver.Path.{succ u1, u2} U _inst_1 u' v'))) (Eq.ndrec.{0, succ u2} U v (fun (_a : U) => Eq.{1} Prop (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u' v) (Quiver.Path.{succ u1, u2} U _inst_1 u' v')) (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u' _a) (Quiver.Path.{succ u1, u2} U _inst_1 u' v'))) (rfl.{1} Prop (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u' v) (Quiver.Path.{succ u1, u2} U _inst_1 u' v'))) v' hv)) (rfl.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u' v')))) p)
but is expected to have type
  forall {U : Type.{u1}} [_inst_1 : Quiver.{succ u2, u1} U] {u : U} {v : U} {u' : U} {v' : U} (hu : Eq.{succ u1} U u u') (hv : Eq.{succ u1} U v v') (p : Quiver.Path.{succ u2, u1} U _inst_1 u v), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u' v') (Quiver.Path.cast.{u2, u1} U _inst_1 u v u' v' hu hv p) (cast.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u v) (Quiver.Path.{succ u2, u1} U _inst_1 u' v') (Eq.mpr.{0} (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u v) (Quiver.Path.{succ u2, u1} U _inst_1 u' v')) (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u' v) (Quiver.Path.{succ u2, u1} U _inst_1 u' v')) (id.{0} (Eq.{1} Prop (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u v) (Quiver.Path.{succ u2, u1} U _inst_1 u' v')) (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u' v) (Quiver.Path.{succ u2, u1} U _inst_1 u' v'))) (Eq.ndrec.{0, succ u1} U u (fun (_a : U) => Eq.{1} Prop (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u v) (Quiver.Path.{succ u2, u1} U _inst_1 u' v')) (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 _a v) (Quiver.Path.{succ u2, u1} U _inst_1 u' v'))) (Eq.refl.{1} Prop (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u v) (Quiver.Path.{succ u2, u1} U _inst_1 u' v'))) u' hu)) (Eq.mpr.{0} (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u' v) (Quiver.Path.{succ u2, u1} U _inst_1 u' v')) (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u' v') (Quiver.Path.{succ u2, u1} U _inst_1 u' v')) (id.{0} (Eq.{1} Prop (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u' v) (Quiver.Path.{succ u2, u1} U _inst_1 u' v')) (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u' v') (Quiver.Path.{succ u2, u1} U _inst_1 u' v'))) (Eq.ndrec.{0, succ u1} U v (fun (_a : U) => Eq.{1} Prop (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u' v) (Quiver.Path.{succ u2, u1} U _inst_1 u' v')) (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u' _a) (Quiver.Path.{succ u2, u1} U _inst_1 u' v'))) (Eq.refl.{1} Prop (Eq.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u' v) (Quiver.Path.{succ u2, u1} U _inst_1 u' v'))) v' hv)) (Eq.refl.{succ (max (succ u2) (succ u1))} Sort.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u' v')))) p)
Case conversion may be inaccurate. Consider using '#align quiver.path.cast_eq_cast Quiver.Path.cast_eq_castₓ'. -/
theorem Path.cast_eq_cast {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v) :
    p.cast hu hv = cast (by rw [hu, hv]) p :=
  Eq.drec (Eq.drec (Eq.refl (Path.cast (Eq.refl u) (Eq.refl v) p)) hu) hv
#align quiver.path.cast_eq_cast Quiver.Path.cast_eq_cast

/- warning: quiver.path.cast_rfl_rfl -> Quiver.Path.cast_rfl_rfl is a dubious translation:
lean 3 declaration is
  forall {U : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} U] {u : U} {v : U} (p : Quiver.Path.{succ u1, u2} U _inst_1 u v), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u v) (Quiver.Path.cast.{u1, u2} U _inst_1 u v u v (rfl.{succ u2} U u) (rfl.{succ u2} U v) p) p
but is expected to have type
  forall {U : Type.{u1}} [_inst_1 : Quiver.{succ u2, u1} U] {u : U} {v : U} (p : Quiver.Path.{succ u2, u1} U _inst_1 u v), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u v) (Quiver.Path.cast.{u2, u1} U _inst_1 u v u v (rfl.{succ u1} U u) (rfl.{succ u1} U v) p) p
Case conversion may be inaccurate. Consider using '#align quiver.path.cast_rfl_rfl Quiver.Path.cast_rfl_rflₓ'. -/
@[simp]
theorem Path.cast_rfl_rfl {u v : U} (p : Path u v) : p.cast rfl rfl = p :=
  rfl
#align quiver.path.cast_rfl_rfl Quiver.Path.cast_rfl_rfl

/- warning: quiver.path.cast_cast -> Quiver.Path.cast_cast is a dubious translation:
lean 3 declaration is
  forall {U : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} U] {u : U} {v : U} {u' : U} {v' : U} {u'' : U} {v'' : U} (p : Quiver.Path.{succ u1, u2} U _inst_1 u v) (hu : Eq.{succ u2} U u u') (hv : Eq.{succ u2} U v v') (hu' : Eq.{succ u2} U u' u'') (hv' : Eq.{succ u2} U v' v''), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u'' v'') (Quiver.Path.cast.{u1, u2} U _inst_1 u' v' u'' v'' hu' hv' (Quiver.Path.cast.{u1, u2} U _inst_1 u v u' v' hu hv p)) (Quiver.Path.cast.{u1, u2} U _inst_1 u v u'' v'' (Eq.trans.{succ u2} U u u' u'' hu hu') (Eq.trans.{succ u2} U v v' v'' hv hv') p)
but is expected to have type
  forall {U : Type.{u1}} [_inst_1 : Quiver.{succ u2, u1} U] {u : U} {v : U} {u' : U} {v' : U} {u'' : U} {v'' : U} (p : Quiver.Path.{succ u2, u1} U _inst_1 u v) (hu : Eq.{succ u1} U u u') (hv : Eq.{succ u1} U v v') (hu' : Eq.{succ u1} U u' u'') (hv' : Eq.{succ u1} U v' v''), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u'' v'') (Quiver.Path.cast.{u2, u1} U _inst_1 u' v' u'' v'' hu' hv' (Quiver.Path.cast.{u2, u1} U _inst_1 u v u' v' hu hv p)) (Quiver.Path.cast.{u2, u1} U _inst_1 u v u'' v'' (Eq.trans.{succ u1} U u u' u'' hu hu') (Eq.trans.{succ u1} U v v' v'' hv hv') p)
Case conversion may be inaccurate. Consider using '#align quiver.path.cast_cast Quiver.Path.cast_castₓ'. -/
@[simp]
theorem Path.cast_cast {u v u' v' u'' v'' : U} (p : Path u v) (hu : u = u') (hv : v = v')
    (hu' : u' = u'') (hv' : v' = v'') :
    (p.cast hu hv).cast hu' hv' = p.cast (hu.trans hu') (hv.trans hv') :=
  by
  subst_vars
  rfl
#align quiver.path.cast_cast Quiver.Path.cast_cast

/- warning: quiver.path.cast_nil -> Quiver.Path.cast_nil is a dubious translation:
lean 3 declaration is
  forall {U : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} U] {u : U} {u' : U} (hu : Eq.{succ u2} U u u'), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u' u') (Quiver.Path.cast.{u1, u2} U _inst_1 u u u' u' hu hu (Quiver.Path.nil.{succ u1, u2} U _inst_1 u)) (Quiver.Path.nil.{succ u1, u2} U _inst_1 u')
but is expected to have type
  forall {U : Type.{u1}} [_inst_1 : Quiver.{succ u2, u1} U] {u : U} {u' : U} (hu : Eq.{succ u1} U u u'), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u' u') (Quiver.Path.cast.{u2, u1} U _inst_1 u u u' u' hu hu (Quiver.Path.nil.{succ u2, u1} U _inst_1 u)) (Quiver.Path.nil.{succ u2, u1} U _inst_1 u')
Case conversion may be inaccurate. Consider using '#align quiver.path.cast_nil Quiver.Path.cast_nilₓ'. -/
@[simp]
theorem Path.cast_nil {u u' : U} (hu : u = u') : (Path.nil : Path u u).cast hu hu = Path.nil :=
  by
  subst_vars
  rfl
#align quiver.path.cast_nil Quiver.Path.cast_nil

/- warning: quiver.path.cast_heq -> Quiver.Path.cast_heq is a dubious translation:
lean 3 declaration is
  forall {U : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} U] {u : U} {v : U} {u' : U} {v' : U} (hu : Eq.{succ u2} U u u') (hv : Eq.{succ u2} U v v') (p : Quiver.Path.{succ u1, u2} U _inst_1 u v), HEq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u' v') (Quiver.Path.cast.{u1, u2} U _inst_1 u v u' v' hu hv p) (Quiver.Path.{succ u1, u2} U _inst_1 u v) p
but is expected to have type
  forall {U : Type.{u1}} [_inst_1 : Quiver.{succ u2, u1} U] {u : U} {v : U} {u' : U} {v' : U} (hu : Eq.{succ u1} U u u') (hv : Eq.{succ u1} U v v') (p : Quiver.Path.{succ u2, u1} U _inst_1 u v), HEq.{max (succ u1) (succ u2)} (Quiver.Path.{succ u2, u1} U _inst_1 u' v') (Quiver.Path.cast.{u2, u1} U _inst_1 u v u' v' hu hv p) (Quiver.Path.{succ u2, u1} U _inst_1 u v) p
Case conversion may be inaccurate. Consider using '#align quiver.path.cast_heq Quiver.Path.cast_heqₓ'. -/
theorem Path.cast_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v) :
    HEq (p.cast hu hv) p := by
  rw [Path.cast_eq_cast]
  exact cast_hEq _ _
#align quiver.path.cast_heq Quiver.Path.cast_heq

/- warning: quiver.path.cast_eq_iff_heq -> Quiver.Path.cast_eq_iff_heq is a dubious translation:
lean 3 declaration is
  forall {U : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} U] {u : U} {v : U} {u' : U} {v' : U} (hu : Eq.{succ u2} U u u') (hv : Eq.{succ u2} U v v') (p : Quiver.Path.{succ u1, u2} U _inst_1 u v) (p' : Quiver.Path.{succ u1, u2} U _inst_1 u' v'), Iff (Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u' v') (Quiver.Path.cast.{u1, u2} U _inst_1 u v u' v' hu hv p) p') (HEq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u v) p (Quiver.Path.{succ u1, u2} U _inst_1 u' v') p')
but is expected to have type
  forall {U : Type.{u1}} [_inst_1 : Quiver.{succ u2, u1} U] {u : U} {v : U} {u' : U} {v' : U} (hu : Eq.{succ u1} U u u') (hv : Eq.{succ u1} U v v') (p : Quiver.Path.{succ u2, u1} U _inst_1 u v) (p' : Quiver.Path.{succ u2, u1} U _inst_1 u' v'), Iff (Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u' v') (Quiver.Path.cast.{u2, u1} U _inst_1 u v u' v' hu hv p) p') (HEq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u v) p (Quiver.Path.{succ u2, u1} U _inst_1 u' v') p')
Case conversion may be inaccurate. Consider using '#align quiver.path.cast_eq_iff_heq Quiver.Path.cast_eq_iff_heqₓ'. -/
theorem Path.cast_eq_iff_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v)
    (p' : Path u' v') : p.cast hu hv = p' ↔ HEq p p' :=
  by
  rw [Path.cast_eq_cast]
  exact cast_eq_iff_heq
#align quiver.path.cast_eq_iff_heq Quiver.Path.cast_eq_iff_heq

/- warning: quiver.path.eq_cast_iff_heq -> Quiver.Path.eq_cast_iff_heq is a dubious translation:
lean 3 declaration is
  forall {U : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} U] {u : U} {v : U} {u' : U} {v' : U} (hu : Eq.{succ u2} U u u') (hv : Eq.{succ u2} U v v') (p : Quiver.Path.{succ u1, u2} U _inst_1 u v) (p' : Quiver.Path.{succ u1, u2} U _inst_1 u' v'), Iff (Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u' v') p' (Quiver.Path.cast.{u1, u2} U _inst_1 u v u' v' hu hv p)) (HEq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u' v') p' (Quiver.Path.{succ u1, u2} U _inst_1 u v) p)
but is expected to have type
  forall {U : Type.{u1}} [_inst_1 : Quiver.{succ u2, u1} U] {u : U} {v : U} {u' : U} {v' : U} (hu : Eq.{succ u1} U u u') (hv : Eq.{succ u1} U v v') (p : Quiver.Path.{succ u2, u1} U _inst_1 u v) (p' : Quiver.Path.{succ u2, u1} U _inst_1 u' v'), Iff (Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u' v') p' (Quiver.Path.cast.{u2, u1} U _inst_1 u v u' v' hu hv p)) (HEq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u' v') p' (Quiver.Path.{succ u2, u1} U _inst_1 u v) p)
Case conversion may be inaccurate. Consider using '#align quiver.path.eq_cast_iff_heq Quiver.Path.eq_cast_iff_heqₓ'. -/
theorem Path.eq_cast_iff_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v)
    (p' : Path u' v') : p' = p.cast hu hv ↔ HEq p' p :=
  ⟨fun h => ((p.cast_eq_iff_heq hu hv p').1 h.symm).symm, fun h =>
    ((p.cast_eq_iff_heq hu hv p').2 h.symm).symm⟩
#align quiver.path.eq_cast_iff_heq Quiver.Path.eq_cast_iff_heq

/- warning: quiver.path.cast_cons -> Quiver.Path.cast_cons is a dubious translation:
lean 3 declaration is
  forall {U : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} U] {u : U} {v : U} {w : U} {u' : U} {w' : U} (p : Quiver.Path.{succ u1, u2} U _inst_1 u v) (e : Quiver.Hom.{succ u1, u2} U _inst_1 v w) (hu : Eq.{succ u2} U u u') (hw : Eq.{succ u2} U w w'), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u' w') (Quiver.Path.cast.{u1, u2} U _inst_1 u w u' w' hu hw (Quiver.Path.cons.{succ u1, u2} U _inst_1 u v w p e)) (Quiver.Path.cons.{succ u1, u2} U _inst_1 u' v w' (Quiver.Path.cast.{u1, u2} U _inst_1 u v u' v hu (rfl.{succ u2} U v) p) (Quiver.Hom.cast.{u1, u2} U _inst_1 v w v w' (rfl.{succ u2} U v) hw e))
but is expected to have type
  forall {U : Type.{u1}} [_inst_1 : Quiver.{succ u2, u1} U] {u : U} {v : U} {w : U} {u' : U} {w' : U} (p : Quiver.Path.{succ u2, u1} U _inst_1 u v) (e : Quiver.Hom.{succ u2, u1} U _inst_1 v w) (hu : Eq.{succ u1} U u u') (hw : Eq.{succ u1} U w w'), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u' w') (Quiver.Path.cast.{u2, u1} U _inst_1 u w u' w' hu hw (Quiver.Path.cons.{succ u2, u1} U _inst_1 u v w p e)) (Quiver.Path.cons.{succ u2, u1} U _inst_1 u' v w' (Quiver.Path.cast.{u2, u1} U _inst_1 u v u' v hu (rfl.{succ u1} U v) p) (Quiver.Hom.cast.{u2, u1} U _inst_1 v w v w' (rfl.{succ u1} U v) hw e))
Case conversion may be inaccurate. Consider using '#align quiver.path.cast_cons Quiver.Path.cast_consₓ'. -/
theorem Path.cast_cons {u v w u' w' : U} (p : Path u v) (e : v ⟶ w) (hu : u = u') (hw : w = w') :
    (p.cons e).cast hu hw = (p.cast hu rfl).cons (e.cast rfl hw) :=
  by
  subst_vars
  rfl
#align quiver.path.cast_cons Quiver.Path.cast_cons

/- warning: quiver.cast_eq_of_cons_eq_cons -> Quiver.cast_eq_of_cons_eq_cons is a dubious translation:
lean 3 declaration is
  forall {U : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} U] {u : U} {v : U} {v' : U} {w : U} {p : Quiver.Path.{succ u1, u2} U _inst_1 u v} {p' : Quiver.Path.{succ u1, u2} U _inst_1 u v'} {e : Quiver.Hom.{succ u1, u2} U _inst_1 v w} {e' : Quiver.Hom.{succ u1, u2} U _inst_1 v' w} (h : Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u w) (Quiver.Path.cons.{succ u1, u2} U _inst_1 u v w p e) (Quiver.Path.cons.{succ u1, u2} U _inst_1 u v' w p' e')), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u v') (Quiver.Path.cast.{u1, u2} U _inst_1 u v u v' (rfl.{succ u2} U u) (Quiver.Path.obj_eq_of_cons_eq_cons.{u2, succ u1} U _inst_1 u v v' w p p' e e' h) p) p'
but is expected to have type
  forall {U : Type.{u1}} [_inst_1 : Quiver.{succ u2, u1} U] {u : U} {v : U} {v' : U} {w : U} {p : Quiver.Path.{succ u2, u1} U _inst_1 u v} {p' : Quiver.Path.{succ u2, u1} U _inst_1 u v'} {e : Quiver.Hom.{succ u2, u1} U _inst_1 v w} {e' : Quiver.Hom.{succ u2, u1} U _inst_1 v' w} (h : Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u w) (Quiver.Path.cons.{succ u2, u1} U _inst_1 u v w p e) (Quiver.Path.cons.{succ u2, u1} U _inst_1 u v' w p' e')), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u v') (Quiver.Path.cast.{u2, u1} U _inst_1 u v u v' (rfl.{succ u1} U u) (Quiver.Path.obj_eq_of_cons_eq_cons.{succ u2, u1} U _inst_1 u v v' w p p' e e' h) p) p'
Case conversion may be inaccurate. Consider using '#align quiver.cast_eq_of_cons_eq_cons Quiver.cast_eq_of_cons_eq_consₓ'. -/
theorem cast_eq_of_cons_eq_cons {u v v' w : U} {p : Path u v} {p' : Path u v'} {e : v ⟶ w}
    {e' : v' ⟶ w} (h : p.cons e = p'.cons e') : p.cast rfl (obj_eq_of_cons_eq_cons h) = p' :=
  by
  rw [Path.cast_eq_iff_heq]
  exact heq_of_cons_eq_cons h
#align quiver.cast_eq_of_cons_eq_cons Quiver.cast_eq_of_cons_eq_cons

/- warning: quiver.hom_cast_eq_of_cons_eq_cons -> Quiver.hom_cast_eq_of_cons_eq_cons is a dubious translation:
lean 3 declaration is
  forall {U : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} U] {u : U} {v : U} {v' : U} {w : U} {p : Quiver.Path.{succ u1, u2} U _inst_1 u v} {p' : Quiver.Path.{succ u1, u2} U _inst_1 u v'} {e : Quiver.Hom.{succ u1, u2} U _inst_1 v w} {e' : Quiver.Hom.{succ u1, u2} U _inst_1 v' w} (h : Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 u w) (Quiver.Path.cons.{succ u1, u2} U _inst_1 u v w p e) (Quiver.Path.cons.{succ u1, u2} U _inst_1 u v' w p' e')), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} U _inst_1 v' w) (Quiver.Hom.cast.{u1, u2} U _inst_1 v w v' w (Quiver.Path.obj_eq_of_cons_eq_cons.{u2, succ u1} U _inst_1 u v v' w p p' e e' h) (rfl.{succ u2} U w) e) e'
but is expected to have type
  forall {U : Type.{u1}} [_inst_1 : Quiver.{succ u2, u1} U] {u : U} {v : U} {v' : U} {w : U} {p : Quiver.Path.{succ u2, u1} U _inst_1 u v} {p' : Quiver.Path.{succ u2, u1} U _inst_1 u v'} {e : Quiver.Hom.{succ u2, u1} U _inst_1 v w} {e' : Quiver.Hom.{succ u2, u1} U _inst_1 v' w} (h : Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 u w) (Quiver.Path.cons.{succ u2, u1} U _inst_1 u v w p e) (Quiver.Path.cons.{succ u2, u1} U _inst_1 u v' w p' e')), Eq.{succ u2} (Quiver.Hom.{succ u2, u1} U _inst_1 v' w) (Quiver.Hom.cast.{u2, u1} U _inst_1 v w v' w (Quiver.Path.obj_eq_of_cons_eq_cons.{succ u2, u1} U _inst_1 u v v' w p p' e e' h) (rfl.{succ u1} U w) e) e'
Case conversion may be inaccurate. Consider using '#align quiver.hom_cast_eq_of_cons_eq_cons Quiver.hom_cast_eq_of_cons_eq_consₓ'. -/
theorem hom_cast_eq_of_cons_eq_cons {u v v' w : U} {p : Path u v} {p' : Path u v'} {e : v ⟶ w}
    {e' : v' ⟶ w} (h : p.cons e = p'.cons e') : e.cast (obj_eq_of_cons_eq_cons h) rfl = e' :=
  by
  rw [Hom.cast_eq_iff_heq]
  exact hom_heq_of_cons_eq_cons h
#align quiver.hom_cast_eq_of_cons_eq_cons Quiver.hom_cast_eq_of_cons_eq_cons

/- warning: quiver.eq_nil_of_length_zero -> Quiver.eq_nil_of_length_zero is a dubious translation:
lean 3 declaration is
  forall {U : Type.{u2}} [_inst_1 : Quiver.{succ u1, u2} U] {u : U} {v : U} (p : Quiver.Path.{succ u1, u2} U _inst_1 u v) (hzero : Eq.{1} Nat (Quiver.Path.length.{u2, succ u1} U _inst_1 u v p) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u1, u2} U _inst_1 v v) (Quiver.Path.cast.{u1, u2} U _inst_1 u v v v (Quiver.Path.eq_of_length_zero.{u2, succ u1} U _inst_1 u v p hzero) (rfl.{succ u2} U v) p) (Quiver.Path.nil.{succ u1, u2} U _inst_1 v)
but is expected to have type
  forall {U : Type.{u1}} [_inst_1 : Quiver.{succ u2, u1} U] {u : U} {v : U} (p : Quiver.Path.{succ u2, u1} U _inst_1 u v) (hzero : Eq.{1} Nat (Quiver.Path.length.{u1, succ u2} U _inst_1 u v p) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))), Eq.{max (succ u2) (succ u1)} (Quiver.Path.{succ u2, u1} U _inst_1 v v) (Quiver.Path.cast.{u2, u1} U _inst_1 u v v v (Quiver.Path.eq_of_length_zero.{succ u2, u1} U _inst_1 u v p hzero) (rfl.{succ u1} U v) p) (Quiver.Path.nil.{succ u2, u1} U _inst_1 v)
Case conversion may be inaccurate. Consider using '#align quiver.eq_nil_of_length_zero Quiver.eq_nil_of_length_zeroₓ'. -/
theorem eq_nil_of_length_zero {u v : U} (p : Path u v) (hzero : p.length = 0) :
    p.cast (eq_of_length_zero p hzero) rfl = Path.nil := by
  cases p <;> simpa only [Nat.succ_ne_zero, length_cons] using hzero
#align quiver.eq_nil_of_length_zero Quiver.eq_nil_of_length_zero

end Quiver

