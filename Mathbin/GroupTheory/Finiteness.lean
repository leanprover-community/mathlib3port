/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

! This file was ported from Lean 3 source module group_theory.finiteness
! leanprover-community/mathlib commit 34ee86e6a59d911a8e4f89b68793ee7577ae79c7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Pointwise.Finite
import Mathbin.GroupTheory.QuotientGroup
import Mathbin.GroupTheory.Submonoid.Operations
import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.SetTheory.Cardinal.Finite
import Mathbin.Data.Finset.Preimage

/-!
# Finitely generated monoids and groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define finitely generated monoids and groups. See also `submodule.fg` and `module.finite` for
finitely-generated modules.

## Main definition

* `submonoid.fg S`, `add_submonoid.fg S` : A submonoid `S` is finitely generated.
* `monoid.fg M`, `add_monoid.fg M` : A typeclass indicating a type `M` is finitely generated as a
monoid.
* `subgroup.fg S`, `add_subgroup.fg S` : A subgroup `S` is finitely generated.
* `group.fg M`, `add_group.fg M` : A typeclass indicating a type `M` is finitely generated as a
group.

-/


/-! ### Monoids and submonoids -/


open Pointwise

variable {M N : Type _} [Monoid M] [AddMonoid N]

section Submonoid

#print Submonoid.FG /-
/-- A submonoid of `M` is finitely generated if it is the closure of a finite subset of `M`. -/
@[to_additive]
def Submonoid.FG (P : Submonoid M) : Prop :=
  ∃ S : Finset M, Submonoid.closure ↑S = P
#align submonoid.fg Submonoid.FG
#align add_submonoid.fg AddSubmonoid.FG
-/

/-- An additive submonoid of `N` is finitely generated if it is the closure of a finite subset of
`M`. -/
add_decl_doc AddSubmonoid.FG

#print Submonoid.fg_iff /-
/-- An equivalent expression of `submonoid.fg` in terms of `set.finite` instead of `finset`. -/
@[to_additive
      "An equivalent expression of `add_submonoid.fg` in terms of `set.finite` instead of\n`finset`."]
theorem Submonoid.fg_iff (P : Submonoid M) :
    Submonoid.FG P ↔ ∃ S : Set M, Submonoid.closure S = P ∧ S.Finite :=
  ⟨fun ⟨S, hS⟩ => ⟨S, hS, Finset.finite_toSet S⟩, fun ⟨S, hS, hf⟩ =>
    ⟨Set.Finite.toFinset hf, by simp [hS]⟩⟩
#align submonoid.fg_iff Submonoid.fg_iff
#align add_submonoid.fg_iff AddSubmonoid.fg_iff
-/

/- warning: submonoid.fg_iff_add_fg -> Submonoid.fg_iff_add_fg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submonoid.fg_iff_add_fg Submonoid.fg_iff_add_fgₓ'. -/
theorem Submonoid.fg_iff_add_fg (P : Submonoid M) : P.FG ↔ P.toAddSubmonoid.FG :=
  ⟨fun h =>
    let ⟨S, hS, hf⟩ := (Submonoid.fg_iff _).1 h
    (AddSubmonoid.fg_iff _).mpr
      ⟨Additive.toMul ⁻¹' S, by simp [← Submonoid.toAddSubmonoid_closure, hS], hf⟩,
    fun h =>
    let ⟨T, hT, hf⟩ := (AddSubmonoid.fg_iff _).1 h
    (Submonoid.fg_iff _).mpr
      ⟨Multiplicative.ofAdd ⁻¹' T, by simp [← AddSubmonoid.toSubmonoid'_closure, hT], hf⟩⟩
#align submonoid.fg_iff_add_fg Submonoid.fg_iff_add_fg

/- warning: add_submonoid.fg_iff_mul_fg -> AddSubmonoid.fg_iff_mul_fg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align add_submonoid.fg_iff_mul_fg AddSubmonoid.fg_iff_mul_fgₓ'. -/
theorem AddSubmonoid.fg_iff_mul_fg (P : AddSubmonoid N) : P.FG ↔ P.toSubmonoid.FG :=
  by
  convert(Submonoid.fg_iff_add_fg P.to_submonoid).symm
  exact SetLike.ext' rfl
#align add_submonoid.fg_iff_mul_fg AddSubmonoid.fg_iff_mul_fg

end Submonoid

section Monoid

variable (M N)

#print Monoid.FG /-
/-- A monoid is finitely generated if it is finitely generated as a submonoid of itself. -/
class Monoid.FG : Prop where
  out : (⊤ : Submonoid M).FG
#align monoid.fg Monoid.FG
-/

#print AddMonoid.FG /-
/-- An additive monoid is finitely generated if it is finitely generated as an additive submonoid of
itself. -/
class AddMonoid.FG : Prop where
  out : (⊤ : AddSubmonoid N).FG
#align add_monoid.fg AddMonoid.FG
-/

attribute [to_additive] Monoid.FG

variable {M N}

/- warning: monoid.fg_def -> Monoid.fg_def is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M], Iff (Monoid.FG.{u1} M _inst_1) (Submonoid.FG.{u1} M _inst_1 (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.hasTop.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M], Iff (Monoid.FG.{u1} M _inst_1) (Submonoid.FG.{u1} M _inst_1 (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.instTopSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align monoid.fg_def Monoid.fg_defₓ'. -/
theorem Monoid.fg_def : Monoid.FG M ↔ (⊤ : Submonoid M).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align monoid.fg_def Monoid.fg_def

/- warning: add_monoid.fg_def -> AddMonoid.fg_def is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u1}} [_inst_2 : AddMonoid.{u1} N], Iff (AddMonoid.FG.{u1} N _inst_2) (AddSubmonoid.FG.{u1} N _inst_2 (Top.top.{u1} (AddSubmonoid.{u1} N (AddMonoid.toAddZeroClass.{u1} N _inst_2)) (AddSubmonoid.hasTop.{u1} N (AddMonoid.toAddZeroClass.{u1} N _inst_2))))
but is expected to have type
  forall {N : Type.{u1}} [_inst_2 : AddMonoid.{u1} N], Iff (AddMonoid.FG.{u1} N _inst_2) (AddSubmonoid.FG.{u1} N _inst_2 (Top.top.{u1} (AddSubmonoid.{u1} N (AddMonoid.toAddZeroClass.{u1} N _inst_2)) (AddSubmonoid.instTopAddSubmonoid.{u1} N (AddMonoid.toAddZeroClass.{u1} N _inst_2))))
Case conversion may be inaccurate. Consider using '#align add_monoid.fg_def AddMonoid.fg_defₓ'. -/
theorem AddMonoid.fg_def : AddMonoid.FG N ↔ (⊤ : AddSubmonoid N).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align add_monoid.fg_def AddMonoid.fg_def

/- warning: monoid.fg_iff -> Monoid.fg_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M], Iff (Monoid.FG.{u1} M _inst_1) (Exists.{succ u1} (Set.{u1} M) (fun (S : Set.{u1} M) => And (Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) S) (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.hasTop.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) (Set.Finite.{u1} M S)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M], Iff (Monoid.FG.{u1} M _inst_1) (Exists.{succ u1} (Set.{u1} M) (fun (S : Set.{u1} M) => And (Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) S) (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.instTopSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) (Set.Finite.{u1} M S)))
Case conversion may be inaccurate. Consider using '#align monoid.fg_iff Monoid.fg_iffₓ'. -/
/-- An equivalent expression of `monoid.fg` in terms of `set.finite` instead of `finset`. -/
@[to_additive
      "An equivalent expression of `add_monoid.fg` in terms of `set.finite` instead of\n`finset`."]
theorem Monoid.fg_iff :
    Monoid.FG M ↔ ∃ S : Set M, Submonoid.closure S = (⊤ : Submonoid M) ∧ S.Finite :=
  ⟨fun h => (Submonoid.fg_iff ⊤).1 h.out, fun h => ⟨(Submonoid.fg_iff ⊤).2 h⟩⟩
#align monoid.fg_iff Monoid.fg_iff
#align add_monoid.fg_iff AddMonoid.fg_iff

#print Monoid.fg_iff_add_fg /-
theorem Monoid.fg_iff_add_fg : Monoid.FG M ↔ AddMonoid.FG (Additive M) :=
  ⟨fun h => ⟨(Submonoid.fg_iff_add_fg ⊤).1 h.out⟩, fun h => ⟨(Submonoid.fg_iff_add_fg ⊤).2 h.out⟩⟩
#align monoid.fg_iff_add_fg Monoid.fg_iff_add_fg
-/

#print AddMonoid.fg_iff_mul_fg /-
theorem AddMonoid.fg_iff_mul_fg : AddMonoid.FG N ↔ Monoid.FG (Multiplicative N) :=
  ⟨fun h => ⟨(AddSubmonoid.fg_iff_mul_fg ⊤).1 h.out⟩, fun h =>
    ⟨(AddSubmonoid.fg_iff_mul_fg ⊤).2 h.out⟩⟩
#align add_monoid.fg_iff_mul_fg AddMonoid.fg_iff_mul_fg
-/

#print AddMonoid.fg_of_monoid_fg /-
instance AddMonoid.fg_of_monoid_fg [Monoid.FG M] : AddMonoid.FG (Additive M) :=
  Monoid.fg_iff_add_fg.1 ‹_›
#align add_monoid.fg_of_monoid_fg AddMonoid.fg_of_monoid_fg
-/

#print Monoid.fg_of_addMonoid_fg /-
instance Monoid.fg_of_addMonoid_fg [AddMonoid.FG N] : Monoid.FG (Multiplicative N) :=
  AddMonoid.fg_iff_mul_fg.1 ‹_›
#align monoid.fg_of_add_monoid_fg Monoid.fg_of_addMonoid_fg
-/

#print Monoid.fg_of_finite /-
@[to_additive]
instance (priority := 100) Monoid.fg_of_finite [Finite M] : Monoid.FG M :=
  by
  cases nonempty_fintype M
  exact ⟨⟨Finset.univ, by rw [Finset.coe_univ] <;> exact Submonoid.closure_univ⟩⟩
#align monoid.fg_of_finite Monoid.fg_of_finite
#align add_monoid.fg_of_finite AddMonoid.fg_of_finite
-/

end Monoid

#print Submonoid.FG.map /-
@[to_additive]
theorem Submonoid.FG.map {M' : Type _} [Monoid M'] {P : Submonoid M} (h : P.FG) (e : M →* M') :
    (P.map e).FG := by
  classical
    obtain ⟨s, rfl⟩ := h
    exact ⟨s.image e, by rw [Finset.coe_image, MonoidHom.map_mclosure]⟩
#align submonoid.fg.map Submonoid.FG.map
#align add_submonoid.fg.map AddSubmonoid.FG.map
-/

/- warning: submonoid.fg.map_injective -> Submonoid.FG.map_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {M' : Type.{u2}} [_inst_3 : Monoid.{u2} M'] {P : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)} (e : MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)), (Function.Injective.{succ u1, succ u2} M M' (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) (fun (_x : MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) => M -> M') (MonoidHom.hasCoeToFun.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) e)) -> (Submonoid.FG.{u2} M' _inst_3 (Submonoid.map.{u1, u2, max u2 u1} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3) (MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) (MonoidHom.monoidHomClass.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) e P)) -> (Submonoid.FG.{u1} M _inst_1 P)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {M' : Type.{u2}} [_inst_3 : Monoid.{u2} M'] {P : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)} (e : MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)), (Function.Injective.{succ u1, succ u2} M M' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : M) => M') _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) M M' (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toMul.{u2} M' (Monoid.toMulOneClass.{u2} M' _inst_3)) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3) (MonoidHom.monoidHomClass.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)))) e)) -> (Submonoid.FG.{u2} M' _inst_3 (Submonoid.map.{u1, u2, max u1 u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3) (MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) (MonoidHom.monoidHomClass.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) e P)) -> (Submonoid.FG.{u1} M _inst_1 P)
Case conversion may be inaccurate. Consider using '#align submonoid.fg.map_injective Submonoid.FG.map_injectiveₓ'. -/
@[to_additive]
theorem Submonoid.FG.map_injective {M' : Type _} [Monoid M'] {P : Submonoid M} (e : M →* M')
    (he : Function.Injective e) (h : (P.map e).FG) : P.FG :=
  by
  obtain ⟨s, hs⟩ := h
  use s.preimage e (he.inj_on _)
  apply Submonoid.map_injective_of_injective he
  rw [← hs, e.map_mclosure, Finset.coe_preimage]
  congr
  rw [Set.image_preimage_eq_iff, ← e.coe_mrange, ← Submonoid.closure_le, hs, e.mrange_eq_map]
  exact Submonoid.monotone_map le_top
#align submonoid.fg.map_injective Submonoid.FG.map_injective
#align add_submonoid.fg.map_injective AddSubmonoid.FG.map_injective

/- warning: monoid.fg_iff_submonoid_fg -> Monoid.fg_iff_submonoid_fg is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (N : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)), Iff (Monoid.FG.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) N) (Submonoid.toMonoid.{u1} M _inst_1 N)) (Submonoid.FG.{u1} M _inst_1 N)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (N : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)), Iff (Monoid.FG.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x N)) (Submonoid.toMonoid.{u1} M _inst_1 N)) (Submonoid.FG.{u1} M _inst_1 N)
Case conversion may be inaccurate. Consider using '#align monoid.fg_iff_submonoid_fg Monoid.fg_iff_submonoid_fgₓ'. -/
@[simp, to_additive]
theorem Monoid.fg_iff_submonoid_fg (N : Submonoid M) : Monoid.FG N ↔ N.FG :=
  by
  conv_rhs => rw [← N.range_subtype, MonoidHom.mrange_eq_map]
  exact ⟨fun h => h.out.map N.subtype, fun h => ⟨h.map_injective N.subtype Subtype.coe_injective⟩⟩
#align monoid.fg_iff_submonoid_fg Monoid.fg_iff_submonoid_fg
#align add_monoid.fg_iff_add_submonoid_fg AddMonoid.fg_iff_addSubmonoid_fg

/- warning: monoid.fg_of_surjective -> Monoid.fg_of_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {M' : Type.{u2}} [_inst_3 : Monoid.{u2} M'] [_inst_4 : Monoid.FG.{u1} M _inst_1] (f : MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)), (Function.Surjective.{succ u1, succ u2} M M' (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) (fun (_x : MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) => M -> M') (MonoidHom.hasCoeToFun.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) f)) -> (Monoid.FG.{u2} M' _inst_3)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {M' : Type.{u2}} [_inst_3 : Monoid.{u2} M'] [_inst_4 : Monoid.FG.{u1} M _inst_1] (f : MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)), (Function.Surjective.{succ u1, succ u2} M M' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : M) => M') _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) M M' (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toMul.{u2} M' (Monoid.toMulOneClass.{u2} M' _inst_3)) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3) (MonoidHom.monoidHomClass.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)))) f)) -> (Monoid.FG.{u2} M' _inst_3)
Case conversion may be inaccurate. Consider using '#align monoid.fg_of_surjective Monoid.fg_of_surjectiveₓ'. -/
@[to_additive]
theorem Monoid.fg_of_surjective {M' : Type _} [Monoid M'] [Monoid.FG M] (f : M →* M')
    (hf : Function.Surjective f) : Monoid.FG M' := by
  classical
    obtain ⟨s, hs⟩ := monoid.fg_def.mp ‹_›
    use s.image f
    rwa [Finset.coe_image, ← MonoidHom.map_mclosure, hs, ← MonoidHom.mrange_eq_map,
      MonoidHom.mrange_top_iff_surjective]
#align monoid.fg_of_surjective Monoid.fg_of_surjective
#align add_monoid.fg_of_surjective AddMonoid.fg_of_surjective

/- warning: monoid.fg_range -> Monoid.fg_range is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {M' : Type.{u2}} [_inst_3 : Monoid.{u2} M'] [_inst_4 : Monoid.FG.{u1} M _inst_1] (f : MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)), Monoid.FG.{u2} (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} M' (Monoid.toMulOneClass.{u2} M' _inst_3)) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} M' (Monoid.toMulOneClass.{u2} M' _inst_3)) M' (Submonoid.setLike.{u2} M' (Monoid.toMulOneClass.{u2} M' _inst_3))) (MonoidHom.mrange.{u1, u2, max u2 u1} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3) (MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) (MonoidHom.monoidHomClass.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) f)) (Submonoid.toMonoid.{u2} M' _inst_3 (MonoidHom.mrange.{u1, u2, max u2 u1} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3) (MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) (MonoidHom.monoidHomClass.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) f))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {M' : Type.{u2}} [_inst_3 : Monoid.{u2} M'] [_inst_4 : Monoid.FG.{u1} M _inst_1] (f : MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)), Monoid.FG.{u2} (Subtype.{succ u2} M' (fun (x : M') => Membership.mem.{u2, u2} M' (Submonoid.{u2} M' (Monoid.toMulOneClass.{u2} M' _inst_3)) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M' (Monoid.toMulOneClass.{u2} M' _inst_3)) M' (Submonoid.instSetLikeSubmonoid.{u2} M' (Monoid.toMulOneClass.{u2} M' _inst_3))) x (MonoidHom.mrange.{u1, u2, max u1 u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3) (MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) (MonoidHom.monoidHomClass.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) f))) (Submonoid.toMonoid.{u2} M' _inst_3 (MonoidHom.mrange.{u1, u2, max u1 u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3) (MonoidHom.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) (MonoidHom.monoidHomClass.{u1, u2} M M' (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} M' _inst_3)) f))
Case conversion may be inaccurate. Consider using '#align monoid.fg_range Monoid.fg_rangeₓ'. -/
@[to_additive]
instance Monoid.fg_range {M' : Type _} [Monoid M'] [Monoid.FG M] (f : M →* M') :
    Monoid.FG f.mrange :=
  Monoid.fg_of_surjective f.mrangeRestrict f.mrangeRestrict_surjective
#align monoid.fg_range Monoid.fg_range
#align add_monoid.fg_range AddMonoid.fg_range

#print Submonoid.powers_fg /-
@[to_additive AddSubmonoid.multiples_fg]
theorem Submonoid.powers_fg (r : M) : (Submonoid.powers r).FG :=
  ⟨{r}, (Finset.coe_singleton r).symm ▸ (Submonoid.powers_eq_closure r).symm⟩
#align submonoid.powers_fg Submonoid.powers_fg
#align add_submonoid.multiples_fg AddSubmonoid.multiples_fg
-/

/- warning: monoid.powers_fg -> Monoid.powers_fg is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (r : M), Monoid.FG.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.powers.{u1} M _inst_1 r)) (Submonoid.toMonoid.{u1} M _inst_1 (Submonoid.powers.{u1} M _inst_1 r))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (r : M), Monoid.FG.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.powers.{u1} M _inst_1 r))) (Submonoid.toMonoid.{u1} M _inst_1 (Submonoid.powers.{u1} M _inst_1 r))
Case conversion may be inaccurate. Consider using '#align monoid.powers_fg Monoid.powers_fgₓ'. -/
@[to_additive AddMonoid.multiples_fg]
instance Monoid.powers_fg (r : M) : Monoid.FG (Submonoid.powers r) :=
  (Monoid.fg_iff_submonoid_fg _).mpr (Submonoid.powers_fg r)
#align monoid.powers_fg Monoid.powers_fg
#align add_monoid.multiples_fg AddMonoid.multiples_fg

/- warning: monoid.closure_finset_fg -> Monoid.closure_finset_fg is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (s : Finset.{u1} M), Monoid.FG.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} M) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} M) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} M) (Set.{u1} M) (Finset.Set.hasCoeT.{u1} M))) s))) (Submonoid.toMonoid.{u1} M _inst_1 (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} M) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} M) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} M) (Set.{u1} M) (Finset.Set.hasCoeT.{u1} M))) s)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (s : Finset.{u1} M), Monoid.FG.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) (Finset.toSet.{u1} M s)))) (Submonoid.toMonoid.{u1} M _inst_1 (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) (Finset.toSet.{u1} M s)))
Case conversion may be inaccurate. Consider using '#align monoid.closure_finset_fg Monoid.closure_finset_fgₓ'. -/
@[to_additive]
instance Monoid.closure_finset_fg (s : Finset M) : Monoid.FG (Submonoid.closure (s : Set M)) :=
  by
  refine' ⟨⟨s.preimage coe (subtype.coe_injective.inj_on _), _⟩⟩
  rw [Finset.coe_preimage, Submonoid.closure_closure_coe_preimage]
#align monoid.closure_finset_fg Monoid.closure_finset_fg
#align add_monoid.closure_finset_fg AddMonoid.closure_finset_fg

/- warning: monoid.closure_finite_fg -> Monoid.closure_finite_fg is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (s : Set.{u1} M) [_inst_3 : Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} M) Type.{u1} (Set.hasCoeToSort.{u1} M) s)], Monoid.FG.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s)) (Submonoid.toMonoid.{u1} M _inst_1 (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (s : Set.{u1} M) [_inst_3 : Finite.{succ u1} (Set.Elem.{u1} M s)], Monoid.FG.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s))) (Submonoid.toMonoid.{u1} M _inst_1 (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s))
Case conversion may be inaccurate. Consider using '#align monoid.closure_finite_fg Monoid.closure_finite_fgₓ'. -/
@[to_additive]
instance Monoid.closure_finite_fg (s : Set M) [Finite s] : Monoid.FG (Submonoid.closure s) :=
  haveI := Fintype.ofFinite s
  s.coe_to_finset ▸ Monoid.closure_finset_fg s.to_finset
#align monoid.closure_finite_fg Monoid.closure_finite_fg
#align add_monoid.closure_finite_fg AddMonoid.closure_finite_fg

/-! ### Groups and subgroups -/


variable {G H : Type _} [Group G] [AddGroup H]

section Subgroup

#print Subgroup.FG /-
/-- A subgroup of `G` is finitely generated if it is the closure of a finite subset of `G`. -/
@[to_additive]
def Subgroup.FG (P : Subgroup G) : Prop :=
  ∃ S : Finset G, Subgroup.closure ↑S = P
#align subgroup.fg Subgroup.FG
#align add_subgroup.fg AddSubgroup.FG
-/

/-- An additive subgroup of `H` is finitely generated if it is the closure of a finite subset of
`H`. -/
add_decl_doc AddSubgroup.FG

#print Subgroup.fg_iff /-
/-- An equivalent expression of `subgroup.fg` in terms of `set.finite` instead of `finset`. -/
@[to_additive
      "An equivalent expression of `add_subgroup.fg` in terms of `set.finite` instead of\n`finset`."]
theorem Subgroup.fg_iff (P : Subgroup G) :
    Subgroup.FG P ↔ ∃ S : Set G, Subgroup.closure S = P ∧ S.Finite :=
  ⟨fun ⟨S, hS⟩ => ⟨S, hS, Finset.finite_toSet S⟩, fun ⟨S, hS, hf⟩ =>
    ⟨Set.Finite.toFinset hf, by simp [hS]⟩⟩
#align subgroup.fg_iff Subgroup.fg_iff
#align add_subgroup.fg_iff AddSubgroup.fg_iff
-/

#print Subgroup.fg_iff_submonoid_fg /-
/-- A subgroup is finitely generated if and only if it is finitely generated as a submonoid. -/
@[to_additive AddSubgroup.fg_iff_addSubmonoid_fg
      "An additive subgroup is finitely generated if\nand only if it is finitely generated as an additive submonoid."]
theorem Subgroup.fg_iff_submonoid_fg (P : Subgroup G) : P.FG ↔ P.toSubmonoid.FG :=
  by
  constructor
  · rintro ⟨S, rfl⟩
    rw [Submonoid.fg_iff]
    refine' ⟨S ∪ S⁻¹, _, S.finite_to_set.union S.finite_to_set.inv⟩
    exact (Subgroup.closure_toSubmonoid _).symm
  · rintro ⟨S, hS⟩
    refine' ⟨S, le_antisymm _ _⟩
    · rw [Subgroup.closure_le, ← Subgroup.coe_toSubmonoid, ← hS]
      exact Submonoid.subset_closure
    · rw [← Subgroup.toSubmonoid_le, ← hS, Submonoid.closure_le]
      exact Subgroup.subset_closure
#align subgroup.fg_iff_submonoid_fg Subgroup.fg_iff_submonoid_fg
#align add_subgroup.fg_iff_add_submonoid.fg AddSubgroup.fg_iff_addSubmonoid_fg
-/

/- warning: subgroup.fg_iff_add_fg -> Subgroup.fg_iff_add_fg is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] (P : Subgroup.{u1} G _inst_3), Iff (Subgroup.FG.{u1} G _inst_3 P) (AddSubgroup.FG.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3) (coeFn.{succ u1, succ u1} (OrderIso.{u1, u1} (Subgroup.{u1} G _inst_3) (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (Preorder.toHasLe.{u1} (Subgroup.{u1} G _inst_3) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_3) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.setLike.{u1} G _inst_3)))) (Preorder.toHasLe.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (PartialOrder.toPreorder.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (SetLike.partialOrder.{u1, u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (Additive.{u1} G) (AddSubgroup.setLike.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)))))) (fun (_x : RelIso.{u1, u1} (Subgroup.{u1} G _inst_3) (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (LE.le.{u1} (Subgroup.{u1} G _inst_3) (Preorder.toHasLe.{u1} (Subgroup.{u1} G _inst_3) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_3) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.setLike.{u1} G _inst_3))))) (LE.le.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (Preorder.toHasLe.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (PartialOrder.toPreorder.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (SetLike.partialOrder.{u1, u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (Additive.{u1} G) (AddSubgroup.setLike.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3))))))) => (Subgroup.{u1} G _inst_3) -> (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3))) (RelIso.hasCoeToFun.{u1, u1} (Subgroup.{u1} G _inst_3) (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (LE.le.{u1} (Subgroup.{u1} G _inst_3) (Preorder.toHasLe.{u1} (Subgroup.{u1} G _inst_3) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_3) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.setLike.{u1} G _inst_3))))) (LE.le.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (Preorder.toHasLe.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (PartialOrder.toPreorder.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (SetLike.partialOrder.{u1, u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (Additive.{u1} G) (AddSubgroup.setLike.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3))))))) (Subgroup.toAddSubgroup.{u1} G _inst_3) P))
but is expected to have type
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] (P : Subgroup.{u1} G _inst_3), Iff (Subgroup.FG.{u1} G _inst_3 P) (AddSubgroup.FG.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3) (FunLike.coe.{succ u1, succ u1, succ u1} (RelIso.{u1, u1} (Subgroup.{u1} G _inst_3) (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Subgroup.{u1} G _inst_3) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Subgroup.{u1} G _inst_3) => LE.le.{u1} (Subgroup.{u1} G _inst_3) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_3) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_3) (SetLike.instPartialOrder.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_3)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) => LE.le.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (Preorder.toLE.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (PartialOrder.toPreorder.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (SetLike.instPartialOrder.{u1, u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (Additive.{u1} G) (AddSubgroup.instSetLikeAddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3))))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) (Subgroup.{u1} G _inst_3) (fun (_x : Subgroup.{u1} G _inst_3) => AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (RelHomClass.toFunLike.{u1, u1, u1} (RelIso.{u1, u1} (Subgroup.{u1} G _inst_3) (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Subgroup.{u1} G _inst_3) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Subgroup.{u1} G _inst_3) => LE.le.{u1} (Subgroup.{u1} G _inst_3) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_3) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_3) (SetLike.instPartialOrder.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_3)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) => LE.le.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (Preorder.toLE.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (PartialOrder.toPreorder.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (SetLike.instPartialOrder.{u1, u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (Additive.{u1} G) (AddSubgroup.instSetLikeAddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3))))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) (Subgroup.{u1} G _inst_3) (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Subgroup.{u1} G _inst_3) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Subgroup.{u1} G _inst_3) => LE.le.{u1} (Subgroup.{u1} G _inst_3) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_3) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_3) (SetLike.instPartialOrder.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_3)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) => LE.le.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (Preorder.toLE.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (PartialOrder.toPreorder.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (SetLike.instPartialOrder.{u1, u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (Additive.{u1} G) (AddSubgroup.instSetLikeAddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3))))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302) (RelIso.instRelHomClassRelIso.{u1, u1} (Subgroup.{u1} G _inst_3) (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Subgroup.{u1} G _inst_3) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Subgroup.{u1} G _inst_3) => LE.le.{u1} (Subgroup.{u1} G _inst_3) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_3) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_3) (SetLike.instPartialOrder.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_3)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) => LE.le.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (Preorder.toLE.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (PartialOrder.toPreorder.{u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (SetLike.instPartialOrder.{u1, u1} (AddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3)) (Additive.{u1} G) (AddSubgroup.instSetLikeAddSubgroup.{u1} (Additive.{u1} G) (Additive.addGroup.{u1} G _inst_3))))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302))) (Subgroup.toAddSubgroup.{u1} G _inst_3) P))
Case conversion may be inaccurate. Consider using '#align subgroup.fg_iff_add_fg Subgroup.fg_iff_add_fgₓ'. -/
theorem Subgroup.fg_iff_add_fg (P : Subgroup G) : P.FG ↔ P.toAddSubgroup.FG :=
  by
  rw [Subgroup.fg_iff_submonoid_fg, AddSubgroup.fg_iff_addSubmonoid_fg]
  exact (Subgroup.toSubmonoid P).fg_iff_add_fg
#align subgroup.fg_iff_add_fg Subgroup.fg_iff_add_fg

/- warning: add_subgroup.fg_iff_mul_fg -> AddSubgroup.fg_iff_mul_fg is a dubious translation:
lean 3 declaration is
  forall {H : Type.{u1}} [_inst_4 : AddGroup.{u1} H] (P : AddSubgroup.{u1} H _inst_4), Iff (AddSubgroup.FG.{u1} H _inst_4 P) (Subgroup.FG.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4) (coeFn.{succ u1, succ u1} (OrderIso.{u1, u1} (AddSubgroup.{u1} H _inst_4) (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (Preorder.toHasLe.{u1} (AddSubgroup.{u1} H _inst_4) (PartialOrder.toPreorder.{u1} (AddSubgroup.{u1} H _inst_4) (SetLike.partialOrder.{u1, u1} (AddSubgroup.{u1} H _inst_4) H (AddSubgroup.setLike.{u1} H _inst_4)))) (Preorder.toHasLe.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (Multiplicative.{u1} H) (Subgroup.setLike.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)))))) (fun (_x : RelIso.{u1, u1} (AddSubgroup.{u1} H _inst_4) (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (LE.le.{u1} (AddSubgroup.{u1} H _inst_4) (Preorder.toHasLe.{u1} (AddSubgroup.{u1} H _inst_4) (PartialOrder.toPreorder.{u1} (AddSubgroup.{u1} H _inst_4) (SetLike.partialOrder.{u1, u1} (AddSubgroup.{u1} H _inst_4) H (AddSubgroup.setLike.{u1} H _inst_4))))) (LE.le.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (Preorder.toHasLe.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (Multiplicative.{u1} H) (Subgroup.setLike.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4))))))) => (AddSubgroup.{u1} H _inst_4) -> (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4))) (RelIso.hasCoeToFun.{u1, u1} (AddSubgroup.{u1} H _inst_4) (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (LE.le.{u1} (AddSubgroup.{u1} H _inst_4) (Preorder.toHasLe.{u1} (AddSubgroup.{u1} H _inst_4) (PartialOrder.toPreorder.{u1} (AddSubgroup.{u1} H _inst_4) (SetLike.partialOrder.{u1, u1} (AddSubgroup.{u1} H _inst_4) H (AddSubgroup.setLike.{u1} H _inst_4))))) (LE.le.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (Preorder.toHasLe.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (Multiplicative.{u1} H) (Subgroup.setLike.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4))))))) (AddSubgroup.toSubgroup.{u1} H _inst_4) P))
but is expected to have type
  forall {H : Type.{u1}} [_inst_4 : AddGroup.{u1} H] (P : AddSubgroup.{u1} H _inst_4), Iff (AddSubgroup.FG.{u1} H _inst_4 P) (Subgroup.FG.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4) (FunLike.coe.{succ u1, succ u1, succ u1} (RelIso.{u1, u1} (AddSubgroup.{u1} H _inst_4) (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : AddSubgroup.{u1} H _inst_4) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : AddSubgroup.{u1} H _inst_4) => LE.le.{u1} (AddSubgroup.{u1} H _inst_4) (Preorder.toLE.{u1} (AddSubgroup.{u1} H _inst_4) (PartialOrder.toPreorder.{u1} (AddSubgroup.{u1} H _inst_4) (SetLike.instPartialOrder.{u1, u1} (AddSubgroup.{u1} H _inst_4) H (AddSubgroup.instSetLikeAddSubgroup.{u1} H _inst_4)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) => LE.le.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (Preorder.toLE.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (SetLike.instPartialOrder.{u1, u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (Multiplicative.{u1} H) (Subgroup.instSetLikeSubgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4))))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) (AddSubgroup.{u1} H _inst_4) (fun (_x : AddSubgroup.{u1} H _inst_4) => Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (RelHomClass.toFunLike.{u1, u1, u1} (RelIso.{u1, u1} (AddSubgroup.{u1} H _inst_4) (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : AddSubgroup.{u1} H _inst_4) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : AddSubgroup.{u1} H _inst_4) => LE.le.{u1} (AddSubgroup.{u1} H _inst_4) (Preorder.toLE.{u1} (AddSubgroup.{u1} H _inst_4) (PartialOrder.toPreorder.{u1} (AddSubgroup.{u1} H _inst_4) (SetLike.instPartialOrder.{u1, u1} (AddSubgroup.{u1} H _inst_4) H (AddSubgroup.instSetLikeAddSubgroup.{u1} H _inst_4)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) => LE.le.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (Preorder.toLE.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (SetLike.instPartialOrder.{u1, u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (Multiplicative.{u1} H) (Subgroup.instSetLikeSubgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4))))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) (AddSubgroup.{u1} H _inst_4) (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : AddSubgroup.{u1} H _inst_4) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : AddSubgroup.{u1} H _inst_4) => LE.le.{u1} (AddSubgroup.{u1} H _inst_4) (Preorder.toLE.{u1} (AddSubgroup.{u1} H _inst_4) (PartialOrder.toPreorder.{u1} (AddSubgroup.{u1} H _inst_4) (SetLike.instPartialOrder.{u1, u1} (AddSubgroup.{u1} H _inst_4) H (AddSubgroup.instSetLikeAddSubgroup.{u1} H _inst_4)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) => LE.le.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (Preorder.toLE.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (SetLike.instPartialOrder.{u1, u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (Multiplicative.{u1} H) (Subgroup.instSetLikeSubgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4))))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302) (RelIso.instRelHomClassRelIso.{u1, u1} (AddSubgroup.{u1} H _inst_4) (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : AddSubgroup.{u1} H _inst_4) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : AddSubgroup.{u1} H _inst_4) => LE.le.{u1} (AddSubgroup.{u1} H _inst_4) (Preorder.toLE.{u1} (AddSubgroup.{u1} H _inst_4) (PartialOrder.toPreorder.{u1} (AddSubgroup.{u1} H _inst_4) (SetLike.instPartialOrder.{u1, u1} (AddSubgroup.{u1} H _inst_4) H (AddSubgroup.instSetLikeAddSubgroup.{u1} H _inst_4)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) => LE.le.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (Preorder.toLE.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (SetLike.instPartialOrder.{u1, u1} (Subgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4)) (Multiplicative.{u1} H) (Subgroup.instSetLikeSubgroup.{u1} (Multiplicative.{u1} H) (Multiplicative.group.{u1} H _inst_4))))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302))) (AddSubgroup.toSubgroup.{u1} H _inst_4) P))
Case conversion may be inaccurate. Consider using '#align add_subgroup.fg_iff_mul_fg AddSubgroup.fg_iff_mul_fgₓ'. -/
theorem AddSubgroup.fg_iff_mul_fg (P : AddSubgroup H) : P.FG ↔ P.toSubgroup.FG :=
  by
  rw [AddSubgroup.fg_iff_addSubmonoid_fg, Subgroup.fg_iff_submonoid_fg]
  exact AddSubmonoid.fg_iff_mul_fg (AddSubgroup.toAddSubmonoid P)
#align add_subgroup.fg_iff_mul_fg AddSubgroup.fg_iff_mul_fg

end Subgroup

section Group

variable (G H)

#print Group.FG /-
/-- A group is finitely generated if it is finitely generated as a submonoid of itself. -/
class Group.FG : Prop where
  out : (⊤ : Subgroup G).FG
#align group.fg Group.FG
-/

#print AddGroup.FG /-
/-- An additive group is finitely generated if it is finitely generated as an additive submonoid of
itself. -/
class AddGroup.FG : Prop where
  out : (⊤ : AddSubgroup H).FG
#align add_group.fg AddGroup.FG
-/

attribute [to_additive] Group.FG

variable {G H}

/- warning: group.fg_def -> Group.fg_def is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G], Iff (Group.FG.{u1} G _inst_3) (Subgroup.FG.{u1} G _inst_3 (Top.top.{u1} (Subgroup.{u1} G _inst_3) (Subgroup.hasTop.{u1} G _inst_3)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G], Iff (Group.FG.{u1} G _inst_3) (Subgroup.FG.{u1} G _inst_3 (Top.top.{u1} (Subgroup.{u1} G _inst_3) (Subgroup.instTopSubgroup.{u1} G _inst_3)))
Case conversion may be inaccurate. Consider using '#align group.fg_def Group.fg_defₓ'. -/
theorem Group.fg_def : Group.FG G ↔ (⊤ : Subgroup G).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align group.fg_def Group.fg_def

/- warning: add_group.fg_def -> AddGroup.fg_def is a dubious translation:
lean 3 declaration is
  forall {H : Type.{u1}} [_inst_4 : AddGroup.{u1} H], Iff (AddGroup.FG.{u1} H _inst_4) (AddSubgroup.FG.{u1} H _inst_4 (Top.top.{u1} (AddSubgroup.{u1} H _inst_4) (AddSubgroup.hasTop.{u1} H _inst_4)))
but is expected to have type
  forall {H : Type.{u1}} [_inst_4 : AddGroup.{u1} H], Iff (AddGroup.FG.{u1} H _inst_4) (AddSubgroup.FG.{u1} H _inst_4 (Top.top.{u1} (AddSubgroup.{u1} H _inst_4) (AddSubgroup.instTopAddSubgroup.{u1} H _inst_4)))
Case conversion may be inaccurate. Consider using '#align add_group.fg_def AddGroup.fg_defₓ'. -/
theorem AddGroup.fg_def : AddGroup.FG H ↔ (⊤ : AddSubgroup H).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align add_group.fg_def AddGroup.fg_def

/- warning: group.fg_iff -> Group.fg_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G], Iff (Group.FG.{u1} G _inst_3) (Exists.{succ u1} (Set.{u1} G) (fun (S : Set.{u1} G) => And (Eq.{succ u1} (Subgroup.{u1} G _inst_3) (Subgroup.closure.{u1} G _inst_3 S) (Top.top.{u1} (Subgroup.{u1} G _inst_3) (Subgroup.hasTop.{u1} G _inst_3))) (Set.Finite.{u1} G S)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G], Iff (Group.FG.{u1} G _inst_3) (Exists.{succ u1} (Set.{u1} G) (fun (S : Set.{u1} G) => And (Eq.{succ u1} (Subgroup.{u1} G _inst_3) (Subgroup.closure.{u1} G _inst_3 S) (Top.top.{u1} (Subgroup.{u1} G _inst_3) (Subgroup.instTopSubgroup.{u1} G _inst_3))) (Set.Finite.{u1} G S)))
Case conversion may be inaccurate. Consider using '#align group.fg_iff Group.fg_iffₓ'. -/
/-- An equivalent expression of `group.fg` in terms of `set.finite` instead of `finset`. -/
@[to_additive
      "An equivalent expression of `add_group.fg` in terms of `set.finite` instead of\n`finset`."]
theorem Group.fg_iff : Group.FG G ↔ ∃ S : Set G, Subgroup.closure S = (⊤ : Subgroup G) ∧ S.Finite :=
  ⟨fun h => (Subgroup.fg_iff ⊤).1 h.out, fun h => ⟨(Subgroup.fg_iff ⊤).2 h⟩⟩
#align group.fg_iff Group.fg_iff
#align add_group.fg_iff AddGroup.fg_iff

/- warning: group.fg_iff' -> Group.fg_iff' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G], Iff (Group.FG.{u1} G _inst_3) (Exists.{1} Nat (fun (n : Nat) => Exists.{succ u1} (Finset.{u1} G) (fun (S : Finset.{u1} G) => And (Eq.{1} Nat (Finset.card.{u1} G S) n) (Eq.{succ u1} (Subgroup.{u1} G _inst_3) (Subgroup.closure.{u1} G _inst_3 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} G) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} G) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} G) (Set.{u1} G) (Finset.Set.hasCoeT.{u1} G))) S)) (Top.top.{u1} (Subgroup.{u1} G _inst_3) (Subgroup.hasTop.{u1} G _inst_3))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G], Iff (Group.FG.{u1} G _inst_3) (Exists.{1} Nat (fun (n : Nat) => Exists.{succ u1} (Finset.{u1} G) (fun (S : Finset.{u1} G) => And (Eq.{1} Nat (Finset.card.{u1} G S) n) (Eq.{succ u1} (Subgroup.{u1} G _inst_3) (Subgroup.closure.{u1} G _inst_3 (Finset.toSet.{u1} G S)) (Top.top.{u1} (Subgroup.{u1} G _inst_3) (Subgroup.instTopSubgroup.{u1} G _inst_3))))))
Case conversion may be inaccurate. Consider using '#align group.fg_iff' Group.fg_iff'ₓ'. -/
@[to_additive]
theorem Group.fg_iff' :
    Group.FG G ↔ ∃ (n : _)(S : Finset G), S.card = n ∧ Subgroup.closure (S : Set G) = ⊤ :=
  Group.fg_def.trans ⟨fun ⟨S, hS⟩ => ⟨S.card, S, rfl, hS⟩, fun ⟨n, S, hn, hS⟩ => ⟨S, hS⟩⟩
#align group.fg_iff' Group.fg_iff'
#align add_group.fg_iff' AddGroup.fg_iff'

#print Group.fg_iff_monoid_fg /-
/-- A group is finitely generated if and only if it is finitely generated as a monoid. -/
@[to_additive AddGroup.fg_iff_addMonoid_fg
      "An additive group is finitely generated if and only\nif it is finitely generated as an additive monoid."]
theorem Group.fg_iff_monoid_fg : Group.FG G ↔ Monoid.FG G :=
  ⟨fun h => Monoid.fg_def.2 <| (Subgroup.fg_iff_submonoid_fg ⊤).1 (Group.fg_def.1 h), fun h =>
    Group.fg_def.2 <| (Subgroup.fg_iff_submonoid_fg ⊤).2 (Monoid.fg_def.1 h)⟩
#align group.fg_iff_monoid.fg Group.fg_iff_monoid_fg
#align add_group.fg_iff_add_monoid.fg AddGroup.fg_iff_addMonoid_fg
-/

#print GroupFG.iff_add_fg /-
theorem GroupFG.iff_add_fg : Group.FG G ↔ AddGroup.FG (Additive G) :=
  ⟨fun h => ⟨(Subgroup.fg_iff_add_fg ⊤).1 h.out⟩, fun h => ⟨(Subgroup.fg_iff_add_fg ⊤).2 h.out⟩⟩
#align group_fg.iff_add_fg GroupFG.iff_add_fg
-/

#print AddGroup.fg_iff_mul_fg /-
theorem AddGroup.fg_iff_mul_fg : AddGroup.FG H ↔ Group.FG (Multiplicative H) :=
  ⟨fun h => ⟨(AddSubgroup.fg_iff_mul_fg ⊤).1 h.out⟩, fun h =>
    ⟨(AddSubgroup.fg_iff_mul_fg ⊤).2 h.out⟩⟩
#align add_group.fg_iff_mul_fg AddGroup.fg_iff_mul_fg
-/

#print AddGroup.fg_of_group_fg /-
instance AddGroup.fg_of_group_fg [Group.FG G] : AddGroup.FG (Additive G) :=
  GroupFG.iff_add_fg.1 ‹_›
#align add_group.fg_of_group_fg AddGroup.fg_of_group_fg
-/

#print Group.fg_of_mul_group_fg /-
instance Group.fg_of_mul_group_fg [AddGroup.FG H] : Group.FG (Multiplicative H) :=
  AddGroup.fg_iff_mul_fg.1 ‹_›
#align group.fg_of_mul_group_fg Group.fg_of_mul_group_fg
-/

#print Group.fg_of_finite /-
@[to_additive]
instance (priority := 100) Group.fg_of_finite [Finite G] : Group.FG G :=
  by
  cases nonempty_fintype G
  exact ⟨⟨Finset.univ, by rw [Finset.coe_univ] <;> exact Subgroup.closure_univ⟩⟩
#align group.fg_of_finite Group.fg_of_finite
#align add_group.fg_of_finite AddGroup.fg_of_finite
-/

/- warning: group.fg_of_surjective -> Group.fg_of_surjective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] {G' : Type.{u2}} [_inst_5 : Group.{u2} G'] [hG : Group.FG.{u1} G _inst_3] {f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_5)))}, (Function.Surjective.{succ u1, succ u2} G G' (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_5)))) (fun (_x : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_5)))) => G -> G') (MonoidHom.hasCoeToFun.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_5)))) f)) -> (Group.FG.{u2} G' _inst_5)
but is expected to have type
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] {G' : Type.{u2}} [_inst_5 : Group.{u2} G'] [hG : Group.FG.{u1} G _inst_3] {f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_5)))}, (Function.Surjective.{succ u1, succ u2} G G' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_5)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : G) => G') _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_5)))) G G' (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)))) (MulOneClass.toMul.{u2} G' (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_5)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_5)))) G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_5))) (MonoidHom.monoidHomClass.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_5)))))) f)) -> (Group.FG.{u2} G' _inst_5)
Case conversion may be inaccurate. Consider using '#align group.fg_of_surjective Group.fg_of_surjectiveₓ'. -/
@[to_additive]
theorem Group.fg_of_surjective {G' : Type _} [Group G'] [hG : Group.FG G] {f : G →* G'}
    (hf : Function.Surjective f) : Group.FG G' :=
  Group.fg_iff_monoid_fg.mpr <|
    @Monoid.fg_of_surjective G _ G' _ (Group.fg_iff_monoid_fg.mp hG) f hf
#align group.fg_of_surjective Group.fg_of_surjective
#align add_group.fg_of_surjective AddGroup.fg_of_surjective

/- warning: group.fg_range -> Group.fg_range is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] {G' : Type.{u2}} [_inst_5 : Group.{u2} G'] [_inst_6 : Group.FG.{u1} G _inst_3] (f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_5)))), Group.FG.{u2} (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} G' _inst_5) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} G' _inst_5) G' (Subgroup.setLike.{u2} G' _inst_5)) (MonoidHom.range.{u1, u2} G _inst_3 G' _inst_5 f)) (Subgroup.toGroup.{u2} G' _inst_5 (MonoidHom.range.{u1, u2} G _inst_3 G' _inst_5 f))
but is expected to have type
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] {G' : Type.{u2}} [_inst_5 : Group.{u2} G'] [_inst_6 : Group.FG.{u1} G _inst_3] (f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_5)))), Group.FG.{u2} (Subtype.{succ u2} G' (fun (x : G') => Membership.mem.{u2, u2} G' (Subgroup.{u2} G' _inst_5) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} G' _inst_5) G' (Subgroup.instSetLikeSubgroup.{u2} G' _inst_5)) x (MonoidHom.range.{u1, u2} G _inst_3 G' _inst_5 f))) (Subgroup.toGroup.{u2} G' _inst_5 (MonoidHom.range.{u1, u2} G _inst_3 G' _inst_5 f))
Case conversion may be inaccurate. Consider using '#align group.fg_range Group.fg_rangeₓ'. -/
@[to_additive]
instance Group.fg_range {G' : Type _} [Group G'] [Group.FG G] (f : G →* G') : Group.FG f.range :=
  Group.fg_of_surjective f.rangeRestrict_surjective
#align group.fg_range Group.fg_range
#align add_group.fg_range AddGroup.fg_range

/- warning: group.closure_finset_fg -> Group.closure_finset_fg is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] (s : Finset.{u1} G), Group.FG.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.setLike.{u1} G _inst_3)) (Subgroup.closure.{u1} G _inst_3 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} G) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} G) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} G) (Set.{u1} G) (Finset.Set.hasCoeT.{u1} G))) s))) (Subgroup.toGroup.{u1} G _inst_3 (Subgroup.closure.{u1} G _inst_3 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} G) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} G) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} G) (Set.{u1} G) (Finset.Set.hasCoeT.{u1} G))) s)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] (s : Finset.{u1} G), Group.FG.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_3) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_3)) x (Subgroup.closure.{u1} G _inst_3 (Finset.toSet.{u1} G s)))) (Subgroup.toGroup.{u1} G _inst_3 (Subgroup.closure.{u1} G _inst_3 (Finset.toSet.{u1} G s)))
Case conversion may be inaccurate. Consider using '#align group.closure_finset_fg Group.closure_finset_fgₓ'. -/
@[to_additive]
instance Group.closure_finset_fg (s : Finset G) : Group.FG (Subgroup.closure (s : Set G)) :=
  by
  refine' ⟨⟨s.preimage coe (subtype.coe_injective.inj_on _), _⟩⟩
  rw [Finset.coe_preimage, ← Subgroup.coeSubtype, Subgroup.closure_preimage_eq_top]
#align group.closure_finset_fg Group.closure_finset_fg
#align add_group.closure_finset_fg AddGroup.closure_finset_fg

/- warning: group.closure_finite_fg -> Group.closure_finite_fg is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] (s : Set.{u1} G) [_inst_5 : Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} G) Type.{u1} (Set.hasCoeToSort.{u1} G) s)], Group.FG.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.setLike.{u1} G _inst_3)) (Subgroup.closure.{u1} G _inst_3 s)) (Subgroup.toGroup.{u1} G _inst_3 (Subgroup.closure.{u1} G _inst_3 s))
but is expected to have type
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] (s : Set.{u1} G) [_inst_5 : Finite.{succ u1} (Set.Elem.{u1} G s)], Group.FG.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_3) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_3)) x (Subgroup.closure.{u1} G _inst_3 s))) (Subgroup.toGroup.{u1} G _inst_3 (Subgroup.closure.{u1} G _inst_3 s))
Case conversion may be inaccurate. Consider using '#align group.closure_finite_fg Group.closure_finite_fgₓ'. -/
@[to_additive]
instance Group.closure_finite_fg (s : Set G) [Finite s] : Group.FG (Subgroup.closure s) :=
  haveI := Fintype.ofFinite s
  s.coe_to_finset ▸ Group.closure_finset_fg s.to_finset
#align group.closure_finite_fg Group.closure_finite_fg
#align add_group.closure_finite_fg AddGroup.closure_finite_fg

variable (G)

#print Group.rank /-
/-- The minimum number of generators of a group. -/
@[to_additive "The minimum number of generators of an additive group"]
noncomputable def Group.rank [h : Group.FG G] :=
  @Nat.find _ (Classical.decPred _) (Group.fg_iff'.mp h)
#align group.rank Group.rank
#align add_group.rank AddGroup.rank
-/

/- warning: group.rank_spec -> Group.rank_spec is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_3 : Group.{u1} G] [h : Group.FG.{u1} G _inst_3], Exists.{succ u1} (Finset.{u1} G) (fun (S : Finset.{u1} G) => And (Eq.{1} Nat (Finset.card.{u1} G S) (Group.rank.{u1} G _inst_3 h)) (Eq.{succ u1} (Subgroup.{u1} G _inst_3) (Subgroup.closure.{u1} G _inst_3 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} G) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} G) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} G) (Set.{u1} G) (Finset.Set.hasCoeT.{u1} G))) S)) (Top.top.{u1} (Subgroup.{u1} G _inst_3) (Subgroup.hasTop.{u1} G _inst_3))))
but is expected to have type
  forall (G : Type.{u1}) [_inst_3 : Group.{u1} G] [h : Group.FG.{u1} G _inst_3], Exists.{succ u1} (Finset.{u1} G) (fun (S : Finset.{u1} G) => And (Eq.{1} Nat (Finset.card.{u1} G S) (Group.rank.{u1} G _inst_3 h)) (Eq.{succ u1} (Subgroup.{u1} G _inst_3) (Subgroup.closure.{u1} G _inst_3 (Finset.toSet.{u1} G S)) (Top.top.{u1} (Subgroup.{u1} G _inst_3) (Subgroup.instTopSubgroup.{u1} G _inst_3))))
Case conversion may be inaccurate. Consider using '#align group.rank_spec Group.rank_specₓ'. -/
@[to_additive]
theorem Group.rank_spec [h : Group.FG G] :
    ∃ S : Finset G, S.card = Group.rank G ∧ Subgroup.closure (S : Set G) = ⊤ :=
  @Nat.find_spec _ (Classical.decPred _) (Group.fg_iff'.mp h)
#align group.rank_spec Group.rank_spec
#align add_group.rank_spec AddGroup.rank_spec

/- warning: group.rank_le -> Group.rank_le is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_3 : Group.{u1} G] [h : Group.FG.{u1} G _inst_3] {S : Finset.{u1} G}, (Eq.{succ u1} (Subgroup.{u1} G _inst_3) (Subgroup.closure.{u1} G _inst_3 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} G) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} G) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} G) (Set.{u1} G) (Finset.Set.hasCoeT.{u1} G))) S)) (Top.top.{u1} (Subgroup.{u1} G _inst_3) (Subgroup.hasTop.{u1} G _inst_3))) -> (LE.le.{0} Nat Nat.hasLe (Group.rank.{u1} G _inst_3 h) (Finset.card.{u1} G S))
but is expected to have type
  forall (G : Type.{u1}) [_inst_3 : Group.{u1} G] [h : Group.FG.{u1} G _inst_3] {S : Finset.{u1} G}, (Eq.{succ u1} (Subgroup.{u1} G _inst_3) (Subgroup.closure.{u1} G _inst_3 (Finset.toSet.{u1} G S)) (Top.top.{u1} (Subgroup.{u1} G _inst_3) (Subgroup.instTopSubgroup.{u1} G _inst_3))) -> (LE.le.{0} Nat instLENat (Group.rank.{u1} G _inst_3 h) (Finset.card.{u1} G S))
Case conversion may be inaccurate. Consider using '#align group.rank_le Group.rank_leₓ'. -/
@[to_additive]
theorem Group.rank_le [h : Group.FG G] {S : Finset G} (hS : Subgroup.closure (S : Set G) = ⊤) :
    Group.rank G ≤ S.card :=
  @Nat.find_le _ _ (Classical.decPred _) (Group.fg_iff'.mp h) ⟨S, rfl, hS⟩
#align group.rank_le Group.rank_le
#align add_group.rank_le AddGroup.rank_le

variable {G} {G' : Type _} [Group G']

/- warning: group.rank_le_of_surjective -> Group.rank_le_of_surjective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] {G' : Type.{u2}} [_inst_5 : Group.{u2} G'] [_inst_6 : Group.FG.{u1} G _inst_3] [_inst_7 : Group.FG.{u2} G' _inst_5] (f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_5)))), (Function.Surjective.{succ u1, succ u2} G G' (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_5)))) (fun (_x : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_5)))) => G -> G') (MonoidHom.hasCoeToFun.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_5)))) f)) -> (LE.le.{0} Nat Nat.hasLe (Group.rank.{u2} G' _inst_5 _inst_7) (Group.rank.{u1} G _inst_3 _inst_6))
but is expected to have type
  forall {G : Type.{u2}} [_inst_3 : Group.{u2} G] {G' : Type.{u1}} [_inst_5 : Group.{u1} G'] [_inst_6 : Group.FG.{u2} G _inst_3] [_inst_7 : Group.FG.{u1} G' _inst_5] (f : MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_5)))), (Function.Surjective.{succ u2, succ u1} G G' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_5)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : G) => G') _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_5)))) G G' (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3)))) (MulOneClass.toMul.{u1} G' (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_5)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_5)))) G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_5))) (MonoidHom.monoidHomClass.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_5)))))) f)) -> (LE.le.{0} Nat instLENat (Group.rank.{u1} G' _inst_5 _inst_7) (Group.rank.{u2} G _inst_3 _inst_6))
Case conversion may be inaccurate. Consider using '#align group.rank_le_of_surjective Group.rank_le_of_surjectiveₓ'. -/
@[to_additive]
theorem Group.rank_le_of_surjective [Group.FG G] [Group.FG G'] (f : G →* G')
    (hf : Function.Surjective f) : Group.rank G' ≤ Group.rank G := by
  classical
    obtain ⟨S, hS1, hS2⟩ := Group.rank_spec G
    trans (S.image f).card
    · apply Group.rank_le
      rw [Finset.coe_image, ← MonoidHom.map_closure, hS2, Subgroup.map_top_of_surjective f hf]
    · exact finset.card_image_le.trans_eq hS1
#align group.rank_le_of_surjective Group.rank_le_of_surjective
#align add_group.rank_le_of_surjective AddGroup.rank_le_of_surjective

/- warning: group.rank_range_le -> Group.rank_range_le is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] {G' : Type.{u2}} [_inst_5 : Group.{u2} G'] [_inst_6 : Group.FG.{u1} G _inst_3] {f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_5)))}, LE.le.{0} Nat Nat.hasLe (Group.rank.{u2} (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} G' _inst_5) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} G' _inst_5) G' (Subgroup.setLike.{u2} G' _inst_5)) (MonoidHom.range.{u1, u2} G _inst_3 G' _inst_5 f)) (Subgroup.toGroup.{u2} G' _inst_5 (MonoidHom.range.{u1, u2} G _inst_3 G' _inst_5 f)) (Group.fg_range.{u1, u2} G _inst_3 G' _inst_5 _inst_6 f)) (Group.rank.{u1} G _inst_3 _inst_6)
but is expected to have type
  forall {G : Type.{u2}} [_inst_3 : Group.{u2} G] {G' : Type.{u1}} [_inst_5 : Group.{u1} G'] [_inst_6 : Group.FG.{u2} G _inst_3] {f : MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_5)))}, LE.le.{0} Nat instLENat (Group.rank.{u1} (Subtype.{succ u1} G' (fun (x : G') => Membership.mem.{u1, u1} G' (Subgroup.{u1} G' _inst_5) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G' _inst_5) G' (Subgroup.instSetLikeSubgroup.{u1} G' _inst_5)) x (MonoidHom.range.{u2, u1} G _inst_3 G' _inst_5 f))) (Subgroup.toGroup.{u1} G' _inst_5 (MonoidHom.range.{u2, u1} G _inst_3 G' _inst_5 f)) (Group.fg_range.{u2, u1} G _inst_3 G' _inst_5 _inst_6 f)) (Group.rank.{u2} G _inst_3 _inst_6)
Case conversion may be inaccurate. Consider using '#align group.rank_range_le Group.rank_range_leₓ'. -/
@[to_additive]
theorem Group.rank_range_le [Group.FG G] {f : G →* G'} : Group.rank f.range ≤ Group.rank G :=
  Group.rank_le_of_surjective f.range_restrict f.rangeRestrict_surjective
#align group.rank_range_le Group.rank_range_le
#align add_group.rank_range_le AddGroup.rank_range_le

/- warning: group.rank_congr -> Group.rank_congr is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] {G' : Type.{u2}} [_inst_5 : Group.{u2} G'] [_inst_6 : Group.FG.{u1} G _inst_3] [_inst_7 : Group.FG.{u2} G' _inst_5], (MulEquiv.{u1, u2} G G' (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)))) (MulOneClass.toHasMul.{u2} G' (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_5))))) -> (Eq.{1} Nat (Group.rank.{u1} G _inst_3 _inst_6) (Group.rank.{u2} G' _inst_5 _inst_7))
but is expected to have type
  forall {G : Type.{u2}} [_inst_3 : Group.{u2} G] {G' : Type.{u1}} [_inst_5 : Group.{u1} G'] [_inst_6 : Group.FG.{u2} G _inst_3] [_inst_7 : Group.FG.{u1} G' _inst_5], (MulEquiv.{u2, u1} G G' (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3)))) (MulOneClass.toMul.{u1} G' (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_5))))) -> (Eq.{1} Nat (Group.rank.{u2} G _inst_3 _inst_6) (Group.rank.{u1} G' _inst_5 _inst_7))
Case conversion may be inaccurate. Consider using '#align group.rank_congr Group.rank_congrₓ'. -/
@[to_additive]
theorem Group.rank_congr [Group.FG G] [Group.FG G'] (f : G ≃* G') : Group.rank G = Group.rank G' :=
  le_antisymm (Group.rank_le_of_surjective f.symm f.symm.Surjective)
    (Group.rank_le_of_surjective f f.Surjective)
#align group.rank_congr Group.rank_congr
#align add_group.rank_congr AddGroup.rank_congr

end Group

namespace Subgroup

/- warning: subgroup.rank_congr -> Subgroup.rank_congr is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] {H : Subgroup.{u1} G _inst_3} {K : Subgroup.{u1} G _inst_3} [_inst_5 : Group.FG.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.setLike.{u1} G _inst_3)) H) (Subgroup.toGroup.{u1} G _inst_3 H)] [_inst_6 : Group.FG.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.setLike.{u1} G _inst_3)) K) (Subgroup.toGroup.{u1} G _inst_3 K)], (Eq.{succ u1} (Subgroup.{u1} G _inst_3) H K) -> (Eq.{1} Nat (Group.rank.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.setLike.{u1} G _inst_3)) H) (Subgroup.toGroup.{u1} G _inst_3 H) _inst_5) (Group.rank.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.setLike.{u1} G _inst_3)) K) (Subgroup.toGroup.{u1} G _inst_3 K) _inst_6))
but is expected to have type
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] {H : Subgroup.{u1} G _inst_3} {K : Subgroup.{u1} G _inst_3} [_inst_5 : Group.FG.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_3) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_3)) x H)) (Subgroup.toGroup.{u1} G _inst_3 H)] [_inst_6 : Group.FG.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_3) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_3)) x K)) (Subgroup.toGroup.{u1} G _inst_3 K)], (Eq.{succ u1} (Subgroup.{u1} G _inst_3) H K) -> (Eq.{1} Nat (Group.rank.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_3) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_3)) x H)) (Subgroup.toGroup.{u1} G _inst_3 H) _inst_5) (Group.rank.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_3) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_3)) x K)) (Subgroup.toGroup.{u1} G _inst_3 K) _inst_6))
Case conversion may be inaccurate. Consider using '#align subgroup.rank_congr Subgroup.rank_congrₓ'. -/
@[to_additive]
theorem rank_congr {H K : Subgroup G} [Group.FG H] [Group.FG K] (h : H = K) :
    Group.rank H = Group.rank K := by subst h
#align subgroup.rank_congr Subgroup.rank_congr
#align add_subgroup.rank_congr AddSubgroup.rank_congr

/- warning: subgroup.rank_closure_finset_le_card -> Subgroup.rank_closure_finset_le_card is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] (s : Finset.{u1} G), LE.le.{0} Nat Nat.hasLe (Group.rank.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.setLike.{u1} G _inst_3)) (Subgroup.closure.{u1} G _inst_3 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} G) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} G) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} G) (Set.{u1} G) (Finset.Set.hasCoeT.{u1} G))) s))) (Subgroup.toGroup.{u1} G _inst_3 (Subgroup.closure.{u1} G _inst_3 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} G) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} G) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} G) (Set.{u1} G) (Finset.Set.hasCoeT.{u1} G))) s))) (Group.closure_finite_fg.{u1} G _inst_3 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} G) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} G) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} G) (Set.{u1} G) (Finset.Set.hasCoeT.{u1} G))) s) (Finite.of_fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} G) Type.{u1} (Set.hasCoeToSort.{u1} G) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} G) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} G) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} G) (Set.{u1} G) (Finset.Set.hasCoeT.{u1} G))) s)) (FinsetCoe.fintype.{u1} G s)))) (Finset.card.{u1} G s)
but is expected to have type
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] (s : Finset.{u1} G), LE.le.{0} Nat instLENat (Group.rank.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_3) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_3)) x (Subgroup.closure.{u1} G _inst_3 (Finset.toSet.{u1} G s)))) (Subgroup.toGroup.{u1} G _inst_3 (Subgroup.closure.{u1} G _inst_3 (Finset.toSet.{u1} G s))) (Group.closure_finite_fg.{u1} G _inst_3 (Finset.toSet.{u1} G s) (Finite.of_fintype.{u1} (Set.Elem.{u1} G (Finset.toSet.{u1} G s)) (FinsetCoe.fintype.{u1} G s)))) (Finset.card.{u1} G s)
Case conversion may be inaccurate. Consider using '#align subgroup.rank_closure_finset_le_card Subgroup.rank_closure_finset_le_cardₓ'. -/
@[to_additive]
theorem rank_closure_finset_le_card (s : Finset G) : Group.rank (closure (s : Set G)) ≤ s.card := by
  classical
    let t : Finset (closure (s : Set G)) := s.preimage coe (subtype.coe_injective.inj_on _)
    have ht : closure (t : Set (closure (s : Set G))) = ⊤ :=
      by
      rw [Finset.coe_preimage]
      exact closure_preimage_eq_top s
    apply (Group.rank_le (closure (s : Set G)) ht).trans
    rw [← Finset.card_image_of_injOn, Finset.image_preimage]
    · apply Finset.card_filter_le
    · apply subtype.coe_injective.inj_on
#align subgroup.rank_closure_finset_le_card Subgroup.rank_closure_finset_le_card
#align add_subgroup.rank_closure_finset_le_card AddSubgroup.rank_closure_finset_le_card

/- warning: subgroup.rank_closure_finite_le_nat_card -> Subgroup.rank_closure_finite_le_nat_card is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] (s : Set.{u1} G) [_inst_5 : Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} G) Type.{u1} (Set.hasCoeToSort.{u1} G) s)], LE.le.{0} Nat Nat.hasLe (Group.rank.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.setLike.{u1} G _inst_3)) (Subgroup.closure.{u1} G _inst_3 s)) (Subgroup.toGroup.{u1} G _inst_3 (Subgroup.closure.{u1} G _inst_3 s)) (Group.closure_finite_fg.{u1} G _inst_3 s _inst_5)) (Nat.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} G) Type.{u1} (Set.hasCoeToSort.{u1} G) s))
but is expected to have type
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] (s : Set.{u1} G) [_inst_5 : Finite.{succ u1} (Set.Elem.{u1} G s)], LE.le.{0} Nat instLENat (Group.rank.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_3) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_3)) x (Subgroup.closure.{u1} G _inst_3 s))) (Subgroup.toGroup.{u1} G _inst_3 (Subgroup.closure.{u1} G _inst_3 s)) (Group.closure_finite_fg.{u1} G _inst_3 s _inst_5)) (Nat.card.{u1} (Set.Elem.{u1} G s))
Case conversion may be inaccurate. Consider using '#align subgroup.rank_closure_finite_le_nat_card Subgroup.rank_closure_finite_le_nat_cardₓ'. -/
@[to_additive]
theorem rank_closure_finite_le_nat_card (s : Set G) [Finite s] :
    Group.rank (closure s) ≤ Nat.card s :=
  by
  haveI := Fintype.ofFinite s
  rw [Nat.card_eq_fintype_card, ← s.to_finset_card, ← rank_congr (congr_arg _ s.coe_to_finset)]
  exact rank_closure_finset_le_card s.to_finset
#align subgroup.rank_closure_finite_le_nat_card Subgroup.rank_closure_finite_le_nat_card
#align add_subgroup.rank_closure_finite_le_nat_card AddSubgroup.rank_closure_finite_le_nat_card

end Subgroup

section QuotientGroup

#print QuotientGroup.fg /-
@[to_additive]
instance QuotientGroup.fg [Group.FG G] (N : Subgroup G) [Subgroup.Normal N] : Group.FG <| G ⧸ N :=
  Group.fg_of_surjective <| QuotientGroup.mk'_surjective N
#align quotient_group.fg QuotientGroup.fg
#align quotient_add_group.fg QuotientAddGroup.fg
-/

end QuotientGroup

