/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

! This file was ported from Lean 3 source module topology.algebra.uniform_group
! leanprover-community/mathlib commit ee05e9ce1322178f0c12004eb93c00d2c8c00ed2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.UniformSpace.UniformConvergence
import Mathbin.Topology.UniformSpace.UniformEmbedding
import Mathbin.Topology.UniformSpace.CompleteSeparated
import Mathbin.Topology.UniformSpace.Compact
import Mathbin.Topology.Algebra.Group.Basic
import Mathbin.Tactic.Abel

/-!
# Uniform structure on topological groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines uniform groups and its additive counterpart. These typeclasses should be
preferred over using `[topological_space α] [topological_group α]` since every topological
group naturally induces a uniform structure.

## Main declarations
* `uniform_group` and `uniform_add_group`: Multiplicative and additive uniform groups, that
  i.e., groups with uniformly continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`.

## Main results

* `topological_add_group.to_uniform_space` and `topological_add_comm_group_is_uniform` can be used
  to construct a canonical uniformity for a topological add group.

* extension of ℤ-bilinear maps to complete groups (useful for ring completions)

* `quotient_group.complete_space` and `quotient_add_group.complete_space` guarantee that quotients
  of first countable topological groups by normal subgroups are themselves complete. In particular,
  the quotient of a Banach space by a subspace is complete.
-/


noncomputable section

open Classical uniformity Topology Filter Pointwise

section UniformGroup

open Filter Set

variable {α : Type _} {β : Type _}

#print UniformGroup /-
/-- A uniform group is a group in which multiplication and inversion are uniformly continuous. -/
class UniformGroup (α : Type _) [UniformSpace α] [Group α] : Prop where
  uniformContinuous_div : UniformContinuous fun p : α × α => p.1 / p.2
#align uniform_group UniformGroup
-/

#print UniformAddGroup /-
/-- A uniform additive group is an additive group in which addition
  and negation are uniformly continuous.-/
class UniformAddGroup (α : Type _) [UniformSpace α] [AddGroup α] : Prop where
  uniformContinuous_sub : UniformContinuous fun p : α × α => p.1 - p.2
#align uniform_add_group UniformAddGroup
-/

attribute [to_additive] UniformGroup

/- warning: uniform_group.mk' -> UniformGroup.mk' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α], (UniformContinuous.{u1, u1} (Prod.{u1, u1} α α) α (Prod.uniformSpace.{u1, u1} α α _inst_1 _inst_1) _inst_1 (fun (p : Prod.{u1, u1} α α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))) -> (UniformContinuous.{u1, u1} α α _inst_1 _inst_1 (fun (p : α) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) p)) -> (UniformGroup.{u1} α _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α], (UniformContinuous.{u1, u1} (Prod.{u1, u1} α α) α (instUniformSpaceProd.{u1, u1} α α _inst_1 _inst_1) _inst_1 (fun (p : Prod.{u1, u1} α α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))) -> (UniformContinuous.{u1, u1} α α _inst_1 _inst_1 (fun (p : α) => Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2)))) p)) -> (UniformGroup.{u1} α _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align uniform_group.mk' UniformGroup.mk'ₓ'. -/
@[to_additive]
theorem UniformGroup.mk' {α} [UniformSpace α] [Group α]
    (h₁ : UniformContinuous fun p : α × α => p.1 * p.2) (h₂ : UniformContinuous fun p : α => p⁻¹) :
    UniformGroup α :=
  ⟨by
    simpa only [div_eq_mul_inv] using
      h₁.comp (uniform_continuous_fst.prod_mk (h₂.comp uniformContinuous_snd))⟩
#align uniform_group.mk' UniformGroup.mk'
#align uniform_add_group.mk' UniformAddGroup.mk'

variable [UniformSpace α] [Group α] [UniformGroup α]

/- warning: uniform_continuous_div -> uniformContinuous_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2], UniformContinuous.{u1, u1} (Prod.{u1, u1} α α) α (Prod.uniformSpace.{u1, u1} α α _inst_1 _inst_1) _inst_1 (fun (p : Prod.{u1, u1} α α) => HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2], UniformContinuous.{u1, u1} (Prod.{u1, u1} α α) α (instUniformSpaceProd.{u1, u1} α α _inst_1 _inst_1) _inst_1 (fun (p : Prod.{u1, u1} α α) => HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))
Case conversion may be inaccurate. Consider using '#align uniform_continuous_div uniformContinuous_divₓ'. -/
@[to_additive]
theorem uniformContinuous_div : UniformContinuous fun p : α × α => p.1 / p.2 :=
  UniformGroup.uniformContinuous_div
#align uniform_continuous_div uniformContinuous_div
#align uniform_continuous_sub uniformContinuous_sub

/- warning: uniform_continuous.div -> UniformContinuous.div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] [_inst_4 : UniformSpace.{u2} β] {f : β -> α} {g : β -> α}, (UniformContinuous.{u2, u1} β α _inst_4 _inst_1 f) -> (UniformContinuous.{u2, u1} β α _inst_4 _inst_1 g) -> (UniformContinuous.{u2, u1} β α _inst_4 _inst_1 (fun (x : β) => HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] [_inst_4 : UniformSpace.{u2} β] {f : β -> α} {g : β -> α}, (UniformContinuous.{u2, u1} β α _inst_4 _inst_1 f) -> (UniformContinuous.{u2, u1} β α _inst_4 _inst_1 g) -> (UniformContinuous.{u2, u1} β α _inst_4 _inst_1 (fun (x : β) => HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align uniform_continuous.div UniformContinuous.divₓ'. -/
@[to_additive]
theorem UniformContinuous.div [UniformSpace β] {f : β → α} {g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun x => f x / g x :=
  uniformContinuous_div.comp (hf.prod_mk hg)
#align uniform_continuous.div UniformContinuous.div
#align uniform_continuous.sub UniformContinuous.sub

/- warning: uniform_continuous.inv -> UniformContinuous.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] [_inst_4 : UniformSpace.{u2} β] {f : β -> α}, (UniformContinuous.{u2, u1} β α _inst_4 _inst_1 f) -> (UniformContinuous.{u2, u1} β α _inst_4 _inst_1 (fun (x : β) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) (f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] [_inst_4 : UniformSpace.{u2} β] {f : β -> α}, (UniformContinuous.{u2, u1} β α _inst_4 _inst_1 f) -> (UniformContinuous.{u2, u1} β α _inst_4 _inst_1 (fun (x : β) => Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2)))) (f x)))
Case conversion may be inaccurate. Consider using '#align uniform_continuous.inv UniformContinuous.invₓ'. -/
@[to_additive]
theorem UniformContinuous.inv [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
    UniformContinuous fun x => (f x)⁻¹ :=
  by
  have : UniformContinuous fun x => 1 / f x := uniformContinuous_const.div hf
  simp_all
#align uniform_continuous.inv UniformContinuous.inv
#align uniform_continuous.neg UniformContinuous.neg

/- warning: uniform_continuous_inv -> uniformContinuous_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2], UniformContinuous.{u1, u1} α α _inst_1 _inst_1 (fun (x : α) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2], UniformContinuous.{u1, u1} α α _inst_1 _inst_1 (fun (x : α) => Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2)))) x)
Case conversion may be inaccurate. Consider using '#align uniform_continuous_inv uniformContinuous_invₓ'. -/
@[to_additive]
theorem uniformContinuous_inv : UniformContinuous fun x : α => x⁻¹ :=
  uniformContinuous_id.inv
#align uniform_continuous_inv uniformContinuous_inv
#align uniform_continuous_neg uniformContinuous_neg

/- warning: uniform_continuous.mul -> UniformContinuous.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] [_inst_4 : UniformSpace.{u2} β] {f : β -> α} {g : β -> α}, (UniformContinuous.{u2, u1} β α _inst_4 _inst_1 f) -> (UniformContinuous.{u2, u1} β α _inst_4 _inst_1 g) -> (UniformContinuous.{u2, u1} β α _inst_4 _inst_1 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] [_inst_4 : UniformSpace.{u2} β] {f : β -> α} {g : β -> α}, (UniformContinuous.{u2, u1} β α _inst_4 _inst_1 f) -> (UniformContinuous.{u2, u1} β α _inst_4 _inst_1 g) -> (UniformContinuous.{u2, u1} β α _inst_4 _inst_1 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align uniform_continuous.mul UniformContinuous.mulₓ'. -/
@[to_additive]
theorem UniformContinuous.mul [UniformSpace β] {f : β → α} {g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun x => f x * g x :=
  by
  have : UniformContinuous fun x => f x / (g x)⁻¹ := hf.div hg.inv
  simp_all
#align uniform_continuous.mul UniformContinuous.mul
#align uniform_continuous.add UniformContinuous.add

/- warning: uniform_continuous_mul -> uniformContinuous_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2], UniformContinuous.{u1, u1} (Prod.{u1, u1} α α) α (Prod.uniformSpace.{u1, u1} α α _inst_1 _inst_1) _inst_1 (fun (p : Prod.{u1, u1} α α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2], UniformContinuous.{u1, u1} (Prod.{u1, u1} α α) α (instUniformSpaceProd.{u1, u1} α α _inst_1 _inst_1) _inst_1 (fun (p : Prod.{u1, u1} α α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))
Case conversion may be inaccurate. Consider using '#align uniform_continuous_mul uniformContinuous_mulₓ'. -/
@[to_additive]
theorem uniformContinuous_mul : UniformContinuous fun p : α × α => p.1 * p.2 :=
  uniformContinuous_fst.mul uniformContinuous_snd
#align uniform_continuous_mul uniformContinuous_mul
#align uniform_continuous_add uniformContinuous_add

#print UniformContinuous.pow_const /-
@[to_additive UniformContinuous.const_nsmul]
theorem UniformContinuous.pow_const [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
    ∀ n : ℕ, UniformContinuous fun x => f x ^ n
  | 0 => by
    simp_rw [pow_zero]
    exact uniformContinuous_const
  | n + 1 => by
    simp_rw [pow_succ]
    exact hf.mul (UniformContinuous.pow_const n)
#align uniform_continuous.pow_const UniformContinuous.pow_const
#align uniform_continuous.const_nsmul UniformContinuous.const_nsmul
-/

#print uniformContinuous_pow_const /-
@[to_additive uniformContinuous_const_nsmul]
theorem uniformContinuous_pow_const (n : ℕ) : UniformContinuous fun x : α => x ^ n :=
  uniformContinuous_id.pow_const n
#align uniform_continuous_pow_const uniformContinuous_pow_const
#align uniform_continuous_const_nsmul uniformContinuous_const_nsmul
-/

#print UniformContinuous.zpow_const /-
@[to_additive UniformContinuous.const_zsmul]
theorem UniformContinuous.zpow_const [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
    ∀ n : ℤ, UniformContinuous fun x => f x ^ n
  | (n : ℕ) => by
    simp_rw [zpow_ofNat]
    exact hf.pow_const _
  | -[n+1] => by
    simp_rw [zpow_negSucc]
    exact (hf.pow_const _).inv
#align uniform_continuous.zpow_const UniformContinuous.zpow_const
#align uniform_continuous.const_zsmul UniformContinuous.const_zsmul
-/

#print uniformContinuous_zpow_const /-
@[to_additive uniformContinuous_const_zsmul]
theorem uniformContinuous_zpow_const (n : ℤ) : UniformContinuous fun x : α => x ^ n :=
  uniformContinuous_id.zpow_const n
#align uniform_continuous_zpow_const uniformContinuous_zpow_const
#align uniform_continuous_const_zsmul uniformContinuous_const_zsmul
-/

#print UniformGroup.to_topologicalGroup /-
@[to_additive]
instance (priority := 10) UniformGroup.to_topologicalGroup : TopologicalGroup α
    where
  continuous_mul := uniformContinuous_mul.Continuous
  continuous_inv := uniformContinuous_inv.Continuous
#align uniform_group.to_topological_group UniformGroup.to_topologicalGroup
#align uniform_add_group.to_topological_add_group UniformAddGroup.to_topologicalAddGroup
-/

@[to_additive]
instance [UniformSpace β] [Group β] [UniformGroup β] : UniformGroup (α × β) :=
  ⟨((uniformContinuous_fst.comp uniformContinuous_fst).div
          (uniformContinuous_fst.comp uniformContinuous_snd)).prod_mk
      ((uniformContinuous_snd.comp uniformContinuous_fst).div
        (uniformContinuous_snd.comp uniformContinuous_snd))⟩

/- warning: uniformity_translate_mul -> uniformity_translate_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] (a : α), Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.map.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Prod.mk.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (Prod.fst.{u1, u1} α α x) a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (Prod.snd.{u1, u1} α α x) a)) (uniformity.{u1} α _inst_1)) (uniformity.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] (a : α), Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.map.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Prod.mk.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (Prod.fst.{u1, u1} α α x) a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (Prod.snd.{u1, u1} α α x) a)) (uniformity.{u1} α _inst_1)) (uniformity.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align uniformity_translate_mul uniformity_translate_mulₓ'. -/
@[to_additive]
theorem uniformity_translate_mul (a : α) : ((𝓤 α).map fun x : α × α => (x.1 * a, x.2 * a)) = 𝓤 α :=
  le_antisymm (uniformContinuous_id.mul uniformContinuous_const)
    (calc
      𝓤 α =
          ((𝓤 α).map fun x : α × α => (x.1 * a⁻¹, x.2 * a⁻¹)).map fun x : α × α =>
            (x.1 * a, x.2 * a) :=
        by simp [Filter.map_map, (· ∘ ·)] <;> exact filter.map_id.symm
      _ ≤ (𝓤 α).map fun x : α × α => (x.1 * a, x.2 * a) :=
        Filter.map_mono (uniformContinuous_id.mul uniformContinuous_const)
      )
#align uniformity_translate_mul uniformity_translate_mul
#align uniformity_translate_add uniformity_translate_add

/- warning: uniform_embedding_translate_mul -> uniformEmbedding_translate_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] (a : α), UniformEmbedding.{u1, u1} α α _inst_1 _inst_1 (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) x a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] (a : α), UniformEmbedding.{u1, u1} α α _inst_1 _inst_1 (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) x a)
Case conversion may be inaccurate. Consider using '#align uniform_embedding_translate_mul uniformEmbedding_translate_mulₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:132:4: warning: unsupported: rw with cfg: { occs := occurrences.pos[occurrences.pos] «expr[ ,]»([1]) } -/
@[to_additive]
theorem uniformEmbedding_translate_mul (a : α) : UniformEmbedding fun x : α => x * a :=
  { comap_uniformity := by
      rw [← uniformity_translate_mul a, comap_map]
      rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
      simp (config := { contextual := true }) [Prod.eq_iff_fst_eq_snd_eq]
    inj := mul_left_injective a }
#align uniform_embedding_translate_mul uniformEmbedding_translate_mul
#align uniform_embedding_translate_add uniformEmbedding_translate_add

namespace MulOpposite

@[to_additive]
instance : UniformGroup αᵐᵒᵖ :=
  ⟨uniformContinuous_op.comp
      ((uniformContinuous_unop.comp uniformContinuous_snd).inv.mul <|
        uniformContinuous_unop.comp uniformContinuous_fst)⟩

end MulOpposite

namespace Subgroup

@[to_additive]
instance (S : Subgroup α) : UniformGroup S :=
  ⟨uniformContinuous_comap'
      (uniformContinuous_div.comp <|
        uniformContinuous_subtype_val.Prod_map uniformContinuous_subtype_val)⟩

end Subgroup

section LatticeOps

variable [Group β]

/- warning: uniform_group_Inf -> uniformGroup_infₛ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_4 : Group.{u1} β] {us : Set.{u1} (UniformSpace.{u1} β)}, (forall (u : UniformSpace.{u1} β), (Membership.Mem.{u1, u1} (UniformSpace.{u1} β) (Set.{u1} (UniformSpace.{u1} β)) (Set.hasMem.{u1} (UniformSpace.{u1} β)) u us) -> (UniformGroup.{u1} β u _inst_4)) -> (UniformGroup.{u1} β (InfSet.infₛ.{u1} (UniformSpace.{u1} β) (UniformSpace.hasInf.{u1} β) us) _inst_4)
but is expected to have type
  forall {β : Type.{u1}} [_inst_4 : Group.{u1} β] {us : Set.{u1} (UniformSpace.{u1} β)}, (forall (u : UniformSpace.{u1} β), (Membership.mem.{u1, u1} (UniformSpace.{u1} β) (Set.{u1} (UniformSpace.{u1} β)) (Set.instMembershipSet.{u1} (UniformSpace.{u1} β)) u us) -> (UniformGroup.{u1} β u _inst_4)) -> (UniformGroup.{u1} β (InfSet.infₛ.{u1} (UniformSpace.{u1} β) (instInfSetUniformSpace.{u1} β) us) _inst_4)
Case conversion may be inaccurate. Consider using '#align uniform_group_Inf uniformGroup_infₛₓ'. -/
@[to_additive]
theorem uniformGroup_infₛ {us : Set (UniformSpace β)} (h : ∀ u ∈ us, @UniformGroup β u _) :
    @UniformGroup β (infₛ us) _ :=
  {
    uniformContinuous_div :=
      uniformContinuous_infₛ_rng fun u hu =>
        uniformContinuous_infₛ_dom₂ hu hu (@UniformGroup.uniformContinuous_div β u _ (h u hu)) }
#align uniform_group_Inf uniformGroup_infₛ
#align uniform_add_group_Inf uniformAddGroup_infₛ

/- warning: uniform_group_infi -> uniformGroup_infᵢ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_4 : Group.{u1} β] {ι : Sort.{u2}} {us' : ι -> (UniformSpace.{u1} β)}, (forall (i : ι), UniformGroup.{u1} β (us' i) _inst_4) -> (UniformGroup.{u1} β (infᵢ.{u1, u2} (UniformSpace.{u1} β) (UniformSpace.hasInf.{u1} β) ι (fun (i : ι) => us' i)) _inst_4)
but is expected to have type
  forall {β : Type.{u1}} [_inst_4 : Group.{u1} β] {ι : Sort.{u2}} {us' : ι -> (UniformSpace.{u1} β)}, (forall (i : ι), UniformGroup.{u1} β (us' i) _inst_4) -> (UniformGroup.{u1} β (infᵢ.{u1, u2} (UniformSpace.{u1} β) (instInfSetUniformSpace.{u1} β) ι (fun (i : ι) => us' i)) _inst_4)
Case conversion may be inaccurate. Consider using '#align uniform_group_infi uniformGroup_infᵢₓ'. -/
@[to_additive]
theorem uniformGroup_infᵢ {ι : Sort _} {us' : ι → UniformSpace β}
    (h' : ∀ i, @UniformGroup β (us' i) _) : @UniformGroup β (⨅ i, us' i) _ :=
  by
  rw [← infₛ_range]
  exact uniformGroup_infₛ (set.forall_range_iff.mpr h')
#align uniform_group_infi uniformGroup_infᵢ
#align uniform_add_group_infi uniformAddGroup_infᵢ

#print uniformGroup_inf /-
@[to_additive]
theorem uniformGroup_inf {u₁ u₂ : UniformSpace β} (h₁ : @UniformGroup β u₁ _)
    (h₂ : @UniformGroup β u₂ _) : @UniformGroup β (u₁ ⊓ u₂) _ :=
  by
  rw [inf_eq_infᵢ]
  refine' uniformGroup_infᵢ fun b => _
  cases b <;> assumption
#align uniform_group_inf uniformGroup_inf
#align uniform_add_group_inf uniformAddGroup_inf
-/

/- warning: uniform_group_comap -> uniformGroup_comap is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_4 : Group.{u1} β] {γ : Type.{u2}} [_inst_5 : Group.{u2} γ] {u : UniformSpace.{u2} γ} [_inst_6 : UniformGroup.{u2} γ u _inst_5] {F : Type.{u3}} [_inst_7 : MonoidHomClass.{u3, u1, u2} F β γ (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (Group.toDivInvMonoid.{u1} β _inst_4))) (Monoid.toMulOneClass.{u2} γ (DivInvMonoid.toMonoid.{u2} γ (Group.toDivInvMonoid.{u2} γ _inst_5)))] (f : F), UniformGroup.{u1} β (UniformSpace.comap.{u1, u2} β γ (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => β -> γ) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F β (fun (_x : β) => γ) (MulHomClass.toFunLike.{u3, u1, u2} F β γ (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (Group.toDivInvMonoid.{u1} β _inst_4)))) (MulOneClass.toHasMul.{u2} γ (Monoid.toMulOneClass.{u2} γ (DivInvMonoid.toMonoid.{u2} γ (Group.toDivInvMonoid.{u2} γ _inst_5)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F β γ (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (Group.toDivInvMonoid.{u1} β _inst_4))) (Monoid.toMulOneClass.{u2} γ (DivInvMonoid.toMonoid.{u2} γ (Group.toDivInvMonoid.{u2} γ _inst_5))) _inst_7))) f) u) _inst_4
but is expected to have type
  forall {β : Type.{u1}} [_inst_4 : Group.{u1} β] {γ : Type.{u3}} [_inst_5 : Group.{u3} γ] {u : UniformSpace.{u3} γ} [_inst_6 : UniformGroup.{u3} γ u _inst_5] {F : Type.{u2}} [_inst_7 : MonoidHomClass.{u2, u1, u3} F β γ (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (Group.toDivInvMonoid.{u1} β _inst_4))) (Monoid.toMulOneClass.{u3} γ (DivInvMonoid.toMonoid.{u3} γ (Group.toDivInvMonoid.{u3} γ _inst_5)))] (f : F), UniformGroup.{u1} β (UniformSpace.comap.{u1, u3} β γ (FunLike.coe.{succ u2, succ u1, succ u3} F β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : β) => γ) _x) (MulHomClass.toFunLike.{u2, u1, u3} F β γ (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (Group.toDivInvMonoid.{u1} β _inst_4)))) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (DivInvMonoid.toMonoid.{u3} γ (Group.toDivInvMonoid.{u3} γ _inst_5)))) (MonoidHomClass.toMulHomClass.{u2, u1, u3} F β γ (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (Group.toDivInvMonoid.{u1} β _inst_4))) (Monoid.toMulOneClass.{u3} γ (DivInvMonoid.toMonoid.{u3} γ (Group.toDivInvMonoid.{u3} γ _inst_5))) _inst_7)) f) u) _inst_4
Case conversion may be inaccurate. Consider using '#align uniform_group_comap uniformGroup_comapₓ'. -/
@[to_additive]
theorem uniformGroup_comap {γ : Type _} [Group γ] {u : UniformSpace γ} [UniformGroup γ] {F : Type _}
    [MonoidHomClass F β γ] (f : F) : @UniformGroup β (u.comap f) _ :=
  {
    uniformContinuous_div := by
      letI : UniformSpace β := u.comap f
      refine' uniformContinuous_comap' _
      simp_rw [Function.comp, map_div]
      change UniformContinuous ((fun p : γ × γ => p.1 / p.2) ∘ Prod.map f f)
      exact
        uniform_continuous_div.comp (uniform_continuous_comap.prod_map uniformContinuous_comap) }
#align uniform_group_comap uniformGroup_comap
#align uniform_add_group_comap uniformAddGroup_comap

end LatticeOps

section

variable (α)

/- warning: uniformity_eq_comap_nhds_one -> uniformity_eq_comap_nhds_one is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (Filter.comap.{u1, u1} (Prod.{u1, u1} α α) α (fun (x : Prod.{u1, u1} α α) => HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Prod.snd.{u1, u1} α α x) (Prod.fst.{u1, u1} α α x)) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (Filter.comap.{u1, u1} (Prod.{u1, u1} α α) α (fun (x : Prod.{u1, u1} α α) => HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Prod.snd.{u1, u1} α α x) (Prod.fst.{u1, u1} α α x)) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align uniformity_eq_comap_nhds_one uniformity_eq_comap_nhds_oneₓ'. -/
@[to_additive]
theorem uniformity_eq_comap_nhds_one : 𝓤 α = comap (fun x : α × α => x.2 / x.1) (𝓝 (1 : α)) :=
  by
  rw [nhds_eq_comap_uniformity, Filter.comap_comap]
  refine' le_antisymm (Filter.map_le_iff_le_comap.1 _) _
  · intro s hs
    rcases mem_uniformity_of_uniformContinuous_invariant uniformContinuous_div hs with ⟨t, ht, hts⟩
    refine' mem_map.2 (mem_of_superset ht _)
    rintro ⟨a, b⟩
    simpa [subset_def] using hts a b a
  · intro s hs
    rcases mem_uniformity_of_uniformContinuous_invariant uniformContinuous_mul hs with ⟨t, ht, hts⟩
    refine' ⟨_, ht, _⟩
    rintro ⟨a, b⟩
    simpa [subset_def] using hts 1 (b / a) a
#align uniformity_eq_comap_nhds_one uniformity_eq_comap_nhds_one
#align uniformity_eq_comap_nhds_zero uniformity_eq_comap_nhds_zero

/- warning: uniformity_eq_comap_nhds_one_swapped -> uniformity_eq_comap_nhds_one_swapped is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (Filter.comap.{u1, u1} (Prod.{u1, u1} α α) α (fun (x : Prod.{u1, u1} α α) => HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Prod.fst.{u1, u1} α α x) (Prod.snd.{u1, u1} α α x)) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (Filter.comap.{u1, u1} (Prod.{u1, u1} α α) α (fun (x : Prod.{u1, u1} α α) => HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Prod.fst.{u1, u1} α α x) (Prod.snd.{u1, u1} α α x)) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align uniformity_eq_comap_nhds_one_swapped uniformity_eq_comap_nhds_one_swappedₓ'. -/
@[to_additive]
theorem uniformity_eq_comap_nhds_one_swapped :
    𝓤 α = comap (fun x : α × α => x.1 / x.2) (𝓝 (1 : α)) :=
  by
  rw [← comap_swap_uniformity, uniformity_eq_comap_nhds_one, comap_comap, (· ∘ ·)]
  rfl
#align uniformity_eq_comap_nhds_one_swapped uniformity_eq_comap_nhds_one_swapped
#align uniformity_eq_comap_nhds_zero_swapped uniformity_eq_comap_nhds_zero_swapped

/- warning: uniform_group.ext -> UniformGroup.ext is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_4 : Group.{u1} G] {u : UniformSpace.{u1} G} {v : UniformSpace.{u1} G}, (UniformGroup.{u1} G u _inst_4) -> (UniformGroup.{u1} G v _inst_4) -> (Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G (UniformSpace.toTopologicalSpace.{u1} G u) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)))))))) (nhds.{u1} G (UniformSpace.toTopologicalSpace.{u1} G v) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))))))) -> (Eq.{succ u1} (UniformSpace.{u1} G) u v)
but is expected to have type
  forall {G : Type.{u1}} [_inst_4 : Group.{u1} G] {u : UniformSpace.{u1} G} {v : UniformSpace.{u1} G}, (UniformGroup.{u1} G u _inst_4) -> (UniformGroup.{u1} G v _inst_4) -> (Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G (UniformSpace.toTopologicalSpace.{u1} G u) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_4))))))) (nhds.{u1} G (UniformSpace.toTopologicalSpace.{u1} G v) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_4)))))))) -> (Eq.{succ u1} (UniformSpace.{u1} G) u v)
Case conversion may be inaccurate. Consider using '#align uniform_group.ext UniformGroup.extₓ'. -/
@[to_additive]
theorem UniformGroup.ext {G : Type _} [Group G] {u v : UniformSpace G} (hu : @UniformGroup G u _)
    (hv : @UniformGroup G v _)
    (h : @nhds _ u.toTopologicalSpace 1 = @nhds _ v.toTopologicalSpace 1) : u = v :=
  uniformSpace_eq <| by
    rw [@uniformity_eq_comap_nhds_one _ u _ hu, @uniformity_eq_comap_nhds_one _ v _ hv, h]
#align uniform_group.ext UniformGroup.ext
#align uniform_add_group.ext UniformAddGroup.ext

/- warning: uniform_group.ext_iff -> UniformGroup.ext_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_4 : Group.{u1} G] {u : UniformSpace.{u1} G} {v : UniformSpace.{u1} G}, (UniformGroup.{u1} G u _inst_4) -> (UniformGroup.{u1} G v _inst_4) -> (Iff (Eq.{succ u1} (UniformSpace.{u1} G) u v) (Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G (UniformSpace.toTopologicalSpace.{u1} G u) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)))))))) (nhds.{u1} G (UniformSpace.toTopologicalSpace.{u1} G v) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_4 : Group.{u1} G] {u : UniformSpace.{u1} G} {v : UniformSpace.{u1} G}, (UniformGroup.{u1} G u _inst_4) -> (UniformGroup.{u1} G v _inst_4) -> (Iff (Eq.{succ u1} (UniformSpace.{u1} G) u v) (Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G (UniformSpace.toTopologicalSpace.{u1} G u) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_4))))))) (nhds.{u1} G (UniformSpace.toTopologicalSpace.{u1} G v) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_4)))))))))
Case conversion may be inaccurate. Consider using '#align uniform_group.ext_iff UniformGroup.ext_iffₓ'. -/
@[to_additive]
theorem UniformGroup.ext_iff {G : Type _} [Group G] {u v : UniformSpace G}
    (hu : @UniformGroup G u _) (hv : @UniformGroup G v _) :
    u = v ↔ @nhds _ u.toTopologicalSpace 1 = @nhds _ v.toTopologicalSpace 1 :=
  ⟨fun h => h ▸ rfl, hu.ext hv⟩
#align uniform_group.ext_iff UniformGroup.ext_iff
#align uniform_add_group.ext_iff UniformAddGroup.ext_iff

variable {α}

/- warning: uniform_group.uniformity_countably_generated -> UniformGroup.uniformity_countably_generated is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] [_inst_4 : Filter.IsCountablyGenerated.{u1} α (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))))))], Filter.IsCountablyGenerated.{u1} (Prod.{u1, u1} α α) (uniformity.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] [_inst_4 : Filter.IsCountablyGenerated.{u1} α (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2)))))))], Filter.IsCountablyGenerated.{u1} (Prod.{u1, u1} α α) (uniformity.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align uniform_group.uniformity_countably_generated UniformGroup.uniformity_countably_generatedₓ'. -/
@[to_additive]
theorem UniformGroup.uniformity_countably_generated [(𝓝 (1 : α)).IsCountablyGenerated] :
    (𝓤 α).IsCountablyGenerated :=
  by
  rw [uniformity_eq_comap_nhds_one]
  exact Filter.comap.isCountablyGenerated _ _
#align uniform_group.uniformity_countably_generated UniformGroup.uniformity_countably_generated
#align uniform_add_group.uniformity_countably_generated UniformAddGroup.uniformity_countably_generated

open MulOpposite

/- warning: uniformity_eq_comap_inv_mul_nhds_one -> uniformity_eq_comap_inv_mul_nhds_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (Filter.comap.{u1, u1} (Prod.{u1, u1} α α) α (fun (x : Prod.{u1, u1} α α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) (Prod.fst.{u1, u1} α α x)) (Prod.snd.{u1, u1} α α x)) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (Filter.comap.{u1, u1} (Prod.{u1, u1} α α) α (fun (x : Prod.{u1, u1} α α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2)))) (Prod.fst.{u1, u1} α α x)) (Prod.snd.{u1, u1} α α x)) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align uniformity_eq_comap_inv_mul_nhds_one uniformity_eq_comap_inv_mul_nhds_oneₓ'. -/
@[to_additive]
theorem uniformity_eq_comap_inv_mul_nhds_one :
    𝓤 α = comap (fun x : α × α => x.1⁻¹ * x.2) (𝓝 (1 : α)) :=
  by
  rw [← comap_uniformity_mulOpposite, uniformity_eq_comap_nhds_one, ← op_one, ← comap_unop_nhds,
    comap_comap, comap_comap]
  simp [(· ∘ ·)]
#align uniformity_eq_comap_inv_mul_nhds_one uniformity_eq_comap_inv_mul_nhds_one
#align uniformity_eq_comap_neg_add_nhds_zero uniformity_eq_comap_neg_add_nhds_zero

/- warning: uniformity_eq_comap_inv_mul_nhds_one_swapped -> uniformity_eq_comap_inv_mul_nhds_one_swapped is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (Filter.comap.{u1, u1} (Prod.{u1, u1} α α) α (fun (x : Prod.{u1, u1} α α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) (Prod.snd.{u1, u1} α α x)) (Prod.fst.{u1, u1} α α x)) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (Filter.comap.{u1, u1} (Prod.{u1, u1} α α) α (fun (x : Prod.{u1, u1} α α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2)))) (Prod.snd.{u1, u1} α α x)) (Prod.fst.{u1, u1} α α x)) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align uniformity_eq_comap_inv_mul_nhds_one_swapped uniformity_eq_comap_inv_mul_nhds_one_swappedₓ'. -/
@[to_additive]
theorem uniformity_eq_comap_inv_mul_nhds_one_swapped :
    𝓤 α = comap (fun x : α × α => x.2⁻¹ * x.1) (𝓝 (1 : α)) :=
  by
  rw [← comap_swap_uniformity, uniformity_eq_comap_inv_mul_nhds_one, comap_comap, (· ∘ ·)]
  rfl
#align uniformity_eq_comap_inv_mul_nhds_one_swapped uniformity_eq_comap_inv_mul_nhds_one_swapped
#align uniformity_eq_comap_neg_add_nhds_zero_swapped uniformity_eq_comap_neg_add_nhds_zero_swapped

end

/- warning: filter.has_basis.uniformity_of_nhds_one -> Filter.HasBasis.uniformity_of_nhds_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Sort.{u2}} {p : ι -> Prop} {U : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))))) p U) -> (Filter.HasBasis.{u1, u2} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p (fun (i : ι) => setOf.{u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Prod.snd.{u1, u1} α α x) (Prod.fst.{u1, u1} α α x)) (U i))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Sort.{u2}} {p : ι -> Prop} {U : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2))))))) p U) -> (Filter.HasBasis.{u1, u2} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p (fun (i : ι) => setOf.{u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Prod.snd.{u1, u1} α α x) (Prod.fst.{u1, u1} α α x)) (U i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.uniformity_of_nhds_one Filter.HasBasis.uniformity_of_nhds_oneₓ'. -/
@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) : (𝓤 α).HasBasis p fun i => { x : α × α | x.2 / x.1 ∈ U i } :=
  by
  rw [uniformity_eq_comap_nhds_one]
  exact h.comap _
#align filter.has_basis.uniformity_of_nhds_one Filter.HasBasis.uniformity_of_nhds_one
#align filter.has_basis.uniformity_of_nhds_zero Filter.HasBasis.uniformity_of_nhds_zero

/- warning: filter.has_basis.uniformity_of_nhds_one_inv_mul -> Filter.HasBasis.uniformity_of_nhds_one_inv_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Sort.{u2}} {p : ι -> Prop} {U : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))))) p U) -> (Filter.HasBasis.{u1, u2} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p (fun (i : ι) => setOf.{u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) (Prod.fst.{u1, u1} α α x)) (Prod.snd.{u1, u1} α α x)) (U i))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Sort.{u2}} {p : ι -> Prop} {U : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2))))))) p U) -> (Filter.HasBasis.{u1, u2} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p (fun (i : ι) => setOf.{u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2)))) (Prod.fst.{u1, u1} α α x)) (Prod.snd.{u1, u1} α α x)) (U i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.uniformity_of_nhds_one_inv_mul Filter.HasBasis.uniformity_of_nhds_one_inv_mulₓ'. -/
@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_inv_mul {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) : (𝓤 α).HasBasis p fun i => { x : α × α | x.1⁻¹ * x.2 ∈ U i } :=
  by
  rw [uniformity_eq_comap_inv_mul_nhds_one]
  exact h.comap _
#align filter.has_basis.uniformity_of_nhds_one_inv_mul Filter.HasBasis.uniformity_of_nhds_one_inv_mul
#align filter.has_basis.uniformity_of_nhds_zero_neg_add Filter.HasBasis.uniformity_of_nhds_zero_neg_add

/- warning: filter.has_basis.uniformity_of_nhds_one_swapped -> Filter.HasBasis.uniformity_of_nhds_one_swapped is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Sort.{u2}} {p : ι -> Prop} {U : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))))) p U) -> (Filter.HasBasis.{u1, u2} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p (fun (i : ι) => setOf.{u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Prod.fst.{u1, u1} α α x) (Prod.snd.{u1, u1} α α x)) (U i))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Sort.{u2}} {p : ι -> Prop} {U : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2))))))) p U) -> (Filter.HasBasis.{u1, u2} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p (fun (i : ι) => setOf.{u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Prod.fst.{u1, u1} α α x) (Prod.snd.{u1, u1} α α x)) (U i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.uniformity_of_nhds_one_swapped Filter.HasBasis.uniformity_of_nhds_one_swappedₓ'. -/
@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_swapped {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) : (𝓤 α).HasBasis p fun i => { x : α × α | x.1 / x.2 ∈ U i } :=
  by
  rw [uniformity_eq_comap_nhds_one_swapped]
  exact h.comap _
#align filter.has_basis.uniformity_of_nhds_one_swapped Filter.HasBasis.uniformity_of_nhds_one_swapped
#align filter.has_basis.uniformity_of_nhds_zero_swapped Filter.HasBasis.uniformity_of_nhds_zero_swapped

/- warning: filter.has_basis.uniformity_of_nhds_one_inv_mul_swapped -> Filter.HasBasis.uniformity_of_nhds_one_inv_mul_swapped is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Sort.{u2}} {p : ι -> Prop} {U : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))))) p U) -> (Filter.HasBasis.{u1, u2} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p (fun (i : ι) => setOf.{u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) (Prod.snd.{u1, u1} α α x)) (Prod.fst.{u1, u1} α α x)) (U i))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Sort.{u2}} {p : ι -> Prop} {U : ι -> (Set.{u1} α)}, (Filter.HasBasis.{u1, u2} α ι (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2))))))) p U) -> (Filter.HasBasis.{u1, u2} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p (fun (i : ι) => setOf.{u1} (Prod.{u1, u1} α α) (fun (x : Prod.{u1, u1} α α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2)))) (Prod.snd.{u1, u1} α α x)) (Prod.fst.{u1, u1} α α x)) (U i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.uniformity_of_nhds_one_inv_mul_swapped Filter.HasBasis.uniformity_of_nhds_one_inv_mul_swappedₓ'. -/
@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_inv_mul_swapped {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) : (𝓤 α).HasBasis p fun i => { x : α × α | x.2⁻¹ * x.1 ∈ U i } :=
  by
  rw [uniformity_eq_comap_inv_mul_nhds_one_swapped]
  exact h.comap _
#align filter.has_basis.uniformity_of_nhds_one_inv_mul_swapped Filter.HasBasis.uniformity_of_nhds_one_inv_mul_swapped
#align filter.has_basis.uniformity_of_nhds_zero_neg_add_swapped Filter.HasBasis.uniformity_of_nhds_zero_neg_add_swapped

/- warning: group_separation_rel -> group_separationRel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] (x : α) (y : α), Iff (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) (separationRel.{u1} α _inst_1)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) x y) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] (x : α) (y : α), Iff (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) (separationRel.{u1} α _inst_1)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) x y) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2)))))))))
Case conversion may be inaccurate. Consider using '#align group_separation_rel group_separationRelₓ'. -/
@[to_additive]
theorem group_separationRel (x y : α) : (x, y) ∈ separationRel α ↔ x / y ∈ closure ({1} : Set α) :=
  have : Embedding fun a => a * (y / x) := (uniformEmbedding_translate_mul (y / x)).Embedding
  show (x, y) ∈ ⋂₀ (𝓤 α).sets ↔ x / y ∈ closure ({1} : Set α)
    by
    rw [this.closure_eq_preimage_closure_image, uniformity_eq_comap_nhds_one α, sInter_comap_sets]
    simp [mem_closure_iff_nhds, inter_singleton_nonempty, sub_eq_add_neg, add_assoc]
#align group_separation_rel group_separationRel
#align add_group_separation_rel addGroup_separationRel

/- warning: uniform_continuous_of_tendsto_one -> uniformContinuous_of_tendsto_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {hom : Type.{u3}} [_inst_4 : UniformSpace.{u2} β] [_inst_5 : Group.{u2} β] [_inst_6 : UniformGroup.{u2} β _inst_4 _inst_5] [_inst_7 : MonoidHomClass.{u3, u1, u2} hom α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))] {f : hom}, (Filter.Tendsto.{u1, u2} α β (coeFn.{succ u3, max (succ u1) (succ u2)} hom (fun (_x : hom) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} hom α (fun (_x : α) => β) (MulHomClass.toFunLike.{u3, u1, u2} hom α β (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} hom α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5))) _inst_7))) f) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))))) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β _inst_4) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5))))))))) -> (UniformContinuous.{u1, u2} α β _inst_1 _inst_4 (coeFn.{succ u3, max (succ u1) (succ u2)} hom (fun (_x : hom) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} hom α (fun (_x : α) => β) (MulHomClass.toFunLike.{u3, u1, u2} hom α β (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} hom α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5))) _inst_7))) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {hom : Type.{u3}} [_inst_4 : UniformSpace.{u2} β] [_inst_5 : Group.{u2} β] [_inst_6 : UniformGroup.{u2} β _inst_4 _inst_5] [_inst_7 : MonoidHomClass.{u3, u1, u2} hom α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))] {f : hom}, (Filter.Tendsto.{u1, u2} α β (FunLike.coe.{succ u3, succ u1, succ u2} hom α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : α) => β) _x) (MulHomClass.toFunLike.{u3, u1, u2} hom α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} hom α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5))) _inst_7)) f) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2))))))) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β _inst_4) (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β (InvOneClass.toOne.{u2} β (DivInvOneMonoid.toInvOneClass.{u2} β (DivisionMonoid.toDivInvOneMonoid.{u2} β (Group.toDivisionMonoid.{u2} β _inst_5)))))))) -> (UniformContinuous.{u1, u2} α β _inst_1 _inst_4 (FunLike.coe.{succ u3, succ u1, succ u2} hom α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : α) => β) _x) (MulHomClass.toFunLike.{u3, u1, u2} hom α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} hom α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5))) _inst_7)) f))
Case conversion may be inaccurate. Consider using '#align uniform_continuous_of_tendsto_one uniformContinuous_of_tendsto_oneₓ'. -/
@[to_additive]
theorem uniformContinuous_of_tendsto_one {hom : Type _} [UniformSpace β] [Group β] [UniformGroup β]
    [MonoidHomClass hom α β] {f : hom} (h : Tendsto f (𝓝 1) (𝓝 1)) : UniformContinuous f :=
  by
  have :
    ((fun x : β × β => x.2 / x.1) ∘ fun x : α × α => (f x.1, f x.2)) = fun x : α × α =>
      f (x.2 / x.1) :=
    by simp only [map_div]
  rw [UniformContinuous, uniformity_eq_comap_nhds_one α, uniformity_eq_comap_nhds_one β,
    tendsto_comap_iff, this]
  exact tendsto.comp h tendsto_comap
#align uniform_continuous_of_tendsto_one uniformContinuous_of_tendsto_one
#align uniform_continuous_of_tendsto_zero uniformContinuous_of_tendsto_zero

/- warning: uniform_continuous_of_continuous_at_one -> uniformContinuous_of_continuousAt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {hom : Type.{u3}} [_inst_4 : UniformSpace.{u2} β] [_inst_5 : Group.{u2} β] [_inst_6 : UniformGroup.{u2} β _inst_4 _inst_5] [_inst_7 : MonoidHomClass.{u3, u1, u2} hom α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))] (f : hom), (ContinuousAt.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} β _inst_4) (coeFn.{succ u3, max (succ u1) (succ u2)} hom (fun (_x : hom) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} hom α (fun (_x : α) => β) (MulHomClass.toFunLike.{u3, u1, u2} hom α β (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} hom α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5))) _inst_7))) f) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))))) -> (UniformContinuous.{u1, u2} α β _inst_1 _inst_4 (coeFn.{succ u3, max (succ u1) (succ u2)} hom (fun (_x : hom) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} hom α (fun (_x : α) => β) (MulHomClass.toFunLike.{u3, u1, u2} hom α β (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} hom α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5))) _inst_7))) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {hom : Type.{u3}} [_inst_4 : UniformSpace.{u2} β] [_inst_5 : Group.{u2} β] [_inst_6 : UniformGroup.{u2} β _inst_4 _inst_5] [_inst_7 : MonoidHomClass.{u3, u1, u2} hom α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))] (f : hom), (ContinuousAt.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} β _inst_4) (FunLike.coe.{succ u3, succ u1, succ u2} hom α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : α) => β) _x) (MulHomClass.toFunLike.{u3, u1, u2} hom α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} hom α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5))) _inst_7)) f) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2))))))) -> (UniformContinuous.{u1, u2} α β _inst_1 _inst_4 (FunLike.coe.{succ u3, succ u1, succ u2} hom α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : α) => β) _x) (MulHomClass.toFunLike.{u3, u1, u2} hom α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} hom α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5))) _inst_7)) f))
Case conversion may be inaccurate. Consider using '#align uniform_continuous_of_continuous_at_one uniformContinuous_of_continuousAt_oneₓ'. -/
/-- A group homomorphism (a bundled morphism of a type that implements `monoid_hom_class`) between
two uniform groups is uniformly continuous provided that it is continuous at one. See also
`continuous_of_continuous_at_one`. -/
@[to_additive
      "An additive group homomorphism (a bundled morphism of a type that implements\n`add_monoid_hom_class`) between two uniform additive groups is uniformly continuous provided that it\nis continuous at zero. See also `continuous_of_continuous_at_zero`."]
theorem uniformContinuous_of_continuousAt_one {hom : Type _} [UniformSpace β] [Group β]
    [UniformGroup β] [MonoidHomClass hom α β] (f : hom) (hf : ContinuousAt f 1) :
    UniformContinuous f :=
  uniformContinuous_of_tendsto_one (by simpa using hf.tendsto)
#align uniform_continuous_of_continuous_at_one uniformContinuous_of_continuousAt_one
#align uniform_continuous_of_continuous_at_zero uniformContinuous_of_continuousAt_zero

/- warning: monoid_hom.uniform_continuous_of_continuous_at_one -> MonoidHom.uniformContinuous_of_continuousAt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] [_inst_4 : UniformSpace.{u2} β] [_inst_5 : Group.{u2} β] [_inst_6 : UniformGroup.{u2} β _inst_4 _inst_5] (f : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))), (ContinuousAt.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} β _inst_4) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) (fun (_x : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) f) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))))) -> (UniformContinuous.{u1, u2} α β _inst_1 _inst_4 (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) (fun (_x : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] [_inst_4 : UniformSpace.{u2} β] [_inst_5 : Group.{u2} β] [_inst_6 : UniformGroup.{u2} β _inst_4 _inst_5] (f : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))), (ContinuousAt.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} β _inst_4) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : α) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5))) (MonoidHom.monoidHomClass.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))))) f) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2))))))) -> (UniformContinuous.{u1, u2} α β _inst_1 _inst_4 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : α) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5))) (MonoidHom.monoidHomClass.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))))) f))
Case conversion may be inaccurate. Consider using '#align monoid_hom.uniform_continuous_of_continuous_at_one MonoidHom.uniformContinuous_of_continuousAt_oneₓ'. -/
@[to_additive]
theorem MonoidHom.uniformContinuous_of_continuousAt_one [UniformSpace β] [Group β] [UniformGroup β]
    (f : α →* β) (hf : ContinuousAt f 1) : UniformContinuous f :=
  uniformContinuous_of_continuousAt_one f hf
#align monoid_hom.uniform_continuous_of_continuous_at_one MonoidHom.uniformContinuous_of_continuousAt_one
#align add_monoid_hom.uniform_continuous_of_continuous_at_zero AddMonoidHom.uniformContinuous_of_continuousAt_zero

/- warning: uniform_group.uniform_continuous_iff_open_ker -> UniformGroup.uniformContinuous_iff_open_ker is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {hom : Type.{u3}} [_inst_4 : UniformSpace.{u2} β] [_inst_5 : DiscreteTopology.{u2} β (UniformSpace.toTopologicalSpace.{u2} β _inst_4)] [_inst_6 : Group.{u2} β] [_inst_7 : UniformGroup.{u2} β _inst_4 _inst_6] [_inst_8 : MonoidHomClass.{u3, u1, u2} hom α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_6)))] {f : hom}, Iff (UniformContinuous.{u1, u2} α β _inst_1 _inst_4 (coeFn.{succ u3, max (succ u1) (succ u2)} hom (fun (_x : hom) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} hom α (fun (_x : α) => β) (MulHomClass.toFunLike.{u3, u1, u2} hom α β (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_6)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} hom α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_6))) _inst_8))) f)) (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subgroup.{u1} α _inst_2) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subgroup.{u1} α _inst_2) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subgroup.{u1} α _inst_2) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Subgroup.{u1} α _inst_2) α (Subgroup.setLike.{u1} α _inst_2)))) (MonoidHom.ker.{u1, u2} α _inst_2 β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_6))) ((fun (a : Type.{u3}) (b : Sort.{max (succ u2) (succ u1)}) [self : HasLiftT.{succ u3, max (succ u2) (succ u1)} a b] => self.0) hom (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_6)))) (HasLiftT.mk.{succ u3, max (succ u2) (succ u1)} hom (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_6)))) (CoeTCₓ.coe.{succ u3, max (succ u2) (succ u1)} hom (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_6)))) (MonoidHom.hasCoeT.{u1, u2, u3} α β hom (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_6))) _inst_8))) f))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {hom : Type.{u3}} [_inst_4 : UniformSpace.{u2} β] [_inst_5 : DiscreteTopology.{u2} β (UniformSpace.toTopologicalSpace.{u2} β _inst_4)] [_inst_6 : Group.{u2} β] [_inst_7 : UniformGroup.{u2} β _inst_4 _inst_6] [_inst_8 : MonoidHomClass.{u3, u1, u2} hom α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_6)))] {f : hom}, Iff (UniformContinuous.{u1, u2} α β _inst_1 _inst_4 (FunLike.coe.{succ u3, succ u1, succ u2} hom α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : α) => β) _x) (MulHomClass.toFunLike.{u3, u1, u2} hom α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_6)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} hom α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_6))) _inst_8)) f)) (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (SetLike.coe.{u1, u1} (Subgroup.{u1} α _inst_2) α (Subgroup.instSetLikeSubgroup.{u1} α _inst_2) (MonoidHom.ker.{u1, u2} α _inst_2 β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_6))) (MonoidHomClass.toMonoidHom.{u1, u2, u3} α β hom (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_6))) _inst_8 f))))
Case conversion may be inaccurate. Consider using '#align uniform_group.uniform_continuous_iff_open_ker UniformGroup.uniformContinuous_iff_open_kerₓ'. -/
/-- A homomorphism from a uniform group to a discrete uniform group is continuous if and only if
its kernel is open. -/
@[to_additive
      "A homomorphism from a uniform additive group to a discrete uniform additive group is\ncontinuous if and only if its kernel is open."]
theorem UniformGroup.uniformContinuous_iff_open_ker {hom : Type _} [UniformSpace β]
    [DiscreteTopology β] [Group β] [UniformGroup β] [MonoidHomClass hom α β] {f : hom} :
    UniformContinuous f ↔ IsOpen ((f : α →* β).ker : Set α) :=
  by
  refine' ⟨fun hf => _, fun hf => _⟩
  · apply (isOpen_discrete ({1} : Set β)).Preimage (UniformContinuous.continuous hf)
  · apply uniformContinuous_of_continuousAt_one
    rw [ContinuousAt, nhds_discrete β, map_one, tendsto_pure]
    exact hf.mem_nhds (map_one f)
#align uniform_group.uniform_continuous_iff_open_ker UniformGroup.uniformContinuous_iff_open_ker
#align uniform_add_group.uniform_continuous_iff_open_ker UniformAddGroup.uniformContinuous_iff_open_ker

#print uniformContinuous_monoidHom_of_continuous /-
@[to_additive]
theorem uniformContinuous_monoidHom_of_continuous {hom : Type _} [UniformSpace β] [Group β]
    [UniformGroup β] [MonoidHomClass hom α β] {f : hom} (h : Continuous f) : UniformContinuous f :=
  uniformContinuous_of_tendsto_one <|
    suffices Tendsto f (𝓝 1) (𝓝 (f 1)) by rwa [map_one] at this
    h.Tendsto 1
#align uniform_continuous_monoid_hom_of_continuous uniformContinuous_monoidHom_of_continuous
#align uniform_continuous_add_monoid_hom_of_continuous uniformContinuous_addMonoidHom_of_continuous
-/

/- warning: cauchy_seq.mul -> CauchySeq.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Type.{u2}} [_inst_4 : SemilatticeSup.{u2} ι] {u : ι -> α} {v : ι -> α}, (CauchySeq.{u1, u2} α ι _inst_1 _inst_4 u) -> (CauchySeq.{u1, u2} α ι _inst_1 _inst_4 v) -> (CauchySeq.{u1, u2} α ι _inst_1 _inst_4 (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (ι -> α) (ι -> α) (ι -> α) (instHMul.{max u2 u1} (ι -> α) (Pi.instMul.{u2, u1} ι (fun (ᾰ : ι) => α) (fun (i : ι) => MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) u v))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Type.{u2}} [_inst_4 : SemilatticeSup.{u2} ι] {u : ι -> α} {v : ι -> α}, (CauchySeq.{u1, u2} α ι _inst_1 _inst_4 u) -> (CauchySeq.{u1, u2} α ι _inst_1 _inst_4 v) -> (CauchySeq.{u1, u2} α ι _inst_1 _inst_4 (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (ι -> α) (ι -> α) (ι -> α) (instHMul.{max u1 u2} (ι -> α) (Pi.instMul.{u2, u1} ι (fun (ᾰ : ι) => α) (fun (i : ι) => MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) u v))
Case conversion may be inaccurate. Consider using '#align cauchy_seq.mul CauchySeq.mulₓ'. -/
@[to_additive]
theorem CauchySeq.mul {ι : Type _} [SemilatticeSup ι] {u v : ι → α} (hu : CauchySeq u)
    (hv : CauchySeq v) : CauchySeq (u * v) :=
  uniformContinuous_mul.comp_cauchySeq (hu.Prod hv)
#align cauchy_seq.mul CauchySeq.mul
#align cauchy_seq.add CauchySeq.add

/- warning: cauchy_seq.mul_const -> CauchySeq.mul_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Type.{u2}} [_inst_4 : SemilatticeSup.{u2} ι] {u : ι -> α} {x : α}, (CauchySeq.{u1, u2} α ι _inst_1 _inst_4 u) -> (CauchySeq.{u1, u2} α ι _inst_1 _inst_4 (fun (n : ι) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (u n) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Type.{u2}} [_inst_4 : SemilatticeSup.{u2} ι] {u : ι -> α} {x : α}, (CauchySeq.{u1, u2} α ι _inst_1 _inst_4 u) -> (CauchySeq.{u1, u2} α ι _inst_1 _inst_4 (fun (n : ι) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) (u n) x))
Case conversion may be inaccurate. Consider using '#align cauchy_seq.mul_const CauchySeq.mul_constₓ'. -/
@[to_additive]
theorem CauchySeq.mul_const {ι : Type _} [SemilatticeSup ι] {u : ι → α} {x : α} (hu : CauchySeq u) :
    CauchySeq fun n => u n * x :=
  (uniformContinuous_id.mul uniformContinuous_const).comp_cauchySeq hu
#align cauchy_seq.mul_const CauchySeq.mul_const
#align cauchy_seq.add_const CauchySeq.add_const

/- warning: cauchy_seq.const_mul -> CauchySeq.const_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Type.{u2}} [_inst_4 : SemilatticeSup.{u2} ι] {u : ι -> α} {x : α}, (CauchySeq.{u1, u2} α ι _inst_1 _inst_4 u) -> (CauchySeq.{u1, u2} α ι _inst_1 _inst_4 (fun (n : ι) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) x (u n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Type.{u2}} [_inst_4 : SemilatticeSup.{u2} ι] {u : ι -> α} {x : α}, (CauchySeq.{u1, u2} α ι _inst_1 _inst_4 u) -> (CauchySeq.{u1, u2} α ι _inst_1 _inst_4 (fun (n : ι) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) x (u n)))
Case conversion may be inaccurate. Consider using '#align cauchy_seq.const_mul CauchySeq.const_mulₓ'. -/
@[to_additive]
theorem CauchySeq.const_mul {ι : Type _} [SemilatticeSup ι] {u : ι → α} {x : α} (hu : CauchySeq u) :
    CauchySeq fun n => x * u n :=
  (uniformContinuous_const.mul uniformContinuous_id).comp_cauchySeq hu
#align cauchy_seq.const_mul CauchySeq.const_mul
#align cauchy_seq.const_add CauchySeq.const_add

/- warning: cauchy_seq.inv -> CauchySeq.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Type.{u2}} [_inst_4 : SemilatticeSup.{u2} ι] {u : ι -> α}, (CauchySeq.{u1, u2} α ι _inst_1 _inst_4 u) -> (CauchySeq.{u1, u2} α ι _inst_1 _inst_4 (Inv.inv.{max u2 u1} (ι -> α) (Pi.instInv.{u2, u1} ι (fun (ᾰ : ι) => α) (fun (i : ι) => DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) u))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Type.{u2}} [_inst_4 : SemilatticeSup.{u2} ι] {u : ι -> α}, (CauchySeq.{u1, u2} α ι _inst_1 _inst_4 u) -> (CauchySeq.{u1, u2} α ι _inst_1 _inst_4 (Inv.inv.{max u2 u1} (ι -> α) (Pi.instInv.{u2, u1} ι (fun (ᾰ : ι) => α) (fun (i : ι) => InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2))))) u))
Case conversion may be inaccurate. Consider using '#align cauchy_seq.inv CauchySeq.invₓ'. -/
@[to_additive]
theorem CauchySeq.inv {ι : Type _} [SemilatticeSup ι] {u : ι → α} (h : CauchySeq u) :
    CauchySeq u⁻¹ :=
  uniformContinuous_inv.comp_cauchySeq h
#align cauchy_seq.inv CauchySeq.inv
#align cauchy_seq.neg CauchySeq.neg

/- warning: totally_bounded_iff_subset_finite_Union_nhds_one -> totallyBounded_iff_subset_finite_unionᵢ_nhds_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {s : Set.{u1} α}, Iff (TotallyBounded.{u1} α _inst_1 s) (forall (U : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))))))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Set.Finite.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.unionᵢ.{u1, succ u1} α α (fun (y : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) => SMul.smul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (Mul.toSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) y U)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {s : Set.{u1} α}, Iff (TotallyBounded.{u1} α _inst_1 s) (forall (U : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) U (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2)))))))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Set.Finite.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.unionᵢ.{u1, succ u1} α α (fun (y : α) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) => HSMul.hSMul.{u1, u1, u1} α (Set.{u1} α) (Set.{u1} α) (instHSMul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (MulAction.toSMul.{u1, u1} α α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) (Monoid.toMulAction.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) y U)))))))
Case conversion may be inaccurate. Consider using '#align totally_bounded_iff_subset_finite_Union_nhds_one totallyBounded_iff_subset_finite_unionᵢ_nhds_oneₓ'. -/
@[to_additive]
theorem totallyBounded_iff_subset_finite_unionᵢ_nhds_one {s : Set α} :
    TotallyBounded s ↔ ∀ U ∈ 𝓝 (1 : α), ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, y • U :=
  (𝓝 (1 : α)).basis_sets.uniformity_of_nhds_one_inv_mul_swapped.totallyBounded_iff.trans <| by
    simp [← preimage_smul_inv, preimage]
#align totally_bounded_iff_subset_finite_Union_nhds_one totallyBounded_iff_subset_finite_unionᵢ_nhds_one
#align totally_bounded_iff_subset_finite_Union_nhds_zero totallyBounded_iff_subset_finite_unionᵢ_nhds_zero

section UniformConvergence

variable {ι : Type _} {l : Filter ι} {l' : Filter β} {f f' : ι → β → α} {g g' : β → α} {s : Set β}

/- warning: tendsto_uniformly_on_filter.mul -> TendstoUniformlyOnFilter.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Type.{u3}} {l : Filter.{u3} ι} {l' : Filter.{u2} β} {f : ι -> β -> α} {f' : ι -> β -> α} {g : β -> α} {g' : β -> α}, (TendstoUniformlyOnFilter.{u2, u1, u3} β α ι _inst_1 f g l l') -> (TendstoUniformlyOnFilter.{u2, u1, u3} β α ι _inst_1 f' g' l l') -> (TendstoUniformlyOnFilter.{u2, u1, u3} β α ι _inst_1 (HMul.hMul.{max u3 u2 u1, max u3 u2 u1, max u3 u2 u1} (ι -> β -> α) (ι -> β -> α) (ι -> β -> α) (instHMul.{max u3 u2 u1} (ι -> β -> α) (Pi.instMul.{u3, max u2 u1} ι (fun (ᾰ : ι) => β -> α) (fun (i : ι) => Pi.instMul.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))))) f f') (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (β -> α) (β -> α) (β -> α) (instHMul.{max u2 u1} (β -> α) (Pi.instMul.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) g g') l l')
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : Group.{u2} α] [_inst_3 : UniformGroup.{u2} α _inst_1 _inst_2] {ι : Type.{u1}} {l : Filter.{u1} ι} {l' : Filter.{u3} β} {f : ι -> β -> α} {f' : ι -> β -> α} {g : β -> α} {g' : β -> α}, (TendstoUniformlyOnFilter.{u3, u2, u1} β α ι _inst_1 f g l l') -> (TendstoUniformlyOnFilter.{u3, u2, u1} β α ι _inst_1 f' g' l l') -> (TendstoUniformlyOnFilter.{u3, u2, u1} β α ι _inst_1 (HMul.hMul.{max (max u2 u3) u1, max (max u2 u3) u1, max (max u2 u3) u1} (ι -> β -> α) (ι -> β -> α) (ι -> β -> α) (instHMul.{max (max u2 u3) u1} (ι -> β -> α) (Pi.instMul.{u1, max u2 u3} ι (fun (ᾰ : ι) => β -> α) (fun (i : ι) => Pi.instMul.{u3, u2} β (fun (ᾰ : β) => α) (fun (i : β) => MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2))))))) f f') (HMul.hMul.{max u2 u3, max u2 u3, max u2 u3} (β -> α) (β -> α) (β -> α) (instHMul.{max u2 u3} (β -> α) (Pi.instMul.{u3, u2} β (fun (ᾰ : β) => α) (fun (i : β) => MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2)))))) g g') l l')
Case conversion may be inaccurate. Consider using '#align tendsto_uniformly_on_filter.mul TendstoUniformlyOnFilter.mulₓ'. -/
@[to_additive]
theorem TendstoUniformlyOnFilter.mul (hf : TendstoUniformlyOnFilter f g l l')
    (hf' : TendstoUniformlyOnFilter f' g' l l') : TendstoUniformlyOnFilter (f * f') (g * g') l l' :=
  fun u hu =>
  ((uniformContinuous_mul.comp_tendstoUniformlyOnFilter (hf.Prod hf')) u hu).diag_of_prod_left
#align tendsto_uniformly_on_filter.mul TendstoUniformlyOnFilter.mul
#align tendsto_uniformly_on_filter.add TendstoUniformlyOnFilter.add

/- warning: tendsto_uniformly_on_filter.div -> TendstoUniformlyOnFilter.div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Type.{u3}} {l : Filter.{u3} ι} {l' : Filter.{u2} β} {f : ι -> β -> α} {f' : ι -> β -> α} {g : β -> α} {g' : β -> α}, (TendstoUniformlyOnFilter.{u2, u1, u3} β α ι _inst_1 f g l l') -> (TendstoUniformlyOnFilter.{u2, u1, u3} β α ι _inst_1 f' g' l l') -> (TendstoUniformlyOnFilter.{u2, u1, u3} β α ι _inst_1 (HDiv.hDiv.{max u3 u2 u1, max u3 u2 u1, max u3 u2 u1} (ι -> β -> α) (ι -> β -> α) (ι -> β -> α) (instHDiv.{max u3 u2 u1} (ι -> β -> α) (Pi.instDiv.{u3, max u2 u1} ι (fun (ᾰ : ι) => β -> α) (fun (i : ι) => Pi.instDiv.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) f f') (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (β -> α) (β -> α) (β -> α) (instHDiv.{max u2 u1} (β -> α) (Pi.instDiv.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) g g') l l')
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : Group.{u2} α] [_inst_3 : UniformGroup.{u2} α _inst_1 _inst_2] {ι : Type.{u1}} {l : Filter.{u1} ι} {l' : Filter.{u3} β} {f : ι -> β -> α} {f' : ι -> β -> α} {g : β -> α} {g' : β -> α}, (TendstoUniformlyOnFilter.{u3, u2, u1} β α ι _inst_1 f g l l') -> (TendstoUniformlyOnFilter.{u3, u2, u1} β α ι _inst_1 f' g' l l') -> (TendstoUniformlyOnFilter.{u3, u2, u1} β α ι _inst_1 (HDiv.hDiv.{max (max u2 u3) u1, max (max u2 u3) u1, max (max u2 u3) u1} (ι -> β -> α) (ι -> β -> α) (ι -> β -> α) (instHDiv.{max (max u2 u3) u1} (ι -> β -> α) (Pi.instDiv.{u1, max u2 u3} ι (fun (ᾰ : ι) => β -> α) (fun (i : ι) => Pi.instDiv.{u3, u2} β (fun (ᾰ : β) => α) (fun (i : β) => DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2))))) f f') (HDiv.hDiv.{max u2 u3, max u2 u3, max u2 u3} (β -> α) (β -> α) (β -> α) (instHDiv.{max u2 u3} (β -> α) (Pi.instDiv.{u3, u2} β (fun (ᾰ : β) => α) (fun (i : β) => DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2)))) g g') l l')
Case conversion may be inaccurate. Consider using '#align tendsto_uniformly_on_filter.div TendstoUniformlyOnFilter.divₓ'. -/
@[to_additive]
theorem TendstoUniformlyOnFilter.div (hf : TendstoUniformlyOnFilter f g l l')
    (hf' : TendstoUniformlyOnFilter f' g' l l') : TendstoUniformlyOnFilter (f / f') (g / g') l l' :=
  fun u hu =>
  ((uniformContinuous_div.comp_tendstoUniformlyOnFilter (hf.Prod hf')) u hu).diag_of_prod_left
#align tendsto_uniformly_on_filter.div TendstoUniformlyOnFilter.div
#align tendsto_uniformly_on_filter.sub TendstoUniformlyOnFilter.sub

/- warning: tendsto_uniformly_on.mul -> TendstoUniformlyOn.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Type.{u3}} {l : Filter.{u3} ι} {f : ι -> β -> α} {f' : ι -> β -> α} {g : β -> α} {g' : β -> α} {s : Set.{u2} β}, (TendstoUniformlyOn.{u2, u1, u3} β α ι _inst_1 f g l s) -> (TendstoUniformlyOn.{u2, u1, u3} β α ι _inst_1 f' g' l s) -> (TendstoUniformlyOn.{u2, u1, u3} β α ι _inst_1 (HMul.hMul.{max u3 u2 u1, max u3 u2 u1, max u3 u2 u1} (ι -> β -> α) (ι -> β -> α) (ι -> β -> α) (instHMul.{max u3 u2 u1} (ι -> β -> α) (Pi.instMul.{u3, max u2 u1} ι (fun (ᾰ : ι) => β -> α) (fun (i : ι) => Pi.instMul.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))))) f f') (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (β -> α) (β -> α) (β -> α) (instHMul.{max u2 u1} (β -> α) (Pi.instMul.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) g g') l s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : Group.{u2} α] [_inst_3 : UniformGroup.{u2} α _inst_1 _inst_2] {ι : Type.{u1}} {l : Filter.{u1} ι} {f : ι -> β -> α} {f' : ι -> β -> α} {g : β -> α} {g' : β -> α} {s : Set.{u3} β}, (TendstoUniformlyOn.{u3, u2, u1} β α ι _inst_1 f g l s) -> (TendstoUniformlyOn.{u3, u2, u1} β α ι _inst_1 f' g' l s) -> (TendstoUniformlyOn.{u3, u2, u1} β α ι _inst_1 (HMul.hMul.{max (max u2 u3) u1, max (max u2 u3) u1, max (max u2 u3) u1} (ι -> β -> α) (ι -> β -> α) (ι -> β -> α) (instHMul.{max (max u2 u3) u1} (ι -> β -> α) (Pi.instMul.{u1, max u2 u3} ι (fun (ᾰ : ι) => β -> α) (fun (i : ι) => Pi.instMul.{u3, u2} β (fun (ᾰ : β) => α) (fun (i : β) => MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2))))))) f f') (HMul.hMul.{max u2 u3, max u2 u3, max u2 u3} (β -> α) (β -> α) (β -> α) (instHMul.{max u2 u3} (β -> α) (Pi.instMul.{u3, u2} β (fun (ᾰ : β) => α) (fun (i : β) => MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2)))))) g g') l s)
Case conversion may be inaccurate. Consider using '#align tendsto_uniformly_on.mul TendstoUniformlyOn.mulₓ'. -/
@[to_additive]
theorem TendstoUniformlyOn.mul (hf : TendstoUniformlyOn f g l s)
    (hf' : TendstoUniformlyOn f' g' l s) : TendstoUniformlyOn (f * f') (g * g') l s := fun u hu =>
  ((uniformContinuous_mul.comp_tendstoUniformlyOn (hf.Prod hf')) u hu).diag_of_prod
#align tendsto_uniformly_on.mul TendstoUniformlyOn.mul
#align tendsto_uniformly_on.add TendstoUniformlyOn.add

/- warning: tendsto_uniformly_on.div -> TendstoUniformlyOn.div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Type.{u3}} {l : Filter.{u3} ι} {f : ι -> β -> α} {f' : ι -> β -> α} {g : β -> α} {g' : β -> α} {s : Set.{u2} β}, (TendstoUniformlyOn.{u2, u1, u3} β α ι _inst_1 f g l s) -> (TendstoUniformlyOn.{u2, u1, u3} β α ι _inst_1 f' g' l s) -> (TendstoUniformlyOn.{u2, u1, u3} β α ι _inst_1 (HDiv.hDiv.{max u3 u2 u1, max u3 u2 u1, max u3 u2 u1} (ι -> β -> α) (ι -> β -> α) (ι -> β -> α) (instHDiv.{max u3 u2 u1} (ι -> β -> α) (Pi.instDiv.{u3, max u2 u1} ι (fun (ᾰ : ι) => β -> α) (fun (i : ι) => Pi.instDiv.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) f f') (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (β -> α) (β -> α) (β -> α) (instHDiv.{max u2 u1} (β -> α) (Pi.instDiv.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) g g') l s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : Group.{u2} α] [_inst_3 : UniformGroup.{u2} α _inst_1 _inst_2] {ι : Type.{u1}} {l : Filter.{u1} ι} {f : ι -> β -> α} {f' : ι -> β -> α} {g : β -> α} {g' : β -> α} {s : Set.{u3} β}, (TendstoUniformlyOn.{u3, u2, u1} β α ι _inst_1 f g l s) -> (TendstoUniformlyOn.{u3, u2, u1} β α ι _inst_1 f' g' l s) -> (TendstoUniformlyOn.{u3, u2, u1} β α ι _inst_1 (HDiv.hDiv.{max (max u2 u3) u1, max (max u2 u3) u1, max (max u2 u3) u1} (ι -> β -> α) (ι -> β -> α) (ι -> β -> α) (instHDiv.{max (max u2 u3) u1} (ι -> β -> α) (Pi.instDiv.{u1, max u2 u3} ι (fun (ᾰ : ι) => β -> α) (fun (i : ι) => Pi.instDiv.{u3, u2} β (fun (ᾰ : β) => α) (fun (i : β) => DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2))))) f f') (HDiv.hDiv.{max u2 u3, max u2 u3, max u2 u3} (β -> α) (β -> α) (β -> α) (instHDiv.{max u2 u3} (β -> α) (Pi.instDiv.{u3, u2} β (fun (ᾰ : β) => α) (fun (i : β) => DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2)))) g g') l s)
Case conversion may be inaccurate. Consider using '#align tendsto_uniformly_on.div TendstoUniformlyOn.divₓ'. -/
@[to_additive]
theorem TendstoUniformlyOn.div (hf : TendstoUniformlyOn f g l s)
    (hf' : TendstoUniformlyOn f' g' l s) : TendstoUniformlyOn (f / f') (g / g') l s := fun u hu =>
  ((uniformContinuous_div.comp_tendstoUniformlyOn (hf.Prod hf')) u hu).diag_of_prod
#align tendsto_uniformly_on.div TendstoUniformlyOn.div
#align tendsto_uniformly_on.sub TendstoUniformlyOn.sub

/- warning: tendsto_uniformly.mul -> TendstoUniformly.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Type.{u3}} {l : Filter.{u3} ι} {f : ι -> β -> α} {f' : ι -> β -> α} {g : β -> α} {g' : β -> α}, (TendstoUniformly.{u2, u1, u3} β α ι _inst_1 f g l) -> (TendstoUniformly.{u2, u1, u3} β α ι _inst_1 f' g' l) -> (TendstoUniformly.{u2, u1, u3} β α ι _inst_1 (HMul.hMul.{max u3 u2 u1, max u3 u2 u1, max u3 u2 u1} (ι -> β -> α) (ι -> β -> α) (ι -> β -> α) (instHMul.{max u3 u2 u1} (ι -> β -> α) (Pi.instMul.{u3, max u2 u1} ι (fun (ᾰ : ι) => β -> α) (fun (i : ι) => Pi.instMul.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))))) f f') (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (β -> α) (β -> α) (β -> α) (instHMul.{max u2 u1} (β -> α) (Pi.instMul.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) g g') l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : Group.{u2} α] [_inst_3 : UniformGroup.{u2} α _inst_1 _inst_2] {ι : Type.{u1}} {l : Filter.{u1} ι} {f : ι -> β -> α} {f' : ι -> β -> α} {g : β -> α} {g' : β -> α}, (TendstoUniformly.{u3, u2, u1} β α ι _inst_1 f g l) -> (TendstoUniformly.{u3, u2, u1} β α ι _inst_1 f' g' l) -> (TendstoUniformly.{u3, u2, u1} β α ι _inst_1 (HMul.hMul.{max (max u2 u3) u1, max (max u2 u3) u1, max (max u2 u3) u1} (ι -> β -> α) (ι -> β -> α) (ι -> β -> α) (instHMul.{max (max u2 u3) u1} (ι -> β -> α) (Pi.instMul.{u1, max u2 u3} ι (fun (ᾰ : ι) => β -> α) (fun (i : ι) => Pi.instMul.{u3, u2} β (fun (ᾰ : β) => α) (fun (i : β) => MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2))))))) f f') (HMul.hMul.{max u2 u3, max u2 u3, max u2 u3} (β -> α) (β -> α) (β -> α) (instHMul.{max u2 u3} (β -> α) (Pi.instMul.{u3, u2} β (fun (ᾰ : β) => α) (fun (i : β) => MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2)))))) g g') l)
Case conversion may be inaccurate. Consider using '#align tendsto_uniformly.mul TendstoUniformly.mulₓ'. -/
@[to_additive]
theorem TendstoUniformly.mul (hf : TendstoUniformly f g l) (hf' : TendstoUniformly f' g' l) :
    TendstoUniformly (f * f') (g * g') l := fun u hu =>
  ((uniformContinuous_mul.comp_tendstoUniformly (hf.Prod hf')) u hu).diag_of_prod
#align tendsto_uniformly.mul TendstoUniformly.mul
#align tendsto_uniformly.add TendstoUniformly.add

/- warning: tendsto_uniformly.div -> TendstoUniformly.div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Type.{u3}} {l : Filter.{u3} ι} {f : ι -> β -> α} {f' : ι -> β -> α} {g : β -> α} {g' : β -> α}, (TendstoUniformly.{u2, u1, u3} β α ι _inst_1 f g l) -> (TendstoUniformly.{u2, u1, u3} β α ι _inst_1 f' g' l) -> (TendstoUniformly.{u2, u1, u3} β α ι _inst_1 (HDiv.hDiv.{max u3 u2 u1, max u3 u2 u1, max u3 u2 u1} (ι -> β -> α) (ι -> β -> α) (ι -> β -> α) (instHDiv.{max u3 u2 u1} (ι -> β -> α) (Pi.instDiv.{u3, max u2 u1} ι (fun (ᾰ : ι) => β -> α) (fun (i : ι) => Pi.instDiv.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) f f') (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (β -> α) (β -> α) (β -> α) (instHDiv.{max u2 u1} (β -> α) (Pi.instDiv.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) g g') l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : Group.{u2} α] [_inst_3 : UniformGroup.{u2} α _inst_1 _inst_2] {ι : Type.{u1}} {l : Filter.{u1} ι} {f : ι -> β -> α} {f' : ι -> β -> α} {g : β -> α} {g' : β -> α}, (TendstoUniformly.{u3, u2, u1} β α ι _inst_1 f g l) -> (TendstoUniformly.{u3, u2, u1} β α ι _inst_1 f' g' l) -> (TendstoUniformly.{u3, u2, u1} β α ι _inst_1 (HDiv.hDiv.{max (max u2 u3) u1, max (max u2 u3) u1, max (max u2 u3) u1} (ι -> β -> α) (ι -> β -> α) (ι -> β -> α) (instHDiv.{max (max u2 u3) u1} (ι -> β -> α) (Pi.instDiv.{u1, max u2 u3} ι (fun (ᾰ : ι) => β -> α) (fun (i : ι) => Pi.instDiv.{u3, u2} β (fun (ᾰ : β) => α) (fun (i : β) => DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2))))) f f') (HDiv.hDiv.{max u2 u3, max u2 u3, max u2 u3} (β -> α) (β -> α) (β -> α) (instHDiv.{max u2 u3} (β -> α) (Pi.instDiv.{u3, u2} β (fun (ᾰ : β) => α) (fun (i : β) => DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2)))) g g') l)
Case conversion may be inaccurate. Consider using '#align tendsto_uniformly.div TendstoUniformly.divₓ'. -/
@[to_additive]
theorem TendstoUniformly.div (hf : TendstoUniformly f g l) (hf' : TendstoUniformly f' g' l) :
    TendstoUniformly (f / f') (g / g') l := fun u hu =>
  ((uniformContinuous_div.comp_tendstoUniformly (hf.Prod hf')) u hu).diag_of_prod
#align tendsto_uniformly.div TendstoUniformly.div
#align tendsto_uniformly.sub TendstoUniformly.sub

/- warning: uniform_cauchy_seq_on.mul -> UniformCauchySeqOn.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Type.{u3}} {l : Filter.{u3} ι} {f : ι -> β -> α} {f' : ι -> β -> α} {s : Set.{u2} β}, (UniformCauchySeqOn.{u2, u1, u3} β α ι _inst_1 f l s) -> (UniformCauchySeqOn.{u2, u1, u3} β α ι _inst_1 f' l s) -> (UniformCauchySeqOn.{u2, u1, u3} β α ι _inst_1 (HMul.hMul.{max u3 u2 u1, max u3 u2 u1, max u3 u2 u1} (ι -> β -> α) (ι -> β -> α) (ι -> β -> α) (instHMul.{max u3 u2 u1} (ι -> β -> α) (Pi.instMul.{u3, max u2 u1} ι (fun (ᾰ : ι) => β -> α) (fun (i : ι) => Pi.instMul.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))))) f f') l s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : Group.{u2} α] [_inst_3 : UniformGroup.{u2} α _inst_1 _inst_2] {ι : Type.{u1}} {l : Filter.{u1} ι} {f : ι -> β -> α} {f' : ι -> β -> α} {s : Set.{u3} β}, (UniformCauchySeqOn.{u3, u2, u1} β α ι _inst_1 f l s) -> (UniformCauchySeqOn.{u3, u2, u1} β α ι _inst_1 f' l s) -> (UniformCauchySeqOn.{u3, u2, u1} β α ι _inst_1 (HMul.hMul.{max (max u2 u3) u1, max (max u2 u3) u1, max (max u2 u3) u1} (ι -> β -> α) (ι -> β -> α) (ι -> β -> α) (instHMul.{max (max u2 u3) u1} (ι -> β -> α) (Pi.instMul.{u1, max u2 u3} ι (fun (ᾰ : ι) => β -> α) (fun (i : ι) => Pi.instMul.{u3, u2} β (fun (ᾰ : β) => α) (fun (i : β) => MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2))))))) f f') l s)
Case conversion may be inaccurate. Consider using '#align uniform_cauchy_seq_on.mul UniformCauchySeqOn.mulₓ'. -/
@[to_additive]
theorem UniformCauchySeqOn.mul (hf : UniformCauchySeqOn f l s) (hf' : UniformCauchySeqOn f' l s) :
    UniformCauchySeqOn (f * f') l s := fun u hu => by
  simpa using (uniform_continuous_mul.comp_uniform_cauchy_seq_on (hf.prod' hf')) u hu
#align uniform_cauchy_seq_on.mul UniformCauchySeqOn.mul
#align uniform_cauchy_seq_on.add UniformCauchySeqOn.add

/- warning: uniform_cauchy_seq_on.div -> UniformCauchySeqOn.div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : UniformGroup.{u1} α _inst_1 _inst_2] {ι : Type.{u3}} {l : Filter.{u3} ι} {f : ι -> β -> α} {f' : ι -> β -> α} {s : Set.{u2} β}, (UniformCauchySeqOn.{u2, u1, u3} β α ι _inst_1 f l s) -> (UniformCauchySeqOn.{u2, u1, u3} β α ι _inst_1 f' l s) -> (UniformCauchySeqOn.{u2, u1, u3} β α ι _inst_1 (HDiv.hDiv.{max u3 u2 u1, max u3 u2 u1, max u3 u2 u1} (ι -> β -> α) (ι -> β -> α) (ι -> β -> α) (instHDiv.{max u3 u2 u1} (ι -> β -> α) (Pi.instDiv.{u3, max u2 u1} ι (fun (ᾰ : ι) => β -> α) (fun (i : ι) => Pi.instDiv.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) f f') l s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : Group.{u2} α] [_inst_3 : UniformGroup.{u2} α _inst_1 _inst_2] {ι : Type.{u1}} {l : Filter.{u1} ι} {f : ι -> β -> α} {f' : ι -> β -> α} {s : Set.{u3} β}, (UniformCauchySeqOn.{u3, u2, u1} β α ι _inst_1 f l s) -> (UniformCauchySeqOn.{u3, u2, u1} β α ι _inst_1 f' l s) -> (UniformCauchySeqOn.{u3, u2, u1} β α ι _inst_1 (HDiv.hDiv.{max (max u2 u3) u1, max (max u2 u3) u1, max (max u2 u3) u1} (ι -> β -> α) (ι -> β -> α) (ι -> β -> α) (instHDiv.{max (max u2 u3) u1} (ι -> β -> α) (Pi.instDiv.{u1, max u2 u3} ι (fun (ᾰ : ι) => β -> α) (fun (i : ι) => Pi.instDiv.{u3, u2} β (fun (ᾰ : β) => α) (fun (i : β) => DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2))))) f f') l s)
Case conversion may be inaccurate. Consider using '#align uniform_cauchy_seq_on.div UniformCauchySeqOn.divₓ'. -/
@[to_additive]
theorem UniformCauchySeqOn.div (hf : UniformCauchySeqOn f l s) (hf' : UniformCauchySeqOn f' l s) :
    UniformCauchySeqOn (f / f') l s := fun u hu => by
  simpa using (uniform_continuous_div.comp_uniform_cauchy_seq_on (hf.prod' hf')) u hu
#align uniform_cauchy_seq_on.div UniformCauchySeqOn.div
#align uniform_cauchy_seq_on.sub UniformCauchySeqOn.sub

end UniformConvergence

end UniformGroup

section TopologicalGroup

open Filter

variable (G : Type _) [Group G] [TopologicalSpace G] [TopologicalGroup G]

#print TopologicalGroup.toUniformSpace /-
/-- The right uniformity on a topological group (as opposed to the left uniformity).

Warning: in general the right and left uniformities do not coincide and so one does not obtain a
`uniform_group` structure. Two important special cases where they _do_ coincide are for
commutative groups (see `topological_comm_group_is_uniform`) and for compact groups (see
`topological_group_is_uniform_of_compact_space`). -/
@[to_additive
      "The right uniformity on a topological additive group (as opposed to the left\nuniformity).\n\nWarning: in general the right and left uniformities do not coincide and so one does not obtain a\n`uniform_add_group` structure. Two important special cases where they _do_ coincide are for\ncommutative additive groups (see `topological_add_comm_group_is_uniform`) and for compact\nadditive groups (see `topological_add_comm_group_is_uniform_of_compact_space`)."]
def TopologicalGroup.toUniformSpace : UniformSpace G
    where
  uniformity := comap (fun p : G × G => p.2 / p.1) (𝓝 1)
  refl := by
    refine' map_le_iff_le_comap.1 (le_trans _ (pure_le_nhds 1)) <;>
      simp (config := { contextual := true }) [Set.subset_def]
  symm :=
    by
    suffices
      tendsto (fun p : G × G => (p.2 / p.1)⁻¹) (comap (fun p : G × G => p.2 / p.1) (𝓝 1)) (𝓝 1⁻¹) by
      simpa [tendsto_comap_iff]
    exact tendsto.comp (tendsto.inv tendsto_id) tendsto_comap
  comp := by
    intro D H
    rw [mem_lift'_sets]
    · rcases H with ⟨U, U_nhds, U_sub⟩
      rcases exists_nhds_one_split U_nhds with ⟨V, ⟨V_nhds, V_sum⟩⟩
      exists (fun p : G × G => p.2 / p.1) ⁻¹' V
      have H :
        (fun p : G × G => p.2 / p.1) ⁻¹' V ∈ comap (fun p : G × G => p.2 / p.1) (𝓝 (1 : G)) := by
        exists V, V_nhds <;> rfl
      exists H
      have comp_rel_sub :
        compRel ((fun p : G × G => p.2 / p.1) ⁻¹' V) ((fun p => p.2 / p.1) ⁻¹' V) ⊆
          (fun p : G × G => p.2 / p.1) ⁻¹' U :=
        by
        intro p p_comp_rel
        rcases p_comp_rel with ⟨z, ⟨Hz1, Hz2⟩⟩
        simpa using V_sum _ Hz2 _ Hz1
      exact Set.Subset.trans comp_rel_sub U_sub
    · exact monotone_id.comp_rel monotone_id
  isOpen_uniformity := by
    intro S
    let S' x := { p : G × G | p.1 = x → p.2 ∈ S }
    show IsOpen S ↔ ∀ x : G, x ∈ S → S' x ∈ comap (fun p : G × G => p.2 / p.1) (𝓝 (1 : G))
    rw [isOpen_iff_mem_nhds]
    refine' forall₂_congr fun a ha => _
    rw [← nhds_translation_div, mem_comap, mem_comap]
    refine' exists₂_congr fun t ht => _
    show (fun y : G => y / a) ⁻¹' t ⊆ S ↔ (fun p : G × G => p.snd / p.fst) ⁻¹' t ⊆ S' a
    constructor
    · rintro h ⟨x, y⟩ hx rfl
      exact h hx
    · rintro h x hx
      exact @h (a, x) hx rfl
#align topological_group.to_uniform_space TopologicalGroup.toUniformSpace
#align topological_add_group.to_uniform_space TopologicalAddGroup.toUniformSpace
-/

attribute [local instance] TopologicalGroup.toUniformSpace

/- warning: uniformity_eq_comap_nhds_one' -> uniformity_eq_comap_nhds_one' is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} G G)) (uniformity.{u1} G (TopologicalGroup.toUniformSpace.{u1} G _inst_1 _inst_2 _inst_3)) (Filter.comap.{u1, u1} (Prod.{u1, u1} G G) G (fun (p : Prod.{u1, u1} G G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Prod.snd.{u1, u1} G G p) (Prod.fst.{u1, u1} G G p)) (nhds.{u1} G _inst_2 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))))))
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} G G)) (uniformity.{u1} G (TopologicalGroup.toUniformSpace.{u1} G _inst_1 _inst_2 _inst_3)) (Filter.comap.{u1, u1} (Prod.{u1, u1} G G) G (fun (p : Prod.{u1, u1} G G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Prod.snd.{u1, u1} G G p) (Prod.fst.{u1, u1} G G p)) (nhds.{u1} G _inst_2 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align uniformity_eq_comap_nhds_one' uniformity_eq_comap_nhds_one'ₓ'. -/
@[to_additive]
theorem uniformity_eq_comap_nhds_one' : 𝓤 G = comap (fun p : G × G => p.2 / p.1) (𝓝 (1 : G)) :=
  rfl
#align uniformity_eq_comap_nhds_one' uniformity_eq_comap_nhds_one'
#align uniformity_eq_comap_nhds_zero' uniformity_eq_comap_nhds_zero'

#print topologicalGroup_is_uniform_of_compactSpace /-
@[to_additive]
theorem topologicalGroup_is_uniform_of_compactSpace [CompactSpace G] : UniformGroup G :=
  ⟨by
    apply CompactSpace.uniformContinuous_of_continuous
    exact continuous_div'⟩
#align topological_group_is_uniform_of_compact_space topologicalGroup_is_uniform_of_compactSpace
#align topological_add_group_is_uniform_of_compact_space topologicalAddGroup_is_uniform_of_compactSpace
-/

variable {G}

/- warning: subgroup.is_closed_of_discrete -> Subgroup.isClosed_of_discrete is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] [_inst_4 : T2Space.{u1} G _inst_2] {H : Subgroup.{u1} G _inst_1} [_inst_5 : DiscreteTopology.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (Subtype.topologicalSpace.{u1} G (fun (x : G) => Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) x H) _inst_2)], IsClosed.{u1} G _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subgroup.{u1} G _inst_1) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] [_inst_4 : T2Space.{u1} G _inst_2] {H : Subgroup.{u1} G _inst_1} [_inst_5 : DiscreteTopology.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) (instTopologicalSpaceSubtype.{u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H) _inst_2)], IsClosed.{u1} G _inst_2 (SetLike.coe.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1) H)
Case conversion may be inaccurate. Consider using '#align subgroup.is_closed_of_discrete Subgroup.isClosed_of_discreteₓ'. -/
@[to_additive]
instance Subgroup.isClosed_of_discrete [T2Space G] {H : Subgroup G} [DiscreteTopology H] :
    IsClosed (H : Set G) :=
  by
  obtain ⟨V, V_in, VH⟩ : ∃ (V : Set G)(hV : V ∈ 𝓝 (1 : G)), V ∩ (H : Set G) = {1}
  exact nhds_inter_eq_singleton_of_mem_discrete H.one_mem
  haveI : SeparatedSpace G := separated_iff_t2.mpr ‹_›
  have : (fun p : G × G => p.2 / p.1) ⁻¹' V ∈ 𝓤 G := preimage_mem_comap V_in
  apply isClosed_of_spaced_out this
  intro h h_in h' h'_in
  contrapose!
  rintro (hyp : h' / h ∈ V)
  have : h' / h ∈ ({1} : Set G) := VH ▸ Set.mem_inter hyp (H.div_mem h'_in h_in)
  exact (eq_of_div_eq_one this).symm
#align subgroup.is_closed_of_discrete Subgroup.isClosed_of_discrete
#align add_subgroup.is_closed_of_discrete AddSubgroup.isClosed_of_discrete

/- warning: topological_group.tendsto_uniformly_iff -> TopologicalGroup.tendstoUniformly_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] {ι : Type.{u2}} {α : Type.{u3}} (F : ι -> α -> G) (f : α -> G) (p : Filter.{u2} ι), Iff (TendstoUniformly.{u3, u1, u2} α G ι (TopologicalGroup.toUniformSpace.{u1} G _inst_1 _inst_2 _inst_3) F f p) (forall (u : Set.{u1} G), (Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) u (nhds.{u1} G _inst_2 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))))) -> (Filter.Eventually.{u2} ι (fun (i : ι) => forall (a : α), Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (F i a) (f a)) u) p))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] {ι : Type.{u3}} {α : Type.{u2}} (F : ι -> α -> G) (f : α -> G) (p : Filter.{u3} ι), Iff (TendstoUniformly.{u2, u1, u3} α G ι (TopologicalGroup.toUniformSpace.{u1} G _inst_1 _inst_2 _inst_3) F f p) (forall (u : Set.{u1} G), (Membership.mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (instMembershipSetFilter.{u1} G) u (nhds.{u1} G _inst_2 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))))))) -> (Filter.Eventually.{u3} ι (fun (i : ι) => forall (a : α), Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (F i a) (f a)) u) p))
Case conversion may be inaccurate. Consider using '#align topological_group.tendsto_uniformly_iff TopologicalGroup.tendstoUniformly_iffₓ'. -/
@[to_additive]
theorem TopologicalGroup.tendstoUniformly_iff {ι α : Type _} (F : ι → α → G) (f : α → G)
    (p : Filter ι) :
    @TendstoUniformly α G ι (TopologicalGroup.toUniformSpace G) F f p ↔
      ∀ u ∈ 𝓝 (1 : G), ∀ᶠ i in p, ∀ a, F i a / f a ∈ u :=
  ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h v ⟨u, hu, hv⟩ =>
    mem_of_superset (h u hu) fun i hi a => hv (hi a)⟩
#align topological_group.tendsto_uniformly_iff TopologicalGroup.tendstoUniformly_iff
#align topological_add_group.tendsto_uniformly_iff TopologicalAddGroup.tendstoUniformly_iff

/- warning: topological_group.tendsto_uniformly_on_iff -> TopologicalGroup.tendstoUniformlyOn_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] {ι : Type.{u2}} {α : Type.{u3}} (F : ι -> α -> G) (f : α -> G) (p : Filter.{u2} ι) (s : Set.{u3} α), Iff (TendstoUniformlyOn.{u3, u1, u2} α G ι (TopologicalGroup.toUniformSpace.{u1} G _inst_1 _inst_2 _inst_3) F f p s) (forall (u : Set.{u1} G), (Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) u (nhds.{u1} G _inst_2 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))))) -> (Filter.Eventually.{u2} ι (fun (i : ι) => forall (a : α), (Membership.Mem.{u3, u3} α (Set.{u3} α) (Set.hasMem.{u3} α) a s) -> (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (F i a) (f a)) u)) p))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] {ι : Type.{u3}} {α : Type.{u2}} (F : ι -> α -> G) (f : α -> G) (p : Filter.{u3} ι) (s : Set.{u2} α), Iff (TendstoUniformlyOn.{u2, u1, u3} α G ι (TopologicalGroup.toUniformSpace.{u1} G _inst_1 _inst_2 _inst_3) F f p s) (forall (u : Set.{u1} G), (Membership.mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (instMembershipSetFilter.{u1} G) u (nhds.{u1} G _inst_2 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))))))) -> (Filter.Eventually.{u3} ι (fun (i : ι) => forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (F i a) (f a)) u)) p))
Case conversion may be inaccurate. Consider using '#align topological_group.tendsto_uniformly_on_iff TopologicalGroup.tendstoUniformlyOn_iffₓ'. -/
@[to_additive]
theorem TopologicalGroup.tendstoUniformlyOn_iff {ι α : Type _} (F : ι → α → G) (f : α → G)
    (p : Filter ι) (s : Set α) :
    @TendstoUniformlyOn α G ι (TopologicalGroup.toUniformSpace G) F f p s ↔
      ∀ u ∈ 𝓝 (1 : G), ∀ᶠ i in p, ∀ a ∈ s, F i a / f a ∈ u :=
  ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h v ⟨u, hu, hv⟩ =>
    mem_of_superset (h u hu) fun i hi a ha => hv (hi a ha)⟩
#align topological_group.tendsto_uniformly_on_iff TopologicalGroup.tendstoUniformlyOn_iff
#align topological_add_group.tendsto_uniformly_on_iff TopologicalAddGroup.tendstoUniformlyOn_iff

/- warning: topological_group.tendsto_locally_uniformly_iff -> TopologicalGroup.tendstoLocallyUniformly_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] {ι : Type.{u2}} {α : Type.{u3}} [_inst_4 : TopologicalSpace.{u3} α] (F : ι -> α -> G) (f : α -> G) (p : Filter.{u2} ι), Iff (TendstoLocallyUniformly.{u3, u1, u2} α G ι (TopologicalGroup.toUniformSpace.{u1} G _inst_1 _inst_2 _inst_3) _inst_4 F f p) (forall (u : Set.{u1} G), (Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) u (nhds.{u1} G _inst_2 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))))) -> (forall (x : α), Exists.{succ u3} (Set.{u3} α) (fun (t : Set.{u3} α) => Exists.{0} (Membership.Mem.{u3, u3} (Set.{u3} α) (Filter.{u3} α) (Filter.hasMem.{u3} α) t (nhds.{u3} α _inst_4 x)) (fun (H : Membership.Mem.{u3, u3} (Set.{u3} α) (Filter.{u3} α) (Filter.hasMem.{u3} α) t (nhds.{u3} α _inst_4 x)) => Filter.Eventually.{u2} ι (fun (i : ι) => forall (a : α), (Membership.Mem.{u3, u3} α (Set.{u3} α) (Set.hasMem.{u3} α) a t) -> (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (F i a) (f a)) u)) p))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] {ι : Type.{u3}} {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (F : ι -> α -> G) (f : α -> G) (p : Filter.{u3} ι), Iff (TendstoLocallyUniformly.{u2, u1, u3} α G ι (TopologicalGroup.toUniformSpace.{u1} G _inst_1 _inst_2 _inst_3) _inst_4 F f p) (forall (u : Set.{u1} G), (Membership.mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (instMembershipSetFilter.{u1} G) u (nhds.{u1} G _inst_2 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))))))) -> (forall (x : α), Exists.{succ u2} (Set.{u2} α) (fun (t : Set.{u2} α) => And (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) t (nhds.{u2} α _inst_4 x)) (Filter.Eventually.{u3} ι (fun (i : ι) => forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a t) -> (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (F i a) (f a)) u)) p))))
Case conversion may be inaccurate. Consider using '#align topological_group.tendsto_locally_uniformly_iff TopologicalGroup.tendstoLocallyUniformly_iffₓ'. -/
@[to_additive]
theorem TopologicalGroup.tendstoLocallyUniformly_iff {ι α : Type _} [TopologicalSpace α]
    (F : ι → α → G) (f : α → G) (p : Filter ι) :
    @TendstoLocallyUniformly α G ι (TopologicalGroup.toUniformSpace G) _ F f p ↔
      ∀ u ∈ 𝓝 (1 : G), ∀ (x : α), ∃ t ∈ 𝓝 x, ∀ᶠ i in p, ∀ a ∈ t, F i a / f a ∈ u :=
  ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h v ⟨u, hu, hv⟩ x =>
    Exists.imp (fun a => Exists.imp fun ha hp => mem_of_superset hp fun i hi a ha => hv (hi a ha))
      (h u hu x)⟩
#align topological_group.tendsto_locally_uniformly_iff TopologicalGroup.tendstoLocallyUniformly_iff
#align topological_add_group.tendsto_locally_uniformly_iff TopologicalAddGroup.tendstoLocallyUniformly_iff

/- warning: topological_group.tendsto_locally_uniformly_on_iff -> TopologicalGroup.tendstoLocallyUniformlyOn_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] {ι : Type.{u2}} {α : Type.{u3}} [_inst_4 : TopologicalSpace.{u3} α] (F : ι -> α -> G) (f : α -> G) (p : Filter.{u2} ι) (s : Set.{u3} α), Iff (TendstoLocallyUniformlyOn.{u3, u1, u2} α G ι (TopologicalGroup.toUniformSpace.{u1} G _inst_1 _inst_2 _inst_3) _inst_4 F f p s) (forall (u : Set.{u1} G), (Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) u (nhds.{u1} G _inst_2 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))))) -> (forall (x : α), (Membership.Mem.{u3, u3} α (Set.{u3} α) (Set.hasMem.{u3} α) x s) -> (Exists.{succ u3} (Set.{u3} α) (fun (t : Set.{u3} α) => Exists.{0} (Membership.Mem.{u3, u3} (Set.{u3} α) (Filter.{u3} α) (Filter.hasMem.{u3} α) t (nhdsWithin.{u3} α _inst_4 x s)) (fun (H : Membership.Mem.{u3, u3} (Set.{u3} α) (Filter.{u3} α) (Filter.hasMem.{u3} α) t (nhdsWithin.{u3} α _inst_4 x s)) => Filter.Eventually.{u2} ι (fun (i : ι) => forall (a : α), (Membership.Mem.{u3, u3} α (Set.{u3} α) (Set.hasMem.{u3} α) a t) -> (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (F i a) (f a)) u)) p)))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] {ι : Type.{u3}} {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (F : ι -> α -> G) (f : α -> G) (p : Filter.{u3} ι) (s : Set.{u2} α), Iff (TendstoLocallyUniformlyOn.{u2, u1, u3} α G ι (TopologicalGroup.toUniformSpace.{u1} G _inst_1 _inst_2 _inst_3) _inst_4 F f p s) (forall (u : Set.{u1} G), (Membership.mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (instMembershipSetFilter.{u1} G) u (nhds.{u1} G _inst_2 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))))))) -> (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Exists.{succ u2} (Set.{u2} α) (fun (t : Set.{u2} α) => And (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) t (nhdsWithin.{u2} α _inst_4 x s)) (Filter.Eventually.{u3} ι (fun (i : ι) => forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a t) -> (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (F i a) (f a)) u)) p)))))
Case conversion may be inaccurate. Consider using '#align topological_group.tendsto_locally_uniformly_on_iff TopologicalGroup.tendstoLocallyUniformlyOn_iffₓ'. -/
@[to_additive]
theorem TopologicalGroup.tendstoLocallyUniformlyOn_iff {ι α : Type _} [TopologicalSpace α]
    (F : ι → α → G) (f : α → G) (p : Filter ι) (s : Set α) :
    @TendstoLocallyUniformlyOn α G ι (TopologicalGroup.toUniformSpace G) _ F f p s ↔
      ∀ u ∈ 𝓝 (1 : G), ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∀ᶠ i in p, ∀ a ∈ t, F i a / f a ∈ u :=
  ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h v ⟨u, hu, hv⟩ x =>
    (Exists.imp fun a => Exists.imp fun ha hp => mem_of_superset hp fun i hi a ha => hv (hi a ha)) ∘
      h u hu x⟩
#align topological_group.tendsto_locally_uniformly_on_iff TopologicalGroup.tendstoLocallyUniformlyOn_iff
#align topological_add_group.tendsto_locally_uniformly_on_iff TopologicalAddGroup.tendstoLocallyUniformlyOn_iff

end TopologicalGroup

section TopologicalCommGroup

universe u v w x

open Filter

variable (G : Type _) [CommGroup G] [TopologicalSpace G] [TopologicalGroup G]

section

attribute [local instance] TopologicalGroup.toUniformSpace

variable {G}

#print comm_topologicalGroup_is_uniform /-
@[to_additive]
theorem comm_topologicalGroup_is_uniform : UniformGroup G :=
  by
  have :
    Tendsto
      ((fun p : G × G => p.1 / p.2) ∘ fun p : (G × G) × G × G => (p.1.2 / p.1.1, p.2.2 / p.2.1))
      (comap (fun p : (G × G) × G × G => (p.1.2 / p.1.1, p.2.2 / p.2.1)) ((𝓝 1).Prod (𝓝 1)))
      (𝓝 (1 / 1)) :=
    (tendsto_fst.div' tendsto_snd).comp tendsto_comap
  constructor
  rw [UniformContinuous, uniformity_prod_eq_prod, tendsto_map'_iff, uniformity_eq_comap_nhds_one' G,
    tendsto_comap_iff, prod_comap_comap_eq]
  simpa [(· ∘ ·), div_eq_mul_inv, mul_comm, mul_left_comm] using this
#align topological_comm_group_is_uniform comm_topologicalGroup_is_uniform
#align topological_add_comm_group_is_uniform comm_topologicalAddGroup_is_uniform
-/

open Set

/- warning: topological_group.t2_space_iff_one_closed -> TopologicalGroup.t2Space_iff_one_closed is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 (CommGroup.toGroup.{u1} G _inst_1)], Iff (T2Space.{u1} G _inst_2) (IsClosed.{u1} G _inst_2 (Singleton.singleton.{u1, u1} G (Set.{u1} G) (Set.hasSingleton.{u1} G) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 (CommGroup.toGroup.{u1} G _inst_1)], Iff (T2Space.{u1} G _inst_2) (IsClosed.{u1} G _inst_2 (Singleton.singleton.{u1, u1} G (Set.{u1} G) (Set.instSingletonSet.{u1} G) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align topological_group.t2_space_iff_one_closed TopologicalGroup.t2Space_iff_one_closedₓ'. -/
@[to_additive]
theorem TopologicalGroup.t2Space_iff_one_closed : T2Space G ↔ IsClosed ({1} : Set G) :=
  by
  haveI : UniformGroup G := comm_topologicalGroup_is_uniform
  rw [← separated_iff_t2, separatedSpace_iff, ← closure_eq_iff_isClosed]
  constructor <;> intro h
  · apply subset.antisymm
    · intro x x_in
      have := group_separationRel x 1
      rw [div_one] at this
      rw [← this, h] at x_in
      change x = 1 at x_in
      simp [x_in]
    · exact subset_closure
  · ext p
    cases' p with x y
    rw [group_separationRel x, h, mem_singleton_iff, div_eq_one]
    rfl
#align topological_group.t2_space_iff_one_closed TopologicalGroup.t2Space_iff_one_closed
#align topological_add_group.t2_space_iff_zero_closed TopologicalAddGroup.t2Space_iff_zero_closed

/- warning: topological_group.t2_space_of_one_sep -> TopologicalGroup.t2Space_of_one_sep is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 (CommGroup.toGroup.{u1} G _inst_1)], (forall (x : G), (Ne.{succ u1} G x (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))))))) -> (Exists.{succ u1} (Set.{u1} G) (fun (U : Set.{u1} G) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) U (nhds.{u1} G _inst_2 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))))))) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) U (nhds.{u1} G _inst_2 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))))))) => Not (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) x U))))) -> (T2Space.{u1} G _inst_2)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 (CommGroup.toGroup.{u1} G _inst_1)], (forall (x : G), (Ne.{succ u1} G x (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1)))))))) -> (Exists.{succ u1} (Set.{u1} G) (fun (U : Set.{u1} G) => And (Membership.mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (instMembershipSetFilter.{u1} G) U (nhds.{u1} G _inst_2 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1))))))))) (Not (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) x U))))) -> (T2Space.{u1} G _inst_2)
Case conversion may be inaccurate. Consider using '#align topological_group.t2_space_of_one_sep TopologicalGroup.t2Space_of_one_sepₓ'. -/
@[to_additive]
theorem TopologicalGroup.t2Space_of_one_sep (H : ∀ x : G, x ≠ 1 → ∃ U ∈ nhds (1 : G), x ∉ U) :
    T2Space G :=
  by
  rw [TopologicalGroup.t2Space_iff_one_closed, ← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x x_not
  have : x ≠ 1 := mem_compl_singleton_iff.mp x_not
  rcases H x this with ⟨U, U_in, xU⟩
  rw [← nhds_one_symm G] at U_in
  rcases U_in with ⟨W, W_in, UW⟩
  rw [← nhds_translation_mul_inv]
  use W, W_in
  rw [subset_compl_comm]
  suffices x⁻¹ ∉ W by simpa
  exact fun h => xU (UW h)
#align topological_group.t2_space_of_one_sep TopologicalGroup.t2Space_of_one_sep
#align topological_add_group.t2_space_of_zero_sep TopologicalAddGroup.t2Space_of_zero_sep

end

#print UniformGroup.toUniformSpace_eq /-
@[to_additive]
theorem UniformGroup.toUniformSpace_eq {G : Type _} [u : UniformSpace G] [Group G]
    [UniformGroup G] : TopologicalGroup.toUniformSpace G = u :=
  by
  ext : 1
  rw [uniformity_eq_comap_nhds_one' G, uniformity_eq_comap_nhds_one G]
#align uniform_group.to_uniform_space_eq UniformGroup.toUniformSpace_eq
#align uniform_add_group.to_uniform_space_eq UniformAddGroup.toUniformSpace_eq
-/

end TopologicalCommGroup

open Filter Set Function

section

variable {α : Type _} {β : Type _} {hom : Type _}

variable [TopologicalSpace α] [Group α] [TopologicalGroup α]

-- β is a dense subgroup of α, inclusion is denoted by e
variable [TopologicalSpace β] [Group β]

variable [MonoidHomClass hom β α] {e : hom} (de : DenseInducing e)

include de

/- warning: tendsto_div_comap_self -> tendsto_div_comap_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {hom : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : TopologicalGroup.{u1} α _inst_1 _inst_2] [_inst_4 : TopologicalSpace.{u2} β] [_inst_5 : Group.{u2} β] [_inst_6 : MonoidHomClass.{u3, u2, u1} hom β α (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))] {e : hom}, (DenseInducing.{u2, u1} β α _inst_4 _inst_1 (coeFn.{succ u3, max (succ u2) (succ u1)} hom (fun (_x : hom) => β -> α) (FunLike.hasCoeToFun.{succ u3, succ u2, succ u1} hom β (fun (_x : β) => α) (MulHomClass.toFunLike.{u3, u2, u1} hom β α (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (MonoidHomClass.toMulHomClass.{u3, u2, u1} hom β α (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) _inst_6))) e)) -> (forall (x₀ : α), Filter.Tendsto.{u2, u2} (Prod.{u2, u2} β β) β (fun (t : Prod.{u2, u2} β β) => HDiv.hDiv.{u2, u2, u2} β β β (instHDiv.{u2} β (DivInvMonoid.toHasDiv.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5))) (Prod.snd.{u2, u2} β β t) (Prod.fst.{u2, u2} β β t)) (Filter.comap.{u2, u1} (Prod.{u2, u2} β β) (Prod.{u1, u1} α α) (fun (p : Prod.{u2, u2} β β) => Prod.mk.{u1, u1} α α (coeFn.{succ u3, max (succ u2) (succ u1)} hom (fun (_x : hom) => β -> α) (FunLike.hasCoeToFun.{succ u3, succ u2, succ u1} hom β (fun (_x : β) => α) (MulHomClass.toFunLike.{u3, u2, u1} hom β α (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (MonoidHomClass.toMulHomClass.{u3, u2, u1} hom β α (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) _inst_6))) e (Prod.fst.{u2, u2} β β p)) (coeFn.{succ u3, max (succ u2) (succ u1)} hom (fun (_x : hom) => β -> α) (FunLike.hasCoeToFun.{succ u3, succ u2, succ u1} hom β (fun (_x : β) => α) (MulHomClass.toFunLike.{u3, u2, u1} hom β α (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (MonoidHomClass.toMulHomClass.{u3, u2, u1} hom β α (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))) _inst_6))) e (Prod.snd.{u2, u2} β β p))) (nhds.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α _inst_1 _inst_1) (Prod.mk.{u1, u1} α α x₀ x₀))) (nhds.{u2} β _inst_4 (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_5)))))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {hom : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Group.{u2} α] [_inst_3 : TopologicalGroup.{u2} α _inst_1 _inst_2] [_inst_4 : TopologicalSpace.{u3} β] [_inst_5 : Group.{u3} β] [_inst_6 : MonoidHomClass.{u1, u3, u2} hom β α (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (Group.toDivInvMonoid.{u3} β _inst_5))) (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2)))] {e : hom}, (DenseInducing.{u3, u2} β α _inst_4 _inst_1 (FunLike.coe.{succ u1, succ u3, succ u2} hom β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : β) => α) _x) (MulHomClass.toFunLike.{u1, u3, u2} hom β α (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (Group.toDivInvMonoid.{u3} β _inst_5)))) (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} hom β α (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (Group.toDivInvMonoid.{u3} β _inst_5))) (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2))) _inst_6)) e)) -> (forall (x₀ : α), Filter.Tendsto.{u3, u3} (Prod.{u3, u3} β β) β (fun (t : Prod.{u3, u3} β β) => HDiv.hDiv.{u3, u3, u3} β β β (instHDiv.{u3} β (DivInvMonoid.toDiv.{u3} β (Group.toDivInvMonoid.{u3} β _inst_5))) (Prod.snd.{u3, u3} β β t) (Prod.fst.{u3, u3} β β t)) (Filter.comap.{u3, u2} (Prod.{u3, u3} β β) (Prod.{u2, u2} α α) (fun (p : Prod.{u3, u3} β β) => Prod.mk.{u2, u2} α α (FunLike.coe.{succ u1, succ u3, succ u2} hom β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : β) => α) _x) (MulHomClass.toFunLike.{u1, u3, u2} hom β α (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (Group.toDivInvMonoid.{u3} β _inst_5)))) (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} hom β α (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (Group.toDivInvMonoid.{u3} β _inst_5))) (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2))) _inst_6)) e (Prod.fst.{u3, u3} β β p)) (FunLike.coe.{succ u1, succ u3, succ u2} hom β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : β) => α) _x) (MulHomClass.toFunLike.{u1, u3, u2} hom β α (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (Group.toDivInvMonoid.{u3} β _inst_5)))) (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} hom β α (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (Group.toDivInvMonoid.{u3} β _inst_5))) (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_2))) _inst_6)) e (Prod.snd.{u3, u3} β β p))) (nhds.{u2} (Prod.{u2, u2} α α) (instTopologicalSpaceProd.{u2, u2} α α _inst_1 _inst_1) (Prod.mk.{u2, u2} α α x₀ x₀))) (nhds.{u3} β _inst_4 (OfNat.ofNat.{u3} β 1 (One.toOfNat1.{u3} β (InvOneClass.toOne.{u3} β (DivInvOneMonoid.toInvOneClass.{u3} β (DivisionMonoid.toDivInvOneMonoid.{u3} β (Group.toDivisionMonoid.{u3} β _inst_5))))))))
Case conversion may be inaccurate. Consider using '#align tendsto_div_comap_self tendsto_div_comap_selfₓ'. -/
@[to_additive]
theorem tendsto_div_comap_self (x₀ : α) :
    Tendsto (fun t : β × β => t.2 / t.1) ((comap fun p : β × β => (e p.1, e p.2)) <| 𝓝 (x₀, x₀))
      (𝓝 1) :=
  by
  have comm :
    ((fun x : α × α => x.2 / x.1) ∘ fun t : β × β => (e t.1, e t.2)) =
      e ∘ fun t : β × β => t.2 / t.1 :=
    by
    ext t
    change e t.2 / e t.1 = e (t.2 / t.1)
    rwa [← map_div e t.2 t.1]
  have lim : tendsto (fun x : α × α => x.2 / x.1) (𝓝 (x₀, x₀)) (𝓝 (e 1)) := by
    simpa using (continuous_div'.comp (@continuous_swap α α _ _)).Tendsto (x₀, x₀)
  simpa using de.tendsto_comap_nhds_nhds limUnder comm
#align tendsto_div_comap_self tendsto_div_comap_self
#align tendsto_sub_comap_self tendsto_sub_comap_self

end

namespace DenseInducing

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

variable {G : Type _}

-- β is a dense subgroup of α, inclusion is denoted by e
-- δ is a dense subgroup of γ, inclusion is denoted by f
variable [TopologicalSpace α] [AddCommGroup α] [TopologicalAddGroup α]

variable [TopologicalSpace β] [AddCommGroup β] [TopologicalAddGroup β]

variable [TopologicalSpace γ] [AddCommGroup γ] [TopologicalAddGroup γ]

variable [TopologicalSpace δ] [AddCommGroup δ] [TopologicalAddGroup δ]

variable [UniformSpace G] [AddCommGroup G] [UniformAddGroup G] [SeparatedSpace G] [CompleteSpace G]

variable {e : β →+ α} (de : DenseInducing e)

variable {f : δ →+ γ} (df : DenseInducing f)

variable {φ : β →+ δ →+ G}

-- mathport name: exprΦ
local notation "Φ" => fun p : β × δ => φ p.1 p.2

variable (hφ : Continuous Φ)

include de df hφ

variable {W' : Set G} (W'_nhd : W' ∈ 𝓝 (0 : G))

include W'_nhd

/- warning: dense_inducing.extend_Z_bilin_aux clashes with [anonymous] -> [anonymous]
Case conversion may be inaccurate. Consider using '#align dense_inducing.extend_Z_bilin_aux [anonymous]ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x x' «expr ∈ » U₂) -/
#print [anonymous] /-
private theorem [anonymous] (x₀ : α) (y₁ : δ) :
    ∃ U₂ ∈ comap e (𝓝 x₀), ∀ (x) (_ : x ∈ U₂) (x') (_ : x' ∈ U₂), Φ (x' - x, y₁) ∈ W' :=
  by
  let Nx := 𝓝 x₀
  let ee := fun u : β × β => (e u.1, e u.2)
  have lim1 : tendsto (fun a : β × β => (a.2 - a.1, y₁)) (comap e Nx ×ᶠ comap e Nx) (𝓝 (0, y₁)) :=
    by
    have :=
      tendsto.prod_mk (tendsto_sub_comap_self de x₀)
        (tendsto_const_nhds : tendsto (fun p : β × β => y₁) (comap ee <| 𝓝 (x₀, x₀)) (𝓝 y₁))
    rw [nhds_prod_eq, prod_comap_comap_eq, ← nhds_prod_eq]
    exact (this : _)
  have lim2 : tendsto Φ (𝓝 (0, y₁)) (𝓝 0) := by simpa using hφ.tendsto (0, y₁)
  have lim := lim2.comp lim1
  rw [tendsto_prod_self_iff] at lim
  simp_rw [ball_mem_comm]
  exact limUnder W' W'_nhd
#align dense_inducing.extend_Z_bilin_aux [anonymous]
-/

/- warning: dense_inducing.extend_Z_bilin_key clashes with [anonymous] -> [anonymous]
Case conversion may be inaccurate. Consider using '#align dense_inducing.extend_Z_bilin_key [anonymous]ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x x' «expr ∈ » U₁) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (y y' «expr ∈ » V₁) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x x' «expr ∈ » U) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (y y' «expr ∈ » V) -/
#print [anonymous] /-
private theorem [anonymous] (x₀ : α) (y₀ : γ) :
    ∃ U ∈ comap e (𝓝 x₀),
      ∃ V ∈ comap f (𝓝 y₀),
        ∀ (x) (_ : x ∈ U) (x') (_ : x' ∈ U),
          ∀ (y) (_ : y ∈ V) (y') (_ : y' ∈ V), Φ (x', y') - Φ (x, y) ∈ W' :=
  by
  let Nx := 𝓝 x₀
  let Ny := 𝓝 y₀
  let dp := DenseInducing.prod de df
  let ee := fun u : β × β => (e u.1, e u.2)
  let ff := fun u : δ × δ => (f u.1, f u.2)
  have lim_φ : Filter.Tendsto Φ (𝓝 (0, 0)) (𝓝 0) := by simpa using hφ.tendsto (0, 0)
  have lim_φ_sub_sub :
    tendsto (fun p : (β × β) × δ × δ => Φ (p.1.2 - p.1.1, p.2.2 - p.2.1))
      ((comap ee <| 𝓝 (x₀, x₀)) ×ᶠ (comap ff <| 𝓝 (y₀, y₀))) (𝓝 0) :=
    by
    have lim_sub_sub :
      tendsto (fun p : (β × β) × δ × δ => (p.1.2 - p.1.1, p.2.2 - p.2.1))
        (comap ee (𝓝 (x₀, x₀)) ×ᶠ comap ff (𝓝 (y₀, y₀))) (𝓝 0 ×ᶠ 𝓝 0) :=
      by
      have := Filter.prod_mono (tendsto_sub_comap_self de x₀) (tendsto_sub_comap_self df y₀)
      rwa [prod_map_map_eq] at this
    rw [← nhds_prod_eq] at lim_sub_sub
    exact tendsto.comp lim_φ lim_sub_sub
  rcases exists_nhds_zero_quarter W'_nhd with ⟨W, W_nhd, W4⟩
  have :
    ∃ U₁ ∈ comap e (𝓝 x₀),
      ∃ V₁ ∈ comap f (𝓝 y₀),
        ∀ (x) (_ : x ∈ U₁) (x') (_ : x' ∈ U₁),
          ∀ (y) (_ : y ∈ V₁) (y') (_ : y' ∈ V₁), Φ (x' - x, y' - y) ∈ W :=
    by
    have := tendsto_prod_iff.1 lim_φ_sub_sub W W_nhd
    repeat' rw [nhds_prod_eq, ← prod_comap_comap_eq] at this
    rcases this with ⟨U, U_in, V, V_in, H⟩
    rw [mem_prod_same_iff] at U_in V_in
    rcases U_in with ⟨U₁, U₁_in, HU₁⟩
    rcases V_in with ⟨V₁, V₁_in, HV₁⟩
    exists U₁, U₁_in, V₁, V₁_in
    intro x x_in x' x'_in y y_in y' y'_in
    exact H _ _ (HU₁ (mk_mem_prod x_in x'_in)) (HV₁ (mk_mem_prod y_in y'_in))
  rcases this with ⟨U₁, U₁_nhd, V₁, V₁_nhd, H⟩
  obtain ⟨x₁, x₁_in⟩ : U₁.nonempty := (de.comap_nhds_ne_bot _).nonempty_of_mem U₁_nhd
  obtain ⟨y₁, y₁_in⟩ : V₁.nonempty := (df.comap_nhds_ne_bot _).nonempty_of_mem V₁_nhd
  have cont_flip : Continuous fun p : δ × β => φ.flip p.1 p.2 :=
    by
    show Continuous (Φ ∘ Prod.swap)
    exact hφ.comp continuous_swap
  rcases extend_Z_bilin_aux de df hφ W_nhd x₀ y₁ with ⟨U₂, U₂_nhd, HU⟩
  rcases extend_Z_bilin_aux df de cont_flip W_nhd y₀ x₁ with ⟨V₂, V₂_nhd, HV⟩
  exists U₁ ∩ U₂, inter_mem U₁_nhd U₂_nhd, V₁ ∩ V₂, inter_mem V₁_nhd V₂_nhd
  rintro x ⟨xU₁, xU₂⟩ x' ⟨x'U₁, x'U₂⟩ y ⟨yV₁, yV₂⟩ y' ⟨y'V₁, y'V₂⟩
  have key_formula :
    φ x' y' - φ x y = φ (x' - x) y₁ + φ (x' - x) (y' - y₁) + φ x₁ (y' - y) + φ (x - x₁) (y' - y) :=
    by
    simp
    abel
  rw [key_formula]
  have h₁ := HU x xU₂ x' x'U₂
  have h₂ := H x xU₁ x' x'U₁ y₁ y₁_in y' y'V₁
  have h₃ := HV y yV₂ y' y'V₂
  have h₄ := H x₁ x₁_in x xU₁ y yV₁ y' y'V₁
  exact W4 h₁ h₂ h₃ h₄
#align dense_inducing.extend_Z_bilin_key [anonymous]
-/

omit W'_nhd

open DenseInducing

/- warning: dense_inducing.extend_Z_bilin -> DenseInducing.extend_Z_bilin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {G : Type.{u5}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : AddCommGroup.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_1 (AddCommGroup.toAddGroup.{u1} α _inst_2)] [_inst_4 : TopologicalSpace.{u2} β] [_inst_5 : AddCommGroup.{u2} β] [_inst_6 : TopologicalAddGroup.{u2} β _inst_4 (AddCommGroup.toAddGroup.{u2} β _inst_5)] [_inst_7 : TopologicalSpace.{u3} γ] [_inst_8 : AddCommGroup.{u3} γ] [_inst_9 : TopologicalAddGroup.{u3} γ _inst_7 (AddCommGroup.toAddGroup.{u3} γ _inst_8)] [_inst_10 : TopologicalSpace.{u4} δ] [_inst_11 : AddCommGroup.{u4} δ] [_inst_12 : TopologicalAddGroup.{u4} δ _inst_10 (AddCommGroup.toAddGroup.{u4} δ _inst_11)] [_inst_13 : UniformSpace.{u5} G] [_inst_14 : AddCommGroup.{u5} G] [_inst_15 : UniformAddGroup.{u5} G _inst_13 (AddCommGroup.toAddGroup.{u5} G _inst_14)] [_inst_16 : SeparatedSpace.{u5} G _inst_13] [_inst_17 : CompleteSpace.{u5} G _inst_13] {e : AddMonoidHom.{u2, u1} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_2))))} (de : DenseInducing.{u2, u1} β α _inst_4 _inst_1 (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (AddMonoidHom.{u2, u1} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_2))))) (fun (_x : AddMonoidHom.{u2, u1} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_2))))) => β -> α) (AddMonoidHom.hasCoeToFun.{u2, u1} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_2))))) e)) {f : AddMonoidHom.{u4, u3} δ γ (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u3} γ (SubNegMonoid.toAddMonoid.{u3} γ (AddGroup.toSubNegMonoid.{u3} γ (AddCommGroup.toAddGroup.{u3} γ _inst_8))))} (df : DenseInducing.{u4, u3} δ γ _inst_10 _inst_7 (coeFn.{max (succ u3) (succ u4), max (succ u4) (succ u3)} (AddMonoidHom.{u4, u3} δ γ (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u3} γ (SubNegMonoid.toAddMonoid.{u3} γ (AddGroup.toSubNegMonoid.{u3} γ (AddCommGroup.toAddGroup.{u3} γ _inst_8))))) (fun (_x : AddMonoidHom.{u4, u3} δ γ (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u3} γ (SubNegMonoid.toAddMonoid.{u3} γ (AddGroup.toSubNegMonoid.{u3} γ (AddCommGroup.toAddGroup.{u3} γ _inst_8))))) => δ -> γ) (AddMonoidHom.hasCoeToFun.{u4, u3} δ γ (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u3} γ (SubNegMonoid.toAddMonoid.{u3} γ (AddGroup.toSubNegMonoid.{u3} γ (AddCommGroup.toAddGroup.{u3} γ _inst_8))))) f)) {φ : AddMonoidHom.{u2, max u5 u4} β (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (SubNegMonoid.toAddMonoid.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddGroup.toSubNegMonoid.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddCommGroup.toAddGroup.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddMonoidHom.addCommGroup.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) _inst_14)))))}, (Continuous.{max u2 u4, u5} (Prod.{u2, u4} β δ) G (Prod.topologicalSpace.{u2, u4} β δ _inst_4 _inst_10) (UniformSpace.toTopologicalSpace.{u5} G _inst_13) (fun (p : Prod.{u2, u4} β δ) => coeFn.{max (succ u5) (succ u4), max (succ u4) (succ u5)} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (fun (_x : AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) => δ -> G) (AddMonoidHom.hasCoeToFun.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (coeFn.{max (succ (max u5 u4)) (succ u2), max (succ u2) (succ (max u5 u4))} (AddMonoidHom.{u2, max u5 u4} β (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (SubNegMonoid.toAddMonoid.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddGroup.toSubNegMonoid.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddCommGroup.toAddGroup.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddMonoidHom.addCommGroup.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) _inst_14)))))) (fun (_x : AddMonoidHom.{u2, max u5 u4} β (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (SubNegMonoid.toAddMonoid.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddGroup.toSubNegMonoid.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddCommGroup.toAddGroup.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddMonoidHom.addCommGroup.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) _inst_14)))))) => β -> (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14)))))) (AddMonoidHom.hasCoeToFun.{u2, max u5 u4} β (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (SubNegMonoid.toAddMonoid.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddGroup.toSubNegMonoid.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddCommGroup.toAddGroup.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddMonoidHom.addCommGroup.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) _inst_14)))))) φ (Prod.fst.{u2, u4} β δ p)) (Prod.snd.{u2, u4} β δ p))) -> (Continuous.{max u1 u3, u5} (Prod.{u1, u3} α γ) G (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_7) (UniformSpace.toTopologicalSpace.{u5} G _inst_13) (DenseInducing.extend.{max u2 u4, max u1 u3, u5} (Prod.{u2, u4} β δ) (Prod.{u1, u3} α γ) G (Prod.topologicalSpace.{u2, u4} β δ _inst_4 _inst_10) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_7) (fun (p : Prod.{u2, u4} β δ) => Prod.mk.{u1, u3} α γ (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (AddMonoidHom.{u2, u1} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_2))))) (fun (_x : AddMonoidHom.{u2, u1} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_2))))) => β -> α) (AddMonoidHom.hasCoeToFun.{u2, u1} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_2))))) e (Prod.fst.{u2, u4} β δ p)) (coeFn.{max (succ u3) (succ u4), max (succ u4) (succ u3)} (AddMonoidHom.{u4, u3} δ γ (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u3} γ (SubNegMonoid.toAddMonoid.{u3} γ (AddGroup.toSubNegMonoid.{u3} γ (AddCommGroup.toAddGroup.{u3} γ _inst_8))))) (fun (_x : AddMonoidHom.{u4, u3} δ γ (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u3} γ (SubNegMonoid.toAddMonoid.{u3} γ (AddGroup.toSubNegMonoid.{u3} γ (AddCommGroup.toAddGroup.{u3} γ _inst_8))))) => δ -> γ) (AddMonoidHom.hasCoeToFun.{u4, u3} δ γ (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u3} γ (SubNegMonoid.toAddMonoid.{u3} γ (AddGroup.toSubNegMonoid.{u3} γ (AddCommGroup.toAddGroup.{u3} γ _inst_8))))) f (Prod.snd.{u2, u4} β δ p))) (UniformSpace.toTopologicalSpace.{u5} G _inst_13) (DenseInducing.prod.{u2, u1, u4, u3} β α δ γ _inst_4 _inst_1 _inst_10 _inst_7 (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (AddMonoidHom.{u2, u1} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_2))))) (fun (_x : AddMonoidHom.{u2, u1} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_2))))) => β -> α) (AddMonoidHom.hasCoeToFun.{u2, u1} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_2))))) e) (coeFn.{max (succ u3) (succ u4), max (succ u4) (succ u3)} (AddMonoidHom.{u4, u3} δ γ (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u3} γ (SubNegMonoid.toAddMonoid.{u3} γ (AddGroup.toSubNegMonoid.{u3} γ (AddCommGroup.toAddGroup.{u3} γ _inst_8))))) (fun (_x : AddMonoidHom.{u4, u3} δ γ (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u3} γ (SubNegMonoid.toAddMonoid.{u3} γ (AddGroup.toSubNegMonoid.{u3} γ (AddCommGroup.toAddGroup.{u3} γ _inst_8))))) => δ -> γ) (AddMonoidHom.hasCoeToFun.{u4, u3} δ γ (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u3} γ (SubNegMonoid.toAddMonoid.{u3} γ (AddGroup.toSubNegMonoid.{u3} γ (AddCommGroup.toAddGroup.{u3} γ _inst_8))))) f) de df) (fun (p : Prod.{u2, u4} β δ) => coeFn.{max (succ u5) (succ u4), max (succ u4) (succ u5)} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (fun (_x : AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) => δ -> G) (AddMonoidHom.hasCoeToFun.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (coeFn.{max (succ (max u5 u4)) (succ u2), max (succ u2) (succ (max u5 u4))} (AddMonoidHom.{u2, max u5 u4} β (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (SubNegMonoid.toAddMonoid.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddGroup.toSubNegMonoid.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddCommGroup.toAddGroup.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddMonoidHom.addCommGroup.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) _inst_14)))))) (fun (_x : AddMonoidHom.{u2, max u5 u4} β (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (SubNegMonoid.toAddMonoid.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddGroup.toSubNegMonoid.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddCommGroup.toAddGroup.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddMonoidHom.addCommGroup.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) _inst_14)))))) => β -> (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14)))))) (AddMonoidHom.hasCoeToFun.{u2, max u5 u4} β (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (SubNegMonoid.toAddMonoid.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddGroup.toSubNegMonoid.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddCommGroup.toAddGroup.{max u5 u4} (AddMonoidHom.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (AddCommGroup.toAddGroup.{u5} G _inst_14))))) (AddMonoidHom.addCommGroup.{u4, u5} δ G (AddMonoid.toAddZeroClass.{u4} δ (SubNegMonoid.toAddMonoid.{u4} δ (AddGroup.toSubNegMonoid.{u4} δ (AddCommGroup.toAddGroup.{u4} δ _inst_11)))) _inst_14)))))) φ (Prod.fst.{u2, u4} β δ p)) (Prod.snd.{u2, u4} β δ p))))
but is expected to have type
  forall {α : Type.{u5}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u1}} {G : Type.{u3}} [_inst_1 : TopologicalSpace.{u5} α] [_inst_2 : AddCommGroup.{u5} α] [_inst_3 : TopologicalAddGroup.{u5} α _inst_1 (AddCommGroup.toAddGroup.{u5} α _inst_2)] [_inst_4 : TopologicalSpace.{u2} β] [_inst_5 : AddCommGroup.{u2} β] [_inst_6 : TopologicalSpace.{u4} γ] [_inst_7 : AddCommGroup.{u4} γ] [_inst_8 : TopologicalAddGroup.{u4} γ _inst_6 (AddCommGroup.toAddGroup.{u4} γ _inst_7)] [_inst_9 : TopologicalSpace.{u1} δ] [_inst_10 : AddCommGroup.{u1} δ] [_inst_11 : UniformSpace.{u3} G] [_inst_12 : AddCommGroup.{u3} G] [_inst_13 : UniformAddGroup.{u3} G _inst_11 (AddCommGroup.toAddGroup.{u3} G _inst_12)] [_inst_14 : SeparatedSpace.{u3} G _inst_11] [_inst_15 : CompleteSpace.{u3} G _inst_11] {_inst_16 : AddMonoidHom.{u2, u5} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u5} α (SubNegMonoid.toAddMonoid.{u5} α (AddGroup.toSubNegMonoid.{u5} α (AddCommGroup.toAddGroup.{u5} α _inst_2))))} (_inst_17 : DenseInducing.{u2, u5} β α _inst_4 _inst_1 (FunLike.coe.{max (succ u5) (succ u2), succ u2, succ u5} (AddMonoidHom.{u2, u5} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u5} α (SubNegMonoid.toAddMonoid.{u5} α (AddGroup.toSubNegMonoid.{u5} α (AddCommGroup.toAddGroup.{u5} α _inst_2))))) β (fun (a : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : β) => α) a) (AddHomClass.toFunLike.{max u5 u2, u2, u5} (AddMonoidHom.{u2, u5} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u5} α (SubNegMonoid.toAddMonoid.{u5} α (AddGroup.toSubNegMonoid.{u5} α (AddCommGroup.toAddGroup.{u5} α _inst_2))))) β α (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5))))) (AddZeroClass.toAdd.{u5} α (AddMonoid.toAddZeroClass.{u5} α (SubNegMonoid.toAddMonoid.{u5} α (AddGroup.toSubNegMonoid.{u5} α (AddCommGroup.toAddGroup.{u5} α _inst_2))))) (AddMonoidHomClass.toAddHomClass.{max u5 u2, u2, u5} (AddMonoidHom.{u2, u5} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u5} α (SubNegMonoid.toAddMonoid.{u5} α (AddGroup.toSubNegMonoid.{u5} α (AddCommGroup.toAddGroup.{u5} α _inst_2))))) β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u5} α (SubNegMonoid.toAddMonoid.{u5} α (AddGroup.toSubNegMonoid.{u5} α (AddCommGroup.toAddGroup.{u5} α _inst_2)))) (AddMonoidHom.addMonoidHomClass.{u2, u5} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u5} α (SubNegMonoid.toAddMonoid.{u5} α (AddGroup.toSubNegMonoid.{u5} α (AddCommGroup.toAddGroup.{u5} α _inst_2))))))) _inst_16)) {e : AddMonoidHom.{u1, u4} δ γ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u4} γ (SubNegMonoid.toAddMonoid.{u4} γ (AddGroup.toSubNegMonoid.{u4} γ (AddCommGroup.toAddGroup.{u4} γ _inst_7))))} (de : DenseInducing.{u1, u4} δ γ _inst_9 _inst_6 (FunLike.coe.{max (succ u4) (succ u1), succ u1, succ u4} (AddMonoidHom.{u1, u4} δ γ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u4} γ (SubNegMonoid.toAddMonoid.{u4} γ (AddGroup.toSubNegMonoid.{u4} γ (AddCommGroup.toAddGroup.{u4} γ _inst_7))))) δ (fun (_x : δ) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : δ) => γ) _x) (AddHomClass.toFunLike.{max u4 u1, u1, u4} (AddMonoidHom.{u1, u4} δ γ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u4} γ (SubNegMonoid.toAddMonoid.{u4} γ (AddGroup.toSubNegMonoid.{u4} γ (AddCommGroup.toAddGroup.{u4} γ _inst_7))))) δ γ (AddZeroClass.toAdd.{u1} δ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10))))) (AddZeroClass.toAdd.{u4} γ (AddMonoid.toAddZeroClass.{u4} γ (SubNegMonoid.toAddMonoid.{u4} γ (AddGroup.toSubNegMonoid.{u4} γ (AddCommGroup.toAddGroup.{u4} γ _inst_7))))) (AddMonoidHomClass.toAddHomClass.{max u4 u1, u1, u4} (AddMonoidHom.{u1, u4} δ γ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u4} γ (SubNegMonoid.toAddMonoid.{u4} γ (AddGroup.toSubNegMonoid.{u4} γ (AddCommGroup.toAddGroup.{u4} γ _inst_7))))) δ γ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u4} γ (SubNegMonoid.toAddMonoid.{u4} γ (AddGroup.toSubNegMonoid.{u4} γ (AddCommGroup.toAddGroup.{u4} γ _inst_7)))) (AddMonoidHom.addMonoidHomClass.{u1, u4} δ γ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u4} γ (SubNegMonoid.toAddMonoid.{u4} γ (AddGroup.toSubNegMonoid.{u4} γ (AddCommGroup.toAddGroup.{u4} γ _inst_7))))))) e)) {f : AddMonoidHom.{u2, max u3 u1} β (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (SubNegMonoid.toAddMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddGroup.toSubNegMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddCommGroup.toAddGroup.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoidHom.addCommGroup.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) _inst_12)))))}, (Continuous.{max u2 u1, u3} (Prod.{u2, u1} β δ) G (instTopologicalSpaceProd.{u2, u1} β δ _inst_4 _inst_9) (UniformSpace.toTopologicalSpace.{u3} G _inst_11) (fun (p : Prod.{u2, u1} β δ) => FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : β) => AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (Prod.fst.{u2, u1} β δ p)) δ (fun (a : δ) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : δ) => G) a) (AddHomClass.toFunLike.{max u1 u3, u1, u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : β) => AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (Prod.fst.{u2, u1} β δ p)) δ G (AddZeroClass.toAdd.{u1} δ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10))))) (AddZeroClass.toAdd.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoidHomClass.toAddHomClass.{max u1 u3, u1, u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : β) => AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (Prod.fst.{u2, u1} β δ p)) δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12)))) (AddMonoidHom.addMonoidHomClass.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))))) (FunLike.coe.{max (max (succ u2) (succ u1)) (succ u3), succ u2, max (succ u1) (succ u3)} (AddMonoidHom.{u2, max u3 u1} β (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (SubNegMonoid.toAddMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddGroup.toSubNegMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddCommGroup.toAddGroup.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoidHom.addCommGroup.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) _inst_12)))))) β (fun (a : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : β) => AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) a) (AddHomClass.toFunLike.{max (max u2 u1) u3, u2, max u1 u3} (AddMonoidHom.{u2, max u3 u1} β (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (SubNegMonoid.toAddMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddGroup.toSubNegMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddCommGroup.toAddGroup.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoidHom.addCommGroup.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) _inst_12)))))) β (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5))))) (AddZeroClass.toAdd.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoid.toAddZeroClass.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (SubNegMonoid.toAddMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddGroup.toSubNegMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddCommGroup.toAddGroup.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoidHom.addCommGroup.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) _inst_12)))))) (AddMonoidHomClass.toAddHomClass.{max (max u2 u1) u3, u2, max u1 u3} (AddMonoidHom.{u2, max u3 u1} β (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (SubNegMonoid.toAddMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddGroup.toSubNegMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddCommGroup.toAddGroup.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoidHom.addCommGroup.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) _inst_12)))))) β (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (SubNegMonoid.toAddMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddGroup.toSubNegMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddCommGroup.toAddGroup.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoidHom.addCommGroup.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) _inst_12))))) (AddMonoidHom.addMonoidHomClass.{u2, max u1 u3} β (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (SubNegMonoid.toAddMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddGroup.toSubNegMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddCommGroup.toAddGroup.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoidHom.addCommGroup.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) _inst_12)))))))) f (Prod.fst.{u2, u1} β δ p)) (Prod.snd.{u2, u1} β δ p))) -> (Continuous.{max u5 u4, u3} (Prod.{u5, u4} α γ) G (instTopologicalSpaceProd.{u5, u4} α γ _inst_1 _inst_6) (UniformSpace.toTopologicalSpace.{u3} G _inst_11) (DenseInducing.extend.{max u2 u1, max u5 u4, u3} (Prod.{u2, u1} β δ) (Prod.{u5, u4} α γ) G (instTopologicalSpaceProd.{u2, u1} β δ _inst_4 _inst_9) (instTopologicalSpaceProd.{u5, u4} α γ _inst_1 _inst_6) (fun (p : Prod.{u2, u1} β δ) => Prod.mk.{u5, u4} α γ (FunLike.coe.{max (succ u5) (succ u2), succ u2, succ u5} (AddMonoidHom.{u2, u5} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u5} α (SubNegMonoid.toAddMonoid.{u5} α (AddGroup.toSubNegMonoid.{u5} α (AddCommGroup.toAddGroup.{u5} α _inst_2))))) β (fun (a : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : β) => α) a) (AddHomClass.toFunLike.{max u5 u2, u2, u5} (AddMonoidHom.{u2, u5} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u5} α (SubNegMonoid.toAddMonoid.{u5} α (AddGroup.toSubNegMonoid.{u5} α (AddCommGroup.toAddGroup.{u5} α _inst_2))))) β α (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5))))) (AddZeroClass.toAdd.{u5} α (AddMonoid.toAddZeroClass.{u5} α (SubNegMonoid.toAddMonoid.{u5} α (AddGroup.toSubNegMonoid.{u5} α (AddCommGroup.toAddGroup.{u5} α _inst_2))))) (AddMonoidHomClass.toAddHomClass.{max u5 u2, u2, u5} (AddMonoidHom.{u2, u5} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u5} α (SubNegMonoid.toAddMonoid.{u5} α (AddGroup.toSubNegMonoid.{u5} α (AddCommGroup.toAddGroup.{u5} α _inst_2))))) β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u5} α (SubNegMonoid.toAddMonoid.{u5} α (AddGroup.toSubNegMonoid.{u5} α (AddCommGroup.toAddGroup.{u5} α _inst_2)))) (AddMonoidHom.addMonoidHomClass.{u2, u5} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u5} α (SubNegMonoid.toAddMonoid.{u5} α (AddGroup.toSubNegMonoid.{u5} α (AddCommGroup.toAddGroup.{u5} α _inst_2))))))) _inst_16 (Prod.fst.{u2, u1} β δ p)) (FunLike.coe.{max (succ u4) (succ u1), succ u1, succ u4} (AddMonoidHom.{u1, u4} δ γ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u4} γ (SubNegMonoid.toAddMonoid.{u4} γ (AddGroup.toSubNegMonoid.{u4} γ (AddCommGroup.toAddGroup.{u4} γ _inst_7))))) δ (fun (a : δ) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : δ) => γ) a) (AddHomClass.toFunLike.{max u4 u1, u1, u4} (AddMonoidHom.{u1, u4} δ γ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u4} γ (SubNegMonoid.toAddMonoid.{u4} γ (AddGroup.toSubNegMonoid.{u4} γ (AddCommGroup.toAddGroup.{u4} γ _inst_7))))) δ γ (AddZeroClass.toAdd.{u1} δ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10))))) (AddZeroClass.toAdd.{u4} γ (AddMonoid.toAddZeroClass.{u4} γ (SubNegMonoid.toAddMonoid.{u4} γ (AddGroup.toSubNegMonoid.{u4} γ (AddCommGroup.toAddGroup.{u4} γ _inst_7))))) (AddMonoidHomClass.toAddHomClass.{max u4 u1, u1, u4} (AddMonoidHom.{u1, u4} δ γ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u4} γ (SubNegMonoid.toAddMonoid.{u4} γ (AddGroup.toSubNegMonoid.{u4} γ (AddCommGroup.toAddGroup.{u4} γ _inst_7))))) δ γ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u4} γ (SubNegMonoid.toAddMonoid.{u4} γ (AddGroup.toSubNegMonoid.{u4} γ (AddCommGroup.toAddGroup.{u4} γ _inst_7)))) (AddMonoidHom.addMonoidHomClass.{u1, u4} δ γ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u4} γ (SubNegMonoid.toAddMonoid.{u4} γ (AddGroup.toSubNegMonoid.{u4} γ (AddCommGroup.toAddGroup.{u4} γ _inst_7))))))) e (Prod.snd.{u2, u1} β δ p))) (UniformSpace.toTopologicalSpace.{u3} G _inst_11) (DenseInducing.prod.{u5, u2, u4, u1} β α δ γ _inst_4 _inst_1 _inst_9 _inst_6 (FunLike.coe.{max (succ u5) (succ u2), succ u2, succ u5} (AddMonoidHom.{u2, u5} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u5} α (SubNegMonoid.toAddMonoid.{u5} α (AddGroup.toSubNegMonoid.{u5} α (AddCommGroup.toAddGroup.{u5} α _inst_2))))) β (fun (a : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : β) => α) a) (AddHomClass.toFunLike.{max u5 u2, u2, u5} (AddMonoidHom.{u2, u5} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u5} α (SubNegMonoid.toAddMonoid.{u5} α (AddGroup.toSubNegMonoid.{u5} α (AddCommGroup.toAddGroup.{u5} α _inst_2))))) β α (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5))))) (AddZeroClass.toAdd.{u5} α (AddMonoid.toAddZeroClass.{u5} α (SubNegMonoid.toAddMonoid.{u5} α (AddGroup.toSubNegMonoid.{u5} α (AddCommGroup.toAddGroup.{u5} α _inst_2))))) (AddMonoidHomClass.toAddHomClass.{max u5 u2, u2, u5} (AddMonoidHom.{u2, u5} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u5} α (SubNegMonoid.toAddMonoid.{u5} α (AddGroup.toSubNegMonoid.{u5} α (AddCommGroup.toAddGroup.{u5} α _inst_2))))) β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u5} α (SubNegMonoid.toAddMonoid.{u5} α (AddGroup.toSubNegMonoid.{u5} α (AddCommGroup.toAddGroup.{u5} α _inst_2)))) (AddMonoidHom.addMonoidHomClass.{u2, u5} β α (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{u5} α (SubNegMonoid.toAddMonoid.{u5} α (AddGroup.toSubNegMonoid.{u5} α (AddCommGroup.toAddGroup.{u5} α _inst_2))))))) _inst_16) (FunLike.coe.{max (succ u4) (succ u1), succ u1, succ u4} (AddMonoidHom.{u1, u4} δ γ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u4} γ (SubNegMonoid.toAddMonoid.{u4} γ (AddGroup.toSubNegMonoid.{u4} γ (AddCommGroup.toAddGroup.{u4} γ _inst_7))))) δ (fun (a : δ) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : δ) => γ) a) (AddHomClass.toFunLike.{max u4 u1, u1, u4} (AddMonoidHom.{u1, u4} δ γ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u4} γ (SubNegMonoid.toAddMonoid.{u4} γ (AddGroup.toSubNegMonoid.{u4} γ (AddCommGroup.toAddGroup.{u4} γ _inst_7))))) δ γ (AddZeroClass.toAdd.{u1} δ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10))))) (AddZeroClass.toAdd.{u4} γ (AddMonoid.toAddZeroClass.{u4} γ (SubNegMonoid.toAddMonoid.{u4} γ (AddGroup.toSubNegMonoid.{u4} γ (AddCommGroup.toAddGroup.{u4} γ _inst_7))))) (AddMonoidHomClass.toAddHomClass.{max u4 u1, u1, u4} (AddMonoidHom.{u1, u4} δ γ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u4} γ (SubNegMonoid.toAddMonoid.{u4} γ (AddGroup.toSubNegMonoid.{u4} γ (AddCommGroup.toAddGroup.{u4} γ _inst_7))))) δ γ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u4} γ (SubNegMonoid.toAddMonoid.{u4} γ (AddGroup.toSubNegMonoid.{u4} γ (AddCommGroup.toAddGroup.{u4} γ _inst_7)))) (AddMonoidHom.addMonoidHomClass.{u1, u4} δ γ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u4} γ (SubNegMonoid.toAddMonoid.{u4} γ (AddGroup.toSubNegMonoid.{u4} γ (AddCommGroup.toAddGroup.{u4} γ _inst_7))))))) e) _inst_17 de) (fun (p : Prod.{u2, u1} β δ) => FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : β) => AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (Prod.fst.{u2, u1} β δ p)) δ (fun (a : δ) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : δ) => G) a) (AddHomClass.toFunLike.{max u1 u3, u1, u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : β) => AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (Prod.fst.{u2, u1} β δ p)) δ G (AddZeroClass.toAdd.{u1} δ (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10))))) (AddZeroClass.toAdd.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoidHomClass.toAddHomClass.{max u1 u3, u1, u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : β) => AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (Prod.fst.{u2, u1} β δ p)) δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12)))) (AddMonoidHom.addMonoidHomClass.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))))) (FunLike.coe.{max (max (succ u2) (succ u1)) (succ u3), succ u2, max (succ u1) (succ u3)} (AddMonoidHom.{u2, max u3 u1} β (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (SubNegMonoid.toAddMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddGroup.toSubNegMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddCommGroup.toAddGroup.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoidHom.addCommGroup.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) _inst_12)))))) β (fun (a : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : β) => AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) a) (AddHomClass.toFunLike.{max (max u2 u1) u3, u2, max u1 u3} (AddMonoidHom.{u2, max u3 u1} β (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (SubNegMonoid.toAddMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddGroup.toSubNegMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddCommGroup.toAddGroup.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoidHom.addCommGroup.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) _inst_12)))))) β (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5))))) (AddZeroClass.toAdd.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoid.toAddZeroClass.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (SubNegMonoid.toAddMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddGroup.toSubNegMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddCommGroup.toAddGroup.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoidHom.addCommGroup.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) _inst_12)))))) (AddMonoidHomClass.toAddHomClass.{max (max u2 u1) u3, u2, max u1 u3} (AddMonoidHom.{u2, max u3 u1} β (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (SubNegMonoid.toAddMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddGroup.toSubNegMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddCommGroup.toAddGroup.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoidHom.addCommGroup.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) _inst_12)))))) β (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (SubNegMonoid.toAddMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddGroup.toSubNegMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddCommGroup.toAddGroup.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoidHom.addCommGroup.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) _inst_12))))) (AddMonoidHom.addMonoidHomClass.{u2, max u1 u3} β (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_5)))) (AddMonoid.toAddZeroClass.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (SubNegMonoid.toAddMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddGroup.toSubNegMonoid.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddCommGroup.toAddGroup.{max u1 u3} (AddMonoidHom.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (AddCommGroup.toAddGroup.{u3} G _inst_12))))) (AddMonoidHom.addCommGroup.{u1, u3} δ G (AddMonoid.toAddZeroClass.{u1} δ (SubNegMonoid.toAddMonoid.{u1} δ (AddGroup.toSubNegMonoid.{u1} δ (AddCommGroup.toAddGroup.{u1} δ _inst_10)))) _inst_12)))))))) f (Prod.fst.{u2, u1} β δ p)) (Prod.snd.{u2, u1} β δ p))))
Case conversion may be inaccurate. Consider using '#align dense_inducing.extend_Z_bilin DenseInducing.extend_Z_bilinₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Bourbaki GT III.6.5 Theorem I:
ℤ-bilinear continuous maps from dense images into a complete Hausdorff group extend by continuity.
Note: Bourbaki assumes that α and β are also complete Hausdorff, but this is not necessary. -/
theorem extend_Z_bilin : Continuous (extend (de.Prod df) Φ) :=
  by
  refine' continuous_extend_of_cauchy _ _
  rintro ⟨x₀, y₀⟩
  constructor
  · apply ne_bot.map
    apply comap_ne_bot
    intro U h
    rcases mem_closure_iff_nhds.1 ((de.prod df).dense (x₀, y₀)) U h with ⟨x, x_in, ⟨z, z_x⟩⟩
    exists z
    cc
  · suffices
      map (fun p : (β × δ) × β × δ => Φ p.2 - Φ p.1)
          (comap (fun p : (β × δ) × β × δ => ((e p.1.1, f p.1.2), (e p.2.1, f p.2.2)))
            (𝓝 (x₀, y₀) ×ᶠ 𝓝 (x₀, y₀))) ≤
        𝓝 0
      by
      rwa [uniformity_eq_comap_nhds_zero G, prod_map_map_eq, ← map_le_iff_le_comap, Filter.map_map,
        prod_comap_comap_eq]
    intro W' W'_nhd
    have key := extend_Z_bilin_key de df hφ W'_nhd x₀ y₀
    rcases key with ⟨U, U_nhd, V, V_nhd, h⟩
    rw [mem_comap] at U_nhd
    rcases U_nhd with ⟨U', U'_nhd, U'_sub⟩
    rw [mem_comap] at V_nhd
    rcases V_nhd with ⟨V', V'_nhd, V'_sub⟩
    rw [mem_map, mem_comap, nhds_prod_eq]
    exists (U' ×ˢ V') ×ˢ U' ×ˢ V'
    rw [mem_prod_same_iff]
    simp only [exists_prop]
    constructor
    · change U' ∈ 𝓝 x₀ at U'_nhd
      change V' ∈ 𝓝 y₀ at V'_nhd
      have := prod_mem_prod U'_nhd V'_nhd
      tauto
    · intro p h'
      simp only [Set.mem_preimage, Set.prod_mk_mem_set_prod_eq] at h'
      rcases p with ⟨⟨x, y⟩, ⟨x', y'⟩⟩
      apply h <;> tauto
#align dense_inducing.extend_Z_bilin DenseInducing.extend_Z_bilin

end DenseInducing

section CompleteQuotient

universe u

open TopologicalSpace Classical

#print QuotientGroup.completeSpace' /-
/-- The quotient `G ⧸ N` of a complete first countable topological group `G` by a normal subgroup
is itself complete. [N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]

Because a topological group is not equipped with a `uniform_space` instance by default, we must
explicitly provide it in order to consider completeness. See `quotient_group.complete_space` for a
version in which `G` is already equipped with a uniform structure. -/
@[to_additive
      "The quotient `G ⧸ N` of a complete first countable topological additive group\n`G` by a normal additive subgroup is itself complete. Consequently, quotients of Banach spaces by\nsubspaces are complete. [N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]\n\nBecause an additive topological group is not equipped with a `uniform_space` instance by default,\nwe must explicitly provide it in order to consider completeness. See\n`quotient_add_group.complete_space` for a version in which `G` is already equipped with a uniform\nstructure."]
instance QuotientGroup.completeSpace' (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [FirstCountableTopology G] (N : Subgroup G) [N.normal]
    [@CompleteSpace G (TopologicalGroup.toUniformSpace G)] :
    @CompleteSpace (G ⧸ N) (TopologicalGroup.toUniformSpace (G ⧸ N)) :=
  by
  /- Since `G ⧸ N` is a topological group it is a uniform space, and since `G` is first countable
    the uniformities of both `G` and `G ⧸ N` are countably generated. Moreover, we may choose a
    sequential antitone neighborhood basis `u` for `𝓝 (1 : G)` so that `(u (n + 1)) ^ 2 ⊆ u n`, and
    this descends to an antitone neighborhood basis `v` for `𝓝 (1 : G ⧸ N)`. Since `𝓤 (G ⧸ N)` is
    countably generated, it suffices to show any Cauchy sequence `x` converges. -/
  letI : UniformSpace (G ⧸ N) := TopologicalGroup.toUniformSpace (G ⧸ N)
  letI : UniformSpace G := TopologicalGroup.toUniformSpace G
  haveI : (𝓤 (G ⧸ N)).IsCountablyGenerated := comap.is_countably_generated _ _
  obtain ⟨u, hu, u_mul⟩ := TopologicalGroup.exists_antitone_basis_nhds_one G
  obtain ⟨hv, v_anti⟩ := @has_antitone_basis.map _ _ _ _ _ _ (coe : G → G ⧸ N) hu
  rw [← QuotientGroup.nhds_eq N 1, QuotientGroup.mk_one] at hv
  refine' UniformSpace.complete_of_cauchySeq_tendsto fun x hx => _
  /- Given `n : ℕ`, for sufficiently large `a b : ℕ`, given any lift of `x b`, we can find a lift
    of `x a` such that the quotient of the lifts lies in `u n`. -/
  have key₀ :
    ∀ i j : ℕ,
      ∃ M : ℕ,
        j < M ∧ ∀ a b : ℕ, M ≤ a → M ≤ b → ∀ g : G, x b = g → ∃ g' : G, g / g' ∈ u i ∧ x a = g' :=
    by
    have h𝓤GN : (𝓤 (G ⧸ N)).HasBasis (fun _ => True) fun i => { x | x.snd / x.fst ∈ coe '' u i } :=
      by simpa [uniformity_eq_comap_nhds_one'] using hv.comap _
    simp only [h𝓤GN.cauchy_seq_iff, ge_iff_le, mem_set_of_eq, forall_true_left, mem_image] at hx
    intro i j
    rcases hx i with ⟨M, hM⟩
    refine' ⟨max j M + 1, (le_max_left _ _).trans_lt (lt_add_one _), fun a b ha hb g hg => _⟩
    obtain ⟨y, y_mem, hy⟩ :=
      hM a (((le_max_right j _).trans (lt_add_one _).le).trans ha) b
        (((le_max_right j _).trans (lt_add_one _).le).trans hb)
    refine'
      ⟨y⁻¹ * g, by
        simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_cancel_left] using y_mem, _⟩
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy, hg, inv_div, div_mul_cancel']
  /- Inductively construct a subsequence `φ : ℕ → ℕ` using `key₀` so that if `a b : ℕ` exceed
    `φ (n + 1)`, then we may find lifts whose quotients lie within `u n`. -/
  set φ : ℕ → ℕ := fun n => Nat.recOn n (some <| key₀ 0 0) fun k yk => some <| key₀ (k + 1) yk
  have hφ :
    ∀ n : ℕ,
      φ n < φ (n + 1) ∧
        ∀ a b : ℕ,
          φ (n + 1) ≤ a →
            φ (n + 1) ≤ b → ∀ g : G, x b = g → ∃ g' : G, g / g' ∈ u (n + 1) ∧ x a = g' :=
    fun n => some_spec (key₀ (n + 1) (φ n))
  /- Inductively construct a sequence `x' n : G` of lifts of `x (φ (n + 1))` such that quotients of
    successive terms lie in `x' n / x' (n + 1) ∈ u (n + 1)`. We actually need the proofs that each
    term is a lift to construct the next term, so we use a Σ-type. -/
  set x' : ∀ n, PSigma fun g : G => x (φ (n + 1)) = g := fun n =>
    Nat.recOn n
      ⟨some (QuotientGroup.mk_surjective (x (φ 1))),
        (some_spec (QuotientGroup.mk_surjective (x (φ 1)))).symm⟩
      fun k hk =>
      ⟨some <| (hφ k).2 _ _ (hφ (k + 1)).1.le le_rfl hk.fst hk.snd,
        (some_spec <| (hφ k).2 _ _ (hφ (k + 1)).1.le le_rfl hk.fst hk.snd).2⟩
  have hx' : ∀ n : ℕ, (x' n).fst / (x' (n + 1)).fst ∈ u (n + 1) := fun n =>
    (some_spec <| (hφ n).2 _ _ (hφ (n + 1)).1.le le_rfl (x' n).fst (x' n).snd).1
  /- The sequence `x'` is Cauchy. This is where we exploit the condition on `u`. The key idea
    is to show by decreasing induction that `x' m / x' n ∈ u m` if `m ≤ n`. -/
  have x'_cauchy : CauchySeq fun n => (x' n).fst :=
    by
    have h𝓤G : (𝓤 G).HasBasis (fun _ => True) fun i => { x | x.snd / x.fst ∈ u i } := by
      simpa [uniformity_eq_comap_nhds_one'] using hu.to_has_basis.comap _
    simp only [h𝓤G.cauchy_seq_iff', ge_iff_le, mem_set_of_eq, forall_true_left]
    exact fun m =>
      ⟨m, fun n hmn =>
        Nat.decreasingInduction'
          (fun k hkn hkm hk => u_mul k ⟨_, _, hx' k, hk, div_mul_div_cancel' _ _ _⟩) hmn
          (by simpa only [div_self'] using mem_of_mem_nhds (hu.mem _))⟩
  /- Since `G` is complete, `x'` converges to some `x₀`, and so the image of this sequence under
    the quotient map converges to `↑x₀`. The image of `x'` is a convergent subsequence of `x`, and
    since `x` is Cauchy, this implies it converges. -/
  rcases cauchySeq_tendsto_of_complete x'_cauchy with ⟨x₀, hx₀⟩
  refine'
    ⟨↑x₀,
      tendsto_nhds_of_cauchySeq_of_subseq hx
        (strictMono_nat_of_lt_succ fun n => (hφ (n + 1)).1).tendsto_atTop _⟩
  convert ((continuous_coinduced_rng : Continuous (coe : G → G ⧸ N)).Tendsto x₀).comp hx₀
  exact funext fun n => (x' n).snd
#align quotient_group.complete_space' QuotientGroup.completeSpace'
#align quotient_add_group.complete_space' QuotientAddGroup.completeSpace'
-/

#print QuotientGroup.completeSpace /-
/-- The quotient `G ⧸ N` of a complete first countable uniform group `G` by a normal subgroup
is itself complete. In constrast to `quotient_group.complete_space'`, in this version `G` is
already equipped with a uniform structure.
[N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]

Even though `G` is equipped with a uniform structure, the quotient `G ⧸ N` does not inherit a
uniform structure, so it is still provided manually via `topological_group.to_uniform_space`.
In the most common use cases, this coincides (definitionally) with the uniform structure on the
quotient obtained via other means.  -/
@[to_additive
      "The quotient `G ⧸ N` of a complete first countable uniform additive group\n`G` by a normal additive subgroup is itself complete. Consequently, quotients of Banach spaces by\nsubspaces are complete. In constrast to `quotient_add_group.complete_space'`, in this version\n`G` is already equipped with a uniform structure.\n[N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]\n\nEven though `G` is equipped with a uniform structure, the quotient `G ⧸ N` does not inherit a\nuniform structure, so it is still provided manually via `topological_add_group.to_uniform_space`.\nIn the most common use case ─ quotients of normed additive commutative groups by subgroups ─\nsignificant care was taken so that the uniform structure inherent in that setting coincides\n(definitionally) with the uniform structure provided here."]
instance QuotientGroup.completeSpace (G : Type u) [Group G] [us : UniformSpace G] [UniformGroup G]
    [FirstCountableTopology G] (N : Subgroup G) [N.normal] [hG : CompleteSpace G] :
    @CompleteSpace (G ⧸ N) (TopologicalGroup.toUniformSpace (G ⧸ N)) :=
  by
  rw [← @UniformGroup.toUniformSpace_eq _ us _ _] at hG
  infer_instance
#align quotient_group.complete_space QuotientGroup.completeSpace
#align quotient_add_group.complete_space QuotientAddGroup.completeSpace
-/

end CompleteQuotient

