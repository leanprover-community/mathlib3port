/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.algebra.uniform_field
! leanprover-community/mathlib commit 19cb3751e5e9b3d97adb51023949c50c13b5fdfd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.UniformRing
import Mathbin.Topology.Algebra.Field
import Mathbin.FieldTheory.Subfield

/-!
# Completion of topological fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The goal of this file is to prove the main part of Proposition 7 of Bourbaki GT III 6.8 :

The completion `hat K` of a Hausdorff topological field is a field if the image under
the mapping `x ↦ x⁻¹` of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at `0` is a Cauchy filter
(with respect to the additive uniform structure).

Bourbaki does not give any detail here, he refers to the general discussion of extending
functions defined on a dense subset with values in a complete Hausdorff space. In particular
the subtlety about clustering at zero is totally left to readers.

Note that the separated completion of a non-separated topological field is the zero ring, hence
the separation assumption is needed. Indeed the kernel of the completion map is the closure of
zero which is an ideal. Hence it's either zero (and the field is separated) or the full field,
which implies one is sent to zero and the completion ring is trivial.

The main definition is `completable_top_field` which packages the assumptions as a Prop-valued
type class and the main results are the instances `uniform_space.completion.field` and
`uniform_space.completion.topological_division_ring`.
-/


noncomputable section

open Classical uniformity Topology

open Set UniformSpace UniformSpace.Completion Filter

variable (K : Type _) [Field K] [UniformSpace K]

-- mathport name: exprhat
local notation "hat" => Completion

#print CompletableTopField /-
/-- A topological field is completable if it is separated and the image under
the mapping x ↦ x⁻¹ of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at 0 is a Cauchy filter
(with respect to the additive uniform structure). This ensures the completion is
a field.
-/
class CompletableTopField extends SeparatedSpace K : Prop where
  nice : ∀ F : Filter K, Cauchy F → 𝓝 0 ⊓ F = ⊥ → Cauchy (map (fun x => x⁻¹) F)
#align completable_top_field CompletableTopField
-/

namespace UniformSpace

namespace Completion

instance (priority := 100) [SeparatedSpace K] : Nontrivial (hat K) :=
  ⟨⟨0, 1, fun h => zero_ne_one <| (uniformEmbedding_coe K).inj h⟩⟩

variable {K}

#print UniformSpace.Completion.hatInv /-
/-- extension of inversion to the completion of a field. -/
def hatInv : hat K → hat K :=
  denseInducing_coe.extend fun x : K => (coe x⁻¹ : hat K)
#align uniform_space.completion.hat_inv UniformSpace.Completion.hatInv
-/

/- warning: uniform_space.completion.continuous_hat_inv -> UniformSpace.Completion.continuous_hatInv is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : Field.{u1} K] [_inst_2 : UniformSpace.{u1} K] [_inst_3 : CompletableTopField.{u1} K _inst_1 _inst_2] {x : UniformSpace.Completion.{u1} K _inst_2}, (Ne.{succ u1} (UniformSpace.Completion.{u1} K _inst_2) x (OfNat.ofNat.{u1} (UniformSpace.Completion.{u1} K _inst_2) 0 (OfNat.mk.{u1} (UniformSpace.Completion.{u1} K _inst_2) 0 (Zero.zero.{u1} (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.hasZero.{u1} K _inst_2 (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1)))))))))))) -> (ContinuousAt.{u1, u1} (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.toTopologicalSpace.{u1} (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.uniformSpace.{u1} K _inst_2)) (UniformSpace.toTopologicalSpace.{u1} (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.uniformSpace.{u1} K _inst_2)) (UniformSpace.Completion.hatInv.{u1} K _inst_1 _inst_2) x)
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : Field.{u1} K] [_inst_2 : UniformSpace.{u1} K] [_inst_3 : CompletableTopField.{u1} K _inst_1 _inst_2] {x : UniformSpace.Completion.{u1} K _inst_2}, (Ne.{succ u1} (UniformSpace.Completion.{u1} K _inst_2) x (OfNat.ofNat.{u1} (UniformSpace.Completion.{u1} K _inst_2) 0 (Zero.toOfNat0.{u1} (UniformSpace.Completion.{u1} K _inst_2) (instZeroCompletion.{u1} K _inst_2 (CommMonoidWithZero.toZero.{u1} K (CommGroupWithZero.toCommMonoidWithZero.{u1} K (Semifield.toCommGroupWithZero.{u1} K (Field.toSemifield.{u1} K _inst_1)))))))) -> (ContinuousAt.{u1, u1} (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.toTopologicalSpace.{u1} (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.uniformSpace.{u1} K _inst_2)) (UniformSpace.toTopologicalSpace.{u1} (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.uniformSpace.{u1} K _inst_2)) (UniformSpace.Completion.hatInv.{u1} K _inst_1 _inst_2) x)
Case conversion may be inaccurate. Consider using '#align uniform_space.completion.continuous_hat_inv UniformSpace.Completion.continuous_hatInvₓ'. -/
theorem continuous_hatInv [CompletableTopField K] {x : hat K} (h : x ≠ 0) : ContinuousAt hatInv x :=
  by
  haveI : T3Space (hat K) := completion.t3_space K
  refine' dense_inducing_coe.continuous_at_extend _
  apply mem_of_superset (compl_singleton_mem_nhds h)
  intro y y_ne
  rw [mem_compl_singleton_iff] at y_ne
  apply CompleteSpace.complete
  rw [← Filter.map_map]
  apply Cauchy.map _ (completion.uniform_continuous_coe K)
  apply CompletableTopField.nice
  · haveI := dense_inducing_coe.comap_nhds_ne_bot y
    apply cauchy_nhds.comap
    · rw [completion.comap_coe_eq_uniformity]
      exact le_rfl
  · have eq_bot : 𝓝 (0 : hat K) ⊓ 𝓝 y = ⊥ := by
      by_contra h
      exact y_ne (eq_of_nhds_neBot <| ne_bot_iff.mpr h).symm
    erw [dense_inducing_coe.nhds_eq_comap (0 : K), ← Filter.comap_inf, eq_bot]
    exact comap_bot
#align uniform_space.completion.continuous_hat_inv UniformSpace.Completion.continuous_hatInv

/-
The value of `hat_inv` at zero is not really specified, although it's probably zero.
Here we explicitly enforce the `inv_zero` axiom.
-/
instance : Inv (hat K) :=
  ⟨fun x => if x = 0 then 0 else hatInv x⟩

variable [TopologicalDivisionRing K]

/- warning: uniform_space.completion.hat_inv_extends -> UniformSpace.Completion.hatInv_extends is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : Field.{u1} K] [_inst_2 : UniformSpace.{u1} K] [_inst_3 : TopologicalDivisionRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1) (UniformSpace.toTopologicalSpace.{u1} K _inst_2)] {x : K}, (Ne.{succ u1} K x (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))))))))) -> (Eq.{succ u1} (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.hatInv.{u1} K _inst_1 _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) K (UniformSpace.Completion.{u1} K _inst_2) (HasLiftT.mk.{succ u1, succ u1} K (UniformSpace.Completion.{u1} K _inst_2) (CoeTCₓ.coe.{succ u1, succ u1} K (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.hasCoeT.{u1} K _inst_2))) x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) K (UniformSpace.Completion.{u1} K _inst_2) (HasLiftT.mk.{succ u1, succ u1} K (UniformSpace.Completion.{u1} K _inst_2) (CoeTCₓ.coe.{succ u1, succ u1} K (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.hasCoeT.{u1} K _inst_2))) (Inv.inv.{u1} K (DivInvMonoid.toHasInv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K (Field.toDivisionRing.{u1} K _inst_1))) x)))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : Field.{u1} K] [_inst_2 : UniformSpace.{u1} K] [_inst_3 : TopologicalDivisionRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1) (UniformSpace.toTopologicalSpace.{u1} K _inst_2)] {x : K}, (Ne.{succ u1} K x (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (CommMonoidWithZero.toZero.{u1} K (CommGroupWithZero.toCommMonoidWithZero.{u1} K (Semifield.toCommGroupWithZero.{u1} K (Field.toSemifield.{u1} K _inst_1))))))) -> (Eq.{succ u1} (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.hatInv.{u1} K _inst_1 _inst_2 (UniformSpace.Completion.coe'.{u1} K _inst_2 x)) (UniformSpace.Completion.coe'.{u1} K _inst_2 (Inv.inv.{u1} K (Field.toInv.{u1} K _inst_1) x)))
Case conversion may be inaccurate. Consider using '#align uniform_space.completion.hat_inv_extends UniformSpace.Completion.hatInv_extendsₓ'. -/
theorem hatInv_extends {x : K} (h : x ≠ 0) : hatInv (x : hat K) = coe (x⁻¹ : K) :=
  denseInducing_coe.extend_eq_at ((continuous_coe K).ContinuousAt.comp (continuousAt_inv₀ h))
#align uniform_space.completion.hat_inv_extends UniformSpace.Completion.hatInv_extends

variable [CompletableTopField K]

/- warning: uniform_space.completion.coe_inv -> UniformSpace.Completion.coe_inv is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : Field.{u1} K] [_inst_2 : UniformSpace.{u1} K] [_inst_3 : TopologicalDivisionRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1) (UniformSpace.toTopologicalSpace.{u1} K _inst_2)] [_inst_4 : CompletableTopField.{u1} K _inst_1 _inst_2] (x : K), Eq.{succ u1} (UniformSpace.Completion.{u1} K _inst_2) (Inv.inv.{u1} (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.hasInv.{u1} K _inst_1 _inst_2) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) K (UniformSpace.Completion.{u1} K _inst_2) (HasLiftT.mk.{succ u1, succ u1} K (UniformSpace.Completion.{u1} K _inst_2) (CoeTCₓ.coe.{succ u1, succ u1} K (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.hasCoeT.{u1} K _inst_2))) x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) K (UniformSpace.Completion.{u1} K _inst_2) (HasLiftT.mk.{succ u1, succ u1} K (UniformSpace.Completion.{u1} K _inst_2) (CoeTCₓ.coe.{succ u1, succ u1} K (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.hasCoeT.{u1} K _inst_2))) (Inv.inv.{u1} K (DivInvMonoid.toHasInv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K (Field.toDivisionRing.{u1} K _inst_1))) x))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : Field.{u1} K] [_inst_2 : UniformSpace.{u1} K] [_inst_3 : TopologicalDivisionRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1) (UniformSpace.toTopologicalSpace.{u1} K _inst_2)] [_inst_4 : CompletableTopField.{u1} K _inst_1 _inst_2] (x : K), Eq.{succ u1} (UniformSpace.Completion.{u1} K _inst_2) (Inv.inv.{u1} (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.instInvCompletion.{u1} K _inst_1 _inst_2) (UniformSpace.Completion.coe'.{u1} K _inst_2 x)) (UniformSpace.Completion.coe'.{u1} K _inst_2 (Inv.inv.{u1} K (Field.toInv.{u1} K _inst_1) x))
Case conversion may be inaccurate. Consider using '#align uniform_space.completion.coe_inv UniformSpace.Completion.coe_invₓ'. -/
@[norm_cast]
theorem coe_inv (x : K) : (x : hat K)⁻¹ = ((x⁻¹ : K) : hat K) :=
  by
  by_cases h : x = 0
  · rw [h, inv_zero]
    dsimp [Inv.inv]
    norm_cast
    simp
  · conv_lhs => dsimp [Inv.inv]
    rw [if_neg]
    · exact hat_inv_extends h
    · exact fun H => h (dense_embedding_coe.inj H)
#align uniform_space.completion.coe_inv UniformSpace.Completion.coe_inv

variable [UniformAddGroup K]

/- warning: uniform_space.completion.mul_hat_inv_cancel -> UniformSpace.Completion.mul_hatInv_cancel is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : Field.{u1} K] [_inst_2 : UniformSpace.{u1} K] [_inst_3 : TopologicalDivisionRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1) (UniformSpace.toTopologicalSpace.{u1} K _inst_2)] [_inst_4 : CompletableTopField.{u1} K _inst_1 _inst_2] [_inst_5 : UniformAddGroup.{u1} K _inst_2 (AddGroupWithOne.toAddGroup.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1)))))] {x : UniformSpace.Completion.{u1} K _inst_2}, (Ne.{succ u1} (UniformSpace.Completion.{u1} K _inst_2) x (OfNat.ofNat.{u1} (UniformSpace.Completion.{u1} K _inst_2) 0 (OfNat.mk.{u1} (UniformSpace.Completion.{u1} K _inst_2) 0 (Zero.zero.{u1} (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.hasZero.{u1} K _inst_2 (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1)))))))))))) -> (Eq.{succ u1} (UniformSpace.Completion.{u1} K _inst_2) (HMul.hMul.{u1, u1, u1} (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.{u1} K _inst_2) (instHMul.{u1} (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.hasMul.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1)) _inst_2)) x (UniformSpace.Completion.hatInv.{u1} K _inst_1 _inst_2 x)) (OfNat.ofNat.{u1} (UniformSpace.Completion.{u1} K _inst_2) 1 (OfNat.mk.{u1} (UniformSpace.Completion.{u1} K _inst_2) 1 (One.one.{u1} (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.hasOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1)) _inst_2)))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : Field.{u1} K] [_inst_2 : UniformSpace.{u1} K] [_inst_3 : TopologicalDivisionRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1) (UniformSpace.toTopologicalSpace.{u1} K _inst_2)] [_inst_4 : CompletableTopField.{u1} K _inst_1 _inst_2] [_inst_5 : UniformAddGroup.{u1} K _inst_2 (AddGroupWithOne.toAddGroup.{u1} K (Ring.toAddGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))] {x : UniformSpace.Completion.{u1} K _inst_2}, (Ne.{succ u1} (UniformSpace.Completion.{u1} K _inst_2) x (OfNat.ofNat.{u1} (UniformSpace.Completion.{u1} K _inst_2) 0 (Zero.toOfNat0.{u1} (UniformSpace.Completion.{u1} K _inst_2) (instZeroCompletion.{u1} K _inst_2 (CommMonoidWithZero.toZero.{u1} K (CommGroupWithZero.toCommMonoidWithZero.{u1} K (Semifield.toCommGroupWithZero.{u1} K (Field.toSemifield.{u1} K _inst_1)))))))) -> (Eq.{succ u1} (UniformSpace.Completion.{u1} K _inst_2) (HMul.hMul.{u1, u1, u1} (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.{u1} K _inst_2) (instHMul.{u1} (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.mul.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1)) _inst_2)) x (UniformSpace.Completion.hatInv.{u1} K _inst_1 _inst_2 x)) (OfNat.ofNat.{u1} (UniformSpace.Completion.{u1} K _inst_2) 1 (One.toOfNat1.{u1} (UniformSpace.Completion.{u1} K _inst_2) (UniformSpace.Completion.one.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1)) _inst_2))))
Case conversion may be inaccurate. Consider using '#align uniform_space.completion.mul_hat_inv_cancel UniformSpace.Completion.mul_hatInv_cancelₓ'. -/
theorem mul_hatInv_cancel {x : hat K} (x_ne : x ≠ 0) : x * hatInv x = 1 :=
  by
  haveI : T1Space (hat K) := T2Space.t1Space
  let f := fun x : hat K => x * hat_inv x
  let c := (coe : K → hat K)
  change f x = 1
  have cont : ContinuousAt f x :=
    by
    letI : TopologicalSpace (hat K × hat K) := Prod.topologicalSpace
    have : ContinuousAt (fun y : hat K => ((y, hat_inv y) : hat K × hat K)) x :=
      continuous_id.continuous_at.prod (continuous_hat_inv x_ne)
    exact (_root_.continuous_mul.continuous_at.comp this : _)
  have clo : x ∈ closure (c '' {0}ᶜ) :=
    by
    have := dense_inducing_coe.dense x
    rw [← image_univ, show (univ : Set K) = {0} ∪ {0}ᶜ from (union_compl_self _).symm,
      image_union] at this
    apply mem_closure_of_mem_closure_union this
    rw [image_singleton]
    exact compl_singleton_mem_nhds x_ne
  have fxclo : f x ∈ closure (f '' (c '' {0}ᶜ)) := mem_closure_image cont clo
  have : f '' (c '' {0}ᶜ) ⊆ {1} := by
    rw [image_image]
    rintro _ ⟨z, z_ne, rfl⟩
    rw [mem_singleton_iff]
    rw [mem_compl_singleton_iff] at z_ne
    dsimp [c, f]
    rw [hat_inv_extends z_ne]
    norm_cast
    rw [mul_inv_cancel z_ne]
  replace fxclo := closure_mono this fxclo
  rwa [closure_singleton, mem_singleton_iff] at fxclo
#align uniform_space.completion.mul_hat_inv_cancel UniformSpace.Completion.mul_hatInv_cancel

instance : Field (hat K) :=
  { Completion.hasInv,
    (by infer_instance :
      CommRing
        (hat
          K)) with
    exists_pair_ne := ⟨0, 1, fun h => zero_ne_one ((uniformEmbedding_coe K).inj h)⟩
    mul_inv_cancel := fun x x_ne => by
      dsimp [Inv.inv]
      simp [if_neg x_ne, mul_hat_inv_cancel x_ne]
    inv_zero := show ((0 : K) : hat K)⁻¹ = ((0 : K) : hat K) by rw [coe_inv, inv_zero] }

instance : TopologicalDivisionRing (hat K) :=
  { Completion.topologicalRing with
    continuousAt_inv₀ := by
      intro x x_ne
      have : { y | hat_inv y = y⁻¹ } ∈ 𝓝 x :=
        haveI : {(0 : hat K)}ᶜ ⊆ { y : hat K | hat_inv y = y⁻¹ } :=
          by
          intro y y_ne
          rw [mem_compl_singleton_iff] at y_ne
          dsimp [Inv.inv]
          rw [if_neg y_ne]
        mem_of_superset (compl_singleton_mem_nhds x_ne) this
      exact ContinuousAt.congr (continuous_hat_inv x_ne) this }

end Completion

end UniformSpace

variable (L : Type _) [Field L] [UniformSpace L] [CompletableTopField L]

/- warning: subfield.completable_top_field -> Subfield.completableTopField is a dubious translation:
lean 3 declaration is
  forall (L : Type.{u1}) [_inst_3 : Field.{u1} L] [_inst_4 : UniformSpace.{u1} L] [_inst_5 : CompletableTopField.{u1} L _inst_3 _inst_4] (K : Subfield.{u1} L _inst_3), CompletableTopField.{u1} (coeSort.{succ u1, succ (succ u1)} (Subfield.{u1} L _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subfield.{u1} L _inst_3) L (Subfield.setLike.{u1} L _inst_3)) K) (Subfield.toField.{u1} L _inst_3 K) (Subtype.uniformSpace.{u1} L (fun (x : L) => Membership.Mem.{u1, u1} L (Subfield.{u1} L _inst_3) (SetLike.hasMem.{u1, u1} (Subfield.{u1} L _inst_3) L (Subfield.setLike.{u1} L _inst_3)) x K) _inst_4)
but is expected to have type
  forall (L : Type.{u1}) [_inst_3 : Field.{u1} L] [_inst_4 : UniformSpace.{u1} L] [_inst_5 : CompletableTopField.{u1} L _inst_3 _inst_4] (K : Subfield.{u1} L _inst_3), CompletableTopField.{u1} (Subtype.{succ u1} L (fun (x : L) => Membership.mem.{u1, u1} L (Subfield.{u1} L _inst_3) (SetLike.instMembership.{u1, u1} (Subfield.{u1} L _inst_3) L (Subfield.instSetLikeSubfield.{u1} L _inst_3)) x K)) (Subfield.toField.{u1} L _inst_3 K) (instUniformSpaceSubtype.{u1} L (fun (x : L) => Membership.mem.{u1, u1} L (Subfield.{u1} L _inst_3) (SetLike.instMembership.{u1, u1} (Subfield.{u1} L _inst_3) L (Subfield.instSetLikeSubfield.{u1} L _inst_3)) x K) _inst_4)
Case conversion may be inaccurate. Consider using '#align subfield.completable_top_field Subfield.completableTopFieldₓ'. -/
instance Subfield.completableTopField (K : Subfield L) : CompletableTopField K :=
  { Subtype.separatedSpace (K : Set L) with
    nice := by
      intro F F_cau inf_F
      let i : K →+* L := K.subtype
      have hi : UniformInducing i := uniform_embedding_subtype_coe.to_uniform_inducing
      rw [← hi.cauchy_map_iff] at F_cau⊢
      rw [map_comm
          (show (i ∘ fun x => x⁻¹) = (fun x => x⁻¹) ∘ i
            by
            ext
            rfl)]
      apply CompletableTopField.nice _ F_cau
      rw [← Filter.push_pull', ← map_zero i, ← hi.inducing.nhds_eq_comap, inf_F, Filter.map_bot] }
#align subfield.completable_top_field Subfield.completableTopField

#print completableTopField_of_complete /-
instance (priority := 100) completableTopField_of_complete (L : Type _) [Field L] [UniformSpace L]
    [TopologicalDivisionRing L] [SeparatedSpace L] [CompleteSpace L] : CompletableTopField L :=
  { ‹SeparatedSpace L› with
    nice := fun F cau_F hF => by
      haveI : ne_bot F := cau_F.1
      rcases CompleteSpace.complete cau_F with ⟨x, hx⟩
      have hx' : x ≠ 0 := by
        rintro rfl
        rw [inf_eq_right.mpr hx] at hF
        exact cau_F.1.Ne hF
      exact
        Filter.Tendsto.cauchy_map
          (calc
            map (fun x => x⁻¹) F ≤ map (fun x => x⁻¹) (𝓝 x) := map_mono hx
            _ ≤ 𝓝 x⁻¹ := continuous_at_inv₀ hx'
            ) }
#align completable_top_field_of_complete completableTopField_of_complete
-/

