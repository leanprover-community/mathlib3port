/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam

! This file was ported from Lean 3 source module algebraic_topology.fundamental_groupoid.basic
! leanprover-community/mathlib commit 3d7987cda72abc473c7cdbbb075170e9ac620042
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.Groupoid
import Mathbin.CategoryTheory.Groupoid
import Mathbin.Topology.Category.Top.Basic
import Mathbin.Topology.Homotopy.Path

/-!
# Fundamental groupoid of a space

Given a topological space `X`, we can define the fundamental groupoid of `X` to be the category with
objects being points of `X`, and morphisms `x ⟶ y` being paths from `x` to `y`, quotiented by
homotopy equivalence. With this, the fundamental group of `X` based at `x` is just the automorphism
group of `x`.
-/


universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

variable {x₀ x₁ : X}

noncomputable section

open unitInterval

namespace Path

namespace Homotopy

section

#print Path.Homotopy.reflTransSymmAux /-
/-- Auxilliary function for `refl_trans_symm` -/
def reflTransSymmAux (x : I × I) : ℝ :=
  if (x.2 : ℝ) ≤ 1 / 2 then x.1 * 2 * x.2 else x.1 * (2 - 2 * x.2)
#align path.homotopy.refl_trans_symm_aux Path.Homotopy.reflTransSymmAux
-/

/- warning: path.homotopy.continuous_refl_trans_symm_aux -> Path.Homotopy.continuous_reflTransSymmAux is a dubious translation:
lean 3 declaration is
  Continuous.{0, 0} (Prod.{0, 0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) Real (Prod.topologicalSpace.{0, 0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (Subtype.topologicalSpace.{0} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) (Subtype.topologicalSpace.{0} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Path.Homotopy.reflTransSymmAux
but is expected to have type
  Continuous.{0, 0} (Prod.{0, 0} (Set.Elem.{0} Real unitInterval) (Set.Elem.{0} Real unitInterval)) Real (instTopologicalSpaceProd.{0, 0} (Set.Elem.{0} Real unitInterval) (Set.Elem.{0} Real unitInterval) (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Path.Homotopy.reflTransSymmAux
Case conversion may be inaccurate. Consider using '#align path.homotopy.continuous_refl_trans_symm_aux Path.Homotopy.continuous_reflTransSymmAuxₓ'. -/
@[continuity]
theorem continuous_reflTransSymmAux : Continuous reflTransSymmAux :=
  by
  refine' continuous_if_le _ _ (Continuous.continuousOn _) (Continuous.continuousOn _) _
  · continuity
  · continuity
  · continuity
  · continuity
  intro x hx
  norm_num [hx, mul_assoc]
#align path.homotopy.continuous_refl_trans_symm_aux Path.Homotopy.continuous_reflTransSymmAux

#print Path.Homotopy.reflTransSymmAux_mem_I /-
theorem reflTransSymmAux_mem_I (x : I × I) : reflTransSymmAux x ∈ I :=
  by
  dsimp only [refl_trans_symm_aux]
  split_ifs
  · constructor
    · apply mul_nonneg
      · apply mul_nonneg
        · unit_interval
        · norm_num
      · unit_interval
    · rw [mul_assoc]
      apply mul_le_one
      · unit_interval
      · apply mul_nonneg
        · norm_num
        · unit_interval
      · linarith
  · constructor
    · apply mul_nonneg
      · unit_interval
      linarith [unitInterval.nonneg x.2, unitInterval.le_one x.2]
    · apply mul_le_one
      · unit_interval
      · linarith [unitInterval.nonneg x.2, unitInterval.le_one x.2]
      · linarith [unitInterval.nonneg x.2, unitInterval.le_one x.2]
#align path.homotopy.refl_trans_symm_aux_mem_I Path.Homotopy.reflTransSymmAux_mem_I
-/

#print Path.Homotopy.reflTransSymm /-
/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from the constant path based at `x₀` to
  `p.trans p.symm`. -/
def reflTransSymm (p : Path x₀ x₁) : Homotopy (Path.refl x₀) (p.trans p.symm)
    where
  toFun x := p ⟨reflTransSymmAux x, reflTransSymmAux_mem_I x⟩
  continuous_toFun := by continuity
  map_zero_left' := by norm_num [refl_trans_symm_aux]
  map_one_left' x :=
    by
    dsimp only [refl_trans_symm_aux, Path.coe_toContinuousMap, Path.trans]
    change _ = ite _ _ _
    split_ifs
    · rw [Path.extend, Set.IccExtend_of_mem]
      · norm_num
      · rw [unitInterval.mul_pos_mem_iff zero_lt_two]
        exact ⟨unitInterval.nonneg x, h⟩
    · rw [Path.symm, Path.extend, Set.IccExtend_of_mem]
      · congr 1
        ext
        norm_num [sub_sub_eq_add_sub]
      · rw [unitInterval.two_mul_sub_one_mem_iff]
        exact ⟨(not_le.1 h).le, unitInterval.le_one x⟩
  prop' t x hx := by
    cases hx
    · rw [hx]
      simp [refl_trans_symm_aux]
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      norm_num [refl_trans_symm_aux]
#align path.homotopy.refl_trans_symm Path.Homotopy.reflTransSymm
-/

#print Path.Homotopy.reflSymmTrans /-
/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from the constant path based at `x₁` to
  `p.symm.trans p`. -/
def reflSymmTrans (p : Path x₀ x₁) : Homotopy (Path.refl x₁) (p.symm.trans p) :=
  (reflTransSymm p.symm).cast rfl <| congr_arg _ Path.symm_symm
#align path.homotopy.refl_symm_trans Path.Homotopy.reflSymmTrans
-/

end

section TransRefl

#print Path.Homotopy.transReflReparamAux /-
/-- Auxilliary function for `trans_refl_reparam` -/
def transReflReparamAux (t : I) : ℝ :=
  if (t : ℝ) ≤ 1 / 2 then 2 * t else 1
#align path.homotopy.trans_refl_reparam_aux Path.Homotopy.transReflReparamAux
-/

#print Path.Homotopy.continuous_transReflReparamAux /-
@[continuity]
theorem continuous_transReflReparamAux : Continuous transReflReparamAux :=
  by
  refine' continuous_if_le _ _ (Continuous.continuousOn _) (Continuous.continuousOn _) _ <;>
    [continuity, continuity, continuity, continuity, skip]
  intro x hx
  norm_num [hx]
#align path.homotopy.continuous_trans_refl_reparam_aux Path.Homotopy.continuous_transReflReparamAux
-/

#print Path.Homotopy.transReflReparamAux_mem_I /-
theorem transReflReparamAux_mem_I (t : I) : transReflReparamAux t ∈ I :=
  by
  unfold trans_refl_reparam_aux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]
#align path.homotopy.trans_refl_reparam_aux_mem_I Path.Homotopy.transReflReparamAux_mem_I
-/

/- warning: path.homotopy.trans_refl_reparam_aux_zero -> Path.Homotopy.transReflReparamAux_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Path.Homotopy.transReflReparamAux (OfNat.ofNat.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) 0 (OfNat.mk.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) 0 (Zero.zero.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) unitInterval.hasZero)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (Path.Homotopy.transReflReparamAux (OfNat.ofNat.{0} (Set.Elem.{0} Real unitInterval) 0 (Zero.toOfNat0.{0} (Set.Elem.{0} Real unitInterval) unitInterval.hasZero))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align path.homotopy.trans_refl_reparam_aux_zero Path.Homotopy.transReflReparamAux_zeroₓ'. -/
theorem transReflReparamAux_zero : transReflReparamAux 0 = 0 := by norm_num [trans_refl_reparam_aux]
#align path.homotopy.trans_refl_reparam_aux_zero Path.Homotopy.transReflReparamAux_zero

/- warning: path.homotopy.trans_refl_reparam_aux_one -> Path.Homotopy.transReflReparamAux_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Path.Homotopy.transReflReparamAux (OfNat.ofNat.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) 1 (OfNat.mk.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) 1 (One.one.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) unitInterval.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  Eq.{1} Real (Path.Homotopy.transReflReparamAux (OfNat.ofNat.{0} (Set.Elem.{0} Real unitInterval) 1 (One.toOfNat1.{0} (Set.Elem.{0} Real unitInterval) unitInterval.hasOne))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align path.homotopy.trans_refl_reparam_aux_one Path.Homotopy.transReflReparamAux_oneₓ'. -/
theorem transReflReparamAux_one : transReflReparamAux 1 = 1 := by norm_num [trans_refl_reparam_aux]
#align path.homotopy.trans_refl_reparam_aux_one Path.Homotopy.transReflReparamAux_one

#print Path.Homotopy.trans_refl_reparam /-
theorem trans_refl_reparam (p : Path x₀ x₁) :
    p.trans (Path.refl x₁) =
      p.reparam (fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩) (by continuity)
        (Subtype.ext transReflReparamAux_zero) (Subtype.ext transReflReparamAux_one) :=
  by
  ext
  unfold trans_refl_reparam_aux
  simp only [Path.trans_apply, not_le, coe_to_fun, Function.comp_apply]
  split_ifs
  · rfl
  · simp
#align path.homotopy.trans_refl_reparam Path.Homotopy.trans_refl_reparam
-/

#print Path.Homotopy.transRefl /-
/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from `p.trans (path.refl x₁)` to `p`.
-/
def transRefl (p : Path x₀ x₁) : Homotopy (p.trans (Path.refl x₁)) p :=
  ((Homotopy.reparam p (fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩)
          (by continuity) (Subtype.ext transReflReparamAux_zero)
          (Subtype.ext transReflReparamAux_one)).cast
      rfl (trans_refl_reparam p).symm).symm
#align path.homotopy.trans_refl Path.Homotopy.transRefl
-/

#print Path.Homotopy.reflTrans /-
/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from `(path.refl x₀).trans p` to `p`.
-/
def reflTrans (p : Path x₀ x₁) : Homotopy ((Path.refl x₀).trans p) p :=
  (transRefl p.symm).symm₂.cast (by simp) (by simp)
#align path.homotopy.refl_trans Path.Homotopy.reflTrans
-/

end TransRefl

section Assoc

#print Path.Homotopy.transAssocReparamAux /-
/-- Auxilliary function for `trans_assoc_reparam`. -/
def transAssocReparamAux (t : I) : ℝ :=
  if (t : ℝ) ≤ 1 / 4 then 2 * t else if (t : ℝ) ≤ 1 / 2 then t + 1 / 4 else 1 / 2 * (t + 1)
#align path.homotopy.trans_assoc_reparam_aux Path.Homotopy.transAssocReparamAux
-/

#print Path.Homotopy.continuous_transAssocReparamAux /-
@[continuity]
theorem continuous_transAssocReparamAux : Continuous transAssocReparamAux := by
  refine'
        continuous_if_le _ _ (Continuous.continuousOn _)
          (continuous_if_le _ _ (Continuous.continuousOn _) (Continuous.continuousOn _)
              _).ContinuousOn
          _ <;>
      [continuity, continuity, continuity, continuity, continuity, continuity, continuity, skip,
      skip] <;>
    · intro x hx
      norm_num [hx]
#align path.homotopy.continuous_trans_assoc_reparam_aux Path.Homotopy.continuous_transAssocReparamAux
-/

#print Path.Homotopy.transAssocReparamAux_mem_I /-
theorem transAssocReparamAux_mem_I (t : I) : transAssocReparamAux t ∈ I :=
  by
  unfold trans_assoc_reparam_aux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]
#align path.homotopy.trans_assoc_reparam_aux_mem_I Path.Homotopy.transAssocReparamAux_mem_I
-/

/- warning: path.homotopy.trans_assoc_reparam_aux_zero -> Path.Homotopy.transAssocReparamAux_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Path.Homotopy.transAssocReparamAux (OfNat.ofNat.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) 0 (OfNat.mk.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) 0 (Zero.zero.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) unitInterval.hasZero)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (Path.Homotopy.transAssocReparamAux (OfNat.ofNat.{0} (Set.Elem.{0} Real unitInterval) 0 (Zero.toOfNat0.{0} (Set.Elem.{0} Real unitInterval) unitInterval.hasZero))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align path.homotopy.trans_assoc_reparam_aux_zero Path.Homotopy.transAssocReparamAux_zeroₓ'. -/
theorem transAssocReparamAux_zero : transAssocReparamAux 0 = 0 := by
  norm_num [trans_assoc_reparam_aux]
#align path.homotopy.trans_assoc_reparam_aux_zero Path.Homotopy.transAssocReparamAux_zero

/- warning: path.homotopy.trans_assoc_reparam_aux_one -> Path.Homotopy.transAssocReparamAux_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Path.Homotopy.transAssocReparamAux (OfNat.ofNat.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) 1 (OfNat.mk.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) 1 (One.one.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) unitInterval.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  Eq.{1} Real (Path.Homotopy.transAssocReparamAux (OfNat.ofNat.{0} (Set.Elem.{0} Real unitInterval) 1 (One.toOfNat1.{0} (Set.Elem.{0} Real unitInterval) unitInterval.hasOne))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align path.homotopy.trans_assoc_reparam_aux_one Path.Homotopy.transAssocReparamAux_oneₓ'. -/
theorem transAssocReparamAux_one : transAssocReparamAux 1 = 1 := by
  norm_num [trans_assoc_reparam_aux]
#align path.homotopy.trans_assoc_reparam_aux_one Path.Homotopy.transAssocReparamAux_one

#print Path.Homotopy.trans_assoc_reparam /-
theorem trans_assoc_reparam {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    (p.trans q).trans r =
      (p.trans (q.trans r)).reparam
        (fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩) (by continuity)
        (Subtype.ext transAssocReparamAux_zero) (Subtype.ext transAssocReparamAux_one) :=
  by
  ext
  simp only [trans_assoc_reparam_aux, Path.trans_apply, mul_inv_cancel_left₀, not_le,
    Function.comp_apply, Ne.def, not_false_iff, bit0_eq_zero, one_ne_zero, mul_ite, Subtype.coe_mk,
    Path.coe_reparam]
  -- TODO: why does split_ifs not reduce the ifs??????
  split_ifs with h₁ h₂ h₃ h₄ h₅
  · simp [h₂, h₃, -one_div]
  · exfalso
    linarith
  · exfalso
    linarith
  · have h : ¬(x : ℝ) + 1 / 4 ≤ 1 / 2 := by linarith
    have h' : 2 * ((x : ℝ) + 1 / 4) - 1 ≤ 1 / 2 := by linarith
    have h'' : 2 * (2 * (x : ℝ)) - 1 = 2 * (2 * (↑x + 1 / 4) - 1) := by linarith
    simp only [h₄, h₁, h, h', h'', dif_neg (show ¬False from id), dif_pos True.intro, if_false,
      if_true]
  · exfalso
    linarith
  · have h : ¬(1 / 2 : ℝ) * (x + 1) ≤ 1 / 2 := by linarith
    have h' : ¬2 * ((1 / 2 : ℝ) * (x + 1)) - 1 ≤ 1 / 2 := by linarith
    simp only [h₁, h₅, h, h', if_false, dif_neg (show ¬False from id)]
    congr
    ring
#align path.homotopy.trans_assoc_reparam Path.Homotopy.trans_assoc_reparam
-/

#print Path.Homotopy.transAssoc /-
/-- For paths `p q r`, we have a homotopy from `(p.trans q).trans r` to `p.trans (q.trans r)`.
-/
def transAssoc {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    Homotopy ((p.trans q).trans r) (p.trans (q.trans r)) :=
  ((Homotopy.reparam (p.trans (q.trans r))
          (fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩) (by continuity)
          (Subtype.ext transAssocReparamAux_zero) (Subtype.ext transAssocReparamAux_one)).cast
      rfl (trans_assoc_reparam p q r).symm).symm
#align path.homotopy.trans_assoc Path.Homotopy.transAssoc
-/

end Assoc

end Homotopy

end Path

#print FundamentalGroupoid /-
/--
The fundamental groupoid of a space `X` is defined to be a type synonym for `X`, and we subsequently
put a `category_theory.groupoid` structure on it.
-/
def FundamentalGroupoid (X : Type u) :=
  X
#align fundamental_groupoid FundamentalGroupoid
-/

namespace FundamentalGroupoid

instance {X : Type u} [h : Inhabited X] : Inhabited (FundamentalGroupoid X) :=
  h

attribute [local reducible] FundamentalGroupoid

attribute [local instance] Path.Homotopic.setoid

instance : CategoryTheory.Groupoid (FundamentalGroupoid X)
    where
  Hom x y := Path.Homotopic.Quotient x y
  id x := ⟦Path.refl x⟧
  comp x y z := Path.Homotopic.Quotient.comp
  id_comp' x y f :=
    Quotient.inductionOn f fun a =>
      show ⟦(Path.refl x).trans a⟧ = ⟦a⟧ from Quotient.sound ⟨Path.Homotopy.reflTrans a⟩
  comp_id' x y f :=
    Quotient.inductionOn f fun a =>
      show ⟦a.trans (Path.refl y)⟧ = ⟦a⟧ from Quotient.sound ⟨Path.Homotopy.transRefl a⟩
  assoc' w x y z f g h :=
    Quotient.induction_on₃ f g h fun p q r =>
      show ⟦(p.trans q).trans r⟧ = ⟦p.trans (q.trans r)⟧ from
        Quotient.sound ⟨Path.Homotopy.transAssoc p q r⟩
  inv x y p :=
    Quotient.lift (fun l : Path x y => ⟦l.symm⟧)
      (by
        rintro a b ⟨h⟩
        rw [Quotient.eq']
        exact ⟨h.symm₂⟩)
      p
  inv_comp' x y f :=
    Quotient.inductionOn f fun a =>
      show ⟦a.symm.trans a⟧ = ⟦Path.refl y⟧ from
        Quotient.sound ⟨(Path.Homotopy.reflSymmTrans a).symm⟩
  comp_inv' x y f :=
    Quotient.inductionOn f fun a =>
      show ⟦a.trans a.symm⟧ = ⟦Path.refl x⟧ from
        Quotient.sound ⟨(Path.Homotopy.reflTransSymm a).symm⟩

#print FundamentalGroupoid.comp_eq /-
theorem comp_eq (x y z : FundamentalGroupoid X) (p : x ⟶ y) (q : y ⟶ z) : p ≫ q = p.comp q :=
  rfl
#align fundamental_groupoid.comp_eq FundamentalGroupoid.comp_eq
-/

#print FundamentalGroupoid.id_eq_path_refl /-
theorem id_eq_path_refl (x : FundamentalGroupoid X) : 𝟙 x = ⟦Path.refl x⟧ :=
  rfl
#align fundamental_groupoid.id_eq_path_refl FundamentalGroupoid.id_eq_path_refl
-/

#print FundamentalGroupoid.fundamentalGroupoidFunctor /-
/-- The functor sending a topological space `X` to its fundamental groupoid.
-/
def fundamentalGroupoidFunctor : TopCat ⥤ CategoryTheory.Grpd
    where
  obj X := { α := FundamentalGroupoid X }
  map X Y f :=
    { obj := f
      map := fun x y p => p.mapFn f
      map_id' := fun X => rfl
      map_comp' := fun x y z p q =>
        Quotient.induction_on₂ p q fun a b => by
          simp [comp_eq, ← Path.Homotopic.map_lift, ← Path.Homotopic.comp_lift] }
  map_id' := by
    intro X
    change _ = (⟨_, _, _, _⟩ : FundamentalGroupoid X ⥤ FundamentalGroupoid X)
    congr
    ext (x y p)
    refine' Quotient.inductionOn p fun q => _
    rw [← Path.Homotopic.map_lift]
    conv_rhs => rw [← q.map_id]
    rfl
  map_comp' := by
    intro X Y Z f g
    congr
    ext (x y p)
    refine' Quotient.inductionOn p fun q => _
    simp only [Quotient.map_mk, Path.map_map, Quotient.eq']
    rfl
#align fundamental_groupoid.fundamental_groupoid_functor FundamentalGroupoid.fundamentalGroupoidFunctor
-/

-- mathport name: fundamental_groupoid_functor
scoped notation "π" => FundamentalGroupoid.fundamentalGroupoidFunctor

-- mathport name: fundamental_groupoid_functor.obj
scoped notation "πₓ" => FundamentalGroupoid.fundamentalGroupoidFunctor.obj

-- mathport name: fundamental_groupoid_functor.map
scoped notation "πₘ" => FundamentalGroupoid.fundamentalGroupoidFunctor.map

/- warning: fundamental_groupoid.map_eq -> FundamentalGroupoid.map_eq is a dubious translation:
lean 3 declaration is
  forall {X : TopCat.{u1}} {Y : TopCat.{u1}} {x₀ : coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X} {x₁ : coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X} (f : ContinuousMap.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} Y) (TopCat.topologicalSpace.{u1} X) (TopCat.topologicalSpace.{u1} Y)) (p : Path.Homotopic.Quotient.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X) x₀ x₁), Eq.{succ u1} (Quiver.Hom.{succ u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} Y)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} Y)) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} Y)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} Y)) (CategoryTheory.Grpd.str'.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} Y))))) (CategoryTheory.Functor.obj.{u1, u1, u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X)) (CategoryTheory.Grpd.str'.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X))) (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} Y)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} Y)) (CategoryTheory.Grpd.str'.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} Y))) (CategoryTheory.Functor.map.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X Y f) x₀) (CategoryTheory.Functor.obj.{u1, u1, u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X)) (CategoryTheory.Grpd.str'.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X))) (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} Y)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} Y)) (CategoryTheory.Grpd.str'.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} Y))) (CategoryTheory.Functor.map.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X Y f) x₁)) (CategoryTheory.Functor.map.{u1, u1, u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X)) (CategoryTheory.Grpd.str'.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X))) (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} Y)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} Y)) (CategoryTheory.Grpd.str'.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} Y))) (CategoryTheory.Functor.map.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X Y f) x₀ x₁ p) (Path.Homotopic.Quotient.mapFn.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (FundamentalGroupoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} Y)) (TopCat.topologicalSpace.{u1} X) (TopCat.topologicalSpace.{u1} Y) x₀ x₁ p f)
but is expected to have type
  forall {X : TopCat.{u1}} {Y : TopCat.{u1}} {x₀ : CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X} {x₁ : CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X} (f : ContinuousMap.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} Y) (TopCat.topologicalSpace_coe.{u1} X) (TopCat.topologicalSpace_coe.{u1} Y)) (p : Path.Homotopic.Quotient.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X) x₀ x₁), Eq.{succ u1} (Quiver.Hom.{succ u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.Grpd.str'.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y))))) (Prefunctor.obj.{succ u1, succ u1, u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.Grpd.str'.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X))))) (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.Grpd.str'.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y))))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.Grpd.str'.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X))) (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.Grpd.str'.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y))) (Prefunctor.map.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X Y f)) x₀) (Prefunctor.obj.{succ u1, succ u1, u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.Grpd.str'.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X))))) (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.Grpd.str'.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y))))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.Grpd.str'.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X))) (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.Grpd.str'.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y))) (Prefunctor.map.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X Y f)) x₁)) (Prefunctor.map.{succ u1, succ u1, u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.Grpd.str'.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X))))) (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.Grpd.str'.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y))))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.Grpd.str'.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X))) (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y)) (CategoryTheory.Grpd.str'.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) Y))) (Prefunctor.map.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X Y f)) x₀ x₁ p) (Path.Homotopic.Quotient.mapFn.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} Y) (TopCat.topologicalSpace_coe.{u1} X) (TopCat.topologicalSpace_coe.{u1} Y) x₀ x₁ p f)
Case conversion may be inaccurate. Consider using '#align fundamental_groupoid.map_eq FundamentalGroupoid.map_eqₓ'. -/
theorem map_eq {X Y : TopCat} {x₀ x₁ : X} (f : C(X, Y)) (p : Path.Homotopic.Quotient x₀ x₁) :
    (πₘ f).map p = p.mapFn f :=
  rfl
#align fundamental_groupoid.map_eq FundamentalGroupoid.map_eq

/- warning: fundamental_groupoid.to_top -> FundamentalGroupoid.toTop is a dubious translation:
lean 3 declaration is
  forall {X : TopCat.{u1}}, (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X)) -> (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X)
but is expected to have type
  forall {X : TopCat.{u1}}, (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) -> (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X)
Case conversion may be inaccurate. Consider using '#align fundamental_groupoid.to_top FundamentalGroupoid.toTopₓ'. -/
/-- Help the typechecker by converting a point in a groupoid back to a point in
the underlying topological space. -/
@[reducible]
def toTop {X : TopCat} (x : πₓ X) : X :=
  x
#align fundamental_groupoid.to_top FundamentalGroupoid.toTop

/- warning: fundamental_groupoid.from_top -> FundamentalGroupoid.fromTop is a dubious translation:
lean 3 declaration is
  forall {X : TopCat.{u1}}, (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) -> (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X))
but is expected to have type
  forall {X : TopCat.{u1}}, (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) -> (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X))
Case conversion may be inaccurate. Consider using '#align fundamental_groupoid.from_top FundamentalGroupoid.fromTopₓ'. -/
/-- Help the typechecker by converting a point in a topological space to a
point in the fundamental groupoid of that space -/
@[reducible]
def fromTop {X : TopCat} (x : X) : πₓ X :=
  x
#align fundamental_groupoid.from_top FundamentalGroupoid.fromTop

/- warning: fundamental_groupoid.to_path -> FundamentalGroupoid.toPath is a dubious translation:
lean 3 declaration is
  forall {X : TopCat.{u1}} {x₀ : coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X)} {x₁ : coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X)}, (Quiver.Hom.{succ u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X)) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X)) (CategoryTheory.Grpd.str'.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X))))) x₀ x₁) -> (Path.Homotopic.Quotient.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CategoryTheory.Grpd.{u1, u1} Type.{u1} CategoryTheory.Grpd.hasCoeToSort.{u1, u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCat.{u1} TopCat.largeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1} X)) (TopCat.topologicalSpace.{u1} X) x₀ x₁)
but is expected to have type
  forall {X : TopCat.{u1}} {x₀ : CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)} {x₁ : CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)}, (Quiver.Hom.{succ u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.Groupoid.toCategory.{u1, u1} (CategoryTheory.Bundled.α.{u1, succ u1} CategoryTheory.Groupoid.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X)) (CategoryTheory.Grpd.str'.{u1, u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) CategoryTheory.Grpd.{u1, u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1} CategoryTheory.Grpd.{u1, u1} CategoryTheory.Grpd.category.{u1, u1} FundamentalGroupoid.fundamentalGroupoidFunctor.{u1}) X))))) x₀ x₁) -> (Path.Homotopic.Quotient.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X) x₀ x₁)
Case conversion may be inaccurate. Consider using '#align fundamental_groupoid.to_path FundamentalGroupoid.toPathₓ'. -/
/-- Help the typechecker by converting an arrow in the fundamental groupoid of
a topological space back to a path in that space (i.e., `path.homotopic.quotient`). -/
@[reducible]
def toPath {X : TopCat} {x₀ x₁ : πₓ X} (p : x₀ ⟶ x₁) : Path.Homotopic.Quotient x₀ x₁ :=
  p
#align fundamental_groupoid.to_path FundamentalGroupoid.toPath

#print FundamentalGroupoid.fromPath /-
/-- Help the typechecker by convering a path in a topological space to an arrow in the
fundamental groupoid of that space. -/
@[reducible]
def fromPath {X : TopCat} {x₀ x₁ : X} (p : Path.Homotopic.Quotient x₀ x₁) : x₀ ⟶ x₁ :=
  p
#align fundamental_groupoid.from_path FundamentalGroupoid.fromPath
-/

end FundamentalGroupoid

