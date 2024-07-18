/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Data.ZMod.Basic
import GroupTheory.GroupAction.ConjAct
import Algebra.Group.Subgroup.Pointwise
import LinearAlgebra.Matrix.SpecialLinearGroup

#align_import number_theory.modular_forms.congruence_subgroups from "leanprover-community/mathlib"@"a87d22575d946e1e156fc1edd1e1269600a8a282"

/-!
# Congruence subgroups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines congruence subgroups of `SL(2, ℤ)` such as `Γ(N)`, `Γ₀(N)` and `Γ₁(N)` for `N` a
natural number.

It also contains basic results about congruence subgroups.

-/


local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToFun

local prefix:1024 "↑ₘ" => @coe _ (Matrix (Fin 2) (Fin 2) _) _

open Matrix.SpecialLinearGroup Matrix

variable (N : ℕ)

local notation "SLMOD(" N ")" =>
  @Matrix.SpecialLinearGroup.map (Fin 2) _ _ _ _ _ _ (Int.castRingHom (ZMod N))

#print SL_reduction_mod_hom_val /-
@[simp]
theorem SL_reduction_mod_hom_val (N : ℕ) (γ : SL(2, ℤ)) :
    ∀ i j : Fin 2, (SLMOD(N) γ : Matrix (Fin 2) (Fin 2) (ZMod N)) i j = ((↑ₘγ i j : ℤ) : ZMod N) :=
  fun i j => rfl
#align SL_reduction_mod_hom_val SL_reduction_mod_hom_val
-/

#print CongruenceSubgroup.Gamma /-
/-- The full level `N` congruence subgroup of `SL(2, ℤ)` of matrices that reduce to the identity
modulo `N`.-/
def CongruenceSubgroup.Gamma (N : ℕ) : Subgroup SL(2, ℤ) :=
  SLMOD(N).ker
#align Gamma CongruenceSubgroup.Gamma
-/

#print CongruenceSubgroup.Gamma_mem' /-
theorem CongruenceSubgroup.Gamma_mem' (N : ℕ) (γ : SL(2, ℤ)) :
    γ ∈ CongruenceSubgroup.Gamma N ↔ SLMOD(N) γ = 1 :=
  Iff.rfl
#align Gamma_mem' CongruenceSubgroup.Gamma_mem'
-/

@[simp]
theorem gamma_mem (N : ℕ) (γ : SL(2, ℤ)) :
    γ ∈ CongruenceSubgroup.Gamma N ↔
      ((↑ₘγ 0 0 : ℤ) : ZMod N) = 1 ∧
        ((↑ₘγ 0 1 : ℤ) : ZMod N) = 0 ∧
          ((↑ₘγ 1 0 : ℤ) : ZMod N) = 0 ∧ ((↑ₘγ 1 1 : ℤ) : ZMod N) = 1 :=
  by
  rw [CongruenceSubgroup.Gamma_mem']
  constructor
  · intro h
    simp [← SL_reduction_mod_hom_val N γ, h]
  · intro h
    ext
    rw [SL_reduction_mod_hom_val N γ]
    fin_cases i <;> fin_cases j
    all_goals simp_rw [h]; rfl
#align Gamma_mem gamma_mem

#print CongruenceSubgroup.Gamma_normal /-
theorem CongruenceSubgroup.Gamma_normal (N : ℕ) : Subgroup.Normal (CongruenceSubgroup.Gamma N) :=
  SLMOD(N).normal_ker
#align Gamma_normal CongruenceSubgroup.Gamma_normal
-/

#print CongruenceSubgroup.Gamma_one_top /-
theorem CongruenceSubgroup.Gamma_one_top : CongruenceSubgroup.Gamma 1 = ⊤ :=
  by
  ext
  simp
#align Gamma_one_top CongruenceSubgroup.Gamma_one_top
-/

#print CongruenceSubgroup.Gamma_zero_bot /-
theorem CongruenceSubgroup.Gamma_zero_bot : CongruenceSubgroup.Gamma 0 = ⊥ :=
  by
  ext
  simp only [gamma_mem, coe_coe, coe_matrix_coe, Int.coe_castRingHom, map_apply, Int.cast_id,
    Subgroup.mem_bot]
  constructor
  · intro h
    ext
    fin_cases i <;> fin_cases j
    any_goals simp [h]
  · intro h
    simp [h]
#align Gamma_zero_bot CongruenceSubgroup.Gamma_zero_bot
-/

#print CongruenceSubgroup.Gamma0 /-
/-- The congruence subgroup of `SL(2, ℤ)` of matrices whose lower left-hand entry reduces to zero
modulo `N`. -/
def CongruenceSubgroup.Gamma0 (N : ℕ) : Subgroup SL(2, ℤ)
    where
  carrier := {g : SL(2, ℤ) | ((↑ₘg 1 0 : ℤ) : ZMod N) = 0}
  one_mem' := by simp
  hMul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq]
    have h := (Matrix.two_mul_expl a.1 b.1).2.2.1
    simp only [coe_coe, coe_matrix_coe, coe_mul, Int.coe_castRingHom, map_apply, Set.mem_setOf_eq,
      Subtype.val_eq_coe, mul_eq_mul] at *
    rw [h]
    simp [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Subtype.val_eq_coe]
    rw [SL2_inv_expl a]
    simp only [Subtype.val_eq_coe, cons_val_zero, cons_val_one, head_cons, coe_coe, coe_matrix_coe,
      coe_mk, Int.coe_castRingHom, map_apply, Int.cast_neg, neg_eq_zero, Set.mem_setOf_eq] at *
    exact ha
#align Gamma0 CongruenceSubgroup.Gamma0
-/

#print CongruenceSubgroup.Gamma0_mem /-
@[simp]
theorem CongruenceSubgroup.Gamma0_mem (N : ℕ) (A : SL(2, ℤ)) :
    A ∈ CongruenceSubgroup.Gamma0 N ↔ ((↑ₘA 1 0 : ℤ) : ZMod N) = 0 :=
  Iff.rfl
#align Gamma0_mem CongruenceSubgroup.Gamma0_mem
-/

#print CongruenceSubgroup.Gamma0_det /-
theorem CongruenceSubgroup.Gamma0_det (N : ℕ) (A : CongruenceSubgroup.Gamma0 N) :
    (A.1.1.det : ZMod N) = 1 := by simp [A.1.property]
#align Gamma0_det CongruenceSubgroup.Gamma0_det
-/

#print CongruenceSubgroup.Gamma0Map /-
/-- The group homomorphism from `Gamma0` to `zmod N` given by mapping a matrix to its lower
right-hand entry. -/
def CongruenceSubgroup.Gamma0Map (N : ℕ) : CongruenceSubgroup.Gamma0 N →* ZMod N
    where
  toFun g := ((↑ₘg 1 1 : ℤ) : ZMod N)
  map_one' := by simp
  map_mul' := by
    intro A B
    have := (two_mul_expl A.1.1 B.1.1).2.2.2
    simp only [coe_coe, Subgroup.coe_mul, coe_matrix_coe, coe_mul, Int.coe_castRingHom, map_apply,
      Subtype.val_eq_coe, mul_eq_mul] at *
    rw [this]
    have ha := A.property
    simp only [Int.cast_add, Int.cast_mul, add_left_eq_self, Subtype.val_eq_coe,
      CongruenceSubgroup.Gamma0_mem, coe_coe, coe_matrix_coe, Int.coe_castRingHom, map_apply] at *
    rw [ha]
    simp
#align Gamma_0_map CongruenceSubgroup.Gamma0Map
-/

#print CongruenceSubgroup.Gamma1' /-
/-- The congruence subgroup `Gamma1` (as a subgroup of `Gamma0`) of matrices whose bottom
row is congruent to `(0,1)` modulo `N`.-/
def CongruenceSubgroup.Gamma1' (N : ℕ) : Subgroup (CongruenceSubgroup.Gamma0 N) :=
  (CongruenceSubgroup.Gamma0Map N).ker
#align Gamma1' CongruenceSubgroup.Gamma1'
-/

#print CongruenceSubgroup.Gamma1_mem' /-
@[simp]
theorem CongruenceSubgroup.Gamma1_mem' (N : ℕ) (γ : CongruenceSubgroup.Gamma0 N) :
    γ ∈ CongruenceSubgroup.Gamma1' N ↔ (CongruenceSubgroup.Gamma0Map N) γ = 1 :=
  Iff.rfl
#align Gamma1_mem' CongruenceSubgroup.Gamma1_mem'
-/

#print CongruenceSubgroup.Gamma1_to_Gamma0_mem /-
theorem CongruenceSubgroup.Gamma1_to_Gamma0_mem (N : ℕ) (A : CongruenceSubgroup.Gamma0 N) :
    A ∈ CongruenceSubgroup.Gamma1' N ↔
      ((↑ₘA 0 0 : ℤ) : ZMod N) = 1 ∧ ((↑ₘA 1 1 : ℤ) : ZMod N) = 1 ∧ ((↑ₘA 1 0 : ℤ) : ZMod N) = 0 :=
  by
  constructor
  · intro ha
    have hA := A.property
    rw [CongruenceSubgroup.Gamma0_mem] at hA
    have adet := CongruenceSubgroup.Gamma0_det N A
    rw [Matrix.det_fin_two] at adet
    simp only [CongruenceSubgroup.Gamma0Map, coe_coe, coe_matrix_coe, Int.coe_castRingHom,
      map_apply, CongruenceSubgroup.Gamma1_mem', MonoidHom.coe_mk, Subtype.val_eq_coe, Int.cast_sub,
      Int.cast_mul] at *
    rw [hA, ha] at adet
    simp only [mul_one, MulZeroClass.mul_zero, sub_zero] at adet
    simp only [adet, hA, ha, eq_self_iff_true, and_self_iff]
  · intro ha
    simp only [CongruenceSubgroup.Gamma1_mem', CongruenceSubgroup.Gamma0Map, MonoidHom.coe_mk,
      coe_coe, coe_matrix_coe, Int.coe_castRingHom, map_apply]
    exact ha.2.1
#align Gamma1_to_Gamma0_mem CongruenceSubgroup.Gamma1_to_Gamma0_mem
-/

#print CongruenceSubgroup.Gamma1 /-
/-- The congruence subgroup `Gamma1` of `SL(2, ℤ)` consisting of matrices whose bottom
row is congruent to `(0,1)` modulo `N`. -/
def CongruenceSubgroup.Gamma1 (N : ℕ) : Subgroup SL(2, ℤ) :=
  Subgroup.map ((CongruenceSubgroup.Gamma0 N).Subtype.comp (CongruenceSubgroup.Gamma1' N).Subtype) ⊤
#align Gamma1 CongruenceSubgroup.Gamma1
-/

#print CongruenceSubgroup.Gamma1_mem /-
@[simp]
theorem CongruenceSubgroup.Gamma1_mem (N : ℕ) (A : SL(2, ℤ)) :
    A ∈ CongruenceSubgroup.Gamma1 N ↔
      ((↑ₘA 0 0 : ℤ) : ZMod N) = 1 ∧ ((↑ₘA 1 1 : ℤ) : ZMod N) = 1 ∧ ((↑ₘA 1 0 : ℤ) : ZMod N) = 0 :=
  by
  constructor
  · intro ha
    simp_rw [CongruenceSubgroup.Gamma1, Subgroup.mem_map] at ha
    simp at ha
    obtain ⟨⟨x, hx⟩, hxx⟩ := ha
    rw [CongruenceSubgroup.Gamma1_to_Gamma0_mem] at hx
    rw [← hxx]
    convert hx
  · intro ha
    simp_rw [CongruenceSubgroup.Gamma1, Subgroup.mem_map]
    have hA : A ∈ CongruenceSubgroup.Gamma0 N := by
      simp [ha.right.right, CongruenceSubgroup.Gamma0_mem, Subtype.val_eq_coe]
    have HA : (⟨A, hA⟩ : CongruenceSubgroup.Gamma0 N) ∈ CongruenceSubgroup.Gamma1' N :=
      by
      simp only [CongruenceSubgroup.Gamma1_to_Gamma0_mem, Subgroup.coe_mk, coe_coe, coe_matrix_coe,
        Int.coe_castRingHom, map_apply]
      exact ha
    refine'
      ⟨(⟨(⟨A, hA⟩ : CongruenceSubgroup.Gamma0 N), HA⟩ :
          (CongruenceSubgroup.Gamma1' N : Subgroup (CongruenceSubgroup.Gamma0 N))),
        _⟩
    simp
#align Gamma1_mem CongruenceSubgroup.Gamma1_mem
-/

#print CongruenceSubgroup.Gamma1_in_Gamma0 /-
theorem CongruenceSubgroup.Gamma1_in_Gamma0 (N : ℕ) :
    CongruenceSubgroup.Gamma1 N ≤ CongruenceSubgroup.Gamma0 N :=
  by
  intro x HA
  simp only [CongruenceSubgroup.Gamma0_mem, CongruenceSubgroup.Gamma1_mem, coe_coe, coe_matrix_coe,
    Int.coe_castRingHom, map_apply] at *
  exact HA.2.2
#align Gamma1_in_Gamma0 CongruenceSubgroup.Gamma1_in_Gamma0
-/

section CongruenceSubgroup

#print CongruenceSubgroup.IsCongruenceSubgroup /-
/-- A congruence subgroup is a subgroup of `SL(2, ℤ)` which contains some `Gamma N` for some
`(N : ℕ+)`. -/
def CongruenceSubgroup.IsCongruenceSubgroup (Γ : Subgroup SL(2, ℤ)) : Prop :=
  ∃ N : ℕ+, CongruenceSubgroup.Gamma N ≤ Γ
#align is_congruence_subgroup CongruenceSubgroup.IsCongruenceSubgroup
-/

#print CongruenceSubgroup.isCongruenceSubgroup_trans /-
theorem CongruenceSubgroup.isCongruenceSubgroup_trans (H K : Subgroup SL(2, ℤ)) (h : H ≤ K)
    (h2 : CongruenceSubgroup.IsCongruenceSubgroup H) : CongruenceSubgroup.IsCongruenceSubgroup K :=
  by
  obtain ⟨N, hN⟩ := h2
  refine' ⟨N, le_trans hN h⟩
#align is_congruence_subgroup_trans CongruenceSubgroup.isCongruenceSubgroup_trans
-/

#print CongruenceSubgroup.Gamma_is_cong_sub /-
theorem CongruenceSubgroup.Gamma_is_cong_sub (N : ℕ+) :
    CongruenceSubgroup.IsCongruenceSubgroup (CongruenceSubgroup.Gamma N) :=
  ⟨N, by simp only [le_refl]⟩
#align Gamma_is_cong_sub CongruenceSubgroup.Gamma_is_cong_sub
-/

#print CongruenceSubgroup.Gamma1_is_congruence /-
theorem CongruenceSubgroup.Gamma1_is_congruence (N : ℕ+) :
    CongruenceSubgroup.IsCongruenceSubgroup (CongruenceSubgroup.Gamma1 N) :=
  by
  refine' ⟨N, _⟩
  intro A hA
  simp only [CongruenceSubgroup.Gamma1_mem, gamma_mem] at *
  simp only [hA, eq_self_iff_true, and_self_iff]
#align Gamma1_is_congruence CongruenceSubgroup.Gamma1_is_congruence
-/

#print CongruenceSubgroup.Gamma0_is_congruence /-
theorem CongruenceSubgroup.Gamma0_is_congruence (N : ℕ+) :
    CongruenceSubgroup.IsCongruenceSubgroup (CongruenceSubgroup.Gamma0 N) :=
  CongruenceSubgroup.isCongruenceSubgroup_trans _ _ (CongruenceSubgroup.Gamma1_in_Gamma0 N)
    (CongruenceSubgroup.Gamma1_is_congruence N)
#align Gamma0_is_congruence CongruenceSubgroup.Gamma0_is_congruence
-/

end CongruenceSubgroup

section Conjugation

open scoped Pointwise

#print CongruenceSubgroup.Gamma_cong_eq_self /-
theorem CongruenceSubgroup.Gamma_cong_eq_self (N : ℕ) (g : ConjAct SL(2, ℤ)) :
    g • CongruenceSubgroup.Gamma N = CongruenceSubgroup.Gamma N := by
  apply Subgroup.Normal.conjAct (CongruenceSubgroup.Gamma_normal N)
#align Gamma_cong_eq_self CongruenceSubgroup.Gamma_cong_eq_self
-/

#print CongruenceSubgroup.conj_cong_is_cong /-
theorem CongruenceSubgroup.conj_cong_is_cong (g : ConjAct SL(2, ℤ)) (Γ : Subgroup SL(2, ℤ))
    (h : CongruenceSubgroup.IsCongruenceSubgroup Γ) :
    CongruenceSubgroup.IsCongruenceSubgroup (g • Γ) :=
  by
  obtain ⟨N, HN⟩ := h
  refine' ⟨N, _⟩
  rw [← CongruenceSubgroup.Gamma_cong_eq_self N g, Subgroup.pointwise_smul_le_pointwise_smul_iff]
  exact HN
#align conj_cong_is_cong CongruenceSubgroup.conj_cong_is_cong
-/

end Conjugation

