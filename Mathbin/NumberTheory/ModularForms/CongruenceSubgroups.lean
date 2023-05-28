/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

! This file was ported from Lean 3 source module number_theory.modular_forms.congruence_subgroups
! leanprover-community/mathlib commit a87d22575d946e1e156fc1edd1e1269600a8a282
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Zmod.Basic
import Mathbin.GroupTheory.GroupAction.ConjAct
import Mathbin.GroupTheory.Subgroup.Pointwise
import Mathbin.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Congruence subgroups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines congruence subgroups of `SL(2, ℤ)` such as `Γ(N)`, `Γ₀(N)` and `Γ₁(N)` for `N` a
natural number.

It also contains basic results about congruence subgroups.

-/


-- mathport name: «exprSL( , )»
local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToFun

-- mathport name: «expr↑ₘ »
local prefix:1024 "↑ₘ" => @coe _ (Matrix (Fin 2) (Fin 2) _) _

open Matrix.SpecialLinearGroup Matrix

variable (N : ℕ)

-- mathport name: «exprSLMOD( )»
local notation "SLMOD(" N ")" =>
  @Matrix.SpecialLinearGroup.map (Fin 2) _ _ _ _ _ _ (Int.castRingHom (ZMod N))

/- warning: SL_reduction_mod_hom_val -> SL_reduction_mod_hom_val is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align SL_reduction_mod_hom_val SL_reduction_mod_hom_valₓ'. -/
@[simp]
theorem SL_reduction_mod_hom_val (N : ℕ) (γ : SL(2, ℤ)) :
    ∀ i j : Fin 2, (SLMOD(N) γ : Matrix (Fin 2) (Fin 2) (ZMod N)) i j = ((↑ₘγ i j : ℤ) : ZMod N) :=
  fun i j => rfl
#align SL_reduction_mod_hom_val SL_reduction_mod_hom_val

/- warning: Gamma -> Gamma is a dubious translation:
lean 3 declaration is
  Nat -> (Subgroup.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing) (Matrix.SpecialLinearGroup.group.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing))
but is expected to have type
  Nat -> (Subgroup.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt) (Matrix.SpecialLinearGroup.instGroupSpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt))
Case conversion may be inaccurate. Consider using '#align Gamma Gammaₓ'. -/
/-- The full level `N` congruence subgroup of `SL(2, ℤ)` of matrices that reduce to the identity
modulo `N`.-/
def Gamma (N : ℕ) : Subgroup SL(2, ℤ) :=
  SLMOD(N).ker
#align Gamma Gamma

/- warning: Gamma_mem' -> Gamma_mem' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Gamma_mem' Gamma_mem'ₓ'. -/
theorem Gamma_mem' (N : ℕ) (γ : SL(2, ℤ)) : γ ∈ Gamma N ↔ SLMOD(N) γ = 1 :=
  Iff.rfl
#align Gamma_mem' Gamma_mem'

/- warning: Gamma_mem -> Gamma_mem is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Gamma_mem Gamma_memₓ'. -/
@[simp]
theorem Gamma_mem (N : ℕ) (γ : SL(2, ℤ)) :
    γ ∈ Gamma N ↔
      ((↑ₘγ 0 0 : ℤ) : ZMod N) = 1 ∧
        ((↑ₘγ 0 1 : ℤ) : ZMod N) = 0 ∧
          ((↑ₘγ 1 0 : ℤ) : ZMod N) = 0 ∧ ((↑ₘγ 1 1 : ℤ) : ZMod N) = 1 :=
  by
  rw [Gamma_mem']
  constructor
  · intro h
    simp [← SL_reduction_mod_hom_val N γ, h]
  · intro h
    ext
    rw [SL_reduction_mod_hom_val N γ]
    fin_cases i <;> fin_cases j
    all_goals simp_rw [h]; rfl
#align Gamma_mem Gamma_mem

/- warning: Gamma_normal -> Gamma_normal is a dubious translation:
lean 3 declaration is
  forall (N : Nat), Subgroup.Normal.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing) (Matrix.SpecialLinearGroup.group.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing) (Gamma N)
but is expected to have type
  forall (N : Nat), Subgroup.Normal.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt) (Matrix.SpecialLinearGroup.instGroupSpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt) (Gamma N)
Case conversion may be inaccurate. Consider using '#align Gamma_normal Gamma_normalₓ'. -/
theorem Gamma_normal (N : ℕ) : Subgroup.Normal (Gamma N) :=
  SLMOD(N).normal_ker
#align Gamma_normal Gamma_normal

/- warning: Gamma_one_top -> Gamma_one_top is a dubious translation:
lean 3 declaration is
  Eq.{1} (Subgroup.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing) (Matrix.SpecialLinearGroup.group.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing)) (Gamma (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Top.top.{0} (Subgroup.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing) (Matrix.SpecialLinearGroup.group.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing)) (Subgroup.hasTop.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing) (Matrix.SpecialLinearGroup.group.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing)))
but is expected to have type
  Eq.{1} (Subgroup.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt) (Matrix.SpecialLinearGroup.instGroupSpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt)) (Gamma (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Top.top.{0} (Subgroup.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt) (Matrix.SpecialLinearGroup.instGroupSpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt)) (Subgroup.instTopSubgroup.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt) (Matrix.SpecialLinearGroup.instGroupSpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt)))
Case conversion may be inaccurate. Consider using '#align Gamma_one_top Gamma_one_topₓ'. -/
theorem Gamma_one_top : Gamma 1 = ⊤ := by
  ext
  simp
#align Gamma_one_top Gamma_one_top

/- warning: Gamma_zero_bot -> Gamma_zero_bot is a dubious translation:
lean 3 declaration is
  Eq.{1} (Subgroup.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing) (Matrix.SpecialLinearGroup.group.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing)) (Gamma (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Bot.bot.{0} (Subgroup.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing) (Matrix.SpecialLinearGroup.group.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing)) (Subgroup.hasBot.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing) (Matrix.SpecialLinearGroup.group.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing)))
but is expected to have type
  Eq.{1} (Subgroup.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt) (Matrix.SpecialLinearGroup.instGroupSpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt)) (Gamma (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Bot.bot.{0} (Subgroup.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt) (Matrix.SpecialLinearGroup.instGroupSpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt)) (Subgroup.instBotSubgroup.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt) (Matrix.SpecialLinearGroup.instGroupSpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt)))
Case conversion may be inaccurate. Consider using '#align Gamma_zero_bot Gamma_zero_botₓ'. -/
theorem Gamma_zero_bot : Gamma 0 = ⊥ := by
  ext
  simp only [Gamma_mem, coe_coe, coe_matrix_coe, Int.coe_castRingHom, map_apply, Int.cast_id,
    Subgroup.mem_bot]
  constructor
  · intro h
    ext
    fin_cases i <;> fin_cases j
    any_goals simp [h]
  · intro h
    simp [h]
#align Gamma_zero_bot Gamma_zero_bot

/- warning: Gamma0 -> Gamma0 is a dubious translation:
lean 3 declaration is
  Nat -> (Subgroup.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing) (Matrix.SpecialLinearGroup.group.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing))
but is expected to have type
  Nat -> (Subgroup.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt) (Matrix.SpecialLinearGroup.instGroupSpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt))
Case conversion may be inaccurate. Consider using '#align Gamma0 Gamma0ₓ'. -/
/-- The congruence subgroup of `SL(2, ℤ)` of matrices whose lower left-hand entry reduces to zero
modulo `N`. -/
def Gamma0 (N : ℕ) : Subgroup SL(2, ℤ)
    where
  carrier := { g : SL(2, ℤ) | ((↑ₘg 1 0 : ℤ) : ZMod N) = 0 }
  one_mem' := by simp
  mul_mem' := by
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
#align Gamma0 Gamma0

/- warning: Gamma0_mem -> Gamma0_mem is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Gamma0_mem Gamma0_memₓ'. -/
@[simp]
theorem Gamma0_mem (N : ℕ) (A : SL(2, ℤ)) : A ∈ Gamma0 N ↔ ((↑ₘA 1 0 : ℤ) : ZMod N) = 0 :=
  Iff.rfl
#align Gamma0_mem Gamma0_mem

/- warning: Gamma0_det -> Gamma0_det is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Gamma0_det Gamma0_detₓ'. -/
theorem Gamma0_det (N : ℕ) (A : Gamma0 N) : (A.1.1.det : ZMod N) = 1 := by simp [A.1.property]
#align Gamma0_det Gamma0_det

/- warning: Gamma_0_map -> Gamma0Map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Gamma_0_map Gamma0Mapₓ'. -/
/-- The group homomorphism from `Gamma0` to `zmod N` given by mapping a matrix to its lower
right-hand entry. -/
def Gamma0Map (N : ℕ) : Gamma0 N →* ZMod N
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
    simp only [Int.cast_add, Int.cast_mul, add_left_eq_self, Subtype.val_eq_coe, Gamma0_mem,
      coe_coe, coe_matrix_coe, Int.coe_castRingHom, map_apply] at *
    rw [ha]
    simp
#align Gamma_0_map Gamma0Map

/- warning: Gamma1' -> Gamma1' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Gamma1' Gamma1'ₓ'. -/
/-- The congruence subgroup `Gamma1` (as a subgroup of `Gamma0`) of matrices whose bottom
row is congruent to `(0,1)` modulo `N`.-/
def Gamma1' (N : ℕ) : Subgroup (Gamma0 N) :=
  (Gamma0Map N).ker
#align Gamma1' Gamma1'

/- warning: Gamma1_mem' -> Gamma1_mem' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Gamma1_mem' Gamma1_mem'ₓ'. -/
@[simp]
theorem Gamma1_mem' (N : ℕ) (γ : Gamma0 N) : γ ∈ Gamma1' N ↔ (Gamma0Map N) γ = 1 :=
  Iff.rfl
#align Gamma1_mem' Gamma1_mem'

/- warning: Gamma1_to_Gamma0_mem -> Gamma1_to_Gamma0_mem is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Gamma1_to_Gamma0_mem Gamma1_to_Gamma0_memₓ'. -/
theorem Gamma1_to_Gamma0_mem (N : ℕ) (A : Gamma0 N) :
    A ∈ Gamma1' N ↔
      ((↑ₘA 0 0 : ℤ) : ZMod N) = 1 ∧ ((↑ₘA 1 1 : ℤ) : ZMod N) = 1 ∧ ((↑ₘA 1 0 : ℤ) : ZMod N) = 0 :=
  by
  constructor
  · intro ha
    have hA := A.property
    rw [Gamma0_mem] at hA
    have adet := Gamma0_det N A
    rw [Matrix.det_fin_two] at adet
    simp only [Gamma0Map, coe_coe, coe_matrix_coe, Int.coe_castRingHom, map_apply, Gamma1_mem',
      MonoidHom.coe_mk, Subtype.val_eq_coe, Int.cast_sub, Int.cast_mul] at *
    rw [hA, ha] at adet
    simp only [mul_one, MulZeroClass.mul_zero, sub_zero] at adet
    simp only [adet, hA, ha, eq_self_iff_true, and_self_iff]
  · intro ha
    simp only [Gamma1_mem', Gamma0Map, MonoidHom.coe_mk, coe_coe, coe_matrix_coe,
      Int.coe_castRingHom, map_apply]
    exact ha.2.1
#align Gamma1_to_Gamma0_mem Gamma1_to_Gamma0_mem

/- warning: Gamma1 -> Gamma1 is a dubious translation:
lean 3 declaration is
  Nat -> (Subgroup.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing) (Matrix.SpecialLinearGroup.group.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing))
but is expected to have type
  Nat -> (Subgroup.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt) (Matrix.SpecialLinearGroup.instGroupSpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt))
Case conversion may be inaccurate. Consider using '#align Gamma1 Gamma1ₓ'. -/
/-- The congruence subgroup `Gamma1` of `SL(2, ℤ)` consisting of matrices whose bottom
row is congruent to `(0,1)` modulo `N`. -/
def Gamma1 (N : ℕ) : Subgroup SL(2, ℤ) :=
  Subgroup.map ((Gamma0 N).Subtype.comp (Gamma1' N).Subtype) ⊤
#align Gamma1 Gamma1

/- warning: Gamma1_mem -> Gamma1_mem is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Gamma1_mem Gamma1_memₓ'. -/
@[simp]
theorem Gamma1_mem (N : ℕ) (A : SL(2, ℤ)) :
    A ∈ Gamma1 N ↔
      ((↑ₘA 0 0 : ℤ) : ZMod N) = 1 ∧ ((↑ₘA 1 1 : ℤ) : ZMod N) = 1 ∧ ((↑ₘA 1 0 : ℤ) : ZMod N) = 0 :=
  by
  constructor
  · intro ha
    simp_rw [Gamma1, Subgroup.mem_map] at ha
    simp at ha
    obtain ⟨⟨x, hx⟩, hxx⟩ := ha
    rw [Gamma1_to_Gamma0_mem] at hx
    rw [← hxx]
    convert hx
  · intro ha
    simp_rw [Gamma1, Subgroup.mem_map]
    have hA : A ∈ Gamma0 N := by simp [ha.right.right, Gamma0_mem, Subtype.val_eq_coe]
    have HA : (⟨A, hA⟩ : Gamma0 N) ∈ Gamma1' N :=
      by
      simp only [Gamma1_to_Gamma0_mem, Subgroup.coe_mk, coe_coe, coe_matrix_coe,
        Int.coe_castRingHom, map_apply]
      exact ha
    refine' ⟨(⟨(⟨A, hA⟩ : Gamma0 N), HA⟩ : (Gamma1' N : Subgroup (Gamma0 N))), _⟩
    simp
#align Gamma1_mem Gamma1_mem

/- warning: Gamma1_in_Gamma0 -> Gamma1_in_Gamma0 is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Gamma1_in_Gamma0 Gamma1_in_Gamma0ₓ'. -/
theorem Gamma1_in_Gamma0 (N : ℕ) : Gamma1 N ≤ Gamma0 N :=
  by
  intro x HA
  simp only [Gamma0_mem, Gamma1_mem, coe_coe, coe_matrix_coe, Int.coe_castRingHom, map_apply] at *
  exact HA.2.2
#align Gamma1_in_Gamma0 Gamma1_in_Gamma0

section CongruenceSubgroup

/- warning: is_congruence_subgroup -> IsCongruenceSubgroup is a dubious translation:
lean 3 declaration is
  (Subgroup.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing) (Matrix.SpecialLinearGroup.group.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (b : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) Int Int.commRing)) -> Prop
but is expected to have type
  (Subgroup.{0} (Matrix.SpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt) (Matrix.SpecialLinearGroup.instGroupSpecialLinearGroup.{0, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (b : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => instDecidableEqFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) a b) (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) Int Int.instCommRingInt)) -> Prop
Case conversion may be inaccurate. Consider using '#align is_congruence_subgroup IsCongruenceSubgroupₓ'. -/
/-- A congruence subgroup is a subgroup of `SL(2, ℤ)` which contains some `Gamma N` for some
`(N : ℕ+)`. -/
def IsCongruenceSubgroup (Γ : Subgroup SL(2, ℤ)) : Prop :=
  ∃ N : ℕ+, Gamma N ≤ Γ
#align is_congruence_subgroup IsCongruenceSubgroup

/- warning: is_congruence_subgroup_trans -> isCongruenceSubgroup_trans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_congruence_subgroup_trans isCongruenceSubgroup_transₓ'. -/
theorem isCongruenceSubgroup_trans (H K : Subgroup SL(2, ℤ)) (h : H ≤ K)
    (h2 : IsCongruenceSubgroup H) : IsCongruenceSubgroup K :=
  by
  obtain ⟨N, hN⟩ := h2
  refine' ⟨N, le_trans hN h⟩
#align is_congruence_subgroup_trans isCongruenceSubgroup_trans

#print Gamma_is_cong_sub /-
theorem Gamma_is_cong_sub (N : ℕ+) : IsCongruenceSubgroup (Gamma N) :=
  ⟨N, by simp only [le_refl]⟩
#align Gamma_is_cong_sub Gamma_is_cong_sub
-/

#print Gamma1_is_congruence /-
theorem Gamma1_is_congruence (N : ℕ+) : IsCongruenceSubgroup (Gamma1 N) :=
  by
  refine' ⟨N, _⟩
  intro A hA
  simp only [Gamma1_mem, Gamma_mem] at *
  simp only [hA, eq_self_iff_true, and_self_iff]
#align Gamma1_is_congruence Gamma1_is_congruence
-/

#print Gamma0_is_congruence /-
theorem Gamma0_is_congruence (N : ℕ+) : IsCongruenceSubgroup (Gamma0 N) :=
  isCongruenceSubgroup_trans _ _ (Gamma1_in_Gamma0 N) (Gamma1_is_congruence N)
#align Gamma0_is_congruence Gamma0_is_congruence
-/

end CongruenceSubgroup

section Conjugation

open Pointwise

/- warning: Gamma_cong_eq_self -> Gamma_cong_eq_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Gamma_cong_eq_self Gamma_cong_eq_selfₓ'. -/
theorem Gamma_cong_eq_self (N : ℕ) (g : ConjAct SL(2, ℤ)) : g • Gamma N = Gamma N := by
  apply Subgroup.Normal.conjAct (Gamma_normal N)
#align Gamma_cong_eq_self Gamma_cong_eq_self

/- warning: conj_cong_is_cong -> conj_cong_is_cong is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align conj_cong_is_cong conj_cong_is_congₓ'. -/
theorem conj_cong_is_cong (g : ConjAct SL(2, ℤ)) (Γ : Subgroup SL(2, ℤ))
    (h : IsCongruenceSubgroup Γ) : IsCongruenceSubgroup (g • Γ) :=
  by
  obtain ⟨N, HN⟩ := h
  refine' ⟨N, _⟩
  rw [← Gamma_cong_eq_self N g, Subgroup.pointwise_smul_le_pointwise_smul_iff]
  exact HN
#align conj_cong_is_cong conj_cong_is_cong

end Conjugation

