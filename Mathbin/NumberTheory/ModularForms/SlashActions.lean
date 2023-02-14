/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

! This file was ported from Lean 3 source module number_theory.modular_forms.slash_actions
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Complex.UpperHalfPlane.Basic
import Mathbin.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathbin.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Slash actions

This file defines a class of slash actions, which are families of right actions of a given group
parametrized by some Type. This is modeled on the slash action of `GL_pos (fin 2) ℝ` on the space
of modular forms.
-/


open Complex UpperHalfPlane

open UpperHalfPlane

-- mathport name: «expr↑ₘ »
local prefix:1024 "↑ₘ" => @coe _ (Matrix (Fin 2) (Fin 2) _) _

-- mathport name: «exprGL( , )⁺»
local notation "GL(" n ", " R ")" "⁺" => Matrix.gLPos (Fin n) R

-- mathport name: «exprSL( , )»
local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

/-- A general version of the slash action of the space of modular forms.-/
class SlashAction (β G α γ : Type _) [Group G] [Zero α] [SMul γ α] [Add α] where
  map : β → G → α → α
  zero_slash : ∀ (k : β) (g : G), map k g 0 = 0
  slash_one : ∀ (k : β) (a : α), map k 1 a = a
  right_action : ∀ (k : β) (g h : G) (a : α), map k h (map k g a) = map k (g * h) a
  smul_action : ∀ (k : β) (g : G) (a : α) (z : γ), map k g (z • a) = z • map k g a
  AddAction : ∀ (k : β) (g : G) (a b : α), map k g (a + b) = map k g a + map k g b
#align slash_action SlashAction

/-- Slash_action induced by a monoid homomorphism.-/
def monoidHomSlashAction {β G H α γ : Type _} [Group G] [Zero α] [SMul γ α] [Add α] [Group H]
    [SlashAction β G α γ] (h : H →* G) : SlashAction β H α γ
    where
  map k g := SlashAction.map γ k (h g)
  zero_slash k g := SlashAction.zero_slash k (h g)
  slash_one k a := by simp only [map_one, SlashAction.slash_one]
  right_action k g gg a := by simp only [map_mul, SlashAction.right_action]
  smul_action _ _ := SlashAction.smul_action _ _
  AddAction _ g _ _ := SlashAction.add_action _ (h g) _ _
#align monoid_hom_slash_action monoidHomSlashAction

namespace ModularForm

noncomputable section

/-- The weight `k` action of `GL(2, ℝ)⁺` on functions `f : ℍ → ℂ`. -/
def slash (k : ℤ) (γ : GL(2, ℝ)⁺) (f : ℍ → ℂ) (x : ℍ) : ℂ :=
  f (γ • x) * ((↑ₘγ).det : ℝ) ^ (k - 1) * UpperHalfPlane.denom γ x ^ (-k)
#align modular_form.slash ModularForm.slash

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f : ℍ → ℂ)

-- mathport name: modular_form.slash
scoped notation:100 f " ∣[" k "]" γ:100 => ModularForm.slash k γ f

theorem slash_right_action (k : ℤ) (A B : GL(2, ℝ)⁺) (f : ℍ → ℂ) :
    (f ∣[k]A) ∣[k]B = f ∣[k](A * B) := by
  ext1
  simp_rw [slash, UpperHalfPlane.denom_cocycle A B x]
  have e3 : (A * B) • x = A • B • x := by convert UpperHalfPlane.mul_smul' A B x
  rw [e3]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, of_real_mul, Subgroup.coe_mul, coe_coe,
    UpperHalfPlane.coe_smul, Units.val_mul, Matrix.mul_eq_mul, Matrix.det_mul,
    UpperHalfPlane.smulAux, UpperHalfPlane.smulAux', Subtype.coe_mk] at *
  field_simp
  have :
    (((↑(↑A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
          ((↑(↑B : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ)) ^
        (k - 1) =
      ((↑(↑A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 1) *
        ((↑(↑B : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 1) :=
    by simp_rw [← mul_zpow]
  simp_rw [this, ← mul_assoc, ← mul_zpow]
#align modular_form.slash_right_action ModularForm.slash_right_action

@[simp]
theorem slash_add (k : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) : (f + g) ∣[k]A = f ∣[k]A + g ∣[k]A :=
  by
  ext1
  simp only [slash, Pi.add_apply, denom, coe_coe, zpow_neg]
  ring
#align modular_form.slash_add ModularForm.slash_add

@[simp]
theorem slash_one (k : ℤ) (f : ℍ → ℂ) : f ∣[k]1 = f :=
  funext <| by simp [slash]
#align modular_form.slash_one ModularForm.slash_one

variable {α : Type _} [SMul α ℂ] [IsScalarTower α ℂ ℂ]

@[simp]
theorem smul_slash (k : ℤ) (A : GL(2, ℝ)⁺) (f : ℍ → ℂ) (c : α) : (c • f) ∣[k]A = c • f ∣[k]A :=
  by
  simp_rw [← smul_one_smul ℂ c f, ← smul_one_smul ℂ c (f ∣[k]A)]
  ext1
  simp_rw [slash]
  simp only [slash, Algebra.id.smul_eq_mul, Matrix.GeneralLinearGroup.coe_det_apply, Pi.smul_apply,
    Subtype.val_eq_coe, coe_coe]
  ring
#align modular_form.smul_slash ModularForm.smul_slash

@[simp]
theorem neg_slash (k : ℤ) (A : GL(2, ℝ)⁺) (f : ℍ → ℂ) : (-f) ∣[k]A = -f ∣[k]A :=
  funext <| by simp [slash]
#align modular_form.neg_slash ModularForm.neg_slash

@[simp]
theorem zero_slash (k : ℤ) (A : GL(2, ℝ)⁺) : (0 : ℍ → ℂ) ∣[k]A = 0 :=
  funext fun _ => by simp only [slash, Pi.zero_apply, zero_mul]
#align modular_form.zero_slash ModularForm.zero_slash

instance : SlashAction ℤ GL(2, ℝ)⁺ (ℍ → ℂ) ℂ
    where
  map := slash
  zero_slash := zero_slash
  slash_one := slash_one
  right_action := slash_right_action
  smul_action := smul_slash
  AddAction := slash_add

instance subgroupAction (Γ : Subgroup SL(2, ℤ)) : SlashAction ℤ Γ (ℍ → ℂ) ℂ :=
  monoidHomSlashAction
    (MonoidHom.comp Matrix.SpecialLinearGroup.toGLPos
      (MonoidHom.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) (Subgroup.subtype Γ)))
#align modular_form.subgroup_action ModularForm.subgroupAction

@[simp]
theorem subgroup_slash (Γ : Subgroup SL(2, ℤ)) (γ : Γ) :
    SlashAction.map ℂ k γ f = slash k (γ : GL(2, ℝ)⁺) f :=
  rfl
#align modular_form.subgroup_slash ModularForm.subgroup_slash

instance sLAction : SlashAction ℤ SL(2, ℤ) (ℍ → ℂ) ℂ :=
  monoidHomSlashAction
    (MonoidHom.comp Matrix.SpecialLinearGroup.toGLPos
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)))
#align modular_form.SL_action ModularForm.sLAction

@[simp]
theorem SL_slash (γ : SL(2, ℤ)) : SlashAction.map ℂ k γ f = slash k (γ : GL(2, ℝ)⁺) f :=
  rfl
#align modular_form.SL_slash ModularForm.SL_slash

-- mathport name: «expr ∣[ , ]»
local notation:73 f "∣[" k:0 "," A "]" => SlashAction.map ℂ k A f

/-- The constant function 1 is invariant under any element of `SL(2, ℤ)`. -/
@[simp]
theorem is_invariant_one (A : SL(2, ℤ)) : (1 : ℍ → ℂ)∣[(0 : ℤ),A] = (1 : ℍ → ℂ) :=
  by
  have : ((↑ₘ(A : GL(2, ℝ)⁺)).det : ℝ) = 1 := by
    simp only [coe_coe, Matrix.SpecialLinearGroup.coe_gLPos_coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.det_coe]
  funext
  rw [SL_slash, slash, zero_sub, this]
  simp
#align modular_form.is_invariant_one ModularForm.is_invariant_one

/-- A function `f : ℍ → ℂ` is `slash_invariant`, of weight `k ∈ ℤ` and level `Γ`,
  if for every matrix `γ ∈ Γ` we have `f(γ • z)= (c*z+d)^k f(z)` where `γ= ![![a, b], ![c, d]]`,
  and it acts on `ℍ` via Möbius transformations. -/
theorem slash_action_eq'_iff (k : ℤ) (Γ : Subgroup SL(2, ℤ)) (f : ℍ → ℂ) (γ : Γ) (z : ℍ) :
    (f∣[k,γ]) z = f z ↔ f (γ • z) = ((↑ₘγ 1 0 : ℂ) * z + (↑ₘγ 1 1 : ℂ)) ^ k * f z :=
  by
  simp only [subgroup_slash, ModularForm.slash]
  convert inv_mul_eq_iff_eq_mul₀ _ using 2
  · rw [mul_comm]
    simp only [denom, coe_coe, Matrix.SpecialLinearGroup.coe_gLPos_coe_GL_coe_matrix, zpow_neg,
      Matrix.SpecialLinearGroup.det_coe, of_real_one, one_zpow, mul_one, subgroup_to_sl_moeb,
      sl_moeb]
    rfl
  · convert zpow_ne_zero k (denom_ne_zero γ z)
#align modular_form.slash_action_eq'_iff ModularForm.slash_action_eq'_iff

theorem mul_slash (k1 k2 : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) :
    (f * g)∣[k1 + k2,A] = ((↑ₘA).det : ℝ) • f∣[k1,A] * g∣[k2,A] :=
  by
  ext1
  simp only [SlashAction.map, slash, Matrix.GeneralLinearGroup.coe_det_apply, Subtype.val_eq_coe,
    Pi.mul_apply, Pi.smul_apply, Algebra.smul_mul_assoc, real_smul]
  set d : ℂ := ↑((↑ₘA).det : ℝ)
  have h1 : d ^ (k1 + k2 - 1) = d * d ^ (k1 - 1) * d ^ (k2 - 1) :=
    by
    have : d ≠ 0 := by
      dsimp [d]
      norm_cast
      exact Matrix.gLPos.det_ne_zero A
    rw [← zpow_one_add₀ this, ← zpow_add₀ this]
    ring
  have h22 : denom A x ^ (-(k1 + k2)) = denom A x ^ (-k1) * denom A x ^ (-k2) :=
    by
    rw [Int.neg_add, zpow_add₀]
    exact UpperHalfPlane.denom_ne_zero A x
  rw [h1, h22]
  ring
#align modular_form.mul_slash ModularForm.mul_slash

@[simp]
theorem mul_slash_SL2 (k1 k2 : ℤ) (A : SL(2, ℤ)) (f g : ℍ → ℂ) :
    (f * g)∣[k1 + k2,A] = f∣[k1,A] * g∣[k2,A] :=
  calc
    (f * g)∣[k1 + k2,(A : GL(2, ℝ)⁺)] = _ • f∣[k1,A] * g∣[k2,A] := mul_slash _ _ _ _ _
    _ = (1 : ℝ) • f∣[k1,A] * g∣[k2,A] := by simp [-Matrix.SpecialLinearGroup.coe_matrix_coe]
    _ = f∣[k1,A] * g∣[k2,A] := by simp
    
#align modular_form.mul_slash_SL2 ModularForm.mul_slash_SL2

theorem mul_slash_subgroup (k1 k2 : ℤ) (Γ : Subgroup SL(2, ℤ)) (A : Γ) (f g : ℍ → ℂ) :
    (f * g)∣[k1 + k2,A] = f∣[k1,A] * g∣[k2,A] :=
  mul_slash_SL2 k1 k2 A f g
#align modular_form.mul_slash_subgroup ModularForm.mul_slash_subgroup

end ModularForm

