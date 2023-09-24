/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Analysis.Complex.UpperHalfPlane.Manifold
import NumberTheory.ModularForms.SlashInvariantForms

#align_import number_theory.modular_forms.basic from "leanprover-community/mathlib"@"1a51edf13debfcbe223fa06b1cb353b9ed9751cc"

/-!
# Modular forms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines modular forms and proves some basic properties about them.

We begin by defining modular forms and cusp forms as extension of `slash_invariant_forms` then we
define the space of modular forms, cusp forms and prove that the product of two modular forms is a
modular form.
-/


open Complex UpperHalfPlane

open scoped Topology Manifold UpperHalfPlane

noncomputable section

local prefix:1024 "↑ₘ" => @coe _ (Matrix (Fin 2) (Fin 2) _) _

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

section ModularForm

open ModularForm

variable (F : Type _) (Γ : Subgroup SL(2, ℤ)) (k : ℤ)

open scoped ModularForm

#print ModularForm /-
/-- These are `slash_invariant_form`'s that are holomophic and bounded at infinity. -/
structure ModularForm extends SlashInvariantForm Γ k where
  holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (to_fun : ℍ → ℂ)
  bdd_at_infty' : ∀ A : SL(2, ℤ), IsBoundedAtImInfty (to_fun ∣[k] A)
#align modular_form ModularForm
-/

/-- The `slash_invariant_form` associated to a `modular_form`. -/
add_decl_doc ModularForm.toSlashInvariantForm

#print CuspForm /-
/-- These are `slash_invariant_form`s that are holomophic and zero at infinity. -/
structure CuspForm extends SlashInvariantForm Γ k where
  holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (to_fun : ℍ → ℂ)
  zero_at_infty' : ∀ A : SL(2, ℤ), IsZeroAtImInfty (to_fun ∣[k] A)
#align cusp_form CuspForm
-/

/-- The `slash_invariant_form` associated to a `cusp_form`. -/
add_decl_doc CuspForm.toSlashInvariantForm

#print ModularFormClass /-
/-- `modular_form_class F Γ k` says that `F` is a type of bundled functions that extend
`slash_invariant_form_class` by requiring that the functions be holomorphic and bounded
at infinity. -/
class ModularFormClass extends SlashInvariantFormClass F Γ k where
  holo : ∀ f : F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f : ℍ → ℂ)
  bdd_at_infty : ∀ (f : F) (A : SL(2, ℤ)), IsBoundedAtImInfty (f ∣[k] A)
#align modular_form_class ModularFormClass
-/

#print CuspFormClass /-
/-- `cusp_form_class F Γ k` says that `F` is a type of bundled functions that extend
`slash_invariant_form_class` by requiring that the functions be holomorphic and zero
at infinity. -/
class CuspFormClass extends SlashInvariantFormClass F Γ k where
  holo : ∀ f : F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f : ℍ → ℂ)
  zero_at_infty : ∀ (f : F) (A : SL(2, ℤ)), IsZeroAtImInfty (f ∣[k] A)
#align cusp_form_class CuspFormClass
-/

#print ModularFormClass.modularForm /-
instance (priority := 100) ModularFormClass.modularForm : ModularFormClass (ModularForm Γ k) Γ k
    where
  coe := ModularForm.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  slash_action_eq := ModularForm.slash_action_eq'
  holo := ModularForm.holo'
  bdd_at_infty := ModularForm.bdd_at_infty'
#align modular_form_class.modular_form ModularFormClass.modularForm
-/

#print CuspFormClass.cuspForm /-
instance (priority := 100) CuspFormClass.cuspForm : CuspFormClass (CuspForm Γ k) Γ k
    where
  coe := CuspForm.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  slash_action_eq := CuspForm.slash_action_eq'
  holo := CuspForm.holo'
  zero_at_infty := CuspForm.zero_at_infty'
#align cusp_form_class.cusp_form CuspFormClass.cuspForm
-/

variable {F Γ k}

#print ModularForm.toFun_eq_coe /-
@[simp]
theorem ModularForm.toFun_eq_coe {f : ModularForm Γ k} : f.toFun = (f : ℍ → ℂ) :=
  rfl
#align modular_form_to_fun_eq_coe ModularForm.toFun_eq_coe
-/

#print CuspForm.toFun_eq_coe /-
@[simp]
theorem CuspForm.toFun_eq_coe {f : CuspForm Γ k} : f.toFun = (f : ℍ → ℂ) :=
  rfl
#align cusp_form_to_fun_eq_coe CuspForm.toFun_eq_coe
-/

#print ModularForm.ext /-
@[ext]
theorem ModularForm.ext {f g : ModularForm Γ k} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align modular_form.ext ModularForm.ext
-/

#print CuspForm.ext /-
@[ext]
theorem CuspForm.ext {f g : CuspForm Γ k} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align cusp_form.ext CuspForm.ext
-/

#print ModularForm.copy /-
/-- Copy of a `modular_form` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def ModularForm.copy (f : ModularForm Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) : ModularForm Γ k
    where
  toFun := f'
  slash_action_eq' := h.symm ▸ f.slash_action_eq'
  holo' := h.symm ▸ f.holo'
  bdd_at_infty' A := h.symm ▸ f.bdd_at_infty' A
#align modular_form.copy ModularForm.copy
-/

#print CuspForm.copy /-
/-- Copy of a `cusp_form` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def CuspForm.copy (f : CuspForm Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) : CuspForm Γ k
    where
  toFun := f'
  slash_action_eq' := h.symm ▸ f.slash_action_eq'
  holo' := h.symm ▸ f.holo'
  zero_at_infty' A := h.symm ▸ f.zero_at_infty' A
#align cusp_form.copy CuspForm.copy
-/

end ModularForm

namespace ModularForm

open SlashInvariantForm

variable {F : Type _} {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

#print ModularForm.add /-
instance add : Add (ModularForm Γ k) :=
  ⟨fun f g =>
    {
      (f : SlashInvariantForm Γ k) +
        g with
      holo' := f.holo'.add g.holo'
      bdd_at_infty' := fun A => by simpa using (f.bdd_at_infty' A).add (g.bdd_at_infty' A) }⟩
#align modular_form.has_add ModularForm.add
-/

#print ModularForm.coe_add /-
@[simp]
theorem coe_add (f g : ModularForm Γ k) : ⇑(f + g) = f + g :=
  rfl
#align modular_form.coe_add ModularForm.coe_add
-/

#print ModularForm.add_apply /-
@[simp]
theorem add_apply (f g : ModularForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
  rfl
#align modular_form.add_apply ModularForm.add_apply
-/

#print ModularForm.instZero /-
instance instZero : Zero (ModularForm Γ k) :=
  ⟨{
      (0 :
        SlashInvariantForm Γ
          k) with
      holo' := fun _ => mdifferentiableAt_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      bdd_at_infty' := fun A => by simpa using zero_form_is_bounded_at_im_infty }⟩
#align modular_form.has_zero ModularForm.instZero
-/

#print ModularForm.coe_zero /-
@[simp]
theorem coe_zero : ⇑(0 : ModularForm Γ k) = (0 : ℍ → ℂ) :=
  rfl
#align modular_form.coe_zero ModularForm.coe_zero
-/

#print ModularForm.zero_apply /-
@[simp]
theorem zero_apply (z : ℍ) : (0 : ModularForm Γ k) z = 0 :=
  rfl
#align modular_form.zero_apply ModularForm.zero_apply
-/

section

variable {α : Type _} [SMul α ℂ] [IsScalarTower α ℂ ℂ]

#print ModularForm.instSMul /-
instance instSMul : SMul α (ModularForm Γ k) :=
  ⟨fun c f =>
    { c • (f : SlashInvariantForm Γ k) with
      toFun := c • f
      holo' := by simpa using f.holo'.const_smul (c • (1 : ℂ))
      bdd_at_infty' := fun A => by simpa using (f.bdd_at_infty' A).const_smul_left (c • (1 : ℂ)) }⟩
#align modular_form.has_smul ModularForm.instSMul
-/

#print ModularForm.coe_smul /-
@[simp]
theorem coe_smul (f : ModularForm Γ k) (n : α) : ⇑(n • f) = n • f :=
  rfl
#align modular_form.coe_smul ModularForm.coe_smul
-/

#print ModularForm.smul_apply /-
@[simp]
theorem smul_apply (f : ModularForm Γ k) (n : α) (z : ℍ) : (n • f) z = n • f z :=
  rfl
#align modular_form.smul_apply ModularForm.smul_apply
-/

end

#print ModularForm.instNeg /-
instance instNeg : Neg (ModularForm Γ k) :=
  ⟨fun f =>
    { -(f : SlashInvariantForm Γ k) with
      toFun := -f
      holo' := f.holo'.neg
      bdd_at_infty' := fun A => by simpa using (f.bdd_at_infty' A).neg }⟩
#align modular_form.has_neg ModularForm.instNeg
-/

#print ModularForm.coe_neg /-
@[simp]
theorem coe_neg (f : ModularForm Γ k) : ⇑(-f) = -f :=
  rfl
#align modular_form.coe_neg ModularForm.coe_neg
-/

#print ModularForm.neg_apply /-
@[simp]
theorem neg_apply (f : ModularForm Γ k) (z : ℍ) : (-f) z = -f z :=
  rfl
#align modular_form.neg_apply ModularForm.neg_apply
-/

#print ModularForm.instSub /-
instance instSub : Sub (ModularForm Γ k) :=
  ⟨fun f g => f + -g⟩
#align modular_form.has_sub ModularForm.instSub
-/

#print ModularForm.coe_sub /-
@[simp]
theorem coe_sub (f g : ModularForm Γ k) : ⇑(f - g) = f - g :=
  rfl
#align modular_form.coe_sub ModularForm.coe_sub
-/

#print ModularForm.sub_apply /-
@[simp]
theorem sub_apply (f g : ModularForm Γ k) (z : ℍ) : (f - g) z = f z - g z :=
  rfl
#align modular_form.sub_apply ModularForm.sub_apply
-/

instance : AddCommGroup (ModularForm Γ k) :=
  FunLike.coe_injective.AddCommGroup _ rfl coe_add coe_neg coe_sub coe_smul coe_smul

#print ModularForm.coeHom /-
/-- Additive coercion from `modular_form` to `ℍ → ℂ`. -/
@[simps]
def coeHom : ModularForm Γ k →+ ℍ → ℂ where
  toFun f := f
  map_zero' := coe_zero
  map_add' _ _ := rfl
#align modular_form.coe_hom ModularForm.coeHom
-/

instance : Module ℂ (ModularForm Γ k) :=
  Function.Injective.module ℂ coeHom FunLike.coe_injective fun _ _ => rfl

instance : Inhabited (ModularForm Γ k) :=
  ⟨0⟩

#print ModularForm.mul /-
/-- The modular form of weight `k_1 + k_2` given by the product of two modular forms of weights
`k_1` and `k_2`. -/
def mul {k_1 k_2 : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : ModularForm Γ k_1) (g : ModularForm Γ k_2) :
    ModularForm Γ (k_1 + k_2) where
  toFun := f * g
  slash_action_eq' A := by simp_rw [mul_slash_subgroup, ModularFormClass.slash_action_eq]
  holo' := f.holo'.mul g.holo'
  bdd_at_infty' A := by simpa using (f.bdd_at_infty' A).mul (g.bdd_at_infty' A)
#align modular_form.mul ModularForm.mul
-/

#print ModularForm.mul_coe /-
@[simp]
theorem mul_coe {k_1 k_2 : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : ModularForm Γ k_1)
    (g : ModularForm Γ k_2) : (f.mul g : ℍ → ℂ) = f * g :=
  rfl
#align modular_form.mul_coe ModularForm.mul_coe
-/

instance : One (ModularForm Γ 0) :=
  ⟨{
      (1 :
        SlashInvariantForm Γ
          0) with
      holo' := fun x => mdifferentiableAt_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      bdd_at_infty' := fun A => by simpa using at_im_infty.const_bounded_at_filter (1 : ℂ) }⟩

#print ModularForm.one_coe_eq_one /-
@[simp]
theorem one_coe_eq_one : ((1 : ModularForm Γ 0) : ℍ → ℂ) = 1 :=
  rfl
#align modular_form.one_coe_eq_one ModularForm.one_coe_eq_one
-/

end ModularForm

namespace CuspForm

open ModularForm

variable {F : Type _} {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

#print CuspForm.hasAdd /-
instance hasAdd : Add (CuspForm Γ k) :=
  ⟨fun f g =>
    { (f : SlashInvariantForm Γ k) + g with
      toFun := f + g
      holo' := f.holo'.add g.holo'
      zero_at_infty' := fun A => by simpa using (f.zero_at_infty' A).add (g.zero_at_infty' A) }⟩
#align cusp_form.has_add CuspForm.hasAdd
-/

#print CuspForm.coe_add /-
@[simp]
theorem coe_add (f g : CuspForm Γ k) : ⇑(f + g) = f + g :=
  rfl
#align cusp_form.coe_add CuspForm.coe_add
-/

#print CuspForm.add_apply /-
@[simp]
theorem add_apply (f g : CuspForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
  rfl
#align cusp_form.add_apply CuspForm.add_apply
-/

#print CuspForm.instZero /-
instance instZero : Zero (CuspForm Γ k) :=
  ⟨{ (0 : SlashInvariantForm Γ k) with
      toFun := 0
      holo' := fun _ => mdifferentiableAt_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      zero_at_infty' := by simpa using Filter.zero_zeroAtFilter _ }⟩
#align cusp_form.has_zero CuspForm.instZero
-/

#print CuspForm.coe_zero /-
@[simp]
theorem coe_zero : ⇑(0 : CuspForm Γ k) = (0 : ℍ → ℂ) :=
  rfl
#align cusp_form.coe_zero CuspForm.coe_zero
-/

#print CuspForm.zero_apply /-
@[simp]
theorem zero_apply (z : ℍ) : (0 : CuspForm Γ k) z = 0 :=
  rfl
#align cusp_form.zero_apply CuspForm.zero_apply
-/

section

variable {α : Type _} [SMul α ℂ] [IsScalarTower α ℂ ℂ]

#print CuspForm.instSMul /-
instance instSMul : SMul α (CuspForm Γ k) :=
  ⟨fun c f =>
    { c • (f : SlashInvariantForm Γ k) with
      toFun := c • f
      holo' := by simpa using f.holo'.const_smul (c • (1 : ℂ))
      zero_at_infty' := fun A => by simpa using (f.zero_at_infty' A).smul (c • (1 : ℂ)) }⟩
#align cusp_form.has_smul CuspForm.instSMul
-/

#print CuspForm.coe_smul /-
@[simp]
theorem coe_smul (f : CuspForm Γ k) (n : α) : ⇑(n • f) = n • f :=
  rfl
#align cusp_form.coe_smul CuspForm.coe_smul
-/

#print CuspForm.smul_apply /-
@[simp]
theorem smul_apply (f : CuspForm Γ k) (n : α) {z : ℍ} : (n • f) z = n • f z :=
  rfl
#align cusp_form.smul_apply CuspForm.smul_apply
-/

end

#print CuspForm.instNeg /-
instance instNeg : Neg (CuspForm Γ k) :=
  ⟨fun f =>
    { -(f : SlashInvariantForm Γ k) with
      toFun := -f
      holo' := f.holo'.neg
      zero_at_infty' := fun A => by simpa using (f.zero_at_infty' A).neg }⟩
#align cusp_form.has_neg CuspForm.instNeg
-/

#print CuspForm.coe_neg /-
@[simp]
theorem coe_neg (f : CuspForm Γ k) : ⇑(-f) = -f :=
  rfl
#align cusp_form.coe_neg CuspForm.coe_neg
-/

#print CuspForm.neg_apply /-
@[simp]
theorem neg_apply (f : CuspForm Γ k) (z : ℍ) : (-f) z = -f z :=
  rfl
#align cusp_form.neg_apply CuspForm.neg_apply
-/

#print CuspForm.instSub /-
instance instSub : Sub (CuspForm Γ k) :=
  ⟨fun f g => f + -g⟩
#align cusp_form.has_sub CuspForm.instSub
-/

#print CuspForm.coe_sub /-
@[simp]
theorem coe_sub (f g : CuspForm Γ k) : ⇑(f - g) = f - g :=
  rfl
#align cusp_form.coe_sub CuspForm.coe_sub
-/

#print CuspForm.sub_apply /-
@[simp]
theorem sub_apply (f g : CuspForm Γ k) (z : ℍ) : (f - g) z = f z - g z :=
  rfl
#align cusp_form.sub_apply CuspForm.sub_apply
-/

instance : AddCommGroup (CuspForm Γ k) :=
  FunLike.coe_injective.AddCommGroup _ rfl coe_add coe_neg coe_sub coe_smul coe_smul

#print CuspForm.coeHom /-
/-- Additive coercion from `cusp_form` to `ℍ → ℂ`. -/
@[simps]
def coeHom : CuspForm Γ k →+ ℍ → ℂ where
  toFun f := f
  map_zero' := CuspForm.coe_zero
  map_add' _ _ := rfl
#align cusp_form.coe_hom CuspForm.coeHom
-/

instance : Module ℂ (CuspForm Γ k) :=
  Function.Injective.module ℂ coeHom FunLike.coe_injective fun _ _ => rfl

instance : Inhabited (CuspForm Γ k) :=
  ⟨0⟩

instance (priority := 99) [CuspFormClass F Γ k] : ModularFormClass F Γ k
    where
  coe := FunLike.coe
  coe_injective' := FunLike.coe_injective'
  slash_action_eq := CuspFormClass.slash_action_eq
  holo := CuspFormClass.holo
  bdd_at_infty _ _ := (CuspFormClass.zero_at_infty _ _).BoundedAtFilter

end CuspForm

