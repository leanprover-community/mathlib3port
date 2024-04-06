/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import GroupTheory.Perm.Basic

#align_import algebra.hom.aut from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

/-!
# Multiplicative and additive group automorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the automorphism group structure on `add_aut R := add_equiv R R` and
`mul_aut R := mul_equiv R R`.

## Implementation notes

The definition of multiplication in the automorphism groups agrees with function composition,
multiplication in `equiv.perm`, and multiplication in `category_theory.End`, but not with
`category_theory.comp`.

This file is kept separate from `data/equiv/mul_add` so that `group_theory.perm` is free to use
equivalences (and other files that use them) before the group structure is defined.

## Tags

mul_aut, add_aut
-/


variable {A : Type _} {M : Type _} {G : Type _}

#print MulAut /-
/-- The group of multiplicative automorphisms. -/
@[reducible, to_additive "The group of additive automorphisms."]
def MulAut (M : Type _) [Mul M] :=
  M ≃* M
#align mul_aut MulAut
#align add_aut AddAut
-/

namespace MulAut

variable (M) [Mul M]

/-- The group operation on multiplicative automorphisms is defined by
`λ g h, mul_equiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`.
-/
instance : Group (MulAut M) := by
  refine_struct
            { mul := fun g h => MulEquiv.trans h g
              one := MulEquiv.refl M
              inv := MulEquiv.symm
              div := _
              npow := @npowRec _ ⟨MulEquiv.refl M⟩ ⟨fun g h => MulEquiv.trans h g⟩
              zpow :=
                @zpowRec _ ⟨MulEquiv.refl M⟩ ⟨fun g h => MulEquiv.trans h g⟩ ⟨MulEquiv.symm⟩ } <;>
          intros <;>
        ext <;>
      try rfl <;>
    apply Equiv.left_inv

instance : Inhabited (MulAut M) :=
  ⟨1⟩

#print MulAut.coe_mul /-
@[simp]
theorem coe_mul (e₁ e₂ : MulAut M) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl
#align mul_aut.coe_mul MulAut.coe_mul
-/

#print MulAut.coe_one /-
@[simp]
theorem coe_one : ⇑(1 : MulAut M) = id :=
  rfl
#align mul_aut.coe_one MulAut.coe_one
-/

#print MulAut.mul_def /-
theorem mul_def (e₁ e₂ : MulAut M) : e₁ * e₂ = e₂.trans e₁ :=
  rfl
#align mul_aut.mul_def MulAut.mul_def
-/

#print MulAut.one_def /-
theorem one_def : (1 : MulAut M) = MulEquiv.refl _ :=
  rfl
#align mul_aut.one_def MulAut.one_def
-/

#print MulAut.inv_def /-
theorem inv_def (e₁ : MulAut M) : e₁⁻¹ = e₁.symm :=
  rfl
#align mul_aut.inv_def MulAut.inv_def
-/

#print MulAut.mul_apply /-
@[simp]
theorem mul_apply (e₁ e₂ : MulAut M) (m : M) : (e₁ * e₂) m = e₁ (e₂ m) :=
  rfl
#align mul_aut.mul_apply MulAut.mul_apply
-/

#print MulAut.one_apply /-
@[simp]
theorem one_apply (m : M) : (1 : MulAut M) m = m :=
  rfl
#align mul_aut.one_apply MulAut.one_apply
-/

#print MulAut.apply_inv_self /-
@[simp]
theorem apply_inv_self (e : MulAut M) (m : M) : e (e⁻¹ m) = m :=
  MulEquiv.apply_symm_apply _ _
#align mul_aut.apply_inv_self MulAut.apply_inv_self
-/

#print MulAut.inv_apply_self /-
@[simp]
theorem inv_apply_self (e : MulAut M) (m : M) : e⁻¹ (e m) = m :=
  MulEquiv.apply_symm_apply _ _
#align mul_aut.inv_apply_self MulAut.inv_apply_self
-/

#print MulAut.toPerm /-
/-- Monoid hom from the group of multiplicative automorphisms to the group of permutations. -/
def toPerm : MulAut M →* Equiv.Perm M := by
  refine_struct { toFun := MulEquiv.toEquiv } <;> intros <;> rfl
#align mul_aut.to_perm MulAut.toPerm
-/

#print MulAut.applyMulDistribMulAction /-
/-- The tautological action by `mul_aut M` on `M`.

This generalizes `function.End.apply_mul_action`. -/
instance applyMulDistribMulAction {M} [Monoid M] : MulDistribMulAction (MulAut M) M
    where
  smul := (· <| ·)
  one_smul _ := rfl
  hMul_smul _ _ _ := rfl
  smul_one := MulEquiv.map_one
  smul_hMul := MulEquiv.map_mul
#align mul_aut.apply_mul_distrib_mul_action MulAut.applyMulDistribMulAction
-/

#print MulAut.smul_def /-
@[simp]
protected theorem smul_def {M} [Monoid M] (f : MulAut M) (a : M) : f • a = f a :=
  rfl
#align mul_aut.smul_def MulAut.smul_def
-/

#print MulAut.apply_faithfulSMul /-
/-- `mul_aut.apply_mul_action` is faithful. -/
instance apply_faithfulSMul {M} [Monoid M] : FaithfulSMul (MulAut M) M :=
  ⟨fun _ _ => MulEquiv.ext⟩
#align mul_aut.apply_has_faithful_smul MulAut.apply_faithfulSMul
-/

#print MulAut.conj /-
/-- Group conjugation, `mul_aut.conj g h = g * h * g⁻¹`, as a monoid homomorphism
mapping multiplication in `G` into multiplication in the automorphism group `mul_aut G`.
See also the type `conj_act G` for any group `G`, which has a `mul_action (conj_act G) G` instance
where `conj G` acts on `G` by conjugation. -/
def conj [Group G] : G →* MulAut G
    where
  toFun g :=
    { toFun := fun h => g * h * g⁻¹
      invFun := fun h => g⁻¹ * h * g
      left_inv := fun _ => by simp [mul_assoc]
      right_inv := fun _ => by simp [mul_assoc]
      map_mul' := by simp [mul_assoc] }
  map_mul' _ _ := by ext <;> simp [mul_assoc]
  map_one' := by ext <;> simp [mul_assoc]
#align mul_aut.conj MulAut.conj
-/

#print MulAut.conj_apply /-
@[simp]
theorem conj_apply [Group G] (g h : G) : conj g h = g * h * g⁻¹ :=
  rfl
#align mul_aut.conj_apply MulAut.conj_apply
-/

#print MulAut.conj_symm_apply /-
@[simp]
theorem conj_symm_apply [Group G] (g h : G) : (conj g).symm h = g⁻¹ * h * g :=
  rfl
#align mul_aut.conj_symm_apply MulAut.conj_symm_apply
-/

#print MulAut.conj_inv_apply /-
@[simp]
theorem conj_inv_apply [Group G] (g h : G) : (conj g)⁻¹ h = g⁻¹ * h * g :=
  rfl
#align mul_aut.conj_inv_apply MulAut.conj_inv_apply
-/

end MulAut

namespace AddAut

variable (A) [Add A]

#print AddAut.group /-
/-- The group operation on additive automorphisms is defined by
`λ g h, add_equiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`.
-/
instance group : Group (AddAut A) := by
  refine_struct
            { mul := fun g h => AddEquiv.trans h g
              one := AddEquiv.refl A
              inv := AddEquiv.symm
              div := _
              npow := @npowRec _ ⟨AddEquiv.refl A⟩ ⟨fun g h => AddEquiv.trans h g⟩
              zpow :=
                @zpowRec _ ⟨AddEquiv.refl A⟩ ⟨fun g h => AddEquiv.trans h g⟩ ⟨AddEquiv.symm⟩ } <;>
          intros <;>
        ext <;>
      try rfl <;>
    apply Equiv.left_inv
#align add_aut.group AddAut.group
-/

instance : Inhabited (AddAut A) :=
  ⟨1⟩

#print AddAut.coe_mul /-
@[simp]
theorem coe_mul (e₁ e₂ : AddAut A) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl
#align add_aut.coe_mul AddAut.coe_mul
-/

#print AddAut.coe_one /-
@[simp]
theorem coe_one : ⇑(1 : AddAut A) = id :=
  rfl
#align add_aut.coe_one AddAut.coe_one
-/

#print AddAut.mul_def /-
theorem mul_def (e₁ e₂ : AddAut A) : e₁ * e₂ = e₂.trans e₁ :=
  rfl
#align add_aut.mul_def AddAut.mul_def
-/

#print AddAut.one_def /-
theorem one_def : (1 : AddAut A) = AddEquiv.refl _ :=
  rfl
#align add_aut.one_def AddAut.one_def
-/

#print AddAut.inv_def /-
theorem inv_def (e₁ : AddAut A) : e₁⁻¹ = e₁.symm :=
  rfl
#align add_aut.inv_def AddAut.inv_def
-/

#print AddAut.mul_apply /-
@[simp]
theorem mul_apply (e₁ e₂ : AddAut A) (a : A) : (e₁ * e₂) a = e₁ (e₂ a) :=
  rfl
#align add_aut.mul_apply AddAut.mul_apply
-/

#print AddAut.one_apply /-
@[simp]
theorem one_apply (a : A) : (1 : AddAut A) a = a :=
  rfl
#align add_aut.one_apply AddAut.one_apply
-/

#print AddAut.apply_inv_self /-
@[simp]
theorem apply_inv_self (e : AddAut A) (a : A) : e⁻¹ (e a) = a :=
  AddEquiv.apply_symm_apply _ _
#align add_aut.apply_inv_self AddAut.apply_inv_self
-/

#print AddAut.inv_apply_self /-
@[simp]
theorem inv_apply_self (e : AddAut A) (a : A) : e (e⁻¹ a) = a :=
  AddEquiv.apply_symm_apply _ _
#align add_aut.inv_apply_self AddAut.inv_apply_self
-/

#print AddAut.toPerm /-
/-- Monoid hom from the group of multiplicative automorphisms to the group of permutations. -/
def toPerm : AddAut A →* Equiv.Perm A := by
  refine_struct { toFun := AddEquiv.toEquiv } <;> intros <;> rfl
#align add_aut.to_perm AddAut.toPerm
-/

#print AddAut.applyDistribMulAction /-
/-- The tautological action by `add_aut A` on `A`.

This generalizes `function.End.apply_mul_action`. -/
instance applyDistribMulAction {A} [AddMonoid A] : DistribMulAction (AddAut A) A
    where
  smul := (· <| ·)
  smul_zero := AddEquiv.map_zero
  smul_add := AddEquiv.map_add
  one_smul _ := rfl
  hMul_smul _ _ _ := rfl
#align add_aut.apply_distrib_mul_action AddAut.applyDistribMulAction
-/

#print AddAut.smul_def /-
@[simp]
protected theorem smul_def {A} [AddMonoid A] (f : AddAut A) (a : A) : f • a = f a :=
  rfl
#align add_aut.smul_def AddAut.smul_def
-/

#print AddAut.apply_faithfulSMul /-
/-- `add_aut.apply_distrib_mul_action` is faithful. -/
instance apply_faithfulSMul {A} [AddMonoid A] : FaithfulSMul (AddAut A) A :=
  ⟨fun _ _ => AddEquiv.ext⟩
#align add_aut.apply_has_faithful_smul AddAut.apply_faithfulSMul
-/

#print AddAut.conj /-
/-- Additive group conjugation, `add_aut.conj g h = g + h - g`, as an additive monoid
homomorphism mapping addition in `G` into multiplication in the automorphism group `add_aut G`
(written additively in order to define the map). -/
def conj [AddGroup G] : G →+ Additive (AddAut G)
    where
  toFun g :=
    @Additive.ofMul (AddAut G)
      { toFun := fun h => g + h + -g
        -- this definition is chosen to match `mul_aut.conj`
        invFun := fun h => -g + h + g
        left_inv := fun _ => by simp [add_assoc]
        right_inv := fun _ => by simp [add_assoc]
        map_add' := by simp [add_assoc] }
  map_add' _ _ := by apply additive.to_mul.injective <;> ext <;> simp [add_assoc]
  map_zero' := by ext <;> simpa
#align add_aut.conj AddAut.conj
-/

#print AddAut.conj_apply /-
@[simp]
theorem conj_apply [AddGroup G] (g h : G) : conj g h = g + h + -g :=
  rfl
#align add_aut.conj_apply AddAut.conj_apply
-/

#print AddAut.conj_symm_apply /-
@[simp]
theorem conj_symm_apply [AddGroup G] (g h : G) : (conj g).symm h = -g + h + g :=
  rfl
#align add_aut.conj_symm_apply AddAut.conj_symm_apply
-/

#print AddAut.conj_inv_apply /-
@[simp]
theorem conj_inv_apply [AddGroup G] (g h : G) : (-conj g) h = -g + h + g :=
  rfl
#align add_aut.conj_inv_apply AddAut.conj_inv_apply
-/

end AddAut

