import Mathbin.GroupTheory.FreeAbelianGroup
import Mathbin.Data.Finsupp.Basic
import Mathbin.Data.Equiv.Module
import Mathbin.LinearAlgebra.Dimension

/-!
# Isomorphism between `free_abelian_group X` and `X →₀ ℤ`

In this file we construct the canonical isomorphism between `free_abelian_group X` and `X →₀ ℤ`.
We use this to transport the notion of `support` from `finsupp` to `free_abelian_group`.

## Main declarations

- `free_abelian_group.equiv_finsupp`: group isomorphism between `free_abelian_group X` and `X →₀ ℤ`
- `free_abelian_group.coeff`: the multiplicity of `x : X` in `a : free_abelian_group X`
- `free_abelian_group.support`: the finset of `x : X` that occur in `a : free_abelian_group X`

-/


noncomputable section

open_locale BigOperators

variable {X : Type _}

/-- The group homomorphism `free_abelian_group X →+ (X →₀ ℤ)`. -/
def FreeAbelianGroup.toFinsupp : FreeAbelianGroup X →+ X →₀ ℤ :=
  FreeAbelianGroup.lift fun x => Finsupp.single x (1 : ℤ)

/-- The group homomorphism `(X →₀ ℤ) →+ free_abelian_group X`. -/
def Finsupp.toFreeAbelianGroup : (X →₀ ℤ) →+ FreeAbelianGroup X :=
  Finsupp.liftAddHom fun x => (smulAddHom ℤ (FreeAbelianGroup X)).flip (FreeAbelianGroup.of x)

open Finsupp FreeAbelianGroup

@[simp]
theorem Finsupp.to_free_abelian_group_comp_single_add_hom (x : X) :
    Finsupp.toFreeAbelianGroup.comp (Finsupp.singleAddHom x) = (smulAddHom ℤ (FreeAbelianGroup X)).flip (of x) := by
  ext
  simp only [AddMonoidHom.coe_comp, Finsupp.single_add_hom_apply, Function.comp_app, one_smul, to_free_abelian_group,
    Finsupp.lift_add_hom_apply_single]

@[simp]
theorem FreeAbelianGroup.to_finsupp_comp_to_free_abelian_group :
    to_finsupp.comp to_free_abelian_group = AddMonoidHom.id (X →₀ ℤ) := by
  ext x y
  simp only [AddMonoidHom.id_comp]
  rw [AddMonoidHom.comp_assoc, Finsupp.to_free_abelian_group_comp_single_add_hom]
  simp only [to_finsupp, AddMonoidHom.coe_comp, Finsupp.single_add_hom_apply, Function.comp_app, one_smul, lift.of,
    AddMonoidHom.flip_apply, smul_add_hom_apply, AddMonoidHom.id_apply]

@[simp]
theorem Finsupp.to_free_abelian_group_comp_to_finsupp :
    to_free_abelian_group.comp to_finsupp = AddMonoidHom.id (FreeAbelianGroup X) := by
  ext
  rw [to_free_abelian_group, to_finsupp, AddMonoidHom.comp_apply, lift.of, lift_add_hom_apply_single,
    AddMonoidHom.flip_apply, smul_add_hom_apply, one_smul, AddMonoidHom.id_apply]

@[simp]
theorem Finsupp.to_free_abelian_group_to_finsupp {X} (x : FreeAbelianGroup X) :
    x.to_finsupp.to_free_abelian_group = x := by
  rw [← AddMonoidHom.comp_apply, Finsupp.to_free_abelian_group_comp_to_finsupp, AddMonoidHom.id_apply]

namespace FreeAbelianGroup

open Finsupp

variable {X}

@[simp]
theorem to_finsupp_of (x : X) : to_finsupp (of x) = Finsupp.single x 1 := by
  simp only [to_finsupp, lift.of]

@[simp]
theorem to_finsupp_to_free_abelian_group (f : X →₀ ℤ) : f.to_free_abelian_group.to_finsupp = f := by
  rw [← AddMonoidHom.comp_apply, to_finsupp_comp_to_free_abelian_group, AddMonoidHom.id_apply]

variable (X)

/-- The additive equivalence between `free_abelian_group X` and `(X →₀ ℤ)`. -/
@[simps]
def equiv_finsupp : FreeAbelianGroup X ≃+ (X →₀ ℤ) where
  toFun := to_finsupp
  invFun := to_free_abelian_group
  left_inv := to_free_abelian_group_to_finsupp
  right_inv := to_finsupp_to_free_abelian_group
  map_add' := to_finsupp.map_add

/-- `A` is a basis of the ℤ-module `free_abelian_group A`. -/
noncomputable def Basis (α : Type _) : Basis α ℤ (FreeAbelianGroup α) :=
  ⟨(FreeAbelianGroup.equivFinsupp α).toIntLinearEquiv⟩

variable {X}

/-- `coeff x` is the additive group homomorphism `free_abelian_group X →+ ℤ`
that sends `a` to the multiplicity of `x : X` in `a`. -/
def coeff (x : X) : FreeAbelianGroup X →+ ℤ :=
  (Finsupp.applyAddHom x).comp to_finsupp

/-- `support a` for `a : free_abelian_group X` is the finite set of `x : X`
that occur in the formal sum `a`. -/
def support (a : FreeAbelianGroup X) : Finset X :=
  a.to_finsupp.support

theorem mem_support_iff (x : X) (a : FreeAbelianGroup X) : x ∈ a.support ↔ coeff x a ≠ 0 := by
  rw [support, Finsupp.mem_support_iff]
  exact Iff.rfl

theorem not_mem_support_iff (x : X) (a : FreeAbelianGroup X) : x ∉ a.support ↔ coeff x a = 0 := by
  rw [support, Finsupp.not_mem_support_iff]
  exact Iff.rfl

@[simp]
theorem support_zero : support (0 : FreeAbelianGroup X) = ∅ := by
  simp only [support, Finsupp.support_zero, AddMonoidHom.map_zero]

@[simp]
theorem support_of (x : X) : support (of x) = {x} := by
  simp only [support, to_finsupp_of, Finsupp.support_single_ne_zero one_ne_zero]

@[simp]
theorem support_neg (a : FreeAbelianGroup X) : support (-a) = support a := by
  simp only [support, AddMonoidHom.map_neg, Finsupp.support_neg]

@[simp]
theorem support_zsmul (k : ℤ) (h : k ≠ 0) (a : FreeAbelianGroup X) : support (k • a) = support a := by
  ext x
  simp only [mem_support_iff, AddMonoidHom.map_zsmul]
  simp only [h, zsmul_int_int, false_orₓ, Ne.def, mul_eq_zero]

@[simp]
theorem support_nsmul (k : ℕ) (h : k ≠ 0) (a : FreeAbelianGroup X) : support (k • a) = support a := by
  apply support_zsmul k _ a
  exact_mod_cast h

open_locale Classical

theorem support_add (a b : FreeAbelianGroup X) : support (a + b) ⊆ a.support ∪ b.support := by
  simp only [support, AddMonoidHom.map_add]
  apply Finsupp.support_add

end FreeAbelianGroup

