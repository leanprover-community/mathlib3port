/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Algebra.Module.LinearMap
import Mathbin.Algebra.Module.Equiv
import Mathbin.GroupTheory.GroupAction.SubMulAction
import Mathbin.GroupTheory.Submonoid.Membership

#align_import algebra.module.submodule.basic from "leanprover-community/mathlib"@"8130e5155d637db35907c272de9aec9dc851c03a"

/-!

# Submodules of a module

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define

* `submodule R M` : a subset of a `module` `M` that contains zero and is closed with respect to
  addition and scalar multiplication.

* `subspace k M` : an abbreviation for `submodule` assuming that `k` is a `field`.

## Tags

submodule, subspace, linear map
-/


open Function

open scoped BigOperators

universe u'' u' u v w

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

#print Submodule /-
/-- A submodule of a module is one which is closed under vector operations.
  This is a sufficient condition for the subset of vectors in the submodule
  to themselves form a module. -/
structure Submodule (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] extends
    AddSubmonoid M, SubMulAction R M : Type v
#align submodule Submodule
-/

/-- Reinterpret a `submodule` as an `add_submonoid`. -/
add_decl_doc Submodule.toAddSubmonoid

/-- Reinterpret a `submodule` as an `sub_mul_action`. -/
add_decl_doc Submodule.toSubMulAction

namespace Submodule

variable [Semiring R] [AddCommMonoid M] [Module R M]

instance : SetLike (Submodule R M) M
    where
  coe := Submodule.carrier
  coe_injective' p q h := by cases p <;> cases q <;> congr

instance : AddSubmonoidClass (Submodule R M) M
    where
  zero_mem := zero_mem'
  add_mem := add_mem'

instance : SMulMemClass (Submodule R M) R M where smul_mem := smul_mem'

#print Submodule.mem_toAddSubmonoid /-
@[simp]
theorem mem_toAddSubmonoid (p : Submodule R M) (x : M) : x ∈ p.toAddSubmonoid ↔ x ∈ p :=
  Iff.rfl
#align submodule.mem_to_add_submonoid Submodule.mem_toAddSubmonoid
-/

variable {p q : Submodule R M}

#print Submodule.mem_mk /-
@[simp]
theorem mem_mk {S : Set M} {x : M} (h₁ h₂ h₃) : x ∈ (⟨S, h₁, h₂, h₃⟩ : Submodule R M) ↔ x ∈ S :=
  Iff.rfl
#align submodule.mem_mk Submodule.mem_mk
-/

#print Submodule.coe_set_mk /-
@[simp]
theorem coe_set_mk (S : Set M) (h₁ h₂ h₃) : ((⟨S, h₁, h₂, h₃⟩ : Submodule R M) : Set M) = S :=
  rfl
#align submodule.coe_set_mk Submodule.coe_set_mk
-/

#print Submodule.mk_le_mk /-
@[simp]
theorem mk_le_mk {S S' : Set M} (h₁ h₂ h₃ h₁' h₂' h₃') :
    (⟨S, h₁, h₂, h₃⟩ : Submodule R M) ≤ (⟨S', h₁', h₂', h₃'⟩ : Submodule R M) ↔ S ⊆ S' :=
  Iff.rfl
#align submodule.mk_le_mk Submodule.mk_le_mk
-/

#print Submodule.ext /-
@[ext]
theorem ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  SetLike.ext h
#align submodule.ext Submodule.ext
-/

#print Submodule.copy /-
/-- Copy of a submodule with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (p : Submodule R M) (s : Set M) (hs : s = ↑p) : Submodule R M
    where
  carrier := s
  zero_mem' := hs.symm ▸ p.zero_mem'
  add_mem' _ _ := hs.symm ▸ p.add_mem'
  smul_mem' := hs.symm ▸ p.smul_mem'
#align submodule.copy Submodule.copy
-/

#print Submodule.coe_copy /-
@[simp]
theorem coe_copy (S : Submodule R M) (s : Set M) (hs : s = ↑S) : (S.copy s hs : Set M) = s :=
  rfl
#align submodule.coe_copy Submodule.coe_copy
-/

#print Submodule.copy_eq /-
theorem copy_eq (S : Submodule R M) (s : Set M) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align submodule.copy_eq Submodule.copy_eq
-/

#print Submodule.toAddSubmonoid_injective /-
theorem toAddSubmonoid_injective : Injective (toAddSubmonoid : Submodule R M → AddSubmonoid M) :=
  fun p q h => SetLike.ext'_iff.2 (show _ from SetLike.ext'_iff.1 h)
#align submodule.to_add_submonoid_injective Submodule.toAddSubmonoid_injective
-/

#print Submodule.toAddSubmonoid_eq /-
@[simp]
theorem toAddSubmonoid_eq : p.toAddSubmonoid = q.toAddSubmonoid ↔ p = q :=
  toAddSubmonoid_injective.eq_iff
#align submodule.to_add_submonoid_eq Submodule.toAddSubmonoid_eq
-/

#print Submodule.toAddSubmonoid_strictMono /-
@[mono]
theorem toAddSubmonoid_strictMono : StrictMono (toAddSubmonoid : Submodule R M → AddSubmonoid M) :=
  fun _ _ => id
#align submodule.to_add_submonoid_strict_mono Submodule.toAddSubmonoid_strictMono
-/

#print Submodule.toAddSubmonoid_le /-
theorem toAddSubmonoid_le : p.toAddSubmonoid ≤ q.toAddSubmonoid ↔ p ≤ q :=
  Iff.rfl
#align submodule.to_add_submonoid_le Submodule.toAddSubmonoid_le
-/

#print Submodule.toAddSubmonoid_mono /-
@[mono]
theorem toAddSubmonoid_mono : Monotone (toAddSubmonoid : Submodule R M → AddSubmonoid M) :=
  toAddSubmonoid_strictMono.Monotone
#align submodule.to_add_submonoid_mono Submodule.toAddSubmonoid_mono
-/

#print Submodule.coe_toAddSubmonoid /-
@[simp]
theorem coe_toAddSubmonoid (p : Submodule R M) : (p.toAddSubmonoid : Set M) = p :=
  rfl
#align submodule.coe_to_add_submonoid Submodule.coe_toAddSubmonoid
-/

#print Submodule.toSubMulAction_injective /-
theorem toSubMulAction_injective : Injective (toSubMulAction : Submodule R M → SubMulAction R M) :=
  fun p q h => SetLike.ext'_iff.2 (show _ from SetLike.ext'_iff.1 h)
#align submodule.to_sub_mul_action_injective Submodule.toSubMulAction_injective
-/

#print Submodule.toSubMulAction_eq /-
@[simp]
theorem toSubMulAction_eq : p.toSubMulAction = q.toSubMulAction ↔ p = q :=
  toSubMulAction_injective.eq_iff
#align submodule.to_sub_mul_action_eq Submodule.toSubMulAction_eq
-/

#print Submodule.toSubMulAction_strictMono /-
@[mono]
theorem toSubMulAction_strictMono :
    StrictMono (toSubMulAction : Submodule R M → SubMulAction R M) := fun _ _ => id
#align submodule.to_sub_mul_action_strict_mono Submodule.toSubMulAction_strictMono
-/

#print Submodule.toSubMulAction_mono /-
@[mono]
theorem toSubMulAction_mono : Monotone (toSubMulAction : Submodule R M → SubMulAction R M) :=
  toSubMulAction_strictMono.Monotone
#align submodule.to_sub_mul_action_mono Submodule.toSubMulAction_mono
-/

#print Submodule.coe_toSubMulAction /-
@[simp]
theorem coe_toSubMulAction (p : Submodule R M) : (p.toSubMulAction : Set M) = p :=
  rfl
#align submodule.coe_to_sub_mul_action Submodule.coe_toSubMulAction
-/

end Submodule

namespace SMulMemClass

variable [Semiring R] [AddCommMonoid M] [Module R M] {A : Type _} [SetLike A M]
  [AddSubmonoidClass A M] [hA : SMulMemClass A R M] (S' : A)

/- warning: smul_mem_class.to_module clashes with submodule_class.to_module -> SMulMemClass.toModule
Case conversion may be inaccurate. Consider using '#align smul_mem_class.to_module SMulMemClass.toModuleₓ'. -/
#print SMulMemClass.toModule /-
-- Prefer subclasses of `module` over `smul_mem_class`.
/-- A submodule of a `module` is a `module`.  -/
instance (priority := 75) toModule : Module R S' :=
  Subtype.coe_injective.Module R (AddSubmonoidClass.Subtype S') (SetLike.val_smul S')
#align smul_mem_class.to_module SMulMemClass.toModule
-/

/- warning: smul_mem_class.subtype clashes with submodule_class.subtype -> SMulMemClass.subtype
Case conversion may be inaccurate. Consider using '#align smul_mem_class.subtype SMulMemClass.subtypeₓ'. -/
#print SMulMemClass.subtype /-
/-- The natural `R`-linear map from a submodule of an `R`-module `M` to `M`. -/
protected def subtype : S' →ₗ[R] M :=
  ⟨coe, fun _ _ => rfl, fun _ _ => rfl⟩
#align smul_mem_class.subtype SMulMemClass.subtype
-/

/- warning: smul_mem_class.coe_subtype clashes with submodule_class.coe_subtype -> SMulMemClass.coeSubtype
Case conversion may be inaccurate. Consider using '#align smul_mem_class.coe_subtype SMulMemClass.coeSubtypeₓ'. -/
#print SMulMemClass.coeSubtype /-
@[simp]
protected theorem coeSubtype : (SMulMemClass.subtype S' : S' → M) = coe :=
  rfl
#align smul_mem_class.coe_subtype SMulMemClass.coeSubtype
-/

end SMulMemClass

namespace Submodule

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M]

-- We can infer the module structure implicitly from the bundled submodule,
-- rather than via typeclass resolution.
variable {module_M : Module R M}

variable {p q : Submodule R M}

variable {r : R} {x y : M}

variable (p)

#print Submodule.mem_carrier /-
@[simp]
theorem mem_carrier : x ∈ p.carrier ↔ x ∈ (p : Set M) :=
  Iff.rfl
#align submodule.mem_carrier Submodule.mem_carrier
-/

#print Submodule.zero_mem /-
@[simp]
protected theorem zero_mem : (0 : M) ∈ p :=
  zero_mem _
#align submodule.zero_mem Submodule.zero_mem
-/

#print Submodule.add_mem /-
protected theorem add_mem (h₁ : x ∈ p) (h₂ : y ∈ p) : x + y ∈ p :=
  add_mem h₁ h₂
#align submodule.add_mem Submodule.add_mem
-/

#print Submodule.smul_mem /-
theorem smul_mem (r : R) (h : x ∈ p) : r • x ∈ p :=
  p.smul_mem' r h
#align submodule.smul_mem Submodule.smul_mem
-/

#print Submodule.smul_of_tower_mem /-
theorem smul_of_tower_mem [SMul S R] [SMul S M] [IsScalarTower S R M] (r : S) (h : x ∈ p) :
    r • x ∈ p :=
  p.toSubMulAction.smul_of_tower_mem r h
#align submodule.smul_of_tower_mem Submodule.smul_of_tower_mem
-/

#print Submodule.sum_mem /-
protected theorem sum_mem {t : Finset ι} {f : ι → M} : (∀ c ∈ t, f c ∈ p) → ∑ i in t, f i ∈ p :=
  sum_mem
#align submodule.sum_mem Submodule.sum_mem
-/

#print Submodule.sum_smul_mem /-
theorem sum_smul_mem {t : Finset ι} {f : ι → M} (r : ι → R) (hyp : ∀ c ∈ t, f c ∈ p) :
    ∑ i in t, r i • f i ∈ p :=
  sum_mem fun i hi => smul_mem _ _ (hyp i hi)
#align submodule.sum_smul_mem Submodule.sum_smul_mem
-/

#print Submodule.smul_mem_iff' /-
@[simp]
theorem smul_mem_iff' [Group G] [MulAction G M] [SMul G R] [IsScalarTower G R M] (g : G) :
    g • x ∈ p ↔ x ∈ p :=
  p.toSubMulAction.smul_mem_iff' g
#align submodule.smul_mem_iff' Submodule.smul_mem_iff'
-/

instance : Add p :=
  ⟨fun x y => ⟨x.1 + y.1, add_mem x.2 y.2⟩⟩

instance : Zero p :=
  ⟨⟨0, zero_mem _⟩⟩

instance : Inhabited p :=
  ⟨0⟩

instance [SMul S R] [SMul S M] [IsScalarTower S R M] : SMul S p :=
  ⟨fun c x => ⟨c • x.1, smul_of_tower_mem _ c x.2⟩⟩

instance [SMul S R] [SMul S M] [IsScalarTower S R M] : IsScalarTower S R p :=
  p.toSubMulAction.IsScalarTower

#print Submodule.isScalarTower' /-
instance isScalarTower' {S' : Type _} [SMul S R] [SMul S M] [SMul S' R] [SMul S' M] [SMul S S']
    [IsScalarTower S' R M] [IsScalarTower S S' M] [IsScalarTower S R M] : IsScalarTower S S' p :=
  p.toSubMulAction.isScalarTower'
#align submodule.is_scalar_tower' Submodule.isScalarTower'
-/

instance [SMul S R] [SMul S M] [IsScalarTower S R M] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M]
    [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] : IsCentralScalar S p :=
  p.toSubMulAction.IsCentralScalar

#print Submodule.nonempty /-
protected theorem nonempty : (p : Set M).Nonempty :=
  ⟨0, p.zero_mem⟩
#align submodule.nonempty Submodule.nonempty
-/

#print Submodule.mk_eq_zero /-
@[simp]
theorem mk_eq_zero {x} (h : x ∈ p) : (⟨x, h⟩ : p) = 0 ↔ x = 0 :=
  Subtype.ext_iff_val
#align submodule.mk_eq_zero Submodule.mk_eq_zero
-/

variable {p}

#print Submodule.coe_eq_zero /-
@[simp, norm_cast]
theorem coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0 :=
  (SetLike.coe_eq_coe : (x : M) = (0 : p) ↔ x = 0)
#align submodule.coe_eq_zero Submodule.coe_eq_zero
-/

#print Submodule.coe_add /-
@[simp, norm_cast]
theorem coe_add (x y : p) : (↑(x + y) : M) = ↑x + ↑y :=
  rfl
#align submodule.coe_add Submodule.coe_add
-/

#print Submodule.coe_zero /-
@[simp, norm_cast]
theorem coe_zero : ((0 : p) : M) = 0 :=
  rfl
#align submodule.coe_zero Submodule.coe_zero
-/

#print Submodule.coe_smul /-
@[norm_cast]
theorem coe_smul (r : R) (x : p) : ((r • x : p) : M) = r • ↑x :=
  rfl
#align submodule.coe_smul Submodule.coe_smul
-/

#print Submodule.coe_smul_of_tower /-
@[simp, norm_cast]
theorem coe_smul_of_tower [SMul S R] [SMul S M] [IsScalarTower S R M] (r : S) (x : p) :
    ((r • x : p) : M) = r • ↑x :=
  rfl
#align submodule.coe_smul_of_tower Submodule.coe_smul_of_tower
-/

#print Submodule.coe_mk /-
@[simp, norm_cast]
theorem coe_mk (x : M) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : M) = x :=
  rfl
#align submodule.coe_mk Submodule.coe_mk
-/

#print Submodule.coe_mem /-
@[simp]
theorem coe_mem (x : p) : (x : M) ∈ p :=
  x.2
#align submodule.coe_mem Submodule.coe_mem
-/

variable (p)

instance : AddCommMonoid p :=
  { p.toAddSubmonoid.toAddCommMonoid with
    add := (· + ·)
    zero := 0 }

#print Submodule.module' /-
instance module' [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] : Module S p := by
  refine' { p.to_sub_mul_action.mul_action' with smul := (· • ·) .. } <;>
    · intros; apply SetCoe.ext; simp [smul_add, add_smul, mul_smul]
#align submodule.module' Submodule.module'
-/

instance : Module R p :=
  p.module'

#print Submodule.noZeroSMulDivisors /-
instance noZeroSMulDivisors [NoZeroSMulDivisors R M] : NoZeroSMulDivisors R p :=
  ⟨fun c x h =>
    have : c = 0 ∨ (x : M) = 0 := eq_zero_or_eq_zero_of_smul_eq_zero (congr_arg coe h)
    this.imp_right (@Subtype.ext_iff _ _ x 0).mpr⟩
#align submodule.no_zero_smul_divisors Submodule.noZeroSMulDivisors
-/

#print Submodule.subtype /-
/-- Embedding of a submodule `p` to the ambient space `M`. -/
protected def subtype : p →ₗ[R] M := by refine' { toFun := coe .. } <;> simp [coe_smul]
#align submodule.subtype Submodule.subtype
-/

#print Submodule.subtype_apply /-
theorem subtype_apply (x : p) : p.Subtype x = x :=
  rfl
#align submodule.subtype_apply Submodule.subtype_apply
-/

#print Submodule.coeSubtype /-
@[simp]
theorem coeSubtype : (Submodule.subtype p : p → M) = coe :=
  rfl
#align submodule.coe_subtype Submodule.coeSubtype
-/

#print Submodule.injective_subtype /-
theorem injective_subtype : Injective p.Subtype :=
  Subtype.coe_injective
#align submodule.injective_subtype Submodule.injective_subtype
-/

#print Submodule.coe_sum /-
/-- Note the `add_submonoid` version of this lemma is called `add_submonoid.coe_finset_sum`. -/
@[simp]
theorem coe_sum (x : ι → p) (s : Finset ι) : ↑(∑ i in s, x i) = ∑ i in s, (x i : M) :=
  map_sum p.Subtype _ _
#align submodule.coe_sum Submodule.coe_sum
-/

section AddAction

/-! ### Additive actions by `submodule`s

These instances transfer the action by an element `m : M` of a `R`-module `M` written as `m +ᵥ a`
onto the action by an element `s : S` of a submodule `S : submodule R M` such that
`s +ᵥ a = (s : M) +ᵥ a`.

These instances work particularly well in conjunction with `add_group.to_add_action`, enabling
`s +ᵥ m` as an alias for `↑s + m`.

-/


variable {α β : Type _}

instance [VAdd M α] : VAdd p α :=
  p.toAddSubmonoid.VAdd

#print Submodule.vaddCommClass /-
instance vaddCommClass [VAdd M β] [VAdd α β] [VAddCommClass M α β] : VAddCommClass p α β :=
  ⟨fun a => (vadd_comm (a : M) : _)⟩
#align submodule.vadd_comm_class Submodule.vaddCommClass
-/

instance [VAdd M α] [FaithfulVAdd M α] : FaithfulVAdd p α :=
  ⟨fun x y h => Subtype.ext <| eq_of_vadd_eq_vadd h⟩

/-- The action by a submodule is the action by the underlying module. -/
instance [AddAction M α] : AddAction p α :=
  AddAction.compHom _ p.Subtype.toAddMonoidHom

variable {p}

#print Submodule.vadd_def /-
theorem vadd_def [VAdd M α] (g : p) (m : α) : g +ᵥ m = (g : M) +ᵥ m :=
  rfl
#align submodule.vadd_def Submodule.vadd_def
-/

end AddAction

section RestrictScalars

variable (S) [Semiring S] [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]

#print Submodule.restrictScalars /-
/-- `V.restrict_scalars S` is the `S`-submodule of the `S`-module given by restriction of scalars,
corresponding to `V`, an `R`-submodule of the original `R`-module.
-/
def restrictScalars (V : Submodule R M) : Submodule S M
    where
  carrier := V
  zero_mem' := V.zero_mem
  smul_mem' c m h := V.smul_of_tower_mem c h
  add_mem' x y hx hy := V.add_mem hx hy
#align submodule.restrict_scalars Submodule.restrictScalars
-/

#print Submodule.coe_restrictScalars /-
@[simp]
theorem coe_restrictScalars (V : Submodule R M) : (V.restrictScalars S : Set M) = V :=
  rfl
#align submodule.coe_restrict_scalars Submodule.coe_restrictScalars
-/

#print Submodule.restrictScalars_mem /-
@[simp]
theorem restrictScalars_mem (V : Submodule R M) (m : M) : m ∈ V.restrictScalars S ↔ m ∈ V :=
  Iff.refl _
#align submodule.restrict_scalars_mem Submodule.restrictScalars_mem
-/

#print Submodule.restrictScalars_self /-
@[simp]
theorem restrictScalars_self (V : Submodule R M) : V.restrictScalars R = V :=
  SetLike.coe_injective rfl
#align submodule.restrict_scalars_self Submodule.restrictScalars_self
-/

variable (R S M)

#print Submodule.restrictScalars_injective /-
theorem restrictScalars_injective :
    Function.Injective (restrictScalars S : Submodule R M → Submodule S M) := fun V₁ V₂ h =>
  ext <| Set.ext_iff.1 (SetLike.ext'_iff.1 h : _)
#align submodule.restrict_scalars_injective Submodule.restrictScalars_injective
-/

#print Submodule.restrictScalars_inj /-
@[simp]
theorem restrictScalars_inj {V₁ V₂ : Submodule R M} :
    restrictScalars S V₁ = restrictScalars S V₂ ↔ V₁ = V₂ :=
  (restrictScalars_injective S _ _).eq_iff
#align submodule.restrict_scalars_inj Submodule.restrictScalars_inj
-/

#print Submodule.restrictScalars.origModule /-
/-- Even though `p.restrict_scalars S` has type `submodule S M`, it is still an `R`-module. -/
instance restrictScalars.origModule (p : Submodule R M) : Module R (p.restrictScalars S) :=
  (by infer_instance : Module R p)
#align submodule.restrict_scalars.orig_module Submodule.restrictScalars.origModule
-/

instance (p : Submodule R M) : IsScalarTower S R (p.restrictScalars S)
    where smul_assoc r s x := Subtype.ext <| smul_assoc r s (x : M)

#print Submodule.restrictScalarsEmbedding /-
/-- `restrict_scalars S` is an embedding of the lattice of `R`-submodules into
the lattice of `S`-submodules. -/
@[simps]
def restrictScalarsEmbedding : Submodule R M ↪o Submodule S M
    where
  toFun := restrictScalars S
  inj' := restrictScalars_injective S R M
  map_rel_iff' p q := by simp [SetLike.le_def]
#align submodule.restrict_scalars_embedding Submodule.restrictScalarsEmbedding
-/

#print Submodule.restrictScalarsEquiv /-
/-- Turning `p : submodule R M` into an `S`-submodule gives the same module structure
as turning it into a type and adding a module structure. -/
@[simps (config := { simpRhs := true })]
def restrictScalarsEquiv (p : Submodule R M) : p.restrictScalars S ≃ₗ[R] p :=
  { AddEquiv.refl p with
    toFun := id
    invFun := id
    map_smul' := fun c x => rfl }
#align submodule.restrict_scalars_equiv Submodule.restrictScalarsEquiv
-/

end RestrictScalars

end AddCommMonoid

section AddCommGroup

variable [Ring R] [AddCommGroup M]

variable {module_M : Module R M}

variable (p p' : Submodule R M)

variable {r : R} {x y : M}

instance [Module R M] : AddSubgroupClass (Submodule R M) M :=
  { Submodule.addSubmonoidClass with neg_mem := fun p x => p.toSubMulAction.neg_mem }

#print Submodule.neg_mem /-
protected theorem neg_mem (hx : x ∈ p) : -x ∈ p :=
  neg_mem hx
#align submodule.neg_mem Submodule.neg_mem
-/

#print Submodule.toAddSubgroup /-
/-- Reinterpret a submodule as an additive subgroup. -/
def toAddSubgroup : AddSubgroup M :=
  { p.toAddSubmonoid with neg_mem' := fun _ => p.neg_mem }
#align submodule.to_add_subgroup Submodule.toAddSubgroup
-/

#print Submodule.coe_toAddSubgroup /-
@[simp]
theorem coe_toAddSubgroup : (p.toAddSubgroup : Set M) = p :=
  rfl
#align submodule.coe_to_add_subgroup Submodule.coe_toAddSubgroup
-/

#print Submodule.mem_toAddSubgroup /-
@[simp]
theorem mem_toAddSubgroup : x ∈ p.toAddSubgroup ↔ x ∈ p :=
  Iff.rfl
#align submodule.mem_to_add_subgroup Submodule.mem_toAddSubgroup
-/

#print Submodule.toAddSubgroup_injective /-
theorem toAddSubgroup_injective : Injective (toAddSubgroup : Submodule R M → AddSubgroup M)
  | p, q, h => SetLike.ext (SetLike.ext_iff.1 h : _)
#align submodule.to_add_subgroup_injective Submodule.toAddSubgroup_injective
-/

#print Submodule.toAddSubgroup_eq /-
@[simp]
theorem toAddSubgroup_eq : p.toAddSubgroup = p'.toAddSubgroup ↔ p = p' :=
  toAddSubgroup_injective.eq_iff
#align submodule.to_add_subgroup_eq Submodule.toAddSubgroup_eq
-/

#print Submodule.toAddSubgroup_strictMono /-
@[mono]
theorem toAddSubgroup_strictMono : StrictMono (toAddSubgroup : Submodule R M → AddSubgroup M) :=
  fun _ _ => id
#align submodule.to_add_subgroup_strict_mono Submodule.toAddSubgroup_strictMono
-/

#print Submodule.toAddSubgroup_le /-
theorem toAddSubgroup_le : p.toAddSubgroup ≤ p'.toAddSubgroup ↔ p ≤ p' :=
  Iff.rfl
#align submodule.to_add_subgroup_le Submodule.toAddSubgroup_le
-/

#print Submodule.toAddSubgroup_mono /-
@[mono]
theorem toAddSubgroup_mono : Monotone (toAddSubgroup : Submodule R M → AddSubgroup M) :=
  toAddSubgroup_strictMono.Monotone
#align submodule.to_add_subgroup_mono Submodule.toAddSubgroup_mono
-/

#print Submodule.sub_mem /-
protected theorem sub_mem : x ∈ p → y ∈ p → x - y ∈ p :=
  sub_mem
#align submodule.sub_mem Submodule.sub_mem
-/

#print Submodule.neg_mem_iff /-
protected theorem neg_mem_iff : -x ∈ p ↔ x ∈ p :=
  neg_mem_iff
#align submodule.neg_mem_iff Submodule.neg_mem_iff
-/

#print Submodule.add_mem_iff_left /-
protected theorem add_mem_iff_left : y ∈ p → (x + y ∈ p ↔ x ∈ p) :=
  add_mem_cancel_right
#align submodule.add_mem_iff_left Submodule.add_mem_iff_left
-/

#print Submodule.add_mem_iff_right /-
protected theorem add_mem_iff_right : x ∈ p → (x + y ∈ p ↔ y ∈ p) :=
  add_mem_cancel_left
#align submodule.add_mem_iff_right Submodule.add_mem_iff_right
-/

#print Submodule.coe_neg /-
protected theorem coe_neg (x : p) : ((-x : p) : M) = -x :=
  AddSubgroupClass.coe_neg _
#align submodule.coe_neg Submodule.coe_neg
-/

#print Submodule.coe_sub /-
protected theorem coe_sub (x y : p) : (↑(x - y) : M) = ↑x - ↑y :=
  AddSubgroupClass.coe_sub _ _
#align submodule.coe_sub Submodule.coe_sub
-/

#print Submodule.sub_mem_iff_left /-
theorem sub_mem_iff_left (hy : y ∈ p) : x - y ∈ p ↔ x ∈ p := by
  rw [sub_eq_add_neg, p.add_mem_iff_left (p.neg_mem hy)]
#align submodule.sub_mem_iff_left Submodule.sub_mem_iff_left
-/

#print Submodule.sub_mem_iff_right /-
theorem sub_mem_iff_right (hx : x ∈ p) : x - y ∈ p ↔ y ∈ p := by
  rw [sub_eq_add_neg, p.add_mem_iff_right hx, p.neg_mem_iff]
#align submodule.sub_mem_iff_right Submodule.sub_mem_iff_right
-/

instance : AddCommGroup p :=
  { p.toAddSubgroup.toAddCommGroup with
    add := (· + ·)
    zero := 0
    neg := Neg.neg }

end AddCommGroup

section IsDomain

variable [Ring R] [IsDomain R]

variable [AddCommGroup M] [Module R M] {b : ι → M}

#print Submodule.not_mem_of_ortho /-
theorem not_mem_of_ortho {x : M} {N : Submodule R M}
    (ortho : ∀ (c : R), ∀ y ∈ N, c • x + y = (0 : M) → c = 0) : x ∉ N := by intro hx;
  simpa using ortho (-1) x hx
#align submodule.not_mem_of_ortho Submodule.not_mem_of_ortho
-/

#print Submodule.ne_zero_of_ortho /-
theorem ne_zero_of_ortho {x : M} {N : Submodule R M}
    (ortho : ∀ (c : R), ∀ y ∈ N, c • x + y = (0 : M) → c = 0) : x ≠ 0 :=
  mt (fun h => show x ∈ N from h.symm ▸ N.zero_mem) (not_mem_of_ortho ortho)
#align submodule.ne_zero_of_ortho Submodule.ne_zero_of_ortho
-/

end IsDomain

section OrderedMonoid

variable [Semiring R]

#print Submodule.toOrderedAddCommMonoid /-
/-- A submodule of an `ordered_add_comm_monoid` is an `ordered_add_comm_monoid`. -/
instance toOrderedAddCommMonoid {M} [OrderedAddCommMonoid M] [Module R M] (S : Submodule R M) :
    OrderedAddCommMonoid S :=
  Subtype.coe_injective.OrderedAddCommMonoid coe rfl (fun _ _ => rfl) fun _ _ => rfl
#align submodule.to_ordered_add_comm_monoid Submodule.toOrderedAddCommMonoid
-/

#print Submodule.toLinearOrderedAddCommMonoid /-
/-- A submodule of a `linear_ordered_add_comm_monoid` is a `linear_ordered_add_comm_monoid`. -/
instance toLinearOrderedAddCommMonoid {M} [LinearOrderedAddCommMonoid M] [Module R M]
    (S : Submodule R M) : LinearOrderedAddCommMonoid S :=
  Subtype.coe_injective.LinearOrderedAddCommMonoid coe rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align submodule.to_linear_ordered_add_comm_monoid Submodule.toLinearOrderedAddCommMonoid
-/

#print Submodule.toOrderedCancelAddCommMonoid /-
/-- A submodule of an `ordered_cancel_add_comm_monoid` is an `ordered_cancel_add_comm_monoid`. -/
instance toOrderedCancelAddCommMonoid {M} [OrderedCancelAddCommMonoid M] [Module R M]
    (S : Submodule R M) : OrderedCancelAddCommMonoid S :=
  Subtype.coe_injective.OrderedCancelAddCommMonoid coe rfl (fun _ _ => rfl) fun _ _ => rfl
#align submodule.to_ordered_cancel_add_comm_monoid Submodule.toOrderedCancelAddCommMonoid
-/

#print Submodule.toLinearOrderedCancelAddCommMonoid /-
/-- A submodule of a `linear_ordered_cancel_add_comm_monoid` is a
`linear_ordered_cancel_add_comm_monoid`. -/
instance toLinearOrderedCancelAddCommMonoid {M} [LinearOrderedCancelAddCommMonoid M] [Module R M]
    (S : Submodule R M) : LinearOrderedCancelAddCommMonoid S :=
  Subtype.coe_injective.LinearOrderedCancelAddCommMonoid coe rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align submodule.to_linear_ordered_cancel_add_comm_monoid Submodule.toLinearOrderedCancelAddCommMonoid
-/

end OrderedMonoid

section OrderedGroup

variable [Ring R]

#print Submodule.toOrderedAddCommGroup /-
/-- A submodule of an `ordered_add_comm_group` is an `ordered_add_comm_group`. -/
instance toOrderedAddCommGroup {M} [OrderedAddCommGroup M] [Module R M] (S : Submodule R M) :
    OrderedAddCommGroup S :=
  Subtype.coe_injective.OrderedAddCommGroup coe rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align submodule.to_ordered_add_comm_group Submodule.toOrderedAddCommGroup
-/

#print Submodule.toLinearOrderedAddCommGroup /-
/-- A submodule of a `linear_ordered_add_comm_group` is a
`linear_ordered_add_comm_group`. -/
instance toLinearOrderedAddCommGroup {M} [LinearOrderedAddCommGroup M] [Module R M]
    (S : Submodule R M) : LinearOrderedAddCommGroup S :=
  Subtype.coe_injective.LinearOrderedAddCommGroup coe rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align submodule.to_linear_ordered_add_comm_group Submodule.toLinearOrderedAddCommGroup
-/

end OrderedGroup

end Submodule

namespace Submodule

variable [DivisionRing S] [Semiring R] [AddCommMonoid M] [Module R M]

variable [SMul S R] [Module S M] [IsScalarTower S R M]

variable (p : Submodule R M) {s : S} {x y : M}

#print Submodule.smul_mem_iff /-
theorem smul_mem_iff (s0 : s ≠ 0) : s • x ∈ p ↔ x ∈ p :=
  p.toSubMulAction.smul_mem_iff s0
#align submodule.smul_mem_iff Submodule.smul_mem_iff
-/

end Submodule

#print Subspace /-
/-- Subspace of a vector space. Defined to equal `submodule`. -/
abbrev Subspace (R : Type u) (M : Type v) [DivisionRing R] [AddCommGroup M] [Module R M] :=
  Submodule R M
#align subspace Subspace
-/

