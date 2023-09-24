/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky, Jireh Loreaux
-/
import GroupTheory.Subsemigroup.Basic
import Algebra.Group.Prod
import Algebra.Group.TypeTags

#align_import group_theory.subsemigroup.operations from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

/-!
# Operations on `subsemigroup`s

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define various operations on `subsemigroup`s and `mul_hom`s.

## Main definitions

### Conversion between multiplicative and additive definitions

* `subsemigroup.to_add_subsemigroup`, `subsemigroup.to_add_subsemigroup'`,
  `add_subsemigroup.to_subsemigroup`, `add_subsemigroup.to_subsemigroup'`:
  convert between multiplicative and additive subsemigroups of `M`,
  `multiplicative M`, and `additive M`. These are stated as `order_iso`s.

### (Commutative) semigroup structure on a subsemigroup

* `subsemigroup.to_semigroup`, `subsemigroup.to_comm_semigroup`: a subsemigroup inherits a
  (commutative) semigroup structure.

### Operations on subsemigroups

* `subsemigroup.comap`: preimage of a subsemigroup under a semigroup homomorphism as a subsemigroup
  of the domain;
* `subsemigroup.map`: image of a subsemigroup under a semigroup homomorphism as a subsemigroup of
  the codomain;
* `subsemigroup.prod`: product of two subsemigroups `s : subsemigroup M` and `t : subsemigroup N`
  as a subsemigroup of `M × N`;

### Semigroup homomorphisms between subsemigroups

* `subsemigroup.subtype`: embedding of a subsemigroup into the ambient semigroup.
* `subsemigroup.inclusion`: given two subsemigroups `S`, `T` such that `S ≤ T`, `S.inclusion T` is
  the inclusion of `S` into `T` as a semigroup homomorphism;
* `mul_equiv.subsemigroup_congr`: converts a proof of `S = T` into a semigroup isomorphism between
  `S` and `T`.
* `subsemigroup.prod_equiv`: semigroup isomorphism between `s.prod t` and `s × t`;

### Operations on `mul_hom`s

* `mul_hom.srange`: range of a semigroup homomorphism as a subsemigroup of the codomain;
* `mul_hom.restrict`: restrict a semigroup homomorphism to a subsemigroup;
* `mul_hom.cod_restrict`: restrict the codomain of a semigroup homomorphism to a subsemigroup;
* `mul_hom.srange_restrict`: restrict a semigroup homomorphism to its range;

### Implementation notes

This file follows closely `group_theory/submonoid/operations.lean`, omitting only that which is
necessary.

## Tags

subsemigroup, range, product, map, comap
-/


variable {M N P σ : Type _}

/-!
### Conversion to/from `additive`/`multiplicative`
-/


section

variable [Mul M]

#print Subsemigroup.toAddSubsemigroup /-
/-- Subsemigroups of semigroup `M` are isomorphic to additive subsemigroups of `additive M`. -/
@[simps]
def Subsemigroup.toAddSubsemigroup : Subsemigroup M ≃o AddSubsemigroup (Additive M)
    where
  toFun S :=
    { carrier := Additive.toMul ⁻¹' S
      add_mem' := fun _ _ => S.hMul_mem' }
  invFun S :=
    { carrier := Additive.ofMul ⁻¹' S
      hMul_mem' := fun _ _ => S.add_mem' }
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl
  map_rel_iff' a b := Iff.rfl
#align subsemigroup.to_add_subsemigroup Subsemigroup.toAddSubsemigroup
-/

#print AddSubsemigroup.toSubsemigroup' /-
/-- Additive subsemigroups of an additive semigroup `additive M` are isomorphic to subsemigroups
of `M`. -/
abbrev AddSubsemigroup.toSubsemigroup' : AddSubsemigroup (Additive M) ≃o Subsemigroup M :=
  Subsemigroup.toAddSubsemigroup.symm
#align add_subsemigroup.to_subsemigroup' AddSubsemigroup.toSubsemigroup'
-/

#print Subsemigroup.toAddSubsemigroup_closure /-
theorem Subsemigroup.toAddSubsemigroup_closure (S : Set M) :
    (Subsemigroup.closure S).toAddSubsemigroup = AddSubsemigroup.closure (Additive.toMul ⁻¹' S) :=
  le_antisymm
    (Subsemigroup.toAddSubsemigroup.le_symm_apply.1 <|
      Subsemigroup.closure_le.2 AddSubsemigroup.subset_closure)
    (AddSubsemigroup.closure_le.2 Subsemigroup.subset_closure)
#align subsemigroup.to_add_subsemigroup_closure Subsemigroup.toAddSubsemigroup_closure
-/

#print AddSubsemigroup.toSubsemigroup'_closure /-
theorem AddSubsemigroup.toSubsemigroup'_closure (S : Set (Additive M)) :
    (AddSubsemigroup.closure S).toSubsemigroup' =
      Subsemigroup.closure (Multiplicative.ofAdd ⁻¹' S) :=
  le_antisymm
    (AddSubsemigroup.toSubsemigroup'.le_symm_apply.1 <|
      AddSubsemigroup.closure_le.2 Subsemigroup.subset_closure)
    (Subsemigroup.closure_le.2 AddSubsemigroup.subset_closure)
#align add_subsemigroup.to_subsemigroup'_closure AddSubsemigroup.toSubsemigroup'_closure
-/

end

section

variable {A : Type _} [Add A]

#print AddSubsemigroup.toSubsemigroup /-
/-- Additive subsemigroups of an additive semigroup `A` are isomorphic to
multiplicative subsemigroups of `multiplicative A`. -/
@[simps]
def AddSubsemigroup.toSubsemigroup : AddSubsemigroup A ≃o Subsemigroup (Multiplicative A)
    where
  toFun S :=
    { carrier := Multiplicative.toAdd ⁻¹' S
      hMul_mem' := fun _ _ => S.add_mem' }
  invFun S :=
    { carrier := Multiplicative.ofAdd ⁻¹' S
      add_mem' := fun _ _ => S.hMul_mem' }
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl
  map_rel_iff' a b := Iff.rfl
#align add_subsemigroup.to_subsemigroup AddSubsemigroup.toSubsemigroup
-/

#print Subsemigroup.toAddSubsemigroup' /-
/-- Subsemigroups of a semigroup `multiplicative A` are isomorphic to additive subsemigroups
of `A`. -/
abbrev Subsemigroup.toAddSubsemigroup' : Subsemigroup (Multiplicative A) ≃o AddSubsemigroup A :=
  AddSubsemigroup.toSubsemigroup.symm
#align subsemigroup.to_add_subsemigroup' Subsemigroup.toAddSubsemigroup'
-/

#print AddSubsemigroup.toSubsemigroup_closure /-
theorem AddSubsemigroup.toSubsemigroup_closure (S : Set A) :
    (AddSubsemigroup.closure S).toSubsemigroup =
      Subsemigroup.closure (Multiplicative.toAdd ⁻¹' S) :=
  le_antisymm
    (AddSubsemigroup.toSubsemigroup.to_galoisConnection.l_le <|
      AddSubsemigroup.closure_le.2 Subsemigroup.subset_closure)
    (Subsemigroup.closure_le.2 AddSubsemigroup.subset_closure)
#align add_subsemigroup.to_subsemigroup_closure AddSubsemigroup.toSubsemigroup_closure
-/

#print Subsemigroup.toAddSubsemigroup'_closure /-
theorem Subsemigroup.toAddSubsemigroup'_closure (S : Set (Multiplicative A)) :
    (Subsemigroup.closure S).toAddSubsemigroup' = AddSubsemigroup.closure (Additive.ofMul ⁻¹' S) :=
  le_antisymm
    (Subsemigroup.toAddSubsemigroup'.to_galoisConnection.l_le <|
      Subsemigroup.closure_le.2 AddSubsemigroup.subset_closure)
    (AddSubsemigroup.closure_le.2 Subsemigroup.subset_closure)
#align subsemigroup.to_add_subsemigroup'_closure Subsemigroup.toAddSubsemigroup'_closure
-/

end

namespace Subsemigroup

open Set

/-!
### `comap` and `map`
-/


variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

#print Subsemigroup.comap /-
/-- The preimage of a subsemigroup along a semigroup homomorphism is a subsemigroup. -/
@[to_additive
      "The preimage of an `add_subsemigroup` along an `add_semigroup` homomorphism is an\n`add_subsemigroup`."]
def comap (f : M →ₙ* N) (S : Subsemigroup N) : Subsemigroup M
    where
  carrier := f ⁻¹' S
  hMul_mem' a b ha hb := show f (a * b) ∈ S by rw [map_mul] <;> exact mul_mem ha hb
#align subsemigroup.comap Subsemigroup.comap
#align add_subsemigroup.comap AddSubsemigroup.comap
-/

#print Subsemigroup.coe_comap /-
@[simp, to_additive]
theorem coe_comap (S : Subsemigroup N) (f : M →ₙ* N) : (S.comap f : Set M) = f ⁻¹' S :=
  rfl
#align subsemigroup.coe_comap Subsemigroup.coe_comap
#align add_subsemigroup.coe_comap AddSubsemigroup.coe_comap
-/

#print Subsemigroup.mem_comap /-
@[simp, to_additive]
theorem mem_comap {S : Subsemigroup N} {f : M →ₙ* N} {x : M} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl
#align subsemigroup.mem_comap Subsemigroup.mem_comap
#align add_subsemigroup.mem_comap AddSubsemigroup.mem_comap
-/

#print Subsemigroup.comap_comap /-
@[to_additive]
theorem comap_comap (S : Subsemigroup P) (g : N →ₙ* P) (f : M →ₙ* N) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl
#align subsemigroup.comap_comap Subsemigroup.comap_comap
#align add_subsemigroup.comap_comap AddSubsemigroup.comap_comap
-/

#print Subsemigroup.comap_id /-
@[simp, to_additive]
theorem comap_id (S : Subsemigroup P) : S.comap (MulHom.id _) = S :=
  ext (by simp)
#align subsemigroup.comap_id Subsemigroup.comap_id
#align add_subsemigroup.comap_id AddSubsemigroup.comap_id
-/

#print Subsemigroup.map /-
/-- The image of a subsemigroup along a semigroup homomorphism is a subsemigroup. -/
@[to_additive
      "The image of an `add_subsemigroup` along an `add_semigroup` homomorphism is\nan `add_subsemigroup`."]
def map (f : M →ₙ* N) (S : Subsemigroup M) : Subsemigroup N
    where
  carrier := f '' S
  hMul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, @mul_mem (Subsemigroup M) M _ _ _ _ _ _ hx hy, by rw [map_mul] <;> rfl⟩
#align subsemigroup.map Subsemigroup.map
#align add_subsemigroup.map AddSubsemigroup.map
-/

#print Subsemigroup.coe_map /-
@[simp, to_additive]
theorem coe_map (f : M →ₙ* N) (S : Subsemigroup M) : (S.map f : Set N) = f '' S :=
  rfl
#align subsemigroup.coe_map Subsemigroup.coe_map
#align add_subsemigroup.coe_map AddSubsemigroup.coe_map
-/

#print Subsemigroup.mem_map /-
@[simp, to_additive]
theorem mem_map {f : M →ₙ* N} {S : Subsemigroup M} {y : N} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  mem_image_iff_bex
#align subsemigroup.mem_map Subsemigroup.mem_map
#align add_subsemigroup.mem_map AddSubsemigroup.mem_map
-/

#print Subsemigroup.mem_map_of_mem /-
@[to_additive]
theorem mem_map_of_mem (f : M →ₙ* N) {S : Subsemigroup M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
  mem_image_of_mem f hx
#align subsemigroup.mem_map_of_mem Subsemigroup.mem_map_of_mem
#align add_subsemigroup.mem_map_of_mem AddSubsemigroup.mem_map_of_mem
-/

#print Subsemigroup.apply_coe_mem_map /-
@[to_additive]
theorem apply_coe_mem_map (f : M →ₙ* N) (S : Subsemigroup M) (x : S) : f x ∈ S.map f :=
  mem_map_of_mem f x.Prop
#align subsemigroup.apply_coe_mem_map Subsemigroup.apply_coe_mem_map
#align add_subsemigroup.apply_coe_mem_map AddSubsemigroup.apply_coe_mem_map
-/

#print Subsemigroup.map_map /-
@[to_additive]
theorem map_map (g : N →ₙ* P) (f : M →ₙ* N) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| image_image _ _ _
#align subsemigroup.map_map Subsemigroup.map_map
#align add_subsemigroup.map_map AddSubsemigroup.map_map
-/

#print Subsemigroup.mem_map_iff_mem /-
@[to_additive]
theorem mem_map_iff_mem {f : M →ₙ* N} (hf : Function.Injective f) {S : Subsemigroup M} {x : M} :
    f x ∈ S.map f ↔ x ∈ S :=
  hf.mem_set_image
#align subsemigroup.mem_map_iff_mem Subsemigroup.mem_map_iff_mem
#align add_subsemigroup.mem_map_iff_mem AddSubsemigroup.mem_map_iff_mem
-/

#print Subsemigroup.map_le_iff_le_comap /-
@[to_additive]
theorem map_le_iff_le_comap {f : M →ₙ* N} {S : Subsemigroup M} {T : Subsemigroup N} :
    S.map f ≤ T ↔ S ≤ T.comap f :=
  image_subset_iff
#align subsemigroup.map_le_iff_le_comap Subsemigroup.map_le_iff_le_comap
#align add_subsemigroup.map_le_iff_le_comap AddSubsemigroup.map_le_iff_le_comap
-/

#print Subsemigroup.gc_map_comap /-
@[to_additive]
theorem gc_map_comap (f : M →ₙ* N) : GaloisConnection (map f) (comap f) := fun S T =>
  map_le_iff_le_comap
#align subsemigroup.gc_map_comap Subsemigroup.gc_map_comap
#align add_subsemigroup.gc_map_comap AddSubsemigroup.gc_map_comap
-/

#print Subsemigroup.map_le_of_le_comap /-
@[to_additive]
theorem map_le_of_le_comap {T : Subsemigroup N} {f : M →ₙ* N} : S ≤ T.comap f → S.map f ≤ T :=
  (gc_map_comap f).l_le
#align subsemigroup.map_le_of_le_comap Subsemigroup.map_le_of_le_comap
#align add_subsemigroup.map_le_of_le_comap AddSubsemigroup.map_le_of_le_comap
-/

#print Subsemigroup.le_comap_of_map_le /-
@[to_additive]
theorem le_comap_of_map_le {T : Subsemigroup N} {f : M →ₙ* N} : S.map f ≤ T → S ≤ T.comap f :=
  (gc_map_comap f).le_u
#align subsemigroup.le_comap_of_map_le Subsemigroup.le_comap_of_map_le
#align add_subsemigroup.le_comap_of_map_le AddSubsemigroup.le_comap_of_map_le
-/

#print Subsemigroup.le_comap_map /-
@[to_additive]
theorem le_comap_map {f : M →ₙ* N} : S ≤ (S.map f).comap f :=
  (gc_map_comap f).le_u_l _
#align subsemigroup.le_comap_map Subsemigroup.le_comap_map
#align add_subsemigroup.le_comap_map AddSubsemigroup.le_comap_map
-/

#print Subsemigroup.map_comap_le /-
@[to_additive]
theorem map_comap_le {S : Subsemigroup N} {f : M →ₙ* N} : (S.comap f).map f ≤ S :=
  (gc_map_comap f).l_u_le _
#align subsemigroup.map_comap_le Subsemigroup.map_comap_le
#align add_subsemigroup.map_comap_le AddSubsemigroup.map_comap_le
-/

#print Subsemigroup.monotone_map /-
@[to_additive]
theorem monotone_map {f : M →ₙ* N} : Monotone (map f) :=
  (gc_map_comap f).monotone_l
#align subsemigroup.monotone_map Subsemigroup.monotone_map
#align add_subsemigroup.monotone_map AddSubsemigroup.monotone_map
-/

#print Subsemigroup.monotone_comap /-
@[to_additive]
theorem monotone_comap {f : M →ₙ* N} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u
#align subsemigroup.monotone_comap Subsemigroup.monotone_comap
#align add_subsemigroup.monotone_comap AddSubsemigroup.monotone_comap
-/

#print Subsemigroup.map_comap_map /-
@[simp, to_additive]
theorem map_comap_map {f : M →ₙ* N} : ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _
#align subsemigroup.map_comap_map Subsemigroup.map_comap_map
#align add_subsemigroup.map_comap_map AddSubsemigroup.map_comap_map
-/

#print Subsemigroup.comap_map_comap /-
@[simp, to_additive]
theorem comap_map_comap {S : Subsemigroup N} {f : M →ₙ* N} :
    ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _
#align subsemigroup.comap_map_comap Subsemigroup.comap_map_comap
#align add_subsemigroup.comap_map_comap AddSubsemigroup.comap_map_comap
-/

#print Subsemigroup.map_sup /-
@[to_additive]
theorem map_sup (S T : Subsemigroup M) (f : M →ₙ* N) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (gc_map_comap f).l_sup
#align subsemigroup.map_sup Subsemigroup.map_sup
#align add_subsemigroup.map_sup AddSubsemigroup.map_sup
-/

#print Subsemigroup.map_iSup /-
@[to_additive]
theorem map_iSup {ι : Sort _} (f : M →ₙ* N) (s : ι → Subsemigroup M) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup
#align subsemigroup.map_supr Subsemigroup.map_iSup
#align add_subsemigroup.map_supr AddSubsemigroup.map_iSup
-/

#print Subsemigroup.comap_inf /-
@[to_additive]
theorem comap_inf (S T : Subsemigroup N) (f : M →ₙ* N) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
  (gc_map_comap f).u_inf
#align subsemigroup.comap_inf Subsemigroup.comap_inf
#align add_subsemigroup.comap_inf AddSubsemigroup.comap_inf
-/

#print Subsemigroup.comap_iInf /-
@[to_additive]
theorem comap_iInf {ι : Sort _} (f : M →ₙ* N) (s : ι → Subsemigroup N) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf
#align subsemigroup.comap_infi Subsemigroup.comap_iInf
#align add_subsemigroup.comap_infi AddSubsemigroup.comap_iInf
-/

#print Subsemigroup.map_bot /-
@[simp, to_additive]
theorem map_bot (f : M →ₙ* N) : (⊥ : Subsemigroup M).map f = ⊥ :=
  (gc_map_comap f).l_bot
#align subsemigroup.map_bot Subsemigroup.map_bot
#align add_subsemigroup.map_bot AddSubsemigroup.map_bot
-/

#print Subsemigroup.comap_top /-
@[simp, to_additive]
theorem comap_top (f : M →ₙ* N) : (⊤ : Subsemigroup N).comap f = ⊤ :=
  (gc_map_comap f).u_top
#align subsemigroup.comap_top Subsemigroup.comap_top
#align add_subsemigroup.comap_top AddSubsemigroup.comap_top
-/

#print Subsemigroup.map_id /-
@[simp, to_additive]
theorem map_id (S : Subsemigroup M) : S.map (MulHom.id M) = S :=
  ext fun x => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩
#align subsemigroup.map_id Subsemigroup.map_id
#align add_subsemigroup.map_id AddSubsemigroup.map_id
-/

section GaloisCoinsertion

variable {ι : Type _} {f : M →ₙ* N} (hf : Function.Injective f)

#print Subsemigroup.gciMapComap /-
/-- `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. -/
@[to_additive " `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. "]
def gciMapComap : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap, mem_map, hf.eq_iff]
#align subsemigroup.gci_map_comap Subsemigroup.gciMapComap
#align add_subsemigroup.gci_map_comap AddSubsemigroup.gciMapComap
-/

#print Subsemigroup.comap_map_eq_of_injective /-
@[to_additive]
theorem comap_map_eq_of_injective (S : Subsemigroup M) : (S.map f).comap f = S :=
  (gciMapComap hf).u_l_eq _
#align subsemigroup.comap_map_eq_of_injective Subsemigroup.comap_map_eq_of_injective
#align add_subsemigroup.comap_map_eq_of_injective AddSubsemigroup.comap_map_eq_of_injective
-/

#print Subsemigroup.comap_surjective_of_injective /-
@[to_additive]
theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective
#align subsemigroup.comap_surjective_of_injective Subsemigroup.comap_surjective_of_injective
#align add_subsemigroup.comap_surjective_of_injective AddSubsemigroup.comap_surjective_of_injective
-/

#print Subsemigroup.map_injective_of_injective /-
@[to_additive]
theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective
#align subsemigroup.map_injective_of_injective Subsemigroup.map_injective_of_injective
#align add_subsemigroup.map_injective_of_injective AddSubsemigroup.map_injective_of_injective
-/

#print Subsemigroup.comap_inf_map_of_injective /-
@[to_additive]
theorem comap_inf_map_of_injective (S T : Subsemigroup M) : (S.map f ⊓ T.map f).comap f = S ⊓ T :=
  (gciMapComap hf).u_inf_l _ _
#align subsemigroup.comap_inf_map_of_injective Subsemigroup.comap_inf_map_of_injective
#align add_subsemigroup.comap_inf_map_of_injective AddSubsemigroup.comap_inf_map_of_injective
-/

#print Subsemigroup.comap_iInf_map_of_injective /-
@[to_additive]
theorem comap_iInf_map_of_injective (S : ι → Subsemigroup M) :
    (⨅ i, (S i).map f).comap f = iInf S :=
  (gciMapComap hf).u_iInf_l _
#align subsemigroup.comap_infi_map_of_injective Subsemigroup.comap_iInf_map_of_injective
#align add_subsemigroup.comap_infi_map_of_injective AddSubsemigroup.comap_iInf_map_of_injective
-/

#print Subsemigroup.comap_sup_map_of_injective /-
@[to_additive]
theorem comap_sup_map_of_injective (S T : Subsemigroup M) : (S.map f ⊔ T.map f).comap f = S ⊔ T :=
  (gciMapComap hf).u_sup_l _ _
#align subsemigroup.comap_sup_map_of_injective Subsemigroup.comap_sup_map_of_injective
#align add_subsemigroup.comap_sup_map_of_injective AddSubsemigroup.comap_sup_map_of_injective
-/

#print Subsemigroup.comap_iSup_map_of_injective /-
@[to_additive]
theorem comap_iSup_map_of_injective (S : ι → Subsemigroup M) :
    (⨆ i, (S i).map f).comap f = iSup S :=
  (gciMapComap hf).u_iSup_l _
#align subsemigroup.comap_supr_map_of_injective Subsemigroup.comap_iSup_map_of_injective
#align add_subsemigroup.comap_supr_map_of_injective AddSubsemigroup.comap_iSup_map_of_injective
-/

#print Subsemigroup.map_le_map_iff_of_injective /-
@[to_additive]
theorem map_le_map_iff_of_injective {S T : Subsemigroup M} : S.map f ≤ T.map f ↔ S ≤ T :=
  (gciMapComap hf).l_le_l_iff
#align subsemigroup.map_le_map_iff_of_injective Subsemigroup.map_le_map_iff_of_injective
#align add_subsemigroup.map_le_map_iff_of_injective AddSubsemigroup.map_le_map_iff_of_injective
-/

#print Subsemigroup.map_strictMono_of_injective /-
@[to_additive]
theorem map_strictMono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strictMono_l
#align subsemigroup.map_strict_mono_of_injective Subsemigroup.map_strictMono_of_injective
#align add_subsemigroup.map_strict_mono_of_injective AddSubsemigroup.map_strictMono_of_injective
-/

end GaloisCoinsertion

section GaloisInsertion

variable {ι : Type _} {f : M →ₙ* N} (hf : Function.Surjective f)

#print Subsemigroup.giMapComap /-
/-- `map f` and `comap f` form a `galois_insertion` when `f` is surjective. -/
@[to_additive " `map f` and `comap f` form a `galois_insertion` when `f` is surjective. "]
def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩
#align subsemigroup.gi_map_comap Subsemigroup.giMapComap
#align add_subsemigroup.gi_map_comap AddSubsemigroup.giMapComap
-/

#print Subsemigroup.map_comap_eq_of_surjective /-
@[to_additive]
theorem map_comap_eq_of_surjective (S : Subsemigroup N) : (S.comap f).map f = S :=
  (giMapComap hf).l_u_eq _
#align subsemigroup.map_comap_eq_of_surjective Subsemigroup.map_comap_eq_of_surjective
#align add_subsemigroup.map_comap_eq_of_surjective AddSubsemigroup.map_comap_eq_of_surjective
-/

#print Subsemigroup.map_surjective_of_surjective /-
@[to_additive]
theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective
#align subsemigroup.map_surjective_of_surjective Subsemigroup.map_surjective_of_surjective
#align add_subsemigroup.map_surjective_of_surjective AddSubsemigroup.map_surjective_of_surjective
-/

#print Subsemigroup.comap_injective_of_surjective /-
@[to_additive]
theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective
#align subsemigroup.comap_injective_of_surjective Subsemigroup.comap_injective_of_surjective
#align add_subsemigroup.comap_injective_of_surjective AddSubsemigroup.comap_injective_of_surjective
-/

#print Subsemigroup.map_inf_comap_of_surjective /-
@[to_additive]
theorem map_inf_comap_of_surjective (S T : Subsemigroup N) :
    (S.comap f ⊓ T.comap f).map f = S ⊓ T :=
  (giMapComap hf).l_inf_u _ _
#align subsemigroup.map_inf_comap_of_surjective Subsemigroup.map_inf_comap_of_surjective
#align add_subsemigroup.map_inf_comap_of_surjective AddSubsemigroup.map_inf_comap_of_surjective
-/

#print Subsemigroup.map_iInf_comap_of_surjective /-
@[to_additive]
theorem map_iInf_comap_of_surjective (S : ι → Subsemigroup N) :
    (⨅ i, (S i).comap f).map f = iInf S :=
  (giMapComap hf).l_iInf_u _
#align subsemigroup.map_infi_comap_of_surjective Subsemigroup.map_iInf_comap_of_surjective
#align add_subsemigroup.map_infi_comap_of_surjective AddSubsemigroup.map_iInf_comap_of_surjective
-/

#print Subsemigroup.map_sup_comap_of_surjective /-
@[to_additive]
theorem map_sup_comap_of_surjective (S T : Subsemigroup N) :
    (S.comap f ⊔ T.comap f).map f = S ⊔ T :=
  (giMapComap hf).l_sup_u _ _
#align subsemigroup.map_sup_comap_of_surjective Subsemigroup.map_sup_comap_of_surjective
#align add_subsemigroup.map_sup_comap_of_surjective AddSubsemigroup.map_sup_comap_of_surjective
-/

#print Subsemigroup.map_iSup_comap_of_surjective /-
@[to_additive]
theorem map_iSup_comap_of_surjective (S : ι → Subsemigroup N) :
    (⨆ i, (S i).comap f).map f = iSup S :=
  (giMapComap hf).l_iSup_u _
#align subsemigroup.map_supr_comap_of_surjective Subsemigroup.map_iSup_comap_of_surjective
#align add_subsemigroup.map_supr_comap_of_surjective AddSubsemigroup.map_iSup_comap_of_surjective
-/

#print Subsemigroup.comap_le_comap_iff_of_surjective /-
@[to_additive]
theorem comap_le_comap_iff_of_surjective {S T : Subsemigroup N} : S.comap f ≤ T.comap f ↔ S ≤ T :=
  (giMapComap hf).u_le_u_iff
#align subsemigroup.comap_le_comap_iff_of_surjective Subsemigroup.comap_le_comap_iff_of_surjective
#align add_subsemigroup.comap_le_comap_iff_of_surjective AddSubsemigroup.comap_le_comap_iff_of_surjective
-/

#print Subsemigroup.comap_strictMono_of_surjective /-
@[to_additive]
theorem comap_strictMono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strictMono_u
#align subsemigroup.comap_strict_mono_of_surjective Subsemigroup.comap_strictMono_of_surjective
#align add_subsemigroup.comap_strict_mono_of_surjective AddSubsemigroup.comap_strictMono_of_surjective
-/

end GaloisInsertion

end Subsemigroup

namespace MulMemClass

variable {A : Type _} [Mul M] [SetLike A M] [hA : MulMemClass A M] (S' : A)

#print MulMemClass.mul /-
-- lower priority so other instances are found first
/-- A submagma of a magma inherits a multiplication. -/
@[to_additive "An additive submagma of an additive magma inherits an addition."]
instance (priority := 900) mul : Mul S' :=
  ⟨fun a b => ⟨a.1 * b.1, hMul_mem a.2 b.2⟩⟩
#align mul_mem_class.has_mul MulMemClass.mul
#align add_mem_class.has_add AddMemClass.add
-/

#print MulMemClass.coe_mul /-
-- lower priority so later simp lemmas are used first; to appease simp_nf
@[simp, norm_cast, to_additive]
theorem coe_mul (x y : S') : (↑(x * y) : M) = ↑x * ↑y :=
  rfl
#align mul_mem_class.coe_mul MulMemClass.coe_mul
#align add_mem_class.coe_add AddMemClass.coe_add
-/

#print MulMemClass.mk_mul_mk /-
-- lower priority so later simp lemmas are used first; to appease simp_nf
@[simp, to_additive]
theorem mk_mul_mk (x y : M) (hx : x ∈ S') (hy : y ∈ S') :
    (⟨x, hx⟩ : S') * ⟨y, hy⟩ = ⟨x * y, hMul_mem hx hy⟩ :=
  rfl
#align mul_mem_class.mk_mul_mk MulMemClass.mk_mul_mk
#align add_mem_class.mk_add_mk AddMemClass.mk_add_mk
-/

#print MulMemClass.mul_def /-
@[to_additive]
theorem mul_def (x y : S') : x * y = ⟨x * y, hMul_mem x.2 y.2⟩ :=
  rfl
#align mul_mem_class.mul_def MulMemClass.mul_def
#align add_mem_class.add_def AddMemClass.add_def
-/

#print MulMemClass.toSemigroup /-
/-- A subsemigroup of a semigroup inherits a semigroup structure. -/
@[to_additive "An `add_subsemigroup` of an `add_semigroup` inherits an `add_semigroup` structure."]
instance toSemigroup {M : Type _} [Semigroup M] {A : Type _} [SetLike A M] [MulMemClass A M]
    (S : A) : Semigroup S :=
  Subtype.coe_injective.Semigroup coe fun _ _ => rfl
#align mul_mem_class.to_semigroup MulMemClass.toSemigroup
#align add_mem_class.to_add_semigroup AddMemClass.toAddSemigroup
-/

#print MulMemClass.toCommSemigroup /-
/-- A subsemigroup of a `comm_semigroup` is a `comm_semigroup`. -/
@[to_additive "An `add_subsemigroup` of an `add_comm_semigroup` is an `add_comm_semigroup`."]
instance toCommSemigroup {M} [CommSemigroup M] {A : Type _} [SetLike A M] [MulMemClass A M]
    (S : A) : CommSemigroup S :=
  Subtype.coe_injective.CommSemigroup coe fun _ _ => rfl
#align mul_mem_class.to_comm_semigroup MulMemClass.toCommSemigroup
#align add_mem_class.to_add_comm_semigroup AddMemClass.toAddCommSemigroup
-/

#print MulMemClass.subtype /-
/-- The natural semigroup hom from a subsemigroup of semigroup `M` to `M`. -/
@[to_additive "The natural semigroup hom from an `add_subsemigroup` of `add_semigroup` `M` to `M`."]
def subtype : S' →ₙ* M :=
  ⟨coe, fun _ _ => rfl⟩
#align mul_mem_class.subtype MulMemClass.subtype
#align add_mem_class.subtype AddMemClass.subtype
-/

#print MulMemClass.coe_subtype /-
@[simp, to_additive]
theorem coe_subtype : (MulMemClass.subtype S' : S' → M) = coe :=
  rfl
#align mul_mem_class.coe_subtype MulMemClass.coe_subtype
#align add_mem_class.coe_subtype AddMemClass.coe_subtype
-/

end MulMemClass

namespace Subsemigroup

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

#print Subsemigroup.topEquiv /-
/-- The top subsemigroup is isomorphic to the semigroup. -/
@[to_additive "The top additive subsemigroup is isomorphic to the additive semigroup.", simps]
def topEquiv : (⊤ : Subsemigroup M) ≃* M
    where
  toFun x := x
  invFun x := ⟨x, mem_top x⟩
  left_inv x := x.eta _
  right_inv _ := rfl
  map_mul' _ _ := rfl
#align subsemigroup.top_equiv Subsemigroup.topEquiv
#align add_subsemigroup.top_equiv AddSubsemigroup.topEquiv
-/

#print Subsemigroup.topEquiv_toMulHom /-
@[simp, to_additive]
theorem topEquiv_toMulHom :
    (topEquiv : _ ≃* M).toMulHom = MulMemClass.subtype (⊤ : Subsemigroup M) :=
  rfl
#align subsemigroup.top_equiv_to_mul_hom Subsemigroup.topEquiv_toMulHom
#align add_subsemigroup.top_equiv_to_add_hom AddSubsemigroup.topEquiv_toAddHom
-/

#print Subsemigroup.equivMapOfInjective /-
/-- A subsemigroup is isomorphic to its image under an injective function -/
@[to_additive "An additive subsemigroup is isomorphic to its image under an injective function"]
noncomputable def equivMapOfInjective (f : M →ₙ* N) (hf : Function.Injective f) : S ≃* S.map f :=
  { Equiv.Set.image f S hf with map_mul' := fun _ _ => Subtype.ext (map_mul f _ _) }
#align subsemigroup.equiv_map_of_injective Subsemigroup.equivMapOfInjective
#align add_subsemigroup.equiv_map_of_injective AddSubsemigroup.equivMapOfInjective
-/

#print Subsemigroup.coe_equivMapOfInjective_apply /-
@[simp, to_additive]
theorem coe_equivMapOfInjective_apply (f : M →ₙ* N) (hf : Function.Injective f) (x : S) :
    (equivMapOfInjective S f hf x : N) = f x :=
  rfl
#align subsemigroup.coe_equiv_map_of_injective_apply Subsemigroup.coe_equivMapOfInjective_apply
#align add_subsemigroup.coe_equiv_map_of_injective_apply AddSubsemigroup.coe_equivMapOfInjective_apply
-/

#print Subsemigroup.closure_closure_coe_preimage /-
@[simp, to_additive]
theorem closure_closure_coe_preimage {s : Set M} : closure ((coe : closure s → M) ⁻¹' s) = ⊤ :=
  eq_top_iff.2 fun x =>
    Subtype.recOn x fun x hx _ =>
      by
      refine' closure_induction' _ (fun g hg => _) (fun g₁ g₂ hg₁ hg₂ => _) hx
      · exact subset_closure hg
      · exact Subsemigroup.mul_mem _
#align subsemigroup.closure_closure_coe_preimage Subsemigroup.closure_closure_coe_preimage
#align add_subsemigroup.closure_closure_coe_preimage AddSubsemigroup.closure_closure_coe_preimage
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Subsemigroup.prod /-
/-- Given `subsemigroup`s `s`, `t` of semigroups `M`, `N` respectively, `s × t` as a subsemigroup
of `M × N`. -/
@[to_additive Prod
      "Given `add_subsemigroup`s `s`, `t` of `add_semigroup`s `A`, `B` respectively,\n`s × t` as an `add_subsemigroup` of `A × B`."]
def prod (s : Subsemigroup M) (t : Subsemigroup N) : Subsemigroup (M × N)
    where
  carrier := s ×ˢ t
  hMul_mem' p q hp hq := ⟨s.hMul_mem hp.1 hq.1, t.hMul_mem hp.2 hq.2⟩
#align subsemigroup.prod Subsemigroup.prod
#align add_subsemigroup.prod AddSubsemigroup.prod
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Subsemigroup.coe_prod /-
@[to_additive coe_prod]
theorem coe_prod (s : Subsemigroup M) (t : Subsemigroup N) : (s.Prod t : Set (M × N)) = s ×ˢ t :=
  rfl
#align subsemigroup.coe_prod Subsemigroup.coe_prod
#align add_subsemigroup.coe_prod AddSubsemigroup.coe_prod
-/

#print Subsemigroup.mem_prod /-
@[to_additive mem_prod]
theorem mem_prod {s : Subsemigroup M} {t : Subsemigroup N} {p : M × N} :
    p ∈ s.Prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl
#align subsemigroup.mem_prod Subsemigroup.mem_prod
#align add_subsemigroup.mem_prod AddSubsemigroup.mem_prod
-/

#print Subsemigroup.prod_mono /-
@[to_additive prod_mono]
theorem prod_mono {s₁ s₂ : Subsemigroup M} {t₁ t₂ : Subsemigroup N} (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) :
    s₁.Prod t₁ ≤ s₂.Prod t₂ :=
  Set.prod_mono hs ht
#align subsemigroup.prod_mono Subsemigroup.prod_mono
#align add_subsemigroup.prod_mono AddSubsemigroup.prod_mono
-/

#print Subsemigroup.prod_top /-
@[to_additive prod_top]
theorem prod_top (s : Subsemigroup M) : s.Prod (⊤ : Subsemigroup N) = s.comap (MulHom.fst M N) :=
  ext fun x => by simp [mem_prod, MulHom.coe_fst]
#align subsemigroup.prod_top Subsemigroup.prod_top
#align add_subsemigroup.prod_top AddSubsemigroup.prod_top
-/

#print Subsemigroup.top_prod /-
@[to_additive top_prod]
theorem top_prod (s : Subsemigroup N) : (⊤ : Subsemigroup M).Prod s = s.comap (MulHom.snd M N) :=
  ext fun x => by simp [mem_prod, MulHom.coe_snd]
#align subsemigroup.top_prod Subsemigroup.top_prod
#align add_subsemigroup.top_prod AddSubsemigroup.top_prod
-/

#print Subsemigroup.top_prod_top /-
@[simp, to_additive top_prod_top]
theorem top_prod_top : (⊤ : Subsemigroup M).Prod (⊤ : Subsemigroup N) = ⊤ :=
  (top_prod _).trans <| comap_top _
#align subsemigroup.top_prod_top Subsemigroup.top_prod_top
#align add_subsemigroup.top_prod_top AddSubsemigroup.top_prod_top
-/

#print Subsemigroup.bot_prod_bot /-
@[to_additive]
theorem bot_prod_bot : (⊥ : Subsemigroup M).Prod (⊥ : Subsemigroup N) = ⊥ :=
  SetLike.coe_injective <| by simp [coe_prod, Prod.one_eq_mk]
#align subsemigroup.bot_prod_bot Subsemigroup.bot_prod_bot
#align add_subsemigroup.bot_sum_bot AddSubsemigroup.bot_prod_bot
-/

#print Subsemigroup.prodEquiv /-
/-- The product of subsemigroups is isomorphic to their product as semigroups. -/
@[to_additive prod_equiv
      "The product of additive subsemigroups is isomorphic to their product\nas additive semigroups"]
def prodEquiv (s : Subsemigroup M) (t : Subsemigroup N) : s.Prod t ≃* s × t :=
  { Equiv.Set.prod ↑s ↑t with map_mul' := fun x y => rfl }
#align subsemigroup.prod_equiv Subsemigroup.prodEquiv
#align add_subsemigroup.prod_equiv AddSubsemigroup.prodEquiv
-/

open MulHom

#print Subsemigroup.mem_map_equiv /-
@[to_additive]
theorem mem_map_equiv {f : M ≃* N} {K : Subsemigroup M} {x : N} :
    x ∈ K.map f.toMulHom ↔ f.symm x ∈ K :=
  @Set.mem_image_equiv _ _ (↑K) f.toEquiv x
#align subsemigroup.mem_map_equiv Subsemigroup.mem_map_equiv
#align add_subsemigroup.mem_map_equiv AddSubsemigroup.mem_map_equiv
-/

#print Subsemigroup.map_equiv_eq_comap_symm /-
@[to_additive]
theorem map_equiv_eq_comap_symm (f : M ≃* N) (K : Subsemigroup M) :
    K.map f.toMulHom = K.comap f.symm.toMulHom :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage K)
#align subsemigroup.map_equiv_eq_comap_symm Subsemigroup.map_equiv_eq_comap_symm
#align add_subsemigroup.map_equiv_eq_comap_symm AddSubsemigroup.map_equiv_eq_comap_symm
-/

#print Subsemigroup.comap_equiv_eq_map_symm /-
@[to_additive]
theorem comap_equiv_eq_map_symm (f : N ≃* M) (K : Subsemigroup M) :
    K.comap f.toMulHom = K.map f.symm.toMulHom :=
  (map_equiv_eq_comap_symm f.symm K).symm
#align subsemigroup.comap_equiv_eq_map_symm Subsemigroup.comap_equiv_eq_map_symm
#align add_subsemigroup.comap_equiv_eq_map_symm AddSubsemigroup.comap_equiv_eq_map_symm
-/

#print Subsemigroup.map_equiv_top /-
@[simp, to_additive]
theorem map_equiv_top (f : M ≃* N) : (⊤ : Subsemigroup M).map f.toMulHom = ⊤ :=
  SetLike.coe_injective <| Set.image_univ.trans f.Surjective.range_eq
#align subsemigroup.map_equiv_top Subsemigroup.map_equiv_top
#align add_subsemigroup.map_equiv_top AddSubsemigroup.map_equiv_top
-/

#print Subsemigroup.le_prod_iff /-
@[to_additive le_prod_iff]
theorem le_prod_iff {s : Subsemigroup M} {t : Subsemigroup N} {u : Subsemigroup (M × N)} :
    u ≤ s.Prod t ↔ u.map (fst M N) ≤ s ∧ u.map (snd M N) ≤ t :=
  by
  constructor
  · intro h
    constructor
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩; exact (h hy1).1
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩; exact (h hy1).2
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ h; exact ⟨hH ⟨_, h, rfl⟩, hK ⟨_, h, rfl⟩⟩
#align subsemigroup.le_prod_iff Subsemigroup.le_prod_iff
#align add_subsemigroup.le_prod_iff AddSubsemigroup.le_prod_iff
-/

end Subsemigroup

namespace MulHom

open Subsemigroup

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

#print MulHom.srange /-
/-- The range of a semigroup homomorphism is a subsemigroup. See Note [range copy pattern]. -/
@[to_additive "The range of an `add_hom` is an `add_subsemigroup`."]
def srange (f : M →ₙ* N) : Subsemigroup N :=
  ((⊤ : Subsemigroup M).map f).copy (Set.range f) Set.image_univ.symm
#align mul_hom.srange MulHom.srange
#align add_hom.srange AddHom.srange
-/

#print MulHom.coe_srange /-
@[simp, to_additive]
theorem coe_srange (f : M →ₙ* N) : (f.srange : Set N) = Set.range f :=
  rfl
#align mul_hom.coe_srange MulHom.coe_srange
#align add_hom.coe_srange AddHom.coe_srange
-/

#print MulHom.mem_srange /-
@[simp, to_additive]
theorem mem_srange {f : M →ₙ* N} {y : N} : y ∈ f.srange ↔ ∃ x, f x = y :=
  Iff.rfl
#align mul_hom.mem_srange MulHom.mem_srange
#align add_hom.mem_srange AddHom.mem_srange
-/

#print MulHom.srange_eq_map /-
@[to_additive]
theorem srange_eq_map (f : M →ₙ* N) : f.srange = (⊤ : Subsemigroup M).map f :=
  copy_eq _
#align mul_hom.srange_eq_map MulHom.srange_eq_map
#align add_hom.srange_eq_map AddHom.srange_eq_map
-/

#print MulHom.map_srange /-
@[to_additive]
theorem map_srange (g : N →ₙ* P) (f : M →ₙ* N) : f.srange.map g = (g.comp f).srange := by
  simpa only [srange_eq_map] using (⊤ : Subsemigroup M).map_map g f
#align mul_hom.map_srange MulHom.map_srange
#align add_hom.map_srange AddHom.map_srange
-/

#print MulHom.srange_top_iff_surjective /-
@[to_additive]
theorem srange_top_iff_surjective {N} [Mul N] {f : M →ₙ* N} :
    f.srange = (⊤ : Subsemigroup N) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_srange, coe_top]) Set.range_iff_surjective
#align mul_hom.srange_top_iff_surjective MulHom.srange_top_iff_surjective
#align add_hom.srange_top_iff_surjective AddHom.srange_top_iff_surjective
-/

#print MulHom.srange_top_of_surjective /-
/-- The range of a surjective semigroup hom is the whole of the codomain. -/
@[to_additive "The range of a surjective `add_semigroup` hom is the whole of the codomain."]
theorem srange_top_of_surjective {N} [Mul N] (f : M →ₙ* N) (hf : Function.Surjective f) :
    f.srange = (⊤ : Subsemigroup N) :=
  srange_top_iff_surjective.2 hf
#align mul_hom.srange_top_of_surjective MulHom.srange_top_of_surjective
#align add_hom.srange_top_of_surjective AddHom.srange_top_of_surjective
-/

#print MulHom.mclosure_preimage_le /-
@[to_additive]
theorem mclosure_preimage_le (f : M →ₙ* N) (s : Set N) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun x hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx
#align mul_hom.mclosure_preimage_le MulHom.mclosure_preimage_le
#align add_hom.mclosure_preimage_le AddHom.mclosure_preimage_le
-/

#print MulHom.map_mclosure /-
/-- The image under a semigroup hom of the subsemigroup generated by a set equals the subsemigroup
generated by the image of the set. -/
@[to_additive
      "The image under an `add_semigroup` hom of the `add_subsemigroup` generated by a set\nequals the `add_subsemigroup` generated by the image of the set."]
theorem map_mclosure (f : M →ₙ* N) (s : Set M) : (closure s).map f = closure (f '' s) :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      le_trans (closure_mono <| Set.subset_preimage_image _ _) (mclosure_preimage_le _ _))
    (closure_le.2 <| Set.image_subset _ subset_closure)
#align mul_hom.map_mclosure MulHom.map_mclosure
#align add_hom.map_mclosure AddHom.map_mclosure
-/

#print MulHom.restrict /-
/-- Restriction of a semigroup hom to a subsemigroup of the domain. -/
@[to_additive "Restriction of an add_semigroup hom to an `add_subsemigroup` of the domain."]
def restrict {N : Type _} [Mul N] [SetLike σ M] [MulMemClass σ M] (f : M →ₙ* N) (S : σ) : S →ₙ* N :=
  f.comp (MulMemClass.subtype S)
#align mul_hom.restrict MulHom.restrict
#align add_hom.restrict AddHom.restrict
-/

#print MulHom.restrict_apply /-
@[simp, to_additive]
theorem restrict_apply {N : Type _} [Mul N] [SetLike σ M] [MulMemClass σ M] (f : M →ₙ* N) {S : σ}
    (x : S) : f.restrict S x = f x :=
  rfl
#align mul_hom.restrict_apply MulHom.restrict_apply
#align add_hom.restrict_apply AddHom.restrict_apply
-/

#print MulHom.codRestrict /-
/-- Restriction of a semigroup hom to a subsemigroup of the codomain. -/
@[to_additive "Restriction of an `add_semigroup` hom to an `add_subsemigroup` of the\ncodomain.",
  simps]
def codRestrict [SetLike σ N] [MulMemClass σ N] (f : M →ₙ* N) (S : σ) (h : ∀ x, f x ∈ S) : M →ₙ* S
    where
  toFun n := ⟨f n, h n⟩
  map_mul' x y := Subtype.eq (map_mul f x y)
#align mul_hom.cod_restrict MulHom.codRestrict
#align add_hom.cod_restrict AddHom.codRestrict
-/

#print MulHom.srangeRestrict /-
/-- Restriction of a semigroup hom to its range interpreted as a subsemigroup. -/
@[to_additive "Restriction of an `add_semigroup` hom to its range interpreted as a subsemigroup."]
def srangeRestrict {N} [Mul N] (f : M →ₙ* N) : M →ₙ* f.srange :=
  f.codRestrict f.srange fun x => ⟨x, rfl⟩
#align mul_hom.srange_restrict MulHom.srangeRestrict
#align add_hom.srange_restrict AddHom.srangeRestrict
-/

#print MulHom.coe_srangeRestrict /-
@[simp, to_additive]
theorem coe_srangeRestrict {N} [Mul N] (f : M →ₙ* N) (x : M) : (f.srangeRestrict x : N) = f x :=
  rfl
#align mul_hom.coe_srange_restrict MulHom.coe_srangeRestrict
#align add_hom.coe_srange_restrict AddHom.coe_srangeRestrict
-/

#print MulHom.srangeRestrict_surjective /-
@[to_additive]
theorem srangeRestrict_surjective (f : M →ₙ* N) : Function.Surjective f.srangeRestrict :=
  fun ⟨_, ⟨x, rfl⟩⟩ => ⟨x, rfl⟩
#align mul_hom.srange_restrict_surjective MulHom.srangeRestrict_surjective
#align add_hom.srange_restrict_surjective AddHom.srangeRestrict_surjective
-/

#print MulHom.prod_map_comap_prod' /-
@[to_additive]
theorem prod_map_comap_prod' {M' : Type _} {N' : Type _} [Mul M'] [Mul N'] (f : M →ₙ* N)
    (g : M' →ₙ* N') (S : Subsemigroup N) (S' : Subsemigroup N') :
    (S.Prod S').comap (prodMap f g) = (S.comap f).Prod (S'.comap g) :=
  SetLike.coe_injective <| Set.preimage_prod_map_prod f g _ _
#align mul_hom.prod_map_comap_prod' MulHom.prod_map_comap_prod'
#align add_hom.sum_map_comap_sum' AddHom.prod_map_comap_prod'
-/

#print MulHom.subsemigroupComap /-
/-- The `mul_hom` from the preimage of a subsemigroup to itself. -/
@[to_additive "the `add_hom` from the preimage of an additive subsemigroup to itself.", simps]
def subsemigroupComap (f : M →ₙ* N) (N' : Subsemigroup N) : N'.comap f →ₙ* N'
    where
  toFun x := ⟨f x, x.Prop⟩
  map_mul' x y := Subtype.eq (@map_mul M N _ _ _ _ f x y)
#align mul_hom.subsemigroup_comap MulHom.subsemigroupComap
#align add_hom.subsemigroup_comap AddHom.subsemigroupComap
-/

#print MulHom.subsemigroupMap /-
/-- The `mul_hom` from a subsemigroup to its image.
See `mul_equiv.subsemigroup_map` for a variant for `mul_equiv`s. -/
@[to_additive
      "the `add_hom` from an additive subsemigroup to its image. See\n`add_equiv.add_subsemigroup_map` for a variant for `add_equiv`s.",
  simps]
def subsemigroupMap (f : M →ₙ* N) (M' : Subsemigroup M) : M' →ₙ* M'.map f
    where
  toFun x := ⟨f x, ⟨x, x.Prop, rfl⟩⟩
  map_mul' x y := Subtype.eq <| @map_mul M N _ _ _ _ f x y
#align mul_hom.subsemigroup_map MulHom.subsemigroupMap
#align add_hom.subsemigroup_map AddHom.subsemigroupMap
-/

#print MulHom.subsemigroupMap_surjective /-
@[to_additive]
theorem subsemigroupMap_surjective (f : M →ₙ* N) (M' : Subsemigroup M) :
    Function.Surjective (f.subsemigroupMap M') := by rintro ⟨_, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
#align mul_hom.subsemigroup_map_surjective MulHom.subsemigroupMap_surjective
#align add_hom.subsemigroup_map_surjective AddHom.subsemigroupMap_surjective
-/

end MulHom

namespace Subsemigroup

open MulHom

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

#print Subsemigroup.srange_fst /-
@[simp, to_additive]
theorem srange_fst [Nonempty N] : (fst M N).srange = ⊤ :=
  (fst M N).srange_top_of_surjective <| Prod.fst_surjective
#align subsemigroup.srange_fst Subsemigroup.srange_fst
#align add_subsemigroup.srange_fst AddSubsemigroup.srange_fst
-/

#print Subsemigroup.srange_snd /-
@[simp, to_additive]
theorem srange_snd [Nonempty M] : (snd M N).srange = ⊤ :=
  (snd M N).srange_top_of_surjective <| Prod.snd_surjective
#align subsemigroup.srange_snd Subsemigroup.srange_snd
#align add_subsemigroup.srange_snd AddSubsemigroup.srange_snd
-/

#print Subsemigroup.prod_eq_top_iff /-
@[to_additive]
theorem prod_eq_top_iff [Nonempty M] [Nonempty N] {s : Subsemigroup M} {t : Subsemigroup N} :
    s.Prod t = ⊤ ↔ s = ⊤ ∧ t = ⊤ := by
  simp only [eq_top_iff, le_prod_iff, ← (gc_map_comap _).le_iff_le, ← srange_eq_map, srange_fst,
    srange_snd]
#align subsemigroup.prod_eq_top_iff Subsemigroup.prod_eq_top_iff
#align add_subsemigroup.sum_eq_top_iff AddSubsemigroup.prod_eq_top_iff
-/

#print Subsemigroup.inclusion /-
/-- The semigroup hom associated to an inclusion of subsemigroups. -/
@[to_additive "The `add_semigroup` hom associated to an inclusion of subsemigroups."]
def inclusion {S T : Subsemigroup M} (h : S ≤ T) : S →ₙ* T :=
  (MulMemClass.subtype S).codRestrict _ fun x => h x.2
#align subsemigroup.inclusion Subsemigroup.inclusion
#align add_subsemigroup.inclusion AddSubsemigroup.inclusion
-/

#print Subsemigroup.range_subtype /-
@[simp, to_additive]
theorem range_subtype (s : Subsemigroup M) : (MulMemClass.subtype s).srange = s :=
  SetLike.coe_injective <| (coe_srange _).trans <| Subtype.range_coe
#align subsemigroup.range_subtype Subsemigroup.range_subtype
#align add_subsemigroup.range_subtype AddSubsemigroup.range_subtype
-/

#print Subsemigroup.eq_top_iff' /-
@[to_additive]
theorem eq_top_iff' : S = ⊤ ↔ ∀ x : M, x ∈ S :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩
#align subsemigroup.eq_top_iff' Subsemigroup.eq_top_iff'
#align add_subsemigroup.eq_top_iff' AddSubsemigroup.eq_top_iff'
-/

end Subsemigroup

namespace MulEquiv

variable [Mul M] [Mul N] {S T : Subsemigroup M}

#print MulEquiv.subsemigroupCongr /-
/-- Makes the identity isomorphism from a proof that two subsemigroups of a multiplicative
    semigroup are equal. -/
@[to_additive
      "Makes the identity additive isomorphism from a proof two\nsubsemigroups of an additive semigroup are equal."]
def subsemigroupCongr (h : S = T) : S ≃* T :=
  { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }
#align mul_equiv.subsemigroup_congr MulEquiv.subsemigroupCongr
#align add_equiv.subsemigroup_congr AddEquiv.subsemigroupCongr
-/

#print MulEquiv.ofLeftInverse /-
-- this name is primed so that the version to `f.range` instead of `f.srange` can be unprimed.
/-- A semigroup homomorphism `f : M →ₙ* N` with a left-inverse `g : N → M` defines a multiplicative
equivalence between `M` and `f.srange`.

This is a bidirectional version of `mul_hom.srange_restrict`. -/
@[to_additive
      "\nAn additive semigroup homomorphism `f : M →+ N` with a left-inverse `g : N → M` defines an additive\nequivalence between `M` and `f.srange`.\n\nThis is a bidirectional version of `add_hom.srange_restrict`. ",
  simps (config := { simpRhs := true })]
def ofLeftInverse (f : M →ₙ* N) {g : N → M} (h : Function.LeftInverse g f) : M ≃* f.srange :=
  { f.srangeRestrict with
    toFun := f.srangeRestrict
    invFun := g ∘ MulMemClass.subtype f.srange
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := MulHom.mem_srange.mp x.Prop
        show f (g x) = x by rw [← hx', h x'] }
#align mul_equiv.of_left_inverse MulEquiv.ofLeftInverse
#align add_equiv.of_left_inverse AddEquiv.ofLeftInverse
-/

#print MulEquiv.subsemigroupMap /-
/-- A `mul_equiv` `φ` between two semigroups `M` and `N` induces a `mul_equiv` between
a subsemigroup `S ≤ M` and the subsemigroup `φ(S) ≤ N`.
See `mul_hom.subsemigroup_map` for a variant for `mul_hom`s. -/
@[to_additive
      "An `add_equiv` `φ` between two additive semigroups `M` and `N` induces an `add_equiv`\nbetween a subsemigroup `S ≤ M` and the subsemigroup `φ(S) ≤ N`. See `add_hom.add_subsemigroup_map`\nfor a variant for `add_hom`s.",
  simps]
def subsemigroupMap (e : M ≃* N) (S : Subsemigroup M) : S ≃* S.map e.toMulHom :=
  {-- we restate this for `simps` to avoid `⇑e.symm.to_equiv x`
          e.toMulHom.subsemigroupMap
      S,
    e.toEquiv.image S with
    toFun := fun x => ⟨e x, _⟩
    invFun := fun x => ⟨e.symm x, _⟩ }
#align mul_equiv.subsemigroup_map MulEquiv.subsemigroupMap
#align add_equiv.subsemigroup_map AddEquiv.subsemigroupMap
-/

end MulEquiv

