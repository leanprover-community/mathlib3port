/-
Copyright (c) 2019 Johan Commelin All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module topology.algebra.open_subgroup
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Ring
import Mathbin.Topology.Sets.Opens

/-!
# Open subgroups of a topological groups

This files builds the lattice `open_subgroup G` of open subgroups in a topological group `G`,
and its additive version `open_add_subgroup`.  This lattice has a top element, the subgroup of all
elements, but no bottom element in general. The trivial subgroup which is the natural candidate
bottom has no reason to be open (this happens only in discrete groups).

Note that this notion is especially relevant in a non-archimedean context, for instance for
`p`-adic groups.

## Main declarations

* `open_subgroup.is_closed`: An open subgroup is automatically closed.
* `subgroup.is_open_mono`: A subgroup containing an open subgroup is open.
                           There are also versions for additive groups, submodules and ideals.
* `open_subgroup.comap`: Open subgroups can be pulled back by a continuous group morphism.

## TODO
* Prove that the identity component of a locally path connected group is an open subgroup.
  Up to now this file is really geared towards non-archimedean algebra, not Lie groups.
-/


open TopologicalSpace

open Topology

/-- The type of open subgroups of a topological additive group. -/
structure OpenAddSubgroup (G : Type _) [AddGroup G] [TopologicalSpace G] extends AddSubgroup G where
  is_open' : IsOpen carrier
#align open_add_subgroup OpenAddSubgroup

/-- The type of open subgroups of a topological group. -/
@[to_additive]
structure OpenSubgroup (G : Type _) [Group G] [TopologicalSpace G] extends Subgroup G where
  is_open' : IsOpen carrier
#align open_subgroup OpenSubgroup
#align open_add_subgroup OpenAddSubgroup

/-- Reinterpret an `open_subgroup` as a `subgroup`. -/
add_decl_doc OpenSubgroup.toSubgroup

/-- Reinterpret an `open_add_subgroup` as an `add_subgroup`. -/
add_decl_doc OpenAddSubgroup.toAddSubgroup

namespace OpenSubgroup

open Function TopologicalSpace

variable {G : Type _} [Group G] [TopologicalSpace G]

variable {U V : OpenSubgroup G} {g : G}

@[to_additive]
instance hasCoeSet : CoeTC (OpenSubgroup G) (Set G) :=
  ⟨fun U => U.1⟩
#align open_subgroup.has_coe_set OpenSubgroup.hasCoeSet
#align open_add_subgroup.has_coe_set OpenAddSubgroup.hasCoeSet

@[to_additive]
instance : Membership G (OpenSubgroup G) :=
  ⟨fun g U => g ∈ (U : Set G)⟩

@[to_additive]
instance hasCoeSubgroup : CoeTC (OpenSubgroup G) (Subgroup G) :=
  ⟨toSubgroup⟩
#align open_subgroup.has_coe_subgroup OpenSubgroup.hasCoeSubgroup
#align open_add_subgroup.has_coe_add_subgroup OpenAddSubgroup.hasCoeAddSubgroup

@[to_additive]
instance hasCoeOpens : CoeTC (OpenSubgroup G) (Opens G) :=
  ⟨fun U => ⟨U, U.is_open'⟩⟩
#align open_subgroup.has_coe_opens OpenSubgroup.hasCoeOpens
#align open_add_subgroup.has_coe_opens OpenAddSubgroup.hasCoeOpens

@[simp, norm_cast, to_additive]
theorem mem_coe : g ∈ (U : Set G) ↔ g ∈ U :=
  Iff.rfl
#align open_subgroup.mem_coe OpenSubgroup.mem_coe
#align open_add_subgroup.mem_coe OpenAddSubgroup.mem_coe

@[simp, norm_cast, to_additive]
theorem mem_coe_opens : g ∈ (U : Opens G) ↔ g ∈ U :=
  Iff.rfl
#align open_subgroup.mem_coe_opens OpenSubgroup.mem_coe_opens
#align open_add_subgroup.mem_coe_opens OpenAddSubgroup.mem_coe_opens

@[simp, norm_cast, to_additive]
theorem mem_coe_subgroup : g ∈ (U : Subgroup G) ↔ g ∈ U :=
  Iff.rfl
#align open_subgroup.mem_coe_subgroup OpenSubgroup.mem_coe_subgroup
#align open_add_subgroup.mem_coe_add_subgroup OpenAddSubgroup.mem_coe_add_subgroup

@[to_additive]
theorem coe_injective : Injective (coe : OpenSubgroup G → Set G) :=
  by
  rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨h⟩
  congr
#align open_subgroup.coe_injective OpenSubgroup.coe_injective
#align open_add_subgroup.coe_injective OpenAddSubgroup.coe_injective

@[ext, to_additive]
theorem ext (h : ∀ x, x ∈ U ↔ x ∈ V) : U = V :=
  coe_injective <| Set.ext h
#align open_subgroup.ext OpenSubgroup.ext
#align open_add_subgroup.ext OpenAddSubgroup.ext

@[to_additive]
theorem ext_iff : U = V ↔ ∀ x, x ∈ U ↔ x ∈ V :=
  ⟨fun h x => h ▸ Iff.rfl, ext⟩
#align open_subgroup.ext_iff OpenSubgroup.ext_iff
#align open_add_subgroup.ext_iff OpenAddSubgroup.ext_iff

variable (U)

@[to_additive]
protected theorem isOpen : IsOpen (U : Set G) :=
  U.is_open'
#align open_subgroup.is_open OpenSubgroup.isOpen
#align open_add_subgroup.is_open OpenAddSubgroup.isOpen

@[to_additive]
protected theorem one_mem : (1 : G) ∈ U :=
  U.one_mem'
#align open_subgroup.one_mem OpenSubgroup.one_mem
#align open_add_subgroup.zero_mem OpenAddSubgroup.zero_mem

@[to_additive]
protected theorem inv_mem {g : G} (h : g ∈ U) : g⁻¹ ∈ U :=
  U.inv_mem' h
#align open_subgroup.inv_mem OpenSubgroup.inv_mem
#align open_add_subgroup.neg_mem OpenAddSubgroup.neg_mem

@[to_additive]
protected theorem mul_mem {g₁ g₂ : G} (h₁ : g₁ ∈ U) (h₂ : g₂ ∈ U) : g₁ * g₂ ∈ U :=
  U.mul_mem' h₁ h₂
#align open_subgroup.mul_mem OpenSubgroup.mul_mem
#align open_add_subgroup.add_mem OpenAddSubgroup.add_mem

@[to_additive]
theorem mem_nhds_one : (U : Set G) ∈ 𝓝 (1 : G) :=
  IsOpen.mem_nhds U.IsOpen U.one_mem
#align open_subgroup.mem_nhds_one OpenSubgroup.mem_nhds_one
#align open_add_subgroup.mem_nhds_zero OpenAddSubgroup.mem_nhds_zero

variable {U}

@[to_additive]
instance : Top (OpenSubgroup G) :=
  ⟨{ (⊤ : Subgroup G) with is_open' := isOpen_univ }⟩

@[to_additive]
instance : Inhabited (OpenSubgroup G) :=
  ⟨⊤⟩

@[to_additive]
theorem isClosed [HasContinuousMul G] (U : OpenSubgroup G) : IsClosed (U : Set G) :=
  by
  apply isOpen_compl_iff.1
  refine' isOpen_iff_forall_mem_open.2 fun x hx => ⟨(fun y => y * x⁻¹) ⁻¹' U, _, _, _⟩
  · intro u hux
    simp only [Set.mem_preimage, Set.mem_compl_iff, mem_coe] at hux hx⊢
    refine' mt (fun hu => _) hx
    convert U.mul_mem (U.inv_mem hux) hu
    simp
  · exact U.is_open.preimage (continuous_mul_right _)
  · simp [U.one_mem]
#align open_subgroup.is_closed OpenSubgroup.isClosed
#align open_add_subgroup.is_closed OpenAddSubgroup.isClosed

section

variable {H : Type _} [Group H] [TopologicalSpace H]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The product of two open subgroups as an open subgroup of the product group. -/
@[to_additive "The product of two open subgroups as an open subgroup of the product group."]
def prod (U : OpenSubgroup G) (V : OpenSubgroup H) : OpenSubgroup (G × H) :=
  {
    (U : Subgroup G).Prod (V : Subgroup
          H) with
    carrier := U ×ˢ V
    is_open' := U.IsOpen.Prod V.IsOpen }
#align open_subgroup.prod OpenSubgroup.prod
#align open_add_subgroup.sum OpenAddSubgroup.sum

end

@[to_additive]
instance : PartialOrder (OpenSubgroup G) :=
  { PartialOrder.lift (coe : OpenSubgroup G → Set G) coe_injective with
    le := fun U V => ∀ ⦃x⦄, x ∈ U → x ∈ V }

@[to_additive]
instance : SemilatticeInf (OpenSubgroup G) :=
  {
    OpenSubgroup.partialOrder with
    inf := fun U V => { (U : Subgroup G) ⊓ V with is_open' := IsOpen.inter U.IsOpen V.IsOpen }
    inf_le_left := fun U V => Set.inter_subset_left _ _
    inf_le_right := fun U V => Set.inter_subset_right _ _
    le_inf := fun U V W hV hW => Set.subset_inter hV hW }

@[to_additive]
instance : OrderTop (OpenSubgroup G) where
  top := ⊤
  le_top U := Set.subset_univ _

@[simp, norm_cast, to_additive]
theorem coe_inf : (↑(U ⊓ V) : Set G) = (U : Set G) ∩ V :=
  rfl
#align open_subgroup.coe_inf OpenSubgroup.coe_inf
#align open_add_subgroup.coe_inf OpenAddSubgroup.coe_inf

@[simp, norm_cast, to_additive]
theorem coe_subset : (U : Set G) ⊆ V ↔ U ≤ V :=
  Iff.rfl
#align open_subgroup.coe_subset OpenSubgroup.coe_subset
#align open_add_subgroup.coe_subset OpenAddSubgroup.coe_subset

@[simp, norm_cast, to_additive]
theorem coe_subgroup_le : (U : Subgroup G) ≤ (V : Subgroup G) ↔ U ≤ V :=
  Iff.rfl
#align open_subgroup.coe_subgroup_le OpenSubgroup.coe_subgroup_le
#align open_add_subgroup.coe_add_subgroup_le OpenAddSubgroup.coe_add_subgroup_le

variable {N : Type _} [Group N] [TopologicalSpace N]

/-- The preimage of an `open_subgroup` along a continuous `monoid` homomorphism
  is an `open_subgroup`. -/
@[to_additive
      "The preimage of an `open_add_subgroup` along a continuous `add_monoid` homomorphism\nis an `open_add_subgroup`."]
def comap (f : G →* N) (hf : Continuous f) (H : OpenSubgroup N) : OpenSubgroup G :=
  { (H : Subgroup N).comap f with is_open' := H.IsOpen.Preimage hf }
#align open_subgroup.comap OpenSubgroup.comap
#align open_add_subgroup.comap OpenAddSubgroup.comap

@[simp, to_additive]
theorem coe_comap (H : OpenSubgroup N) (f : G →* N) (hf : Continuous f) :
    (H.comap f hf : Set G) = f ⁻¹' H :=
  rfl
#align open_subgroup.coe_comap OpenSubgroup.coe_comap
#align open_add_subgroup.coe_comap OpenAddSubgroup.coe_comap

@[simp, to_additive]
theorem mem_comap {H : OpenSubgroup N} {f : G →* N} {hf : Continuous f} {x : G} :
    x ∈ H.comap f hf ↔ f x ∈ H :=
  Iff.rfl
#align open_subgroup.mem_comap OpenSubgroup.mem_comap
#align open_add_subgroup.mem_comap OpenAddSubgroup.mem_comap

@[to_additive]
theorem comap_comap {P : Type _} [Group P] [TopologicalSpace P] (K : OpenSubgroup P) (f₂ : N →* P)
    (hf₂ : Continuous f₂) (f₁ : G →* N) (hf₁ : Continuous f₁) :
    (K.comap f₂ hf₂).comap f₁ hf₁ = K.comap (f₂.comp f₁) (hf₂.comp hf₁) :=
  rfl
#align open_subgroup.comap_comap OpenSubgroup.comap_comap
#align open_add_subgroup.comap_comap OpenAddSubgroup.comap_comap

end OpenSubgroup

namespace Subgroup

variable {G : Type _} [Group G] [TopologicalSpace G] [HasContinuousMul G] (H : Subgroup G)

@[to_additive]
theorem isOpen_of_mem_nhds {g : G} (hg : (H : Set G) ∈ 𝓝 g) : IsOpen (H : Set G) :=
  by
  simp only [isOpen_iff_mem_nhds, SetLike.mem_coe] at hg⊢
  intro x hx
  have : Filter.Tendsto (fun y => y * (x⁻¹ * g)) (𝓝 x) (𝓝 <| x * (x⁻¹ * g)) :=
    (continuous_id.mul continuous_const).Tendsto _
  rw [mul_inv_cancel_left] at this
  have := Filter.mem_map'.1 (this hg)
  replace hg : g ∈ H := SetLike.mem_coe.1 (mem_of_mem_nhds hg)
  simp only [SetLike.mem_coe, H.mul_mem_cancel_right (H.mul_mem (H.inv_mem hx) hg)] at this
  exact this
#align subgroup.is_open_of_mem_nhds Subgroup.isOpen_of_mem_nhds
#align add_subgroup.is_open_of_mem_nhds AddSubgroup.isOpen_of_mem_nhds

@[to_additive]
theorem isOpen_of_openSubgroup {U : OpenSubgroup G} (h : U.1 ≤ H) : IsOpen (H : Set G) :=
  H.isOpen_of_mem_nhds (Filter.mem_of_superset U.mem_nhds_one h)
#align subgroup.is_open_of_open_subgroup Subgroup.isOpen_of_openSubgroup
#align add_subgroup.is_open_of_open_add_subgroup AddSubgroup.isOpen_of_open_add_subgroup

/-- If a subgroup of a topological group has `1` in its interior, then it is open. -/
@[to_additive
      "If a subgroup of an additive topological group has `0` in its interior, then it is\nopen."]
theorem isOpen_of_one_mem_interior {G : Type _} [Group G] [TopologicalSpace G] [TopologicalGroup G]
    {H : Subgroup G} (h_1_int : (1 : G) ∈ interior (H : Set G)) : IsOpen (H : Set G) :=
  by
  have h : 𝓝 1 ≤ Filter.principal (H : Set G) :=
    nhds_le_of_le h_1_int isOpen_interior (Filter.principal_mono.2 interior_subset)
  rw [isOpen_iff_nhds]
  intro g hg
  rw [show 𝓝 g = Filter.map (⇑(Homeomorph.mulLeft g)) (𝓝 1) by simp]
  convert Filter.map_mono h
  simp only [Homeomorph.coe_mulLeft, Filter.map_principal, Set.image_mul_left,
    Filter.principal_eq_iff_eq]
  ext
  simp [H.mul_mem_cancel_left (H.inv_mem hg)]
#align subgroup.is_open_of_one_mem_interior Subgroup.isOpen_of_one_mem_interior
#align add_subgroup.is_open_of_zero_mem_interior AddSubgroup.isOpen_of_zero_mem_interior

@[to_additive]
theorem isOpen_mono {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) (h₁ : IsOpen (H₁ : Set G)) :
    IsOpen (H₂ : Set G) :=
  @isOpen_of_openSubgroup _ _ _ _ H₂ { H₁ with is_open' := h₁ } h
#align subgroup.is_open_mono Subgroup.isOpen_mono
#align add_subgroup.is_open_mono AddSubgroup.isOpen_mono

end Subgroup

namespace OpenSubgroup

variable {G : Type _} [Group G] [TopologicalSpace G] [HasContinuousMul G]

@[to_additive]
instance : SemilatticeSup (OpenSubgroup G) :=
  {
    OpenSubgroup.semilatticeInf with
    sup := fun U V =>
      { (U : Subgroup G) ⊔ V with
        is_open' :=
          show IsOpen (((U : Subgroup G) ⊔ V : Subgroup G) : Set G) from
            Subgroup.isOpen_mono le_sup_left U.IsOpen }
    le_sup_left := fun U V => coe_subgroup_le.1 le_sup_left
    le_sup_right := fun U V => coe_subgroup_le.1 le_sup_right
    sup_le := fun U V W hU hV => coe_subgroup_le.1 (sup_le hU hV) }

@[to_additive]
instance : Lattice (OpenSubgroup G) :=
  { OpenSubgroup.semilatticeSup, OpenSubgroup.semilatticeInf with }

end OpenSubgroup

namespace Submodule

open OpenAddSubgroup

variable {R : Type _} {M : Type _} [CommRing R]

variable [AddCommGroup M] [TopologicalSpace M] [TopologicalAddGroup M] [Module R M]

theorem isOpen_mono {U P : Submodule R M} (h : U ≤ P) (hU : IsOpen (U : Set M)) :
    IsOpen (P : Set M) :=
  @AddSubgroup.isOpen_mono M _ _ _ U.toAddSubgroup P.toAddSubgroup h hU
#align submodule.is_open_mono Submodule.isOpen_mono

end Submodule

namespace Ideal

variable {R : Type _} [CommRing R]

variable [TopologicalSpace R] [TopologicalRing R]

theorem isOpen_of_open_subideal {U I : Ideal R} (h : U ≤ I) (hU : IsOpen (U : Set R)) :
    IsOpen (I : Set R) :=
  Submodule.isOpen_mono h hU
#align ideal.is_open_of_open_subideal Ideal.isOpen_of_open_subideal

end Ideal

