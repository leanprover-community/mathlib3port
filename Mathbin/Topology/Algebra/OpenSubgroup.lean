/-
Copyright (c) 2019 Johan Commelin All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import RingTheory.Ideal.Basic
import Topology.Algebra.Ring.Basic
import Topology.Sets.Opens

#align_import topology.algebra.open_subgroup from "leanprover-community/mathlib"@"932872382355f00112641d305ba0619305dc8642"

/-!
# Open subgroups of a topological groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

open scoped Topology

#print OpenAddSubgroup /-
/-- The type of open subgroups of a topological additive group. -/
structure OpenAddSubgroup (G : Type _) [AddGroup G] [TopologicalSpace G] extends AddSubgroup G where
  is_open' : IsOpen carrier
#align open_add_subgroup OpenAddSubgroup
-/

#print OpenSubgroup /-
/-- The type of open subgroups of a topological group. -/
@[to_additive]
structure OpenSubgroup (G : Type _) [Group G] [TopologicalSpace G] extends Subgroup G where
  is_open' : IsOpen carrier
#align open_subgroup OpenSubgroup
#align open_add_subgroup OpenAddSubgroup
-/

/-- Reinterpret an `open_subgroup` as a `subgroup`. -/
add_decl_doc OpenSubgroup.toSubgroup

/-- Reinterpret an `open_add_subgroup` as an `add_subgroup`. -/
add_decl_doc OpenAddSubgroup.toAddSubgroup

namespace OpenSubgroup

open Function TopologicalSpace

variable {G : Type _} [Group G] [TopologicalSpace G]

variable {U V : OpenSubgroup G} {g : G}

#print OpenSubgroup.hasCoeSubgroup /-
@[to_additive]
instance hasCoeSubgroup : CoeTC (OpenSubgroup G) (Subgroup G) :=
  ⟨toSubgroup⟩
#align open_subgroup.has_coe_subgroup OpenSubgroup.hasCoeSubgroup
#align open_add_subgroup.has_coe_add_subgroup OpenAddSubgroup.hasCoeAddSubgroup
-/

#print OpenSubgroup.toSubgroup_injective /-
@[to_additive]
theorem toSubgroup_injective : Injective (coe : OpenSubgroup G → Subgroup G)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
#align open_subgroup.coe_subgroup_injective OpenSubgroup.toSubgroup_injective
#align open_add_subgroup.coe_add_subgroup_injective OpenAddSubgroup.toAddSubgroup_injective
-/

@[to_additive]
instance : SetLike (OpenSubgroup G) G where
  coe U := U.1
  coe_injective' _ _ h := toSubgroup_injective <| SetLike.ext' h

@[to_additive]
instance : SubgroupClass (OpenSubgroup G) G
    where
  hMul_mem U _ _ := U.hMul_mem'
  one_mem U := U.one_mem'
  inv_mem U _ := U.inv_mem'

#print OpenSubgroup.hasCoeOpens /-
@[to_additive]
instance hasCoeOpens : CoeTC (OpenSubgroup G) (Opens G) :=
  ⟨fun U => ⟨U, U.is_open'⟩⟩
#align open_subgroup.has_coe_opens OpenSubgroup.hasCoeOpens
#align open_add_subgroup.has_coe_opens OpenAddSubgroup.hasCoeOpens
-/

#print OpenSubgroup.coe_toOpens /-
@[simp, norm_cast, to_additive]
theorem coe_toOpens : ((U : Opens G) : Set G) = U :=
  rfl
#align open_subgroup.coe_coe_opens OpenSubgroup.coe_toOpens
#align open_add_subgroup.coe_coe_opens OpenAddSubgroup.coe_toOpens
-/

#print OpenSubgroup.coe_toSubgroup /-
@[simp, norm_cast, to_additive]
theorem coe_toSubgroup : ((U : Subgroup G) : Set G) = U :=
  rfl
#align open_subgroup.coe_coe_subgroup OpenSubgroup.coe_toSubgroup
#align open_add_subgroup.coe_coe_add_subgroup OpenAddSubgroup.coe_toAddSubgroup
-/

#print OpenSubgroup.mem_toOpens /-
@[simp, norm_cast, to_additive]
theorem mem_toOpens : g ∈ (U : Opens G) ↔ g ∈ U :=
  Iff.rfl
#align open_subgroup.mem_coe_opens OpenSubgroup.mem_toOpens
#align open_add_subgroup.mem_coe_opens OpenAddSubgroup.mem_toOpens
-/

#print OpenSubgroup.mem_toSubgroup /-
@[simp, norm_cast, to_additive]
theorem mem_toSubgroup : g ∈ (U : Subgroup G) ↔ g ∈ U :=
  Iff.rfl
#align open_subgroup.mem_coe_subgroup OpenSubgroup.mem_toSubgroup
#align open_add_subgroup.mem_coe_add_subgroup OpenAddSubgroup.mem_toAddSubgroup
-/

#print OpenSubgroup.ext /-
@[ext, to_additive]
theorem ext (h : ∀ x, x ∈ U ↔ x ∈ V) : U = V :=
  SetLike.ext h
#align open_subgroup.ext OpenSubgroup.ext
#align open_add_subgroup.ext OpenAddSubgroup.ext
-/

variable (U)

#print OpenSubgroup.isOpen /-
@[to_additive]
protected theorem isOpen : IsOpen (U : Set G) :=
  U.is_open'
#align open_subgroup.is_open OpenSubgroup.isOpen
#align open_add_subgroup.is_open OpenAddSubgroup.isOpen
-/

#print OpenSubgroup.mem_nhds_one /-
@[to_additive]
theorem mem_nhds_one : (U : Set G) ∈ 𝓝 (1 : G) :=
  IsOpen.mem_nhds U.IsOpen U.one_mem
#align open_subgroup.mem_nhds_one OpenSubgroup.mem_nhds_one
#align open_add_subgroup.mem_nhds_zero OpenAddSubgroup.mem_nhds_zero
-/

variable {U}

@[to_additive]
instance : Top (OpenSubgroup G) :=
  ⟨{ (⊤ : Subgroup G) with is_open' := isOpen_univ }⟩

#print OpenSubgroup.mem_top /-
@[simp, to_additive]
theorem mem_top (x : G) : x ∈ (⊤ : OpenSubgroup G) :=
  trivial
#align open_subgroup.mem_top OpenSubgroup.mem_top
#align open_add_subgroup.mem_top OpenAddSubgroup.mem_top
-/

#print OpenSubgroup.coe_top /-
@[simp, norm_cast, to_additive]
theorem coe_top : ((⊤ : OpenSubgroup G) : Set G) = Set.univ :=
  rfl
#align open_subgroup.coe_top OpenSubgroup.coe_top
#align open_add_subgroup.coe_top OpenAddSubgroup.coe_top
-/

#print OpenSubgroup.toSubgroup_top /-
@[simp, norm_cast, to_additive]
theorem toSubgroup_top : ((⊤ : OpenSubgroup G) : Subgroup G) = ⊤ :=
  rfl
#align open_subgroup.coe_subgroup_top OpenSubgroup.toSubgroup_top
#align open_add_subgroup.coe_add_subgroup_top OpenAddSubgroup.toAddSubgroup_top
-/

#print OpenSubgroup.toOpens_top /-
@[simp, norm_cast, to_additive]
theorem toOpens_top : ((⊤ : OpenSubgroup G) : Opens G) = ⊤ :=
  rfl
#align open_subgroup.coe_opens_top OpenSubgroup.toOpens_top
#align open_add_subgroup.coe_opens_top OpenAddSubgroup.toOpens_top
-/

@[to_additive]
instance : Inhabited (OpenSubgroup G) :=
  ⟨⊤⟩

#print OpenSubgroup.isClosed /-
@[to_additive]
theorem isClosed [ContinuousMul G] (U : OpenSubgroup G) : IsClosed (U : Set G) :=
  by
  apply isOpen_compl_iff.1
  refine' isOpen_iff_forall_mem_open.2 fun x hx => ⟨(fun y => y * x⁻¹) ⁻¹' U, _, _, _⟩
  · refine' fun u hux hu => hx _
    simp only [Set.mem_preimage, SetLike.mem_coe] at hux hu ⊢
    convert U.mul_mem (U.inv_mem hux) hu
    simp
  · exact U.is_open.preimage (continuous_mul_right _)
  · simp [one_mem]
#align open_subgroup.is_closed OpenSubgroup.isClosed
#align open_add_subgroup.is_closed OpenAddSubgroup.isClosed
-/

#print OpenSubgroup.isClopen /-
@[to_additive]
theorem isClopen [ContinuousMul G] (U : OpenSubgroup G) : IsClopen (U : Set G) :=
  ⟨U.IsOpen, U.IsClosed⟩
#align open_subgroup.is_clopen OpenSubgroup.isClopen
#align open_add_subgroup.is_clopen OpenAddSubgroup.isClopen
-/

section

variable {H : Type _} [Group H] [TopologicalSpace H]

#print OpenSubgroup.prod /-
/-- The product of two open subgroups as an open subgroup of the product group. -/
@[to_additive "The product of two open subgroups as an open subgroup of the product group."]
def prod (U : OpenSubgroup G) (V : OpenSubgroup H) : OpenSubgroup (G × H) :=
  { (U : Subgroup G).Prod (V : Subgroup H) with is_open' := U.IsOpen.Prod V.IsOpen }
#align open_subgroup.prod OpenSubgroup.prod
#align open_add_subgroup.sum OpenAddSubgroup.sum
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print OpenSubgroup.coe_prod /-
@[simp, norm_cast, to_additive]
theorem coe_prod (U : OpenSubgroup G) (V : OpenSubgroup H) : (U.Prod V : Set (G × H)) = U ×ˢ V :=
  rfl
#align open_subgroup.coe_prod OpenSubgroup.coe_prod
#align open_add_subgroup.coe_sum OpenAddSubgroup.coe_sum
-/

#print OpenSubgroup.toSubgroup_prod /-
@[simp, norm_cast, to_additive]
theorem toSubgroup_prod (U : OpenSubgroup G) (V : OpenSubgroup H) :
    (U.Prod V : Subgroup (G × H)) = (U : Subgroup G).Prod V :=
  rfl
#align open_subgroup.coe_subgroup_prod OpenSubgroup.toSubgroup_prod
#align open_add_subgroup.coe_add_subgroup_sum OpenAddSubgroup.toAddSubgroup_sum
-/

end

@[to_additive]
instance : Inf (OpenSubgroup G) :=
  ⟨fun U V => ⟨U ⊓ V, U.IsOpen.inter V.IsOpen⟩⟩

#print OpenSubgroup.coe_inf /-
@[simp, norm_cast, to_additive]
theorem coe_inf : (↑(U ⊓ V) : Set G) = (U : Set G) ∩ V :=
  rfl
#align open_subgroup.coe_inf OpenSubgroup.coe_inf
#align open_add_subgroup.coe_inf OpenAddSubgroup.coe_inf
-/

#print OpenSubgroup.toSubgroup_inf /-
@[simp, norm_cast, to_additive]
theorem toSubgroup_inf : (↑(U ⊓ V) : Subgroup G) = ↑U ⊓ ↑V :=
  rfl
#align open_subgroup.coe_subgroup_inf OpenSubgroup.toSubgroup_inf
#align open_add_subgroup.coe_add_subgroup_inf OpenAddSubgroup.toAddSubgroup_inf
-/

#print OpenSubgroup.toOpens_inf /-
@[simp, norm_cast, to_additive]
theorem toOpens_inf : (↑(U ⊓ V) : Opens G) = ↑U ⊓ ↑V :=
  rfl
#align open_subgroup.coe_opens_inf OpenSubgroup.toOpens_inf
#align open_add_subgroup.coe_opens_inf OpenAddSubgroup.toOpens_inf
-/

#print OpenSubgroup.mem_inf /-
@[simp, to_additive]
theorem mem_inf {x} : x ∈ U ⊓ V ↔ x ∈ U ∧ x ∈ V :=
  Iff.rfl
#align open_subgroup.mem_inf OpenSubgroup.mem_inf
#align open_add_subgroup.mem_inf OpenAddSubgroup.mem_inf
-/

@[to_additive]
instance : SemilatticeInf (OpenSubgroup G) :=
  { SetLike.partialOrder,
    SetLike.coe_injective.SemilatticeInf (coe : OpenSubgroup G → Set G) fun _ _ => rfl with }

@[to_additive]
instance : OrderTop (OpenSubgroup G) where
  top := ⊤
  le_top U := Set.subset_univ _

#print OpenSubgroup.toSubgroup_le /-
@[simp, norm_cast, to_additive]
theorem toSubgroup_le : (U : Subgroup G) ≤ (V : Subgroup G) ↔ U ≤ V :=
  Iff.rfl
#align open_subgroup.coe_subgroup_le OpenSubgroup.toSubgroup_le
#align open_add_subgroup.coe_add_subgroup_le OpenAddSubgroup.toAddSubgroup_le
-/

variable {N : Type _} [Group N] [TopologicalSpace N]

#print OpenSubgroup.comap /-
/-- The preimage of an `open_subgroup` along a continuous `monoid` homomorphism
  is an `open_subgroup`. -/
@[to_additive
      "The preimage of an `open_add_subgroup` along a continuous `add_monoid` homomorphism\nis an `open_add_subgroup`."]
def comap (f : G →* N) (hf : Continuous f) (H : OpenSubgroup N) : OpenSubgroup G :=
  { (H : Subgroup N).comap f with is_open' := H.IsOpen.Preimage hf }
#align open_subgroup.comap OpenSubgroup.comap
#align open_add_subgroup.comap OpenAddSubgroup.comap
-/

#print OpenSubgroup.coe_comap /-
@[simp, norm_cast, to_additive]
theorem coe_comap (H : OpenSubgroup N) (f : G →* N) (hf : Continuous f) :
    (H.comap f hf : Set G) = f ⁻¹' H :=
  rfl
#align open_subgroup.coe_comap OpenSubgroup.coe_comap
#align open_add_subgroup.coe_comap OpenAddSubgroup.coe_comap
-/

#print OpenSubgroup.toSubgroup_comap /-
@[simp, norm_cast, to_additive]
theorem toSubgroup_comap (H : OpenSubgroup N) (f : G →* N) (hf : Continuous f) :
    (H.comap f hf : Subgroup G) = (H : Subgroup N).comap f :=
  rfl
#align open_subgroup.coe_subgroup_comap OpenSubgroup.toSubgroup_comap
#align open_add_subgroup.coe_add_subgroup_comap OpenAddSubgroup.toAddSubgroup_comap
-/

#print OpenSubgroup.mem_comap /-
@[simp, to_additive]
theorem mem_comap {H : OpenSubgroup N} {f : G →* N} {hf : Continuous f} {x : G} :
    x ∈ H.comap f hf ↔ f x ∈ H :=
  Iff.rfl
#align open_subgroup.mem_comap OpenSubgroup.mem_comap
#align open_add_subgroup.mem_comap OpenAddSubgroup.mem_comap
-/

#print OpenSubgroup.comap_comap /-
@[to_additive]
theorem comap_comap {P : Type _} [Group P] [TopologicalSpace P] (K : OpenSubgroup P) (f₂ : N →* P)
    (hf₂ : Continuous f₂) (f₁ : G →* N) (hf₁ : Continuous f₁) :
    (K.comap f₂ hf₂).comap f₁ hf₁ = K.comap (f₂.comp f₁) (hf₂.comp hf₁) :=
  rfl
#align open_subgroup.comap_comap OpenSubgroup.comap_comap
#align open_add_subgroup.comap_comap OpenAddSubgroup.comap_comap
-/

end OpenSubgroup

namespace Subgroup

variable {G : Type _} [Group G] [TopologicalSpace G] [ContinuousMul G] (H : Subgroup G)

#print Subgroup.isOpen_of_mem_nhds /-
@[to_additive]
theorem isOpen_of_mem_nhds {g : G} (hg : (H : Set G) ∈ 𝓝 g) : IsOpen (H : Set G) :=
  by
  refine' isOpen_iff_mem_nhds.2 fun x hx => _
  have hg' : g ∈ H := SetLike.mem_coe.1 (mem_of_mem_nhds hg)
  have : Filter.Tendsto (fun y => y * (x⁻¹ * g)) (𝓝 x) (𝓝 g) :=
    (continuous_id.mul continuous_const).tendsto' _ _ (mul_inv_cancel_left _ _)
  simpa only [SetLike.mem_coe, Filter.mem_map',
    H.mul_mem_cancel_right (H.mul_mem (H.inv_mem hx) hg')] using this hg
#align subgroup.is_open_of_mem_nhds Subgroup.isOpen_of_mem_nhds
#align add_subgroup.is_open_of_mem_nhds AddSubgroup.isOpen_of_mem_nhds
-/

#print Subgroup.isOpen_mono /-
@[to_additive]
theorem isOpen_mono {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) (h₁ : IsOpen (H₁ : Set G)) :
    IsOpen (H₂ : Set G) :=
  isOpen_of_mem_nhds _ <| Filter.mem_of_superset (h₁.mem_nhds <| one_mem H₁) h
#align subgroup.is_open_mono Subgroup.isOpen_mono
#align add_subgroup.is_open_mono AddSubgroup.isOpen_mono
-/

#print Subgroup.isOpen_of_openSubgroup /-
@[to_additive]
theorem isOpen_of_openSubgroup {U : OpenSubgroup G} (h : ↑U ≤ H) : IsOpen (H : Set G) :=
  isOpen_mono h U.IsOpen
#align subgroup.is_open_of_open_subgroup Subgroup.isOpen_of_openSubgroup
#align add_subgroup.is_open_of_open_add_subgroup AddSubgroup.isOpen_of_openAddSubgroup
-/

#print Subgroup.isOpen_of_one_mem_interior /-
/-- If a subgroup of a topological group has `1` in its interior, then it is open. -/
@[to_additive
      "If a subgroup of an additive topological group has `0` in its interior, then it is\nopen."]
theorem isOpen_of_one_mem_interior (h_1_int : (1 : G) ∈ interior (H : Set G)) :
    IsOpen (H : Set G) :=
  isOpen_of_mem_nhds H <| mem_interior_iff_mem_nhds.1 h_1_int
#align subgroup.is_open_of_one_mem_interior Subgroup.isOpen_of_one_mem_interior
#align add_subgroup.is_open_of_zero_mem_interior AddSubgroup.isOpen_of_zero_mem_interior
-/

end Subgroup

namespace OpenSubgroup

variable {G : Type _} [Group G] [TopologicalSpace G] [ContinuousMul G]

@[to_additive]
instance : Sup (OpenSubgroup G) :=
  ⟨fun U V => ⟨U ⊔ V, Subgroup.isOpen_mono (le_sup_left : U.1 ≤ U ⊔ V) U.IsOpen⟩⟩

#print OpenSubgroup.toSubgroup_sup /-
@[simp, norm_cast, to_additive]
theorem toSubgroup_sup (U V : OpenSubgroup G) : (↑(U ⊔ V) : Subgroup G) = ↑U ⊔ ↑V :=
  rfl
#align open_subgroup.coe_subgroup_sup OpenSubgroup.toSubgroup_sup
#align open_add_subgroup.coe_add_subgroup_sup OpenAddSubgroup.toAddSubgroup_sup
-/

@[to_additive]
instance : Lattice (OpenSubgroup G) :=
  { OpenSubgroup.semilatticeInf,
    toSubgroup_injective.SemilatticeSup (coe : OpenSubgroup G → Subgroup G) fun _ _ => rfl with }

end OpenSubgroup

namespace Submodule

open OpenAddSubgroup

variable {R : Type _} {M : Type _} [CommRing R]

variable [AddCommGroup M] [TopologicalSpace M] [TopologicalAddGroup M] [Module R M]

#print Submodule.isOpen_mono /-
theorem isOpen_mono {U P : Submodule R M} (h : U ≤ P) (hU : IsOpen (U : Set M)) :
    IsOpen (P : Set M) :=
  @AddSubgroup.isOpen_mono M _ _ _ U.toAddSubgroup P.toAddSubgroup h hU
#align submodule.is_open_mono Submodule.isOpen_mono
-/

end Submodule

namespace Ideal

variable {R : Type _} [CommRing R]

variable [TopologicalSpace R] [TopologicalRing R]

#print Ideal.isOpen_of_isOpen_subideal /-
theorem isOpen_of_isOpen_subideal {U I : Ideal R} (h : U ≤ I) (hU : IsOpen (U : Set R)) :
    IsOpen (I : Set R) :=
  Submodule.isOpen_mono h hU
#align ideal.is_open_of_open_subideal Ideal.isOpen_of_isOpen_subideal
-/

end Ideal

