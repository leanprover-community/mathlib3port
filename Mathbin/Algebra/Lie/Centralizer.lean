/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module algebra.lie.centralizer
! leanprover-community/mathlib commit d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Lie.Abelian
import Mathbin.Algebra.Lie.IdealOperations
import Mathbin.Algebra.Lie.Quotient

/-!
# The centralizer of a Lie submodule and the normalizer of a Lie subalgebra.

Given a Lie module `M` over a Lie subalgebra `L`, the centralizer of a Lie submodule `N ⊆ M` is
the Lie submodule with underlying set `{ m | ∀ (x : L), ⁅x, m⁆ ∈ N }`.

The lattice of Lie submodules thus has two natural operations, the centralizer: `N ↦ N.centralizer`
and the ideal operation: `N ↦ ⁅⊤, N⁆`; these are adjoint, i.e., they form a Galois connection. This
adjointness is the reason that we may define nilpotency in terms of either the upper or lower
central series.

Given a Lie subalgebra `H ⊆ L`, we may regard `H` as a Lie submodule of `L` over `H`, and thus
consider the centralizer. This turns out to be a Lie subalgebra and is known as the normalizer.

## Main definitions

  * `lie_submodule.centralizer`
  * `lie_subalgebra.normalizer`
  * `lie_submodule.gc_top_lie_centralizer`

## Tags

lie algebra, centralizer, normalizer
-/


variable {R L M M' : Type _}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']

namespace LieSubmodule

variable (N : LieSubmodule R L M) {N₁ N₂ : LieSubmodule R L M}

/-- The centralizer of a Lie submodule. -/
def centralizer : LieSubmodule R L M
    where
  carrier := { m | ∀ x : L, ⁅x, m⁆ ∈ N }
  add_mem' m₁ m₂ hm₁ hm₂ x := by
    rw [lie_add]
    exact N.add_mem' (hm₁ x) (hm₂ x)
  zero_mem' x := by simp
  smul_mem' t m hm x := by
    rw [lie_smul]
    exact N.smul_mem' t (hm x)
  lie_mem x m hm y := by
    rw [leibniz_lie]
    exact N.add_mem' (hm ⁅y, x⁆) (N.lie_mem (hm y))
#align lie_submodule.centralizer LieSubmodule.centralizer

@[simp]
theorem mem_centralizer (m : M) : m ∈ N.centralizer ↔ ∀ x : L, ⁅x, m⁆ ∈ N :=
  Iff.rfl
#align lie_submodule.mem_centralizer LieSubmodule.mem_centralizer

theorem le_centralizer : N ≤ N.centralizer :=
  by
  intro m hm
  rw [mem_centralizer]
  exact fun x => N.lie_mem hm
#align lie_submodule.le_centralizer LieSubmodule.le_centralizer

theorem centralizer_inf : (N₁ ⊓ N₂).centralizer = N₁.centralizer ⊓ N₂.centralizer :=
  by
  ext
  simp [← forall_and]
#align lie_submodule.centralizer_inf LieSubmodule.centralizer_inf

@[mono]
theorem monotone_centalizer : Monotone (centralizer : LieSubmodule R L M → LieSubmodule R L M) :=
  by
  intro N₁ N₂ h m hm
  rw [mem_centralizer] at hm⊢
  exact fun x => h (hm x)
#align lie_submodule.monotone_centalizer LieSubmodule.monotone_centalizer

@[simp]
theorem comap_centralizer (f : M' →ₗ⁅R,L⁆ M) : N.centralizer.comap f = (N.comap f).centralizer :=
  by
  ext
  simp
#align lie_submodule.comap_centralizer LieSubmodule.comap_centralizer

theorem top_lie_le_iff_le_centralizer (N' : LieSubmodule R L M) :
    ⁅(⊤ : LieIdeal R L), N⁆ ≤ N' ↔ N ≤ N'.centralizer :=
  by
  rw [lie_le_iff]
  tauto
#align lie_submodule.top_lie_le_iff_le_centralizer LieSubmodule.top_lie_le_iff_le_centralizer

theorem gc_top_lie_centralizer :
    GaloisConnection (fun N : LieSubmodule R L M => ⁅(⊤ : LieIdeal R L), N⁆) centralizer :=
  top_lie_le_iff_le_centralizer
#align lie_submodule.gc_top_lie_centralizer LieSubmodule.gc_top_lie_centralizer

variable (R L M)

theorem centralizer_bot_eq_maxTrivSubmodule :
    (⊥ : LieSubmodule R L M).centralizer = LieModule.maxTrivSubmodule R L M :=
  rfl
#align lie_submodule.centralizer_bot_eq_max_triv_submodule LieSubmodule.centralizer_bot_eq_maxTrivSubmodule

end LieSubmodule

namespace LieSubalgebra

variable (H : LieSubalgebra R L)

/-- Regarding a Lie subalgebra `H ⊆ L` as a module over itself, its centralizer is in fact a Lie
subalgebra. This is called the normalizer of the Lie subalgebra. -/
def normalizer : LieSubalgebra R L :=
  { H.toLieSubmodule.centralizer with
    lie_mem' := fun y z hy hz x =>
      by
      rw [coe_bracket_of_module, mem_to_lie_submodule, leibniz_lie, ← lie_skew y, ← sub_eq_add_neg]
      exact H.sub_mem (hz ⟨_, hy x⟩) (hy ⟨_, hz x⟩) }
#align lie_subalgebra.normalizer LieSubalgebra.normalizer

theorem mem_normalizer_iff' (x : L) : x ∈ H.normalizer ↔ ∀ y : L, y ∈ H → ⁅y, x⁆ ∈ H :=
  by
  rw [Subtype.forall']
  rfl
#align lie_subalgebra.mem_normalizer_iff' LieSubalgebra.mem_normalizer_iff'

theorem mem_normalizer_iff (x : L) : x ∈ H.normalizer ↔ ∀ y : L, y ∈ H → ⁅x, y⁆ ∈ H :=
  by
  rw [mem_normalizer_iff']
  refine' forall₂_congr fun y hy => _
  rw [← lie_skew, neg_mem_iff]
#align lie_subalgebra.mem_normalizer_iff LieSubalgebra.mem_normalizer_iff

theorem le_normalizer : H ≤ H.normalizer :=
  H.toLieSubmodule.le_centralizer
#align lie_subalgebra.le_normalizer LieSubalgebra.le_normalizer

theorem coe_centralizer_eq_normalizer :
    (H.toLieSubmodule.centralizer : Submodule R L) = H.normalizer :=
  rfl
#align lie_subalgebra.coe_centralizer_eq_normalizer LieSubalgebra.coe_centralizer_eq_normalizer

variable {H}

theorem lie_mem_sup_of_mem_normalizer {x y z : L} (hx : x ∈ H.normalizer) (hy : y ∈ (R ∙ x) ⊔ ↑H)
    (hz : z ∈ (R ∙ x) ⊔ ↑H) : ⁅y, z⁆ ∈ (R ∙ x) ⊔ ↑H :=
  by
  rw [Submodule.mem_sup] at hy hz
  obtain ⟨u₁, hu₁, v, hv : v ∈ H, rfl⟩ := hy
  obtain ⟨u₂, hu₂, w, hw : w ∈ H, rfl⟩ := hz
  obtain ⟨t, rfl⟩ := submodule.mem_span_singleton.mp hu₁
  obtain ⟨s, rfl⟩ := submodule.mem_span_singleton.mp hu₂
  apply Submodule.mem_sup_right
  simp only [LieSubalgebra.mem_coe_submodule, smul_lie, add_lie, zero_add, lie_add, smul_zero,
    lie_smul, lie_self]
  refine' H.add_mem (H.smul_mem s _) (H.add_mem (H.smul_mem t _) (H.lie_mem hv hw))
  exacts[(H.mem_normalizer_iff' x).mp hx v hv, (H.mem_normalizer_iff x).mp hx w hw]
#align lie_subalgebra.lie_mem_sup_of_mem_normalizer LieSubalgebra.lie_mem_sup_of_mem_normalizer

/-- A Lie subalgebra is an ideal of its normalizer. -/
theorem ideal_in_normalizer {x y : L} (hx : x ∈ H.normalizer) (hy : y ∈ H) : ⁅x, y⁆ ∈ H :=
  by
  rw [← lie_skew, neg_mem_iff]
  exact hx ⟨y, hy⟩
#align lie_subalgebra.ideal_in_normalizer LieSubalgebra.ideal_in_normalizer

/-- A Lie subalgebra `H` is an ideal of any Lie subalgebra `K` containing `H` and contained in the
normalizer of `H`. -/
theorem exists_nested_lieIdeal_ofLe_normalizer {K : LieSubalgebra R L} (h₁ : H ≤ K)
    (h₂ : K ≤ H.normalizer) : ∃ I : LieIdeal R K, (I : LieSubalgebra R K) = ofLe h₁ :=
  by
  rw [exists_nested_lie_ideal_coe_eq_iff]
  exact fun x y hx hy => ideal_in_normalizer (h₂ hx) hy
#align lie_subalgebra.exists_nested_lie_ideal_of_le_normalizer LieSubalgebra.exists_nested_lieIdeal_ofLe_normalizer

variable (H)

theorem normalizer_eq_self_iff :
    H.normalizer = H ↔ (LieModule.maxTrivSubmodule R H <| L ⧸ H.toLieSubmodule) = ⊥ :=
  by
  rw [LieSubmodule.eq_bot_iff]
  refine' ⟨fun h => _, fun h => le_antisymm (fun x hx => _) H.le_normalizer⟩
  · rintro ⟨x⟩ hx
    suffices x ∈ H by simpa
    rw [← h, H.mem_normalizer_iff']
    intro y hy
    replace hx : ⁅_, LieSubmodule.Quotient.mk' _ x⁆ = 0 := hx ⟨y, hy⟩
    rwa [← LieModuleHom.map_lie, LieSubmodule.Quotient.mk_eq_zero] at hx
  · let y := LieSubmodule.Quotient.mk' H.to_lie_submodule x
    have hy : y ∈ LieModule.maxTrivSubmodule R H (L ⧸ H.to_lie_submodule) :=
      by
      rintro ⟨z, hz⟩
      rw [← LieModuleHom.map_lie, LieSubmodule.Quotient.mk_eq_zero, coe_bracket_of_module,
        Submodule.coe_mk, mem_to_lie_submodule]
      exact (H.mem_normalizer_iff' x).mp hx z hz
    simpa using h y hy
#align lie_subalgebra.normalizer_eq_self_iff LieSubalgebra.normalizer_eq_self_iff

end LieSubalgebra

