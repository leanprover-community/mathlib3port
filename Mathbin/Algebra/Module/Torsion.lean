/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import Mathbin.Algebra.Module.Default
import Mathbin.LinearAlgebra.Quotient
import Mathbin.RingTheory.Ideal.Quotient
import Mathbin.RingTheory.NonZeroDivisors
import Mathbin.GroupTheory.Torsion

/-!
# Torsion submodules

## Main definitions

* `submodule.torsion_by R M a` : the `a`-torsion submodule, containing all elements `x` of `M` such
  that `a • x = 0`.
* `submodule.torsion' R M S` : the `S`-torsion submodule, containing all elements `x` of `M` such
  that `a • x = 0` for some `a` in `S`.
* `submodule.torsion R M` : the torsion submoule, containing all elements `x` of `M` such that
  `a • x = 0` for some non-zero-divisor `a` in `R`.
* `module.is_torsion_by R M a` : the property that defines a `a`-torsion module. Similarly,
  `is_torsion'` and `is_torsion`.

## Main statements

* `torsion' R M S` and `torsion R M` are submodules.
* `torsion_by R M a` can be viewed as a `(R ⧸ R∙a)`-module.
* `submodule.torsion_by_is_torsion_by` : the `a`-torsion submodule is a `a`-torsion module.
  Similar lemmas for `torsion'` and `torsion`.
* `submodule.no_zero_smul_divisors_iff_torsion_bot` : a module over a domain has
  `no_zero_smul_divisors` (that is, there is no non-zero `a`, `x` such that `a • x = 0`)
  iff its torsion submodule is trivial.
* `submodule.quotient_torsion.torsion_eq_bot` : quotienting by the torsion submodule makes the
  torsion submodule of the new module trivial. If `R` is a domain, we can derive an instance
  `submodule.quotient_torsion.no_zero_smul_divisors : no_zero_smul_divisors R (M ⧸ torsion R M)`.

## Notation

* The notions are defined for a `comm_semiring R` and a `module R M`. Some additional hypotheses on
  `R` and `M` are required by some lemmas.
* The letters `a`, `b`, ... are used for scalars (in `R`), while `x`, `y`, ... are used for vectors
  (in `M`).

## Tags

Torsion, submodule, module, quotient
-/


open nonZeroDivisors

section Defs

variable (R M : Type _) [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M]

namespace Submodule

/-- The `a`-torsion submodule for `a` in `R`, containing all elements `x` of `M` such that
  `a • x = 0`. -/
@[simps]
def torsionBy (a : R) : Submodule R M :=
  (DistribMulAction.toLinearMap _ _ a).ker

/-- The `S`-torsion submodule, containing all elements `x` of `M` such that `a • x = 0` for some
`a` in `S`. -/
@[simps]
def torsion' (S : Type _) [CommMonoidₓ S] [DistribMulAction S M] [SmulCommClass S R M] : Submodule R M where
  Carrier := { x | ∃ a : S, a • x = 0 }
  zero_mem' := ⟨1, smul_zero _⟩
  add_mem' := fun x y ⟨a, hx⟩ ⟨b, hy⟩ =>
    ⟨b * a, by
      rw [smul_add, mul_smul, mul_comm, mul_smul, hx, hy, smul_zero, smul_zero, add_zeroₓ]⟩
  smul_mem' := fun a x ⟨b, h⟩ =>
    ⟨b, by
      rw [smul_comm, h, smul_zero]⟩

/-- The torsion submodule, containing all elements `x` of `M` such that  `a • x = 0` for some
  non-zero-divisor `a` in `R`. -/
@[reducible]
def torsion :=
  torsion' R M R⁰

end Submodule

namespace Module

/-- A `a`-torsion module is a module where every element is `a`-torsion. -/
@[reducible]
def IsTorsionBy (a : R) :=
  ∀ ⦃x : M⦄, a • x = 0

/-- A `S`-torsion module is a module where every element is `a`-torsion for some `a` in `S`. -/
@[reducible]
def IsTorsion' (S : Type _) [HasScalar S M] :=
  ∀ ⦃x : M⦄, ∃ a : S, a • x = 0

/-- A torsion module is a module where every element is `a`-torsion for some non-zero-divisor `a`.
-/
@[reducible]
def IsTorsion :=
  ∀ ⦃x : M⦄, ∃ a : R⁰, a • x = 0

end Module

end Defs

namespace Submodule

open Module

variable {R M : Type _}

section TorsionBy

variable [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M] (a : R)

@[simp]
theorem smul_torsion_by (x : torsionBy R M a) : a • x = 0 :=
  Subtype.ext x.Prop

@[simp]
theorem smul_coe_torsion_by (x : torsionBy R M a) : a • (x : M) = 0 :=
  x.Prop

@[simp]
theorem mem_torsion_by_iff (x : M) : x ∈ torsionBy R M a ↔ a • x = 0 :=
  Iff.rfl

/-- A `a`-torsion module is a module whose `a`-torsion submodule is the full space. -/
theorem is_torsion_by_iff_torsion_by_eq_top : IsTorsionBy R M a ↔ torsionBy R M a = ⊤ :=
  ⟨fun h => eq_top_iff.mpr fun _ _ => @h _, fun h x => by
    rw [← mem_torsion_by_iff, h]
    trivial⟩

/-- The `a`-torsion submodule is a `a`-torsion module. -/
theorem torsion_by_is_torsion_by : IsTorsionBy R (torsionBy R M a) a := fun _ => smul_torsion_by _ _

@[simp]
theorem torsion_by_torsion_by_eq_top : torsionBy R (torsionBy R M a) a = ⊤ :=
  (is_torsion_by_iff_torsion_by_eq_top a).mp <| torsion_by_is_torsion_by a

end TorsionBy

section Quotientₓ

variable [CommRingₓ R] [AddCommGroupₓ M] [Module R M] (a : R)

instance : HasScalar (R ⧸ R∙a) (torsionBy R M a) where
  smul := fun b x =>
    (Quotientₓ.liftOn' b (· • x)) fun b₁ b₂ h => by
      rw [Submodule.quotient_rel_r_def] at h
      show b₁ • x = b₂ • x
      obtain ⟨c, h⟩ := ideal.mem_span_singleton'.mp h
      rw [← sub_eq_zero, ← sub_smul, ← h, mul_smul, smul_torsion_by, smul_zero]

@[simp]
theorem torsionBy.mk_smul (b : R) (x : torsionBy R M a) : Ideal.Quotient.mk (R∙a) b • x = b • x :=
  rfl

/-- The `a`-torsion submodule as a `(R ⧸ R∙a)`-module. -/
instance : Module (R ⧸ R∙a) (torsionBy R M a) :=
  @Function.Surjective.moduleLeft _ _ (torsionBy R M a) _ _ _ _ _ (Ideal.Quotient.mk <| R∙a)
    Ideal.Quotient.mk_surjective (torsionBy.mk_smul _)

instance {S : Type _} [HasScalar S R] [HasScalar S M] [IsScalarTower S R M] [IsScalarTower S R R] :
    IsScalarTower S (R ⧸ R∙a) (torsionBy R M a) where
  smul_assoc := fun b d x => (Quotientₓ.induction_on' d) fun c => (smul_assoc b c x : _)

end Quotientₓ

section Torsion'

variable [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M]

variable (S : Type _) [CommMonoidₓ S] [DistribMulAction S M] [SmulCommClass S R M]

@[simp]
theorem mem_torsion'_iff (x : M) : x ∈ torsion' R M S ↔ ∃ a : S, a • x = 0 :=
  Iff.rfl

@[simp]
theorem mem_torsion_iff (x : M) : x ∈ torsion R M ↔ ∃ a : R⁰, a • x = 0 :=
  Iff.rfl

@[simps]
instance : HasScalar S (torsion' R M S) :=
  ⟨fun s x =>
    ⟨s • x, by
      obtain ⟨x, a, h⟩ := x
      use a
      dsimp'
      rw [smul_comm, h, smul_zero]⟩⟩

instance : DistribMulAction S (torsion' R M S) :=
  Subtype.coe_injective.DistribMulAction (torsion' R M S).Subtype.toAddMonoidHom fun x => rfl

instance : SmulCommClass S R (torsion' R M S) :=
  ⟨fun s a x => Subtype.ext <| smul_comm _ _ _⟩

/-- A `S`-torsion module is a module whose `S`-torsion submodule is the full space. -/
theorem is_torsion'_iff_torsion'_eq_top : IsTorsion' M S ↔ torsion' R M S = ⊤ :=
  ⟨fun h => eq_top_iff.mpr fun _ _ => @h _, fun h x => by
    rw [← @mem_torsion'_iff R, h]
    trivial⟩

/-- The `S`-torsion submodule is a `S`-torsion module. -/
theorem torsion'_is_torsion' : IsTorsion' (torsion' R M S) S := fun ⟨x, ⟨a, h⟩⟩ => ⟨a, Subtype.ext h⟩

@[simp]
theorem torsion'_torsion'_eq_top : torsion' R (torsion' R M S) S = ⊤ :=
  (is_torsion'_iff_torsion'_eq_top S).mp <| torsion'_is_torsion' S

/-- The torsion submodule of the torsion submodule (viewed as a module) is the full
torsion module. -/
@[simp]
theorem torsion_torsion_eq_top : torsion R (torsion R M) = ⊤ :=
  torsion'_torsion'_eq_top R⁰

/-- The torsion submodule is always a torsion module. -/
theorem torsion_is_torsion : Module.IsTorsion R (torsion R M) :=
  torsion'_is_torsion' R⁰

end Torsion'

section torsion

variable [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M] [NoZeroDivisors R] [Nontrivial R]

theorem coe_torsion_eq_annihilator_ne_bot : (torsion R M : Set M) = { x : M | (R∙x).annihilator ≠ ⊥ } := by
  ext x
  simp_rw [Submodule.ne_bot_iff, mem_annihilator, mem_span_singleton]
  exact
    ⟨fun ⟨a, hax⟩ =>
      ⟨a, fun _ ⟨b, hb⟩ => by
        rw [← hb, smul_comm, ← Submonoid.smul_def, hax, smul_zero], nonZeroDivisors.coe_ne_zero _⟩,
      fun ⟨a, hax, ha⟩ => ⟨⟨_, mem_non_zero_divisors_of_ne_zero ha⟩, hax x ⟨1, one_smul _ _⟩⟩⟩

/-- A module over a domain has `no_zero_smul_divisors` iff its torsion submodule is trivial. -/
theorem no_zero_smul_divisors_iff_torsion_eq_bot : NoZeroSmulDivisors R M ↔ torsion R M = ⊥ := by
  constructor <;> intro h
  · have : NoZeroSmulDivisors R M := h
    rw [eq_bot_iff]
    rintro x ⟨a, hax⟩
    change (a : R) • x = 0 at hax
    cases' eq_zero_or_eq_zero_of_smul_eq_zero hax with h0 h0
    · exfalso
      exact nonZeroDivisors.coe_ne_zero a h0
      
    · exact h0
      
    
  · exact
      { eq_zero_or_eq_zero_of_smul_eq_zero := fun a x hax => by
          by_cases' ha : a = 0
          · left
            exact ha
            
          · right
            rw [← mem_bot _, ← h]
            exact ⟨⟨a, mem_non_zero_divisors_of_ne_zero ha⟩, hax⟩
             }
    

end torsion

namespace QuotientTorsion

variable [CommRingₓ R] [AddCommGroupₓ M] [Module R M]

/-- Quotienting by the torsion submodule gives a torsion-free module. -/
@[simp]
theorem torsion_eq_bot : torsion R (M ⧸ torsion R M) = ⊥ :=
  eq_bot_iff.mpr fun z =>
    (Quotientₓ.induction_on' z) fun x ⟨a, hax⟩ => by
      rw [Quotientₓ.mk'_eq_mk, ← quotient.mk_smul, quotient.mk_eq_zero] at hax
      rw [mem_bot, Quotientₓ.mk'_eq_mk, quotient.mk_eq_zero]
      cases' hax with b h
      exact ⟨b * a, (mul_smul _ _ _).trans h⟩

instance no_zero_smul_divisors [IsDomain R] : NoZeroSmulDivisors R (M ⧸ torsion R M) :=
  no_zero_smul_divisors_iff_torsion_eq_bot.mpr torsion_eq_bot

end QuotientTorsion

end Submodule

namespace AddMonoidₓ

variable {M : Type _}

theorem is_torsion_iff_is_torsion_nat [AddCommMonoidₓ M] : AddMonoidₓ.IsTorsion M ↔ Module.IsTorsion ℕ M := by
  refine' ⟨fun h x => _, fun h x => _⟩
  · obtain ⟨n, h0, hn⟩ := (is_of_fin_add_order_iff_nsmul_eq_zero x).mp (h x)
    exact ⟨⟨n, mem_non_zero_divisors_of_ne_zero <| ne_of_gtₓ h0⟩, hn⟩
    
  · rw [is_of_fin_add_order_iff_nsmul_eq_zero]
    obtain ⟨n, hn⟩ := @h x
    refine' ⟨n, Nat.pos_of_ne_zeroₓ (nonZeroDivisors.coe_ne_zero _), hn⟩
    

theorem is_torsion_iff_is_torsion_int [AddCommGroupₓ M] : AddMonoidₓ.IsTorsion M ↔ Module.IsTorsion ℤ M := by
  refine' ⟨fun h x => _, fun h x => _⟩
  · obtain ⟨n, h0, hn⟩ := (is_of_fin_add_order_iff_nsmul_eq_zero x).mp (h x)
    exact ⟨⟨n, mem_non_zero_divisors_of_ne_zero <| ne_of_gtₓ <| int.coe_nat_pos.mpr h0⟩, (coe_nat_zsmul _ _).trans hn⟩
    
  · rw [is_of_fin_add_order_iff_nsmul_eq_zero]
    obtain ⟨n, hn⟩ := @h x
    exact exists_nsmul_eq_zero_of_zsmul_eq_zero (nonZeroDivisors.coe_ne_zero n) hn
    

end AddMonoidₓ

