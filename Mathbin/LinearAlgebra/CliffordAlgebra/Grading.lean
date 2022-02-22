/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.LinearAlgebra.CliffordAlgebra.Basic
import Mathbin.Data.Zmod.Basic
import Mathbin.RingTheory.GradedAlgebra.Basic

/-!
# Results about the grading structure of the clifford algebra

The main result is `clifford_algebra.graded_algebra`, which says that the clifford algebra is a
ℤ₂-graded algebra (or "superalgebra").
-/


namespace CliffordAlgebra

variable {R M : Type _} [CommRingₓ R] [AddCommGroupₓ M] [Module R M]

variable {Q : QuadraticForm R M}

open_locale DirectSum

variable (Q)

/-- The even or odd submodule, defined as the supremum of the even or odd powers of
`(ι Q).range`. `even_odd 0` is the even submodule, and `even_odd 1` is the odd submodule. -/
def evenOdd (i : Zmod 2) : Submodule R (CliffordAlgebra Q) :=
  ⨆ j : { n : ℕ // ↑n = i }, (ι Q).range ^ (j : ℕ)

theorem one_le_even_odd_zero : 1 ≤ evenOdd Q 0 := by
  refine' le_transₓ _ (le_supr _ ⟨0, Nat.cast_zeroₓ⟩)
  exact (pow_zeroₓ _).Ge

theorem range_ι_le_even_odd_one : (ι Q).range ≤ evenOdd Q 1 := by
  refine' le_transₓ _ (le_supr _ ⟨1, Nat.cast_oneₓ⟩)
  exact (pow_oneₓ _).Ge

theorem even_odd_mul_le (i j : Zmod 2) : evenOdd Q i * evenOdd Q j ≤ evenOdd Q (i + j) := by
  simp_rw [even_odd, Submodule.supr_eq_span, Submodule.span_mul_span]
  apply Submodule.span_mono
  intro z hz
  obtain ⟨x, y, hx, hy, rfl⟩ := hz
  obtain ⟨xi, hx'⟩ := set.mem_Union.mp hx
  obtain ⟨yi, hy'⟩ := set.mem_Union.mp hy
  refine'
    set.mem_Union.mpr
      ⟨⟨xi + yi, by
          simp only [Nat.cast_addₓ, xi.prop, yi.prop]⟩,
        _⟩
  simp only [Subtype.coe_mk, Nat.cast_addₓ, pow_addₓ]
  exact Submodule.mul_mem_mul hx' hy'

instance evenOdd.graded_monoid : SetLike.GradedMonoid (evenOdd Q) where
  one_mem := Submodule.one_le.mp (one_le_even_odd_zero Q)
  mul_mem := fun i j p q hp hq => Submodule.mul_le.mp (even_odd_mul_le Q _ _) _ hp _ hq

/-- A version of `clifford_algebra.ι` that maps directly into the graded structure. This is
primarily an auxiliary construction used to provide `clifford_algebra.graded_algebra`. -/
def GradedAlgebra.ι : M →ₗ[R] ⨁ i : Zmod 2, evenOdd Q i :=
  DirectSum.lof R (Zmod 2) (fun i => ↥(evenOdd Q i)) 1 ∘ₗ
    (ι Q).codRestrict _ fun m => range_ι_le_even_odd_one Q <| LinearMap.mem_range_self _ m

theorem GradedAlgebra.ι_apply (m : M) :
    GradedAlgebra.ι Q m =
      DirectSum.of (fun i => ↥(evenOdd Q i)) 1 ⟨ι Q m, range_ι_le_even_odd_one Q <| LinearMap.mem_range_self _ m⟩ :=
  rfl

theorem GradedAlgebra.ι_sq_scalar (m : M) : GradedAlgebra.ι Q m * GradedAlgebra.ι Q m = algebraMap R _ (Q m) := by
  rw [graded_algebra.ι_apply, DirectSum.of_mul_of, DirectSum.algebra_map_apply]
  refine' DirectSum.of_eq_of_graded_monoid_eq (Sigma.subtype_ext rfl <| ι_sq_scalar _ _)

/-- The clifford algebra is graded by the even and odd parts. -/
instance gradedAlgebra : GradedAlgebra (evenOdd Q) :=
  GradedAlgebra.ofAlgHom _ (lift _ <| ⟨GradedAlgebra.ι Q, GradedAlgebra.ι_sq_scalar Q⟩)
    (-- the proof from here onward is mostly similar to the `tensor_algebra` case, with some extra
    -- handling for the `supr` in `even_odd`.
    by
      ext m
      dsimp only [LinearMap.comp_apply, AlgHom.to_linear_map_apply, AlgHom.comp_apply, AlgHom.id_apply]
      rw [lift_ι_apply, graded_algebra.ι_apply, DirectSum.submodule_coe_alg_hom_of, Subtype.coe_mk])
    fun i' x' => by
    cases' x' with x' hx'
    dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
    refine' Submodule.supr_induction' _ (fun i x hx => _) _ (fun x y hx hy ihx ihy => _) hx'
    · obtain ⟨i, rfl⟩ := i
      dsimp only [Subtype.coe_mk]  at hx
      refine' Submodule.pow_induction_on' _ (fun r => _) (fun x y i hx hy ihx ihy => _) (fun m hm i x hx ih => _) hx
      · rw [AlgHom.commutes, DirectSum.algebra_map_apply]
        rfl
        
      · rw [AlgHom.map_add, ihx, ihy, ← map_add]
        rfl
        
      · obtain ⟨_, rfl⟩ := hm
        rw [AlgHom.map_mul, ih, lift_ι_apply, graded_algebra.ι_apply, DirectSum.of_mul_of]
        refine' DirectSum.of_eq_of_graded_monoid_eq (Sigma.subtype_ext _ _)
        dsimp only [GradedMonoid.mk, Subtype.coe_mk]
        · rw [Nat.succ_eq_add_one, add_commₓ]
          rfl
          
        rfl
        
      
    · rw [AlgHom.map_zero]
      apply Eq.symm
      apply dfinsupp.single_eq_zero.mpr
      rfl
      
    · rw [AlgHom.map_add, ihx, ihy, ← map_add]
      rfl
      

theorem supr_ι_range_eq_top : (⨆ i : ℕ, (ι Q).range ^ i) = ⊤ := by
  rw [← (GradedAlgebra.is_internal fun i => even_odd Q i).supr_eq_top, eq_comm]
  dunfold even_odd
  calc
    (⨆ (i : Zmod 2) (j : { n // ↑n = i }), (ι Q).range ^ ↑j) =
        ⨆ i : Σi : Zmod 2, { n : ℕ // ↑n = i }, (ι Q).range ^ (i.2 : ℕ) :=
      by
      rw [supr_sigma]_ = ⨆ i : ℕ, (ι Q).range ^ i :=
      supr_congr (fun i => i.2) (fun i => ⟨⟨_, i, rfl⟩, rfl⟩) fun _ => rfl

end CliffordAlgebra

