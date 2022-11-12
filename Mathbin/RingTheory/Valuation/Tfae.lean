/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.RingTheory.Valuation.ValuationSubring
import Mathbin.RingTheory.Ideal.Cotangent
import Mathbin.RingTheory.DedekindDomain.Basic

/-!

# Equivalent conditions for DVR

In `discrete_valuation_ring.tfae`, we show that the following are equivalent for a
noetherian local domain `(R, m, k)`:
- `R` is a discrete valuation ring
- `R` is a valuation ring
- `R` is a dedekind domain
- `R` is integrally closed with a unique prime ideal
- `m` is principal
- `dimₖ m/m² = 1`
- Every nonzero ideal is a power of `m`.

-/


variable (R : Type _) [CommRing R] (K : Type _) [Field K] [Algebra R K] [IsFractionRing R K]

open DiscreteValuation

open LocalRing

open BigOperators

theorem exists_maximal_ideal_pow_eq_of_principal [IsNoetherianRing R] [LocalRing R] [IsDomain R] (h : ¬IsField R)
    (h' : (maximalIdeal R).IsPrincipal) (I : Ideal R) (hI : I ≠ ⊥) : ∃ n : ℕ, I = maximalIdeal R ^ n := by
  classical obtain ⟨x, hx : _ = Ideal.span _⟩ := h'
    · use 0
      rw [pow_zero, hI', Ideal.one_eq_top]
      
    have : x ≠ 0
    have hx' := DiscreteValuationRing.irreducible_of_span_eq_maximal_ideal x this hx
    · intro r hr₁ hr₂
      obtain ⟨f, hf₁, rfl, hf₂⟩ := (WfDvdMonoid.not_unit_iff_exists_factors_eq r hr₁).mp hr₂
      have : ∀ b ∈ f, Associated x b := by
        intro b hb
        exact Irreducible.associated_of_dvd hx' (hf₁ b hb) ((H b).mp (hf₁ b hb).1)
      clear hr₁ hr₂ hf₁
      induction' f using Multiset.induction with fa fs fh
      · exact (hf₂ rfl).elim
        
      rcases eq_or_ne fs ∅ with (rfl | hf')
      · use 1
        rw [pow_one, Multiset.prod_cons, Multiset.empty_eq_zero, Multiset.prod_zero, mul_one]
        exact this _ (Multiset.mem_cons_self _ _)
        
      · obtain ⟨n, hn⟩ := fh hf' fun b hb => this _ (Multiset.mem_cons_of_mem hb)
        use n + 1
        rw [pow_add, Multiset.prod_cons, mul_comm, pow_one]
        exact Associated.mul_mul (this _ (Multiset.mem_cons_self _ _)) hn
        
      
    · obtain ⟨r, hr₁, hr₂⟩ : ∃ r : R, r ∈ I ∧ r ≠ 0 := by
        by_contra h
        push_neg  at h
        apply hI
        rw [eq_bot_iff]
        exact h
      obtain ⟨n, u, rfl⟩ := H' r hr₂ (le_maximal_ideal hI' hr₁)
      use n
      rwa [← I.unit_mul_mem_iff_mem u.is_unit, mul_comm]
      
    apply le_antisymm
    · rw [hx, Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
      exact Nat.find_spec this
      
#align exists_maximal_ideal_pow_eq_of_principal exists_maximal_ideal_pow_eq_of_principal

theorem maximal_ideal_is_principal_of_is_dedekind_domain [LocalRing R] [IsDomain R] [IsDedekindDomain R] :
    (maximalIdeal R).IsPrincipal := by
  classical by_cases ne_bot:maximal_ideal R = ⊥
    obtain ⟨a, ha₁, ha₂⟩ : ∃ a ∈ maximal_ideal R, a ≠ (0 : R)
    have hle : Ideal.span {a} ≤ maximal_ideal R
    have : (Ideal.span {a}).radical = maximal_ideal R
    have : ∃ n, maximal_ideal R ^ n ≤ Ideal.span {a}
    cases hn : Nat.find this
    obtain ⟨b, hb₁, hb₂⟩ : ∃ b ∈ maximal_ideal R ^ n, ¬b ∈ Ideal.span {a}
    have hb₃ : ∀ m ∈ maximal_ideal R, ∃ k : R, k * a = b * m
    have hb₄ : b ≠ 0
    let K := FractionRing R
    let M := Submodule.map (Algebra.ofId R K).toLinearMap (maximal_ideal R)
    by_cases hx:∀ y ∈ M, x * y ∈ M
    · have : (M.map (DistribMulAction.toLinearMap R K x)).comap (Algebra.ofId R K).toLinearMap = ⊤ := by
        by_contra h
        apply hx
        rintro m' ⟨m, hm, rfl : algebraMap R K m = m'⟩
        obtain ⟨k, hk⟩ := hb₃ m hm
        have hk' : x * algebraMap R K m = algebraMap R K k := by
          rw [← mul_div_right_comm, ← map_mul, ← hk, map_mul, mul_div_cancel _ ha₃]
        exact ⟨k, le_maximal_ideal h ⟨_, ⟨_, hm, rfl⟩, hk'⟩, hk'.symm⟩
      obtain ⟨y, hy₁, hy₂⟩ : ∃ y ∈ maximal_ideal R, b * y = a := by
        rw [Ideal.eq_top_iff_one, Submodule.mem_comap] at this
        obtain ⟨_, ⟨y, hy, rfl⟩, hy' : x * algebraMap R K y = algebraMap R K 1⟩ := this
        rw [map_one, ← mul_div_right_comm, div_eq_one_iff_eq ha₃, ← map_mul] at hy'
        exact ⟨y, hy, IsFractionRing.injective R K hy'⟩
      refine' ⟨⟨y, _⟩⟩
      apply le_antisymm
      · intro m hm
        obtain ⟨k, hk⟩ := hb₃ m hm
        rw [← hy₂, mul_comm, mul_assoc] at hk
        rw [← mul_left_cancel₀ hb₄ hk, mul_comm]
        exact ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
        
      · rwa [Submodule.span_le, Set.singleton_subset_iff]
        
      
#align maximal_ideal_is_principal_of_is_dedekind_domain maximal_ideal_is_principal_of_is_dedekind_domain

/- ./././Mathport/Syntax/Translate/Basic.lean:610:2: warning: expanding binder collection (I «expr ≠ » «expr⊥»()) -/
theorem DiscreteValuationRing.tfae [IsNoetherianRing R] [LocalRing R] [IsDomain R] (h : ¬IsField R) :
    Tfae
      [DiscreteValuationRing R, ValuationRing R, IsDedekindDomain R,
        IsIntegrallyClosed R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime, (maximalIdeal R).IsPrincipal,
        FiniteDimensional.finrank (ResidueField R) (CotangentSpace R) = 1,
        ∀ (I) (_ : I ≠ ⊥), ∃ n : ℕ, I = maximalIdeal R ^ n] :=
  by
  have ne_bot := Ring.ne_bot_of_is_maximal_of_not_is_field (maximal_ideal.is_maximal R) h
  classical rw [finrank_eq_one_iff']
    · intro
      infer_instance
      
    · intro
      haveI := IsBezout.toGcdDomain R
      haveI : UniqueFactorizationMonoid R := ufmOfGcdOfWfDvdMonoid
      apply DiscreteValuationRing.ofUfdOfUniqueIrreducible
      · obtain ⟨x, hx₁, hx₂⟩ := Ring.exists_not_is_unit_of_not_is_field h
        obtain ⟨p, hp₁, hp₂⟩ := WfDvdMonoid.exists_irreducible_factor hx₂ hx₁
        exact ⟨p, hp₁⟩
        
      · exact ValuationRing.unique_irreducible
        
      
    · intro H
      exact ⟨inferInstance, ((DiscreteValuationRing.iff_pid_with_one_nonzero_prime R).mp H).2⟩
      
    · rintro ⟨h₁, h₂⟩
      exact
        ⟨inferInstance, fun I hI hI' =>
          ExistsUnique.unique h₂ ⟨ne_bot, inferInstance⟩ ⟨hI, hI'⟩ ▸ maximal_ideal.is_maximal R, h₁⟩
      
    · intro h
      exact maximal_ideal_is_principal_of_is_dedekind_domain R
      
    · rintro ⟨x, hx⟩
      have : x ∈ maximal_ideal R := by
        rw [hx]
        exact Submodule.subset_span (Set.mem_singleton x)
      let x' : maximal_ideal R := ⟨x, this⟩
      use Submodule.Quotient.mk x'
      constructor
      · intro e
        rw [Submodule.Quotient.mk_eq_zero] at e
        apply Ring.ne_bot_of_is_maximal_of_not_is_field (maximal_ideal.is_maximal R) h
        apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximal_ideal R)
        · exact ⟨{x}, (Finset.coe_singleton x).symm ▸ hx.symm⟩
          
        · conv_lhs => rw [hx]
          rw [Submodule.mem_smul_top_iff] at e
          rwa [Submodule.span_le, Set.singleton_subset_iff]
          
        · rw [LocalRing.jacobson_eq_maximal_ideal (⊥ : Ideal R) bot_ne_top]
          exact le_refl _
          
        
      · refine' fun w => (Quotient.inductionOn' w) fun y => _
        obtain ⟨y, hy⟩ := y
        rw [hx, Submodule.mem_span_singleton] at hy
        obtain ⟨a, rfl⟩ := hy
        exact ⟨Ideal.Quotient.mk _ a, rfl⟩
        
      
    · rintro ⟨x, hx, hx'⟩
      induction x using Quotient.inductionOn'
      use x
      apply le_antisymm
      swap
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact x.prop
        
      have h₁ : (Ideal.span {x} : Ideal R) ⊔ maximal_ideal R ≤ Ideal.span {x} ⊔ maximal_ideal R • maximal_ideal R := by
        refine' sup_le le_sup_left _
        rintro m hm
        obtain ⟨c, hc⟩ := hx' (Submodule.Quotient.mk ⟨m, hm⟩)
        induction c using Quotient.inductionOn'
        rw [← sub_sub_cancel (c * x) m]
        apply sub_mem _ _
        · infer_instance
          
        · refine' Ideal.mem_sup_left (ideal.mem_span_singleton'.mpr ⟨c, rfl⟩)
          
        · have := (Submodule.Quotient.eq _).mp hc
          rw [Submodule.mem_smul_top_iff] at this
          exact Ideal.mem_sup_right this
          
      have h₂ : maximal_ideal R ≤ (⊥ : Ideal R).jacobson := by
        rw [LocalRing.jacobson_eq_maximal_ideal]
        exacts[le_refl _, bot_ne_top]
      have := Submodule.smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson (IsNoetherian.noetherian _) h₂ h₁
      rw [Submodule.bot_smul, sup_bot_eq] at this
      rw [← sup_eq_left, eq_comm]
      exact le_sup_left.antisymm (h₁.trans <| le_of_eq this)
      
    · exact exists_maximal_ideal_pow_eq_of_principal R h
      
    · rw [ValuationRing.iff_ideal_total]
      intro H
      constructor
      intro I J
      by_cases hI:I = ⊥
      · subst hI
        left
        exact bot_le
        
      by_cases hJ:J = ⊥
      · subst hJ
        right
        exact bot_le
        
      obtain ⟨n, rfl⟩ := H I hI
      obtain ⟨m, rfl⟩ := H J hJ
      cases' le_total m n with h' h'
      · left
        exact Ideal.pow_le_pow h'
        
      · right
        exact Ideal.pow_le_pow h'
        
      
#align discrete_valuation_ring.tfae DiscreteValuationRing.tfae

