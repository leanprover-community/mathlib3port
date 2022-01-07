import Mathbin.RingTheory.Polynomial.Cyclotomic.Basic
import Mathbin.NumberTheory.NumberField
import Mathbin.Algebra.CharP.Algebra

/-!
# Cyclotomic extensions

Let `A` and `B` be commutative rings with `algebra A B`. For `S : set ℕ+`, we define a class
`is_cyclotomic_extension S A B` expressing the fact that `B` is obtained from `A` by adding `n`-th
primitive roots of unity, for all `n ∈ S`.

## Main definition

* `is_cyclotomic_extension S A B` : means that `B` is obtained from `A` by adding `n`-th primitive
roots of unity, for all `n ∈ S`.

## Main results

* `is_cyclotomic_extension.trans`: if `is_cyclotomic_extension S A B` and
  `is_cyclotomic_extension T B C`, then `is_cyclotomic_extension (S ∪ T) A C`.
* `is_cyclotomic_extension.union_right` : given `is_cyclotomic_extension (S ∪ T) A B`, then
  `is_cyclotomic_extension T (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }) B`.
* `is_cyclotomic_extension.union_right` : given `is_cyclotomic_extension T A B` and `S ⊆ T`, then
  `is_cyclotomic_extension S A (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 })`.
* `is_cyclotomic_extension.finite` : if `S` is finite and `is_cyclotomic_extension S A B`, then
  `B` is a finite `A`-algebra.
* `is_cyclotomic_extension.number_field` : a finite cyclotomic extension of a number field is a
  number field.

## Implementation details

Our definition of `is_cyclotomic_extension` is very general, to allow rings of any characteristic
and infinite extensions, but it will mainly be used in the case `S = {n}` with `(n : A) ≠ 0` (and
for integral domains).
All results are in the `is_cyclotomic_extension` namespace.
Note that some results, `is_cyclotomic_extension.trans`, `is_cyclotomic_extension.finite` and
`is_cyclotomic_extension.number_field` are lemmas, but they can be made local instances.

-/


open Polynomial Algebra FiniteDimensional Module Set

open_locale BigOperators

universe u v w z

variable (n : ℕ+) (S T : Set ℕ+) (A : Type u) (B : Type v) (K : Type w) (L : Type z)

variable [CommRingₓ A] [CommRingₓ B] [Algebra A B]

variable [Field K] [Field L] [Algebra K L]

noncomputable section

/-- Given an `A`-algebra `B` and `S : set ℕ+`, we define `is_cyclotomic_extension S A B` requiring
that `cyclotomic a A` has a root in `B` for all `a ∈ S` and that `B` is generated over `A` by the
roots of `X ^ n - 1`. -/
@[mk_iff]
class IsCyclotomicExtension : Prop where
  exists_root {a : ℕ+} (ha : a ∈ S) : ∃ r : B, aeval r (cyclotomic a A) = 0
  adjoin_roots : ∀ x : B, x ∈ adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }

namespace IsCyclotomicExtension

section Basic

/-- A reformulation of `is_cyclotomic_extension` that uses `⊤`. -/
theorem iff_adjoin_eq_top :
    IsCyclotomicExtension S A B ↔
      (∀ a : ℕ+, a ∈ S → ∃ r : B, aeval r (cyclotomic a A) = 0) ∧
        adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 } = ⊤ :=
  ⟨fun h => ⟨h.exists_root, Algebra.eq_top_iff.2 h.adjoin_roots⟩, fun h => ⟨h.1, Algebra.eq_top_iff.1 h.2⟩⟩

/-- A reformulation of `is_cyclotomic_extension` in the case `S` is a singleton. -/
theorem iff_singleton :
    IsCyclotomicExtension {n} A B ↔
      (∃ r : B, aeval r (cyclotomic n A) = 0) ∧ ∀ x, x ∈ adjoin A { b : B | b ^ (n : ℕ) = 1 } :=
  by
  simp [is_cyclotomic_extension_iff]

/-- If `is_cyclotomic_extension ∅ A B`, then `A = B`. -/
theorem Empty [h : IsCyclotomicExtension ∅ A B] : (⊥ : Subalgebra A B) = ⊤ := by
  simpa [Algebra.eq_top_iff, is_cyclotomic_extension_iff] using h

/-- Transitivity of cyclotomic extensions. -/
theorem trans (C : Type w) [CommRingₓ C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [hS : IsCyclotomicExtension S A B] [hT : IsCyclotomicExtension T B C] : IsCyclotomicExtension (S ∪ T) A C := by
  refine' ⟨fun n hn => _, fun x => _⟩
  · cases hn
    · obtain ⟨b, hb⟩ := ((is_cyclotomic_extension_iff _ _ _).1 hS).1 hn
      refine' ⟨algebraMap B C b, _⟩
      replace hb := congr_argₓ (algebraMap B C) hb
      rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic, RingHom.map_zero, ← eval₂_at_apply, eval₂_eq_eval_map,
        map_cyclotomic] at hb
      rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
      
    · obtain ⟨c, hc⟩ := ((is_cyclotomic_extension_iff _ _ _).1 hT).1 hn
      refine' ⟨c, _⟩
      rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic] at hc
      rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
      
    
  · refine'
      adjoin_induction (((is_cyclotomic_extension_iff _ _ _).1 hT).2 x)
        (fun c ⟨n, hn⟩ => subset_adjoin ⟨n, Or.inr hn.1, hn.2⟩) (fun b => _)
        (fun x y hx hy => Subalgebra.add_mem _ hx hy) fun x y hx hy => Subalgebra.mul_mem _ hx hy
    · let f := IsScalarTower.toAlgHom A B C
      have hb : f b ∈ (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }).map f :=
        ⟨b, ((is_cyclotomic_extension_iff _ _ _).1 hS).2 b, rfl⟩
      rw [IsScalarTower.to_alg_hom_apply, ← adjoin_image] at hb
      refine' adjoin_mono (fun y hy => _) hb
      obtain ⟨b₁, ⟨⟨n, hn⟩, h₁⟩⟩ := hy
      exact
        ⟨n,
          ⟨mem_union_left T hn.1, by
            rw [← h₁, ← AlgHom.map_pow, hn.2, AlgHom.map_one]⟩⟩
      
    

/-- If `B` is a cyclotomic extension of `A` given by roots of unity of order in `S ∪ T`, then `B`
is a cyclotomic extension of `adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 } ` given by
roots of unity of order in `T`. -/
theorem union_right [h : IsCyclotomicExtension (S ∪ T) A B] :
    IsCyclotomicExtension T (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }) B := by
  have :
    { b : B | ∃ n : ℕ+, n ∈ S ∪ T ∧ b ^ (n : ℕ) = 1 } =
      { b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1 } ∪ { b : B | ∃ n : ℕ+, n ∈ T ∧ b ^ (n : ℕ) = 1 } :=
    by
    refine' le_antisymmₓ (fun x hx => _) fun x hx => _
    · rcases hx with ⟨n, hn₁ | hn₂, hnpow⟩
      · left
        exact ⟨n, hn₁, hnpow⟩
        
      · right
        exact ⟨n, hn₂, hnpow⟩
        
      
    · rcases hx with (⟨n, hn⟩ | ⟨n, hn⟩)
      · exact ⟨n, Or.inl hn.1, hn.2⟩
        
      · exact ⟨n, Or.inr hn.1, hn.2⟩
        
      
  refine' ⟨fun n hn => _, fun b => _⟩
  · obtain ⟨b, hb⟩ := ((is_cyclotomic_extension_iff _ _ _).1 h).1 (mem_union_right S hn)
    refine' ⟨b, _⟩
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic] at hb
    rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    
  · replace h := ((is_cyclotomic_extension_iff _ _ _).1 h).2 b
    rwa [this, adjoin_union_eq_adjoin_adjoin, Subalgebra.mem_restrict_scalars] at h
    

/-- If `B` is a cyclotomic extension of `A` given by roots of unity of order in `T` and `S ⊆ T`,
then `adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }` is a cyclotomic extension of `B`
given by roots of unity of order in `S`. -/
theorem union_left [h : IsCyclotomicExtension T A B] (hS : S ⊆ T) :
    IsCyclotomicExtension S A (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }) := by
  refine' ⟨fun n hn => _, fun b => _⟩
  · obtain ⟨b, hb⟩ := ((is_cyclotomic_extension_iff _ _ _).1 h).1 (hS hn)
    refine' ⟨⟨b, subset_adjoin ⟨n, hn, _⟩⟩, _⟩
    · rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ← is_root.def] at hb
      suffices (X ^ (n : ℕ) - 1).IsRoot b by
        simpa [sub_eq_zero] using this
      exact hb.dvd (cyclotomic.dvd_X_pow_sub_one _ _)
      
    rwa [← Subalgebra.coe_eq_zero, aeval_subalgebra_coe, Subtype.coe_mk]
    
  · convert mem_top
    rw [← adjoin_adjoin_coe_preimage]
    simp
    norm_cast
    

end Basic

section Fintype

theorem finite_of_singleton [IsDomain B] [h : IsCyclotomicExtension {n} A B] : finite A B := by
  classical
  rw [Module.finite_def, ← top_to_submodule, ← ((iff_adjoin_eq_top _ _ _).1 h).2]
  refine' fg_adjoin_of_finite _ fun b hb => _
  · simp only [mem_singleton_iff, exists_eq_left]
    have : { b : B | b ^ (n : ℕ) = 1 } = (nth_roots n (1 : B)).toFinset :=
      Set.ext fun x =>
        ⟨fun h => by
          simpa using h, fun h => by
          simpa using h⟩
    rw [this]
    exact (nth_roots (↑n) 1).toFinset.finite_to_set
    
  · simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq] at hb
    refine'
      ⟨X ^ (n : ℕ) - 1,
        ⟨monic_X_pow_sub_C _ n.pos.ne.symm, by
          simp [hb]⟩⟩
    

/-- If `S` is finite and `is_cyclotomic_extension S A B`, then `B` is a finite `A`-algebra. -/
theorem finite [IsDomain B] [h₁ : Fintype S] [h₂ : IsCyclotomicExtension S A B] : finite A B := by
  revert h₂ A B
  refine' Set.Finite.induction_on (Set.Finite.intro h₁) (fun A B => _) fun n S hn hS H A B => _
  · intros _ _ _ _ _
    refine' Module.finite_def.2 ⟨({1} : Finset B), _⟩
    simp [← top_to_submodule, ← Empty, to_submodule_bot]
    
  · intros _ _ _ _ h
    have : IsCyclotomicExtension S A (adjoin A { b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1 }) :=
      union_left _ (insert n S) _ _ (subset_insert n S)
    have := H A (adjoin A { b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1 })
    have : finite (adjoin A { b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1 }) B := by
      rw [← union_singleton] at h
      let this' := @union_right S {n} A B _ _ _ h
      exact finite_of_singleton n _ _
    exact finite.trans (adjoin A { b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1 }) _
    

/-- A cyclotomic finite extension of a number field is a number field. -/
theorem NumberField [h : NumberField K] [Fintype S] [IsCyclotomicExtension S K L] : NumberField L :=
  { to_char_zero := char_zero_of_injective_algebra_map (algebraMap K L).Injective,
    to_finite_dimensional :=
      @finite.trans _ K L _ _ _ _ (@algebraRat L _ (char_zero_of_injective_algebra_map (algebraMap K L).Injective)) _ _
        h.to_finite_dimensional (finite S K L) }

end Fintype

end IsCyclotomicExtension

