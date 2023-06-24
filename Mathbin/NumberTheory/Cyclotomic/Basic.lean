/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

! This file was ported from Lean 3 source module number_theory.cyclotomic.basic
! leanprover-community/mathlib commit 5d0c76894ada7940957143163d7b921345474cbc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Polynomial.Cyclotomic.Roots
import Mathbin.NumberTheory.NumberField.Basic
import Mathbin.FieldTheory.Galois

/-!
# Cyclotomic extensions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Let `A` and `B` be commutative rings with `algebra A B`. For `S : set ℕ+`, we define a class
`is_cyclotomic_extension S A B` expressing the fact that `B` is obtained from `A` by adding `n`-th
primitive roots of unity, for all `n ∈ S`.

## Main definitions

* `is_cyclotomic_extension S A B` : means that `B` is obtained from `A` by adding `n`-th primitive
  roots of unity, for all `n ∈ S`.
* `cyclotomic_field`: given `n : ℕ+` and a field `K`, we define `cyclotomic n K` as the splitting
  field of `cyclotomic n K`. If `n` is nonzero in `K`, it has the instance
  `is_cyclotomic_extension {n} K (cyclotomic_field n K)`.
* `cyclotomic_ring` : if `A` is a domain with fraction field `K` and `n : ℕ+`, we define
  `cyclotomic_ring n A K` as the `A`-subalgebra of `cyclotomic_field n K` generated by the roots of
  `X ^ n - 1`. If `n` is nonzero in `A`, it has the instance
  `is_cyclotomic_extension {n} A (cyclotomic_ring n A K)`.

## Main results

* `is_cyclotomic_extension.trans` : if `is_cyclotomic_extension S A B` and
  `is_cyclotomic_extension T B C`, then `is_cyclotomic_extension (S ∪ T) A C` if
  `function.injective (algebra_map B C)`.
* `is_cyclotomic_extension.union_right` : given `is_cyclotomic_extension (S ∪ T) A B`, then
  `is_cyclotomic_extension T (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }) B`.
* `is_cyclotomic_extension.union_right` : given `is_cyclotomic_extension T A B` and `S ⊆ T`, then
  `is_cyclotomic_extension S A (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 })`.
* `is_cyclotomic_extension.finite` : if `S` is finite and `is_cyclotomic_extension S A B`, then
  `B` is a finite `A`-algebra.
* `is_cyclotomic_extension.number_field` : a finite cyclotomic extension of a number field is a
  number field.
* `is_cyclotomic_extension.splitting_field_X_pow_sub_one` : if `is_cyclotomic_extension {n} K L`,
  then `L` is the splitting field of `X ^ n - 1`.
* `is_cyclotomic_extension.splitting_field_cyclotomic` : if `is_cyclotomic_extension {n} K L`,
  then `L` is the splitting field of `cyclotomic n K`.

## Implementation details

Our definition of `is_cyclotomic_extension` is very general, to allow rings of any characteristic
and infinite extensions, but it will mainly be used in the case `S = {n}` and for integral domains.
All results are in the `is_cyclotomic_extension` namespace.
Note that some results, for example `is_cyclotomic_extension.trans`,
`is_cyclotomic_extension.finite`, `is_cyclotomic_extension.number_field`,
`is_cyclotomic_extension.finite_dimensional`, `is_cyclotomic_extension.is_galois` and
`cyclotomic_field.algebra_base` are lemmas, but they can be made local instances. Some of them are
included in the `cyclotomic` locale.

-/


open Polynomial Algebra FiniteDimensional Set

open scoped BigOperators

universe u v w z

variable (n : ℕ+) (S T : Set ℕ+) (A : Type u) (B : Type v) (K : Type w) (L : Type z)

variable [CommRing A] [CommRing B] [Algebra A B]

variable [Field K] [Field L] [Algebra K L]

noncomputable section

#print IsCyclotomicExtension /-
/-- Given an `A`-algebra `B` and `S : set ℕ+`, we define `is_cyclotomic_extension S A B` requiring
that there is a `n`-th primitive root of unity in `B` for all `n ∈ S` and that `B` is generated
over `A` by the roots of `X ^ n - 1`. -/
@[mk_iff]
class IsCyclotomicExtension : Prop where
  exists_prim_root {n : ℕ+} (ha : n ∈ S) : ∃ r : B, IsPrimitiveRoot r n
  adjoin_roots : ∀ x : B, x ∈ adjoin A {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1}
#align is_cyclotomic_extension IsCyclotomicExtension
-/

namespace IsCyclotomicExtension

section Basic

#print IsCyclotomicExtension.iff_adjoin_eq_top /-
/-- A reformulation of `is_cyclotomic_extension` that uses `⊤`. -/
theorem iff_adjoin_eq_top :
    IsCyclotomicExtension S A B ↔
      (∀ n : ℕ+, n ∈ S → ∃ r : B, IsPrimitiveRoot r n) ∧
        adjoin A {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1} = ⊤ :=
  ⟨fun h => ⟨fun _ => h.exists_prim_root, Algebra.eq_top_iff.2 h.adjoin_roots⟩, fun h =>
    ⟨h.1, Algebra.eq_top_iff.1 h.2⟩⟩
#align is_cyclotomic_extension.iff_adjoin_eq_top IsCyclotomicExtension.iff_adjoin_eq_top
-/

#print IsCyclotomicExtension.iff_singleton /-
/-- A reformulation of `is_cyclotomic_extension` in the case `S` is a singleton. -/
theorem iff_singleton :
    IsCyclotomicExtension {n} A B ↔
      (∃ r : B, IsPrimitiveRoot r n) ∧ ∀ x, x ∈ adjoin A {b : B | b ^ (n : ℕ) = 1} :=
  by simp [isCyclotomicExtension_iff]
#align is_cyclotomic_extension.iff_singleton IsCyclotomicExtension.iff_singleton
-/

#print IsCyclotomicExtension.empty /-
/-- If `is_cyclotomic_extension ∅ A B`, then the image of `A` in `B` equals `B`. -/
theorem empty [h : IsCyclotomicExtension ∅ A B] : (⊥ : Subalgebra A B) = ⊤ := by
  simpa [Algebra.eq_top_iff, isCyclotomicExtension_iff] using h
#align is_cyclotomic_extension.empty IsCyclotomicExtension.empty
-/

#print IsCyclotomicExtension.singleton_one /-
/-- If `is_cyclotomic_extension {1} A B`, then the image of `A` in `B` equals `B`. -/
theorem singleton_one [h : IsCyclotomicExtension {1} A B] : (⊥ : Subalgebra A B) = ⊤ :=
  Algebra.eq_top_iff.2 fun x => by
    simpa [adjoin_singleton_one] using ((isCyclotomicExtension_iff _ _ _).1 h).2 x
#align is_cyclotomic_extension.singleton_one IsCyclotomicExtension.singleton_one
-/

variable {A B}

#print IsCyclotomicExtension.singleton_zero_of_bot_eq_top /-
/-- If `(⊥ : subalgebra A B) = ⊤`, then `is_cyclotomic_extension ∅ A B`. -/
theorem singleton_zero_of_bot_eq_top (h : (⊥ : Subalgebra A B) = ⊤) : IsCyclotomicExtension ∅ A B :=
  by
  refine'
    (iff_adjoin_eq_top _ _ _).2 ⟨fun s hs => by simpa using hs, _root_.eq_top_iff.2 fun x hx => _⟩
  rw [← h] at hx 
  simpa using hx
#align is_cyclotomic_extension.singleton_zero_of_bot_eq_top IsCyclotomicExtension.singleton_zero_of_bot_eq_top
-/

variable (A B)

#print IsCyclotomicExtension.trans /-
/-- Transitivity of cyclotomic extensions. -/
theorem trans (C : Type w) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [hS : IsCyclotomicExtension S A B] [hT : IsCyclotomicExtension T B C]
    (h : Function.Injective (algebraMap B C)) : IsCyclotomicExtension (S ∪ T) A C :=
  by
  refine' ⟨fun n hn => _, fun x => _⟩
  · cases hn
    · obtain ⟨b, hb⟩ := ((isCyclotomicExtension_iff _ _ _).1 hS).1 hn
      refine' ⟨algebraMap B C b, _⟩
      exact hb.map_of_injective h
    · exact ((isCyclotomicExtension_iff _ _ _).1 hT).1 hn
  · refine'
      adjoin_induction (((isCyclotomicExtension_iff _ _ _).1 hT).2 x)
        (fun c ⟨n, hn⟩ => subset_adjoin ⟨n, Or.inr hn.1, hn.2⟩) (fun b => _)
        (fun x y hx hy => Subalgebra.add_mem _ hx hy) fun x y hx hy => Subalgebra.mul_mem _ hx hy
    · let f := IsScalarTower.toAlgHom A B C
      have hb : f b ∈ (adjoin A {b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1}).map f :=
        ⟨b, ((isCyclotomicExtension_iff _ _ _).1 hS).2 b, rfl⟩
      rw [IsScalarTower.toAlgHom_apply, ← adjoin_image] at hb 
      refine' adjoin_mono (fun y hy => _) hb
      obtain ⟨b₁, ⟨⟨n, hn⟩, h₁⟩⟩ := hy
      exact ⟨n, ⟨mem_union_left T hn.1, by rw [← h₁, ← AlgHom.map_pow, hn.2, AlgHom.map_one]⟩⟩
#align is_cyclotomic_extension.trans IsCyclotomicExtension.trans
-/

#print IsCyclotomicExtension.subsingleton_iff /-
@[nontriviality]
theorem subsingleton_iff [Subsingleton B] : IsCyclotomicExtension S A B ↔ S = { } ∨ S = {1} :=
  by
  constructor
  · rintro ⟨hprim, -⟩
    rw [← subset_singleton_iff_eq]
    intro t ht
    obtain ⟨ζ, hζ⟩ := hprim ht
    rw [mem_singleton_iff, ← PNat.coe_eq_one_iff]
    exact_mod_cast hζ.unique (IsPrimitiveRoot.of_subsingleton ζ)
  · rintro (rfl | rfl)
    · refine' ⟨fun _ h => h.elim, fun x => by convert (mem_top : x ∈ ⊤)⟩
    · rw [iff_singleton]
      refine' ⟨⟨0, IsPrimitiveRoot.of_subsingleton 0⟩, fun x => by convert (mem_top : x ∈ ⊤)⟩
#align is_cyclotomic_extension.subsingleton_iff IsCyclotomicExtension.subsingleton_iff
-/

#print IsCyclotomicExtension.union_right /-
/-- If `B` is a cyclotomic extension of `A` given by roots of unity of order in `S ∪ T`, then `B`
is a cyclotomic extension of `adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 } ` given by
roots of unity of order in `T`. -/
theorem union_right [h : IsCyclotomicExtension (S ∪ T) A B] :
    IsCyclotomicExtension T (adjoin A {b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1}) B :=
  by
  have :
    {b : B | ∃ n : ℕ+, n ∈ S ∪ T ∧ b ^ (n : ℕ) = 1} =
      {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1} ∪ {b : B | ∃ n : ℕ+, n ∈ T ∧ b ^ (n : ℕ) = 1} :=
    by
    refine' le_antisymm (fun x hx => _) fun x hx => _
    · rcases hx with ⟨n, hn₁ | hn₂, hnpow⟩
      · left; exact ⟨n, hn₁, hnpow⟩
      · right; exact ⟨n, hn₂, hnpow⟩
    · rcases hx with (⟨n, hn⟩ | ⟨n, hn⟩)
      · exact ⟨n, Or.inl hn.1, hn.2⟩
      · exact ⟨n, Or.inr hn.1, hn.2⟩
  refine' ⟨fun n hn => ((isCyclotomicExtension_iff _ _ _).1 h).1 (mem_union_right S hn), fun b => _⟩
  replace h := ((isCyclotomicExtension_iff _ _ _).1 h).2 b
  rwa [this, adjoin_union_eq_adjoin_adjoin, Subalgebra.mem_restrictScalars] at h 
#align is_cyclotomic_extension.union_right IsCyclotomicExtension.union_right
-/

#print IsCyclotomicExtension.union_left /-
/-- If `B` is a cyclotomic extension of `A` given by roots of unity of order in `T` and `S ⊆ T`,
then `adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }` is a cyclotomic extension of `B`
given by roots of unity of order in `S`. -/
theorem union_left [h : IsCyclotomicExtension T A B] (hS : S ⊆ T) :
    IsCyclotomicExtension S A (adjoin A {b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1}) :=
  by
  refine' ⟨fun n hn => _, fun b => _⟩
  · obtain ⟨b, hb⟩ := ((isCyclotomicExtension_iff _ _ _).1 h).1 (hS hn)
    refine' ⟨⟨b, subset_adjoin ⟨n, hn, hb.pow_eq_one⟩⟩, _⟩
    rwa [← IsPrimitiveRoot.coe_submonoidClass_iff, Subtype.coe_mk]
  · convert mem_top
    rw [← adjoin_adjoin_coe_preimage, preimage_set_of_eq]
    norm_cast
#align is_cyclotomic_extension.union_left IsCyclotomicExtension.union_left
-/

variable {n S}

#print IsCyclotomicExtension.of_union_of_dvd /-
/-- If `∀ s ∈ S, n ∣ s` and `S` is not empty, then `is_cyclotomic_extension S A B` implies
`is_cyclotomic_extension (S ∪ {n}) A B`. -/
theorem of_union_of_dvd (h : ∀ s ∈ S, n ∣ s) (hS : S.Nonempty) [H : IsCyclotomicExtension S A B] :
    IsCyclotomicExtension (S ∪ {n}) A B :=
  by
  refine' (iff_adjoin_eq_top _ _ _).2 ⟨fun s hs => _, _⟩
  · rw [mem_union, mem_singleton_iff] at hs 
    obtain hs | rfl := hs
    · exact H.exists_prim_root hs
    · obtain ⟨m, hm⟩ := hS
      obtain ⟨x, rfl⟩ := h m hm
      obtain ⟨ζ, hζ⟩ := H.exists_prim_root hm
      refine' ⟨ζ ^ (x : ℕ), _⟩
      convert hζ.pow_of_dvd x.ne_zero (dvd_mul_left (x : ℕ) s)
      simp only [PNat.mul_coe, Nat.mul_div_left, PNat.pos]
  · refine' _root_.eq_top_iff.2 _
    rw [← ((iff_adjoin_eq_top S A B).1 H).2]
    refine' adjoin_mono fun x hx => _
    simp only [union_singleton, mem_insert_iff, mem_set_of_eq] at hx ⊢
    obtain ⟨m, hm⟩ := hx
    exact ⟨m, ⟨Or.inr hm.1, hm.2⟩⟩
#align is_cyclotomic_extension.of_union_of_dvd IsCyclotomicExtension.of_union_of_dvd
-/

#print IsCyclotomicExtension.iff_union_of_dvd /-
/-- If `∀ s ∈ S, n ∣ s` and `S` is not empty, then `is_cyclotomic_extension S A B` if and only if
`is_cyclotomic_extension (S ∪ {n}) A B`. -/
theorem iff_union_of_dvd (h : ∀ s ∈ S, n ∣ s) (hS : S.Nonempty) :
    IsCyclotomicExtension S A B ↔ IsCyclotomicExtension (S ∪ {n}) A B :=
  by
  refine'
    ⟨fun H => of_union_of_dvd A B h hS, fun H => (iff_adjoin_eq_top _ _ _).2 ⟨fun s hs => _, _⟩⟩
  · exact H.exists_prim_root (subset_union_left _ _ hs)
  · rw [_root_.eq_top_iff, ← ((iff_adjoin_eq_top _ A B).1 H).2]
    refine' adjoin_mono fun x hx => _
    simp only [union_singleton, mem_insert_iff, mem_set_of_eq] at hx ⊢
    obtain ⟨m, rfl | hm, hxpow⟩ := hx
    · obtain ⟨y, hy⟩ := hS
      refine' ⟨y, ⟨hy, _⟩⟩
      obtain ⟨z, rfl⟩ := h y hy
      simp only [PNat.mul_coe, pow_mul, hxpow, one_pow]
    · exact ⟨m, ⟨hm, hxpow⟩⟩
#align is_cyclotomic_extension.iff_union_of_dvd IsCyclotomicExtension.iff_union_of_dvd
-/

variable (n S)

#print IsCyclotomicExtension.iff_union_singleton_one /-
/-- `is_cyclotomic_extension S A B` is equivalent to `is_cyclotomic_extension (S ∪ {1}) A B`. -/
theorem iff_union_singleton_one :
    IsCyclotomicExtension S A B ↔ IsCyclotomicExtension (S ∪ {1}) A B :=
  by
  obtain hS | rfl := S.eq_empty_or_nonempty.symm
  · exact iff_union_of_dvd _ _ (fun s hs => one_dvd _) hS
  rw [empty_union]
  refine' ⟨fun H => _, fun H => _⟩
  · refine' (iff_adjoin_eq_top _ _ _).2 ⟨fun s hs => ⟨1, by simp [mem_singleton_iff.1 hs]⟩, _⟩
    simp [adjoin_singleton_one, @Empty _ _ _ _ _ H]
  · refine' (iff_adjoin_eq_top _ _ _).2 ⟨fun s hs => (not_mem_empty s hs).elim, _⟩
    simp [@singleton_one A B _ _ _ H]
#align is_cyclotomic_extension.iff_union_singleton_one IsCyclotomicExtension.iff_union_singleton_one
-/

variable {A B}

#print IsCyclotomicExtension.singleton_one_of_bot_eq_top /-
/-- If `(⊥ : subalgebra A B) = ⊤`, then `is_cyclotomic_extension {1} A B`. -/
theorem singleton_one_of_bot_eq_top (h : (⊥ : Subalgebra A B) = ⊤) :
    IsCyclotomicExtension {1} A B :=
  by
  convert (iff_union_singleton_one _ _ _).1 (singleton_zero_of_bot_eq_top h)
  simp
#align is_cyclotomic_extension.singleton_one_of_bot_eq_top IsCyclotomicExtension.singleton_one_of_bot_eq_top
-/

#print IsCyclotomicExtension.singleton_one_of_algebraMap_bijective /-
/-- If `function.surjective (algebra_map A B)`, then `is_cyclotomic_extension {1} A B`. -/
theorem singleton_one_of_algebraMap_bijective (h : Function.Surjective (algebraMap A B)) :
    IsCyclotomicExtension {1} A B :=
  singleton_one_of_bot_eq_top (surjective_algebraMap_iff.1 h).symm
#align is_cyclotomic_extension.singleton_one_of_algebra_map_bijective IsCyclotomicExtension.singleton_one_of_algebraMap_bijective
-/

variable (A B)

#print IsCyclotomicExtension.equiv /-
/-- Given `(f : B ≃ₐ[A] C)`, if `is_cyclotomic_extension S A B` then
`is_cyclotomic_extension S A C`. -/
@[protected]
theorem equiv {C : Type _} [CommRing C] [Algebra A C] [h : IsCyclotomicExtension S A B]
    (f : B ≃ₐ[A] C) : IsCyclotomicExtension S A C :=
  by
  letI : Algebra B C := f.to_alg_hom.to_ring_hom.to_algebra
  haveI : IsCyclotomicExtension {1} B C := singleton_one_of_algebra_map_bijective f.surjective
  haveI : IsScalarTower A B C := IsScalarTower.of_ring_hom f.to_alg_hom
  exact (iff_union_singleton_one _ _ _).2 (trans S {1} A B C f.injective)
#align is_cyclotomic_extension.equiv IsCyclotomicExtension.equiv
-/

#print IsCyclotomicExtension.neZero /-
@[protected]
theorem neZero [h : IsCyclotomicExtension {n} A B] [IsDomain B] : NeZero ((n : ℕ) : B) :=
  by
  obtain ⟨⟨r, hr⟩, -⟩ := (iff_singleton n A B).1 h
  exact hr.ne_zero'
#align is_cyclotomic_extension.ne_zero IsCyclotomicExtension.neZero
-/

#print IsCyclotomicExtension.neZero' /-
@[protected]
theorem neZero' [IsCyclotomicExtension {n} A B] [IsDomain B] : NeZero ((n : ℕ) : A) :=
  by
  apply NeZero.nat_of_neZero (algebraMap A B)
  exact NeZero n A B
#align is_cyclotomic_extension.ne_zero' IsCyclotomicExtension.neZero'
-/

end Basic

section Fintype

#print IsCyclotomicExtension.finite_of_singleton /-
theorem finite_of_singleton [IsDomain B] [h : IsCyclotomicExtension {n} A B] : Module.Finite A B :=
  by
  classical
  rw [Module.finite_def, ← top_to_submodule, ← ((iff_adjoin_eq_top _ _ _).1 h).2]
  refine' FG_adjoin_of_finite _ fun b hb => _
  · simp only [mem_singleton_iff, exists_eq_left]
    have : {b : B | b ^ (n : ℕ) = 1} = (nth_roots n (1 : B)).toFinset :=
      Set.ext fun x => ⟨fun h => by simpa using h, fun h => by simpa using h⟩
    rw [this]
    exact (nth_roots (↑n) 1).toFinset.finite_toSet
  · simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq] at hb 
    refine' ⟨X ^ (n : ℕ) - 1, ⟨monic_X_pow_sub_C _ n.pos.ne.symm, by simp [hb]⟩⟩
#align is_cyclotomic_extension.finite_of_singleton IsCyclotomicExtension.finite_of_singleton
-/

#print IsCyclotomicExtension.finite /-
/-- If `S` is finite and `is_cyclotomic_extension S A B`, then `B` is a finite `A`-algebra. -/
@[protected]
theorem finite [IsDomain B] [h₁ : Finite S] [h₂ : IsCyclotomicExtension S A B] :
    Module.Finite A B := by
  cases' nonempty_fintype S with h
  revert h₂ A B
  refine' Set.Finite.induction_on (Set.Finite.intro h) (fun A B => _) fun n S hn hS H A B => _
  · intro _ _ _ _ _
    refine' Module.finite_def.2 ⟨({1} : Finset B), _⟩
    simp [← top_to_submodule, ← Empty, to_submodule_bot]
  · intro _ _ _ _ h
    haveI : IsCyclotomicExtension S A (adjoin A {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1}) :=
      union_left _ (insert n S) _ _ (subset_insert n S)
    haveI := H A (adjoin A {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1})
    have : Module.Finite (adjoin A {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1}) B :=
      by
      rw [← union_singleton] at h 
      letI := @union_right S {n} A B _ _ _ h
      exact finite_of_singleton n _ _
    exact Module.Finite.trans (adjoin A {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1}) _
#align is_cyclotomic_extension.finite IsCyclotomicExtension.finite
-/

#print IsCyclotomicExtension.numberField /-
/-- A cyclotomic finite extension of a number field is a number field. -/
theorem numberField [h : NumberField K] [Finite S] [IsCyclotomicExtension S K L] : NumberField L :=
  { to_charZero := charZero_of_injective_algebraMap (algebraMap K L).Injective
    to_finiteDimensional :=
      by
      haveI := charZero_of_injective_algebraMap (algebraMap K L).Injective
      haveI := Finite S K L
      exact Module.Finite.trans K _ }
#align is_cyclotomic_extension.number_field IsCyclotomicExtension.numberField
-/

scoped[Cyclotomic] attribute [instance] IsCyclotomicExtension.numberField

#print IsCyclotomicExtension.integral /-
/-- A finite cyclotomic extension of an integral noetherian domain is integral -/
theorem integral [IsDomain B] [IsNoetherianRing A] [Finite S] [IsCyclotomicExtension S A B] :
    Algebra.IsIntegral A B :=
  isIntegral_of_noetherian <| isNoetherian_of_fg_of_noetherian' <| (Finite S A B).out
#align is_cyclotomic_extension.integral IsCyclotomicExtension.integral
-/

#print IsCyclotomicExtension.finiteDimensional /-
/-- If `S` is finite and `is_cyclotomic_extension S K A`, then `finite_dimensional K A`. -/
theorem finiteDimensional (C : Type z) [Finite S] [CommRing C] [Algebra K C] [IsDomain C]
    [IsCyclotomicExtension S K C] : FiniteDimensional K C :=
  IsCyclotomicExtension.finite S K C
#align is_cyclotomic_extension.finite_dimensional IsCyclotomicExtension.finiteDimensional
-/

scoped[Cyclotomic] attribute [instance] IsCyclotomicExtension.finiteDimensional

end Fintype

section

variable {A B}

#print IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots /-
theorem adjoin_roots_cyclotomic_eq_adjoin_nth_roots [IsDomain B] {ζ : B} {n : ℕ+}
    (hζ : IsPrimitiveRoot ζ n) :
    adjoin A ((cyclotomic n A).rootSet B) =
      adjoin A {b : B | ∃ a : ℕ+, a ∈ ({n} : Set ℕ+) ∧ b ^ (a : ℕ) = 1} :=
  by
  simp only [mem_singleton_iff, exists_eq_left, map_cyclotomic]
  refine' le_antisymm (adjoin_mono fun x hx => _) (adjoin_le fun x hx => _)
  · rw [mem_root_set'] at hx 
    simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq]
    rw [isRoot_of_unity_iff n.pos]
    refine' ⟨n, Nat.mem_divisors_self n n.ne_zero, _⟩
    rw [is_root.def, ← map_cyclotomic n (algebraMap A B), eval_map, ← aeval_def]
    exact hx.2
  · simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq] at hx 
    obtain ⟨i, hin, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx n.pos
    refine' SetLike.mem_coe.2 (Subalgebra.pow_mem _ (subset_adjoin _) _)
    rw [mem_root_set', map_cyclotomic, aeval_def, ← eval_map, map_cyclotomic, ← is_root]
    refine' ⟨cyclotomic_ne_zero n B, hζ.is_root_cyclotomic n.pos⟩
#align is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots
-/

#print IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic /-
theorem adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic {n : ℕ+} [IsDomain B] {ζ : B}
    (hζ : IsPrimitiveRoot ζ n) : adjoin A ((cyclotomic n A).rootSet B) = adjoin A {ζ} :=
  by
  refine' le_antisymm (adjoin_le fun x hx => _) (adjoin_mono fun x hx => _)
  · suffices hx : x ^ ↑n = 1
    obtain ⟨i, hin, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx n.pos
    exact SetLike.mem_coe.2 (Subalgebra.pow_mem _ (subset_adjoin <| mem_singleton ζ) _)
    rw [isRoot_of_unity_iff n.pos]
    refine' ⟨n, Nat.mem_divisors_self n n.ne_zero, _⟩
    rw [mem_root_set', aeval_def, ← eval_map, map_cyclotomic, ← is_root] at hx 
    exact hx.2
  · simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq] at hx 
    simpa only [hx, mem_root_set', map_cyclotomic, aeval_def, ← eval_map, is_root] using
      And.intro (cyclotomic_ne_zero n B) (hζ.is_root_cyclotomic n.pos)
#align is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic
-/

#print IsCyclotomicExtension.adjoin_primitive_root_eq_top /-
theorem adjoin_primitive_root_eq_top {n : ℕ+} [IsDomain B] [h : IsCyclotomicExtension {n} A B]
    {ζ : B} (hζ : IsPrimitiveRoot ζ n) : adjoin A ({ζ} : Set B) = ⊤ := by
  classical
  rw [← adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic hζ]
  rw [adjoin_roots_cyclotomic_eq_adjoin_nth_roots hζ]
  exact ((iff_adjoin_eq_top {n} A B).mp h).2
#align is_cyclotomic_extension.adjoin_primitive_root_eq_top IsCyclotomicExtension.adjoin_primitive_root_eq_top
-/

variable (A)

#print IsPrimitiveRoot.adjoin_isCyclotomicExtension /-
theorem IsPrimitiveRoot.adjoin_isCyclotomicExtension {ζ : B} {n : ℕ+} (h : IsPrimitiveRoot ζ n) :
    IsCyclotomicExtension {n} A (adjoin A ({ζ} : Set B)) :=
  { exists_prim_root := fun i hi =>
      by
      rw [Set.mem_singleton_iff] at hi 
      refine' ⟨⟨ζ, subset_adjoin <| Set.mem_singleton ζ⟩, _⟩
      rwa [← IsPrimitiveRoot.coe_submonoidClass_iff, Subtype.coe_mk, hi]
    adjoin_roots := fun x =>
      by
      refine'
        adjoin_induction' (fun b hb => _) (fun a => _) (fun b₁ b₂ hb₁ hb₂ => _)
          (fun b₁ b₂ hb₁ hb₂ => _) x
      · rw [Set.mem_singleton_iff] at hb 
        refine' subset_adjoin _
        simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq, hb]
        rw [← Subalgebra.coe_eq_one, Subalgebra.coe_pow, SetLike.coe_mk]
        exact ((IsPrimitiveRoot.iff_def ζ n).1 h).1
      · exact Subalgebra.algebraMap_mem _ _
      · exact Subalgebra.add_mem _ hb₁ hb₂
      · exact Subalgebra.mul_mem _ hb₁ hb₂ }
#align is_primitive_root.adjoin_is_cyclotomic_extension IsPrimitiveRoot.adjoin_isCyclotomicExtension
-/

end

section Field

variable {n S}

#print IsCyclotomicExtension.splits_X_pow_sub_one /-
/-- A cyclotomic extension splits `X ^ n - 1` if `n ∈ S`.-/
theorem splits_X_pow_sub_one [H : IsCyclotomicExtension S K L] (hS : n ∈ S) :
    Splits (algebraMap K L) (X ^ (n : ℕ) - 1) :=
  by
  rw [← splits_id_iff_splits, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow,
    Polynomial.map_X]
  obtain ⟨z, hz⟩ := ((isCyclotomicExtension_iff _ _ _).1 H).1 hS
  exact X_pow_sub_one_splits hz
#align is_cyclotomic_extension.splits_X_pow_sub_one IsCyclotomicExtension.splits_X_pow_sub_one
-/

#print IsCyclotomicExtension.splits_cyclotomic /-
/-- A cyclotomic extension splits `cyclotomic n K` if `n ∈ S` and `ne_zero (n : K)`.-/
theorem splits_cyclotomic [IsCyclotomicExtension S K L] (hS : n ∈ S) :
    Splits (algebraMap K L) (cyclotomic n K) :=
  by
  refine' splits_of_splits_of_dvd _ (X_pow_sub_C_ne_zero n.pos _) (splits_X_pow_sub_one K L hS) _
  use ∏ i : ℕ in (n : ℕ).properDivisors, Polynomial.cyclotomic i K
  rw [(eq_cyclotomic_iff n.pos _).1 rfl, RingHom.map_one]
#align is_cyclotomic_extension.splits_cyclotomic IsCyclotomicExtension.splits_cyclotomic
-/

variable (n S)

section Singleton

variable [IsCyclotomicExtension {n} K L]

#print IsCyclotomicExtension.isSplittingField_X_pow_sub_one /-
/-- If `is_cyclotomic_extension {n} K L`, then `L` is the splitting field of `X ^ n - 1`. -/
theorem isSplittingField_X_pow_sub_one : IsSplittingField K L (X ^ (n : ℕ) - 1) :=
  { Splits := splits_X_pow_sub_one K L (mem_singleton n)
    adjoin_rootSet := by
      rw [← ((iff_adjoin_eq_top {n} K L).1 inferInstance).2]
      congr
      refine' Set.ext fun x => _
      simp only [Polynomial.map_pow, mem_singleton_iff, Multiset.mem_toFinset, exists_eq_left,
        mem_set_of_eq, Polynomial.map_X, Polynomial.map_one, Finset.mem_coe, Polynomial.map_sub]
      simp only [mem_root_set', map_sub, map_pow, aeval_one, aeval_X, sub_eq_zero, map_X,
        and_iff_right_iff_imp, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one]
      exact fun _ => X_pow_sub_C_ne_zero n.pos (1 : L) }
#align is_cyclotomic_extension.splitting_field_X_pow_sub_one IsCyclotomicExtension.isSplittingField_X_pow_sub_one
-/

#print IsCyclotomicExtension.algEquiv /-
/-- Any two `n`-th cyclotomic extensions are isomorphic. -/
def algEquiv (L' : Type _) [Field L'] [Algebra K L'] [IsCyclotomicExtension {n} K L'] :
    L ≃ₐ[K] L' :=
  let h₁ := isSplittingField_X_pow_sub_one n K L
  let h₂ := isSplittingField_X_pow_sub_one n K L'
  (@IsSplittingField.algEquiv K L _ _ _ (X ^ (n : ℕ) - 1) h₁).trans
    (@IsSplittingField.algEquiv K L' _ _ _ (X ^ (n : ℕ) - 1) h₂).symm
#align is_cyclotomic_extension.alg_equiv IsCyclotomicExtension.algEquiv
-/

scoped[Cyclotomic] attribute [instance] IsCyclotomicExtension.isSplittingField_X_pow_sub_one

#print IsCyclotomicExtension.isGalois /-
theorem isGalois : IsGalois K L :=
  letI := splitting_field_X_pow_sub_one n K L
  IsGalois.of_separable_splitting_field (X_pow_sub_one_separable_iff.2 (ne_zero' n K L).1)
#align is_cyclotomic_extension.is_galois IsCyclotomicExtension.isGalois
-/

scoped[Cyclotomic] attribute [instance] IsCyclotomicExtension.isGalois

#print IsCyclotomicExtension.splitting_field_cyclotomic /-
/-- If `is_cyclotomic_extension {n} K L`, then `L` is the splitting field of `cyclotomic n K`. -/
theorem splitting_field_cyclotomic : IsSplittingField K L (cyclotomic n K) :=
  { Splits := splits_cyclotomic K L (mem_singleton n)
    adjoin_rootSet := by
      rw [← ((iff_adjoin_eq_top {n} K L).1 inferInstance).2]
      letI := Classical.decEq L
      -- todo: make `exists_prim_root` take an explicit `L`
      obtain ⟨ζ : L, hζ⟩ := IsCyclotomicExtension.exists_prim_root K (mem_singleton n)
      exact adjoin_roots_cyclotomic_eq_adjoin_nth_roots hζ
      all_goals infer_instance }
#align is_cyclotomic_extension.splitting_field_cyclotomic IsCyclotomicExtension.splitting_field_cyclotomic
-/

scoped[Cyclotomic] attribute [instance] IsCyclotomicExtension.splitting_field_cyclotomic

end Singleton

end Field

end IsCyclotomicExtension

section CyclotomicField

/- ./././Mathport/Syntax/Translate/Command.lean:43:9: unsupported derive handler algebra[algebra] K -/
#print CyclotomicField /-
/-- Given `n : ℕ+` and a field `K`, we define `cyclotomic_field n K` as the
splitting field of `cyclotomic n K`. If `n` is nonzero in `K`, it has
the instance `is_cyclotomic_extension {n} K (cyclotomic_field n K)`. -/
def CyclotomicField : Type w :=
  (cyclotomic n K).SplittingField
deriving Field,
  «./././Mathport/Syntax/Translate/Command.lean:43:9: unsupported derive handler algebra[algebra] K»,
  Inhabited
#align cyclotomic_field CyclotomicField
-/

namespace CyclotomicField

instance [CharZero K] : CharZero (CyclotomicField n K) :=
  charZero_of_injective_algebraMap (algebraMap K _).Injective

#print CyclotomicField.isCyclotomicExtension /-
instance isCyclotomicExtension [NeZero ((n : ℕ) : K)] :
    IsCyclotomicExtension {n} K (CyclotomicField n K) :=
  by
  haveI : NeZero ((n : ℕ) : CyclotomicField n K) :=
    NeZero.nat_of_injective (algebraMap K _).Injective
  letI := Classical.decEq (CyclotomicField n K)
  obtain ⟨ζ, hζ⟩ :=
    exists_root_of_splits (algebraMap K (CyclotomicField n K)) (splitting_field.splits _)
      (degree_cyclotomic_pos n K n.pos).ne'
  rw [← eval_map, ← is_root.def, map_cyclotomic, is_root_cyclotomic_iff] at hζ 
  refine' ⟨forall_eq.2 ⟨ζ, hζ⟩, _⟩
  rw [← Algebra.eq_top_iff, ← splitting_field.adjoin_root_set, eq_comm]
  exact IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots hζ
#align cyclotomic_field.is_cyclotomic_extension CyclotomicField.isCyclotomicExtension
-/

end CyclotomicField

end CyclotomicField

section IsDomain

variable [Algebra A K] [IsFractionRing A K]

section CyclotomicRing

#print CyclotomicField.algebraBase /-
/-- If `K` is the fraction field of `A`, the `A`-algebra structure on `cyclotomic_field n K`.
-/
@[nolint unused_arguments]
instance CyclotomicField.algebraBase : Algebra A (CyclotomicField n K) :=
  SplittingField.algebra' (cyclotomic n K)
#align cyclotomic_field.algebra_base CyclotomicField.algebraBase
-/

/-- Ensure there are no diamonds when `A = ℤ`. -/
example : algebraInt (CyclotomicField n ℚ) = CyclotomicField.algebraBase _ _ _ :=
  rfl

#print CyclotomicField.algebra' /-
instance CyclotomicField.algebra' {R : Type _} [CommRing R] [Algebra R K] :
    Algebra R (CyclotomicField n K) :=
  SplittingField.algebra' (cyclotomic n K)
#align cyclotomic_field.algebra' CyclotomicField.algebra'
-/

instance {R : Type _} [CommRing R] [Algebra R K] : IsScalarTower R K (CyclotomicField n K) :=
  SplittingField.isScalarTower _

#print CyclotomicField.noZeroSMulDivisors /-
instance CyclotomicField.noZeroSMulDivisors : NoZeroSMulDivisors A (CyclotomicField n K) :=
  by
  refine' NoZeroSMulDivisors.of_algebraMap_injective _
  rw [IsScalarTower.algebraMap_eq A K (CyclotomicField n K)]
  exact
    Function.Injective.comp (NoZeroSMulDivisors.algebraMap_injective K (CyclotomicField n K))
      (IsFractionRing.injective A K)
#align cyclotomic_field.no_zero_smul_divisors CyclotomicField.noZeroSMulDivisors
-/

#print CyclotomicRing /-
/-- If `A` is a domain with fraction field `K` and `n : ℕ+`, we define `cyclotomic_ring n A K` as
the `A`-subalgebra of `cyclotomic_field n K` generated by the roots of `X ^ n - 1`. If `n`
is nonzero in `A`, it has the instance `is_cyclotomic_extension {n} A (cyclotomic_ring n A K)`. -/
@[nolint unused_arguments]
def CyclotomicRing : Type w :=
  adjoin A {b : CyclotomicField n K | b ^ (n : ℕ) = 1}
deriving CommRing, IsDomain, Inhabited
#align cyclotomic_ring CyclotomicRing
-/

namespace CyclotomicRing

#print CyclotomicRing.algebraBase /-
/-- The `A`-algebra structure on `cyclotomic_ring n A K`. -/
instance algebraBase : Algebra A (CyclotomicRing n A K) :=
  (adjoin A _).Algebra
#align cyclotomic_ring.algebra_base CyclotomicRing.algebraBase
-/

-- Ensure that there is no diamonds with ℤ.
example {n : ℕ+} : CyclotomicRing.algebraBase n ℤ ℚ = algebraInt _ :=
  rfl

instance : NoZeroSMulDivisors A (CyclotomicRing n A K) :=
  (adjoin A _).noZeroSMulDivisors_bot

#print CyclotomicRing.algebraBase_injective /-
theorem algebraBase_injective : Function.Injective <| algebraMap A (CyclotomicRing n A K) :=
  NoZeroSMulDivisors.algebraMap_injective _ _
#align cyclotomic_ring.algebra_base_injective CyclotomicRing.algebraBase_injective
-/

instance : Algebra (CyclotomicRing n A K) (CyclotomicField n K) :=
  (adjoin A _).toAlgebra

#print CyclotomicRing.adjoin_algebra_injective /-
theorem adjoin_algebra_injective :
    Function.Injective <| algebraMap (CyclotomicRing n A K) (CyclotomicField n K) :=
  Subtype.val_injective
#align cyclotomic_ring.adjoin_algebra_injective CyclotomicRing.adjoin_algebra_injective
-/

instance : NoZeroSMulDivisors (CyclotomicRing n A K) (CyclotomicField n K) :=
  NoZeroSMulDivisors.of_algebraMap_injective (adjoin_algebra_injective n A K)

instance : IsScalarTower A (CyclotomicRing n A K) (CyclotomicField n K) :=
  IsScalarTower.subalgebra' _ _ _ _

#print CyclotomicRing.isCyclotomicExtension /-
instance isCyclotomicExtension [NeZero ((n : ℕ) : A)] :
    IsCyclotomicExtension {n} A (CyclotomicRing n A K)
    where
  exists_prim_root a han := by
    rw [mem_singleton_iff] at han 
    subst a
    haveI := NeZero.of_noZeroSMulDivisors A K n
    haveI := NeZero.of_noZeroSMulDivisors A (CyclotomicField n K) n
    obtain ⟨μ, hμ⟩ := (CyclotomicField.isCyclotomicExtension n K).exists_prim_root (mem_singleton n)
    refine' ⟨⟨μ, subset_adjoin _⟩, _⟩
    · apply (isRoot_of_unity_iff n.pos (CyclotomicField n K)).mpr
      refine' ⟨n, Nat.mem_divisors_self _ n.ne_zero, _⟩
      rwa [← is_root_cyclotomic_iff] at hμ 
    · rwa [← IsPrimitiveRoot.coe_submonoidClass_iff, Subtype.coe_mk]
  adjoin_roots x :=
    by
    refine'
      adjoin_induction' (fun y hy => _) (fun a => _) (fun y z hy hz => _) (fun y z hy hz => _) x
    · refine' subset_adjoin _
      simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq]
      rwa [← Subalgebra.coe_eq_one, Subalgebra.coe_pow, Subtype.coe_mk]
    · exact Subalgebra.algebraMap_mem _ a
    · exact Subalgebra.add_mem _ hy hz
    · exact Subalgebra.mul_mem _ hy hz
#align cyclotomic_ring.is_cyclotomic_extension CyclotomicRing.isCyclotomicExtension
-/

instance [IsDomain A] [NeZero ((n : ℕ) : A)] :
    IsFractionRing (CyclotomicRing n A K) (CyclotomicField n K)
    where
  map_units := fun ⟨x, hx⟩ => by
    rw [isUnit_iff_ne_zero]
    apply map_ne_zero_of_mem_nonZeroDivisors
    apply adjoin_algebra_injective
    exact hx
  surj x :=
    by
    letI : NeZero ((n : ℕ) : K) := NeZero.nat_of_injective (IsFractionRing.injective A K)
    refine'
      Algebra.adjoin_induction
        (((IsCyclotomicExtension.iff_singleton n K _).1
              (CyclotomicField.isCyclotomicExtension n K)).2
          x)
        (fun y hy => _) (fun k => _) _ _
    · exact ⟨⟨⟨y, subset_adjoin hy⟩, 1⟩, by simpa⟩
    · have : IsLocalization (nonZeroDivisors A) K := inferInstance
      replace := this.surj
      obtain ⟨⟨z, w⟩, hw⟩ := this k
      refine'
        ⟨⟨algebraMap A _ z, algebraMap A _ w,
            map_mem_nonZeroDivisors _ (algebra_base_injective n A K) w.2⟩,
          _⟩
      letI : IsScalarTower A K (CyclotomicField n K) :=
        IsScalarTower.of_algebraMap_eq (congr_fun rfl)
      rw [SetLike.coe_mk, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        @IsScalarTower.algebraMap_apply A K _ _ _ _ _ (_root_.cyclotomic_field.algebra n K) _ _ w, ←
        RingHom.map_mul, hw, ← IsScalarTower.algebraMap_apply]
    · rintro y z ⟨a, ha⟩ ⟨b, hb⟩
      refine' ⟨⟨a.1 * b.2 + b.1 * a.2, a.2 * b.2, mul_mem_nonZeroDivisors.2 ⟨a.2.2, b.2.2⟩⟩, _⟩
      rw [SetLike.coe_mk, RingHom.map_mul, add_mul, ← mul_assoc, ha,
        mul_comm ((algebraMap _ _) ↑a.2), ← mul_assoc, hb]
      simp only [map_add, map_mul]
    · rintro y z ⟨a, ha⟩ ⟨b, hb⟩
      refine' ⟨⟨a.1 * b.1, a.2 * b.2, mul_mem_nonZeroDivisors.2 ⟨a.2.2, b.2.2⟩⟩, _⟩
      rw [SetLike.coe_mk, RingHom.map_mul, mul_comm ((algebraMap _ _) ↑a.2), mul_assoc, ←
        mul_assoc z, hb, ← mul_comm ((algebraMap _ _) ↑a.2), ← mul_assoc, ha]
      simp only [map_mul]
  eq_iff_exists x y :=
    ⟨fun h => ⟨1, by rw [adjoin_algebra_injective n A K h]⟩, fun ⟨c, hc⟩ => by
      rw [mul_left_cancel₀ (nonZeroDivisors.ne_zero c.prop) hc]⟩

#print CyclotomicRing.eq_adjoin_primitive_root /-
theorem eq_adjoin_primitive_root {μ : CyclotomicField n K} (h : IsPrimitiveRoot μ n) :
    CyclotomicRing n A K = adjoin A ({μ} : Set (CyclotomicField n K)) :=
  by
  rw [← IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic h,
    IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots h]
  simp [CyclotomicRing]
#align cyclotomic_ring.eq_adjoin_primitive_root CyclotomicRing.eq_adjoin_primitive_root
-/

end CyclotomicRing

end CyclotomicRing

end IsDomain

section IsAlgClosed

variable [IsAlgClosed K]

#print IsAlgClosed.isCyclotomicExtension /-
/-- Algebraically closed fields are `S`-cyclotomic extensions over themselves if
`ne_zero ((a : ℕ) : K))` for all `a ∈ S`. -/
theorem IsAlgClosed.isCyclotomicExtension (h : ∀ a ∈ S, NeZero ((a : ℕ) : K)) :
    IsCyclotomicExtension S K K :=
  by
  refine' ⟨fun a ha => _, algebra.eq_top_iff.mp <| Subsingleton.elim _ _⟩
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_aeval_eq_zero K _ (degree_cyclotomic_pos a K a.pos).ne'
  refine' ⟨r, _⟩
  haveI := h a ha
  rwa [coe_aeval_eq_eval, ← is_root.def, is_root_cyclotomic_iff] at hr 
#align is_alg_closed.is_cyclotomic_extension IsAlgClosed.isCyclotomicExtension
-/

#print IsAlgClosedOfCharZero.isCyclotomicExtension /-
instance IsAlgClosedOfCharZero.isCyclotomicExtension [CharZero K] :
    ∀ S, IsCyclotomicExtension S K K := fun S =>
  IsAlgClosed.isCyclotomicExtension S K fun a ha => inferInstance
#align is_alg_closed_of_char_zero.is_cyclotomic_extension IsAlgClosedOfCharZero.isCyclotomicExtension
-/

end IsAlgClosed

