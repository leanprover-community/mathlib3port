/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
import Mathbin.Data.Finsupp.Fintype
import Mathbin.Data.Matrix.Notation
import Mathbin.Data.Zmod.Quotient
import Mathbin.LinearAlgebra.FreeModule.Finite.Basic
import Mathbin.LinearAlgebra.FreeModule.Pid
import Mathbin.LinearAlgebra.FreeModule.IdealQuotient
import Mathbin.LinearAlgebra.Isomorphisms
import Mathbin.RingTheory.DedekindDomain.Ideal
import Mathbin.RingTheory.Norm

/-!

# Ideal norms

This file defines the absolute ideal norm `ideal.abs_norm (I : ideal R) : ℕ` as the cardinality of
the quotient `R ⧸ I` (setting it to 0 if the cardinality is infinite).

## Main definitions

 * `submodule.card_quot (S : submodule R M)`: the cardinality of the quotient `M ⧸ S`, in `ℕ`.
   This maps `⊥` to `0` and `⊤` to `1`.
 * `ideal.abs_norm (I : ideal R)`: the absolute ideal norm, defined as
   the cardinality of the quotient `R ⧸ I`, as a bundled monoid-with-zero homomorphism.

## TODO

Define the relative norm.
-/


open BigOperators

namespace Submodule

variable {R M : Type _} [Ring R] [AddCommGroup M] [Module R M]

section

/-- The cardinality of `(M ⧸ S)`, if `(M ⧸ S)` is finite, and `0` otherwise.
This is used to define the absolute ideal norm `ideal.abs_norm`.
-/
noncomputable def cardQuot (S : Submodule R M) : ℕ :=
  AddSubgroup.index S.toAddSubgroup
#align submodule.card_quot Submodule.cardQuot

@[simp]
theorem card_quot_apply (S : Submodule R M) [Fintype (M ⧸ S)] : cardQuot S = Fintype.card (M ⧸ S) :=
  AddSubgroup.index_eq_card _
#align submodule.card_quot_apply Submodule.card_quot_apply

variable (R M)

@[simp]
theorem card_quot_bot [Infinite M] : cardQuot (⊥ : Submodule R M) = 0 :=
  AddSubgroup.index_bot.trans Nat.card_eq_zero_of_infinite
#align submodule.card_quot_bot Submodule.card_quot_bot

@[simp]
theorem card_quot_top : cardQuot (⊤ : Submodule R M) = 1 :=
  AddSubgroup.index_top
#align submodule.card_quot_top Submodule.card_quot_top

variable {R M}

@[simp]
theorem card_quot_eq_one_iff {P : Submodule R M} : cardQuot P = 1 ↔ P = ⊤ :=
  AddSubgroup.index_eq_one.trans (by simp [SetLike.ext_iff])
#align submodule.card_quot_eq_one_iff Submodule.card_quot_eq_one_iff

end

end Submodule

variable {S : Type _} [CommRing S] [IsDomain S]

open Submodule

/-- Multiplicity of the ideal norm, for coprime ideals.
This is essentially just a repackaging of the Chinese Remainder Theorem.
-/
theorem card_quot_mul_of_coprime [IsDedekindDomain S] [Module.Free ℤ S] [Module.Finite ℤ S] {I J : Ideal S}
    (coprime : I ⊔ J = ⊤) : cardQuot (I * J) = cardQuot I * cardQuot J := by
  let b := Module.Free.chooseBasis ℤ S
  cases isEmpty_or_nonempty (Module.Free.ChooseBasisIndex ℤ S)
  · haveI : Subsingleton S := Function.Surjective.subsingleton b.repr.to_equiv.symm.surjective
    nontriviality S
    exfalso
    exact not_nontrivial_iff_subsingleton.mpr ‹Subsingleton S› ‹Nontrivial S›
    
  haveI : Infinite S := Infinite.of_surjective _ b.repr.to_equiv.surjective
  by_cases hI : I = ⊥
  · rw [hI, Submodule.bot_mul, card_quot_bot, zero_mul]
    
  by_cases hJ : J = ⊥
  · rw [hJ, Submodule.mul_bot, card_quot_bot, mul_zero]
    
  have hIJ : I * J ≠ ⊥ := mt ideal.mul_eq_bot.mp (not_or_of_not hI hJ)
  letI := Classical.decEq (Module.Free.ChooseBasisIndex ℤ S)
  letI := I.fintype_quotient_of_free_of_ne_bot hI
  letI := J.fintype_quotient_of_free_of_ne_bot hJ
  letI := (I * J).fintypeQuotientOfFreeOfNeBot hIJ
  rw [card_quot_apply, card_quot_apply, card_quot_apply,
    fintype.card_eq.mpr ⟨(Ideal.quotientMulEquivQuotientProd I J coprime).toEquiv⟩, Fintype.card_prod]
#align card_quot_mul_of_coprime card_quot_mul_of_coprime

/-- If the `d` from `ideal.exists_mul_add_mem_pow_succ` is unique, up to `P`,
then so are the `c`s, up to `P ^ (i + 1)`.
Inspired by [Neukirch], proposition 6.1 -/
theorem Ideal.mul_add_mem_pow_succ_inj (P : Ideal S) {i : ℕ} (a d d' e e' : S) (a_mem : a ∈ P ^ i)
    (e_mem : e ∈ P ^ (i + 1)) (e'_mem : e' ∈ P ^ (i + 1)) (h : d - d' ∈ P) : a * d + e - (a * d' + e') ∈ P ^ (i + 1) :=
  by
  have : a * d - a * d' ∈ P ^ (i + 1) := by convert Ideal.mul_mem_mul a_mem h <;> simp [mul_sub, pow_succ, mul_comm]
  convert Ideal.add_mem _ this (Ideal.sub_mem _ e_mem e'_mem)
  ring
#align ideal.mul_add_mem_pow_succ_inj Ideal.mul_add_mem_pow_succ_inj

section PPrime

variable {P : Ideal S} [P_prime : P.IsPrime] (hP : P ≠ ⊥)

include P_prime hP

/-- If `a ∈ P^i \ P^(i+1)` and `c ∈ P^i`, then `a * d + e = c` for `e ∈ P^(i+1)`.
`ideal.mul_add_mem_pow_succ_unique` shows the choice of `d` is unique, up to `P`.
Inspired by [Neukirch], proposition 6.1 -/
theorem Ideal.exists_mul_add_mem_pow_succ [IsDedekindDomain S] {i : ℕ} (a c : S) (a_mem : a ∈ P ^ i)
    (a_not_mem : a ∉ P ^ (i + 1)) (c_mem : c ∈ P ^ i) : ∃ d : S, ∃ e ∈ P ^ (i + 1), a * d + e = c := by
  suffices eq_b : P ^ i = Ideal.span {a} ⊔ P ^ (i + 1)
  · rw [eq_b] at c_mem
    simp only [mul_comm a]
    exact ideal.mem_span_singleton_sup.mp c_mem
    
  refine'
    (Ideal.eq_prime_pow_of_succ_lt_of_le hP (lt_of_le_of_ne le_sup_right _)
        (sup_le (ideal.span_le.mpr (set.singleton_subset_iff.mpr a_mem)) (Ideal.pow_succ_lt_pow hP i).le)).symm
  contrapose! a_not_mem with this
  rw [this]
  exact mem_sup.mpr ⟨a, mem_span_singleton_self a, 0, by simp, by simp⟩
#align ideal.exists_mul_add_mem_pow_succ Ideal.exists_mul_add_mem_pow_succ

theorem Ideal.mem_prime_of_mul_mem_pow [IsDedekindDomain S] {P : Ideal S} [P_prime : P.IsPrime] (hP : P ≠ ⊥) {i : ℕ}
    {a b : S} (a_not_mem : a ∉ P ^ (i + 1)) (ab_mem : a * b ∈ P ^ (i + 1)) : b ∈ P := by
  simp only [← Ideal.span_singleton_le_iff_mem, ← Ideal.dvd_iff_le, pow_succ, ←
    Ideal.span_singleton_mul_span_singleton] at a_not_mem ab_mem⊢
  exact (prime_pow_succ_dvd_mul (Ideal.prime_of_is_prime hP P_prime) ab_mem).resolve_left a_not_mem
#align ideal.mem_prime_of_mul_mem_pow Ideal.mem_prime_of_mul_mem_pow

/-- The choice of `d` in `ideal.exists_mul_add_mem_pow_succ` is unique, up to `P`.
Inspired by [Neukirch], proposition 6.1 -/
theorem Ideal.mul_add_mem_pow_succ_unique [IsDedekindDomain S] {i : ℕ} (a d d' e e' : S) (a_not_mem : a ∉ P ^ (i + 1))
    (e_mem : e ∈ P ^ (i + 1)) (e'_mem : e' ∈ P ^ (i + 1)) (h : a * d + e - (a * d' + e') ∈ P ^ (i + 1)) : d - d' ∈ P :=
  by
  have : e' - e ∈ P ^ (i + 1) := Ideal.sub_mem _ e'_mem e_mem
  have h' : a * (d - d') ∈ P ^ (i + 1) := by
    convert Ideal.add_mem _ h (Ideal.sub_mem _ e'_mem e_mem)
    ring
  exact Ideal.mem_prime_of_mul_mem_pow hP a_not_mem h'
#align ideal.mul_add_mem_pow_succ_unique Ideal.mul_add_mem_pow_succ_unique

/-- Multiplicity of the ideal norm, for powers of prime ideals. -/
theorem card_quot_pow_of_prime [IsDedekindDomain S] [Module.Finite ℤ S] [Module.Free ℤ S] {i : ℕ} :
    cardQuot (P ^ i) = cardQuot P ^ i := by
  let b := Module.Free.chooseBasis ℤ S
  classical
  induction' i with i ih
  · simp
    
  letI := Ideal.fintypeQuotientOfFreeOfNeBot (P ^ i.succ) (pow_ne_zero _ hP)
  letI := Ideal.fintypeQuotientOfFreeOfNeBot (P ^ i) (pow_ne_zero _ hP)
  letI := Ideal.fintypeQuotientOfFreeOfNeBot P hP
  have : P ^ (i + 1) < P ^ i := Ideal.pow_succ_lt_pow hP i
  suffices hquot : map (P ^ i.succ).mkq (P ^ i) ≃ S ⧸ P
  · rw [pow_succ (card_quot P), ← ih, card_quot_apply (P ^ i.succ), ←
      card_quotient_mul_card_quotient (P ^ i) (P ^ i.succ) this.le, card_quot_apply (P ^ i), card_quot_apply P]
    congr 1
    rw [Fintype.card_eq]
    exact ⟨hquot⟩
    
  choose a a_mem a_not_mem using SetLike.exists_of_lt this
  choose f g hg hf using fun c (hc : c ∈ P ^ i) => Ideal.exists_mul_add_mem_pow_succ hP a c a_mem a_not_mem hc
  choose k hk_mem hk_eq using fun c' (hc' : c' ∈ map (mkq (P ^ i.succ)) (P ^ i)) => submodule.mem_map.mp hc'
  refine' Equiv.ofBijective (fun c' => Quotient.mk' (f (k c' c'.Prop) (hk_mem c' c'.Prop))) ⟨_, _⟩
  · rintro ⟨c₁', hc₁'⟩ ⟨c₂', hc₂'⟩ h
    rw [Subtype.mk_eq_mk, ← hk_eq _ hc₁', ← hk_eq _ hc₂', mkq_apply, mkq_apply, Submodule.Quotient.eq, ←
      hf _ (hk_mem _ hc₁'), ← hf _ (hk_mem _ hc₂')]
    refine' Ideal.mul_add_mem_pow_succ_inj _ _ _ _ _ _ a_mem (hg _ _) (hg _ _) _
    simpa only [Submodule.Quotient.mk'_eq_mk, Submodule.Quotient.mk'_eq_mk, Submodule.Quotient.eq] using h
    
  · intro d'
    refine' Quotient.inductionOn' d' fun d => _
    have hd' := mem_map.mpr ⟨a * d, Ideal.mul_mem_right d _ a_mem, rfl⟩
    refine' ⟨⟨_, hd'⟩, _⟩
    simp only [Submodule.Quotient.mk'_eq_mk, Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq, Subtype.coe_mk]
    refine' Ideal.mul_add_mem_pow_succ_unique hP a _ _ _ _ a_not_mem (hg _ (hk_mem _ hd')) (zero_mem _) _
    rw [hf, add_zero]
    exact (Submodule.Quotient.eq _).mp (hk_eq _ hd')
    
#align card_quot_pow_of_prime card_quot_pow_of_prime

end PPrime

/-- Multiplicativity of the ideal norm in number rings. -/
theorem card_quot_mul [IsDedekindDomain S] [Module.Free ℤ S] [Module.Finite ℤ S] (I J : Ideal S) :
    cardQuot (I * J) = cardQuot I * cardQuot J := by
  let b := Module.Free.chooseBasis ℤ S
  cases isEmpty_or_nonempty (Module.Free.ChooseBasisIndex ℤ S)
  · haveI : Subsingleton S := Function.Surjective.subsingleton b.repr.to_equiv.symm.surjective
    nontriviality S
    exfalso
    exact not_nontrivial_iff_subsingleton.mpr ‹Subsingleton S› ‹Nontrivial S›
    
  haveI : Infinite S := Infinite.of_surjective _ b.repr.to_equiv.surjective
  exact
    UniqueFactorizationMonoid.multiplicative_of_coprime card_quot I J (card_quot_bot _ _)
      (fun I J hI => by simp [ideal.is_unit_iff.mp hI, Ideal.mul_top])
      (fun I i hI =>
        have : Ideal.IsPrime I := Ideal.is_prime_of_prime hI
        card_quot_pow_of_prime hI.ne_zero)
      fun I J hIJ =>
      card_quot_mul_of_coprime
        (ideal.is_unit_iff.mp (hIJ _ (ideal.dvd_iff_le.mpr le_sup_left) (ideal.dvd_iff_le.mpr le_sup_right)))
#align card_quot_mul card_quot_mul

/-- The absolute norm of the ideal `I : ideal R` is the cardinality of the quotient `R ⧸ I`. -/
noncomputable def Ideal.absNorm [Infinite S] [IsDedekindDomain S] [Module.Free ℤ S] [Module.Finite ℤ S] :
    Ideal S →*₀ ℕ where
  toFun := Submodule.cardQuot
  map_mul' I J := by rw [card_quot_mul]
  map_one' := by rw [Ideal.one_eq_top, card_quot_top]
  map_zero' := by rw [Ideal.zero_eq_bot, card_quot_bot]
#align ideal.abs_norm Ideal.absNorm

