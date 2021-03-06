/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
import Mathbin.RingTheory.GradedAlgebra.HomogeneousIdeal

/-!

This file contains a proof that the radical of any homogeneous ideal is a homogeneous ideal

## Main statements

* `ideal.is_homogeneous.is_prime_iff`: for any `I : ideal A`, if `I` is homogeneous, then
  `I` is prime if and only if `I` is homogeneously prime, i.e. `I β  β€` and if `x, y` are
  homogeneous elements such that `x * y β I`, then at least one of `x,y` is in `I`.
* `ideal.is_prime.homogeneous_core`: for any `I : ideal A`, if `I` is prime, then
  `I.homogeneous_core π` (i.e. the largest homogeneous ideal contained in `I`) is also prime.
* `ideal.is_homogeneous.radical`: for any `I : ideal A`, if `I` is homogeneous, then the
  radical of `I` is homogeneous as well.
* `homogeneous_ideal.radical`: for any `I : homogeneous_ideal π`, `I.radical` is the the
  radical of `I` as a `homogeneous_ideal π`

## Implementation details

Throughout this file, the indexing type `ΞΉ` of grading is assumed to be a
`linear_ordered_cancel_add_comm_monoid`. This might be stronger than necessary but cancelling
property is strictly necessary; for a counterexample of how `ideal.is_homogeneous.is_prime_iff`
fails for a non-cancellative set see `counterexample/homogeneous_prime_not_prime.lean`.

## Tags

homogeneous, radical
-/


open GradedRing DirectSum SetLike Finset

open BigOperators

variable {ΞΉ Ο A : Type _}

variable [CommRingβ A]

variable [LinearOrderedCancelAddCommMonoid ΞΉ]

variable [SetLike Ο A] [AddSubmonoidClass Ο A] {π : ΞΉ β Ο} [GradedRing π]

include A

theorem Ideal.IsHomogeneous.is_prime_of_homogeneous_mem_or_mem {I : Ideal A} (hI : I.IsHomogeneous π) (I_ne_top : I β  β€)
    (homogeneous_mem_or_mem : β {x y : A}, IsHomogeneous π x β IsHomogeneous π y β x * y β I β x β I β¨ y β I) :
    Ideal.IsPrime I :=
  β¨I_ne_top, by
    intro x y hxy
    by_contra rid
    obtain β¨ridβ, ridββ© := not_or_distrib.mp rid
    /-
      The idea of the proof is the following :
      since `x * y β I` and `I` homogeneous, then `proj i (x * y) β I` for any `i : ΞΉ`.
      Then consider two sets `{i β x.support | xα΅’ β I}` and `{j β y.support | yβ±Ό β J}`;
      let `maxβ, maxβ` be the maximum of the two sets, then `proj (maxβ + maxβ) (x * y) β I`.
      Then, `proj maxβ x β I` and `proj maxβ j β I`
      but `proj i x β I` for all `maxβ < i` and `proj j y β I` for all `maxβ < j`.
      `  proj (maxβ + maxβ) (x * y)`
      `= β {(i, j) β supports | i + j = maxβ + maxβ}, xα΅’ * yβ±Ό`
      `= proj maxβ x * proj maxβ y`
      `  + β {(i, j) β supports \ {(maxβ, maxβ)} | i + j = maxβ + maxβ}, xα΅’ * yβ±Ό`.
      This is a contradiction, because both `proj (maxβ + maxβ) (x * y) β I` and the sum on the
      right hand side is in `I` however `proj maxβ x * proj maxβ y` is not in `I`.
      -/
    classical
    set setβ := (decompose π x).support.filter fun i => proj π i x β I with setβ_eq
    set setβ := (decompose π y).support.filter fun i => proj π i y β I with setβ_eq
    have nonempty : β x : A, x β I β ((decompose π x).support.filter fun i => proj π i x β I).Nonempty := by
      intro x hx
      rw [filter_nonempty_iff]
      contrapose! hx
      simp_rw [proj_apply] at hx
      rw [β sum_support_decompose π x]
      exact Ideal.sum_mem _ hx
    set maxβ := setβ.max' (Nonempty x ridβ) with maxβ_eq
    set maxβ := setβ.max' (Nonempty y ridβ) with maxβ_eq
    have mem_maxβ : maxβ β setβ := max'_mem setβ (Nonempty x ridβ)
    have mem_maxβ : maxβ β setβ := max'_mem setβ (Nonempty y ridβ)
    replace hxy : proj π (maxβ + maxβ) (x * y) β I := hI _ hxy
    have mem_I : proj π maxβ x * proj π maxβ y β I := by
      set antidiag :=
        ((decompose π x).support.product (decompose π y).support).filter fun z : ΞΉ Γ ΞΉ => z.1 + z.2 = maxβ + maxβ with
        ha
      have mem_antidiag : (maxβ, maxβ) β antidiag := by
        simp only [β add_sum_erase, β mem_filter, β mem_product]
        exact β¨β¨mem_of_mem_filter _ mem_maxβ, mem_of_mem_filter _ mem_maxββ©, rflβ©
      have eq_add_sum :=
        calc
          proj π (maxβ + maxβ) (x * y) = β ij in antidiag, proj π ij.1 x * proj π ij.2 y := by
            simp_rw [ha, proj_apply, DirectSum.decompose_mul, DirectSum.coe_mul_apply π]
          _ = proj π maxβ x * proj π maxβ y + β ij in antidiag.erase (maxβ, maxβ), proj π ij.1 x * proj π ij.2 y :=
            (add_sum_erase _ _ mem_antidiag).symm
          
      rw [eq_sub_of_add_eq eq_add_sum.symm]
      refine' Ideal.sub_mem _ hxy (Ideal.sum_mem _ fun z H => _)
      rcases z with β¨i, jβ©
      simp only [β mem_erase, β Prod.mk.inj_iff, β Ne.def, β mem_filter, β mem_product] at H
      rcases H with β¨Hβ, β¨Hβ, Hββ©, Hββ©
      have max_lt : maxβ < i β¨ maxβ < j := by
        rcases lt_trichotomyβ maxβ i with (h | rfl | h)
        Β· exact Or.inl h
          
        Β· refine' False.elim (Hβ β¨rfl, add_left_cancelβ Hββ©)
          
        Β· apply Or.inr
          have := add_lt_add_right h j
          rw [Hβ] at this
          exact lt_of_add_lt_add_left this
          
      cases max_ltβ
      Β· -- in this case `maxβ < i`, then `xα΅’ β I`; for otherwise `i β setβ` then `i β€ maxβ`.
        have not_mem : i β setβ := fun h => lt_irreflβ _ ((max'_lt_iff setβ (Nonempty x ridβ)).mp max_ltβ i h)
        rw [setβ_eq] at not_mem
        simp only [β not_and, β not_not, β Ne.def, β mem_filter] at not_mem
        exact Ideal.mul_mem_right _ I (not_mem Hβ)
        
      Β· -- in this case  `maxβ < j`, then `yβ±Ό β I`; for otherwise `j β setβ`, then `j β€ maxβ`.
        have not_mem : j β setβ := fun h => lt_irreflβ _ ((max'_lt_iff setβ (Nonempty y ridβ)).mp max_ltβ j h)
        rw [setβ_eq] at not_mem
        simp only [β not_and, β not_not, β Ne.def, β mem_filter] at not_mem
        exact Ideal.mul_mem_left I _ (not_mem Hβ)
        
    have not_mem_I : proj π maxβ x * proj π maxβ y β I := by
      have neither_mem : proj π maxβ x β I β§ proj π maxβ y β I := by
        rw [mem_filter] at mem_maxβ mem_maxβ
        exact β¨mem_maxβ.2, mem_maxβ.2β©
      intro rid
      cases homogeneous_mem_or_mem β¨maxβ, SetLike.coe_mem _β© β¨maxβ, SetLike.coe_mem _β© mem_I
      Β· apply neither_mem.1 h
        
      Β· apply neither_mem.2 h
        
    exact not_mem_I mem_Iβ©

theorem Ideal.IsHomogeneous.is_prime_iff {I : Ideal A} (h : I.IsHomogeneous π) :
    I.IsPrime β
      I β  β€ β§ β {x y : A}, SetLike.IsHomogeneous π x β SetLike.IsHomogeneous π y β x * y β I β x β I β¨ y β I :=
  β¨fun HI => β¨ne_of_apply_ne _ HI.ne_top, fun x y hx hy hxy => Ideal.IsPrime.mem_or_mem HI hxyβ©,
    fun β¨I_ne_top, homogeneous_mem_or_memβ© => h.is_prime_of_homogeneous_mem_or_mem I_ne_top @homogeneous_mem_or_memβ©

theorem Ideal.IsPrime.homogeneous_core {I : Ideal A} (h : I.IsPrime) : (I.homogeneousCore π).toIdeal.IsPrime := by
  apply (Ideal.homogeneousCore π I).IsHomogeneous.is_prime_of_homogeneous_mem_or_mem
  Β· exact ne_top_of_le_ne_top h.ne_top (Ideal.to_ideal_homogeneous_core_le π I)
    
  rintro x y hx hy hxy
  have H := h.mem_or_mem (Ideal.to_ideal_homogeneous_core_le π I hxy)
  refine' H.imp _ _
  Β· exact Ideal.mem_homogeneous_core_of_is_homogeneous_of_mem hx
    
  Β· exact Ideal.mem_homogeneous_core_of_is_homogeneous_of_mem hy
    

theorem Ideal.IsHomogeneous.radical_eq {I : Ideal A} (hI : I.IsHomogeneous π) :
    I.radical = inf { J | J.IsHomogeneous π β§ I β€ J β§ J.IsPrime } := by
  rw [Ideal.radical_eq_Inf]
  apply le_antisymmβ
  Β· exact Inf_le_Inf fun J => And.right
    
  Β· refine' Inf_le_Inf_of_forall_exists_le _
    rintro J β¨HJβ, HJββ©
    refine' β¨(J.homogeneous_core π).toIdeal, _, J.to_ideal_homogeneous_core_le _β©
    refine' β¨HomogeneousIdeal.is_homogeneous _, _, HJβ.homogeneous_coreβ©
    refine' hI.to_ideal_homogeneous_core_eq_self.symm.trans_le (Ideal.homogeneous_core_mono _ HJβ)
    

theorem Ideal.IsHomogeneous.radical {I : Ideal A} (h : I.IsHomogeneous π) : I.radical.IsHomogeneous π := by
  rw [h.radical_eq]
  exact Ideal.IsHomogeneous.Inf fun _ => And.left

/-- The radical of a homogenous ideal, as another homogenous ideal. -/
def HomogeneousIdeal.radical (I : HomogeneousIdeal π) : HomogeneousIdeal π :=
  β¨I.toIdeal.radical, I.IsHomogeneous.radicalβ©

@[simp]
theorem HomogeneousIdeal.coe_radical (I : HomogeneousIdeal π) : I.radical.toIdeal = I.toIdeal.radical :=
  rfl

