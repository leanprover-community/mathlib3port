/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathbin.GroupTheory.Complement
import Mathbin.GroupTheory.GroupAction.Basic
import Mathbin.GroupTheory.Sylow

/-!
# The Schur-Zassenhaus Theorem

In this file we prove the Schur-Zassenhaus theorem.

## Main results

- `exists_right_complement'_of_coprime` : The **Schur-Zassenhaus** theorem:
  If `H : subgroup G` is normal and has order coprime to its index,
  then there exists a subgroup `K` which is a (right) complement of `H`.
- `exists_left_complement'_of_coprime`  The **Schur-Zassenhaus** theorem:
  If `H : subgroup G` is normal and has order coprime to its index,
  then there exists a subgroup `K` which is a (left) complement of `H`.
-/


open_locale BigOperators

namespace Subgroup

section SchurZassenhausAbelian

variable {G : Type _} [Groupₓ G] {H : Subgroup G}

@[to_additive]
instance : MulAction G (LeftTransversals (H : Set G)) where
  smul := fun g T =>
    ⟨LeftCoset g T,
      mem_left_transversals_iff_exists_unique_inv_mul_mem.mpr fun g' => by
        obtain ⟨t, ht1, ht2⟩ := mem_left_transversals_iff_exists_unique_inv_mul_mem.mp T.2 (g⁻¹ * g')
        simp_rw [← mul_assoc, ← mul_inv_rev]  at ht1 ht2
        refine' ⟨⟨g * t, mem_left_coset g t.2⟩, ht1, _⟩
        rintro ⟨_, t', ht', rfl⟩ h
        exact Subtype.ext ((mul_right_injₓ g).mpr (subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h)))⟩
  one_smul := fun T => Subtype.ext (one_left_coset T)
  mul_smul := fun g g' T => Subtype.ext (left_coset_assoc (↑T) g g').symm

theorem smul_symm_apply_eq_mul_symm_apply_inv_smul (g : G) (α : LeftTransversals (H : Set G)) (q : G ⧸ H) :
    ↑((Equivₓ.ofBijective _ (mem_left_transversals_iff_bijective.mp (g • α).2)).symm q) =
      g * (Equivₓ.ofBijective _ (mem_left_transversals_iff_bijective.mp α.2)).symm (g⁻¹ • q : G ⧸ H) :=
  by
  let w := Equivₓ.ofBijective _ (mem_left_transversals_iff_bijective.mp α.2)
  let y := Equivₓ.ofBijective _ (mem_left_transversals_iff_bijective.mp (g • α).2)
  change ↑(y.symm q) = ↑(⟨_, mem_left_coset g (Subtype.mem _)⟩ : (g • α).1)
  refine' subtype.ext_iff.mp (y.symm_apply_eq.mpr _)
  change q = g • w (w.symm (g⁻¹ • q : G ⧸ H))
  rw [Equivₓ.apply_symm_apply, ← mul_smul, mul_inv_selfₓ, one_smul]

variable [IsCommutative H] [Fintype (G ⧸ H)]

variable (α β γ : LeftTransversals (H : Set G))

/-- The difference of two left transversals -/
@[to_additive "The difference of two left transversals"]
noncomputable def diff [hH : Normal H] : H :=
  let α' := (Equivₓ.ofBijective _ (mem_left_transversals_iff_bijective.mp α.2)).symm
  let β' := (Equivₓ.ofBijective _ (mem_left_transversals_iff_bijective.mp β.2)).symm
  ∏ q : G ⧸ H,
    ⟨α' q * (β' q)⁻¹, hH.mem_comm (Quotientₓ.exact' ((β'.symm_apply_apply q).trans (α'.symm_apply_apply q).symm))⟩

@[to_additive]
theorem diff_mul_diff [Normal H] : diff α β * diff β γ = diff α γ :=
  Finset.prod_mul_distrib.symm.trans
    (Finset.prod_congr rfl fun x hx =>
      Subtype.ext
        (by
          rw [coe_mul, coe_mk, coe_mk, coe_mk, mul_assoc, inv_mul_cancel_leftₓ]))

@[to_additive]
theorem diff_self [Normal H] : diff α α = 1 :=
  mul_right_eq_self.mp (diff_mul_diff α α α)

@[to_additive]
theorem diff_inv [Normal H] : (diff α β)⁻¹ = diff β α :=
  inv_eq_of_mul_eq_oneₓ ((diff_mul_diff α β α).trans (diff_self α))

theorem smul_diff_smul [hH : Normal H] (g : G) :
    diff (g • α) (g • β) = ⟨g * diff α β * g⁻¹, hH.conj_mem (diff α β).1 (diff α β).2 g⟩ := by
  let ϕ : H →* H :=
    { toFun := fun h => ⟨g * h * g⁻¹, hH.conj_mem h.1 h.2 g⟩,
      map_one' :=
        Subtype.ext
          (by
            rw [coe_mk, coe_one, mul_oneₓ, mul_inv_selfₓ]),
      map_mul' := fun h₁ h₂ =>
        Subtype.ext
          (by
            rw [coe_mk, coe_mul, coe_mul, coe_mk, coe_mk, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc,
              inv_mul_cancel_leftₓ]) }
  refine'
    Eq.trans
      (Finset.prod_bij' (fun q _ => (↑g)⁻¹ * q) (fun _ _ => Finset.mem_univ _) (fun q _ => Subtype.ext _)
        (fun q _ => ↑g * q) (fun _ _ => Finset.mem_univ _) (fun q _ => mul_inv_cancel_left g q) fun q _ =>
        inv_mul_cancel_leftₓ g q)
      (ϕ.map_prod _ _).symm
  change _ * _ = g * (_ * _) * g⁻¹
  simp_rw [smul_symm_apply_eq_mul_symm_apply_inv_smul, mul_inv_rev, mul_assoc]
  rfl

theorem smul_diff [H.Normal] (h : H) : diff (h • α) β = h ^ H.index * diff α β := by
  rw [diff, diff, index_eq_card, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine' Finset.prod_congr rfl fun q _ => _
  rw [Subtype.ext_iff, coe_mul, coe_mk, coe_mk, ← mul_assoc, mul_right_cancel_iffₓ]
  rw [show h • α = (h : G) • α from rfl, smul_symm_apply_eq_mul_symm_apply_inv_smul]
  rw [mul_left_cancel_iffₓ, ← Subtype.ext_iff, Equivₓ.apply_eq_iff_eq, inv_smul_eq_iff]
  exact self_eq_mul_left.mpr ((QuotientGroup.eq_one_iff _).mpr h.2)

variable (H)

instance setoidDiff [H.Normal] : Setoidₓ (LeftTransversals (H : Set G)) :=
  Setoidₓ.mk (fun α β => diff α β = 1)
    ⟨fun α => diff_self α, fun α β h₁ => by
      rw [← diff_inv, h₁, one_inv], fun α β γ h₁ h₂ => by
      rw [← diff_mul_diff, h₁, h₂, one_mulₓ]⟩

/-- The quotient of the transversals of an abelian normal `N` by the `diff` relation -/
def QuotientDiff [H.Normal] :=
  Quotientₓ H.setoidDiff

instance [H.Normal] : Inhabited H.QuotientDiff :=
  Quotientₓ.inhabited _

variable {H}

instance [H.Normal] : MulAction G H.QuotientDiff where
  smul := fun g =>
    Quotientₓ.map (fun α => g • α) fun α β h =>
      (smul_diff_smul α β g).trans (Subtype.ext (mul_inv_eq_one.mpr (mul_right_eq_self.mpr (Subtype.ext_iff.mp h))))
  mul_smul := fun g₁ g₂ q => Quotientₓ.induction_on q fun α => congr_argₓ Quotientₓ.mk (mul_smul g₁ g₂ α)
  one_smul := fun q => Quotientₓ.induction_on q fun α => congr_argₓ Quotientₓ.mk (one_smul G α)

variable [Fintype H]

theorem exists_smul_eq [H.Normal] (α β : H.QuotientDiff) (hH : Nat.Coprime (Fintype.card H) H.index) :
    ∃ h : H, h • α = β :=
  Quotientₓ.induction_on α
    (Quotientₓ.induction_on β fun β α =>
      exists_imp_exists (fun n => Quotientₓ.sound)
        ⟨(powCoprime hH).symm (diff α β)⁻¹, by
          change diff ((_ : H) • _) _ = 1
          rw [smul_diff]
          change powCoprime hH ((powCoprime hH).symm (diff α β)⁻¹) * diff α β = 1
          rw [Equivₓ.apply_symm_apply, inv_mul_selfₓ]⟩)

theorem smul_left_injective [H.Normal] (α : H.QuotientDiff) (hH : Nat.Coprime (Fintype.card H) H.index) :
    Function.Injective fun h : H => h • α := fun h₁ h₂ => by
  refine' Quotientₓ.induction_on α fun α hα => _
  replace hα : diff (h₁ • α) (h₂ • α) = 1 := Quotientₓ.exact hα
  rw [smul_diff, ← diff_inv, smul_diff, diff_self, mul_oneₓ, mul_inv_eq_one] at hα
  exact (powCoprime hH).Injective hα

theorem is_complement'_stabilizer_of_coprime [Fintype G] [H.Normal] {α : H.QuotientDiff}
    (hH : Nat.Coprime (Fintype.card H) H.index) : IsComplement' H (MulAction.stabilizer G α) := by
  classical
  let ϕ : H ≃ MulAction.Orbit G α :=
    Equivₓ.ofBijective (fun h => ⟨h • α, h, rfl⟩)
      ⟨fun h₁ h₂ hh => smul_left_injective α hH (subtype.ext_iff.mp hh), fun β =>
        exists_imp_exists (fun h hh => Subtype.ext hh) (exists_smul_eq α β hH)⟩
  have key := card_eq_card_quotient_mul_card_subgroup (MulAction.stabilizer G α)
  rw [← Fintype.card_congr (ϕ.trans (MulAction.orbitEquivQuotientStabilizer G α))] at key
  apply is_complement'_of_coprime key.symm
  rw [card_eq_card_quotient_mul_card_subgroup H, mul_comm, mul_right_inj'] at key
  · rwa [← key, ← index_eq_card]
    
  · rw [← pos_iff_ne_zero, Fintype.card_pos_iff]
    infer_instance
    

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem exists_right_complement'_of_coprime_aux [Fintype G] [H.Normal]
    (hH : Nat.Coprime (Fintype.card H) H.index) : ∃ K : Subgroup G, IsComplement' H K :=
  nonempty_of_inhabited.elim fun α : H.QuotientDiff =>
    ⟨MulAction.stabilizer G α, is_complement'_stabilizer_of_coprime hH⟩

end SchurZassenhausAbelian

open_locale Classical

universe u

namespace SchurZassenhausInduction

/-! ## Proof of the Schur-Zassenhaus theorem

In this section, we prove the Schur-Zassenhaus theorem.
The proof is by contradiction. We assume that `G` is a minimal counterexample to the theorem.
-/


variable {G : Type u} [Groupₓ G] [Fintype G] {N : Subgroup G} [Normal N] (h1 : Nat.Coprime (Fintype.card N) N.index)
  (h2 :
    ∀ G' : Type u [Groupₓ G'] [Fintype G'],
      ∀ hG'3 : Fintype.card G' < Fintype.card G {N' : Subgroup G'} [N'.Normal] hN :
        Nat.Coprime (Fintype.card N') N'.index, ∃ H' : Subgroup G', is_complement' N' H')
  (h3 : ∀ H : Subgroup G, ¬IsComplement' N H)

include h1 h2 h3

/-! We will arrive at a contradiction via the following steps:
 * step 0: `N` (the normal Hall subgroup) is nontrivial.
 * step 1: If `K` is a subgroup of `G` with `K ⊔ N = ⊤`, then `K = ⊤`.
 * step 2: `N` is a minimal normal subgroup, phrased in terms of subgroups of `G`.
 * step 3: `N` is a minimal normal subgroup, phrased in terms of subgroups of `N`.
 * step 4: `p` (`min_fact (fintype.card N)`) is prime (follows from step0).
 * step 5: `P` (a Sylow `p`-subgroup of `N`) is nontrivial.
 * step 6: `N` is a `p`-group (applies step 1 to the normalizer of `P` in `G`).
 * step 7: `N` is abelian (applies step 3 to the center of `N`).
-/


/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
@[nolint unused_arguments]
private theorem step0 : N ≠ ⊥ := by
  rintro rfl
  exact h3 ⊤ is_complement'_bot_top

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step1 (K : Subgroup G) (hK : K⊔N = ⊤) : K = ⊤ := by
  contrapose! h3
  have h4 : (N.comap K.subtype).index = N.index := by
    rw [← N.relindex_top_right, ← hK]
    exact relindex_eq_relindex_sup K N
  have h5 : Fintype.card K < Fintype.card G := by
    rw [← K.index_mul_card]
    exact lt_mul_of_one_lt_left Fintype.card_pos (one_lt_index_of_ne_top h3)
  have h6 : Nat.Coprime (Fintype.card (N.comap K.subtype)) (N.comap K.subtype).index := by
    rw [h4]
    exact h1.coprime_dvd_left (card_comap_dvd_of_injective N K.subtype Subtype.coe_injective)
  obtain ⟨H, hH⟩ := h2 K h5 h6
  replace hH : Fintype.card (H.map K.subtype) = N.index :=
    ((Set.card_image_of_injective _ Subtype.coe_injective).trans
          (Nat.mul_left_injective Fintype.card_pos
            (hH.symm.card_mul.trans (N.comap K.subtype).index_mul_card.symm))).trans
      h4
  have h7 : Fintype.card N * Fintype.card (H.map K.subtype) = Fintype.card G := by
    rw [hH, ← N.index_mul_card, mul_comm]
  have h8 : (Fintype.card N).Coprime (Fintype.card (H.map K.subtype)) := by
    rwa [hH]
  exact ⟨H.map K.subtype, is_complement'_of_coprime h7 h8⟩

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step2 (K : Subgroup G) [K.Normal] (hK : K ≤ N) : K = ⊥ ∨ K = N := by
  have : Function.Surjective (QuotientGroup.mk' K) := Quotientₓ.surjective_quotient_mk'
  have h4 := step1 h1 h2 h3
  contrapose! h4
  have h5 : Fintype.card (G ⧸ K) < Fintype.card G := by
    rw [← index_eq_card, ← K.index_mul_card]
    refine' lt_mul_of_one_lt_right (Nat.pos_of_ne_zeroₓ index_ne_zero_of_fintype) (K.one_lt_card_iff_ne_bot.mpr h4.1)
  have h6 : Nat.Coprime (Fintype.card (N.map (QuotientGroup.mk' K))) (N.map (QuotientGroup.mk' K)).index := by
    have index_map :=
      N.index_map_eq this
        (by
          rwa [QuotientGroup.ker_mk])
    have index_pos : 0 < N.index := Nat.pos_of_ne_zeroₓ index_ne_zero_of_fintype
    rw [index_map]
    refine' h1.coprime_dvd_left _
    rw [← Nat.mul_dvd_mul_iff_left index_pos, index_mul_card, ← index_map, index_mul_card]
    exact K.card_quotient_dvd_card
  obtain ⟨H, hH⟩ := h2 (G ⧸ K) h5 h6
  refine' ⟨H.comap (QuotientGroup.mk' K), _, _⟩
  · have key : (N.map (QuotientGroup.mk' K)).comap (QuotientGroup.mk' K) = N := by
      refine' comap_map_eq_self _
      rwa [QuotientGroup.ker_mk]
    rwa [← key, comap_sup_eq, hH.symm.sup_eq_top, comap_top]
    
  · rw [← comap_top (QuotientGroup.mk' K)]
    intro hH'
    rw [comap_injective this hH', is_complement'_top_right, map_eq_bot_iff, QuotientGroup.ker_mk] at hH
    · exact h4.2 (le_antisymmₓ hK hH)
      
    

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step3 (K : Subgroup N) [(K.map N.Subtype).Normal] : K = ⊥ ∨ K = ⊤ := by
  have key := step2 h1 h2 h3 (K.map N.subtype) K.map_subtype_le
  rw [← map_bot N.subtype] at key
  conv at key => congr skip rhs rw [← N.subtype_range, N.subtype.range_eq_map]
  have inj := map_injective (show Function.Injective N.subtype from Subtype.coe_injective)
  rwa [inj.eq_iff, inj.eq_iff] at key

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step4 : (Fintype.card N).minFac.Prime :=
  Nat.min_fac_prime (N.one_lt_card_iff_ne_bot.mpr (step0 h1 h2 h3)).ne'

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step5 {P : Sylow (Fintype.card N).minFac N} : P.1 ≠ ⊥ :=
  have : Fact (Fintype.card N).minFac.Prime := ⟨step4 h1 h2 h3⟩
  P.ne_bot_of_dvd_card (Fintype.card N).min_fac_dvd

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step6 : IsPGroup (Fintype.card N).minFac N := by
  have : Fact (Fintype.card N).minFac.Prime := ⟨step4 h1 h2 h3⟩
  refine' sylow.nonempty.elim fun P => P.2.ofSurjective P.1.Subtype _
  rw [← MonoidHom.range_top_iff_surjective, subtype_range]
  have : (P.1.map N.subtype).Normal :=
    normalizer_eq_top.mp (step1 h1 h2 h3 (P.1.map N.subtype).normalizer P.normalizer_sup_eq_top)
  exact (step3 h1 h2 h3 P.1).resolve_left (step5 h1 h2 h3)

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
theorem step7 : IsCommutative N := by
  have := N.bot_or_nontrivial.resolve_left (step0 h1 h2 h3)
  have : Fact (Fintype.card N).minFac.Prime := ⟨step4 h1 h2 h3⟩
  exact
    ⟨⟨fun g h =>
        eq_top_iff.mp ((step3 h1 h2 h3 N.center).resolve_left (step6 h1 h2 h3).bot_lt_center.ne') (mem_top h) g⟩⟩

end SchurZassenhausInduction

variable {n : ℕ} {G : Type u} [Groupₓ G]

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem exists_right_complement'_of_coprime_aux' [Fintype G] (hG : Fintype.card G = n) {N : Subgroup G}
    [N.Normal] (hN : Nat.Coprime (Fintype.card N) N.index) : ∃ H : Subgroup G, IsComplement' N H := by
  revert G
  apply Nat.strong_induction_onₓ n
  rintro n ih G _ _ rfl N _ hN
  refine' not_forall_not.mp fun h3 => _
  have :=
    schur_zassenhaus_induction.step7 hN
      (fun G' _ _ hG' => by
        apply ih _ hG'
        rfl)
      h3
  exact not_exists_of_forall_not h3 (exists_right_complement'_of_coprime_aux hN)

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (right) complement of `H`. -/
theorem exists_right_complement'_of_coprime_of_fintype [Fintype G] {N : Subgroup G} [N.Normal]
    (hN : Nat.Coprime (Fintype.card N) N.index) : ∃ H : Subgroup G, IsComplement' N H :=
  exists_right_complement'_of_coprime_aux' rfl hN

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (right) complement of `H`. -/
theorem exists_right_complement'_of_coprime {N : Subgroup G} [N.Normal] (hN : Nat.Coprime (Nat.card N) N.index) :
    ∃ H : Subgroup G, IsComplement' N H := by
  by_cases' hN1 : Nat.card N = 0
  · rw [hN1, Nat.coprime_zero_leftₓ, index_eq_one] at hN
    rw [hN]
    exact ⟨⊥, is_complement'_top_bot⟩
    
  by_cases' hN2 : N.index = 0
  · rw [hN2, Nat.coprime_zero_rightₓ] at hN
    have := (cardinal.to_nat_eq_one_iff_unique.mp hN).1
    rw [N.eq_bot_of_subsingleton]
    exact ⟨⊤, is_complement'_bot_top⟩
    
  have hN3 : Nat.card G ≠ 0 := by
    rw [← N.card_mul_index]
    exact mul_ne_zero hN1 hN2
  have := (cardinal.lt_omega_iff_fintype.mp (lt_of_not_geₓ (mt Cardinal.to_nat_apply_of_omega_le hN3))).some
  rw [Nat.card_eq_fintype_card] at hN
  exact exists_right_complement'_of_coprime_of_fintype hN

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (left) complement of `H`. -/
theorem exists_left_complement'_of_coprime_of_fintype [Fintype G] {N : Subgroup G} [N.Normal]
    (hN : Nat.Coprime (Fintype.card N) N.index) : ∃ H : Subgroup G, IsComplement' H N :=
  Exists.impₓ (fun _ => IsComplement'.symm) (exists_right_complement'_of_coprime_of_fintype hN)

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (left) complement of `H`. -/
theorem exists_left_complement'_of_coprime {N : Subgroup G} [N.Normal] (hN : Nat.Coprime (Nat.card N) N.index) :
    ∃ H : Subgroup G, IsComplement' H N :=
  Exists.impₓ (fun _ => IsComplement'.symm) (exists_right_complement'_of_coprime hN)

end Subgroup

