import Mathbin.Data.Zmod.Basic 
import Mathbin.GroupTheory.Index 
import Mathbin.GroupTheory.GroupAction.ConjAct 
import Mathbin.GroupTheory.Perm.CycleType 
import Mathbin.GroupTheory.QuotientGroup

/-!
# p-groups

This file contains a proof that if `G` is a `p`-group acting on a finite set `α`,
then the number of fixed points of the action is congruent mod `p` to the cardinality of `α`.
It also contains proofs of some corollaries of this lemma about existence of fixed points.
-/


open_locale BigOperators

open Fintype MulAction

variable (p : ℕ) (G : Type _) [Groupₓ G]

/-- A p-group is a group in which every element has prime power order -/
def IsPGroup : Prop :=
  ∀ g : G, ∃ k : ℕ, (g^p^k) = 1

variable {p} {G}

namespace IsPGroup

theorem iff_order_of [hp : Fact p.prime] : IsPGroup p G ↔ ∀ g : G, ∃ k : ℕ, orderOf g = (p^k) :=
  forall_congrₓ
    fun g =>
      ⟨fun ⟨k, hk⟩ =>
          exists_imp_exists
            (by 
              exact fun j => Exists.snd)
            ((Nat.dvd_prime_pow hp.out).mp (order_of_dvd_of_pow_eq_one hk)),
        exists_imp_exists
          fun k hk =>
            by 
              rw [←hk, pow_order_of_eq_one]⟩

theorem of_card [Fintype G] {n : ℕ} (hG : card G = (p^n)) : IsPGroup p G :=
  fun g =>
    ⟨n,
      by 
        rw [←hG, pow_card_eq_one]⟩

theorem of_bot : IsPGroup p (⊥ : Subgroup G) :=
  of_card (Subgroup.card_bot.trans (pow_zeroₓ p).symm)

-- error in GroupTheory.PGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem iff_card
[fact p.prime]
[fintype G] : «expr ↔ »(is_p_group p G, «expr∃ , »((n : exprℕ()), «expr = »(card G, «expr ^ »(p, n)))) :=
begin
  have [ident hG] [":", expr «expr < »(0, card G)] [":=", expr card_pos_iff.mpr has_one.nonempty],
  refine [expr ⟨λ h, _, λ ⟨n, hn⟩, of_card hn⟩],
  suffices [] [":", expr ∀ q «expr ∈ » nat.factors (card G), «expr = »(q, p)],
  { use [expr (card G).factors.length],
    rw ["[", "<-", expr list.prod_repeat, ",", "<-", expr list.eq_repeat_of_mem this, ",", expr nat.prod_factors hG, "]"] [] },
  intros [ident q, ident hq],
  obtain ["⟨", ident hq1, ",", ident hq2, "⟩", ":=", expr (nat.mem_factors hG).mp hq],
  haveI [] [":", expr fact q.prime] [":=", expr ⟨hq1⟩],
  obtain ["⟨", ident g, ",", ident hg, "⟩", ":=", expr equiv.perm.exists_prime_order_of_dvd_card q hq2],
  obtain ["⟨", ident k, ",", ident hk, "⟩", ":=", expr iff_order_of.mp h g],
  exact [expr (hq1.pow_eq_iff.mp (hg.symm.trans hk).symm).1.symm]
end

section GIsPGroup

variable (hG : IsPGroup p G)

include hG

theorem of_injective {H : Type _} [Groupₓ H] (ϕ : H →* G) (hϕ : Function.Injective ϕ) : IsPGroup p H :=
  by 
    simpRw [IsPGroup, ←hϕ.eq_iff, ϕ.map_pow, ϕ.map_one]
    exact fun h => hG (ϕ h)

theorem to_subgroup (H : Subgroup G) : IsPGroup p H :=
  hG.of_injective H.subtype Subtype.coe_injective

theorem of_surjective {H : Type _} [Groupₓ H] (ϕ : G →* H) (hϕ : Function.Surjective ϕ) : IsPGroup p H :=
  by 
    refine' fun h => Exists.elim (hϕ h) fun g hg => exists_imp_exists (fun k hk => _) (hG g)
    rw [←hg, ←ϕ.map_pow, hk, ϕ.map_one]

theorem to_quotient (H : Subgroup G) [H.normal] : IsPGroup p (QuotientGroup.Quotient H) :=
  hG.of_surjective (QuotientGroup.mk' H) Quotientₓ.surjective_quotient_mk'

theorem of_equiv {H : Type _} [Groupₓ H] (ϕ : G ≃* H) : IsPGroup p H :=
  hG.of_surjective ϕ.to_monoid_hom ϕ.surjective

variable [hp : Fact p.prime]

include hp

theorem index (H : Subgroup G) [Fintype (QuotientGroup.Quotient H)] : ∃ n : ℕ, H.index = (p^n) :=
  by 
    obtain ⟨n, hn⟩ := iff_card.mp (hG.to_quotient H.normal_core)
    obtain ⟨k, hk1, hk2⟩ :=
      (Nat.dvd_prime_pow hp.out).mp
        ((congr_argₓ _ (H.normal_core.index_eq_card.trans hn)).mp (Subgroup.index_dvd_of_le H.normal_core_le))
    exact ⟨k, hk2⟩

variable {α : Type _} [MulAction G α]

-- error in GroupTheory.PGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem card_orbit
(a : α)
[fintype (orbit G a)] : «expr∃ , »((n : exprℕ()), «expr = »(card (orbit G a), «expr ^ »(p, n))) :=
begin
  let [ident ϕ] [] [":=", expr orbit_equiv_quotient_stabilizer G a],
  haveI [] [] [":=", expr fintype.of_equiv (orbit G a) ϕ],
  rw ["[", expr card_congr ϕ, ",", "<-", expr subgroup.index_eq_card, "]"] [],
  exact [expr hG.index (stabilizer G a)]
end

variable (α) [Fintype α] [Fintype (fixed_points G α)]

-- error in GroupTheory.PGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `G` is a `p`-group acting on a finite set `α`, then the number of fixed points
  of the action is congruent mod `p` to the cardinality of `α` -/
theorem card_modeq_card_fixed_points : «expr ≡ [MOD ]»(card α, card (fixed_points G α), p) :=
begin
  classical,
  calc
    «expr = »(card α, card «exprΣ , »((y : quotient (orbit_rel G α)), {x // «expr = »(quotient.mk' x, y)})) : card_congr (equiv.sigma_preimage_equiv (@quotient.mk' _ (orbit_rel G α))).symm
    «expr = »(..., «expr∑ , »((a : quotient (orbit_rel G α)), card {x // «expr = »(quotient.mk' x, a)})) : card_sigma _
    «expr ≡ [MOD ]»(..., «expr∑ , »((a : fixed_points G α), 1), p) : _
    «expr = »(..., _) : by simp [] [] [] [] [] []; refl,
  rw ["[", "<-", expr zmod.eq_iff_modeq_nat p, ",", expr nat.cast_sum, ",", expr nat.cast_sum, "]"] [],
  have [ident key] [":", expr ∀
   x, «expr = »(card {y // «expr = »((quotient.mk' y : quotient (orbit_rel G α)), quotient.mk' x)}, card (orbit G x))] [":=", expr λ
   x, by simp [] [] ["only"] ["[", expr quotient.eq', "]"] [] []; congr],
  refine [expr eq.symm (finset.sum_bij_ne_zero (λ
     a
     _
     _, quotient.mk' a.1) (λ
     _
     _
     _, finset.mem_univ _) (λ
     a₁
     a₂
     _
     _
     _
     _
     h, subtype.eq ((mem_fixed_points' α).mp a₂.2 a₁.1 (quotient.exact' h))) (λ
     b, quotient.induction_on' b (λ
      b
      _
      hb, _)) (λ a ha _, by { rw ["[", expr key, ",", expr mem_fixed_points_iff_card_orbit_eq_one.mp a.2, "]"] [] }))],
  obtain ["⟨", ident k, ",", ident hk, "⟩", ":=", expr hG.card_orbit b],
  have [] [":", expr «expr = »(k, 0)] [":=", expr nat.le_zero_iff.1 (nat.le_of_lt_succ (lt_of_not_ge (mt (pow_dvd_pow p) (by rwa ["[", expr pow_one, ",", "<-", expr hk, ",", "<-", expr nat.modeq_zero_iff_dvd, ",", "<-", expr zmod.eq_iff_modeq_nat, ",", "<-", expr key, "]"] []))))],
  exact [expr ⟨⟨b, «expr $ »(mem_fixed_points_iff_card_orbit_eq_one.2, by rw ["[", expr hk, ",", expr this, ",", expr pow_zero, "]"] [])⟩, finset.mem_univ _, ne_of_eq_of_ne nat.cast_one one_ne_zero, rfl⟩]
end

/-- If a p-group acts on `α` and the cardinality of `α` is not a multiple
  of `p` then the action has a fixed point. -/
theorem nonempty_fixed_point_of_prime_not_dvd_card (hpα : ¬p ∣ card α) : (fixed_points G α).Nonempty :=
  @Set.nonempty_of_nonempty_subtype _ _
    (by 
      rw [←card_pos_iff, pos_iff_ne_zero]
      contrapose! hpα 
      rw [←Nat.modeq_zero_iff_dvd, ←hpα]
      exact hG.card_modeq_card_fixed_points α)

/-- If a p-group acts on `α` and the cardinality of `α` is a multiple
  of `p`, and the action has one fixed point, then it has another fixed point. -/
theorem exists_fixed_point_of_prime_dvd_card_of_fixed_point (hpα : p ∣ card α) {a : α} (ha : a ∈ fixed_points G α) :
  ∃ b, b ∈ fixed_points G α ∧ a ≠ b :=
  have hpf : p ∣ card (fixed_points G α) :=
    Nat.modeq_zero_iff_dvd.mp ((hG.card_modeq_card_fixed_points α).symm.trans hpα.modeq_zero_nat)
  have hα : 1 < card (fixed_points G α) :=
    (Fact.out p.prime).one_lt.trans_le (Nat.le_of_dvdₓ (card_pos_iff.2 ⟨⟨a, ha⟩⟩) hpf)
  let ⟨⟨b, hb⟩, hba⟩ := exists_ne_of_one_lt_card hα ⟨a, ha⟩
  ⟨b, hb,
    fun hab =>
      hba
        (by 
          simpRw [hab])⟩

-- error in GroupTheory.PGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem center_nontrivial [nontrivial G] [fintype G] : nontrivial (subgroup.center G) :=
begin
  classical,
  have [] [] [":=", expr (hG.of_equiv conj_act.to_conj_act).exists_fixed_point_of_prime_dvd_card_of_fixed_point G],
  rw [expr conj_act.fixed_points_eq_center] ["at", ident this],
  obtain ["⟨", ident g, ",", ident hg, "⟩", ":=", expr this _ (subgroup.center G).one_mem],
  { exact [expr ⟨⟨1, ⟨g, hg.1⟩, mt subtype.ext_iff.mp hg.2⟩⟩] },
  { obtain ["⟨", ident n, ",", ident hn, "⟩", ":=", expr is_p_group.iff_card.mp hG],
    rw [expr hn] [],
    apply [expr dvd_pow_self],
    rintro [ident rfl],
    exact [expr fintype.one_lt_card.ne' hn] }
end

-- error in GroupTheory.PGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem bot_lt_center [nontrivial G] [fintype G] : «expr < »(«expr⊥»(), subgroup.center G) :=
begin
  haveI [] [] [":=", expr center_nontrivial hG],
  classical,
  exact [expr bot_lt_iff_ne_bot.mpr ((subgroup.center G).one_lt_card_iff_ne_bot.mp fintype.one_lt_card)]
end

end GIsPGroup

theorem to_le {H K : Subgroup G} (hK : IsPGroup p K) (hHK : H ≤ K) : IsPGroup p H :=
  hK.of_injective (Subgroup.inclusion hHK) fun a b h => Subtype.ext (show _ from Subtype.ext_iff.mp h)

theorem to_inf_left {H K : Subgroup G} (hH : IsPGroup p H) : IsPGroup p (H⊓K : Subgroup G) :=
  hH.to_le inf_le_left

theorem to_inf_right {H K : Subgroup G} (hK : IsPGroup p K) : IsPGroup p (H⊓K : Subgroup G) :=
  hK.to_le inf_le_right

theorem map {H : Subgroup G} (hH : IsPGroup p H) {K : Type _} [Groupₓ K] (ϕ : G →* K) : IsPGroup p (H.map ϕ) :=
  by 
    rw [←H.subtype_range, MonoidHom.map_range]
    exact hH.of_surjective (ϕ.restrict H).range_restrict (ϕ.restrict H).range_restrict_surjective

theorem comap_of_ker_is_p_group {H : Subgroup G} (hH : IsPGroup p H) {K : Type _} [Groupₓ K] (ϕ : K →* G)
  (hϕ : IsPGroup p ϕ.ker) : IsPGroup p (H.comap ϕ) :=
  by 
    intro g 
    obtain ⟨j, hj⟩ := hH ⟨ϕ g.1, g.2⟩
    rw [Subtype.ext_iff, H.coe_pow, Subtype.coe_mk, ←ϕ.map_pow] at hj 
    obtain ⟨k, hk⟩ := hϕ ⟨g.1^p^j, hj⟩
    rwa [Subtype.ext_iff, ϕ.ker.coe_pow, Subtype.coe_mk, ←pow_mulₓ, ←pow_addₓ] at hk 
    exact
      ⟨j+k,
        by 
          rwa [Subtype.ext_iff, (H.comap ϕ).coe_pow]⟩

theorem comap_of_injective {H : Subgroup G} (hH : IsPGroup p H) {K : Type _} [Groupₓ K] (ϕ : K →* G)
  (hϕ : Function.Injective ϕ) : IsPGroup p (H.comap ϕ) :=
  by 
    apply hH.comap_of_ker_is_p_group ϕ 
    rw [ϕ.ker_eq_bot_iff.mpr hϕ]
    exact IsPGroup.of_bot

theorem to_sup_of_normal_right {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K) [K.normal] :
  IsPGroup p (H⊔K : Subgroup G) :=
  by 
    rw [←QuotientGroup.ker_mk K, ←Subgroup.comap_map_eq]
    apply (hH.map (QuotientGroup.mk' K)).comap_of_ker_is_p_group 
    rwa [QuotientGroup.ker_mk]

theorem to_sup_of_normal_left {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K) [H.normal] :
  IsPGroup p (H⊔K : Subgroup G) :=
  (congr_argₓ (fun H : Subgroup G => IsPGroup p H) sup_comm).mp (to_sup_of_normal_right hK hH)

theorem to_sup_of_normal_right' {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K) (hHK : H ≤ K.normalizer) :
  IsPGroup p (H⊔K : Subgroup G) :=
  let hHK' :=
    to_sup_of_normal_right (hH.of_equiv (Subgroup.comapSubtypeEquivOfLe hHK).symm)
      (hK.of_equiv (Subgroup.comapSubtypeEquivOfLe Subgroup.le_normalizer).symm)
  ((congr_argₓ (fun H : Subgroup K.normalizer => IsPGroup p H)
            (Subgroup.sup_subgroup_of_eq hHK Subgroup.le_normalizer)).mp
        hHK').ofEquiv
    (Subgroup.comapSubtypeEquivOfLe (sup_le hHK Subgroup.le_normalizer))

theorem to_sup_of_normal_left' {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K) (hHK : K ≤ H.normalizer) :
  IsPGroup p (H⊔K : Subgroup G) :=
  (congr_argₓ (fun H : Subgroup G => IsPGroup p H) sup_comm).mp (to_sup_of_normal_right' hK hH hHK)

end IsPGroup

