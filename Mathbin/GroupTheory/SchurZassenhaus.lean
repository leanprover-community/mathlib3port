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

@[toAdditive]
instance : MulAction G (left_transversals (H : Set G)) :=
  { smul :=
      fun g T =>
        ⟨LeftCoset g T,
          mem_left_transversals_iff_exists_unique_inv_mul_mem.mpr
            fun g' =>
              by 
                obtain ⟨t, ht1, ht2⟩ := mem_left_transversals_iff_exists_unique_inv_mul_mem.mp T.2 (g⁻¹*g')
                simpRw [←mul_assocₓ, ←mul_inv_rev]  at ht1 ht2 
                refine' ⟨⟨g*t, mem_left_coset g t.2⟩, ht1, _⟩
                rintro ⟨_, t', ht', rfl⟩ h 
                exact Subtype.ext ((mul_right_injₓ g).mpr (subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h)))⟩,
    one_smul := fun T => Subtype.ext (one_left_coset T),
    mul_smul := fun g g' T => Subtype.ext (left_coset_assoc («expr↑ » T) g g').symm }

theorem smul_symm_apply_eq_mul_symm_apply_inv_smul (g : G) (α : left_transversals (H : Set G))
  (q : QuotientGroup.Quotient H) :
  «expr↑ » ((Equiv.ofBijective _ (mem_left_transversals_iff_bijective.mp (g • α).2)).symm q) =
    g*(Equiv.ofBijective _ (mem_left_transversals_iff_bijective.mp α.2)).symm (g⁻¹ • q : QuotientGroup.Quotient H) :=
  by 
    let w := Equiv.ofBijective _ (mem_left_transversals_iff_bijective.mp α.2)
    let y := Equiv.ofBijective _ (mem_left_transversals_iff_bijective.mp (g • α).2)
    change «expr↑ » (y.symm q) = «expr↑ » (⟨_, mem_left_coset g (Subtype.mem _)⟩ : (g • α).1)
    refine' subtype.ext_iff.mp (y.symm_apply_eq.mpr _)
    change q = g • w (w.symm (g⁻¹ • q : QuotientGroup.Quotient H))
    rw [Equiv.apply_symm_apply, ←mul_smul, mul_inv_selfₓ, one_smul]

variable [IsCommutative H] [Fintype (QuotientGroup.Quotient H)]

variable (α β γ : left_transversals (H : Set G))

/-- The difference of two left transversals -/
@[toAdditive "The difference of two left transversals"]
noncomputable def diff [hH : normal H] : H :=
  let α' := (Equiv.ofBijective _ (mem_left_transversals_iff_bijective.mp α.2)).symm 
  let β' := (Equiv.ofBijective _ (mem_left_transversals_iff_bijective.mp β.2)).symm
  ∏q : QuotientGroup.Quotient H,
    ⟨α' q*β' q⁻¹, hH.mem_comm (Quotientₓ.exact' ((β'.symm_apply_apply q).trans (α'.symm_apply_apply q).symm))⟩

@[toAdditive]
theorem diff_mul_diff [normal H] : (diff α β*diff β γ) = diff α γ :=
  Finset.prod_mul_distrib.symm.trans
    (Finset.prod_congr rfl
      fun x hx =>
        Subtype.ext
          (by 
            rw [coe_mul, coe_mk, coe_mk, coe_mk, mul_assocₓ, inv_mul_cancel_leftₓ]))

@[toAdditive]
theorem diff_self [normal H] : diff α α = 1 :=
  mul_right_eq_self.mp (diff_mul_diff α α α)

@[toAdditive]
theorem diff_inv [normal H] : diff α β⁻¹ = diff β α :=
  inv_eq_of_mul_eq_oneₓ ((diff_mul_diff α β α).trans (diff_self α))

theorem smul_diff_smul [hH : normal H] (g : G) :
  diff (g • α) (g • β) = ⟨(g*diff α β)*g⁻¹, hH.conj_mem (diff α β).1 (diff α β).2 g⟩ :=
  by 
    let ϕ : H →* H :=
      { toFun := fun h => ⟨(g*h)*g⁻¹, hH.conj_mem h.1 h.2 g⟩,
        map_one' :=
          Subtype.ext
            (by 
              rw [coe_mk, coe_one, mul_oneₓ, mul_inv_selfₓ]),
        map_mul' :=
          fun h₁ h₂ =>
            Subtype.ext
              (by 
                rw [coe_mk, coe_mul, coe_mul, coe_mk, coe_mk, mul_assocₓ, mul_assocₓ, mul_assocₓ, mul_assocₓ,
                  mul_assocₓ, inv_mul_cancel_leftₓ]) }
    refine'
      Eq.trans
        (Finset.prod_bij' (fun q _ => «expr↑ » g⁻¹*q) (fun _ _ => Finset.mem_univ _) (fun q _ => Subtype.ext _)
          (fun q _ => «expr↑ » g*q) (fun _ _ => Finset.mem_univ _) (fun q _ => mul_inv_cancel_left g q)
          fun q _ => inv_mul_cancel_leftₓ g q)
        (ϕ.map_prod _ _).symm 
    change (_*_) = (g*_*_)*g⁻¹
    simpRw [smul_symm_apply_eq_mul_symm_apply_inv_smul, mul_inv_rev, mul_assocₓ]
    rfl

theorem smul_diff [H.normal] (h : H) : diff (h • α) β = (h^H.index)*diff α β :=
  by 
    rw [diff, diff, index_eq_card, ←Finset.card_univ, ←Finset.prod_const, ←Finset.prod_mul_distrib]
    refine' Finset.prod_congr rfl fun q _ => _ 
    rw [Subtype.ext_iff, coe_mul, coe_mk, coe_mk, ←mul_assocₓ, mul_right_cancel_iffₓ]
    rw [show h • α = (h : G) • α from rfl, smul_symm_apply_eq_mul_symm_apply_inv_smul]
    rw [mul_left_cancel_iffₓ, ←Subtype.ext_iff, Equiv.apply_eq_iff_eq, inv_smul_eq_iff]
    exact self_eq_mul_left.mpr ((QuotientGroup.eq_one_iff _).mpr h.2)

variable (H)

instance setoid_diff [H.normal] : Setoidₓ (left_transversals (H : Set G)) :=
  Setoidₓ.mk (fun α β => diff α β = 1)
    ⟨fun α => diff_self α,
      fun α β h₁ =>
        by 
          rw [←diff_inv, h₁, one_inv],
      fun α β γ h₁ h₂ =>
        by 
          rw [←diff_mul_diff, h₁, h₂, one_mulₓ]⟩

/-- The quotient of the transversals of an abelian normal `N` by the `diff` relation -/
def quotient_diff [H.normal] :=
  Quotientₓ H.setoid_diff

instance [H.normal] : Inhabited H.quotient_diff :=
  Quotientₓ.inhabited

variable {H}

instance [H.normal] : MulAction G H.quotient_diff :=
  { smul :=
      fun g =>
        Quotientₓ.map (fun α => g • α)
          fun α β h =>
            (smul_diff_smul α β g).trans
              (Subtype.ext (mul_inv_eq_one.mpr (mul_right_eq_self.mpr (Subtype.ext_iff.mp h)))),
    mul_smul := fun g₁ g₂ q => Quotientₓ.induction_on q fun α => congr_argₓ Quotientₓ.mk (mul_smul g₁ g₂ α),
    one_smul := fun q => Quotientₓ.induction_on q fun α => congr_argₓ Quotientₓ.mk (one_smul G α) }

variable [Fintype H]

theorem exists_smul_eq [H.normal] (α β : H.quotient_diff) (hH : Nat.Coprime (Fintype.card H) H.index) :
  ∃ h : H, h • α = β :=
  Quotientₓ.induction_on α
    (Quotientₓ.induction_on β
      fun β α =>
        exists_imp_exists (fun n => Quotientₓ.sound)
          ⟨(powCoprime hH).symm (diff α β⁻¹),
            by 
              change diff ((_ : H) • _) _ = 1
              rw [smul_diff]
              change (powCoprime hH ((powCoprime hH).symm (diff α β⁻¹))*diff α β) = 1
              rw [Equiv.apply_symm_apply, inv_mul_selfₓ]⟩)

theorem smul_left_injective [H.normal] (α : H.quotient_diff) (hH : Nat.Coprime (Fintype.card H) H.index) :
  Function.Injective fun h : H => h • α :=
  fun h₁ h₂ =>
    by 
      refine' Quotientₓ.induction_on α fun α hα => _ 
      replace hα : diff (h₁ • α) (h₂ • α) = 1 := Quotientₓ.exact hα 
      rw [smul_diff, ←diff_inv, smul_diff, diff_self, mul_oneₓ, mul_inv_eq_one] at hα 
      exact (powCoprime hH).Injective hα

-- error in GroupTheory.SchurZassenhaus: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_complement'_stabilizer_of_coprime
[fintype G]
[H.normal]
{α : H.quotient_diff}
(hH : nat.coprime (fintype.card H) H.index) : is_complement' H (mul_action.stabilizer G α) :=
begin
  classical,
  let [ident ϕ] [":", expr «expr ≃ »(H, mul_action.orbit G α)] [":=", expr equiv.of_bijective (λ
    h, ⟨«expr • »(h, α), h, rfl⟩) ⟨λ
    h₁
    h₂
    hh, smul_left_injective α hH (subtype.ext_iff.mp hh), λ
    β, exists_imp_exists (λ h hh, subtype.ext hh) (exists_smul_eq α β hH)⟩],
  have [ident key] [] [":=", expr card_eq_card_quotient_mul_card_subgroup (mul_action.stabilizer G α)],
  rw ["<-", expr fintype.card_congr (ϕ.trans (mul_action.orbit_equiv_quotient_stabilizer G α))] ["at", ident key],
  apply [expr is_complement'_of_coprime key.symm],
  rw ["[", expr card_eq_card_quotient_mul_card_subgroup H, ",", expr mul_comm, ",", expr mul_right_inj', "]"] ["at", ident key],
  { rwa ["[", "<-", expr key, ",", "<-", expr index_eq_card, "]"] [] },
  { rw ["[", "<-", expr pos_iff_ne_zero, ",", expr fintype.card_pos_iff, "]"] [],
    apply_instance }
end

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem exists_right_complement'_of_coprime_aux [Fintype G] [H.normal]
  (hH : Nat.Coprime (Fintype.card H) H.index) : ∃ K : Subgroup G, is_complement' H K :=
  nonempty_of_inhabited.elim
    fun α : H.quotient_diff => ⟨MulAction.stabilizer G α, is_complement'_stabilizer_of_coprime hH⟩

end SchurZassenhausAbelian

open_locale Classical

universe u

namespace SchurZassenhausInduction

/-! ## Proof of the Schur-Zassenhaus theorem

In this section, we prove the Schur-Zassenhaus theorem.
The proof is by contradiction. We assume that `G` is a minimal counterexample to the theorem.
-/


variable {G : Type u} [Groupₓ G] [Fintype G] {N : Subgroup G} [normal N] (h1 : Nat.Coprime (Fintype.card N) N.index)
  (h2 :
    ∀ G' : Type u [Groupₓ G'] [Fintype G'],
      by 
        exact
          ∀ hG'3 : Fintype.card G' < Fintype.card G {N' : Subgroup G'} [N'.normal] hN :
            Nat.Coprime (Fintype.card N') N'.index, ∃ H' : Subgroup G', is_complement' N' H')
  (h3 : ∀ H : Subgroup G, ¬is_complement' N H)

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
private theorem step0 : N ≠ ⊥ :=
  by 
    (
      rintro rfl)
    exact h3 ⊤ is_complement'_bot_top

-- error in GroupTheory.SchurZassenhaus: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private
theorem step1 (K : subgroup G) (hK : «expr = »(«expr ⊔ »(K, N), «expr⊤»())) : «expr = »(K, «expr⊤»()) :=
begin
  contrapose ["!"] [ident h3],
  have [ident h4] [":", expr «expr = »((N.comap K.subtype).index, N.index)] [],
  { rw ["[", "<-", expr N.relindex_top_right, ",", "<-", expr hK, "]"] [],
    exact [expr relindex_eq_relindex_sup K N] },
  have [ident h5] [":", expr «expr < »(fintype.card K, fintype.card G)] [],
  { rw ["<-", expr K.index_mul_card] [],
    exact [expr lt_mul_of_one_lt_left fintype.card_pos (one_lt_index_of_ne_top h3)] },
  have [ident h6] [":", expr nat.coprime (fintype.card (N.comap K.subtype)) (N.comap K.subtype).index] [],
  { rw [expr h4] [],
    exact [expr h1.coprime_dvd_left (card_comap_dvd_of_injective N K.subtype subtype.coe_injective)] },
  obtain ["⟨", ident H, ",", ident hH, "⟩", ":=", expr h2 K h5 h6],
  replace [ident hH] [":", expr «expr = »(fintype.card (H.map K.subtype), N.index)] [":=", expr ((set.card_image_of_injective _ subtype.coe_injective).trans (nat.mul_left_injective fintype.card_pos (hH.symm.card_mul.trans (N.comap K.subtype).index_mul_card.symm))).trans h4],
  have [ident h7] [":", expr «expr = »(«expr * »(fintype.card N, fintype.card (H.map K.subtype)), fintype.card G)] [],
  { rw ["[", expr hH, ",", "<-", expr N.index_mul_card, ",", expr mul_comm, "]"] [] },
  have [ident h8] [":", expr (fintype.card N).coprime (fintype.card (H.map K.subtype))] [],
  { rwa [expr hH] [] },
  exact [expr ⟨H.map K.subtype, is_complement'_of_coprime h7 h8⟩]
end

-- error in GroupTheory.SchurZassenhaus: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private
theorem step2
(K : subgroup G)
[K.normal]
(hK : «expr ≤ »(K, N)) : «expr ∨ »(«expr = »(K, «expr⊥»()), «expr = »(K, N)) :=
begin
  have [] [":", expr function.surjective (quotient_group.mk' K)] [":=", expr quotient.surjective_quotient_mk'],
  have [ident h4] [] [":=", expr step1 h1 h2 h3],
  contrapose ["!"] [ident h4],
  have [ident h5] [":", expr «expr < »(fintype.card (quotient_group.quotient K), fintype.card G)] [],
  { rw ["[", "<-", expr index_eq_card, ",", "<-", expr K.index_mul_card, "]"] [],
    refine [expr lt_mul_of_one_lt_right (nat.pos_of_ne_zero index_ne_zero_of_fintype) (K.one_lt_card_iff_ne_bot.mpr h4.1)] },
  have [ident h6] [":", expr nat.coprime (fintype.card (N.map (quotient_group.mk' K))) (N.map (quotient_group.mk' K)).index] [],
  { have [ident index_map] [] [":=", expr N.index_map_eq this (by rwa [expr quotient_group.ker_mk] [])],
    have [ident index_pos] [":", expr «expr < »(0, N.index)] [":=", expr nat.pos_of_ne_zero index_ne_zero_of_fintype],
    rw [expr index_map] [],
    refine [expr h1.coprime_dvd_left _],
    rw ["[", "<-", expr nat.mul_dvd_mul_iff_left index_pos, ",", expr index_mul_card, ",", "<-", expr index_map, ",", expr index_mul_card, "]"] [],
    exact [expr K.card_quotient_dvd_card] },
  obtain ["⟨", ident H, ",", ident hH, "⟩", ":=", expr h2 (quotient_group.quotient K) h5 h6],
  refine [expr ⟨H.comap (quotient_group.mk' K), _, _⟩],
  { have [ident key] [":", expr «expr = »((N.map (quotient_group.mk' K)).comap (quotient_group.mk' K), N)] [],
    { refine [expr comap_map_eq_self _],
      rwa [expr quotient_group.ker_mk] [] },
    rwa ["[", "<-", expr key, ",", expr comap_sup_eq, ",", expr hH.symm.sup_eq_top, ",", expr comap_top, "]"] [] },
  { rw ["<-", expr comap_top (quotient_group.mk' K)] [],
    intro [ident hH'],
    rw ["[", expr comap_injective this hH', ",", expr is_complement'_top_right, ",", expr map_eq_bot_iff, ",", expr quotient_group.ker_mk, "]"] ["at", ident hH],
    { exact [expr h4.2 (le_antisymm hK hH)] } }
end

-- error in GroupTheory.SchurZassenhaus: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private
theorem step3
(K : subgroup N)
[(K.map N.subtype).normal] : «expr ∨ »(«expr = »(K, «expr⊥»()), «expr = »(K, «expr⊤»())) :=
begin
  have [ident key] [] [":=", expr step2 h1 h2 h3 (K.map N.subtype) K.map_subtype_le],
  rw ["<-", expr map_bot N.subtype] ["at", ident key],
  conv ["at", ident key] [] { congr,
    skip,
    to_rhs,
    rw ["[", "<-", expr N.subtype_range, ",", expr N.subtype.range_eq_map, "]"] },
  have [ident inj] [] [":=", expr map_injective (show function.injective N.subtype, from subtype.coe_injective)],
  rwa ["[", expr inj.eq_iff, ",", expr inj.eq_iff, "]"] ["at", ident key]
end

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step4 : (Fintype.card N).minFac.Prime :=
  Nat.min_fac_prime (N.one_lt_card_iff_ne_bot.mpr (step0 h1 h2 h3)).ne'

-- error in GroupTheory.SchurZassenhaus: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private
theorem step5 {P : sylow (fintype.card N).min_fac N} : «expr ≠ »(P.1, «expr⊥»()) :=
begin
  haveI [] [":", expr fact (fintype.card N).min_fac.prime] [":=", expr ⟨step4 h1 h2 h3⟩],
  exact [expr P.ne_bot_of_dvd_card (fintype.card N).min_fac_dvd]
end

-- error in GroupTheory.SchurZassenhaus: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private
theorem step6 : is_p_group (fintype.card N).min_fac N :=
begin
  haveI [] [":", expr fact (fintype.card N).min_fac.prime] [":=", expr ⟨step4 h1 h2 h3⟩],
  refine [expr sylow.nonempty.elim (λ P, P.2.of_surjective P.1.subtype _)],
  rw ["[", "<-", expr monoid_hom.range_top_iff_surjective, ",", expr subtype_range, "]"] [],
  haveI [] [":", expr (P.1.map N.subtype).normal] [":=", expr normalizer_eq_top.mp (step1 h1 h2 h3 (P.1.map N.subtype).normalizer P.normalizer_sup_eq_top)],
  exact [expr (step3 h1 h2 h3 P.1).resolve_left (step5 h1 h2 h3)]
end

-- error in GroupTheory.SchurZassenhaus: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
theorem step7 : is_commutative N :=
begin
  haveI [] [] [":=", expr N.bot_or_nontrivial.resolve_left (step0 h1 h2 h3)],
  haveI [] [":", expr fact (fintype.card N).min_fac.prime] [":=", expr ⟨step4 h1 h2 h3⟩],
  exact [expr ⟨⟨λ
     g h, eq_top_iff.mp ((step3 h1 h2 h3 N.center).resolve_left (step6 h1 h2 h3).bot_lt_center.ne') (mem_top h) g⟩⟩]
end

end SchurZassenhausInduction

variable {n : ℕ} {G : Type u} [Groupₓ G]

-- error in GroupTheory.SchurZassenhaus: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private
theorem exists_right_complement'_of_coprime_aux'
[fintype G]
(hG : «expr = »(fintype.card G, n))
{N : subgroup G}
[N.normal]
(hN : nat.coprime (fintype.card N) N.index) : «expr∃ , »((H : subgroup G), is_complement' N H) :=
begin
  unfreezingI { revert [ident G] },
  apply [expr nat.strong_induction_on n],
  rintros [ident n, ident ih, ident G, "_", "_", ident rfl, ident N, "_", ident hN],
  refine [expr not_forall_not.mp (λ h3, _)],
  haveI [] [] [":=", expr by exactI [expr schur_zassenhaus_induction.step7 hN (λ G' _ _ hG', by { apply [expr ih _ hG'],
       refl }) h3]],
  exact [expr not_exists_of_forall_not h3 (exists_right_complement'_of_coprime_aux hN)]
end

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (right) complement of `H`. -/
theorem exists_right_complement'_of_coprime_of_fintype [Fintype G] {N : Subgroup G} [N.normal]
  (hN : Nat.Coprime (Fintype.card N) N.index) : ∃ H : Subgroup G, is_complement' N H :=
  exists_right_complement'_of_coprime_aux' rfl hN

-- error in GroupTheory.SchurZassenhaus: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (right) complement of `H`. -/
theorem exists_right_complement'_of_coprime
{N : subgroup G}
[N.normal]
(hN : nat.coprime (nat.card N) N.index) : «expr∃ , »((H : subgroup G), is_complement' N H) :=
begin
  by_cases [expr hN1, ":", expr «expr = »(nat.card N, 0)],
  { rw ["[", expr hN1, ",", expr nat.coprime_zero_left, ",", expr index_eq_one, "]"] ["at", ident hN],
    rw [expr hN] [],
    exact [expr ⟨«expr⊥»(), is_complement'_top_bot⟩] },
  by_cases [expr hN2, ":", expr «expr = »(N.index, 0)],
  { rw ["[", expr hN2, ",", expr nat.coprime_zero_right, "]"] ["at", ident hN],
    haveI [] [] [":=", expr (cardinal.to_nat_eq_one_iff_unique.mp hN).1],
    rw [expr N.eq_bot_of_subsingleton] [],
    exact [expr ⟨«expr⊤»(), is_complement'_bot_top⟩] },
  have [ident hN3] [":", expr «expr ≠ »(nat.card G, 0)] [],
  { rw ["<-", expr N.card_mul_index] [],
    exact [expr mul_ne_zero hN1 hN2] },
  haveI [] [] [":=", expr (cardinal.lt_omega_iff_fintype.mp (lt_of_not_ge (mt cardinal.to_nat_apply_of_omega_le hN3))).some],
  rw [expr nat.card_eq_fintype_card] ["at", ident hN],
  exact [expr exists_right_complement'_of_coprime_of_fintype hN]
end

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (left) complement of `H`. -/
theorem exists_left_complement'_of_coprime_of_fintype [Fintype G] {N : Subgroup G} [N.normal]
  (hN : Nat.Coprime (Fintype.card N) N.index) : ∃ H : Subgroup G, is_complement' H N :=
  Exists.impₓ (fun _ => is_complement'.symm) (exists_right_complement'_of_coprime_of_fintype hN)

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (left) complement of `H`. -/
theorem exists_left_complement'_of_coprime {N : Subgroup G} [N.normal] (hN : Nat.Coprime (Nat.card N) N.index) :
  ∃ H : Subgroup G, is_complement' H N :=
  Exists.impₓ (fun _ => is_complement'.symm) (exists_right_complement'_of_coprime hN)

end Subgroup

