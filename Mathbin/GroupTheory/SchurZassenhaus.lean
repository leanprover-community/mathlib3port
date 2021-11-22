import Mathbin.GroupTheory.Complement 
import Mathbin.GroupTheory.Index

/-!
# Complements

In this file we prove the Schur-Zassenhaus theorem for abelian normal subgroups.

## Main results

- `exists_right_complement_of_coprime` : **Schur-Zassenhaus** for abelian normal subgroups:
  If `H : subgroup G` is abelian, normal, and has order coprime to its index, then there exists
  a subgroup `K` which is a (right) complement of `H`.
- `exists_left_complement_of_coprime` : **Schur-Zassenhaus** for abelian normal subgroups:
  If `H : subgroup G` is abelian, normal, and has order coprime to its index, then there exists
  a subgroup `K` which is a (left) complement of `H`.
-/


open_locale BigOperators

namespace Subgroup

variable{G : Type _}[Groupₓ G]{H : Subgroup G}

@[toAdditive]
instance  : MulAction G (left_transversals (H : Set G)) :=
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

variable[IsCommutative H][Fintype (QuotientGroup.Quotient H)]

variable(α β γ : left_transversals (H : Set G))

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

variable(H)

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

instance  [H.normal] : Inhabited H.quotient_diff :=
  Quotientₓ.inhabited

variable{H}

instance  [H.normal] : MulAction G H.quotient_diff :=
  { smul :=
      fun g =>
        Quotientₓ.map (fun α => g • α)
          fun α β h =>
            (smul_diff_smul α β g).trans
              (Subtype.ext (mul_inv_eq_one.mpr (mul_right_eq_self.mpr (Subtype.ext_iff.mp h)))),
    mul_smul := fun g₁ g₂ q => Quotientₓ.induction_on q fun α => congr_argₓ Quotientₓ.mk (mul_smul g₁ g₂ α),
    one_smul := fun q => Quotientₓ.induction_on q fun α => congr_argₓ Quotientₓ.mk (one_smul G α) }

variable[Fintype H]

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

theorem is_complement'_stabilizer_of_coprime [Fintype G] [H.normal] {α : H.quotient_diff}
  (hH : Nat.Coprime (Fintype.card H) H.index) : is_complement' H (MulAction.stabilizer G α) :=
  by 
    classical 
    let ϕ : H ≃ MulAction.Orbit G α :=
      Equiv.ofBijective (fun h => ⟨h • α, h, rfl⟩)
        ⟨fun h₁ h₂ hh => smul_left_injective α hH (subtype.ext_iff.mp hh),
          fun β => exists_imp_exists (fun h hh => Subtype.ext hh) (exists_smul_eq α β hH)⟩
    have key := card_eq_card_quotient_mul_card_subgroup (MulAction.stabilizer G α)
    rw [←Fintype.card_congr (ϕ.trans (MulAction.orbitEquivQuotientStabilizer G α))] at key 
    apply is_complement'_of_coprime key.symm 
    rw [card_eq_card_quotient_mul_card_subgroup H, mul_commₓ, mul_right_inj'] at key
    ·
      rwa [←key, ←index_eq_card]
    ·
      rw [←pos_iff_ne_zero, Fintype.card_pos_iff]
      infer_instance

/-- **Schur-Zassenhaus** for abelian normal subgroups:
  If `H : subgroup G` is abelian, normal, and has order coprime to its index, then there exists
  a subgroup `K` which is a (right) complement of `H`. -/
theorem exists_right_complement'_of_coprime [Fintype G] [H.normal] (hH : Nat.Coprime (Fintype.card H) H.index) :
  ∃ K : Subgroup G, is_complement' H K :=
  nonempty_of_inhabited.elim
    fun α : H.quotient_diff => ⟨MulAction.stabilizer G α, is_complement'_stabilizer_of_coprime hH⟩

/-- **Schur-Zassenhaus** for abelian normal subgroups:
  If `H : subgroup G` is abelian, normal, and has order coprime to its index, then there exists
  a subgroup `K` which is a (left) complement of `H`. -/
theorem exists_left_complement'_of_coprime [Fintype G] [H.normal] (hH : Nat.Coprime (Fintype.card H) H.index) :
  ∃ K : Subgroup G, is_complement' K H :=
  Exists.impₓ (fun _ => is_complement'.symm) (exists_right_complement'_of_coprime hH)

end Subgroup

