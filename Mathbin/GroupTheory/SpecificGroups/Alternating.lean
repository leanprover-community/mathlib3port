/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.GroupTheory.Perm.Fin
import Mathbin.Tactic.IntervalCases

/-!
# Alternating Groups

The alternating group on a finite type `α` is the subgroup of the permutation group `perm α`
consisting of the even permutations.

## Main definitions

* `alternating_group α` is the alternating group on `α`, defined as a `subgroup (perm α)`.

## Main results
* `two_mul_card_alternating_group` shows that the alternating group is half as large as
  the permutation group it is a subgroup of.

* `closure_three_cycles_eq_alternating` shows that the alternating group is
  generated by 3-cycles.

* `alternating_group.is_simple_group_five` shows that the alternating group on `fin 5` is simple.
  The proof shows that the normal closure of any non-identity element of this group contains a
  3-cycle.

## Tags
alternating group permutation


## TODO
* Show that `alternating_group α` is simple if and only if `fintype.card α ≠ 4`.

-/


open Equivₓ Equivₓ.Perm Subgroup Fintype

variable (α : Type _) [Fintype α] [DecidableEq α]

/-- The alternating group on a finite type, realized as a subgroup of `equiv.perm`.
  For $A_n$, use `alternating_group (fin n)`. -/
def alternatingGroup : Subgroup (Perm α) :=
  sign.ker deriving Fintype

instance [Subsingleton α] : Unique (alternatingGroup α) :=
  ⟨⟨1⟩, fun ⟨p, hp⟩ => Subtype.eq (Subsingleton.elimₓ p _)⟩

variable {α}

theorem alternating_group_eq_sign_ker : alternatingGroup α = sign.ker :=
  rfl

namespace Equivₓ.Perm

@[simp]
theorem mem_alternating_group {f : Perm α} : f ∈ alternatingGroup α ↔ sign f = 1 :=
  sign.mem_ker

theorem prod_list_swap_mem_alternating_group_iff_even_length {l : List (Perm α)} (hl : ∀, ∀ g ∈ l, ∀, IsSwap g) :
    l.Prod ∈ alternatingGroup α ↔ Even l.length := by
  rw [mem_alternating_group, sign_prod_list_swap hl, ← Units.coe_eq_one, Units.coe_pow, Units.coe_neg_one,
    Nat.neg_one_pow_eq_one_iff_even]
  decide

theorem IsThreeCycle.mem_alternating_group {f : Perm α} (h : IsThreeCycle f) : f ∈ alternatingGroup α :=
  mem_alternating_group.2 h.sign

theorem fin_rotate_bit1_mem_alternating_group {n : ℕ} : finRotate (bit1 n) ∈ alternatingGroup (Finₓ (bit1 n)) := by
  rw [mem_alternating_group, bit1, sign_fin_rotate, pow_bit0', Int.units_mul_self, one_pow]

end Equivₓ.Perm

theorem two_mul_card_alternating_group [Nontrivial α] : 2 * card (alternatingGroup α) = card (Perm α) := by
  let this := (QuotientGroup.quotientKerEquivOfSurjective _ (sign_surjective α)).toEquiv
  rw [← Fintype.card_units_int, ← Fintype.card_congr this]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm

namespace alternatingGroup

open Equivₓ.Perm

instance normal : (alternatingGroup α).Normal :=
  sign.normal_ker

theorem is_conj_of {σ τ : alternatingGroup α} (hc : IsConj (σ : Perm α) (τ : Perm α))
    (hσ : (σ : Perm α).support.card + 2 ≤ Fintype.card α) : IsConj σ τ := by
  obtain ⟨σ, hσ⟩ := σ
  obtain ⟨τ, hτ⟩ := τ
  obtain ⟨π, hπ⟩ := is_conj_iff.1 hc
  rw [Subtype.coe_mk, Subtype.coe_mk] at hπ
  cases' Int.units_eq_one_or (sign π) with h h
  · rw [is_conj_iff]
    refine' ⟨⟨π, mem_alternating_group.mp h⟩, Subtype.val_injective _⟩
    simpa only [Subtype.val_eq_coe, Subgroup.coe_mul, coe_inv, coe_mk] using hπ
    
  · have h2 : 2 ≤ σ.supportᶜ.card := by
      rw [Finset.card_compl, le_tsub_iff_left σ.support.card_le_univ]
      exact hσ
    obtain ⟨a, ha, b, hb, ab⟩ := Finset.one_lt_card.1 h2
    refine' is_conj_iff.2 ⟨⟨π * swap a b, _⟩, Subtype.val_injective _⟩
    · rw [mem_alternating_group, MonoidHom.map_mul, h, sign_swap ab, Int.units_mul_self]
      
    · simp only [← hπ, coe_mk, Subgroup.coe_mul, Subtype.val_eq_coe]
      have hd : Disjoint (swap a b) σ := by
        rw [disjoint_iff_disjoint_support, support_swap ab, Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
        exact ⟨Finset.mem_compl.1 ha, Finset.mem_compl.1 hb⟩
      rw [mul_assoc π _ σ, hd.commute.eq, coe_inv, coe_mk]
      simp [mul_assoc]
      
    

theorem is_three_cycle_is_conj (h5 : 5 ≤ Fintype.card α) {σ τ : alternatingGroup α} (hσ : IsThreeCycle (σ : Perm α))
    (hτ : IsThreeCycle (τ : Perm α)) : IsConj σ τ :=
  alternatingGroup.is_conj_of (is_conj_iff_cycle_type_eq.2 (hσ.trans hτ.symm))
    (by
      rwa [hσ.card_support])

end alternatingGroup

namespace Equivₓ.Perm

open alternatingGroup

@[simp]
theorem closure_three_cycles_eq_alternating : closure { σ : Perm α | IsThreeCycle σ } = alternatingGroup α :=
  (closure_eq_of_le _ fun σ hσ => mem_alternating_group.2 hσ.sign) fun σ hσ => by
    suffices hind :
      ∀ n : ℕ l : List (perm α) hl : ∀ g, g ∈ l → is_swap g hn : l.length = 2 * n,
        l.Prod ∈ closure { σ : perm α | is_three_cycle σ }
    · obtain ⟨l, rfl, hl⟩ := trunc_swap_factors σ
      obtain ⟨n, hn⟩ := (prod_list_swap_mem_alternating_group_iff_even_length hl).1 hσ
      exact hind n l hl hn
      
    intro n
    induction' n with n ih <;> intro l hl hn
    · simp [List.length_eq_zero.1 hn, one_mem]
      
    rw [Nat.mul_succ] at hn
    obtain ⟨a, l, rfl⟩ := l.exists_of_length_succ hn
    rw [List.length_cons, Nat.succ_inj'] at hn
    obtain ⟨b, l, rfl⟩ := l.exists_of_length_succ hn
    rw [List.prod_cons, List.prod_cons, ← mul_assoc]
    rw [List.length_cons, Nat.succ_inj'] at hn
    exact
      mul_mem _
        (is_swap.mul_mem_closure_three_cycles (hl a (List.mem_cons_selfₓ a _))
          (hl b (List.mem_cons_of_memₓ a (l.mem_cons_self b))))
        (ih _ (fun g hg => hl g (List.mem_cons_of_memₓ _ (List.mem_cons_of_memₓ _ hg))) hn)

/-- A key lemma to prove $A_5$ is simple. Shows that any normal subgroup of an alternating group on
  at least 5 elements is the entire alternating group if it contains a 3-cycle. -/
theorem IsThreeCycle.alternating_normal_closure (h5 : 5 ≤ Fintype.card α) {f : Perm α} (hf : IsThreeCycle f) :
    normalClosure ({⟨f, hf.mem_alternating_group⟩} : Set (alternatingGroup α)) = ⊤ :=
  eq_top_iff.2
    (by
      have hi : Function.Injective (alternatingGroup α).Subtype := Subtype.coe_injective
      refine' eq_top_iff.1 (map_injective hi (le_antisymmₓ (map_mono le_top) _))
      rw [← MonoidHom.range_eq_map, subtype_range, normal_closure, MonoidHom.map_closure]
      refine' (le_of_eqₓ closure_three_cycles_eq_alternating.symm).trans (closure_mono _)
      intro g h
      obtain ⟨c, rfl⟩ := is_conj_iff.1 (is_conj_iff_cycle_type_eq.2 (hf.trans h.symm))
      refine' ⟨⟨c * f * c⁻¹, h.mem_alternating_group⟩, _, rfl⟩
      rw [Groupₓ.mem_conjugates_of_set_iff]
      exact ⟨⟨f, hf.mem_alternating_group⟩, Set.mem_singleton _, is_three_cycle_is_conj h5 hf h⟩)

/-- Part of proving $A_5$ is simple. Shows that the square of any element of $A_5$ with a 3-cycle in
  its cycle decomposition is a 3-cycle, so the normal closure of the original element must be
  $A_5$. -/
theorem is_three_cycle_sq_of_three_mem_cycle_type_five {g : Perm (Finₓ 5)} (h : 3 ∈ cycleType g) :
    IsThreeCycle (g * g) := by
  obtain ⟨c, g', rfl, hd, hc, h3⟩ := mem_cycle_type_iff.1 h
  simp only [mul_assoc]
  rw [hd.commute.eq, ← mul_assoc g']
  suffices hg' : orderOf g' ∣ 2
  · rw [← pow_two, order_of_dvd_iff_pow_eq_one.1 hg', one_mulₓ]
    exact (card_support_eq_three_iff.1 h3).is_three_cycle_sq
    
  rw [← lcm_cycle_type, Multiset.lcm_dvd]
  intro n hn
  rw [le_antisymmₓ (two_le_of_mem_cycle_type hn) (le_transₓ (le_card_support_of_mem_cycle_type hn) _)]
  apply le_of_add_le_add_left
  rw [← hd.card_support_mul, h3]
  exact (c * g').support.card_le_univ

end Equivₓ.Perm

namespace alternatingGroup

open Equivₓ.Perm

theorem nontrivial_of_three_le_card (h3 : 3 ≤ card α) : Nontrivial (alternatingGroup α) := by
  have :=
    Fintype.one_lt_card_iff_nontrivial.1
      (lt_transₓ
        (by
          decide)
        h3)
  rw [← Fintype.one_lt_card_iff_nontrivial]
  refine' lt_of_mul_lt_mul_left _ (le_of_ltₓ nat.prime_two.pos)
  rw [two_mul_card_alternating_group, card_perm, ← Nat.succ_le_iff]
  exact le_transₓ h3 (card α).self_le_factorial

instance {n : ℕ} : Nontrivial (alternatingGroup (Finₓ (n + 3))) :=
  nontrivial_of_three_le_card
    (by
      rw [card_fin]
      exact le_add_left (le_reflₓ 3))

/-- The normal closure of the 5-cycle `fin_rotate 5` within $A_5$ is the whole group. This will be
  used to show that the normal closure of any 5-cycle within $A_5$ is the whole group. -/
theorem normal_closure_fin_rotate_five :
    normalClosure ({⟨finRotate 5, fin_rotate_bit1_mem_alternating_group⟩} : Set (alternatingGroup (Finₓ 5))) = ⊤ :=
  eq_top_iff.2
    (by
      have h3 : is_three_cycle (Finₓ.cycleRange 2 * finRotate 5 * (Finₓ.cycleRange 2)⁻¹ * (finRotate 5)⁻¹) :=
        card_support_eq_three_iff.1
          (by
            decide)
      rw [←
        h3.alternating_normal_closure
          (by
            rw [card_fin])]
      refine' normal_closure_le_normal _
      rw [Set.singleton_subset_iff, SetLike.mem_coe]
      have h : (⟨finRotate 5, fin_rotate_bit1_mem_alternating_group⟩ : alternatingGroup (Finₓ 5)) ∈ normal_closure _ :=
        SetLike.mem_coe.1 (subset_normal_closure (Set.mem_singleton _))
      exact
        mul_mem _
          (subgroup.normal_closure_normal.conj_mem _ h
            ⟨Finₓ.cycleRange 2, fin.is_three_cycle_cycle_range_two.mem_alternating_group⟩)
          (inv_mem _ h))

/-- The normal closure of $(04)(13)$ within $A_5$ is the whole group. This will be
  used to show that the normal closure of any permutation of cycle type $(2,2)$ is the whole group.
  -/
theorem normal_closure_swap_mul_swap_five :
    normalClosure
        ({⟨swap 0 4 * swap 1 3,
            mem_alternating_group.2
              (by
                decide)⟩} :
          Set (alternatingGroup (Finₓ 5))) =
      ⊤ :=
  by
  let g1 :=
    (⟨swap 0 2 * swap 0 1,
      mem_alternating_group.2
        (by
          decide)⟩ :
      alternatingGroup (Finₓ 5))
  let g2 :=
    (⟨swap 0 4 * swap 1 3,
      mem_alternating_group.2
        (by
          decide)⟩ :
      alternatingGroup (Finₓ 5))
  have h5 : g1 * g2 * g1⁻¹ * g2⁻¹ = ⟨finRotate 5, fin_rotate_bit1_mem_alternating_group⟩ := by
    rw [Subtype.ext_iff]
    simp only [Finₓ.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv, Finₓ.coe_mk]
    decide
  rw [eq_top_iff, ← normal_closure_fin_rotate_five]
  refine' normal_closure_le_normal _
  rw [Set.singleton_subset_iff, SetLike.mem_coe, ← h5]
  have h : g2 ∈ normal_closure {g2} := SetLike.mem_coe.1 (subset_normal_closure (Set.mem_singleton _))
  exact mul_mem _ (subgroup.normal_closure_normal.conj_mem _ h g1) (inv_mem _ h)

/-- Shows that any non-identity element of $A_5$ whose cycle decomposition consists only of swaps
  is conjugate to $(04)(13)$. This is used to show that the normal closure of such a permutation
  in $A_5$ is $A_5$. -/
theorem is_conj_swap_mul_swap_of_cycle_type_two {g : Perm (Finₓ 5)} (ha : g ∈ alternatingGroup (Finₓ 5)) (h1 : g ≠ 1)
    (h2 : ∀ n, n ∈ cycleType (g : Perm (Finₓ 5)) → n = 2) : IsConj (swap 0 4 * swap 1 3) g := by
  have h := g.support.card_le_univ
  rw [← sum_cycle_type, Multiset.eq_repeat_of_mem h2, Multiset.sum_repeat, smul_eq_mul] at h
  rw [← Multiset.eq_repeat'] at h2
  have h56 : 5 ≤ 3 * 2 := Nat.le_succₓ 5
  have h :=
    le_of_mul_le_mul_right (le_transₓ h h56)
      (by
        decide)
  rw [mem_alternating_group, sign_of_cycle_type, h2, Multiset.map_repeat, Multiset.prod_repeat, Int.units_pow_two,
    Units.ext_iff, Units.coe_one, Units.coe_pow, Units.coe_neg_one, Nat.neg_one_pow_eq_one_iff_even _] at ha
  swap
  · decide
    
  rw [is_conj_iff_cycle_type_eq, h2]
  interval_cases Multiset.card g.cycle_type
  · exact (h1 (card_cycle_type_eq_zero.1 h_1)).elim
    
  · contrapose! ha
    simp [h_1]
    
  · have h04 : (0 : Finₓ 5) ≠ 4 := by
      decide
    have h13 : (1 : Finₓ 5) ≠ 3 := by
      decide
    rw [h_1, disjoint.cycle_type, (is_cycle_swap h04).cycleType, (is_cycle_swap h13).cycleType, card_support_swap h04,
      card_support_swap h13]
    · rfl
      
    · rw [disjoint_iff_disjoint_support, support_swap h04, support_swap h13]
      decide
      
    
  · contrapose! ha
    simp [h_1]
    

/-- Shows that $A_5$ is simple by taking an arbitrary non-identity element and showing by casework
  on its cycle type that its normal closure is all of $A_5$.   -/
instance is_simple_group_five : IsSimpleGroup (alternatingGroup (Finₓ 5)) :=
  ⟨exists_pair_ne _, fun H => by
    intro Hn
    refine' or_not.imp id fun Hb => _
    rw [eq_bot_iff_forall] at Hb
    push_neg  at Hb
    obtain ⟨⟨g, gA⟩, gH, g1⟩ : ∃ x : ↥(alternatingGroup (Finₓ 5)), x ∈ H ∧ x ≠ 1 := Hb
    -- `g` is a non-identity alternating permutation in a normal subgroup `H` of $A_5$.
    rw [← SetLike.mem_coe, ← Set.singleton_subset_iff] at gH
    refine' eq_top_iff.2 (le_transₓ (ge_of_eq _) (normal_closure_le_normal gH))
    -- It suffices to show that the normal closure of `g` in $A_5$ is $A_5$.
    by_cases' h2 : ∀, ∀ n ∈ g.cycle_type, ∀, n = 2
    · -- If the cycle decomposition of `g` consists entirely of swaps, then the cycle type is $(2,2)$.
      -- This means that it is conjugate to $(04)(13)$, whose normal closure is $A_5$.
      rw [Ne.def, Subtype.ext_iff] at g1
      exact
        (is_conj_swap_mul_swap_of_cycle_type_two gA g1 h2).normal_closure_eq_top_of normal_closure_swap_mul_swap_five
      
    push_neg  at h2
    obtain ⟨n, ng, n2⟩ : ∃ n : ℕ, n ∈ g.cycle_type ∧ n ≠ 2 := h2
    -- `n` is the size of a non-swap cycle in the decomposition of `g`.
    have n2' : 2 < n := lt_of_le_of_neₓ (two_le_of_mem_cycle_type ng) n2.symm
    have n5 : n ≤ 5 := le_transₓ _ g.support.card_le_univ
    -- We check that `2 < n ≤ 5`, so that `interval_cases` has a precise range to check.
    swap
    · obtain ⟨m, hm⟩ := Multiset.exists_cons_of_mem ng
      rw [← sum_cycle_type, hm, Multiset.sum_cons]
      exact le_add_right le_rfl
      
    interval_cases n
    -- This breaks into cases `n = 3`, `n = 4`, `n = 5`.
    · -- If `n = 3`, then `g` has a 3-cycle in its decomposition, so `g^2` is a 3-cycle.
      -- `g^2` is in the normal closure of `g`, so that normal closure must be $A_5$.
      rw [eq_top_iff, ←
        (is_three_cycle_sq_of_three_mem_cycle_type_five ng).alternating_normal_closure
          (by
            rw [card_fin])]
      refine' normal_closure_le_normal _
      rw [Set.singleton_subset_iff, SetLike.mem_coe]
      have h := SetLike.mem_coe.1 (subset_normal_closure (Set.mem_singleton _))
      exact mul_mem _ h h
      
    · -- The case `n = 4` leads to contradiction, as no element of $A_5$ includes a 4-cycle.
      have con := mem_alternating_group.1 gA
      contrapose! con
      rw [sign_of_cycle_type,
        cycle_type_of_card_le_mem_cycle_type_add_two
          (by
            decide)
          ng,
        Multiset.map_singleton, Multiset.prod_singleton]
      decide
      
    · -- If `n = 5`, then `g` is itself a 5-cycle, conjugate to `fin_rotate 5`.
      refine' (is_conj_iff_cycle_type_eq.2 _).normal_closure_eq_top_of normal_closure_fin_rotate_five
      rw
        [cycle_type_of_card_le_mem_cycle_type_add_two
          (by
            decide)
          ng,
        cycle_type_fin_rotate]
      ⟩

end alternatingGroup

