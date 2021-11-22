import Mathbin.Algebra.GcdMonoid.Multiset 
import Mathbin.Combinatorics.Partition 
import Mathbin.GroupTheory.Perm.Cycles 
import Mathbin.RingTheory.Int.Basic 
import Mathbin.Tactic.Linarith.Default

/-!
# Cycle Types

In this file we define the cycle type of a permutation.

## Main definitions

- `σ.cycle_type` where `σ` is a permutation of a `fintype`
- `σ.partition` where `σ` is a permutation of a `fintype`

## Main results

- `sum_cycle_type` : The sum of `σ.cycle_type` equals `σ.support.card`
- `lcm_cycle_type` : The lcm of `σ.cycle_type` equals `order_of σ`
- `is_conj_iff_cycle_type_eq` : Two permutations are conjugate if and only if they have the same
  cycle type.
* `exists_prime_order_of_dvd_card`: For every prime `p` dividing the order of a finite group `G`
  there exists an element of order `p` in `G`. This is known as Cauchy`s theorem.
-/


namespace Equiv.Perm

open Equiv List Multiset

variable{α : Type _}[Fintype α]

section CycleType

variable[DecidableEq α]

/-- The cycle type of a permutation -/
def cycle_type (σ : perm α) : Multiset ℕ :=
  σ.cycle_factors_finset.1.map (Finset.card ∘ support)

theorem cycle_type_def (σ : perm α) : σ.cycle_type = σ.cycle_factors_finset.1.map (Finset.card ∘ support) :=
  rfl

theorem cycle_type_eq' {σ : perm α} (s : Finset (perm α)) (h1 : ∀ f : perm α, f ∈ s → f.is_cycle)
  (h2 : ∀ a _ : a ∈ s b _ : b ∈ s, a ≠ b → Disjoint a b)
  (h0 :
    (s.noncomm_prod id
        fun a ha b hb =>
          (em (a = b)).byCases (fun h => h ▸ Commute.refl a)
            (Set.Pairwise.mono' (fun _ _ => disjoint.commute) h2 a ha b hb)) =
      σ) :
  σ.cycle_type = s.1.map (Finset.card ∘ support) :=
  by 
    rw [cycle_type_def]
    congr 
    rw [cycle_factors_finset_eq_finset]
    exact ⟨h1, h2, h0⟩

theorem cycle_type_eq {σ : perm α} (l : List (perm α)) (h0 : l.prod = σ) (h1 : ∀ σ : perm α, σ ∈ l → σ.is_cycle)
  (h2 : l.pairwise Disjoint) : σ.cycle_type = l.map (Finset.card ∘ support) :=
  by 
    have hl : l.nodup := nodup_of_pairwise_disjoint_cycles h1 h2 
    rw [cycle_type_eq' l.to_finset]
    ·
      simp [list.erase_dup_eq_self.mpr hl]
    ·
      simpa using h1
    ·
      simpa [hl] using h0
    ·
      simpa [list.erase_dup_eq_self.mpr hl] using List.forall_of_pairwise disjoint.symmetric h2

theorem cycle_type_one : (1 : perm α).cycleType = 0 :=
  cycle_type_eq [] rfl (fun _ => False.elim) pairwise.nil

theorem cycle_type_eq_zero {σ : perm α} : σ.cycle_type = 0 ↔ σ = 1 :=
  by 
    simp [cycle_type_def, cycle_factors_finset_eq_empty_iff]

theorem card_cycle_type_eq_zero {σ : perm α} : σ.cycle_type.card = 0 ↔ σ = 1 :=
  by 
    rw [card_eq_zero, cycle_type_eq_zero]

theorem two_le_of_mem_cycle_type {σ : perm α} {n : ℕ} (h : n ∈ σ.cycle_type) : 2 ≤ n :=
  by 
    simp only [cycle_type_def, ←Finset.mem_def, Function.comp_app, Multiset.mem_map, mem_cycle_factors_finset_iff] at h 
    obtain ⟨_, ⟨hc, -⟩, rfl⟩ := h 
    exact hc.two_le_card_support

theorem one_lt_of_mem_cycle_type {σ : perm α} {n : ℕ} (h : n ∈ σ.cycle_type) : 1 < n :=
  two_le_of_mem_cycle_type h

theorem is_cycle.cycle_type {σ : perm α} (hσ : is_cycle σ) : σ.cycle_type = [σ.support.card] :=
  cycle_type_eq [σ] (mul_oneₓ σ) (fun τ hτ => (congr_argₓ is_cycle (List.mem_singleton.mp hτ)).mpr hσ)
    (pairwise_singleton Disjoint σ)

theorem card_cycle_type_eq_one {σ : perm α} : σ.cycle_type.card = 1 ↔ σ.is_cycle :=
  by 
    rw [card_eq_one]
    simpRw [cycle_type_def, Multiset.map_eq_singleton, ←Finset.singleton_val, Finset.val_inj,
      cycle_factors_finset_eq_singleton_iff]
    split 
    ·
      rintro ⟨_, _, ⟨h, -⟩, -⟩
      exact h
    ·
      intro h 
      use σ.support.card, σ 
      simp [h]

theorem disjoint.cycle_type {σ τ : perm α} (h : Disjoint σ τ) : (σ*τ).cycleType = σ.cycle_type+τ.cycle_type :=
  by 
    rw [cycle_type_def, cycle_type_def, cycle_type_def, h.cycle_factors_finset_mul_eq_union, ←map_add, Finset.union_val,
      multiset.add_eq_union_iff_disjoint.mpr _]
    rw [←Finset.disjoint_val]
    exact h.disjoint_cycle_factors_finset

theorem cycle_type_inv (σ : perm α) : σ⁻¹.cycleType = σ.cycle_type :=
  cycle_induction_on (fun τ : perm α => τ⁻¹.cycleType = τ.cycle_type) σ rfl
    (fun σ hσ =>
      by 
        rw [hσ.cycle_type, hσ.inv.cycle_type, support_inv])
    fun σ τ hστ hc hσ hτ =>
      by 
        rw [mul_inv_rev, hστ.cycle_type, ←hσ, ←hτ, add_commₓ,
          disjoint.cycle_type
            fun x =>
              Or.imp (fun h : τ x = x => inv_eq_iff_eq.mpr h.symm) (fun h : σ x = x => inv_eq_iff_eq.mpr h.symm)
                (hστ x).symm]

theorem cycle_type_conj {σ τ : perm α} : ((τ*σ)*τ⁻¹).cycleType = σ.cycle_type :=
  by 
    revert τ 
    apply cycle_induction_on _ σ
    ·
      intro 
      simp 
    ·
      intro σ hσ τ 
      rw [hσ.cycle_type, hσ.is_cycle_conj.cycle_type, card_support_conj]
    ·
      intro σ τ hd hc hσ hτ π 
      rw [←conj_mul, hd.cycle_type, disjoint.cycle_type, hσ, hτ]
      intro a 
      apply (hd ((π⁻¹) a)).imp _ _ <;>
        ·
          intro h 
          rw [perm.mul_apply, perm.mul_apply, h, apply_inv_self]

theorem sum_cycle_type (σ : perm α) : σ.cycle_type.sum = σ.support.card :=
  cycle_induction_on (fun τ : perm α => τ.cycle_type.sum = τ.support.card) σ
    (by 
      rw [cycle_type_one, sum_zero, support_one, Finset.card_empty])
    (fun σ hσ =>
      by 
        rw [hσ.cycle_type, coe_sum, List.sum_singleton])
    fun σ τ hστ hc hσ hτ =>
      by 
        rw [hστ.cycle_type, sum_add, hσ, hτ, hστ.card_support_mul]

theorem sign_of_cycle_type (σ : perm α) : sign σ = (σ.cycle_type.map fun n => -((-1 : Units ℤ)^n)).Prod :=
  cycle_induction_on (fun τ : perm α => sign τ = (τ.cycle_type.map fun n => -((-1 : Units ℤ)^n)).Prod) σ
    (by 
      rw [sign_one, cycle_type_one, map_zero, prod_zero])
    (fun σ hσ =>
      by 
        rw [hσ.sign, hσ.cycle_type, coe_map, coe_prod, List.map_singleton, List.prod_singleton])
    fun σ τ hστ hc hσ hτ =>
      by 
        rw [sign_mul, hσ, hτ, hστ.cycle_type, map_add, prod_add]

theorem lcm_cycle_type (σ : perm α) : σ.cycle_type.lcm = orderOf σ :=
  cycle_induction_on (fun τ : perm α => τ.cycle_type.lcm = orderOf τ) σ
    (by 
      rw [cycle_type_one, lcm_zero, order_of_one])
    (fun σ hσ =>
      by 
        rw [hσ.cycle_type, ←singleton_coe, ←singleton_eq_cons, lcm_singleton, order_of_is_cycle hσ, normalize_eq])
    fun σ τ hστ hc hσ hτ =>
      by 
        rw [hστ.cycle_type, lcm_add, lcm_eq_nat_lcm, hστ.order_of, hσ, hτ]

theorem dvd_of_mem_cycle_type {σ : perm α} {n : ℕ} (h : n ∈ σ.cycle_type) : n ∣ orderOf σ :=
  by 
    rw [←lcm_cycle_type]
    exact dvd_lcm h

theorem order_of_cycle_of_dvd_order_of (f : perm α) (x : α) : orderOf (cycle_of f x) ∣ orderOf f :=
  by 
    byCases' hx : f x = x
    ·
      rw [←cycle_of_eq_one_iff] at hx 
      simp [hx]
    ·
      refine' dvd_of_mem_cycle_type _ 
      rw [cycle_type, Multiset.mem_map]
      refine' ⟨f.cycle_of x, _, _⟩
      ·
        rwa [←Finset.mem_def, cycle_of_mem_cycle_factors_finset_iff, mem_support]
      ·
        simp [order_of_is_cycle (is_cycle_cycle_of _ hx)]

theorem two_dvd_card_support {σ : perm α} (hσ : (σ^2) = 1) : 2 ∣ σ.support.card :=
  (congr_argₓ (HasDvd.Dvd 2) σ.sum_cycle_type).mp
    (Multiset.dvd_sum
      fun n hn =>
        by 
          rw
            [le_antisymmₓ (Nat.le_of_dvdₓ zero_lt_two$ (dvd_of_mem_cycle_type hn).trans$ order_of_dvd_of_pow_eq_one hσ)
              (two_le_of_mem_cycle_type hn)])

theorem cycle_type_prime_order {σ : perm α} (hσ : (orderOf σ).Prime) :
  ∃ n : ℕ, σ.cycle_type = repeat (orderOf σ) (n+1) :=
  by 
    rw
      [eq_repeat_of_mem
        fun n hn =>
          or_iff_not_imp_left.mp (hσ.2 n (dvd_of_mem_cycle_type hn)) (ne_of_gtₓ (one_lt_of_mem_cycle_type hn))]
    use σ.cycle_type.card - 1
    rw [tsub_add_cancel_of_le]
    rw [Nat.succ_le_iff, pos_iff_ne_zero, Ne, card_cycle_type_eq_zero]
    rintro rfl 
    rw [order_of_one] at hσ 
    exact hσ.ne_one rfl

theorem is_cycle_of_prime_order {σ : perm α} (h1 : (orderOf σ).Prime) (h2 : σ.support.card < 2*orderOf σ) :
  σ.is_cycle :=
  by 
    obtain ⟨n, hn⟩ := cycle_type_prime_order h1 
    rw [←σ.sum_cycle_type, hn, Multiset.sum_repeat, nsmul_eq_mul, Nat.cast_id, mul_lt_mul_right (order_of_pos σ),
      Nat.succ_lt_succ_iff, Nat.lt_succ_iff, Nat.le_zero_iff] at h2 
    rw [←card_cycle_type_eq_one, hn, card_repeat, h2]

theorem cycle_type_le_of_mem_cycle_factors_finset {f g : perm α} (hf : f ∈ g.cycle_factors_finset) :
  f.cycle_type ≤ g.cycle_type :=
  by 
    rw [mem_cycle_factors_finset_iff] at hf 
    rw [cycle_type_def, cycle_type_def, hf.left.cycle_factors_finset_eq_singleton]
    refine' map_le_map _ 
    simpa [←Finset.mem_def, mem_cycle_factors_finset_iff] using hf

theorem cycle_type_mul_mem_cycle_factors_finset_eq_sub {f g : perm α} (hf : f ∈ g.cycle_factors_finset) :
  (g*f⁻¹).cycleType = g.cycle_type - f.cycle_type :=
  by 
    suffices  : ((g*f⁻¹).cycleType+f.cycle_type) = (g.cycle_type - f.cycle_type)+f.cycle_type
    ·
      rw [tsub_add_cancel_of_le (cycle_type_le_of_mem_cycle_factors_finset hf)] at this 
      simp [←this]
    simp [←(disjoint_mul_inv_of_mem_cycle_factors_finset hf).cycleType,
      tsub_add_cancel_of_le (cycle_type_le_of_mem_cycle_factors_finset hf)]

theorem is_conj_of_cycle_type_eq {σ τ : perm α} (h : cycle_type σ = cycle_type τ) : IsConj σ τ :=
  by 
    revert τ 
    apply cycle_induction_on _ σ
    ·
      intro τ h 
      rw [cycle_type_one, eq_comm, cycle_type_eq_zero] at h 
      rw [h]
    ·
      intro σ hσ τ hστ 
      have hτ := card_cycle_type_eq_one.2 hσ 
      rw [hστ, card_cycle_type_eq_one] at hτ 
      apply hσ.is_conj hτ 
      rw [hσ.cycle_type, hτ.cycle_type, coe_eq_coe, singleton_perm] at hστ 
      simp only [and_trueₓ, eq_self_iff_true] at hστ 
      exact hστ
    ·
      intro σ τ hστ hσ h1 h2 π hπ 
      rw [hστ.cycle_type] at hπ
      ·
        have h : σ.support.card ∈ map (Finset.card ∘ perm.support) π.cycle_factors_finset.val
        ·
          simp [←cycle_type_def, ←hπ, hσ.cycle_type]
        obtain ⟨σ', hσ'l, hσ'⟩ := multiset.mem_map.mp h 
        have key : IsConj (σ'*π*σ'⁻¹) π
        ·
          rw [is_conj_iff]
          use σ'⁻¹
          simp [mul_assocₓ]
        refine' IsConj.trans _ key 
        have hs : σ.cycle_type = σ'.cycle_type
        ·
          rw [←Finset.mem_def, mem_cycle_factors_finset_iff] at hσ'l 
          rw [hσ.cycle_type, ←hσ', hσ'l.left.cycle_type]
        refine' hστ.is_conj_mul (h1 hs) (h2 _) _
        ·
          rw [cycle_type_mul_mem_cycle_factors_finset_eq_sub, ←hπ, add_commₓ, hs, add_tsub_cancel_right]
          rwa [Finset.mem_def]
        ·
          exact (disjoint_mul_inv_of_mem_cycle_factors_finset hσ'l).symm

theorem is_conj_iff_cycle_type_eq {σ τ : perm α} : IsConj σ τ ↔ σ.cycle_type = τ.cycle_type :=
  ⟨fun h =>
      by 
        obtain ⟨π, rfl⟩ := is_conj_iff.1 h 
        rw [cycle_type_conj],
    is_conj_of_cycle_type_eq⟩

@[simp]
theorem cycle_type_extend_domain {β : Type _} [Fintype β] [DecidableEq β] {p : β → Prop} [DecidablePred p]
  (f : α ≃ Subtype p) {g : perm α} : cycle_type (g.extend_domain f) = cycle_type g :=
  by 
    apply cycle_induction_on _ g
    ·
      rw [extend_domain_one, cycle_type_one, cycle_type_one]
    ·
      intro σ hσ 
      rw [(hσ.extend_domain f).cycleType, hσ.cycle_type, card_support_extend_domain]
    ·
      intro σ τ hd hc hσ hτ 
      rw [hd.cycle_type, ←extend_domain_mul, (hd.extend_domain f).cycleType, hσ, hτ]

theorem mem_cycle_type_iff {n : ℕ} {σ : perm α} :
  n ∈ cycle_type σ ↔ ∃ c τ : perm α, (σ = c*τ) ∧ Disjoint c τ ∧ is_cycle c ∧ c.support.card = n :=
  by 
    split 
    ·
      intro h 
      obtain ⟨l, rfl, hlc, hld⟩ := trunc_cycle_factors σ 
      rw [cycle_type_eq _ rfl hlc hld] at h 
      obtain ⟨c, cl, rfl⟩ := List.exists_of_mem_mapₓ h 
      rw [(List.perm_cons_erase cl).pairwise_iff fun _ _ hd => _] at hld 
      swap
      ·
        exact hd.symm 
      refine' ⟨c, (l.erase c).Prod, _, _, hlc _ cl, rfl⟩
      ·
        rw [←List.prod_cons, (List.perm_cons_erase cl).symm.prod_eq' (hld.imp fun _ _ => disjoint.commute)]
      ·
        exact disjoint_prod_right _ fun g => List.rel_of_pairwise_cons hld
    ·
      rintro ⟨c, t, rfl, hd, hc, rfl⟩
      simp [hd.cycle_type, hc.cycle_type]

theorem le_card_support_of_mem_cycle_type {n : ℕ} {σ : perm α} (h : n ∈ cycle_type σ) : n ≤ σ.support.card :=
  (le_sum_of_mem h).trans (le_of_eqₓ σ.sum_cycle_type)

theorem cycle_type_of_card_le_mem_cycle_type_add_two {n : ℕ} {g : perm α} (hn2 : Fintype.card α < n+2)
  (hng : n ∈ g.cycle_type) : g.cycle_type = {n} :=
  by 
    obtain ⟨c, g', rfl, hd, hc, rfl⟩ := mem_cycle_type_iff.1 hng 
    byCases' g'1 : g' = 1
    ·
      rw [hd.cycle_type, hc.cycle_type, Multiset.singleton_eq_cons, Multiset.singleton_coe, g'1, cycle_type_one,
        add_zeroₓ]
    contrapose! hn2 
    apply le_transₓ _ (c*g').support.card_le_univ 
    rw [hd.card_support_mul]
    exact add_le_add_left (two_le_card_support_of_ne_one g'1) _

end CycleType

theorem card_compl_support_modeq [DecidableEq α] {p n : ℕ} [hp : Fact p.prime] {σ : perm α} (hσ : (σ^p^n) = 1) :
  («expr ᶜ» σ.support).card ≡ Fintype.card α [MOD p] :=
  by 
    rw [Nat.modeq_iff_dvd' («expr ᶜ» σ.support).card_le_univ, ←Finset.card_compl, compl_compl]
    refine' (congr_argₓ _ σ.sum_cycle_type).mp (Multiset.dvd_sum fun k hk => _)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp.out).mp (order_of_dvd_of_pow_eq_one hσ)
    obtain ⟨l, -, rfl⟩ := (Nat.dvd_prime_pow hp.out).mp ((congr_argₓ _ hm).mp (dvd_of_mem_cycle_type hk))
    exact
      dvd_pow_self _
        fun h =>
          (one_lt_of_mem_cycle_type hk).Ne$
            by 
              rw [h, pow_zeroₓ]

theorem exists_fixed_point_of_prime {p n : ℕ} [hp : Fact p.prime] (hα : ¬p ∣ Fintype.card α) {σ : perm α}
  (hσ : (σ^p^n) = 1) : ∃ a : α, σ a = a :=
  by 
    classical 
    contrapose! hα 
    simpRw [←mem_support]  at hα 
    exact
      nat.modeq_zero_iff_dvd.mp
        ((congr_argₓ _ (finset.card_eq_zero.mpr (compl_eq_bot.mpr (finset.eq_univ_iff_forall.mpr hα)))).mp
          (card_compl_support_modeq hσ).symm)

theorem exists_fixed_point_of_prime' {p n : ℕ} [hp : Fact p.prime] (hα : p ∣ Fintype.card α) {σ : perm α}
  (hσ : (σ^p^n) = 1) {a : α} (ha : σ a = a) : ∃ b : α, σ b = b ∧ b ≠ a :=
  by 
    classical 
    have h : ∀ b : α, b ∈ «expr ᶜ» σ.support ↔ σ b = b :=
      fun b =>
        by 
          rw [Finset.mem_compl, mem_support, not_not]
    obtain ⟨b, hb1, hb2⟩ :=
      Finset.exists_ne_of_one_lt_card
        (lt_of_lt_of_leₓ hp.out.one_lt
          (Nat.le_of_dvdₓ (finset.card_pos.mpr ⟨a, (h a).mpr ha⟩)
            (nat.modeq_zero_iff_dvd.mp ((card_compl_support_modeq hσ).trans (nat.modeq_zero_iff_dvd.mpr hα)))))
        a 
    exact ⟨b, (h b).mp hb1, hb2⟩

theorem is_cycle_of_prime_order' {σ : perm α} (h1 : (orderOf σ).Prime) (h2 : Fintype.card α < 2*orderOf σ) :
  σ.is_cycle :=
  by 
    classical 
    exact is_cycle_of_prime_order h1 (lt_of_le_of_ltₓ σ.support.card_le_univ h2)

theorem is_cycle_of_prime_order'' {σ : perm α} (h1 : (Fintype.card α).Prime) (h2 : orderOf σ = Fintype.card α) :
  σ.is_cycle :=
  is_cycle_of_prime_order' ((congr_argₓ Nat.Prime h2).mpr h1)
    (by 
      classical 
      rw [←one_mulₓ (Fintype.card α), ←h2, mul_lt_mul_right (order_of_pos σ)]
      exact one_lt_two)

section Cauchy

variable(G : Type _)[Groupₓ G](n : ℕ)

/-- The type of vectors with terms from `G`, length `n`, and product equal to `1:G`. -/
def vectors_prod_eq_one : Set (Vector G n) :=
  { v | v.to_list.prod = 1 }

namespace VectorsProdEqOne

theorem mem_iff {n : ℕ} (v : Vector G n) : v ∈ vectors_prod_eq_one G n ↔ v.to_list.prod = 1 :=
  Iff.rfl

theorem zero_eq : vectors_prod_eq_one G 0 = {Vector.nil} :=
  Set.eq_singleton_iff_unique_mem.mpr ⟨Eq.refl (1 : G), fun v hv => v.eq_nil⟩

theorem one_eq : vectors_prod_eq_one G 1 = {Vector.nil.cons 1} :=
  by 
    simpRw [Set.eq_singleton_iff_unique_mem, mem_iff, Vector.to_list_singleton, List.prod_singleton, Vector.head_cons]
    exact ⟨rfl, fun v hv => v.cons_head_tail.symm.trans (congr_arg2 Vector.cons hv v.tail.eq_nil)⟩

instance zero_unique : Unique (vectors_prod_eq_one G 0) :=
  by 
    rw [zero_eq]
    exact Set.uniqueSingleton Vector.nil

instance one_unique : Unique (vectors_prod_eq_one G 1) :=
  by 
    rw [one_eq]
    exact Set.uniqueSingleton (vector.nil.cons 1)

/-- Given a vector `v` of length `n`, make a vector of length `n + 1` whose product is `1`,
by appending the inverse of the product of `v`. -/
@[simps]
def vector_equiv : Vector G n ≃ vectors_prod_eq_one G (n+1) :=
  { toFun :=
      fun v =>
        ⟨v.to_list.prod⁻¹::ᵥv,
          by 
            rw [mem_iff, Vector.to_list_cons, List.prod_cons, inv_mul_selfₓ]⟩,
    invFun := fun v => v.1.tail, left_inv := fun v => v.tail_cons (v.to_list.prod⁻¹),
    right_inv :=
      fun v =>
        Subtype.ext
          ((congr_arg2 Vector.cons
                (eq_inv_of_mul_eq_one
                    (by 
                      rw [←List.prod_cons, ←Vector.to_list_cons, v.1.cons_head_tail]
                      exact v.2)).symm
                rfl).trans
            v.1.cons_head_tail) }

/-- Given a vector `v` of length `n` whose product is 1, make a vector of length `n - 1`,
by deleting the last entry of `v`. -/
def equiv_vector : vectors_prod_eq_one G n ≃ Vector G (n - 1) :=
  ((vector_equiv G (n - 1)).trans
      (if hn : n = 0 then
        show vectors_prod_eq_one G ((n - 1)+1) ≃ vectors_prod_eq_one G n by 
          rw [hn]
          exact equivOfUniqueOfUnique
      else
        by 
          rw [tsub_add_cancel_of_le (Nat.pos_of_ne_zeroₓ hn).nat_succ_le])).symm

instance  [Fintype G] : Fintype (vectors_prod_eq_one G n) :=
  Fintype.ofEquiv (Vector G (n - 1)) (equiv_vector G n).symm

theorem card [Fintype G] : Fintype.card (vectors_prod_eq_one G n) = (Fintype.card G^n - 1) :=
  (Fintype.card_congr (equiv_vector G n)).trans (card_vector (n - 1))

variable{G n}{g : G}(v : vectors_prod_eq_one G n)(j k : ℕ)

/-- Rotate a vector whose product is 1. -/
def rotate : vectors_prod_eq_one G n :=
  ⟨⟨_, (v.1.1.length_rotate k).trans v.1.2⟩, List.prod_rotate_eq_one_of_prod_eq_one v.2 k⟩

theorem rotate_zero : rotate v 0 = v :=
  Subtype.ext (Subtype.ext v.1.1.rotate_zero)

theorem rotate_rotate : rotate (rotate v j) k = rotate v (j+k) :=
  Subtype.ext (Subtype.ext (v.1.1.rotate_rotate j k))

theorem rotate_length : rotate v n = v :=
  Subtype.ext (Subtype.ext ((congr_argₓ _ v.1.2.symm).trans v.1.1.rotate_length))

end VectorsProdEqOne

theorem exists_prime_order_of_dvd_card {G : Type _} [Groupₓ G] [Fintype G] (p : ℕ) [hp : Fact p.prime]
  (hdvd : p ∣ Fintype.card G) : ∃ x : G, orderOf x = p :=
  by 
    have hp' : p - 1 ≠ 0 := mt tsub_eq_zero_iff_le.mp (not_le_of_lt hp.out.one_lt)
    have Scard :=
      calc p ∣ (Fintype.card G^p - 1) := hdvd.trans (dvd_pow (dvd_refl _) hp')
        _ = Fintype.card (vectors_prod_eq_one G p) := (vectors_prod_eq_one.card G p).symm 
        
    let f : ℕ → vectors_prod_eq_one G p → vectors_prod_eq_one G p := fun k v => vectors_prod_eq_one.rotate v k 
    have hf1 : ∀ v, f 0 v = v := vectors_prod_eq_one.rotate_zero 
    have hf2 : ∀ j k v, f k (f j v) = f (j+k) v := fun j k v => vectors_prod_eq_one.rotate_rotate v j k 
    have hf3 : ∀ v, f p v = v := vectors_prod_eq_one.rotate_length 
    let σ :=
      Equiv.mk (f 1) (f (p - 1))
        (fun s =>
          by 
            rw [hf2, add_tsub_cancel_of_le hp.out.one_lt.le, hf3])
        fun s =>
          by 
            rw [hf2, tsub_add_cancel_of_le hp.out.one_lt.le, hf3]
    have hσ : ∀ k v, (σ^k) v = f k v :=
      fun k v =>
        Nat.rec (hf1 v).symm
          (fun k hk =>
            Eq.trans
              (by 
                exact congr_argₓ σ hk)
              (hf2 k 1 v))
          k 
    replace hσ : (σ^p^1) = 1 :=
      perm.ext
        fun v =>
          by 
            rw [pow_oneₓ, hσ, hf3, one_apply]
    let v₀ : vectors_prod_eq_one G p := ⟨Vector.repeat 1 p, (List.prod_repeat 1 p).trans (one_pow p)⟩
    have hv₀ : σ v₀ = v₀ := Subtype.ext (Subtype.ext (List.rotate_repeat (1 : G) p 1))
    obtain ⟨v, hv1, hv2⟩ := exists_fixed_point_of_prime' Scard hσ hv₀ 
    refine'
      exists_imp_exists (fun g hg => order_of_eq_prime _ fun hg' => hv2 _)
        (list.rotate_one_eq_self_iff_eq_repeat.mp (subtype.ext_iff.mp (subtype.ext_iff.mp hv1)))
    ·
      rw [←List.prod_repeat, ←v.1.2, ←hg, show v.val.val.prod = 1 from v.2]
    ·
      rw [Subtype.ext_iff_val, Subtype.ext_iff_val, hg, hg', v.1.2]
      rfl

end Cauchy

theorem subgroup_eq_top_of_swap_mem [DecidableEq α] {H : Subgroup (perm α)} [d : DecidablePred (· ∈ H)] {τ : perm α}
  (h0 : (Fintype.card α).Prime) (h1 : Fintype.card α ∣ Fintype.card H) (h2 : τ ∈ H) (h3 : is_swap τ) : H = ⊤ :=
  by 
    haveI  : Fact (Fintype.card α).Prime := ⟨h0⟩
    obtain ⟨σ, hσ⟩ := exists_prime_order_of_dvd_card (Fintype.card α) h1 
    have hσ1 : orderOf (σ : perm α) = Fintype.card α := (order_of_subgroup σ).trans hσ 
    have hσ2 : is_cycle («expr↑ » σ) := is_cycle_of_prime_order'' h0 hσ1 
    have hσ3 : (σ : perm α).support = ⊤ :=
      Finset.eq_univ_of_card (σ : perm α).support ((order_of_is_cycle hσ2).symm.trans hσ1)
    have hσ4 : Subgroup.closure {«expr↑ » σ, τ} = ⊤ := closure_prime_cycle_swap h0 hσ2 hσ3 h3 
    rw [eq_top_iff, ←hσ4, Subgroup.closure_le, Set.insert_subset, Set.singleton_subset_iff]
    exact ⟨Subtype.mem σ, h2⟩

section Partition

variable[DecidableEq α]

/-- The partition corresponding to a permutation -/
def partition (σ : perm α) : (Fintype.card α).partition :=
  { parts := σ.cycle_type+repeat 1 (Fintype.card α - σ.support.card),
    parts_pos :=
      fun n hn =>
        by 
          cases' mem_add.mp hn with hn hn
          ·
            exact zero_lt_one.trans (one_lt_of_mem_cycle_type hn)
          ·
            exact lt_of_lt_of_leₓ zero_lt_one (ge_of_eq (Multiset.eq_of_mem_repeat hn)),
    parts_sum :=
      by 
        rw [sum_add, sum_cycle_type, Multiset.sum_repeat, nsmul_eq_mul, Nat.cast_id, mul_oneₓ,
          add_tsub_cancel_of_le σ.support.card_le_univ] }

theorem parts_partition {σ : perm α} : σ.partition.parts = σ.cycle_type+repeat 1 (Fintype.card α - σ.support.card) :=
  rfl

theorem filter_parts_partition_eq_cycle_type {σ : perm α} :
  ((partition σ).parts.filter fun n => 2 ≤ n) = σ.cycle_type :=
  by 
    rw [parts_partition, filter_add, Multiset.filter_eq_self.2 fun _ => two_le_of_mem_cycle_type,
      Multiset.filter_eq_nil.2 fun a h => _, add_zeroₓ]
    rw [Multiset.eq_of_mem_repeat h]
    decide

theorem partition_eq_of_is_conj {σ τ : perm α} : IsConj σ τ ↔ σ.partition = τ.partition :=
  by 
    rw [is_conj_iff_cycle_type_eq]
    refine' ⟨fun h => _, fun h => _⟩
    ·
      rw [Nat.Partition.ext_iff, parts_partition, parts_partition, ←sum_cycle_type, ←sum_cycle_type, h]
    ·
      rw [←filter_parts_partition_eq_cycle_type, ←filter_parts_partition_eq_cycle_type, h]

end Partition

/-!
### 3-cycles
-/


/-- A three-cycle is a cycle of length 3. -/
def is_three_cycle [DecidableEq α] (σ : perm α) : Prop :=
  σ.cycle_type = {3}

namespace IsThreeCycle

variable[DecidableEq α]{σ : perm α}

theorem cycle_type (h : is_three_cycle σ) : σ.cycle_type = {3} :=
  h

theorem card_support (h : is_three_cycle σ) : σ.support.card = 3 :=
  by 
    rw [←sum_cycle_type, h.cycle_type, Multiset.sum_singleton]

theorem _root_.card_support_eq_three_iff : σ.support.card = 3 ↔ σ.is_three_cycle :=
  by 
    refine' ⟨fun h => _, is_three_cycle.card_support⟩
    byCases' h0 : σ.cycle_type = 0
    ·
      rw [←sum_cycle_type, h0, sum_zero] at h 
      exact (ne_of_ltₓ zero_lt_three h).elim 
    obtain ⟨n, hn⟩ := exists_mem_of_ne_zero h0 
    byCases' h1 : σ.cycle_type.erase n = 0
    ·
      rw [←sum_cycle_type, ←cons_erase hn, h1, ←singleton_eq_cons, Multiset.sum_singleton] at h 
      rw [is_three_cycle, ←cons_erase hn, h1, h, singleton_eq_cons]
    obtain ⟨m, hm⟩ := exists_mem_of_ne_zero h1 
    rw [←sum_cycle_type, ←cons_erase hn, ←cons_erase hm, Multiset.sum_cons, Multiset.sum_cons] at h 
    linarith [two_le_of_mem_cycle_type hn, two_le_of_mem_cycle_type (mem_of_mem_erase hm)]

theorem is_cycle (h : is_three_cycle σ) : is_cycle σ :=
  by 
    rw [←card_cycle_type_eq_one, h.cycle_type, card_singleton]

theorem sign (h : is_three_cycle σ) : sign σ = 1 :=
  by 
    rw [sign_of_cycle_type, h.cycle_type]
    rfl

theorem inv {f : perm α} (h : is_three_cycle f) : is_three_cycle (f⁻¹) :=
  by 
    rwa [is_three_cycle, cycle_type_inv]

@[simp]
theorem inv_iff {f : perm α} : is_three_cycle (f⁻¹) ↔ is_three_cycle f :=
  ⟨by 
      rw [←inv_invₓ f]
      apply inv,
    inv⟩

theorem orderOf {g : perm α} (ht : is_three_cycle g) : orderOf g = 3 :=
  by 
    rw [←lcm_cycle_type, ht.cycle_type, Multiset.lcm_singleton, normalize_eq]

theorem is_three_cycle_sq {g : perm α} (ht : is_three_cycle g) : is_three_cycle (g*g) :=
  by 
    rw [←pow_two, ←card_support_eq_three_iff, support_pow_coprime, ht.card_support]
    rw [ht.order_of, Nat.coprime_iff_gcd_eq_oneₓ]
    normNum

end IsThreeCycle

section 

variable[DecidableEq α]

theorem is_three_cycle_swap_mul_swap_same {a b c : α} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
  is_three_cycle (swap a b*swap a c) :=
  by 
    suffices h : support (swap a b*swap a c) = {a, b, c}
    ·
      rw [←card_support_eq_three_iff, h]
      simp [ab, ac, bc]
    apply le_antisymmₓ ((support_mul_le _ _).trans fun x => _) fun x hx => _
    ·
      simp [ab, ac, bc]
    ·
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx 
      rw [mem_support]
      simp only [perm.coe_mul, Function.comp_app, Ne.def]
      obtain rfl | rfl | rfl := hx
      ·
        rw [swap_apply_left, swap_apply_of_ne_of_ne ac.symm bc.symm]
        exact ac.symm
      ·
        rw [swap_apply_of_ne_of_ne ab.symm bc, swap_apply_right]
        exact ab
      ·
        rw [swap_apply_right, swap_apply_left]
        exact bc

open Subgroup

theorem swap_mul_swap_same_mem_closure_three_cycles {a b c : α} (ab : a ≠ b) (ac : a ≠ c) :
  (swap a b*swap a c) ∈ closure { σ : perm α | is_three_cycle σ } :=
  by 
    byCases' bc : b = c
    ·
      subst bc 
      simp [one_mem]
    exact subset_closure (is_three_cycle_swap_mul_swap_same ab ac bc)

theorem is_swap.mul_mem_closure_three_cycles {σ τ : perm α} (hσ : is_swap σ) (hτ : is_swap τ) :
  (σ*τ) ∈ closure { σ : perm α | is_three_cycle σ } :=
  by 
    obtain ⟨a, b, ab, rfl⟩ := hσ 
    obtain ⟨c, d, cd, rfl⟩ := hτ 
    byCases' ac : a = c
    ·
      subst ac 
      exact swap_mul_swap_same_mem_closure_three_cycles ab cd 
    have h' : (swap a b*swap c d) = (swap a b*swap a c)*swap c a*swap c d
    ·
      simp [swap_comm c a, mul_assocₓ]
    rw [h']
    exact
      mul_mem _ (swap_mul_swap_same_mem_closure_three_cycles ab ac)
        (swap_mul_swap_same_mem_closure_three_cycles (Ne.symm ac) cd)

end 

end Equiv.Perm

