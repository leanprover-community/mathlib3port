import Mathbin.Data.Polynomial.AlgebraMap
import Mathbin.Data.Polynomial.Degree.Lemmas
import Mathbin.Data.Polynomial.Div

/-!
# Theory of univariate polynomials

This file starts looking like the ring theory of $ R[X] $

-/


noncomputable section

open_locale Classical

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

section CommRingₓ

variable [CommRingₓ R] {p q : Polynomial R}

variable [CommRingₓ S]

theorem nat_degree_pos_of_aeval_root [Algebra R S] {p : Polynomial R} (hp : p ≠ 0) {z : S} (hz : aeval z p = 0)
    (inj : ∀ x : R, algebraMap R S x = 0 → x = 0) : 0 < p.nat_degree :=
  nat_degree_pos_of_eval₂_root hp (algebraMap R S) hz inj

theorem degree_pos_of_aeval_root [Algebra R S] {p : Polynomial R} (hp : p ≠ 0) {z : S} (hz : aeval z p = 0)
    (inj : ∀ x : R, algebraMap R S x = 0 → x = 0) : 0 < p.degree :=
  nat_degree_pos_iff_degree_pos.mp (nat_degree_pos_of_aeval_root hp hz inj)

theorem aeval_mod_by_monic_eq_self_of_root [Algebra R S] {p q : Polynomial R} (hq : q.monic) {x : S}
    (hx : aeval x q = 0) : aeval x (p %ₘ q) = aeval x p :=
  eval₂_mod_by_monic_eq_self_of_root hq hx

theorem mod_by_monic_eq_of_dvd_sub [Nontrivial R] (hq : q.monic) {p₁ p₂ : Polynomial R} (h : q ∣ p₁ - p₂) :
    p₁ %ₘ q = p₂ %ₘ q := by
  obtain ⟨f, sub_eq⟩ := h
  refine' (div_mod_by_monic_unique (p₂ /ₘ q + f) _ hq ⟨_, degree_mod_by_monic_lt _ hq⟩).2
  rw [sub_eq_iff_eq_add.mp sub_eq, mul_addₓ, ← add_assocₓ, mod_by_monic_add_div _ hq, add_commₓ]

theorem add_mod_by_monic [Nontrivial R] (hq : q.monic) (p₁ p₂ : Polynomial R) : (p₁ + p₂) %ₘ q = p₁ %ₘ q + p₂ %ₘ q :=
  (div_mod_by_monic_unique (p₁ /ₘ q + p₂ /ₘ q) _ hq
      ⟨by
        rw [mul_addₓ, add_left_commₓ, add_assocₓ, mod_by_monic_add_div _ hq, ← add_assocₓ, add_commₓ (q * _),
          mod_by_monic_add_div _ hq],
        (degree_add_le _ _).trans_lt (max_ltₓ (degree_mod_by_monic_lt _ hq) (degree_mod_by_monic_lt _ hq))⟩).2

theorem smul_mod_by_monic [Nontrivial R] (hq : q.monic) (c : R) (p : Polynomial R) : c • p %ₘ q = c • (p %ₘ q) :=
  (div_mod_by_monic_unique (c • (p /ₘ q)) (c • (p %ₘ q)) hq
      ⟨by
        rw [mul_smul_comm, ← smul_add, mod_by_monic_add_div p hq],
        (degree_smul_le _ _).trans_lt (degree_mod_by_monic_lt _ hq)⟩).2

/-- `polynomial.mod_by_monic_hom (hq : monic (q : polynomial R))` is `_ %ₘ q` as a `R`-linear map.
-/
@[simps]
def mod_by_monic_hom [Nontrivial R] (hq : q.monic) : Polynomial R →ₗ[R] Polynomial R where
  toFun := fun p => p %ₘ q
  map_add' := add_mod_by_monic hq
  map_smul' := smul_mod_by_monic hq

end CommRingₓ

section NoZeroDivisors

variable [Ringₓ R] [NoZeroDivisors R] {p q : Polynomial R}

instance : NoZeroDivisors (Polynomial R) where
  eq_zero_or_eq_zero_of_mul_eq_zero := fun a b h => by
    rw [← leading_coeff_eq_zero, ← leading_coeff_eq_zero]
    refine' eq_zero_or_eq_zero_of_mul_eq_zero _
    rw [← leading_coeff_zero, ← leading_coeff_mul, h]

theorem nat_degree_mul (hp : p ≠ 0) (hq : q ≠ 0) : nat_degree (p * q) = nat_degree p + nat_degree q := by
  rw [← WithBot.coe_eq_coe, ← degree_eq_nat_degree (mul_ne_zero hp hq), WithBot.coe_add, ← degree_eq_nat_degree hp, ←
    degree_eq_nat_degree hq, degree_mul]

@[simp]
theorem nat_degree_pow (p : Polynomial R) (n : ℕ) : nat_degree (p ^ n) = n * nat_degree p :=
  if hp0 : p = 0 then
    if hn0 : n = 0 then by
      simp [hp0, hn0]
    else by
      rw [hp0, zero_pow (Nat.pos_of_ne_zeroₓ hn0)] <;> simp
  else
    nat_degree_pow'
      (by
        rw [← leading_coeff_pow, Ne.def, leading_coeff_eq_zero] <;> exact pow_ne_zero _ hp0)

theorem degree_le_mul_left (p : Polynomial R) (hq : q ≠ 0) : degree p ≤ degree (p * q) :=
  if hp : p = 0 then by
    simp only [hp, zero_mul, le_reflₓ]
  else by
    rw [degree_mul, degree_eq_nat_degree hp, degree_eq_nat_degree hq] <;>
      exact WithBot.coe_le_coe.2 (Nat.le_add_rightₓ _ _)

theorem nat_degree_le_of_dvd {p q : Polynomial R} (h1 : p ∣ q) (h2 : q ≠ 0) : p.nat_degree ≤ q.nat_degree := by
  rcases h1 with ⟨q, rfl⟩
  rw [mul_ne_zero_iff] at h2
  rw [nat_degree_mul h2.1 h2.2]
  exact Nat.le_add_rightₓ _ _

end NoZeroDivisors

section NoZeroDivisors

variable [CommRingₓ R] [NoZeroDivisors R] {p q : Polynomial R}

theorem root_mul : is_root (p * q) a ↔ is_root p a ∨ is_root q a := by
  simp_rw [is_root, eval_mul, mul_eq_zero]

theorem root_or_root_of_root_mul (h : is_root (p * q) a) : is_root p a ∨ is_root q a :=
  root_mul.1 h

end NoZeroDivisors

section Ringₓ

variable [Ringₓ R] [IsDomain R] {p q : Polynomial R}

instance : IsDomain (Polynomial R) :=
  { Polynomial.no_zero_divisors, Polynomial.nontrivial with }

theorem nat_trailing_degree_mul (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).natTrailingDegree = p.nat_trailing_degree + q.nat_trailing_degree := by
  simp only [← tsub_eq_of_eq_add_rev (nat_degree_eq_reverse_nat_degree_add_nat_trailing_degree _)]
  rw [reverse_mul_of_domain, nat_degree_mul hp hq, nat_degree_mul (mt reverse_eq_zero.mp hp) (mt reverse_eq_zero.mp hq),
    reverse_nat_degree, reverse_nat_degree, tsub_add_eq_tsub_tsub, Nat.add_comm, add_tsub_assoc_of_le (Nat.sub_leₓ _ _),
    add_commₓ, add_tsub_assoc_of_le (Nat.sub_leₓ _ _)]

end Ringₓ

section CommRingₓ

variable [CommRingₓ R] [IsDomain R] {p q : Polynomial R}

section Roots

open Multiset

theorem degree_eq_zero_of_is_unit (h : IsUnit p) : degree p = 0 := by
  let ⟨q, hq⟩ := is_unit_iff_dvd_one.1 h
  have hp0 : p ≠ 0 := fun hp0 => by
    simpa [hp0] using hq
  have hq0 : q ≠ 0 := fun hp0 => by
    simpa [hp0] using hq
  have : nat_degree (1 : Polynomial R) = nat_degree (p * q) := congr_argₓ _ hq
  rw [nat_degree_one, nat_degree_mul hp0 hq0, eq_comm, _root_.add_eq_zero_iff, ← WithBot.coe_eq_coe, ←
      degree_eq_nat_degree hp0] at this <;>
    exact this.1

@[simp]
theorem degree_coe_units (u : (Polynomial R)ˣ) : degree (u : Polynomial R) = 0 :=
  degree_eq_zero_of_is_unit ⟨u, rfl⟩

theorem prime_X_sub_C (r : R) : Prime (X - C r) :=
  ⟨X_sub_C_ne_zero r, not_is_unit_X_sub_C r, fun _ _ => by
    simp_rw [dvd_iff_is_root, is_root.def, eval_mul, mul_eq_zero]
    exact id⟩

theorem prime_X : Prime (X : Polynomial R) := by
  convert prime_X_sub_C (0 : R)
  simp

theorem monic.prime_of_degree_eq_one (hp1 : degree p = 1) (hm : monic p) : Prime p :=
  have : p = X - C (-p.coeff 0) := by
    simpa [hm.leading_coeff] using eq_X_add_C_of_degree_eq_one hp1
  this.symm ▸ prime_X_sub_C _

theorem irreducible_X_sub_C (r : R) : Irreducible (X - C r) :=
  (prime_X_sub_C r).Irreducible

theorem irreducible_X : Irreducible (X : Polynomial R) :=
  Prime.irreducible prime_X

theorem monic.irreducible_of_degree_eq_one (hp1 : degree p = 1) (hm : monic p) : Irreducible p :=
  (hm.prime_of_degree_eq_one hp1).Irreducible

theorem eq_of_monic_of_associated (hp : p.monic) (hq : q.monic) (hpq : Associated p q) : p = q := by
  obtain ⟨u, hu⟩ := hpq
  unfold monic  at hp hq
  rw [eq_C_of_degree_le_zero (le_of_eqₓ $ degree_coe_units _)] at hu
  rw [← hu, leading_coeff_mul, hp, one_mulₓ, leading_coeff_C] at hq
  rwa [hq, C_1, mul_oneₓ] at hu
  infer_instance

theorem root_multiplicity_mul {p q : Polynomial R} {x : R} (hpq : p * q ≠ 0) :
    root_multiplicity x (p * q) = root_multiplicity x p + root_multiplicity x q := by
  have hp : p ≠ 0 := left_ne_zero_of_mul hpq
  have hq : q ≠ 0 := right_ne_zero_of_mul hpq
  rw [root_multiplicity_eq_multiplicity (p * q), dif_neg hpq, root_multiplicity_eq_multiplicity p, dif_neg hp,
    root_multiplicity_eq_multiplicity q, dif_neg hq, multiplicity.mul' (prime_X_sub_C x)]

theorem root_multiplicity_X_sub_C_self {x : R} : root_multiplicity x (X - C x) = 1 := by
  rw [root_multiplicity_eq_multiplicity, dif_neg (X_sub_C_ne_zero x), multiplicity.get_multiplicity_self]

theorem root_multiplicity_X_sub_C {x y : R} : root_multiplicity x (X - C y) = if x = y then 1 else 0 := by
  split_ifs with hxy
  · rw [hxy]
    exact root_multiplicity_X_sub_C_self
    
  exact root_multiplicity_eq_zero (mt root_X_sub_C.mp (Ne.symm hxy))

/-- The multiplicity of `a` as root of `(X - a) ^ n` is `n`. -/
theorem root_multiplicity_X_sub_C_pow (a : R) (n : ℕ) : root_multiplicity a ((X - C a) ^ n) = n := by
  induction' n with n hn
  · refine' root_multiplicity_eq_zero _
    simp only [eval_one, is_root.def, not_false_iff, one_ne_zero, pow_zeroₓ]
    
  have hzero := ne_zero_of_monic (monic_pow (monic_X_sub_C a) n.succ)
  rw [pow_succₓ (X - C a) n] at hzero⊢
  simp only [root_multiplicity_mul hzero, root_multiplicity_X_sub_C_self, hn, Nat.one_add]

/-- If `(X - a) ^ n` divides a polynomial `p` then the multiplicity of `a` as root of `p` is at
least `n`. -/
theorem root_multiplicity_of_dvd {p : Polynomial R} {a : R} {n : ℕ} (hzero : p ≠ 0) (h : (X - C a) ^ n ∣ p) :
    n ≤ root_multiplicity a p := by
  obtain ⟨q, hq⟩ := exists_eq_mul_right_of_dvd h
  rw [hq] at hzero
  simp only [hq, root_multiplicity_mul hzero, root_multiplicity_X_sub_C_pow, ge_iff_le, _root_.zero_le,
    le_add_iff_nonneg_right]

/-- The multiplicity of `p + q` is at least the minimum of the multiplicities. -/
theorem root_multiplicity_add {p q : Polynomial R} (a : R) (hzero : p + q ≠ 0) :
    min (root_multiplicity a p) (root_multiplicity a q) ≤ root_multiplicity a (p + q) := by
  refine' root_multiplicity_of_dvd hzero _
  have hdivp : (X - C a) ^ root_multiplicity a p ∣ p := pow_root_multiplicity_dvd p a
  have hdivq : (X - C a) ^ root_multiplicity a q ∣ q := pow_root_multiplicity_dvd q a
  exact min_pow_dvd_add hdivp hdivq

theorem exists_multiset_roots :
    ∀ {p : Polynomial R} hp : p ≠ 0,
      ∃ s : Multiset R, (s.card : WithBot ℕ) ≤ degree p ∧ ∀ a, s.count a = root_multiplicity a p
  | p => fun hp =>
    have := Classical.propDecidable (∃ x, is_root p x)
    if h : ∃ x, is_root p x then
      let ⟨x, hx⟩ := h
      have hpd : 0 < degree p := degree_pos_of_root hp hx
      have hd0 : p /ₘ (X - C x) ≠ 0 := fun h => by
        rw [← mul_div_by_monic_eq_iff_is_root.2 hx, h, mul_zero] at hp <;> exact hp rfl
      have wf : degree (p /ₘ _) < degree p :=
        degree_div_by_monic_lt _ (monic_X_sub_C x) hp
          ((degree_X_sub_C x).symm ▸ by
            decide)
      let ⟨t, htd, htr⟩ := @exists_multiset_roots (p /ₘ (X - C x)) hd0
      have hdeg : degree (X - C x) ≤ degree p := by
        rw [degree_X_sub_C, degree_eq_nat_degree hp]
        rw [degree_eq_nat_degree hp] at hpd
        exact WithBot.coe_le_coe.2 (WithBot.coe_lt_coe.1 hpd)
      have hdiv0 : p /ₘ (X - C x) ≠ 0 := mt (div_by_monic_eq_zero_iff (monic_X_sub_C x)).1 $ not_ltₓ.2 hdeg
      ⟨x ::ₘ t,
        calc
          (card (x ::ₘ t) : WithBot ℕ) = t.card + 1 := by
            exact_mod_cast card_cons _ _
          _ ≤ degree p := by
            rw [← degree_add_div_by_monic (monic_X_sub_C x) hdeg, degree_X_sub_C, add_commₓ] <;>
              exact add_le_add (le_reflₓ (1 : WithBot ℕ)) htd
          ,
        by
        intro a
        conv_rhs => rw [← mul_div_by_monic_eq_iff_is_root.mpr hx]
        rw [root_multiplicity_mul (mul_ne_zero (X_sub_C_ne_zero x) hdiv0), root_multiplicity_X_sub_C, ← htr a]
        split_ifs with ha
        · rw [ha, count_cons_self, Nat.succ_eq_add_one, add_commₓ]
          
        · rw [count_cons_of_ne ha, zero_addₓ]
          ⟩
    else
      ⟨0, (degree_eq_nat_degree hp).symm ▸ WithBot.coe_le_coe.2 (Nat.zero_leₓ _), by
        intro a
        rw [count_zero, root_multiplicity_eq_zero (not_exists.mp h a)]⟩

/-- `roots p` noncomputably gives a multiset containing all the roots of `p`,
including their multiplicities. -/
noncomputable def roots (p : Polynomial R) : Multiset R :=
  if h : p = 0 then ∅ else Classical.some (exists_multiset_roots h)

@[simp]
theorem roots_zero : (0 : Polynomial R).roots = 0 :=
  dif_pos rfl

theorem card_roots (hp0 : p ≠ 0) : ((roots p).card : WithBot ℕ) ≤ degree p := by
  unfold roots
  rw [dif_neg hp0]
  exact (Classical.some_spec (exists_multiset_roots hp0)).1

theorem card_roots' (p : Polynomial R) : p.roots.card ≤ nat_degree p := by
  by_cases' hp0 : p = 0
  · simp [hp0]
    
  exact WithBot.coe_le_coe.1 (le_transₓ (card_roots hp0) (le_of_eqₓ $ degree_eq_nat_degree hp0))

theorem card_roots_sub_C {p : Polynomial R} {a : R} (hp0 : 0 < degree p) :
    ((p - C a).roots.card : WithBot ℕ) ≤ degree p :=
  calc
    ((p - C a).roots.card : WithBot ℕ) ≤ degree (p - C a) :=
      card_roots $ mt sub_eq_zero.1 $ fun h => not_le_of_gtₓ hp0 $ h.symm ▸ degree_C_le
    _ = degree p := by
      rw [sub_eq_add_neg, ← C_neg] <;> exact degree_add_C hp0
    

theorem card_roots_sub_C' {p : Polynomial R} {a : R} (hp0 : 0 < degree p) : (p - C a).roots.card ≤ nat_degree p :=
  WithBot.coe_le_coe.1
    (le_transₓ (card_roots_sub_C hp0)
      (le_of_eqₓ $
        degree_eq_nat_degree fun h => by
          simp_all [lt_irreflₓ]))

@[simp]
theorem count_roots (p : Polynomial R) : p.roots.count a = root_multiplicity a p := by
  by_cases' hp : p = 0
  · simp [hp]
    
  rw [roots, dif_neg hp]
  exact (Classical.some_spec (exists_multiset_roots hp)).2 a

@[simp]
theorem mem_roots (hp : p ≠ 0) : a ∈ p.roots ↔ is_root p a := by
  rw [← count_pos, count_roots p, root_multiplicity_pos hp]

theorem card_le_degree_of_subset_roots {p : Polynomial R} {Z : Finset R} (h : Z.val ⊆ p.roots) :
    Z.card ≤ p.nat_degree :=
  (Multiset.card_le_of_le (Finset.val_le_iff_val_subset.2 h)).trans (Polynomial.card_roots' p)

theorem eq_zero_of_infinite_is_root (p : Polynomial R) (h : Set.Infinite { x | is_root p x }) : p = 0 := by
  by_contra hp
  apply h
  convert p.roots.to_finset.finite_to_set using 1
  ext1 r
  simp only [mem_roots hp, Multiset.mem_to_finset, Set.mem_set_of_eq, Finset.mem_coe]

theorem exists_max_root [LinearOrderₓ R] (p : Polynomial R) (hp : p ≠ 0) : ∃ x₀, ∀ x, p.is_root x → x ≤ x₀ :=
  Set.exists_upper_bound_image _ _ $ not_not.mp (mt (eq_zero_of_infinite_is_root p) hp)

theorem exists_min_root [LinearOrderₓ R] (p : Polynomial R) (hp : p ≠ 0) : ∃ x₀, ∀ x, p.is_root x → x₀ ≤ x :=
  Set.exists_lower_bound_image _ _ $ not_not.mp (mt (eq_zero_of_infinite_is_root p) hp)

theorem eq_of_infinite_eval_eq {R : Type _} [CommRingₓ R] [IsDomain R] (p q : Polynomial R)
    (h : Set.Infinite { x | eval x p = eval x q }) : p = q := by
  rw [← sub_eq_zero]
  apply eq_zero_of_infinite_is_root
  simpa only [is_root, eval_sub, sub_eq_zero]

theorem roots_mul {p q : Polynomial R} (hpq : p * q ≠ 0) : (p * q).roots = p.roots + q.roots :=
  Multiset.ext.mpr $ fun r => by
    rw [count_add, count_roots, count_roots, count_roots, root_multiplicity_mul hpq]

theorem roots.le_of_dvd (h : q ≠ 0) : p ∣ q → roots p ≤ roots q := by
  rintro ⟨k, rfl⟩
  exact multiset.le_iff_exists_add.mpr ⟨k.roots, roots_mul h⟩

@[simp]
theorem mem_roots_sub_C {p : Polynomial R} {a x : R} (hp0 : 0 < degree p) : x ∈ (p - C a).roots ↔ p.eval x = a :=
  (mem_roots (show p - C a ≠ 0 from mt sub_eq_zero.1 $ fun h => not_le_of_gtₓ hp0 $ h.symm ▸ degree_C_le)).trans
    (by
      rw [is_root.def, eval_sub, eval_C, sub_eq_zero])

@[simp]
theorem roots_X_sub_C (r : R) : roots (X - C r) = {r} := by
  ext s
  rw [count_roots, root_multiplicity_X_sub_C]
  split_ifs with h
  · rw [h, count_singleton_self]
    
  · rw [singleton_eq_cons, count_cons_of_ne h, count_zero]
    

@[simp]
theorem roots_C (x : R) : (C x).roots = 0 :=
  if H : x = 0 then by
    rw [H, C_0, roots_zero]
  else
    Multiset.ext.mpr $ fun r => by
      rw [count_roots, count_zero, root_multiplicity_eq_zero (not_is_root_C _ _ H)]

@[simp]
theorem roots_one : (1 : Polynomial R).roots = ∅ :=
  roots_C 1

theorem roots_smul_nonzero (p : Polynomial R) {r : R} (hr : r ≠ 0) : (r • p).roots = p.roots := by
  by_cases' hp : p = 0 <;> simp [smul_eq_C_mul, roots_mul, hr, hp]

theorem roots_list_prod (L : List (Polynomial R)) :
    (0 : Polynomial R) ∉ L → L.prod.roots = (L : Multiset (Polynomial R)).bind roots :=
  (List.recOn L fun _ => roots_one) $ fun hd tl ih H => by
    rw [List.mem_cons_iff, not_or_distrib] at H
    rw [List.prod_cons, roots_mul (mul_ne_zero (Ne.symm H.1) $ List.prod_ne_zero H.2), ← Multiset.cons_coe,
      Multiset.cons_bind, ih H.2]

theorem roots_multiset_prod (m : Multiset (Polynomial R)) : (0 : Polynomial R) ∉ m → m.prod.roots = m.bind roots := by
  rcases m with ⟨L⟩
  simpa only [coe_prod, quot_mk_to_coe''] using roots_list_prod L

theorem roots_prod {ι : Type _} (f : ι → Polynomial R) (s : Finset ι) :
    s.prod f ≠ 0 → (s.prod f).roots = s.val.bind fun i => roots (f i) := by
  rcases s with ⟨m, hm⟩
  simpa [Multiset.prod_eq_zero_iff, bind_map] using roots_multiset_prod (m.map f)

theorem roots_prod_X_sub_C (s : Finset R) : (s.prod fun a => X - C a).roots = s.val :=
  (roots_prod (fun a => X - C a) s (prod_ne_zero_iff.mpr fun a _ => X_sub_C_ne_zero a)).trans
    (by
      simp_rw [roots_X_sub_C, Multiset.bind_singleton, Multiset.map_id'])

theorem card_roots_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) : (roots ((X : Polynomial R) ^ n - C a)).card ≤ n :=
  WithBot.coe_le_coe.1 $
    calc
      ((roots ((X : Polynomial R) ^ n - C a)).card : WithBot ℕ) ≤ degree ((X : Polynomial R) ^ n - C a) :=
        card_roots (X_pow_sub_C_ne_zero hn a)
      _ = n := degree_X_pow_sub_C hn a
      

theorem le_root_multiplicity_map {K L : Type _} [CommRingₓ K] [CommRingₓ L] {p : Polynomial K} {f : K →+* L}
    (hf : Function.Injective f) (a : K) : root_multiplicity a p ≤ root_multiplicity (f a) (map f p) := by
  by_cases' hp0 : p = 0
  · simp only [hp0, root_multiplicity_zero, map_zero]
    
  have hmap : map f p ≠ 0 := by
    simpa only [map_zero] using (map_injective f hf).Ne hp0
  rw [root_multiplicity, root_multiplicity, dif_neg hp0, dif_neg hmap]
  simp only [not_not, Nat.lt_find_iff, Nat.le_find_iff]
  intro m hm
  have := RingHom.map_dvd (map_ring_hom f) (hm m le_rfl)
  simpa only [coe_map_ring_hom, map_pow, map_sub, map_X, map_C]

theorem count_map_roots {K L : Type _} [CommRingₓ K] [IsDomain K] [CommRingₓ L] {p : Polynomial K} {f : K →+* L}
    (hf : Function.Injective f) (a : L) : count a (Multiset.map f p.roots) ≤ root_multiplicity a (map f p) := by
  by_cases' h : ∃ t, f t = a
  · rcases h with ⟨h_w, rfl⟩
    rw [Multiset.count_map_eq_count' f _ hf, count_roots]
    exact le_root_multiplicity_map hf h_w
    
  · suffices Multiset.count a (Multiset.map f p.roots) = 0 by
      rw [this]
      exact zero_le _
    rw [Multiset.count_map, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    rintro k hk rfl
    exact h ⟨k, rfl⟩
    

theorem roots_map_of_injective_card_eq_total_degree {K L : Type _} [CommRingₓ K] [IsDomain K] [CommRingₓ L] [IsDomain L]
    {p : Polynomial K} {f : K →+* L} (hf : Function.Injective f) (hroots : p.roots.card = p.nat_degree) :
    Multiset.map f p.roots = (map f p).roots := by
  by_cases' hp0 : p = 0
  · simp only [hp0, roots_zero, Multiset.map_zero, map_zero]
    
  have hmap : map f p ≠ 0 := by
    simpa only [map_zero] using (map_injective f hf).Ne hp0
  apply Multiset.eq_of_le_of_card_le
  · simpa only [Multiset.le_iff_count, count_roots] using count_map_roots hf
    
  · simpa only [Multiset.card_map, hroots] using (card_roots' _).trans (nat_degree_map_le f p)
    

section NthRoots

/-- `nth_roots n a` noncomputably returns the solutions to `x ^ n = a`-/
def nth_roots (n : ℕ) (a : R) : Multiset R :=
  roots ((X : Polynomial R) ^ n - C a)

@[simp]
theorem mem_nth_roots {n : ℕ} (hn : 0 < n) {a x : R} : x ∈ nth_roots n a ↔ x ^ n = a := by
  rw [nth_roots, mem_roots (X_pow_sub_C_ne_zero hn a), is_root.def, eval_sub, eval_C, eval_pow, eval_X, sub_eq_zero]

@[simp]
theorem nth_roots_zero (r : R) : nth_roots 0 r = 0 := by
  simp only [empty_eq_zero, pow_zeroₓ, nth_roots, ← C_1, ← C_sub, roots_C]

theorem card_nth_roots (n : ℕ) (a : R) : (nth_roots n a).card ≤ n :=
  if hn : n = 0 then
    if h : (X : Polynomial R) ^ n - C a = 0 then by
      simp only [Nat.zero_leₓ, nth_roots, roots, h, dif_pos rfl, empty_eq_zero, card_zero]
    else
      WithBot.coe_le_coe.1
        (le_transₓ (card_roots h)
          (by
            rw [hn, pow_zeroₓ, ← C_1, ← RingHom.map_sub]
            exact degree_C_le))
  else by
    rw [← WithBot.coe_le_coe, ← degree_X_pow_sub_C (Nat.pos_of_ne_zeroₓ hn) a] <;>
      exact card_roots (X_pow_sub_C_ne_zero (Nat.pos_of_ne_zeroₓ hn) a)

/-- The multiset `nth_roots ↑n (1 : R)` as a finset. -/
def nth_roots_finset (n : ℕ) (R : Type _) [CommRingₓ R] [IsDomain R] : Finset R :=
  Multiset.toFinset (nth_roots n (1 : R))

@[simp]
theorem mem_nth_roots_finset {n : ℕ} (h : 0 < n) {x : R} : x ∈ nth_roots_finset n R ↔ x ^ (n : ℕ) = 1 := by
  rw [nth_roots_finset, mem_to_finset, mem_nth_roots h]

@[simp]
theorem nth_roots_finset_zero : nth_roots_finset 0 R = ∅ := by
  simp [nth_roots_finset]

end NthRoots

theorem coeff_comp_degree_mul_degree (hqd0 : nat_degree q ≠ 0) :
    coeff (p.comp q) (nat_degree p * nat_degree q) = leading_coeff p * leading_coeff q ^ nat_degree p :=
  if hp0 : p = 0 then by
    simp [hp0]
  else
    calc
      coeff (p.comp q) (nat_degree p * nat_degree q) =
          p.sum fun n a => coeff (C a * q ^ n) (nat_degree p * nat_degree q) :=
        by
        rw [comp, eval₂, coeff_sum]
      _ = coeff (C (leading_coeff p) * q ^ nat_degree p) (nat_degree p * nat_degree q) :=
        Finset.sum_eq_single _
          (by
            intro b hbs hbp
            have hq0 : q ≠ 0 := fun hq0 =>
              hqd0
                (by
                  rw [hq0, nat_degree_zero])
            have : coeff p b ≠ 0 := by
              rwa [mem_support_iff] at hbs
            refine' coeff_eq_zero_of_degree_lt _
            erw [degree_mul, degree_C this, degree_pow, zero_addₓ, degree_eq_nat_degree hq0, ← WithBot.coe_nsmul,
              nsmul_eq_mul, WithBot.coe_lt_coe, Nat.cast_id, mul_lt_mul_right (pos_iff_ne_zero.mpr hqd0)]
            exact lt_of_le_of_neₓ (le_nat_degree_of_ne_zero this) hbp)
          (by
            intro h
            contrapose! hp0
            rw [mem_support_iff] at h
            push_neg  at h
            rwa [← leading_coeff_eq_zero])
      _ = _ := by
        have : coeff (q ^ nat_degree p) (nat_degree p * nat_degree q) = leading_coeff (q ^ nat_degree p) := by
          rw [leading_coeff, nat_degree_pow]
        rw [coeff_C_mul, this, leading_coeff_pow]
      

theorem nat_degree_comp : nat_degree (p.comp q) = nat_degree p * nat_degree q :=
  le_antisymmₓ nat_degree_comp_le
    (if hp0 : p = 0 then by
      rw [hp0, zero_comp, nat_degree_zero, zero_mul]
    else
      if hqd0 : nat_degree q = 0 then by
        have : degree q ≤ 0 := by
          rw [← WithBot.coe_zero, ← hqd0] <;> exact degree_le_nat_degree
        rw [eq_C_of_degree_le_zero this] <;> simp
      else
        le_nat_degree_of_ne_zero $
          have hq0 : q ≠ 0 := fun hq0 =>
            hqd0 $ by
              rw [hq0, nat_degree_zero]
          calc
            coeff (p.comp q) (nat_degree p * nat_degree q) = leading_coeff p * leading_coeff q ^ nat_degree p :=
              coeff_comp_degree_mul_degree hqd0
            _ ≠ 0 := mul_ne_zero (mt leading_coeff_eq_zero.1 hp0) (pow_ne_zero _ (mt leading_coeff_eq_zero.1 hq0))
            )

theorem leading_coeff_comp (hq : nat_degree q ≠ 0) :
    leading_coeff (p.comp q) = leading_coeff p * leading_coeff q ^ nat_degree p := by
  rw [← coeff_comp_degree_mul_degree hq, ← nat_degree_comp] <;> rfl

theorem units_coeff_zero_smul (c : (Polynomial R)ˣ) (p : Polynomial R) : (c : Polynomial R).coeff 0 • p = c * p := by
  rw [← Polynomial.C_mul', ← Polynomial.eq_C_of_degree_eq_zero (degree_coe_units c)]

@[simp]
theorem nat_degree_coe_units (u : (Polynomial R)ˣ) : nat_degree (u : Polynomial R) = 0 :=
  nat_degree_eq_of_degree_eq_some (degree_coe_units u)

theorem comp_eq_zero_iff : p.comp q = 0 ↔ p = 0 ∨ p.eval (q.coeff 0) = 0 ∧ q = C (q.coeff 0) := by
  constructor
  · intro h
    have key : p.nat_degree = 0 ∨ q.nat_degree = 0 := by
      rw [← mul_eq_zero, ← nat_degree_comp, h, nat_degree_zero]
    replace key := Or.imp eq_C_of_nat_degree_eq_zero eq_C_of_nat_degree_eq_zero key
    cases key
    · rw [key, C_comp] at h
      exact Or.inl (key.trans h)
      
    · rw [key, comp_C, C_eq_zero] at h
      exact Or.inr ⟨h, key⟩
      
    
  · exact fun h =>
      Or.ndrec
        (fun h => by
          rw [h, zero_comp])
        (fun h => by
          rw [h.2, comp_C, h.1, C_0])
        h
    

theorem zero_of_eval_zero [Infinite R] (p : Polynomial R) (h : ∀ x, p.eval x = 0) : p = 0 := by
  classical <;>
    by_contra hp <;>
      exact Fintype.false ⟨p.roots.to_finset, fun x => multiset.mem_to_finset.mpr ((mem_roots hp).mpr (h _))⟩

theorem funext [Infinite R] {p q : Polynomial R} (ext : ∀ r : R, p.eval r = q.eval r) : p = q := by
  rw [← sub_eq_zero]
  apply zero_of_eval_zero
  intro x
  rw [eval_sub, sub_eq_zero, ext]

variable [CommRingₓ T]

/-- The set of distinct roots of `p` in `E`.

If you have a non-separable polynomial, use `polynomial.roots` for the multiset
where multiple roots have the appropriate multiplicity. -/
def root_set (p : Polynomial T) S [CommRingₓ S] [IsDomain S] [Algebra T S] : Set S :=
  (p.map (algebraMap T S)).roots.toFinset

theorem root_set_def (p : Polynomial T) S [CommRingₓ S] [IsDomain S] [Algebra T S] :
    p.root_set S = (p.map (algebraMap T S)).roots.toFinset :=
  rfl

@[simp]
theorem root_set_zero S [CommRingₓ S] [IsDomain S] [Algebra T S] : (0 : Polynomial T).RootSet S = ∅ := by
  rw [root_set_def, Polynomial.map_zero, roots_zero, to_finset_zero, Finset.coe_empty]

@[simp]
theorem root_set_C [CommRingₓ S] [IsDomain S] [Algebra T S] (a : T) : (C a).RootSet S = ∅ := by
  rw [root_set_def, map_C, roots_C, Multiset.to_finset_zero, Finset.coe_empty]

instance root_set_fintype (p : Polynomial T) (S : Type _) [CommRingₓ S] [IsDomain S] [Algebra T S] :
    Fintype (p.root_set S) :=
  FinsetCoe.fintype _

theorem root_set_finite (p : Polynomial T) (S : Type _) [CommRingₓ S] [IsDomain S] [Algebra T S] :
    (p.root_set S).Finite :=
  ⟨Polynomial.rootSetFintype p S⟩

end Roots

theorem is_unit_iff {f : Polynomial R} : IsUnit f ↔ ∃ r : R, IsUnit r ∧ C r = f :=
  ⟨fun hf =>
    ⟨f.coeff 0, is_unit_C.1 $ eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit hf) ▸ hf,
      (eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit hf)).symm⟩,
    fun ⟨r, hr, hrf⟩ => hrf ▸ is_unit_C.2 hr⟩

theorem coeff_coe_units_zero_ne_zero (u : (Polynomial R)ˣ) : coeff (u : Polynomial R) 0 ≠ 0 := by
  conv in 0 => rw [← nat_degree_coe_units u]
  rw [← leading_coeff, Ne.def, leading_coeff_eq_zero]
  exact Units.ne_zero _

theorem degree_eq_degree_of_associated (h : Associated p q) : degree p = degree q := by
  let ⟨u, hu⟩ := h
  simp [hu.symm]

theorem degree_eq_one_of_irreducible_of_root (hi : Irreducible p) {x : R} (hx : is_root p x) : degree p = 1 :=
  let ⟨g, hg⟩ := dvd_iff_is_root.2 hx
  have : IsUnit (X - C x) ∨ IsUnit g := hi.is_unit_or_is_unit hg
  this.elim
    (fun h => by
      have h₁ : degree (X - C x) = 1 := degree_X_sub_C x
      have h₂ : degree (X - C x) = 0 := degree_eq_zero_of_is_unit h
      rw [h₁] at h₂ <;>
        exact
          absurd h₂
            (by
              decide))
    fun hgu => by
    rw [hg, degree_mul, degree_X_sub_C, degree_eq_zero_of_is_unit hgu, add_zeroₓ]

/-- Division by a monic polynomial doesn't change the leading coefficient. -/
theorem leading_coeff_div_by_monic_of_monic {R : Type u} [CommRingₓ R] {p q : Polynomial R} (hmonic : q.monic)
    (hdegree : q.degree ≤ p.degree) : (p /ₘ q).leadingCoeff = p.leading_coeff := by
  nontriviality
  have h : q.leading_coeff * (p /ₘ q).leadingCoeff ≠ 0 := by
    simpa [div_by_monic_eq_zero_iff hmonic, hmonic.leading_coeff, Nat.WithBot.one_le_iff_zero_lt] using hdegree
  nth_rw_rhs 0[← mod_by_monic_add_div p hmonic]
  rw [leading_coeff_add_of_degree_lt, leading_coeff_monic_mul hmonic]
  rw [degree_mul' h, degree_add_div_by_monic hmonic hdegree]
  exact (degree_mod_by_monic_lt p hmonic).trans_le hdegree

theorem leading_coeff_div_by_monic_X_sub_C (p : Polynomial R) (hp : degree p ≠ 0) (a : R) :
    leading_coeff (p /ₘ (X - C a)) = leading_coeff p := by
  nontriviality
  cases' hp.lt_or_lt with hd hd
  · rw [degree_eq_bot.mp $ (Nat.WithBot.lt_zero_iff _).mp hd, zero_div_by_monic]
    
  refine' leading_coeff_div_by_monic_of_monic (monic_X_sub_C a) _
  rwa [degree_X_sub_C, Nat.WithBot.one_le_iff_zero_lt]

theorem eq_of_monic_of_dvd_of_nat_degree_le (hp : p.monic) (hq : q.monic) (hdiv : p ∣ q)
    (hdeg : q.nat_degree ≤ p.nat_degree) : q = p := by
  obtain ⟨r, hr⟩ := hdiv
  have rzero : r ≠ 0 := by
    intro h
    simpa [h, monic.ne_zero hq] using hr
  rw [hr, nat_degree_mul (monic.ne_zero hp) rzero] at hdeg
  have hdegeq : p.nat_degree + r.nat_degree = p.nat_degree := by
    suffices hdegle : p.nat_degree ≤ p.nat_degree + r.nat_degree
    · exact le_antisymmₓ hdeg hdegle
      
    exact Nat.Le.intro rfl
  replace hdegeq := eq_C_of_nat_degree_eq_zero (((@add_right_injₓ _ _ p.nat_degree) _ 0).1 hdegeq)
  suffices hlead : 1 = r.leading_coeff
  · have hcoeff := leading_coeff_C (r.coeff 0)
    rw [← hdegeq, ← hlead] at hcoeff
    rw [← hcoeff, C_1] at hdegeq
    rwa [hdegeq, mul_oneₓ] at hr
    
  have hprod : q.leading_coeff = p.leading_coeff * r.leading_coeff := by
    simp only [hr, leading_coeff_mul]
  rwa [monic.leading_coeff hp, monic.leading_coeff hq, one_mulₓ] at hprod

end CommRingₓ

section

variable [Semiringₓ R] [CommRingₓ S] [IsDomain S] (φ : R →+* S)

theorem is_unit_of_is_unit_leading_coeff_of_is_unit_map (f : Polynomial R) (hf : IsUnit (leading_coeff f))
    (H : IsUnit (map φ f)) : IsUnit f := by
  have dz := degree_eq_zero_of_is_unit H
  rw [degree_map_eq_of_leading_coeff_ne_zero] at dz
  · rw [eq_C_of_degree_eq_zero dz]
    refine' IsUnit.map (C.to_monoid_hom : R →* Polynomial R) _
    convert hf
    rw [(degree_eq_iff_nat_degree_eq _).1 dz]
    rintro rfl
    simpa using H
    
  · intro h
    have u : IsUnit (φ f.leading_coeff) := IsUnit.map φ.to_monoid_hom hf
    rw [h] at u
    simpa using u
    

end

section

variable [CommRingₓ R] [IsDomain R] [CommRingₓ S] [IsDomain S] (φ : R →+* S)

/-- A polynomial over an integral domain `R` is irreducible if it is monic and
  irreducible after mapping into an integral domain `S`.

A special case of this lemma is that a polynomial over `ℤ` is irreducible if
  it is monic and irreducible over `ℤ/pℤ` for some prime `p`.
-/
theorem monic.irreducible_of_irreducible_map (f : Polynomial R) (h_mon : monic f) (h_irr : Irreducible (map φ f)) :
    Irreducible f := by
  fconstructor
  · intro h
    exact h_irr.not_unit (IsUnit.map (map_ring_hom φ).toMonoidHom h)
    
  · intro a b h
    have q := (leading_coeff_mul a b).symm
    rw [← h] at q
    dsimp [monic]  at h_mon
    rw [h_mon] at q
    have au : IsUnit a.leading_coeff := is_unit_of_mul_eq_one _ _ q
    rw [mul_comm] at q
    have bu : IsUnit b.leading_coeff := is_unit_of_mul_eq_one _ _ q
    clear q h_mon
    have h' := congr_argₓ (map φ) h
    simp only [map_mul] at h'
    cases' h_irr.is_unit_or_is_unit h' with w w
    · left
      exact is_unit_of_is_unit_leading_coeff_of_is_unit_map _ _ au w
      
    · right
      exact is_unit_of_is_unit_leading_coeff_of_is_unit_map _ _ bu w
      
    

end

end Polynomial

