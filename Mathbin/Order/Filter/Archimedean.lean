import Mathbin.Algebra.Order.Archimedean
import Mathbin.Order.Filter.AtTopBot

/-!
# `at_top` filter and archimedean (semi)rings/fields

In this file we prove that for a linear ordered archimedean semiring `R` and a function `f : α → ℕ`,
the function `coe ∘ f : α → R` tends to `at_top` along a filter `l` if and only if so does `f`.
We also prove that `coe : ℕ → R` tends to `at_top` along `at_top`, as well as version of these
two results for `ℤ` (and a ring `R`) and `ℚ` (and a field `R`).
-/


variable {α R : Type _}

open Filter Set

@[simp]
theorem Nat.comap_coe_at_top [OrderedSemiring R] [Nontrivial R] [Archimedean R] :
    comap (coeₓ : ℕ → R) at_top = at_top :=
  comap_embedding_at_top (fun _ _ => Nat.cast_le) exists_nat_ge

theorem tendsto_coe_nat_at_top_iff [OrderedSemiring R] [Nontrivial R] [Archimedean R] {f : α → ℕ} {l : Filter α} :
    tendsto (fun n => (f n : R)) l at_top ↔ tendsto f l at_top :=
  tendsto_at_top_embedding (fun a₁ a₂ => Nat.cast_le) exists_nat_ge

theorem tendsto_coe_nat_at_top_at_top [OrderedSemiring R] [Archimedean R] : tendsto (coeₓ : ℕ → R) at_top at_top :=
  Nat.mono_cast.tendsto_at_top_at_top exists_nat_ge

@[simp]
theorem Int.comap_coe_at_top [OrderedRing R] [Nontrivial R] [Archimedean R] : comap (coeₓ : ℤ → R) at_top = at_top :=
  (comap_embedding_at_top fun _ _ => Int.cast_le) $ fun r =>
    let ⟨n, hn⟩ := exists_nat_ge r
    ⟨n, hn⟩

@[simp]
theorem Int.comap_coe_at_bot [OrderedRing R] [Nontrivial R] [Archimedean R] : comap (coeₓ : ℤ → R) at_bot = at_bot :=
  (comap_embedding_at_bot fun _ _ => Int.cast_le) $ fun r =>
    let ⟨n, hn⟩ := exists_nat_ge (-r)
    ⟨-n, by
      simpa [neg_le] using hn⟩

theorem tendsto_coe_int_at_top_iff [OrderedRing R] [Nontrivial R] [Archimedean R] {f : α → ℤ} {l : Filter α} :
    tendsto (fun n => (f n : R)) l at_top ↔ tendsto f l at_top := by
  rw [← tendsto_comap_iff, Int.comap_coe_at_top]

theorem tendsto_coe_int_at_bot_iff [OrderedRing R] [Nontrivial R] [Archimedean R] {f : α → ℤ} {l : Filter α} :
    tendsto (fun n => (f n : R)) l at_bot ↔ tendsto f l at_bot := by
  rw [← tendsto_comap_iff, Int.comap_coe_at_bot]

theorem tendsto_coe_int_at_top_at_top [OrderedRing R] [Archimedean R] : tendsto (coeₓ : ℤ → R) at_top at_top :=
  Int.cast_mono.tendsto_at_top_at_top $ fun b =>
    let ⟨n, hn⟩ := exists_nat_ge b
    ⟨n, hn⟩

@[simp]
theorem Rat.comap_coe_at_top [LinearOrderedField R] [Archimedean R] : comap (coeₓ : ℚ → R) at_top = at_top :=
  (comap_embedding_at_top fun _ _ => Rat.cast_le) $ fun r =>
    let ⟨n, hn⟩ := exists_nat_ge r
    ⟨n, by
      simpa⟩

@[simp]
theorem Rat.comap_coe_at_bot [LinearOrderedField R] [Archimedean R] : comap (coeₓ : ℚ → R) at_bot = at_bot :=
  (comap_embedding_at_bot fun _ _ => Rat.cast_le) $ fun r =>
    let ⟨n, hn⟩ := exists_nat_ge (-r)
    ⟨-n, by
      simpa [neg_le]⟩

theorem tendsto_coe_rat_at_top_iff [LinearOrderedField R] [Archimedean R] {f : α → ℚ} {l : Filter α} :
    tendsto (fun n => (f n : R)) l at_top ↔ tendsto f l at_top := by
  rw [← tendsto_comap_iff, Rat.comap_coe_at_top]

theorem tendsto_coe_rat_at_bot_iff [LinearOrderedField R] [Archimedean R] {f : α → ℚ} {l : Filter α} :
    tendsto (fun n => (f n : R)) l at_bot ↔ tendsto f l at_bot := by
  rw [← tendsto_comap_iff, Rat.comap_coe_at_bot]

theorem at_top_countable_basis_of_archimedean [LinearOrderedSemiring R] [Archimedean R] :
    (at_top : Filter R).HasCountableBasis (fun n : ℕ => True) fun n => Ici n :=
  { Countable := countable_encodable _,
    to_has_basis :=
      at_top_basis.to_has_basis
        (fun x hx =>
          let ⟨n, hn⟩ := exists_nat_ge x
          ⟨n, trivialₓ, Ici_subset_Ici.2 hn⟩)
        fun n hn => ⟨n, trivialₓ, subset.rfl⟩ }

theorem at_bot_countable_basis_of_archimedean [LinearOrderedRing R] [Archimedean R] :
    (at_bot : Filter R).HasCountableBasis (fun m : ℤ => True) fun m => Iic m :=
  { Countable := countable_encodable _,
    to_has_basis :=
      at_bot_basis.to_has_basis
        (fun x hx =>
          let ⟨m, hm⟩ := exists_int_lt x
          ⟨m, trivialₓ, Iic_subset_Iic.2 hm.le⟩)
        fun m hm => ⟨m, trivialₓ, subset.rfl⟩ }

instance (priority := 100) at_top_countably_generated_of_archimedean [LinearOrderedSemiring R] [Archimedean R] :
    (at_top : Filter R).IsCountablyGenerated :=
  at_top_countable_basis_of_archimedean.IsCountablyGenerated

instance (priority := 100) at_bot_countably_generated_of_archimedean [LinearOrderedRing R] [Archimedean R] :
    (at_bot : Filter R).IsCountablyGenerated :=
  at_bot_countable_basis_of_archimedean.IsCountablyGenerated

variable [LinearOrderedSemiring R] [Archimedean R]

variable {l : Filter α} {f : α → R} {r : R}

/--  If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the left) also tends to infinity. The archimedean assumption is convenient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in ordered fields is
given in `filter.tendsto.const_mul_at_top`). -/
theorem Filter.Tendsto.const_mul_at_top' (hr : 0 < r) (hf : tendsto f l at_top) : tendsto (fun x => r*f x) l at_top :=
  by
  apply tendsto_at_top.2 fun b => _
  obtain ⟨n : ℕ, hn : 1 ≤ n • r⟩ := Archimedean.arch 1 hr
  rw [nsmul_eq_mul'] at hn
  filter_upwards [tendsto_at_top.1 hf (n*max b 0)]
  intro x hx
  calc b ≤ 1*max b 0 := by
    rw [one_mulₓ]
    exact le_max_leftₓ _ _ _ ≤ (r*n)*max b 0 := mul_le_mul_of_nonneg_right hn (le_max_rightₓ _ _)_ = r*n*max b 0 := by
    rw [mul_assocₓ]_ ≤ r*f x := mul_le_mul_of_nonneg_left hx (le_of_ltₓ hr)

/--  If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the right) also tends to infinity. The archimedean assumption is convenient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in ordered fields is
given in `filter.tendsto.at_top_mul_const`). -/
theorem Filter.Tendsto.at_top_mul_const' (hr : 0 < r) (hf : tendsto f l at_top) : tendsto (fun x => f x*r) l at_top :=
  by
  apply tendsto_at_top.2 fun b => _
  obtain ⟨n : ℕ, hn : 1 ≤ n • r⟩ := Archimedean.arch 1 hr
  have hn' : 1 ≤ (n : R)*r := by
    rwa [nsmul_eq_mul] at hn
  filter_upwards [tendsto_at_top.1 hf (max b 0*n)]
  intro x hx
  calc b ≤ max b 0*1 := by
    rw [mul_oneₓ]
    exact le_max_leftₓ _ _ _ ≤ max b 0*n*r := mul_le_mul_of_nonneg_left hn' (le_max_rightₓ _ _)_ = (max b 0*n)*r := by
    rw [mul_assocₓ]_ ≤ f x*r := mul_le_mul_of_nonneg_right hx (le_of_ltₓ hr)

