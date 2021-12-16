import Mathbin.Data.Set.Intervals.UnorderedInterval 
import Mathbin.Data.Set.Lattice

/-!
# Order-connected sets

We say that a set `s : set α` is `ord_connected` if for all `x y ∈ s` it includes the
interval `[x, y]`. If `α` is a `densely_ordered` `conditionally_complete_linear_order` with
the `order_topology`, then this condition is equivalent to `is_preconnected s`. If `α` is a
`linear_ordered_field`, then this condition is also equivalent to `convex α s`.

In this file we prove that intersection of a family of `ord_connected` sets is `ord_connected` and
that all standard intervals are `ord_connected`.
-/


namespace Set

section Preorderₓ

variable {α : Type _} [Preorderₓ α] {s t : Set α}

/--
We say that a set `s : set α` is `ord_connected` if for all `x y ∈ s` it includes the
interval `[x, y]`. If `α` is a `densely_ordered` `conditionally_complete_linear_order` with
the `order_topology`, then this condition is equivalent to `is_preconnected s`. If `α` is a
`linear_ordered_field`, then this condition is also equivalent to `convex α s`.
-/
class ord_connected (s : Set α) : Prop where 
  out' ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) : Icc x y ⊆ s

theorem ord_connected.out (h : ord_connected s) : ∀ ⦃x⦄ hx : x ∈ s ⦃y⦄ hy : y ∈ s, Icc x y ⊆ s :=
  h.1

theorem ord_connected_def : ord_connected s ↔ ∀ ⦃x⦄ hx : x ∈ s ⦃y⦄ hy : y ∈ s, Icc x y ⊆ s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » s)
/-- It suffices to prove `[x, y] ⊆ s` for `x y ∈ s`, `x ≤ y`. -/
theorem ord_connected_iff : ord_connected s ↔ ∀ x _ : x ∈ s y _ : y ∈ s, x ≤ y → Icc x y ⊆ s :=
  ord_connected_def.trans
    ⟨fun hs x hx y hy hxy => hs hx hy, fun H x hx y hy z hz => H x hx y hy (le_transₓ hz.1 hz.2) hz⟩

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » s)
theorem ord_connected_of_Ioo {α : Type _} [PartialOrderₓ α] {s : Set α}
  (hs : ∀ x _ : x ∈ s y _ : y ∈ s, x < y → Ioo x y ⊆ s) : ord_connected s :=
  by 
    rw [ord_connected_iff]
    intro x hx y hy hxy 
    rcases eq_or_lt_of_le hxy with (rfl | hxy')
    ·
      simpa 
    have  := hs x hx y hy hxy' 
    rw [←union_diff_cancel Ioo_subset_Icc_self]
    simp [insert_subset]

protected theorem Icc_subset (s : Set α) [hs : ord_connected s] {x y} (hx : x ∈ s) (hy : y ∈ s) : Icc x y ⊆ s :=
  hs.out hx hy

theorem ord_connected.inter {s t : Set α} (hs : ord_connected s) (ht : ord_connected t) : ord_connected (s ∩ t) :=
  ⟨fun x hx y hy => subset_inter (hs.out hx.1 hy.1) (ht.out hx.2 hy.2)⟩

instance ord_connected.inter' {s t : Set α} [ord_connected s] [ord_connected t] : ord_connected (s ∩ t) :=
  ord_connected.inter ‹_› ‹_›

theorem ord_connected.dual {s : Set α} (hs : ord_connected s) : ord_connected (OrderDual.ofDual ⁻¹' s) :=
  ⟨fun x hx y hy z hz => hs.out hy hx ⟨hz.2, hz.1⟩⟩

theorem ord_connected_dual {s : Set α} : ord_connected (OrderDual.ofDual ⁻¹' s) ↔ ord_connected s :=
  ⟨fun h =>
      by 
        simpa only [ord_connected_def] using h.dual,
    fun h => h.dual⟩

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (s «expr ∈ » S)
theorem ord_connected_sInter {S : Set (Set α)} (hS : ∀ s _ : s ∈ S, ord_connected s) : ord_connected (⋂₀S) :=
  ⟨fun x hx y hy => subset_sInter$ fun s hs => (hS s hs).out (hx s hs) (hy s hs)⟩

theorem ord_connected_Inter {ι : Sort _} {s : ι → Set α} (hs : ∀ i, ord_connected (s i)) : ord_connected (⋂ i, s i) :=
  ord_connected_sInter$ forall_range_iff.2 hs

instance ord_connected_Inter' {ι : Sort _} {s : ι → Set α} [∀ i, ord_connected (s i)] : ord_connected (⋂ i, s i) :=
  ord_connected_Inter ‹_›

theorem ord_connected_bInter {ι : Sort _} {p : ι → Prop} {s : ∀ i : ι hi : p i, Set α}
  (hs : ∀ i hi, ord_connected (s i hi)) : ord_connected (⋂ i hi, s i hi) :=
  ord_connected_Inter$ fun i => ord_connected_Inter$ hs i

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (i «expr ∈ » s)
theorem ord_connected_pi {ι : Type _} {α : ι → Type _} [∀ i, Preorderₓ (α i)] {s : Set ι} {t : ∀ i, Set (α i)}
  (h : ∀ i _ : i ∈ s, ord_connected (t i)) : ord_connected (s.pi t) :=
  ⟨fun x hx y hy z hz i hi => (h i hi).out (hx i hi) (hy i hi) ⟨hz.1 i, hz.2 i⟩⟩

instance ord_connected_pi' {ι : Type _} {α : ι → Type _} [∀ i, Preorderₓ (α i)] {s : Set ι} {t : ∀ i, Set (α i)}
  [h : ∀ i, ord_connected (t i)] : ord_connected (s.pi t) :=
  ord_connected_pi$ fun i hi => h i

@[instance]
theorem ord_connected_Ici {a : α} : ord_connected (Ici a) :=
  ⟨fun x hx y hy z hz => le_transₓ hx hz.1⟩

@[instance]
theorem ord_connected_Iic {a : α} : ord_connected (Iic a) :=
  ⟨fun x hx y hy z hz => le_transₓ hz.2 hy⟩

@[instance]
theorem ord_connected_Ioi {a : α} : ord_connected (Ioi a) :=
  ⟨fun x hx y hy z hz => lt_of_lt_of_leₓ hx hz.1⟩

@[instance]
theorem ord_connected_Iio {a : α} : ord_connected (Iio a) :=
  ⟨fun x hx y hy z hz => lt_of_le_of_ltₓ hz.2 hy⟩

@[instance]
theorem ord_connected_Icc {a b : α} : ord_connected (Icc a b) :=
  ord_connected_Ici.inter ord_connected_Iic

@[instance]
theorem ord_connected_Ico {a b : α} : ord_connected (Ico a b) :=
  ord_connected_Ici.inter ord_connected_Iio

@[instance]
theorem ord_connected_Ioc {a b : α} : ord_connected (Ioc a b) :=
  ord_connected_Ioi.inter ord_connected_Iic

@[instance]
theorem ord_connected_Ioo {a b : α} : ord_connected (Ioo a b) :=
  ord_connected_Ioi.inter ord_connected_Iio

@[instance]
theorem ord_connected_singleton {α : Type _} [PartialOrderₓ α] {a : α} : ord_connected ({a} : Set α) :=
  by 
    rw [←Icc_self]
    exact ord_connected_Icc

@[instance]
theorem ord_connected_empty : ord_connected (∅ : Set α) :=
  ⟨fun x => False.elim⟩

@[instance]
theorem ord_connected_univ : ord_connected (univ : Set α) :=
  ⟨fun _ _ _ _ => subset_univ _⟩

/-- In a dense order `α`, the subtype from an `ord_connected` set is also densely ordered. -/
instance [DenselyOrdered α] {s : Set α} [hs : ord_connected s] : DenselyOrdered s :=
  ⟨by 
      intro a₁ a₂ ha 
      have ha' : ↑a₁ < ↑a₂ := ha 
      obtain ⟨x, ha₁x, hxa₂⟩ := exists_between ha' 
      refine' ⟨⟨x, _⟩, ⟨ha₁x, hxa₂⟩⟩
      exact (hs.out a₁.2 a₂.2) (Ioo_subset_Icc_self ⟨ha₁x, hxa₂⟩)⟩

end Preorderₓ

section LinearOrderₓ

variable {α : Type _} [LinearOrderₓ α] {s : Set α} {x : α}

@[instance]
theorem ord_connected_interval {a b : α} : ord_connected (interval a b) :=
  ord_connected_Icc

theorem ord_connected.interval_subset (hs : ord_connected s) ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) : interval x y ⊆ s :=
  by 
    cases le_totalₓ x y <;> simp only [interval_of_le, interval_of_ge] <;> apply hs.out <;> assumption

theorem ord_connected_iff_interval_subset : ord_connected s ↔ ∀ ⦃x⦄ hx : x ∈ s ⦃y⦄ hy : y ∈ s, interval x y ⊆ s :=
  ⟨fun h => h.interval_subset,
    fun h =>
      ord_connected_iff.2$
        fun x hx y hy hxy =>
          by 
            simpa only [interval_of_le hxy] using h hx hy⟩

theorem ord_connected_iff_interval_subset_left (hx : x ∈ s) : ord_connected s ↔ ∀ ⦃y⦄, y ∈ s → interval x y ⊆ s :=
  by 
    refine' ⟨fun hs => hs.interval_subset hx, fun hs => ord_connected_iff_interval_subset.2$ fun y hy z hz => _⟩
    suffices h : interval y x ∪ interval x z ⊆ s
    ·
      exact interval_subset_interval_union_interval.trans h 
    rw [interval_swap, union_subset_iff]
    exact ⟨hs hy, hs hz⟩

theorem ord_connected_iff_interval_subset_right (hx : x ∈ s) : ord_connected s ↔ ∀ ⦃y⦄, y ∈ s → interval y x ⊆ s :=
  by 
    simpRw [ord_connected_iff_interval_subset_left hx, interval_swap]

end LinearOrderₓ

end Set

