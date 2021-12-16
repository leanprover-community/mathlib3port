import Mathbin.Topology.Algebra.Ordered.Basic 
import Mathbin.Topology.Algebra.Ordered.LeftRight

/-!
# Continuity of monotone functions

In this file we prove the following fact: if `f` is a monotone function on a neighborhood of `a`
and the image of this neighborhood is a neighborhood of `f a`, then `f` is continuous at `a`, see
`continuous_at_of_monotone_on_of_image_mem_nhds`, as well as several similar facts.

We also prove that an `order_iso` is continuous.

## Tags

continuous, monotone
-/


open Set Filter

open_locale TopologicalSpace

section LinearOrderₓ

variable {α β : Type _} [LinearOrderₓ α] [TopologicalSpace α] [OrderTopology α]

variable [LinearOrderₓ β] [TopologicalSpace β] [OrderTopology β]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr > » f a)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (c «expr ∈ » s)
/-- If `f` is a function strictly monotone on a right neighborhood of `a` and the
image of this neighborhood under `f` meets every interval `(f a, b]`, `b > f a`, then `f` is
continuous at `a` from the right.

The assumption `hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioc (f a) b` is required because otherwise the
function `f : ℝ → ℝ` given by `f x = if x ≤ 0 then x else x + 1` would be a counter-example at
`a = 0`. -/
theorem StrictMonoOn.continuous_at_right_of_exists_between {f : α → β} {s : Set α} {a : α} (h_mono : StrictMonoOn f s)
  (hs : s ∈ 𝓝[Ici a] a) (hfs : ∀ b _ : b > f a, ∃ (c : _)(_ : c ∈ s), f c ∈ Ioc (f a) b) :
  ContinuousWithinAt f (Ici a) a :=
  by 
    have ha : a ∈ Ici a := left_mem_Ici 
    have has : a ∈ s := mem_of_mem_nhds_within ha hs 
    refine' tendsto_order.2 ⟨fun b hb => _, fun b hb => _⟩
    ·
      filterUpwards [hs, self_mem_nhds_within]
      intro x hxs hxa 
      exact hb.trans_le ((h_mono.le_iff_le has hxs).2 hxa)
    ·
      rcases hfs b hb with ⟨c, hcs, hac, hcb⟩
      rw [h_mono.lt_iff_lt has hcs] at hac 
      filterUpwards [hs, Ico_mem_nhds_within_Ici (left_mem_Ico.2 hac)]
      rintro x hx ⟨hax, hxc⟩
      exact ((h_mono.lt_iff_lt hx hcs).2 hxc).trans_le hcb

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr > » f a)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (c «expr ∈ » s)
/-- If `f` is a monotone function on a right neighborhood of `a` and the image of this neighborhood
under `f` meets every interval `(f a, b)`, `b > f a`, then `f` is continuous at `a` from the right.

The assumption `hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioo (f a) b` cannot be replaced by the weaker
assumption `hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioc (f a) b` we use for strictly monotone functions
because otherwise the function `ceil : ℝ → ℤ` would be a counter-example at `a = 0`. -/
theorem continuous_at_right_of_monotone_on_of_exists_between {f : α → β} {s : Set α} {a : α} (h_mono : MonotoneOn f s)
  (hs : s ∈ 𝓝[Ici a] a) (hfs : ∀ b _ : b > f a, ∃ (c : _)(_ : c ∈ s), f c ∈ Ioo (f a) b) :
  ContinuousWithinAt f (Ici a) a :=
  by 
    have ha : a ∈ Ici a := left_mem_Ici 
    have has : a ∈ s := mem_of_mem_nhds_within ha hs 
    refine' tendsto_order.2 ⟨fun b hb => _, fun b hb => _⟩
    ·
      filterUpwards [hs, self_mem_nhds_within]
      intro x hxs hxa 
      exact hb.trans_le (h_mono has hxs hxa)
    ·
      rcases hfs b hb with ⟨c, hcs, hac, hcb⟩
      have  : a < c 
      exact not_leₓ.1 fun h => hac.not_le$ h_mono hcs has h 
      filterUpwards [hs, Ico_mem_nhds_within_Ici (left_mem_Ico.2 this)]
      rintro x hx ⟨hax, hxc⟩
      exact (h_mono hx hcs hxc.le).trans_lt hcb

/-- If a function `f` with a densely ordered codomain is monotone on a right neighborhood of `a` and
the closure of the image of this neighborhood under `f` is a right neighborhood of `f a`, then `f`
is continuous at `a` from the right. -/
theorem continuous_at_right_of_monotone_on_of_closure_image_mem_nhds_within [DenselyOrdered β] {f : α → β} {s : Set α}
  {a : α} (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝[Ici a] a) (hfs : Closure (f '' s) ∈ 𝓝[Ici (f a)] f a) :
  ContinuousWithinAt f (Ici a) a :=
  by 
    refine' continuous_at_right_of_monotone_on_of_exists_between h_mono hs fun b hb => _ 
    rcases(mem_nhds_within_Ici_iff_exists_mem_Ioc_Ico_subset hb).1 hfs with ⟨b', ⟨hab', hbb'⟩, hb'⟩
    rcases exists_between hab' with ⟨c', hc'⟩
    rcases mem_closure_iff.1 (hb' ⟨hc'.1.le, hc'.2⟩) (Ioo (f a) b') is_open_Ioo hc' with ⟨_, hc, ⟨c, hcs, rfl⟩⟩
    exact ⟨c, hcs, hc.1, hc.2.trans_le hbb'⟩

/-- If a function `f` with a densely ordered codomain is monotone on a right neighborhood of `a` and
the image of this neighborhood under `f` is a right neighborhood of `f a`, then `f` is continuous at
`a` from the right. -/
theorem continuous_at_right_of_monotone_on_of_image_mem_nhds_within [DenselyOrdered β] {f : α → β} {s : Set α} {a : α}
  (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝[Ici a] a) (hfs : f '' s ∈ 𝓝[Ici (f a)] f a) : ContinuousWithinAt f (Ici a) a :=
  continuous_at_right_of_monotone_on_of_closure_image_mem_nhds_within h_mono hs$ mem_of_superset hfs subset_closure

/-- If a function `f` with a densely ordered codomain is strictly monotone on a right neighborhood
of `a` and the closure of the image of this neighborhood under `f` is a right neighborhood of `f a`,
then `f` is continuous at `a` from the right. -/
theorem StrictMonoOn.continuous_at_right_of_closure_image_mem_nhds_within [DenselyOrdered β] {f : α → β} {s : Set α}
  {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[Ici a] a) (hfs : Closure (f '' s) ∈ 𝓝[Ici (f a)] f a) :
  ContinuousWithinAt f (Ici a) a :=
  continuous_at_right_of_monotone_on_of_closure_image_mem_nhds_within (fun x hx y hy => (h_mono.le_iff_le hx hy).2) hs
    hfs

/-- If a function `f` with a densely ordered codomain is strictly monotone on a right neighborhood
of `a` and the image of this neighborhood under `f` is a right neighborhood of `f a`, then `f` is
continuous at `a` from the right. -/
theorem StrictMonoOn.continuous_at_right_of_image_mem_nhds_within [DenselyOrdered β] {f : α → β} {s : Set α} {a : α}
  (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[Ici a] a) (hfs : f '' s ∈ 𝓝[Ici (f a)] f a) :
  ContinuousWithinAt f (Ici a) a :=
  h_mono.continuous_at_right_of_closure_image_mem_nhds_within hs (mem_of_superset hfs subset_closure)

/-- If a function `f` is strictly monotone on a right neighborhood of `a` and the image of this
neighborhood under `f` includes `Ioi (f a)`, then `f` is continuous at `a` from the right. -/
theorem StrictMonoOn.continuous_at_right_of_surj_on {f : α → β} {s : Set α} {a : α} (h_mono : StrictMonoOn f s)
  (hs : s ∈ 𝓝[Ici a] a) (hfs : surj_on f s (Ioi (f a))) : ContinuousWithinAt f (Ici a) a :=
  h_mono.continuous_at_right_of_exists_between hs$
    fun b hb =>
      let ⟨c, hcs, hcb⟩ := hfs hb
      ⟨c, hcs, hcb.symm ▸ hb, hcb.le⟩

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr < » f a)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (c «expr ∈ » s)
/-- If `f` is a strictly monotone function on a left neighborhood of `a` and the image of this
neighborhood under `f` meets every interval `[b, f a)`, `b < f a`, then `f` is continuous at `a`
from the left.

The assumption `hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ico b (f a)` is required because otherwise the
function `f : ℝ → ℝ` given by `f x = if x < 0 then x else x + 1` would be a counter-example at
`a = 0`. -/
theorem StrictMonoOn.continuous_at_left_of_exists_between {f : α → β} {s : Set α} {a : α} (h_mono : StrictMonoOn f s)
  (hs : s ∈ 𝓝[Iic a] a) (hfs : ∀ b _ : b < f a, ∃ (c : _)(_ : c ∈ s), f c ∈ Ico b (f a)) :
  ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuous_at_right_of_exists_between hs$
    fun b hb =>
      let ⟨c, hcs, hcb, hca⟩ := hfs b hb
      ⟨c, hcs, hca, hcb⟩

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr < » f a)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (c «expr ∈ » s)
/-- If `f` is a monotone function on a left neighborhood of `a` and the image of this neighborhood
under `f` meets every interval `(b, f a)`, `b < f a`, then `f` is continuous at `a` from the left.

The assumption `hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ioo b (f a)` cannot be replaced by the weaker
assumption `hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ico b (f a)` we use for strictly monotone functions
because otherwise the function `floor : ℝ → ℤ` would be a counter-example at `a = 0`. -/
theorem continuous_at_left_of_monotone_on_of_exists_between {f : α → β} {s : Set α} {a : α} (hf : MonotoneOn f s)
  (hs : s ∈ 𝓝[Iic a] a) (hfs : ∀ b _ : b < f a, ∃ (c : _)(_ : c ∈ s), f c ∈ Ioo b (f a)) :
  ContinuousWithinAt f (Iic a) a :=
  @continuous_at_right_of_monotone_on_of_exists_between (OrderDual α) (OrderDual β) _ _ _ _ _ _ f s a hf.dual hs$
    fun b hb =>
      let ⟨c, hcs, hcb, hca⟩ := hfs b hb
      ⟨c, hcs, hca, hcb⟩

/-- If a function `f` with a densely ordered codomain is monotone on a left neighborhood of `a` and
the closure of the image of this neighborhood under `f` is a left neighborhood of `f a`, then `f` is
continuous at `a` from the left -/
theorem continuous_at_left_of_monotone_on_of_closure_image_mem_nhds_within [DenselyOrdered β] {f : α → β} {s : Set α}
  {a : α} (hf : MonotoneOn f s) (hs : s ∈ 𝓝[Iic a] a) (hfs : Closure (f '' s) ∈ 𝓝[Iic (f a)] f a) :
  ContinuousWithinAt f (Iic a) a :=
  @continuous_at_right_of_monotone_on_of_closure_image_mem_nhds_within (OrderDual α) (OrderDual β) _ _ _ _ _ _ _ f s a
    hf.dual hs hfs

/-- If a function `f` with a densely ordered codomain is monotone on a left neighborhood of `a` and
the image of this neighborhood under `f` is a left neighborhood of `f a`, then `f` is continuous at
`a` from the left. -/
theorem continuous_at_left_of_monotone_on_of_image_mem_nhds_within [DenselyOrdered β] {f : α → β} {s : Set α} {a : α}
  (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝[Iic a] a) (hfs : f '' s ∈ 𝓝[Iic (f a)] f a) : ContinuousWithinAt f (Iic a) a :=
  continuous_at_left_of_monotone_on_of_closure_image_mem_nhds_within h_mono hs (mem_of_superset hfs subset_closure)

/-- If a function `f` with a densely ordered codomain is strictly monotone on a left neighborhood of
`a` and the closure of the image of this neighborhood under `f` is a left neighborhood of `f a`,
then `f` is continuous at `a` from the left. -/
theorem StrictMonoOn.continuous_at_left_of_closure_image_mem_nhds_within [DenselyOrdered β] {f : α → β} {s : Set α}
  {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[Iic a] a) (hfs : Closure (f '' s) ∈ 𝓝[Iic (f a)] f a) :
  ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuous_at_right_of_closure_image_mem_nhds_within hs hfs

/-- If a function `f` with a densely ordered codomain is strictly monotone on a left neighborhood of
`a` and the image of this neighborhood under `f` is a left neighborhood of `f a`, then `f` is
continuous at `a` from the left. -/
theorem StrictMonoOn.continuous_at_left_of_image_mem_nhds_within [DenselyOrdered β] {f : α → β} {s : Set α} {a : α}
  (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[Iic a] a) (hfs : f '' s ∈ 𝓝[Iic (f a)] f a) :
  ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuous_at_right_of_image_mem_nhds_within hs hfs

/-- If a function `f` is strictly monotone on a left neighborhood of `a` and the image of this
neighborhood under `f` includes `Iio (f a)`, then `f` is continuous at `a` from the left. -/
theorem StrictMonoOn.continuous_at_left_of_surj_on {f : α → β} {s : Set α} {a : α} (h_mono : StrictMonoOn f s)
  (hs : s ∈ 𝓝[Iic a] a) (hfs : surj_on f s (Iio (f a))) : ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuous_at_right_of_surj_on hs hfs

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr < » f a)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (c «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr > » f a)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (c «expr ∈ » s)
/-- If a function `f` is strictly monotone on a neighborhood of `a` and the image of this
neighborhood under `f` meets every interval `[b, f a)`, `b < f a`, and every interval
`(f a, b]`, `b > f a`, then `f` is continuous at `a`. -/
theorem StrictMonoOn.continuous_at_of_exists_between {f : α → β} {s : Set α} {a : α} (h_mono : StrictMonoOn f s)
  (hs : s ∈ 𝓝 a) (hfs_l : ∀ b _ : b < f a, ∃ (c : _)(_ : c ∈ s), f c ∈ Ico b (f a))
  (hfs_r : ∀ b _ : b > f a, ∃ (c : _)(_ : c ∈ s), f c ∈ Ioc (f a) b) : ContinuousAt f a :=
  continuous_at_iff_continuous_left_right.2
    ⟨h_mono.continuous_at_left_of_exists_between (mem_nhds_within_of_mem_nhds hs) hfs_l,
      h_mono.continuous_at_right_of_exists_between (mem_nhds_within_of_mem_nhds hs) hfs_r⟩

/-- If a function `f` with a densely ordered codomain is strictly monotone on a neighborhood of `a`
and the closure of the image of this neighborhood under `f` is a neighborhood of `f a`, then `f` is
continuous at `a`. -/
theorem StrictMonoOn.continuous_at_of_closure_image_mem_nhds [DenselyOrdered β] {f : α → β} {s : Set α} {a : α}
  (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝 a) (hfs : Closure (f '' s) ∈ 𝓝 (f a)) : ContinuousAt f a :=
  continuous_at_iff_continuous_left_right.2
    ⟨h_mono.continuous_at_left_of_closure_image_mem_nhds_within (mem_nhds_within_of_mem_nhds hs)
        (mem_nhds_within_of_mem_nhds hfs),
      h_mono.continuous_at_right_of_closure_image_mem_nhds_within (mem_nhds_within_of_mem_nhds hs)
        (mem_nhds_within_of_mem_nhds hfs)⟩

/-- If a function `f` with a densely ordered codomain is strictly monotone on a neighborhood of `a`
and the image of this set under `f` is a neighborhood of `f a`, then `f` is continuous at `a`. -/
theorem StrictMonoOn.continuous_at_of_image_mem_nhds [DenselyOrdered β] {f : α → β} {s : Set α} {a : α}
  (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝 a) (hfs : f '' s ∈ 𝓝 (f a)) : ContinuousAt f a :=
  h_mono.continuous_at_of_closure_image_mem_nhds hs (mem_of_superset hfs subset_closure)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr < » f a)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (c «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr > » f a)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (c «expr ∈ » s)
/-- If `f` is a monotone function on a neighborhood of `a` and the image of this neighborhood under
`f` meets every interval `(b, f a)`, `b < f a`, and every interval `(f a, b)`, `b > f a`, then `f`
is continuous at `a`. -/
theorem continuous_at_of_monotone_on_of_exists_between {f : α → β} {s : Set α} {a : α} (h_mono : MonotoneOn f s)
  (hs : s ∈ 𝓝 a) (hfs_l : ∀ b _ : b < f a, ∃ (c : _)(_ : c ∈ s), f c ∈ Ioo b (f a))
  (hfs_r : ∀ b _ : b > f a, ∃ (c : _)(_ : c ∈ s), f c ∈ Ioo (f a) b) : ContinuousAt f a :=
  continuous_at_iff_continuous_left_right.2
    ⟨continuous_at_left_of_monotone_on_of_exists_between h_mono (mem_nhds_within_of_mem_nhds hs) hfs_l,
      continuous_at_right_of_monotone_on_of_exists_between h_mono (mem_nhds_within_of_mem_nhds hs) hfs_r⟩

/-- If a function `f` with a densely ordered codomain is monotone on a neighborhood of `a` and the
closure of the image of this neighborhood under `f` is a neighborhood of `f a`, then `f` is
continuous at `a`. -/
theorem continuous_at_of_monotone_on_of_closure_image_mem_nhds [DenselyOrdered β] {f : α → β} {s : Set α} {a : α}
  (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝 a) (hfs : Closure (f '' s) ∈ 𝓝 (f a)) : ContinuousAt f a :=
  continuous_at_iff_continuous_left_right.2
    ⟨continuous_at_left_of_monotone_on_of_closure_image_mem_nhds_within h_mono (mem_nhds_within_of_mem_nhds hs)
        (mem_nhds_within_of_mem_nhds hfs),
      continuous_at_right_of_monotone_on_of_closure_image_mem_nhds_within h_mono (mem_nhds_within_of_mem_nhds hs)
        (mem_nhds_within_of_mem_nhds hfs)⟩

/-- If a function `f` with a densely ordered codomain is monotone on a neighborhood of `a` and the
image of this neighborhood under `f` is a neighborhood of `f a`, then `f` is continuous at `a`. -/
theorem continuous_at_of_monotone_on_of_image_mem_nhds [DenselyOrdered β] {f : α → β} {s : Set α} {a : α}
  (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝 a) (hfs : f '' s ∈ 𝓝 (f a)) : ContinuousAt f a :=
  continuous_at_of_monotone_on_of_closure_image_mem_nhds h_mono hs (mem_of_superset hfs subset_closure)

/-- A monotone function with densely ordered codomain and a dense range is continuous. -/
theorem Monotone.continuous_of_dense_range [DenselyOrdered β] {f : α → β} (h_mono : Monotone f)
  (h_dense : DenseRange f) : Continuous f :=
  continuous_iff_continuous_at.mpr$
    fun a =>
      continuous_at_of_monotone_on_of_closure_image_mem_nhds (fun x hx y hy hxy => h_mono hxy) univ_mem$
        by 
          simp only [image_univ, h_dense.closure_eq, univ_mem]

/-- A monotone surjective function with a densely ordered codomain is continuous. -/
theorem Monotone.continuous_of_surjective [DenselyOrdered β] {f : α → β} (h_mono : Monotone f)
  (h_surj : Function.Surjective f) : Continuous f :=
  h_mono.continuous_of_dense_range h_surj.dense_range

end LinearOrderₓ

/-!
### Continuity of order isomorphisms

In this section we prove that an `order_iso` is continuous, hence it is a `homeomorph`. We prove
this for an `order_iso` between to partial orders with order topology.
-/


namespace OrderIso

variable {α β : Type _} [PartialOrderₓ α] [PartialOrderₓ β] [TopologicalSpace α] [TopologicalSpace β] [OrderTopology α]
  [OrderTopology β]

protected theorem Continuous (e : α ≃o β) : Continuous e :=
  by 
    rw [‹OrderTopology β›.topology_eq_generate_intervals]
    refine' continuous_generated_from fun s hs => _ 
    rcases hs with ⟨a, rfl | rfl⟩
    ·
      rw [e.preimage_Ioi]
      apply is_open_lt'
    ·
      rw [e.preimage_Iio]
      apply is_open_gt'

/-- An order isomorphism between two linear order `order_topology` spaces is a homeomorphism. -/
def to_homeomorph (e : α ≃o β) : α ≃ₜ β :=
  { e with continuous_to_fun := e.continuous, continuous_inv_fun := e.symm.continuous }

@[simp]
theorem coe_to_homeomorph (e : α ≃o β) : ⇑e.to_homeomorph = e :=
  rfl

@[simp]
theorem coe_to_homeomorph_symm (e : α ≃o β) : ⇑e.to_homeomorph.symm = e.symm :=
  rfl

end OrderIso

