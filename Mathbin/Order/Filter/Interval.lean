import Mathbin.Data.Set.Intervals.OrdConnected 
import Mathbin.Order.Filter.Lift 
import Mathbin.Order.Filter.AtTopBot

/-!
# Convergence of intervals

If both `a` and `b` tend to some filter `l₁`, sometimes this implies that `Ixx a b` tends to
`l₂.lift' powerset`, i.e., for any `s ∈ l₂` eventually `Ixx a b` becomes a subset of `s`.  Here and
below `Ixx` is one of `Icc`, `Ico`, `Ioc`, and `Ioo`. We define `filter.tendsto_Ixx_class Ixx l₁ l₂`
to be a typeclass representing this property.

The instances provide the best `l₂` for a given `l₁`. In many cases `l₁ = l₂` but sometimes we can
drop an endpoint from an interval: e.g., we prove `tendsto_Ixx_class Ico (𝓟 $ Iic a) (𝓟 $ Iio a)`,
i.e., if `u₁ n` and `u₂ n` belong eventually to `Iic a`, then the interval `Ico (u₁ n) (u₂ n)` is
eventually included in `Iio a`.

The next table shows “output” filters `l₂` for different values of `Ixx` and `l₁`. The instances
that need topology are defined in `topology/algebra/ordered`.

| Input filter |  `Ixx = Icc`  |  `Ixx = Ico`  |  `Ixx = Ioc`  |  `Ixx = Ioo`  |
| -----------: | :-----------: | :-----------: | :-----------: | :-----------: |
|     `at_top` |    `at_top`   |    `at_top`   |    `at_top`   |    `at_top`   |
|     `at_bot` |    `at_bot`   |    `at_bot`   |    `at_bot`   |    `at_bot`   |
|     `pure a` |    `pure a`   |      `⊥`      |      `⊥`      |      `⊥`      |
|  `𝓟 (Iic a)` |  `𝓟 (Iic a)`  |  `𝓟 (Iio a)`  |  `𝓟 (Iic a)`  |  `𝓟 (Iio a)`  |
|  `𝓟 (Ici a)` |  `𝓟 (Ici a)`  |  `𝓟 (Ici a)`  |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |
|  `𝓟 (Ioi a)` |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |
|  `𝓟 (Iio a)` |  `𝓟 (Iio a)`  |  `𝓟 (Iio a)`  |  `𝓟 (Iio a)`  |  `𝓟 (Iio a)`  |
|        `𝓝 a` |     `𝓝 a`     |     `𝓝 a`     |     `𝓝 a`     |     `𝓝 a`     |
| `𝓝[Iic a] b` |  `𝓝[Iic a] b` |  `𝓝[Iio a] b` |  `𝓝[Iic a] b` |  `𝓝[Iio a] b` |
| `𝓝[Ici a] b` |  `𝓝[Ici a] b` |  `𝓝[Ici a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |
| `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |
| `𝓝[Iio a] b` |  `𝓝[Iio a] b` |  `𝓝[Iio a] b` |  `𝓝[Iio a] b` |  `𝓝[Iio a] b` |

-/


variable {α β : Type _}

open_locale Classical Filter Interval

open Set Function

namespace Filter

section Preorderₓ

variable [Preorderₓ α]

/-- A pair of filters `l₁`, `l₂` has `tendsto_Ixx_class Ixx` property if `Ixx a b` tends to
`l₂.lift' powerset` as `a` and `b` tend to `l₁`. In all instances `Ixx` is one of `Icc`, `Ico`,
`Ioc`, or `Ioo`. The instances provide the best `l₂` for a given `l₁`. In many cases `l₁ = l₂` but
sometimes we can drop an endpoint from an interval: e.g., we prove `tendsto_Ixx_class Ico (𝓟 $ Iic
a) (𝓟 $ Iio a)`, i.e., if `u₁ n` and `u₂ n` belong eventually to `Iic a`, then the interval `Ico (u₁
n) (u₂ n)` is eventually included in `Iio a`.

We mark `l₂` as an `out_param` so that Lean can automatically find an appropriate `l₂` based on
`Ixx` and `l₁`. This way, e.g., `tendsto.Ico h₁ h₂` works without specifying explicitly `l₂`. -/
class tendsto_Ixx_class (Ixx : α → α → Set α) (l₁ : Filter α) (l₂ : outParam$ Filter α) : Prop where 
  tendsto_Ixx : tendsto (fun p : α × α => Ixx p.1 p.2) (l₁ ×ᶠ l₁) (l₂.lift' powerset)

theorem tendsto.Icc {l₁ l₂ : Filter α} [tendsto_Ixx_class Icc l₁ l₂] {lb : Filter β} {u₁ u₂ : β → α}
  (h₁ : tendsto u₁ lb l₁) (h₂ : tendsto u₂ lb l₁) : tendsto (fun x => Icc (u₁ x) (u₂ x)) lb (l₂.lift' powerset) :=
  tendsto_Ixx_class.tendsto_Ixx.comp$ h₁.prod_mk h₂

theorem tendsto.Ioc {l₁ l₂ : Filter α} [tendsto_Ixx_class Ioc l₁ l₂] {lb : Filter β} {u₁ u₂ : β → α}
  (h₁ : tendsto u₁ lb l₁) (h₂ : tendsto u₂ lb l₁) : tendsto (fun x => Ioc (u₁ x) (u₂ x)) lb (l₂.lift' powerset) :=
  tendsto_Ixx_class.tendsto_Ixx.comp$ h₁.prod_mk h₂

theorem tendsto.Ico {l₁ l₂ : Filter α} [tendsto_Ixx_class Ico l₁ l₂] {lb : Filter β} {u₁ u₂ : β → α}
  (h₁ : tendsto u₁ lb l₁) (h₂ : tendsto u₂ lb l₁) : tendsto (fun x => Ico (u₁ x) (u₂ x)) lb (l₂.lift' powerset) :=
  tendsto_Ixx_class.tendsto_Ixx.comp$ h₁.prod_mk h₂

theorem tendsto.Ioo {l₁ l₂ : Filter α} [tendsto_Ixx_class Ioo l₁ l₂] {lb : Filter β} {u₁ u₂ : β → α}
  (h₁ : tendsto u₁ lb l₁) (h₂ : tendsto u₂ lb l₁) : tendsto (fun x => Ioo (u₁ x) (u₂ x)) lb (l₂.lift' powerset) :=
  tendsto_Ixx_class.tendsto_Ixx.comp$ h₁.prod_mk h₂

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » s)
theorem tendsto_Ixx_class_principal {s t : Set α} {Ixx : α → α → Set α} :
  tendsto_Ixx_class Ixx (𝓟 s) (𝓟 t) ↔ ∀ x _ : x ∈ s y _ : y ∈ s, Ixx x y ⊆ t :=
  by 
    refine' Iff.trans ⟨fun h => h.1, fun h => ⟨h⟩⟩ _ 
    simp [lift'_principal monotone_powerset, -mem_prod, -Prod.forall, forall_prod_set]

theorem tendsto_Ixx_class_inf {l₁ l₁' l₂ l₂' : Filter α} {Ixx} [h : tendsto_Ixx_class Ixx l₁ l₂]
  [h' : tendsto_Ixx_class Ixx l₁' l₂'] : tendsto_Ixx_class Ixx (l₁⊓l₁') (l₂⊓l₂') :=
  ⟨by 
      simpa only [prod_inf_prod, lift'_inf_powerset] using h.1.inf h'.1⟩

theorem tendsto_Ixx_class_of_subset {l₁ l₂ : Filter α} {Ixx Ixx' : α → α → Set α} (h : ∀ a b, Ixx a b ⊆ Ixx' a b)
  [h' : tendsto_Ixx_class Ixx' l₁ l₂] : tendsto_Ixx_class Ixx l₁ l₂ :=
  ⟨tendsto_lift'_powerset_mono h'.1$ eventually_of_forall$ Prod.forall.2 h⟩

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s i)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » s i)
theorem has_basis.tendsto_Ixx_class {ι : Type _} {p : ι → Prop} {s} {l : Filter α} (hl : l.has_basis p s)
  {Ixx : α → α → Set α} (H : ∀ i, p i → ∀ x _ : x ∈ s i y _ : y ∈ s i, Ixx x y ⊆ s i) : tendsto_Ixx_class Ixx l l :=
  ⟨(hl.prod_self.tendsto_iff (hl.lift' monotone_powerset)).2$ fun i hi => ⟨i, hi, fun x hx => H i hi _ hx.1 _ hx.2⟩⟩

instance tendsto_Icc_at_top_at_top : tendsto_Ixx_class Icc (at_top : Filter α) at_top :=
  (has_basis_infi_principal_finite _).TendstoIxxClass$
    fun s hs => Set.OrdConnected.out$ ord_connected_bInter$ fun i hi => ord_connected_Ici

instance tendsto_Ico_at_top_at_top : tendsto_Ixx_class Ico (at_top : Filter α) at_top :=
  tendsto_Ixx_class_of_subset fun _ _ => Ico_subset_Icc_self

instance tendsto_Ioc_at_top_at_top : tendsto_Ixx_class Ioc (at_top : Filter α) at_top :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioc_subset_Icc_self

instance tendsto_Ioo_at_top_at_top : tendsto_Ixx_class Ioo (at_top : Filter α) at_top :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioo_subset_Icc_self

instance tendsto_Icc_at_bot_at_bot : tendsto_Ixx_class Icc (at_bot : Filter α) at_bot :=
  (has_basis_infi_principal_finite _).TendstoIxxClass$
    fun s hs => Set.OrdConnected.out$ ord_connected_bInter$ fun i hi => ord_connected_Iic

instance tendsto_Ico_at_bot_at_bot : tendsto_Ixx_class Ico (at_bot : Filter α) at_bot :=
  tendsto_Ixx_class_of_subset fun _ _ => Ico_subset_Icc_self

instance tendsto_Ioc_at_bot_at_bot : tendsto_Ixx_class Ioc (at_bot : Filter α) at_bot :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioc_subset_Icc_self

instance tendsto_Ioo_at_bot_at_bot : tendsto_Ixx_class Ioo (at_bot : Filter α) at_bot :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioo_subset_Icc_self

instance ord_connected.tendsto_Icc {s : Set α} [hs : ord_connected s] : tendsto_Ixx_class Icc (𝓟 s) (𝓟 s) :=
  tendsto_Ixx_class_principal.2 hs.out

instance tendsto_Ico_Ici_Ici {a : α} : tendsto_Ixx_class Ico (𝓟 (Ici a)) (𝓟 (Ici a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ico_subset_Icc_self

instance tendsto_Ico_Ioi_Ioi {a : α} : tendsto_Ixx_class Ico (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ico_subset_Icc_self

instance tendsto_Ico_Iic_Iio {a : α} : tendsto_Ixx_class Ico (𝓟 (Iic a)) (𝓟 (Iio a)) :=
  tendsto_Ixx_class_principal.2$ fun a ha b hb x hx => lt_of_lt_of_leₓ hx.2 hb

instance tendsto_Ico_Iio_Iio {a : α} : tendsto_Ixx_class Ico (𝓟 (Iio a)) (𝓟 (Iio a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ico_subset_Icc_self

instance tendsto_Ioc_Ici_Ioi {a : α} : tendsto_Ixx_class Ioc (𝓟 (Ici a)) (𝓟 (Ioi a)) :=
  tendsto_Ixx_class_principal.2$ fun x hx y hy t ht => lt_of_le_of_ltₓ hx ht.1

instance tendsto_Ioc_Iic_Iic {a : α} : tendsto_Ixx_class Ioc (𝓟 (Iic a)) (𝓟 (Iic a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioc_subset_Icc_self

instance tendsto_Ioc_Iio_Iio {a : α} : tendsto_Ixx_class Ioc (𝓟 (Iio a)) (𝓟 (Iio a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioc_subset_Icc_self

instance tendsto_Ioc_Ioi_Ioi {a : α} : tendsto_Ixx_class Ioc (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioc_subset_Icc_self

instance tendsto_Ioo_Ici_Ioi {a : α} : tendsto_Ixx_class Ioo (𝓟 (Ici a)) (𝓟 (Ioi a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioo_subset_Ioc_self

instance tendsto_Ioo_Iic_Iio {a : α} : tendsto_Ixx_class Ioo (𝓟 (Iic a)) (𝓟 (Iio a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioo_subset_Ico_self

instance tendsto_Ioo_Ioi_Ioi {a : α} : tendsto_Ixx_class Ioo (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioo_subset_Ioc_self

instance tendsto_Ioo_Iio_Iio {a : α} : tendsto_Ixx_class Ioo (𝓟 (Iio a)) (𝓟 (Iio a)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioo_subset_Ioc_self

instance tendsto_Icc_Icc_icc {a b : α} : tendsto_Ixx_class Icc (𝓟 (Icc a b)) (𝓟 (Icc a b)) :=
  tendsto_Ixx_class_principal.mpr$ fun x hx y hy => Icc_subset_Icc hx.1 hy.2

instance tendsto_Ioc_Icc_Icc {a b : α} : tendsto_Ixx_class Ioc (𝓟 (Icc a b)) (𝓟 (Icc a b)) :=
  tendsto_Ixx_class_of_subset$ fun _ _ => Ioc_subset_Icc_self

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α]

instance tendsto_Icc_pure_pure {a : α} : tendsto_Ixx_class Icc (pure a) (pure a : Filter α) :=
  by 
    rw [←principal_singleton]
    exact tendsto_Ixx_class_principal.2 ord_connected_singleton.out

instance tendsto_Ico_pure_bot {a : α} : tendsto_Ixx_class Ico (pure a) ⊥ :=
  ⟨by 
      simp [lift'_bot monotone_powerset]⟩

instance tendsto_Ioc_pure_bot {a : α} : tendsto_Ixx_class Ioc (pure a) ⊥ :=
  ⟨by 
      simp [lift'_bot monotone_powerset]⟩

instance tendsto_Ioo_pure_bot {a : α} : tendsto_Ixx_class Ioo (pure a) ⊥ :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioo_subset_Ioc_self

end PartialOrderₓ

section LinearOrderₓ

variable [LinearOrderₓ α]

-- ././Mathport/Syntax/Translate/Basic.lean:589:47: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:589:47: unsupported (impossible)
instance tendsto_Icc_interval_interval {a b : α} :
  tendsto_Ixx_class Icc (𝓟 "././Mathport/Syntax/Translate/Basic.lean:589:47: unsupported (impossible)")
    (𝓟 "././Mathport/Syntax/Translate/Basic.lean:589:47: unsupported (impossible)") :=
  Filter.tendsto_Icc_Icc_icc

-- ././Mathport/Syntax/Translate/Basic.lean:589:47: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:589:47: unsupported (impossible)
instance tendsto_Ioc_interval_interval {a b : α} :
  tendsto_Ixx_class Ioc (𝓟 "././Mathport/Syntax/Translate/Basic.lean:589:47: unsupported (impossible)")
    (𝓟 "././Mathport/Syntax/Translate/Basic.lean:589:47: unsupported (impossible)") :=
  tendsto_Ixx_class_of_subset$ fun _ _ => Ioc_subset_Icc_self

end LinearOrderₓ

end Filter

