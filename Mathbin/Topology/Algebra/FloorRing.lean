import Mathbin.Algebra.Order.Floor 
import Mathbin.Topology.Algebra.Ordered.Basic

/-!
# Topological facts about `int.floor`, `int.ceil` and `int.fract`

This file proves statements about limits and continuity of functions involving `floor`, `ceil` and
`fract`.

## Main declarations

* `tendsto_floor_at_top`, `tendsto_floor_at_bot`, `tendsto_ceil_at_top`, `tendsto_ceil_at_bot`:
  `int.floor` and `int.ceil` tend to +-∞ in +-∞.
* `continuous_on_floor`: `int.floor` is continuous on `Ico n (n + 1)`, because constant.
* `continuous_on_ceil`: `int.ceil` is continuous on `Ioc n (n + 1)`, because constant.
* `continuous_on_fract`: `int.fract` is continuous on `Ico n (n + 1)`.
* `continuous_on.comp_fract`: Precomposing a continuous function satisfying `f 0 = f 1` with
  `int.fract` yields another continuous function.
-/


open Filter Function Int Set

open_locale TopologicalSpace

variable{α : Type _}[LinearOrderedRing α][FloorRing α]

theorem tendsto_floor_at_top : tendsto (floor : α → ℤ) at_top at_top :=
  floor_mono.tendsto_at_top_at_top$
    fun b =>
      ⟨(b+1 : ℤ),
        by 
          rw [floor_coe]
          exact (lt_add_one _).le⟩

theorem tendsto_floor_at_bot : tendsto (floor : α → ℤ) at_bot at_bot :=
  floor_mono.tendsto_at_bot_at_bot$ fun b => ⟨b, (floor_coe _).le⟩

theorem tendsto_ceil_at_top : tendsto (ceil : α → ℤ) at_top at_top :=
  ceil_mono.tendsto_at_top_at_top$ fun b => ⟨b, (ceil_coe _).Ge⟩

theorem tendsto_ceil_at_bot : tendsto (ceil : α → ℤ) at_bot at_bot :=
  ceil_mono.tendsto_at_bot_at_bot$
    fun b =>
      ⟨(b - 1 : ℤ),
        by 
          rw [ceil_coe]
          exact (sub_one_lt _).le⟩

variable[TopologicalSpace α]

theorem continuous_on_floor (n : ℤ) : ContinuousOn (fun x => floor x : α → α) (Ico n (n+1) : Set α) :=
  (continuous_on_congr$ floor_eq_on_Ico' n).mpr continuous_on_const

theorem continuous_on_ceil (n : ℤ) : ContinuousOn (fun x => ceil x : α → α) (Ioc (n - 1) n : Set α) :=
  (continuous_on_congr$ ceil_eq_on_Ioc' n).mpr continuous_on_const

theorem tendsto_floor_right' [OrderClosedTopology α] (n : ℤ) : tendsto (fun x => floor x : α → α) (𝓝[Ici n] n) (𝓝 n) :=
  by 
    rw [←nhds_within_Ico_eq_nhds_within_Ici (lt_add_one (n : α))]
    simpa only [floor_coe] using (continuous_on_floor n _ (left_mem_Ico.mpr$ lt_add_one (_ : α))).Tendsto

theorem tendsto_ceil_left' [OrderClosedTopology α] (n : ℤ) : tendsto (fun x => ceil x : α → α) (𝓝[Iic n] n) (𝓝 n) :=
  by 
    rw [←nhds_within_Ioc_eq_nhds_within_Iic (sub_one_lt (n : α))]
    simpa only [ceil_coe] using (continuous_on_ceil _ _ (right_mem_Ioc.mpr$ sub_one_lt (_ : α))).Tendsto

theorem tendsto_floor_right [OrderClosedTopology α] (n : ℤ) :
  tendsto (fun x => floor x : α → α) (𝓝[Ici n] n) (𝓝[Ici n] n) :=
  tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (tendsto_floor_right' _)
    (by 
      refine' eventually_nhds_with_of_forall$ fun x hx : (n : α) ≤ x => _ 
      change _ ≤ _ 
      normCast 
      convert ← floor_mono hx 
      rw [floor_eq_iff]
      exact ⟨le_reflₓ _, lt_add_one _⟩)

theorem tendsto_ceil_left [OrderClosedTopology α] (n : ℤ) :
  tendsto (fun x => ceil x : α → α) (𝓝[Iic n] n) (𝓝[Iic n] n) :=
  tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (tendsto_ceil_left' _)
    (by 
      refine' eventually_nhds_with_of_forall$ fun x hx : x ≤ (n : α) => _ 
      change _ ≤ _ 
      normCast 
      convert ← ceil_mono hx 
      rw [ceil_eq_iff]
      exact ⟨sub_one_lt _, le_reflₓ _⟩)

theorem tendsto_floor_left [OrderClosedTopology α] (n : ℤ) :
  tendsto (fun x => floor x : α → α) (𝓝[Iio n] n) (𝓝[Iic (n - 1)] (n - 1)) :=
  by 
    rw [←nhds_within_Ico_eq_nhds_within_Iio (sub_one_lt (n : α))]
    convert
        (tendsto_nhds_within_congr$ fun x hx => (floor_eq_on_Ico' (n - 1) x hx).symm)
          (tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ tendsto_const_nhds
            (eventually_of_forall fun _ => mem_Iic.mpr$ le_reflₓ _)) <;>
      first |
        normCast|
        infer_instance 
    ring

theorem tendsto_ceil_right [OrderClosedTopology α] (n : ℤ) :
  tendsto (fun x => ceil x : α → α) (𝓝[Ioi n] n) (𝓝[Ici (n+1)] n+1) :=
  by 
    rw [←nhds_within_Ioc_eq_nhds_within_Ioi (lt_add_one (n : α))]
    convert
        (tendsto_nhds_within_congr$ fun x hx => (ceil_eq_on_Ioc' (n+1) x hx).symm)
          (tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ tendsto_const_nhds
            (eventually_of_forall fun _ => mem_Ici.mpr$ le_reflₓ _)) <;>
      first |
        normCast|
        infer_instance 
    ring

theorem tendsto_floor_left' [OrderClosedTopology α] (n : ℤ) :
  tendsto (fun x => floor x : α → α) (𝓝[Iio n] n) (𝓝 (n - 1)) :=
  by 
    rw [←nhds_within_univ]
    exact tendsto_nhds_within_mono_right (subset_univ _) (tendsto_floor_left n)

theorem tendsto_ceil_right' [OrderClosedTopology α] (n : ℤ) :
  tendsto (fun x => ceil x : α → α) (𝓝[Ioi n] n) (𝓝 (n+1)) :=
  by 
    rw [←nhds_within_univ]
    exact tendsto_nhds_within_mono_right (subset_univ _) (tendsto_ceil_right n)

theorem continuous_on_fract [TopologicalAddGroup α] (n : ℤ) : ContinuousOn (fract : α → α) (Ico n (n+1) : Set α) :=
  continuous_on_id.sub (continuous_on_floor n)

theorem tendsto_fract_left' [OrderClosedTopology α] [TopologicalAddGroup α] (n : ℤ) :
  tendsto (fract : α → α) (𝓝[Iio n] n) (𝓝 1) :=
  by 
    convert (tendsto_nhds_within_of_tendsto_nhds tendsto_id).sub (tendsto_floor_left' n) <;>
      [·
        normCast 
        ring,
      infer_instance, infer_instance]

theorem tendsto_fract_left [OrderClosedTopology α] [TopologicalAddGroup α] (n : ℤ) :
  tendsto (fract : α → α) (𝓝[Iio n] n) (𝓝[Iio 1] 1) :=
  tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_left' _) (eventually_of_forall fract_lt_one)

theorem tendsto_fract_right' [OrderClosedTopology α] [TopologicalAddGroup α] (n : ℤ) :
  tendsto (fract : α → α) (𝓝[Ici n] n) (𝓝 0) :=
  by 
    convert (tendsto_nhds_within_of_tendsto_nhds tendsto_id).sub (tendsto_floor_right' n) <;> [exact (sub_self _).symm,
      infer_instance, infer_instance]

theorem tendsto_fract_right [OrderClosedTopology α] [TopologicalAddGroup α] (n : ℤ) :
  tendsto (fract : α → α) (𝓝[Ici n] n) (𝓝[Ici 0] 0) :=
  tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_right' _)
    (eventually_of_forall fract_nonneg)

local notation "I" => (Icc 0 1 : Set α)

-- error in Topology.Algebra.FloorRing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem continuous_on.comp_fract'
{β γ : Type*}
[order_topology α]
[topological_add_group α]
[topological_space β]
[topological_space γ]
{f : β → α → γ}
(h : «expr $ »(continuous_on (uncurry f), (univ : set β).prod exprI()))
(hf : ∀ s, «expr = »(f s 0, f s 1)) : continuous (λ st : «expr × »(β, α), «expr $ »(f st.1, fract st.2)) :=
begin
  change [expr continuous «expr ∘ »(uncurry f, prod.map id fract)] [] [],
  rw [expr continuous_iff_continuous_at] [],
  rintro ["⟨", ident s, ",", ident t, "⟩"],
  by_cases [expr ht, ":", expr «expr = »(t, floor t)],
  { rw [expr ht] [],
    rw ["<-", expr continuous_within_at_univ] [],
    have [] [":", expr «expr ⊆ »((univ : set «expr × »(β, α)), «expr ∪ »(set.prod univ «expr $ »(Iio, floor t), set.prod univ «expr $ »(Ici, floor t)))] [],
    { rintros [ident p, "-"],
      rw ["<-", expr prod_union] [],
      exact [expr ⟨true.intro, lt_or_le _ _⟩] },
    refine [expr continuous_within_at.mono _ this],
    refine [expr continuous_within_at.union _ _],
    { simp [] [] ["only"] ["[", expr continuous_within_at, ",", expr fract_coe, ",", expr nhds_within_prod_eq, ",", expr nhds_within_univ, ",", expr id.def, ",", expr comp_app, ",", expr prod.map_mk, "]"] [] [],
      have [] [":", expr «expr = »(uncurry f (s, 0), uncurry f (s, (1 : α)))] [],
      by simp [] [] [] ["[", expr uncurry, ",", expr hf, "]"] [] [],
      rw [expr this] [],
      refine [expr (h _ ⟨true.intro, by exact_mod_cast [expr right_mem_Icc.mpr zero_le_one]⟩).tendsto.comp _],
      rw ["[", expr nhds_within_prod_eq, ",", expr nhds_within_univ, "]"] [],
      rw [expr nhds_within_Icc_eq_nhds_within_Iic (@zero_lt_one α _ _)] [],
      exact [expr tendsto_id.prod_map «expr $ »(tendsto_nhds_within_mono_right Iio_subset_Iic_self, tendsto_fract_left _)] },
    { simp [] [] ["only"] ["[", expr continuous_within_at, ",", expr fract_coe, ",", expr nhds_within_prod_eq, ",", expr nhds_within_univ, ",", expr id.def, ",", expr comp_app, ",", expr prod.map_mk, "]"] [] [],
      refine [expr (h _ ⟨true.intro, by exact_mod_cast [expr left_mem_Icc.mpr zero_le_one]⟩).tendsto.comp _],
      rw ["[", expr nhds_within_prod_eq, ",", expr nhds_within_univ, ",", expr nhds_within_Icc_eq_nhds_within_Ici (@zero_lt_one α _ _), "]"] [],
      exact [expr tendsto_id.prod_map (tendsto_fract_right _)] } },
  { have [] [":", expr «expr ∈ »(t, Ioo (floor t : α) «expr + »((floor t : α), 1))] [],
    from [expr ⟨lt_of_le_of_ne (floor_le t) (ne.symm ht), lt_floor_add_one _⟩],
    apply [expr (h (prod.map _ fract _) ⟨trivial, ⟨fract_nonneg _, (fract_lt_one _).le⟩⟩).tendsto.comp],
    simp [] [] ["only"] ["[", expr nhds_prod_eq, ",", expr nhds_within_prod_eq, ",", expr nhds_within_univ, ",", expr id.def, ",", expr prod.map_mk, "]"] [] [],
    exact [expr continuous_at_id.tendsto.prod_map (tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (((continuous_on_fract _ _ (Ioo_subset_Ico_self this)).mono Ioo_subset_Ico_self).continuous_at (Ioo_mem_nhds this.1 this.2)) (eventually_of_forall (λ
        x, ⟨fract_nonneg _, (fract_lt_one _).le⟩)))] }
end

-- error in Topology.Algebra.FloorRing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem continuous_on.comp_fract
{β : Type*}
[order_topology α]
[topological_add_group α]
[topological_space β]
{f : α → β}
(h : continuous_on f exprI())
(hf : «expr = »(f 0, f 1)) : continuous «expr ∘ »(f, fract) :=
begin
  let [ident f'] [":", expr unit → α → β] [":=", expr λ x y, f y],
  have [] [":", expr continuous_on (uncurry f') ((univ : set unit).prod exprI())] [],
  { rintros ["⟨", ident s, ",", ident t, "⟩", "⟨", "-", ",", ident ht, ":", expr «expr ∈ »(t, exprI()), "⟩"],
    simp [] [] ["only"] ["[", expr continuous_within_at, ",", expr uncurry, ",", expr nhds_within_prod_eq, ",", expr nhds_within_univ, ",", expr f', "]"] [] [],
    rw [expr tendsto_prod_iff] [],
    intros [ident W, ident hW],
    specialize [expr h t ht hW],
    rw [expr mem_map_iff_exists_image] ["at", ident h],
    rcases [expr h, "with", "⟨", ident V, ",", ident hV, ",", ident hVW, "⟩"],
    rw [expr image_subset_iff] ["at", ident hVW],
    use ["[", expr univ, ",", expr univ_mem, ",", expr V, ",", expr hV, "]"],
    intros [ident x, ident y, ident hx, ident hy],
    exact [expr hVW hy] },
  have [ident key] [":", expr continuous (λ
   s, ⟨unit.star, s⟩ : α → «expr × »(unit, α))] [":=", expr by continuity [] []],
  exact [expr (this.comp_fract' (λ s, hf)).comp key]
end

