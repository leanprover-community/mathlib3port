import Mathbin.Topology.Instances.Ennreal 
import Mathbin.Topology.Algebra.Ordered.MonotoneContinuity 
import Mathbin.Data.Real.Ereal

/-!
# Topological structure on `ereal`

We endow `ereal` with the order topology, and prove basic properties of this topology.

## Main results

* `coe : ℝ → ereal` is an open embedding
* `coe : ℝ≥0∞ → ereal` is an embedding
* The addition on `ereal` is continuous except at `(⊥, ⊤)` and at `(⊤, ⊥)`.
* Negation is a homeomorphism on `ereal`.

## Implementation

Most proofs are adapted from the corresponding proofs on `ℝ≥0∞`.
-/


noncomputable theory

open Classical Set Filter Metric TopologicalSpace

open_locale Classical TopologicalSpace Ennreal Nnreal BigOperators Filter

variable{α : Type _}[TopologicalSpace α]

namespace Ereal

instance  : TopologicalSpace Ereal :=
  Preorderₓ.topology Ereal

instance  : OrderTopology Ereal :=
  ⟨rfl⟩

instance  : T2Space Ereal :=
  by 
    infer_instance

-- error in Topology.Instances.Ereal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance : second_countable_topology ereal :=
⟨begin
   refine [expr ⟨«expr⋃ , »((q : exprℚ()), {{a : ereal | «expr < »(a, (q : exprℝ()))}, {a : ereal | «expr < »(((q : exprℝ()) : ereal), a)}}), countable_Union (λ
      a, (countable_singleton _).insert _), _⟩],
   refine [expr le_antisymm «expr $ »(le_generate_from, by simp [] [] [] ["[", expr or_imp_distrib, ",", expr is_open_lt', ",", expr is_open_gt', "]"] [] [] { contextual := tt }) _],
   apply [expr le_generate_from (λ s h, _)],
   rcases [expr h, "with", "⟨", ident a, ",", ident hs, "|", ident hs, "⟩"]; [rw [expr show «expr = »(s, «expr⋃ , »((q «expr ∈ » {q : exprℚ() | «expr < »(a, (q : exprℝ()))}), {b | «expr < »(((q : exprℝ()) : ereal), b)})), by { ext [] [ident x] [],
       simpa [] [] ["only"] ["[", expr hs, ",", expr exists_prop, ",", expr mem_Union, "]"] [] ["using", expr lt_iff_exists_rat_btwn] }] [], rw [expr show «expr = »(s, «expr⋃ , »((q «expr ∈ » {q : exprℚ() | «expr < »(((q : exprℝ()) : ereal), a)}), {b | «expr < »(b, ((q : exprℝ()) : ereal))})), by { ext [] [ident x] [],
       simpa [] [] ["only"] ["[", expr hs, ",", expr and_comm, ",", expr exists_prop, ",", expr mem_Union, "]"] [] ["using", expr lt_iff_exists_rat_btwn] }] []]; { apply [expr is_open_Union],
     intro [ident q],
     apply [expr is_open_Union],
     intro [ident hq],
     apply [expr generate_open.basic],
     exact [expr mem_Union.2 ⟨q, by simp [] [] [] [] [] []⟩] }
 end⟩

/-! ### Real coercion -/


theorem embedding_coe : Embedding (coeₓ : ℝ → Ereal) :=
  ⟨⟨by 
        refine' le_antisymmₓ _ _
        ·
          rw [@OrderTopology.topology_eq_generate_intervals Ereal _, ←coinduced_le_iff_le_induced]
          refine' le_generate_from fun s ha => _ 
          rcases ha with ⟨a, rfl | rfl⟩
          show IsOpen { b:ℝ | a < «expr↑ » b }
          ·
            induction a using Ereal.rec
            ·
              simp only [is_open_univ, bot_lt_coe, set_of_true]
            ·
              simp only [Ereal.coe_lt_coe_iff]
              exact is_open_Ioi
            ·
              simp only [set_of_false, is_open_empty, not_top_lt]
          show IsOpen { b:ℝ | «expr↑ » b < a }
          ·
            induction a using Ereal.rec
            ·
              simp only [not_lt_bot, set_of_false, is_open_empty]
            ·
              simp only [Ereal.coe_lt_coe_iff]
              exact is_open_Iio
            ·
              simp only [is_open_univ, coe_lt_top, set_of_true]
        ·
          rw [@OrderTopology.topology_eq_generate_intervals ℝ _]
          refine' le_generate_from fun s ha => _ 
          rcases ha with ⟨a, rfl | rfl⟩
          exact
            ⟨Ioi a, is_open_Ioi,
              by 
                simp [Ioi]⟩
          exact
            ⟨Iio a, is_open_Iio,
              by 
                simp [Iio]⟩⟩,
    fun a b =>
      by 
        simp only [imp_self, Ereal.coe_eq_coe_iff]⟩

theorem open_embedding_coe : OpenEmbedding (coeₓ : ℝ → Ereal) :=
  ⟨embedding_coe,
    by 
      convert @is_open_Ioo Ereal _ _ _ ⊥ ⊤
      ext x 
      induction x using Ereal.rec
      ·
        simp only [left_mem_Ioo, mem_range, coe_ne_bot, exists_false, not_false_iff]
      ·
        simp only [mem_range_self, mem_Ioo, bot_lt_coe, coe_lt_top, and_selfₓ]
      ·
        simp only [mem_range, right_mem_Ioo, exists_false, coe_ne_top]⟩

@[normCast]
theorem tendsto_coe {α : Type _} {f : Filter α} {m : α → ℝ} {a : ℝ} :
  tendsto (fun a => (m a : Ereal)) f (𝓝 («expr↑ » a)) ↔ tendsto m f (𝓝 a) :=
  embedding_coe.tendsto_nhds_iff.symm

theorem _root_.continuous_coe_real_ereal : Continuous (coeₓ : ℝ → Ereal) :=
  embedding_coe.Continuous

theorem continuous_coe_iff {f : α → ℝ} : (Continuous fun a => (f a : Ereal)) ↔ Continuous f :=
  embedding_coe.continuous_iff.symm

theorem nhds_coe {r : ℝ} : 𝓝 (r : Ereal) = (𝓝 r).map coeₓ :=
  (open_embedding_coe.map_nhds_eq r).symm

theorem nhds_coe_coe {r p : ℝ} : 𝓝 ((r : Ereal), (p : Ereal)) = (𝓝 (r, p)).map fun p : ℝ × ℝ => (p.1, p.2) :=
  ((open_embedding_coe.Prod open_embedding_coe).map_nhds_eq (r, p)).symm

theorem tendsto_to_real {a : Ereal} (ha : a ≠ ⊤) (h'a : a ≠ ⊥) : tendsto Ereal.toReal (𝓝 a) (𝓝 a.to_real) :=
  by 
    lift a to ℝ using And.intro ha h'a 
    rw [nhds_coe, tendsto_map'_iff]
    exact tendsto_id

theorem continuous_on_to_real : ContinuousOn Ereal.toReal ({⊥, ⊤} : Set Ereal).Compl :=
  fun a ha =>
    ContinuousAt.continuous_within_at
      (tendsto_to_real
        (by 
          simp [not_or_distrib] at ha 
          exact ha.2)
        (by 
          simp [not_or_distrib] at ha 
          exact ha.1))

/-- The set of finite `ereal` numbers is homeomorphic to `ℝ`. -/
def ne_bot_top_homeomorph_real : ({⊥, ⊤} : Set Ereal).Compl ≃ₜ ℝ :=
  { ne_top_bot_equiv_real with continuous_to_fun := continuous_on_iff_continuous_restrict.1 continuous_on_to_real,
    continuous_inv_fun := continuous_subtype_mk _ continuous_coe_real_ereal }

/-! ### ennreal coercion -/


-- error in Topology.Instances.Ereal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem embedding_coe_ennreal : embedding (coe : «exprℝ≥0∞»() → ereal) :=
⟨⟨begin
    refine [expr le_antisymm _ _],
    { rw ["[", expr @order_topology.topology_eq_generate_intervals ereal _, ",", "<-", expr coinduced_le_iff_le_induced, "]"] [],
      refine [expr le_generate_from (assume s ha, _)],
      rcases [expr ha, "with", "⟨", ident a, ",", ident rfl, "|", ident rfl, "⟩"],
      show [expr is_open {b : «exprℝ≥0∞»() | «expr < »(a, «expr↑ »(b))}],
      { induction [expr a] ["using", ident ereal.rec] ["with", ident x] [],
        { simp [] [] ["only"] ["[", expr is_open_univ, ",", expr bot_lt_coe_ennreal, ",", expr set_of_true, "]"] [] [] },
        { rcases [expr le_or_lt 0 x, "with", ident h, "|", ident h],
          { have [] [":", expr «expr = »((x : ereal), ((id ⟨x, h⟩ : «exprℝ≥0»()) : «exprℝ≥0∞»()))] [":=", expr rfl],
            rw [expr this] [],
            simp [] [] ["only"] ["[", expr id.def, ",", expr coe_ennreal_lt_coe_ennreal_iff, "]"] [] [],
            exact [expr is_open_Ioi] },
          { have [] [":", expr ∀
             y : «exprℝ≥0∞»(), «expr < »((x : ereal), y)] [":=", expr λ
             y, (ereal.coe_lt_coe_iff.2 h).trans_le (coe_ennreal_nonneg _)],
            simp [] [] ["only"] ["[", expr this, ",", expr is_open_univ, ",", expr set_of_true, "]"] [] [] } },
        { simp [] [] ["only"] ["[", expr set_of_false, ",", expr is_open_empty, ",", expr not_top_lt, "]"] [] [] } },
      show [expr is_open {b : «exprℝ≥0∞»() | «expr < »(«expr↑ »(b), a)}],
      { induction [expr a] ["using", ident ereal.rec] ["with", ident x] [],
        { simp [] [] ["only"] ["[", expr not_lt_bot, ",", expr set_of_false, ",", expr is_open_empty, "]"] [] [] },
        { rcases [expr le_or_lt 0 x, "with", ident h, "|", ident h],
          { have [] [":", expr «expr = »((x : ereal), ((id ⟨x, h⟩ : «exprℝ≥0»()) : «exprℝ≥0∞»()))] [":=", expr rfl],
            rw [expr this] [],
            simp [] [] ["only"] ["[", expr id.def, ",", expr coe_ennreal_lt_coe_ennreal_iff, "]"] [] [],
            exact [expr is_open_Iio] },
          { convert [] [expr is_open_empty] [],
            apply [expr eq_empty_iff_forall_not_mem.2 (λ y hy, lt_irrefl (x : ereal) _)],
            exact [expr ((ereal.coe_lt_coe_iff.2 h).trans_le (coe_ennreal_nonneg y)).trans hy] } },
        { simp [] [] ["only"] ["[", "<-", expr coe_ennreal_top, ",", expr coe_ennreal_lt_coe_ennreal_iff, "]"] [] [],
          exact [expr is_open_Iio] } } },
    { rw ["[", expr @order_topology.topology_eq_generate_intervals «exprℝ≥0∞»() _, "]"] [],
      refine [expr le_generate_from (assume s ha, _)],
      rcases [expr ha, "with", "⟨", ident a, ",", ident rfl, "|", ident rfl, "⟩"],
      exact [expr ⟨Ioi a, is_open_Ioi, by simp [] [] [] ["[", expr Ioi, "]"] [] []⟩],
      exact [expr ⟨Iio a, is_open_Iio, by simp [] [] [] ["[", expr Iio, "]"] [] []⟩] }
  end⟩, assume a b, by simp [] [] ["only"] ["[", expr imp_self, ",", expr coe_ennreal_eq_coe_ennreal_iff, "]"] [] []⟩

@[normCast]
theorem tendsto_coe_ennreal {α : Type _} {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} :
  tendsto (fun a => (m a : Ereal)) f (𝓝 («expr↑ » a)) ↔ tendsto m f (𝓝 a) :=
  embedding_coe_ennreal.tendsto_nhds_iff.symm

theorem _root_.continuous_coe_ennreal_ereal : Continuous (coeₓ : ℝ≥0∞ → Ereal) :=
  embedding_coe_ennreal.Continuous

theorem continuous_coe_ennreal_iff {f : α → ℝ≥0∞} : (Continuous fun a => (f a : Ereal)) ↔ Continuous f :=
  embedding_coe_ennreal.continuous_iff.symm

/-! ### Neighborhoods of infinity -/


theorem nhds_top : 𝓝 (⊤ : Ereal) = ⨅(a : _)(_ : a ≠ ⊤), 𝓟 (Ioi a) :=
  nhds_top_order.trans$
    by 
      simp [lt_top_iff_ne_top, Ioi]

theorem nhds_top' : 𝓝 (⊤ : Ereal) = ⨅a : ℝ, 𝓟 (Ioi a) :=
  by 
    rw [nhds_top]
    apply le_antisymmₓ
    ·
      exact
        infi_le_infi2
          fun x =>
            ⟨x,
              by 
                simp ⟩
    ·
      refine' le_infi fun r => le_infi fun hr => _ 
      induction r using Ereal.rec
      ·
        exact
          (infi_le _ 0).trans
            (by 
              simp )
      ·
        exact infi_le _ _
      ·
        simpa using hr

theorem mem_nhds_top_iff {s : Set Ereal} : s ∈ 𝓝 (⊤ : Ereal) ↔ ∃ y : ℝ, Ioi (y : Ereal) ⊆ s :=
  by 
    rw [nhds_top', mem_infi_of_directed]
    ·
      rfl 
    exact
      fun x y =>
        ⟨max x y,
          by 
            simp [le_reflₓ],
          by 
            simp [le_reflₓ]⟩

theorem tendsto_nhds_top_iff_real {α : Type _} {m : α → Ereal} {f : Filter α} :
  tendsto m f (𝓝 ⊤) ↔ ∀ x : ℝ, ∀ᶠa in f, «expr↑ » x < m a :=
  by 
    simp only [nhds_top', mem_Ioi, tendsto_infi, tendsto_principal]

theorem nhds_bot : 𝓝 (⊥ : Ereal) = ⨅(a : _)(_ : a ≠ ⊥), 𝓟 (Iio a) :=
  nhds_bot_order.trans$
    by 
      simp [bot_lt_iff_ne_bot]

theorem nhds_bot' : 𝓝 (⊥ : Ereal) = ⨅a : ℝ, 𝓟 (Iio a) :=
  by 
    rw [nhds_bot]
    apply le_antisymmₓ
    ·
      exact
        infi_le_infi2
          fun x =>
            ⟨x,
              by 
                simp ⟩
    ·
      refine' le_infi fun r => le_infi fun hr => _ 
      induction r using Ereal.rec
      ·
        simpa using hr
      ·
        exact infi_le _ _
      ·
        exact
          (infi_le _ 0).trans
            (by 
              simp )

theorem mem_nhds_bot_iff {s : Set Ereal} : s ∈ 𝓝 (⊥ : Ereal) ↔ ∃ y : ℝ, Iio (y : Ereal) ⊆ s :=
  by 
    rw [nhds_bot', mem_infi_of_directed]
    ·
      rfl 
    exact
      fun x y =>
        ⟨min x y,
          by 
            simp [le_reflₓ],
          by 
            simp [le_reflₓ]⟩

theorem tendsto_nhds_bot_iff_real {α : Type _} {m : α → Ereal} {f : Filter α} :
  tendsto m f (𝓝 ⊥) ↔ ∀ x : ℝ, ∀ᶠa in f, m a < x :=
  by 
    simp only [nhds_bot', mem_Iio, tendsto_infi, tendsto_principal]

/-! ### Continuity of addition -/


theorem continuous_at_add_coe_coe (a b : ℝ) : ContinuousAt (fun p : Ereal × Ereal => p.1+p.2) (a, b) :=
  by 
    simp only [ContinuousAt, nhds_coe_coe, ←coe_add, tendsto_map'_iff, · ∘ ·, tendsto_coe, tendsto_add]

theorem continuous_at_add_top_coe (a : ℝ) : ContinuousAt (fun p : Ereal × Ereal => p.1+p.2) (⊤, a) :=
  by 
    simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add, nhds_prod_eq]
    intro r 
    rw [eventually_prod_iff]
    refine'
      ⟨fun z => ((r - (a - 1) : ℝ) : Ereal) < z, Ioi_mem_nhds (coe_lt_top _), fun z => ((a - 1 : ℝ) : Ereal) < z,
        Ioi_mem_nhds
          (by 
            simp [zero_lt_one]),
        fun x hx y hy => _⟩
    dsimp 
    convert add_lt_add hx hy 
    simp 

theorem continuous_at_add_coe_top (a : ℝ) : ContinuousAt (fun p : Ereal × Ereal => p.1+p.2) (a, ⊤) :=
  by 
    change ContinuousAt ((fun p : Ereal × Ereal => p.2+p.1) ∘ Prod.swap) (a, ⊤)
    apply ContinuousAt.comp _ continuous_swap.continuous_at 
    simpRw [add_commₓ]
    exact continuous_at_add_top_coe a

theorem continuous_at_add_top_top : ContinuousAt (fun p : Ereal × Ereal => p.1+p.2) (⊤, ⊤) :=
  by 
    simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add, nhds_prod_eq]
    intro r 
    rw [eventually_prod_iff]
    refine'
      ⟨fun z => (r : Ereal) < z, Ioi_mem_nhds (coe_lt_top _), fun z => ((0 : ℝ) : Ereal) < z,
        Ioi_mem_nhds
          (by 
            simp [zero_lt_one]),
        fun x hx y hy => _⟩
    dsimp 
    convert add_lt_add hx hy 
    simp 

theorem continuous_at_add_bot_coe (a : ℝ) : ContinuousAt (fun p : Ereal × Ereal => p.1+p.2) (⊥, a) :=
  by 
    simp only [ContinuousAt, tendsto_nhds_bot_iff_real, nhds_prod_eq, bot_add_coe]
    intro r 
    rw [eventually_prod_iff]
    refine'
      ⟨fun z => z < ((r - a+1 : ℝ) : Ereal), Iio_mem_nhds (bot_lt_coe _), fun z => z < ((a+1 : ℝ) : Ereal),
        Iio_mem_nhds
          (by 
            simp [-coe_add, zero_lt_one]),
        fun x hx y hy => _⟩
    dsimp 
    convert add_lt_add hx hy 
    dsimp 
    ring

theorem continuous_at_add_coe_bot (a : ℝ) : ContinuousAt (fun p : Ereal × Ereal => p.1+p.2) (a, ⊥) :=
  by 
    change ContinuousAt ((fun p : Ereal × Ereal => p.2+p.1) ∘ Prod.swap) (a, ⊥)
    apply ContinuousAt.comp _ continuous_swap.continuous_at 
    simpRw [add_commₓ]
    exact continuous_at_add_bot_coe a

theorem continuous_at_add_bot_bot : ContinuousAt (fun p : Ereal × Ereal => p.1+p.2) (⊥, ⊥) :=
  by 
    simp only [ContinuousAt, tendsto_nhds_bot_iff_real, nhds_prod_eq, bot_add_bot]
    intro r 
    rw [eventually_prod_iff]
    refine'
      ⟨fun z => z < r, Iio_mem_nhds (bot_lt_coe _), fun z => z < 0, Iio_mem_nhds (bot_lt_coe _), fun x hx y hy => _⟩
    dsimp 
    convert add_lt_add hx hy 
    simp 

/-- The addition on `ereal` is continuous except where it doesn't make sense (i.e., at `(⊥, ⊤)`
and at `(⊤, ⊥)`). -/
theorem continuous_at_add {p : Ereal × Ereal} (h : p.1 ≠ ⊤ ∨ p.2 ≠ ⊥) (h' : p.1 ≠ ⊥ ∨ p.2 ≠ ⊤) :
  ContinuousAt (fun p : Ereal × Ereal => p.1+p.2) p :=
  by 
    rcases p with ⟨x, y⟩
    induction x using Ereal.rec <;> induction y using Ereal.rec
    ·
      exact continuous_at_add_bot_bot
    ·
      exact continuous_at_add_bot_coe _
    ·
      simpa using h'
    ·
      exact continuous_at_add_coe_bot _
    ·
      exact continuous_at_add_coe_coe _ _
    ·
      exact continuous_at_add_coe_top _
    ·
      simpa using h
    ·
      exact continuous_at_add_top_coe _
    ·
      exact continuous_at_add_top_top

/-! ### Negation-/


/-- Negation on `ereal` as a homeomorphism -/
def neg_homeo : Ereal ≃ₜ Ereal :=
  neg_order_iso.toHomeomorph

theorem continuous_neg : Continuous fun x : Ereal => -x :=
  neg_homeo.Continuous

end Ereal

