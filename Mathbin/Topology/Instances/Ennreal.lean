import Mathbin.Topology.Instances.Nnreal 
import Mathbin.Order.LiminfLimsup 
import Mathbin.Topology.MetricSpace.Lipschitz

/-!
# Extended non-negative reals
-/


noncomputable theory

open Classical Set Filter Metric

open_locale Classical TopologicalSpace Ennreal Nnreal BigOperators Filter

variable {α : Type _} {β : Type _} {γ : Type _}

namespace Ennreal

variable {a b c d : ℝ≥0∞} {r p q :  ℝ≥0 }

variable {x y z : ℝ≥0∞} {ε ε₁ ε₂ : ℝ≥0∞} {s : Set ℝ≥0∞}

section TopologicalSpace

open TopologicalSpace

/-- Topology on `ℝ≥0∞`.

Note: this is different from the `emetric_space` topology. The `emetric_space` topology has
`is_open {⊤}`, while this topology doesn't have singleton elements. -/
instance : TopologicalSpace ℝ≥0∞ :=
  Preorderₓ.topology ℝ≥0∞

instance : OrderTopology ℝ≥0∞ :=
  ⟨rfl⟩

instance : T2Space ℝ≥0∞ :=
  by 
    infer_instance

-- error in Topology.Instances.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance : second_countable_topology «exprℝ≥0∞»() :=
⟨⟨«expr⋃ , »((q «expr ≥ » (0 : exprℚ())), {{a : «exprℝ≥0∞»() | «expr < »(a, real.to_nnreal q)}, {a : «exprℝ≥0∞»() | «expr < »(«expr↑ »(real.to_nnreal q), a)}}), «expr $ »((countable_encodable _).bUnion, assume
   a
   ha, (countable_singleton _).insert _), le_antisymm «expr $ »(le_generate_from, by simp [] [] [] ["[", expr or_imp_distrib, ",", expr is_open_lt', ",", expr is_open_gt', "]"] [] [] { contextual := tt }) «expr $ »(le_generate_from, λ
   s h, begin
     rcases [expr h, "with", "⟨", ident a, ",", ident hs, "|", ident hs, "⟩"]; [rw [expr show «expr = »(s, «expr⋃ , »((q «expr ∈ » {q : exprℚ() | «expr ∧ »(«expr ≤ »(0, q), «expr < »(a, real.to_nnreal q))}), {b | «expr < »(«expr↑ »(real.to_nnreal q), b)})), from set.ext (assume
        b, by simp [] [] [] ["[", expr hs, ",", expr @ennreal.lt_iff_exists_rat_btwn a b, ",", expr and_assoc, "]"] [] [])] [], rw [expr show «expr = »(s, «expr⋃ , »((q «expr ∈ » {q : exprℚ() | «expr ∧ »(«expr ≤ »(0, q), «expr < »(«expr↑ »(real.to_nnreal q), a))}), {b | «expr < »(b, «expr↑ »(real.to_nnreal q))})), from set.ext (assume
        b, by simp [] [] [] ["[", expr hs, ",", expr @ennreal.lt_iff_exists_rat_btwn b a, ",", expr and_comm, ",", expr and_assoc, "]"] [] [])] []]; { apply [expr is_open_Union],
       intro [ident q],
       apply [expr is_open_Union],
       intro [ident hq],
       exact [expr generate_open.basic _ «expr $ »(mem_bUnion hq.1, by simp [] [] [] [] [] [])] }
   end)⟩⟩

theorem embedding_coe : Embedding (coeₓ :  ℝ≥0  → ℝ≥0∞) :=
  ⟨⟨by 
        refine' le_antisymmₓ _ _
        ·
          rw [@OrderTopology.topology_eq_generate_intervals ℝ≥0∞ _, ←coinduced_le_iff_le_induced]
          refine' le_generate_from fun s ha => _ 
          rcases ha with ⟨a, rfl | rfl⟩
          show IsOpen { b: ℝ≥0  | a < «expr↑ » b }
          ·
            cases a <;> simp [none_eq_top, some_eq_coe, is_open_lt']
          show IsOpen { b: ℝ≥0  | «expr↑ » b < a }
          ·
            cases a <;> simp [none_eq_top, some_eq_coe, is_open_gt', is_open_const]
        ·
          rw [@OrderTopology.topology_eq_generate_intervals ℝ≥0  _]
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
    fun a b => coe_eq_coe.1⟩

theorem is_open_ne_top : IsOpen { a:ℝ≥0∞ | a ≠ ⊤ } :=
  is_open_ne

theorem is_open_Ico_zero : IsOpen (Ico 0 b) :=
  by 
    rw [Ennreal.Ico_eq_Iio]
    exact is_open_Iio

theorem open_embedding_coe : OpenEmbedding (coeₓ :  ℝ≥0  → ℝ≥0∞) :=
  ⟨embedding_coe,
    by 
      convert is_open_ne_top 
      ext (x | _) <;> simp [none_eq_top, some_eq_coe]⟩

theorem coe_range_mem_nhds : range (coeₓ :  ℝ≥0  → ℝ≥0∞) ∈ 𝓝 (r : ℝ≥0∞) :=
  IsOpen.mem_nhds open_embedding_coe.open_range$ mem_range_self _

@[normCast]
theorem tendsto_coe {f : Filter α} {m : α →  ℝ≥0 } {a :  ℝ≥0 } :
  tendsto (fun a => (m a : ℝ≥0∞)) f (𝓝 («expr↑ » a)) ↔ tendsto m f (𝓝 a) :=
  embedding_coe.tendsto_nhds_iff.symm

theorem continuous_coe : Continuous (coeₓ :  ℝ≥0  → ℝ≥0∞) :=
  embedding_coe.Continuous

theorem continuous_coe_iff {α} [TopologicalSpace α] {f : α →  ℝ≥0 } :
  (Continuous fun a => (f a : ℝ≥0∞)) ↔ Continuous f :=
  embedding_coe.continuous_iff.symm

theorem nhds_coe {r :  ℝ≥0 } : 𝓝 (r : ℝ≥0∞) = (𝓝 r).map coeₓ :=
  (open_embedding_coe.map_nhds_eq r).symm

theorem tendsto_nhds_coe_iff {α : Type _} {l : Filter α} {x :  ℝ≥0 } {f : ℝ≥0∞ → α} :
  tendsto f (𝓝 («expr↑ » x)) l ↔ tendsto (f ∘ coeₓ :  ℝ≥0  → α) (𝓝 x) l :=
  show _ ≤ _ ↔ _ ≤ _ by 
    rw [nhds_coe, Filter.map_map]

theorem continuous_at_coe_iff {α : Type _} [TopologicalSpace α] {x :  ℝ≥0 } {f : ℝ≥0∞ → α} :
  ContinuousAt f («expr↑ » x) ↔ ContinuousAt (f ∘ coeₓ :  ℝ≥0  → α) x :=
  tendsto_nhds_coe_iff

theorem nhds_coe_coe {r p :  ℝ≥0 } : 𝓝 ((r : ℝ≥0∞), (p : ℝ≥0∞)) = (𝓝 (r, p)).map fun p :  ℝ≥0  ×  ℝ≥0  => (p.1, p.2) :=
  ((open_embedding_coe.Prod open_embedding_coe).map_nhds_eq (r, p)).symm

theorem continuous_of_real : Continuous Ennreal.ofReal :=
  (continuous_coe_iff.2 continuous_id).comp Nnreal.continuous_of_real

theorem tendsto_of_real {f : Filter α} {m : α → ℝ} {a : ℝ} (h : tendsto m f (𝓝 a)) :
  tendsto (fun a => Ennreal.ofReal (m a)) f (𝓝 (Ennreal.ofReal a)) :=
  tendsto.comp (Continuous.tendsto continuous_of_real _) h

theorem tendsto_to_nnreal {a : ℝ≥0∞} (ha : a ≠ ⊤) : tendsto Ennreal.toNnreal (𝓝 a) (𝓝 a.to_nnreal) :=
  by 
    lift a to  ℝ≥0  using ha 
    rw [nhds_coe, tendsto_map'_iff]
    exact tendsto_id

theorem eventually_eq_of_to_real_eventually_eq {l : Filter α} {f g : α → ℝ≥0∞} (hfi : ∀ᶠx in l, f x ≠ ∞)
  (hgi : ∀ᶠx in l, g x ≠ ∞) (hfg : (fun x => (f x).toReal) =ᶠ[l] fun x => (g x).toReal) : f =ᶠ[l] g :=
  by 
    filterUpwards [hfi, hgi, hfg]
    intro x hfx hgx hfgx 
    rwa [←Ennreal.to_real_eq_to_real hfx hgx]

theorem continuous_on_to_nnreal : ContinuousOn Ennreal.toNnreal { a | a ≠ ∞ } :=
  fun a ha => ContinuousAt.continuous_within_at (tendsto_to_nnreal ha)

theorem tendsto_to_real {a : ℝ≥0∞} (ha : a ≠ ⊤) : tendsto Ennreal.toReal (𝓝 a) (𝓝 a.to_real) :=
  Nnreal.tendsto_coe.2$ tendsto_to_nnreal ha

/-- The set of finite `ℝ≥0∞` numbers is homeomorphic to `ℝ≥0`. -/
def ne_top_homeomorph_nnreal : { a | a ≠ ∞ } ≃ₜ  ℝ≥0  :=
  { ne_top_equiv_nnreal with continuous_to_fun := continuous_on_iff_continuous_restrict.1 continuous_on_to_nnreal,
    continuous_inv_fun := continuous_subtype_mk _ continuous_coe }

/-- The set of finite `ℝ≥0∞` numbers is homeomorphic to `ℝ≥0`. -/
def lt_top_homeomorph_nnreal : { a | a < ∞ } ≃ₜ  ℝ≥0  :=
  by 
    refine' (Homeomorph.setCongr$ Set.ext$ fun x => _).trans ne_top_homeomorph_nnreal <;>
      simp only [mem_set_of_eq, lt_top_iff_ne_top]

theorem nhds_top : 𝓝 ∞ = ⨅(a : _)(_ : a ≠ ∞), 𝓟 (Ioi a) :=
  nhds_top_order.trans$
    by 
      simp [lt_top_iff_ne_top, Ioi]

theorem nhds_top' : 𝓝 ∞ = ⨅r :  ℝ≥0 , 𝓟 (Ioi r) :=
  nhds_top.trans$ infi_ne_top _

theorem nhds_top_basis : (𝓝 ∞).HasBasis (fun a => a < ∞) fun a => Ioi a :=
  nhds_top_basis

theorem tendsto_nhds_top_iff_nnreal {m : α → ℝ≥0∞} {f : Filter α} :
  tendsto m f (𝓝 ⊤) ↔ ∀ x :  ℝ≥0 , ∀ᶠa in f, «expr↑ » x < m a :=
  by 
    simp only [nhds_top', tendsto_infi, tendsto_principal, mem_Ioi]

theorem tendsto_nhds_top_iff_nat {m : α → ℝ≥0∞} {f : Filter α} :
  tendsto m f (𝓝 ⊤) ↔ ∀ n : ℕ, ∀ᶠa in f, «expr↑ » n < m a :=
  tendsto_nhds_top_iff_nnreal.trans
    ⟨fun h n =>
        by 
          simpa only [Ennreal.coe_nat] using h n,
      fun h x =>
        let ⟨n, hn⟩ := exists_nat_gt x
        (h n).mono
          fun y =>
            lt_transₓ$
              by 
                rwa [←Ennreal.coe_nat, coe_lt_coe]⟩

theorem tendsto_nhds_top {m : α → ℝ≥0∞} {f : Filter α} (h : ∀ n : ℕ, ∀ᶠa in f, «expr↑ » n < m a) : tendsto m f (𝓝 ⊤) :=
  tendsto_nhds_top_iff_nat.2 h

theorem tendsto_nat_nhds_top : tendsto (fun n : ℕ => «expr↑ » n) at_top (𝓝 ∞) :=
  tendsto_nhds_top$ fun n => mem_at_top_sets.2 ⟨n+1, fun m hm => Ennreal.coe_nat_lt_coe_nat.2$ Nat.lt_of_succ_leₓ hm⟩

@[simp, normCast]
theorem tendsto_coe_nhds_top {f : α →  ℝ≥0 } {l : Filter α} :
  tendsto (fun x => (f x : ℝ≥0∞)) l (𝓝 ∞) ↔ tendsto f l at_top :=
  by 
    rw [tendsto_nhds_top_iff_nnreal, at_top_basis_Ioi.tendsto_right_iff] <;> [simp , infer_instance, infer_instance]

theorem nhds_zero : 𝓝 (0 : ℝ≥0∞) = ⨅(a : _)(_ : a ≠ 0), 𝓟 (Iio a) :=
  nhds_bot_order.trans$
    by 
      simp [bot_lt_iff_ne_bot, Iio]

theorem nhds_zero_basis : (𝓝 (0 : ℝ≥0∞)).HasBasis (fun a : ℝ≥0∞ => 0 < a) fun a => Iio a :=
  nhds_bot_basis

theorem nhds_zero_basis_Iic : (𝓝 (0 : ℝ≥0∞)).HasBasis (fun a : ℝ≥0∞ => 0 < a) Iic :=
  nhds_bot_basis_Iic

@[instance]
theorem nhds_within_Ioi_coe_ne_bot {r :  ℝ≥0 } : (𝓝[Ioi r] (r : ℝ≥0∞)).ne_bot :=
  nhds_within_Ioi_self_ne_bot' Ennreal.coe_lt_top

@[instance]
theorem nhds_within_Ioi_zero_ne_bot : (𝓝[Ioi 0] (0 : ℝ≥0∞)).ne_bot :=
  nhds_within_Ioi_coe_ne_bot

-- error in Topology.Instances.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem Icc_mem_nhds
(xt : «expr ≠ »(x, «expr⊤»()))
(ε0 : «expr ≠ »(ε, 0)) : «expr ∈ »(Icc «expr - »(x, ε) «expr + »(x, ε), expr𝓝() x) :=
begin
  rw [expr _root_.mem_nhds_iff] [],
  by_cases [expr x0, ":", expr «expr = »(x, 0)],
  { use [expr Iio «expr + »(x, ε)],
    have [] [":", expr «expr ⊆ »(Iio «expr + »(x, ε), Icc «expr - »(x, ε) «expr + »(x, ε))] [],
    assume [binders (a)],
    rw [expr x0] [],
    simpa [] [] [] [] [] ["using", expr le_of_lt],
    use [expr this],
    exact [expr ⟨is_open_Iio, mem_Iio_self_add xt ε0⟩] },
  { use [expr Ioo «expr - »(x, ε) «expr + »(x, ε)],
    use [expr Ioo_subset_Icc_self],
    exact [expr ⟨is_open_Ioo, mem_Ioo_self_sub_add xt x0 ε0 ε0⟩] }
end

-- error in Topology.Instances.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nhds_of_ne_top
(xt : «expr ≠ »(x, «expr⊤»())) : «expr = »(expr𝓝() x, «expr⨅ , »((ε «expr > » 0), expr𝓟() (Icc «expr - »(x, ε) «expr + »(x, ε)))) :=
begin
  refine [expr le_antisymm _ _],
  simp [] [] ["only"] ["[", expr le_infi_iff, ",", expr le_principal_iff, "]"] [] [],
  assume [binders (ε ε0)],
  exact [expr Icc_mem_nhds xt ε0.lt.ne'],
  rw [expr nhds_generate_from] [],
  refine [expr le_infi (assume s, «expr $ »(le_infi, assume hs, _))],
  rcases [expr hs, "with", "⟨", ident xs, ",", "⟨", ident a, ",", "(", ident rfl, ":", expr «expr = »(s, Ioi a), ")", "|", "(", ident rfl, ":", expr «expr = »(s, Iio a), ")", "⟩", "⟩"],
  { rcases [expr exists_between xs, "with", "⟨", ident b, ",", ident ab, ",", ident bx, "⟩"],
    have [ident xb_pos] [":", expr «expr < »(0, «expr - »(x, b))] [":=", expr tsub_pos_iff_lt.2 bx],
    have [ident xxb] [":", expr «expr = »(«expr - »(x, «expr - »(x, b)), b)] [":=", expr sub_sub_cancel xt bx.le],
    refine [expr infi_le_of_le «expr - »(x, b) (infi_le_of_le xb_pos _)],
    simp [] [] ["only"] ["[", expr mem_principal, ",", expr le_principal_iff, "]"] [] [],
    assume [binders (y)],
    rintros ["⟨", ident h₁, ",", ident h₂, "⟩"],
    rw [expr xxb] ["at", ident h₁],
    calc
      «expr < »(a, b) : ab
      «expr ≤ »(..., y) : h₁ },
  { rcases [expr exists_between xs, "with", "⟨", ident b, ",", ident xb, ",", ident ba, "⟩"],
    have [ident bx_pos] [":", expr «expr < »(0, «expr - »(b, x))] [":=", expr tsub_pos_iff_lt.2 xb],
    have [ident xbx] [":", expr «expr = »(«expr + »(x, «expr - »(b, x)), b)] [":=", expr add_tsub_cancel_of_le xb.le],
    refine [expr infi_le_of_le «expr - »(b, x) (infi_le_of_le bx_pos _)],
    simp [] [] ["only"] ["[", expr mem_principal, ",", expr le_principal_iff, "]"] [] [],
    assume [binders (y)],
    rintros ["⟨", ident h₁, ",", ident h₂, "⟩"],
    rw [expr xbx] ["at", ident h₂],
    calc
      «expr ≤ »(y, b) : h₂
      «expr < »(..., a) : ba }
end

/-- Characterization of neighborhoods for `ℝ≥0∞` numbers. See also `tendsto_order`
for a version with strict inequalities. -/
protected theorem tendsto_nhds {f : Filter α} {u : α → ℝ≥0∞} {a : ℝ≥0∞} (ha : a ≠ ⊤) :
  tendsto u f (𝓝 a) ↔ ∀ ε _ : ε > 0, ∀ᶠx in f, u x ∈ Icc (a - ε) (a+ε) :=
  by 
    simp only [nhds_of_ne_top ha, tendsto_infi, tendsto_principal, mem_Icc]

protected theorem tendsto_at_top [Nonempty β] [SemilatticeSup β] {f : β → ℝ≥0∞} {a : ℝ≥0∞} (ha : a ≠ ⊤) :
  tendsto f at_top (𝓝 a) ↔ ∀ ε _ : ε > 0, ∃ N, ∀ n _ : n ≥ N, f n ∈ Icc (a - ε) (a+ε) :=
  by 
    simp only [Ennreal.tendsto_nhds ha, mem_at_top_sets, mem_set_of_eq, Filter.Eventually]

instance : HasContinuousAdd ℝ≥0∞ :=
  by 
    refine' ⟨continuous_iff_continuous_at.2 _⟩
    rintro ⟨_ | a, b⟩
    ·
      exact tendsto_nhds_top_mono' continuous_at_fst fun p => le_add_right le_rfl 
    rcases b with (_ | b)
    ·
      exact tendsto_nhds_top_mono' continuous_at_snd fun p => le_add_left le_rfl 
    simp only [ContinuousAt, some_eq_coe, nhds_coe_coe, ←coe_add, tendsto_map'_iff, · ∘ ·, tendsto_coe, tendsto_add]

protected theorem tendsto_at_top_zero [hβ : Nonempty β] [SemilatticeSup β] {f : β → ℝ≥0∞} :
  Filter.atTop.Tendsto f (𝓝 0) ↔ ∀ ε _ : ε > 0, ∃ N, ∀ n _ : n ≥ N, f n ≤ ε :=
  by 
    rw [Ennreal.tendsto_at_top zero_ne_top]
    ·
      simpRw [Set.mem_Icc, zero_addₓ, zero_tsub, zero_le _, true_andₓ]
    ·
      exact hβ

protected theorem tendsto_mul (ha : a ≠ 0 ∨ b ≠ ⊤) (hb : b ≠ 0 ∨ a ≠ ⊤) :
  tendsto (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1*p.2) (𝓝 (a, b)) (𝓝 (a*b)) :=
  have ht : ∀ b : ℝ≥0∞, b ≠ 0 → tendsto (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1*p.2) (𝓝 ((⊤ : ℝ≥0∞), b)) (𝓝 ⊤) :=
    by 
      refine' fun b hb => tendsto_nhds_top_iff_nnreal.2$ fun n => _ 
      rcases lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hb) with ⟨ε, hε, hεb⟩
      replace hε : 0 < ε 
      exact coe_pos.1 hε 
      filterUpwards [ProdIsOpen.mem_nhds (lt_mem_nhds$ @coe_lt_top (n / ε)) (lt_mem_nhds hεb)]
      rintro ⟨a₁, a₂⟩ ⟨h₁, h₂⟩
      dsimp  at h₁ h₂⊢
      rw [←div_mul_cancel n hε.ne', coe_mul]
      exact mul_lt_mul h₁ h₂ 
  by 
    cases a
    ·
      simp [none_eq_top] at hb 
      simp [none_eq_top, ht b hb, top_mul, hb]
    cases b
    ·
      simp [none_eq_top] at ha 
      simp [nhds_swap (a : ℝ≥0∞) ⊤, none_eq_top, some_eq_coe, top_mul, tendsto_map'_iff, · ∘ ·, mul_commₓ]
    simp [some_eq_coe, nhds_coe_coe, tendsto_map'_iff, · ∘ ·]
    simp only [coe_mul.symm, tendsto_coe, tendsto_mul]

protected theorem tendsto.mul {f : Filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞} (hma : tendsto ma f (𝓝 a))
  (ha : a ≠ 0 ∨ b ≠ ⊤) (hmb : tendsto mb f (𝓝 b)) (hb : b ≠ 0 ∨ a ≠ ⊤) : tendsto (fun a => ma a*mb a) f (𝓝 (a*b)) :=
  show tendsto ((fun p : ℝ≥0∞ × ℝ≥0∞ => p.1*p.2) ∘ fun a => (ma a, mb a)) f (𝓝 (a*b)) from
    tendsto.comp (Ennreal.tendsto_mul ha hb) (hma.prod_mk_nhds hmb)

protected theorem tendsto.const_mul {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞} (hm : tendsto m f (𝓝 b))
  (hb : b ≠ 0 ∨ a ≠ ⊤) : tendsto (fun b => a*m b) f (𝓝 (a*b)) :=
  by_cases
    (fun this : a = 0 =>
      by 
        simp [this, tendsto_const_nhds])
    fun ha : a ≠ 0 => Ennreal.Tendsto.mul tendsto_const_nhds (Or.inl ha) hm hb

protected theorem tendsto.mul_const {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞} (hm : tendsto m f (𝓝 a))
  (ha : a ≠ 0 ∨ b ≠ ⊤) : tendsto (fun x => m x*b) f (𝓝 (a*b)) :=
  by 
    simpa only [mul_commₓ] using Ennreal.Tendsto.const_mul hm ha

theorem tendsto_finset_prod_of_ne_top {ι : Type _} {f : ι → α → ℝ≥0∞} {x : Filter α} {a : ι → ℝ≥0∞} (s : Finset ι)
  (h : ∀ i _ : i ∈ s, tendsto (f i) x (𝓝 (a i))) (h' : ∀ i _ : i ∈ s, a i ≠ ∞) :
  tendsto (fun b => ∏c in s, f c b) x (𝓝 (∏c in s, a c)) :=
  by 
    induction' s using Finset.induction with a s has IH
    ·
      simp [tendsto_const_nhds]
    simp only [Finset.prod_insert has]
    apply tendsto.mul (h _ (Finset.mem_insert_self _ _))
    ·
      right 
      exact (prod_lt_top fun i hi => h' _ (Finset.mem_insert_of_mem hi)).Ne
    ·
      exact IH (fun i hi => h _ (Finset.mem_insert_of_mem hi)) fun i hi => h' _ (Finset.mem_insert_of_mem hi)
    ·
      exact Or.inr (h' _ (Finset.mem_insert_self _ _))

protected theorem continuous_at_const_mul {a b : ℝ≥0∞} (h : a ≠ ⊤ ∨ b ≠ 0) : ContinuousAt ((·*·) a) b :=
  tendsto.const_mul tendsto_id h.symm

protected theorem continuous_at_mul_const {a b : ℝ≥0∞} (h : a ≠ ⊤ ∨ b ≠ 0) : ContinuousAt (fun x => x*a) b :=
  tendsto.mul_const tendsto_id h.symm

protected theorem continuous_const_mul {a : ℝ≥0∞} (ha : a ≠ ⊤) : Continuous ((·*·) a) :=
  continuous_iff_continuous_at.2$ fun x => Ennreal.continuous_at_const_mul (Or.inl ha)

protected theorem continuous_mul_const {a : ℝ≥0∞} (ha : a ≠ ⊤) : Continuous fun x => x*a :=
  continuous_iff_continuous_at.2$ fun x => Ennreal.continuous_at_mul_const (Or.inl ha)

@[continuity]
theorem continuous_pow (n : ℕ) : Continuous fun a : ℝ≥0∞ => a ^ n :=
  by 
    induction' n with n IH
    ·
      simp [continuous_const]
    simpRw [Nat.succ_eq_add_one, pow_addₓ, pow_oneₓ, continuous_iff_continuous_at]
    intro x 
    refine' Ennreal.Tendsto.mul (IH.tendsto _) _ tendsto_id _ <;> byCases' H : x = 0
    ·
      simp only [H, zero_ne_top, Ne.def, or_trueₓ, not_false_iff]
    ·
      exact Or.inl fun h => H (pow_eq_zero h)
    ·
      simp only [H, pow_eq_top_iff, zero_ne_top, false_orₓ, eq_self_iff_true, not_true, Ne.def, not_false_iff,
        false_andₓ]
    ·
      simp only [H, true_orₓ, Ne.def, not_false_iff]

protected theorem tendsto.pow {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} {n : ℕ} (hm : tendsto m f (𝓝 a)) :
  tendsto (fun x => m x ^ n) f (𝓝 (a ^ n)) :=
  ((continuous_pow n).Tendsto a).comp hm

-- error in Topology.Instances.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem le_of_forall_lt_one_mul_le
{x y : «exprℝ≥0∞»()}
(h : ∀ a «expr < » 1, «expr ≤ »(«expr * »(a, x), y)) : «expr ≤ »(x, y) :=
begin
  have [] [":", expr tendsto ((«expr * » x)) «expr𝓝[ ] »(Iio 1, 1) (expr𝓝() «expr * »(1, x))] [":=", expr (ennreal.continuous_at_mul_const (or.inr one_ne_zero)).mono_left inf_le_left],
  rw [expr one_mul] ["at", ident this],
  haveI [] [":", expr «expr𝓝[ ] »(Iio 1, (1 : «exprℝ≥0∞»())).ne_bot] [":=", expr nhds_within_Iio_self_ne_bot' ennreal.zero_lt_one],
  exact [expr le_of_tendsto this «expr $ »(eventually_nhds_within_iff.2, eventually_of_forall h)]
end

theorem infi_mul_left' {ι} {f : ι → ℝ≥0∞} {a : ℝ≥0∞} (h : a = ⊤ → (⨅i, f i) = 0 → ∃ i, f i = 0)
  (h0 : a = 0 → Nonempty ι) : (⨅i, a*f i) = a*⨅i, f i :=
  by 
    byCases' H : a = ⊤ ∧ (⨅i, f i) = 0
    ·
      rcases h H.1 H.2 with ⟨i, hi⟩
      rw [H.2, mul_zero, ←bot_eq_zero, infi_eq_bot]
      exact
        fun b hb =>
          ⟨i,
            by 
              rwa [hi, mul_zero, ←bot_eq_zero]⟩
    ·
      rw [not_and_distrib] at H 
      cases' is_empty_or_nonempty ι
      ·
        rw [infi_of_empty, infi_of_empty, mul_top, if_neg]
        exact mt h0 (not_nonempty_iff.2 ‹_›)
      ·
        exact (map_infi_of_continuous_at_of_monotone' (Ennreal.continuous_at_const_mul H) Ennreal.mul_left_mono).symm

theorem infi_mul_left {ι} [Nonempty ι] {f : ι → ℝ≥0∞} {a : ℝ≥0∞} (h : a = ⊤ → (⨅i, f i) = 0 → ∃ i, f i = 0) :
  (⨅i, a*f i) = a*⨅i, f i :=
  infi_mul_left' h fun _ => ‹Nonempty ι›

theorem infi_mul_right' {ι} {f : ι → ℝ≥0∞} {a : ℝ≥0∞} (h : a = ⊤ → (⨅i, f i) = 0 → ∃ i, f i = 0)
  (h0 : a = 0 → Nonempty ι) : (⨅i, f i*a) = (⨅i, f i)*a :=
  by 
    simpa only [mul_commₓ a] using infi_mul_left' h h0

theorem infi_mul_right {ι} [Nonempty ι] {f : ι → ℝ≥0∞} {a : ℝ≥0∞} (h : a = ⊤ → (⨅i, f i) = 0 → ∃ i, f i = 0) :
  (⨅i, f i*a) = (⨅i, f i)*a :=
  infi_mul_right' h fun _ => ‹Nonempty ι›

protected theorem continuous_inv : Continuous (HasInv.inv : ℝ≥0∞ → ℝ≥0∞) :=
  continuous_iff_continuous_at.2$
    fun a =>
      tendsto_order.2
        ⟨by 
            intro b hb 
            simp only [@Ennreal.lt_inv_iff_lt_inv b]
            exact gt_mem_nhds (Ennreal.lt_inv_iff_lt_inv.1 hb),
          by 
            intro b hb 
            simp only [gt_iff_lt, @Ennreal.inv_lt_iff_inv_lt _ b]
            exact lt_mem_nhds (Ennreal.inv_lt_iff_inv_lt.1 hb)⟩

@[simp]
protected theorem tendsto_inv_iff {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} :
  tendsto (fun x => m x⁻¹) f (𝓝 (a⁻¹)) ↔ tendsto m f (𝓝 a) :=
  ⟨fun h =>
      by 
        simpa only [Function.comp, Ennreal.inv_inv] using (ennreal.continuous_inv.tendsto (a⁻¹)).comp h,
    (Ennreal.continuous_inv.Tendsto a).comp⟩

protected theorem tendsto.div {f : Filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞} (hma : tendsto ma f (𝓝 a))
  (ha : a ≠ 0 ∨ b ≠ 0) (hmb : tendsto mb f (𝓝 b)) (hb : b ≠ ⊤ ∨ a ≠ ⊤) : tendsto (fun a => ma a / mb a) f (𝓝 (a / b)) :=
  by 
    apply tendsto.mul hma _ (Ennreal.tendsto_inv_iff.2 hmb) _ <;> simp [ha, hb]

protected theorem tendsto.const_div {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞} (hm : tendsto m f (𝓝 b))
  (hb : b ≠ ⊤ ∨ a ≠ ⊤) : tendsto (fun b => a / m b) f (𝓝 (a / b)) :=
  by 
    apply tendsto.const_mul (Ennreal.tendsto_inv_iff.2 hm)
    simp [hb]

protected theorem tendsto.div_const {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞} (hm : tendsto m f (𝓝 a))
  (ha : a ≠ 0 ∨ b ≠ 0) : tendsto (fun x => m x / b) f (𝓝 (a / b)) :=
  by 
    apply tendsto.mul_const hm 
    simp [ha]

protected theorem tendsto_inv_nat_nhds_zero : tendsto (fun n : ℕ => (n : ℝ≥0∞)⁻¹) at_top (𝓝 0) :=
  Ennreal.inv_top ▸ Ennreal.tendsto_inv_iff.2 tendsto_nat_nhds_top

theorem bsupr_add {ι} {s : Set ι} (hs : s.nonempty) {f : ι → ℝ≥0∞} :
  ((⨆(i : _)(_ : i ∈ s), f i)+a) = ⨆(i : _)(_ : i ∈ s), f i+a :=
  by 
    simp only [←Sup_image]
    symm 
    rw [image_comp (·+a)]
    refine' IsLub.Sup_eq ((is_lub_Sup$ f '' s).is_lub_of_tendsto _ (hs.image _) _)
    exacts[fun x _ y _ hxy => add_le_add hxy le_rfl, tendsto.add (tendsto_id' inf_le_left) tendsto_const_nhds]

theorem Sup_add {s : Set ℝ≥0∞} (hs : s.nonempty) : (Sup s+a) = ⨆(b : _)(_ : b ∈ s), b+a :=
  by 
    rw [Sup_eq_supr, bsupr_add hs]

theorem supr_add {ι : Sort _} {s : ι → ℝ≥0∞} [h : Nonempty ι] : (supr s+a) = ⨆b, s b+a :=
  let ⟨x⟩ := h 
  calc (supr s+a) = Sup (range s)+a :=
    by 
      rw [Sup_range]
    _ = ⨆(b : _)(_ : b ∈ range s), b+a := Sup_add ⟨s x, x, rfl⟩
    _ = _ := supr_range
    

theorem add_supr {ι : Sort _} {s : ι → ℝ≥0∞} [h : Nonempty ι] : (a+supr s) = ⨆b, a+s b :=
  by 
    rw [add_commₓ, supr_add] <;> simp [add_commₓ]

-- error in Topology.Instances.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem supr_add_supr
{ι : Sort*}
{f g : ι → «exprℝ≥0∞»()}
(h : ∀
 i
 j, «expr∃ , »((k), «expr ≤ »(«expr + »(f i, g j), «expr + »(f k, g k)))) : «expr = »(«expr + »(supr f, supr g), «expr⨆ , »((a), «expr + »(f a, g a))) :=
begin
  by_cases [expr hι, ":", expr nonempty ι],
  { letI [] [] [":=", expr hι],
    refine [expr le_antisymm _ «expr $ »(supr_le, λ a, add_le_add (le_supr _ _) (le_supr _ _))],
    simpa [] [] [] ["[", expr add_supr, ",", expr supr_add, "]"] [] ["using", expr λ
     i j : ι, show «expr ≤ »(«expr + »(f i, g j), «expr⨆ , »((a), «expr + »(f a, g a))), from let ⟨k, hk⟩ := h i j in
     le_supr_of_le k hk] },
  { have [] [":", expr ∀
     f : ι → «exprℝ≥0∞»(), «expr = »(«expr⨆ , »((i), f i), 0)] [":=", expr λ f, supr_eq_zero.mpr (λ i, (hι ⟨i⟩).elim)],
    rw ["[", expr this, ",", expr this, ",", expr this, ",", expr zero_add, "]"] [] }
end

theorem supr_add_supr_of_monotone {ι : Sort _} [SemilatticeSup ι] {f g : ι → ℝ≥0∞} (hf : Monotone f) (hg : Monotone g) :
  (supr f+supr g) = ⨆a, f a+g a :=
  supr_add_supr$ fun i j => ⟨i⊔j, add_le_add (hf$ le_sup_left) (hg$ le_sup_right)⟩

theorem finset_sum_supr_nat {α} {ι} [SemilatticeSup ι] {s : Finset α} {f : α → ι → ℝ≥0∞} (hf : ∀ a, Monotone (f a)) :
  (∑a in s, supr (f a)) = ⨆n, ∑a in s, f a n :=
  by 
    refine' Finset.induction_on s _ _
    ·
      simp 
    ·
      intro a s has ih 
      simp only [Finset.sum_insert has]
      rw [ih, supr_add_supr_of_monotone (hf a)]
      intro i j h 
      exact Finset.sum_le_sum$ fun a ha => hf a h

-- error in Topology.Instances.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mul_Sup
{s : set «exprℝ≥0∞»()}
{a : «exprℝ≥0∞»()} : «expr = »(«expr * »(a, Sup s), «expr⨆ , »((i «expr ∈ » s), «expr * »(a, i))) :=
begin
  by_cases [expr hs, ":", expr ∀ x «expr ∈ » s, «expr = »(x, (0 : «exprℝ≥0∞»()))],
  { have [ident h₁] [":", expr «expr = »(Sup s, 0)] [":=", expr «expr $ »(bot_unique, «expr $ »(Sup_le, assume
       a ha, «expr ▸ »((hs a ha).symm, le_refl 0)))],
    have [ident h₂] [":", expr «expr = »(«expr⨆ , »((i «expr ∈ » s), «expr * »(a, i)), 0)] [":=", expr «expr $ »(bot_unique, «expr $ »(supr_le, assume
       a, «expr $ »(supr_le, assume ha, by simp [] [] [] ["[", expr hs a ha, "]"] [] [])))],
    rw ["[", expr h₁, ",", expr h₂, ",", expr mul_zero, "]"] [] },
  { simp [] [] ["only"] ["[", expr not_forall, "]"] [] ["at", ident hs],
    rcases [expr hs, "with", "⟨", ident x, ",", ident hx, ",", ident hx0, "⟩"],
    have [ident s₁] [":", expr «expr ≠ »(Sup s, 0)] [":=", expr pos_iff_ne_zero.1 (lt_of_lt_of_le (pos_iff_ne_zero.2 hx0) (le_Sup hx))],
    have [] [":", expr «expr = »(Sup «expr '' »(λ
       b, «expr * »(a, b), s), «expr * »(a, Sup s))] [":=", expr is_lub.Sup_eq ((is_lub_Sup s).is_lub_of_tendsto (assume
       x _ y _ h, mul_le_mul_left' h _) ⟨x, hx⟩ (ennreal.tendsto.const_mul (tendsto_id' inf_le_left) (or.inl s₁)))],
    rw ["[", expr this.symm, ",", expr Sup_image, "]"] [] }
end

theorem mul_supr {ι : Sort _} {f : ι → ℝ≥0∞} {a : ℝ≥0∞} : (a*supr f) = ⨆i, a*f i :=
  by 
    rw [←Sup_range, mul_Sup, supr_range]

theorem supr_mul {ι : Sort _} {f : ι → ℝ≥0∞} {a : ℝ≥0∞} : (supr f*a) = ⨆i, f i*a :=
  by 
    rw [mul_commₓ, mul_supr] <;> congr <;> funext  <;> rw [mul_commₓ]

theorem supr_div {ι : Sort _} {f : ι → ℝ≥0∞} {a : ℝ≥0∞} : supr f / a = ⨆i, f i / a :=
  supr_mul

-- error in Topology.Instances.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem tendsto_coe_sub : ∀
{b : «exprℝ≥0∞»()}, tendsto (λ
 b : «exprℝ≥0∞»(), «expr - »(«expr↑ »(r), b)) (expr𝓝() b) (expr𝓝() «expr - »(«expr↑ »(r), b)) :=
begin
  refine [expr forall_ennreal.2 ⟨λ a, _, _⟩],
  { simp [] [] [] ["[", expr @nhds_coe a, ",", expr tendsto_map'_iff, ",", expr («expr ∘ »), ",", expr tendsto_coe, ",", "<-", expr with_top.coe_sub, "]"] [] [],
    exact [expr tendsto_const_nhds.sub tendsto_id] },
  simp [] [] [] [] [] [],
  exact [expr tendsto.congr' «expr $ »(mem_of_superset «expr $ »(lt_mem_nhds, @coe_lt_top r), by simp [] [] [] ["[", expr le_of_lt, "]"] [] [] { contextual := tt }) tendsto_const_nhds]
end

theorem sub_supr {ι : Sort _} [Nonempty ι] {b : ι → ℝ≥0∞} (hr : a < ⊤) : (a - ⨆i, b i) = ⨅i, a - b i :=
  let ⟨r, Eq, _⟩ := lt_iff_exists_coe.mp hr 
  have  : Inf ((fun b => «expr↑ » r - b) '' range b) = «expr↑ » r - ⨆i, b i :=
    IsGlb.Inf_eq$
      is_lub_supr.is_glb_of_tendsto (fun x _ y _ => tsub_le_tsub (le_reflₓ (r : ℝ≥0∞))) (range_nonempty _)
        (Ennreal.tendsto_coe_sub.comp (tendsto_id' inf_le_left))
  by 
    rw [Eq, ←this] <;> simp [Inf_image, infi_range, -mem_range] <;> exact le_rfl

theorem exists_countable_dense_no_zero_top : ∃ s : Set ℝ≥0∞, countable s ∧ Dense s ∧ 0 ∉ s ∧ ∞ ∉ s :=
  by 
    obtain ⟨s, s_count, s_dense, hs⟩ :
      ∃ s : Set ℝ≥0∞, countable s ∧ Dense s ∧ (∀ x, IsBot x → x ∉ s) ∧ ∀ x, IsTop x → x ∉ s :=
      exists_countable_dense_no_bot_top ℝ≥0∞
    exact
      ⟨s, s_count, s_dense,
        fun h =>
          hs.1 0
            (by 
              simp )
            h,
        fun h =>
          hs.2 ∞
            (by 
              simp )
            h⟩

end TopologicalSpace

section tsum

variable {f g : α → ℝ≥0∞}

@[normCast]
protected theorem has_sum_coe {f : α →  ℝ≥0 } {r :  ℝ≥0 } : HasSum (fun a => (f a : ℝ≥0∞)) («expr↑ » r) ↔ HasSum f r :=
  have  : (fun s : Finset α => ∑a in s, «expr↑ » (f a)) = ((coeₓ :  ℝ≥0  → ℝ≥0∞) ∘ fun s : Finset α => ∑a in s, f a) :=
    funext$ fun s => Ennreal.coe_finset_sum.symm 
  by 
    unfold HasSum <;> rw [this, tendsto_coe]

protected theorem tsum_coe_eq {f : α →  ℝ≥0 } (h : HasSum f r) : (∑'a, (f a : ℝ≥0∞)) = r :=
  (Ennreal.has_sum_coe.2 h).tsum_eq

protected theorem coe_tsum {f : α →  ℝ≥0 } : Summable f → «expr↑ » (tsum f) = ∑'a, (f a : ℝ≥0∞)
| ⟨r, hr⟩ =>
  by 
    rw [hr.tsum_eq, Ennreal.tsum_coe_eq hr]

protected theorem HasSum : HasSum f (⨆s : Finset α, ∑a in s, f a) :=
  tendsto_at_top_supr$ fun s t => Finset.sum_le_sum_of_subset

@[simp]
protected theorem Summable : Summable f :=
  ⟨_, Ennreal.has_sum⟩

theorem tsum_coe_ne_top_iff_summable {f : β →  ℝ≥0 } : (∑'b, (f b : ℝ≥0∞)) ≠ ∞ ↔ Summable f :=
  by 
    refine' ⟨fun h => _, fun h => Ennreal.coe_tsum h ▸ Ennreal.coe_ne_top⟩
    lift ∑'b, (f b : ℝ≥0∞) to  ℝ≥0  using h with a ha 
    refine' ⟨a, Ennreal.has_sum_coe.1 _⟩
    rw [ha]
    exact ennreal.summable.has_sum

protected theorem tsum_eq_supr_sum : (∑'a, f a) = ⨆s : Finset α, ∑a in s, f a :=
  Ennreal.has_sum.tsum_eq

protected theorem tsum_eq_supr_sum' {ι : Type _} (s : ι → Finset α) (hs : ∀ t, ∃ i, t ⊆ s i) :
  (∑'a, f a) = ⨆i, ∑a in s i, f a :=
  by 
    rw [Ennreal.tsum_eq_supr_sum]
    symm 
    change (⨆i : ι, (fun t : Finset α => ∑a in t, f a) (s i)) = ⨆s : Finset α, ∑a in s, f a 
    exact (Finset.sum_mono_set f).supr_comp_eq hs

protected theorem tsum_sigma {β : α → Type _} (f : ∀ a, β a → ℝ≥0∞) : (∑'p : Σa, β a, f p.1 p.2) = ∑'a b, f a b :=
  tsum_sigma' (fun b => Ennreal.summable) Ennreal.summable

protected theorem tsum_sigma' {β : α → Type _} (f : (Σa, β a) → ℝ≥0∞) : (∑'p : Σa, β a, f p) = ∑'a b, f ⟨a, b⟩ :=
  tsum_sigma' (fun b => Ennreal.summable) Ennreal.summable

protected theorem tsum_prod {f : α → β → ℝ≥0∞} : (∑'p : α × β, f p.1 p.2) = ∑'a, ∑'b, f a b :=
  tsum_prod' Ennreal.summable$ fun _ => Ennreal.summable

protected theorem tsum_comm {f : α → β → ℝ≥0∞} : (∑'a, ∑'b, f a b) = ∑'b, ∑'a, f a b :=
  tsum_comm' Ennreal.summable (fun _ => Ennreal.summable) fun _ => Ennreal.summable

protected theorem tsum_add : (∑'a, f a+g a) = (∑'a, f a)+∑'a, g a :=
  tsum_add Ennreal.summable Ennreal.summable

protected theorem tsum_le_tsum (h : ∀ a, f a ≤ g a) : (∑'a, f a) ≤ ∑'a, g a :=
  tsum_le_tsum h Ennreal.summable Ennreal.summable

protected theorem sum_le_tsum {f : α → ℝ≥0∞} (s : Finset α) : (∑x in s, f x) ≤ ∑'x, f x :=
  sum_le_tsum s (fun x hx => zero_le _) Ennreal.summable

protected theorem tsum_eq_supr_nat' {f : ℕ → ℝ≥0∞} {N : ℕ → ℕ} (hN : tendsto N at_top at_top) :
  (∑'i : ℕ, f i) = ⨆i : ℕ, ∑a in Finset.range (N i), f a :=
  Ennreal.tsum_eq_supr_sum' _$
    fun t =>
      let ⟨n, hn⟩ := t.exists_nat_subset_range 
      let ⟨k, _, hk⟩ := exists_le_of_tendsto_at_top hN 0 n
      ⟨k, Finset.Subset.trans hn (Finset.range_mono hk)⟩

protected theorem tsum_eq_supr_nat {f : ℕ → ℝ≥0∞} : (∑'i : ℕ, f i) = ⨆i : ℕ, ∑a in Finset.range i, f a :=
  Ennreal.tsum_eq_supr_sum' _ Finset.exists_nat_subset_range

protected theorem tsum_eq_liminf_sum_nat {f : ℕ → ℝ≥0∞} :
  (∑'i, f i) = Filter.atTop.liminf fun n => ∑i in Finset.range n, f i :=
  by 
    rw [Ennreal.tsum_eq_supr_nat, Filter.liminf_eq_supr_infi_of_nat]
    congr 
    refine' funext fun n => le_antisymmₓ _ _
    ·
      refine' le_binfi fun i hi => Finset.sum_le_sum_of_subset_of_nonneg _ fun _ _ _ => zero_le _ 
      simpa only [Finset.range_subset, add_le_add_iff_right] using hi
    ·
      refine' le_transₓ (infi_le _ n) _ 
      simp [le_reflₓ n, le_reflₓ ((Finset.range n).Sum f)]

protected theorem le_tsum (a : α) : f a ≤ ∑'a, f a :=
  le_tsum' Ennreal.summable a

@[simp]
protected theorem tsum_eq_zero : (∑'i, f i) = 0 ↔ ∀ i, f i = 0 :=
  ⟨fun h i => nonpos_iff_eq_zero.1$ h ▸ Ennreal.le_tsum i,
    fun h =>
      by 
        simp [h]⟩

protected theorem tsum_eq_top_of_eq_top : (∃ a, f a = ∞) → (∑'a, f a) = ∞
| ⟨a, ha⟩ => top_unique$ ha ▸ Ennreal.le_tsum a

@[simp]
protected theorem tsum_top [Nonempty α] : (∑'a : α, ∞) = ∞ :=
  let ⟨a⟩ := ‹Nonempty α›
  Ennreal.tsum_eq_top_of_eq_top ⟨a, rfl⟩

-- error in Topology.Instances.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tsum_const_eq_top_of_ne_zero
{α : Type*}
[infinite α]
{c : «exprℝ≥0∞»()}
(hc : «expr ≠ »(c, 0)) : «expr = »(«expr∑' , »((a : α), c), «expr∞»()) :=
begin
  have [ident A] [":", expr tendsto (λ
    n : exprℕ(), «expr * »((n : «exprℝ≥0∞»()), c)) at_top (expr𝓝() «expr * »(«expr∞»(), c))] [],
  { apply [expr ennreal.tendsto.mul_const tendsto_nat_nhds_top],
    simp [] [] ["only"] ["[", expr true_or, ",", expr top_ne_zero, ",", expr ne.def, ",", expr not_false_iff, "]"] [] [] },
  have [ident B] [":", expr ∀ n : exprℕ(), «expr ≤ »(«expr * »((n : «exprℝ≥0∞»()), c), «expr∑' , »((a : α), c))] [],
  { assume [binders (n)],
    rcases [expr infinite.exists_subset_card_eq α n, "with", "⟨", ident s, ",", ident hs, "⟩"],
    simpa [] [] [] ["[", expr hs, "]"] [] ["using", expr @ennreal.sum_le_tsum α (λ i, c) s] },
  simpa [] [] [] ["[", expr hc, "]"] [] ["using", expr le_of_tendsto' A B]
end

protected theorem ne_top_of_tsum_ne_top (h : (∑'a, f a) ≠ ∞) (a : α) : f a ≠ ∞ :=
  fun ha => h$ Ennreal.tsum_eq_top_of_eq_top ⟨a, ha⟩

protected theorem tsum_mul_left : (∑'i, a*f i) = a*∑'i, f i :=
  if h : ∀ i, f i = 0 then
    by 
      simp [h]
  else
    let ⟨i, (hi : f i ≠ 0)⟩ := not_forall.mp h 
    have sum_ne_0 : (∑'i, f i) ≠ 0 :=
      ne_of_gtₓ$
        calc 0 < f i := lt_of_le_of_neₓ (zero_le _) hi.symm 
          _ ≤ ∑'i, f i := Ennreal.le_tsum _ 
          
    have  : tendsto (fun s : Finset α => ∑j in s, a*f j) at_top (𝓝 (a*∑'i, f i)) :=
      by 
        rw
            [←show ((·*·) a ∘ fun s : Finset α => ∑j in s, f j) = fun s => ∑j in s, a*f j from
              funext$ fun s => Finset.mul_sum] <;>
          exact Ennreal.Tendsto.const_mul ennreal.summable.has_sum (Or.inl sum_ne_0)
    HasSum.tsum_eq this

protected theorem tsum_mul_right : (∑'i, f i*a) = (∑'i, f i)*a :=
  by 
    simp [mul_commₓ, Ennreal.tsum_mul_left]

@[simp]
theorem tsum_supr_eq {α : Type _} (a : α) {f : α → ℝ≥0∞} : (∑'b : α, ⨆h : a = b, f b) = f a :=
  le_antisymmₓ
    (by 
      rw [Ennreal.tsum_eq_supr_sum] <;>
        exact
          supr_le
            fun s =>
              calc (∑b in s, ⨆h : a = b, f b) ≤ ∑b in {a}, ⨆h : a = b, f b :=
                Finset.sum_le_sum_of_ne_zero$
                  fun b _ hb =>
                    suffices a = b by 
                      simpa using this.symm 
                    Classical.by_contradiction$
                      fun h =>
                        by 
                          simpa [h] using hb 
                _ = f a :=
                by 
                  simp 
                )
    (calc f a ≤ ⨆h : a = a, f a := le_supr (fun h : a = a => f a) rfl 
      _ ≤ ∑'b : α, ⨆h : a = b, f b := Ennreal.le_tsum _
      )

theorem has_sum_iff_tendsto_nat {f : ℕ → ℝ≥0∞} (r : ℝ≥0∞) :
  HasSum f r ↔ tendsto (fun n : ℕ => ∑i in Finset.range n, f i) at_top (𝓝 r) :=
  by 
    refine' ⟨HasSum.tendsto_sum_nat, fun h => _⟩
    rw [←supr_eq_of_tendsto _ h, ←Ennreal.tsum_eq_supr_nat]
    ·
      exact ennreal.summable.has_sum
    ·
      exact fun s t hst => Finset.sum_le_sum_of_subset (Finset.range_subset.2 hst)

theorem tendsto_nat_tsum (f : ℕ → ℝ≥0∞) : tendsto (fun n : ℕ => ∑i in Finset.range n, f i) at_top (𝓝 (∑'n, f n)) :=
  by 
    rw [←has_sum_iff_tendsto_nat]
    exact ennreal.summable.has_sum

theorem to_nnreal_apply_of_tsum_ne_top {α : Type _} {f : α → ℝ≥0∞} (hf : (∑'i, f i) ≠ ∞) (x : α) :
  (((Ennreal.toNnreal ∘ f) x :  ℝ≥0 ) : ℝ≥0∞) = f x :=
  coe_to_nnreal$ Ennreal.ne_top_of_tsum_ne_top hf _

theorem summable_to_nnreal_of_tsum_ne_top {α : Type _} {f : α → ℝ≥0∞} (hf : (∑'i, f i) ≠ ∞) :
  Summable (Ennreal.toNnreal ∘ f) :=
  by 
    simpa only [←tsum_coe_ne_top_iff_summable, to_nnreal_apply_of_tsum_ne_top hf] using hf

-- error in Topology.Instances.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tendsto_cofinite_zero_of_tsum_ne_top
{α}
{f : α → «exprℝ≥0∞»()}
(hf : «expr ≠ »(«expr∑' , »((x), f x), «expr∞»())) : tendsto f cofinite (expr𝓝() 0) :=
begin
  have [ident f_ne_top] [":", expr ∀ n, «expr ≠ »(f n, «expr∞»())] [],
  from [expr ennreal.ne_top_of_tsum_ne_top hf],
  have [ident h_f_coe] [":", expr «expr = »(f, λ n, ((f n).to_nnreal : ennreal))] [],
  from [expr funext (λ n, (coe_to_nnreal (f_ne_top n)).symm)],
  rw ["[", expr h_f_coe, ",", "<-", expr @coe_zero, ",", expr tendsto_coe, "]"] [],
  exact [expr nnreal.tendsto_cofinite_zero_of_summable (summable_to_nnreal_of_tsum_ne_top hf)]
end

theorem tendsto_at_top_zero_of_tsum_ne_top {f : ℕ → ℝ≥0∞} (hf : (∑'x, f x) ≠ ∞) : tendsto f at_top (𝓝 0) :=
  by 
    rw [←Nat.cofinite_eq_at_top]
    exact tendsto_cofinite_zero_of_tsum_ne_top hf

/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
theorem tendsto_tsum_compl_at_top_zero {α : Type _} {f : α → ℝ≥0∞} (hf : (∑'x, f x) ≠ ∞) :
  tendsto (fun s : Finset α => ∑'b : { x // x ∉ s }, f b) at_top (𝓝 0) :=
  by 
    lift f to α →  ℝ≥0  using Ennreal.ne_top_of_tsum_ne_top hf 
    convert Ennreal.tendsto_coe.2 (Nnreal.tendsto_tsum_compl_at_top_zero f)
    ext1 s 
    rw [Ennreal.coe_tsum]
    exact Nnreal.summable_comp_injective (tsum_coe_ne_top_iff_summable.1 hf) Subtype.coe_injective

protected theorem tsum_apply {ι α : Type _} {f : ι → α → ℝ≥0∞} {x : α} : (∑'i, f i) x = ∑'i, f i x :=
  tsum_apply$ Pi.summable.mpr$ fun _ => Ennreal.summable

-- error in Topology.Instances.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tsum_sub
{f : exprℕ() → «exprℝ≥0∞»()}
{g : exprℕ() → «exprℝ≥0∞»()}
(h₁ : «expr ≠ »(«expr∑' , »((i), g i), «expr∞»()))
(h₂ : «expr ≤ »(g, f)) : «expr = »(«expr∑' , »((i), «expr - »(f i, g i)), «expr - »(«expr∑' , »((i), f i), «expr∑' , »((i), g i))) :=
begin
  have [ident h₃] [":", expr «expr = »(«expr∑' , »((i), «expr - »(f i, g i)), «expr - »(«expr∑' , »((i), «expr + »(«expr - »(f i, g i), g i)), «expr∑' , »((i), g i)))] [],
  { rw ["[", expr ennreal.tsum_add, ",", expr add_sub_self h₁, "]"] [] },
  have [ident h₄] [":", expr «expr = »(λ i, «expr + »(«expr - »(f i, g i), g i), f)] [],
  { ext [] [ident n] [],
    rw [expr tsub_add_cancel_of_le (h₂ n)] [] },
  rw [expr h₄] ["at", ident h₃],
  apply [expr h₃]
end

end tsum

-- error in Topology.Instances.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tendsto_to_real_iff
{ι}
{fi : filter ι}
{f : ι → «exprℝ≥0∞»()}
(hf : ∀ i, «expr ≠ »(f i, «expr∞»()))
{x : «exprℝ≥0∞»()}
(hx : «expr ≠ »(x, «expr∞»())) : «expr ↔ »(fi.tendsto (λ
  n, (f n).to_real) (expr𝓝() x.to_real), fi.tendsto f (expr𝓝() x)) :=
begin
  refine [expr ⟨λ h, _, λ h, tendsto.comp (ennreal.tendsto_to_real hx) h⟩],
  have [ident h_eq] [":", expr «expr = »(f, λ n, ennreal.of_real (f n).to_real)] [],
  by { ext1 [] [ident n],
    rw [expr ennreal.of_real_to_real (hf n)] [] },
  rw ["[", expr h_eq, ",", "<-", expr ennreal.of_real_to_real hx, "]"] [],
  exact [expr ennreal.tendsto_of_real h]
end

theorem tsum_coe_ne_top_iff_summable_coe {f : α →  ℝ≥0 } : (∑'a, (f a : ℝ≥0∞)) ≠ ∞ ↔ Summable fun a => (f a : ℝ) :=
  by 
    rw [Nnreal.summable_coe]
    exact tsum_coe_ne_top_iff_summable

theorem tsum_coe_eq_top_iff_not_summable_coe {f : α →  ℝ≥0 } : (∑'a, (f a : ℝ≥0∞)) = ∞ ↔ ¬Summable fun a => (f a : ℝ) :=
  by 
    rw [←@not_not ((∑'a, «expr↑ » (f a)) = ⊤)]
    exact not_congr tsum_coe_ne_top_iff_summable_coe

theorem summable_to_real {f : α → ℝ≥0∞} (hsum : (∑'x, f x) ≠ ∞) : Summable fun x => (f x).toReal :=
  by 
    lift f to α →  ℝ≥0  using Ennreal.ne_top_of_tsum_ne_top hsum 
    rwa [Ennreal.tsum_coe_ne_top_iff_summable_coe] at hsum

end Ennreal

namespace Nnreal

open_locale Nnreal

-- error in Topology.Instances.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tsum_eq_to_nnreal_tsum
{f : β → «exprℝ≥0»()} : «expr = »(«expr∑' , »((b), f b), «expr∑' , »((b), (f b : «exprℝ≥0∞»())).to_nnreal) :=
begin
  by_cases [expr h, ":", expr summable f],
  { rw ["[", "<-", expr ennreal.coe_tsum h, ",", expr ennreal.to_nnreal_coe, "]"] [] },
  { have [ident A] [] [":=", expr tsum_eq_zero_of_not_summable h],
    simp [] [] ["only"] ["[", "<-", expr ennreal.tsum_coe_ne_top_iff_summable, ",", expr not_not, "]"] [] ["at", ident h],
    simp [] [] ["only"] ["[", expr h, ",", expr ennreal.top_to_nnreal, ",", expr A, "]"] [] [] }
end

/-- Comparison test of convergence of `ℝ≥0`-valued series. -/
theorem exists_le_has_sum_of_le {f g : β →  ℝ≥0 } {r :  ℝ≥0 } (hgf : ∀ b, g b ≤ f b) (hfr : HasSum f r) :
  ∃ (p : _)(_ : p ≤ r), HasSum g p :=
  have  : (∑'b, (g b : ℝ≥0∞)) ≤ r :=
    by 
      refine' has_sum_le (fun b => _) ennreal.summable.has_sum (Ennreal.has_sum_coe.2 hfr)
      exact Ennreal.coe_le_coe.2 (hgf _)
  let ⟨p, Eq, hpr⟩ := Ennreal.le_coe_iff.1 this
  ⟨p, hpr, Ennreal.has_sum_coe.1$ Eq ▸ Ennreal.summable.HasSum⟩

/-- Comparison test of convergence of `ℝ≥0`-valued series. -/
theorem summable_of_le {f g : β →  ℝ≥0 } (hgf : ∀ b, g b ≤ f b) : Summable f → Summable g
| ⟨r, hfr⟩ =>
  let ⟨p, _, hp⟩ := exists_le_has_sum_of_le hgf hfr 
  hp.summable

/-- A series of non-negative real numbers converges to `r` in the sense of `has_sum` if and only if
the sequence of partial sum converges to `r`. -/
theorem has_sum_iff_tendsto_nat {f : ℕ →  ℝ≥0 } {r :  ℝ≥0 } :
  HasSum f r ↔ tendsto (fun n : ℕ => ∑i in Finset.range n, f i) at_top (𝓝 r) :=
  by 
    rw [←Ennreal.has_sum_coe, Ennreal.has_sum_iff_tendsto_nat]
    simp only [ennreal.coe_finset_sum.symm]
    exact Ennreal.tendsto_coe

theorem not_summable_iff_tendsto_nat_at_top {f : ℕ →  ℝ≥0 } :
  ¬Summable f ↔ tendsto (fun n : ℕ => ∑i in Finset.range n, f i) at_top at_top :=
  by 
    split 
    ·
      intro h 
      refine' ((tendsto_of_monotone _).resolve_right h).comp _ 
      exacts[Finset.sum_mono_set _, tendsto_finset_range]
    ·
      rintro hnat ⟨r, hr⟩
      exact not_tendsto_nhds_of_tendsto_at_top hnat _ (has_sum_iff_tendsto_nat.1 hr)

theorem summable_iff_not_tendsto_nat_at_top {f : ℕ →  ℝ≥0 } :
  Summable f ↔ ¬tendsto (fun n : ℕ => ∑i in Finset.range n, f i) at_top at_top :=
  by 
    rw [←not_iff_not, not_not, not_summable_iff_tendsto_nat_at_top]

theorem summable_of_sum_range_le {f : ℕ →  ℝ≥0 } {c :  ℝ≥0 } (h : ∀ n, (∑i in Finset.range n, f i) ≤ c) : Summable f :=
  by 
    apply summable_iff_not_tendsto_nat_at_top.2 fun H => _ 
    rcases exists_lt_of_tendsto_at_top H 0 c with ⟨n, -, hn⟩
    exact lt_irreflₓ _ (hn.trans_le (h n))

theorem tsum_le_of_sum_range_le {f : ℕ →  ℝ≥0 } {c :  ℝ≥0 } (h : ∀ n, (∑i in Finset.range n, f i) ≤ c) :
  (∑'n, f n) ≤ c :=
  le_of_tendsto' (has_sum_iff_tendsto_nat.1 (summable_of_sum_range_le h).HasSum) h

theorem tsum_comp_le_tsum_of_inj {β : Type _} {f : α →  ℝ≥0 } (hf : Summable f) {i : β → α}
  (hi : Function.Injective i) : (∑'x, f (i x)) ≤ ∑'x, f x :=
  tsum_le_tsum_of_inj i hi (fun c hc => zero_le _) (fun b => le_reflₓ _) (summable_comp_injective hf hi) hf

theorem summable_sigma {β : ∀ x : α, Type _} {f : (Σx, β x) →  ℝ≥0 } :
  Summable f ↔ (∀ x, Summable fun y => f ⟨x, y⟩) ∧ Summable fun x => ∑'y, f ⟨x, y⟩ :=
  by 
    split 
    ·
      simp only [←Nnreal.summable_coe, Nnreal.coe_tsum]
      exact fun h => ⟨h.sigma_factor, h.sigma⟩
    ·
      rintro ⟨h₁, h₂⟩
      simpa only [←Ennreal.tsum_coe_ne_top_iff_summable, Ennreal.tsum_sigma', Ennreal.coe_tsum, h₁] using h₂

theorem indicator_summable {f : α →  ℝ≥0 } (hf : Summable f) (s : Set α) : Summable (s.indicator f) :=
  by 
    refine' Nnreal.summable_of_le (fun a => le_transₓ (le_of_eqₓ (s.indicator_apply f a)) _) hf 
    splitIfs 
    exact le_reflₓ (f a)
    exact zero_le_coe

theorem tsum_indicator_ne_zero {f : α →  ℝ≥0 } (hf : Summable f) {s : Set α} (h : ∃ (a : _)(_ : a ∈ s), f a ≠ 0) :
  (∑'x, (s.indicator f) x) ≠ 0 :=
  fun h' =>
    let ⟨a, ha, hap⟩ := h 
    hap
      (trans (Set.indicator_apply_eq_self.mpr (absurd ha)).symm (((tsum_eq_zero_iff (indicator_summable hf s)).1 h') a))

open Finset

/-- For `f : ℕ → ℝ≥0`, then `∑' k, f (k + i)` tends to zero. This does not require a summability
assumption on `f`, as otherwise all sums are zero. -/
theorem tendsto_sum_nat_add (f : ℕ →  ℝ≥0 ) : tendsto (fun i => ∑'k, f (k+i)) at_top (𝓝 0) :=
  by 
    rw [←tendsto_coe]
    convert tendsto_sum_nat_add fun i => (f i : ℝ)
    normCast

-- error in Topology.Instances.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_sum_lt
{f g : α → «exprℝ≥0»()}
{sf sg : «exprℝ≥0»()}
{i : α}
(h : ∀ a : α, «expr ≤ »(f a, g a))
(hi : «expr < »(f i, g i))
(hf : has_sum f sf)
(hg : has_sum g sg) : «expr < »(sf, sg) :=
begin
  have [ident A] [":", expr ∀ a : α, «expr ≤ »((f a : exprℝ()), g a)] [":=", expr λ a, nnreal.coe_le_coe.2 (h a)],
  have [] [":", expr «expr < »((sf : exprℝ()), sg)] [":=", expr has_sum_lt A (nnreal.coe_lt_coe.2 hi) (has_sum_coe.2 hf) (has_sum_coe.2 hg)],
  exact [expr nnreal.coe_lt_coe.1 this]
end

@[mono]
theorem has_sum_strict_mono {f g : α →  ℝ≥0 } {sf sg :  ℝ≥0 } (hf : HasSum f sf) (hg : HasSum g sg) (h : f < g) :
  sf < sg :=
  let ⟨hle, i, hi⟩ := Pi.lt_def.mp h 
  has_sum_lt hle hi hf hg

theorem tsum_lt_tsum {f g : α →  ℝ≥0 } {i : α} (h : ∀ a : α, f a ≤ g a) (hi : f i < g i) (hg : Summable g) :
  (∑'n, f n) < ∑'n, g n :=
  has_sum_lt h hi (summable_of_le h hg).HasSum hg.has_sum

@[mono]
theorem tsum_strict_mono {f g : α →  ℝ≥0 } (hg : Summable g) (h : f < g) : (∑'n, f n) < ∑'n, g n :=
  let ⟨hle, i, hi⟩ := Pi.lt_def.mp h 
  tsum_lt_tsum hle hi hg

theorem tsum_pos {g : α →  ℝ≥0 } (hg : Summable g) (i : α) (hi : 0 < g i) : 0 < ∑'b, g b :=
  by 
    rw [←tsum_zero]
    exact tsum_lt_tsum (fun a => zero_le _) hi hg

end Nnreal

namespace Ennreal

-- error in Topology.Instances.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tsum_to_real_eq
{f : α → «exprℝ≥0∞»()}
(hf : ∀ a, «expr ≠ »(f a, «expr∞»())) : «expr = »(«expr∑' , »((a), f a).to_real, «expr∑' , »((a), (f a).to_real)) :=
begin
  lift [expr f] ["to", expr α → «exprℝ≥0»()] ["using", expr hf] [],
  have [] [":", expr «expr = »(«expr∑' , »((a : α), (f a : «exprℝ≥0∞»())).to_real, («expr∑' , »((a : α), (f a : «exprℝ≥0∞»())).to_nnreal : «exprℝ≥0∞»()).to_real)] [],
  { rw ["[", expr ennreal.coe_to_real, "]"] [],
    refl },
  rw ["[", expr this, ",", "<-", expr nnreal.tsum_eq_to_nnreal_tsum, ",", expr ennreal.coe_to_real, "]"] [],
  exact [expr nnreal.coe_tsum]
end

theorem tendsto_sum_nat_add (f : ℕ → ℝ≥0∞) (hf : (∑'i, f i) ≠ ∞) : tendsto (fun i => ∑'k, f (k+i)) at_top (𝓝 0) :=
  by 
    lift f to ℕ →  ℝ≥0  using Ennreal.ne_top_of_tsum_ne_top hf 
    replace hf : Summable f := tsum_coe_ne_top_iff_summable.1 hf 
    simp only [←Ennreal.coe_tsum, Nnreal.summable_nat_add _ hf, ←Ennreal.coe_zero]
    exactModCast Nnreal.tendsto_sum_nat_add f

end Ennreal

theorem tsum_comp_le_tsum_of_inj {β : Type _} {f : α → ℝ} (hf : Summable f) (hn : ∀ a, 0 ≤ f a) {i : β → α}
  (hi : Function.Injective i) : tsum (f ∘ i) ≤ tsum f :=
  by 
    lift f to α →  ℝ≥0  using hn 
    rw [Nnreal.summable_coe] at hf 
    simpa only [· ∘ ·, ←Nnreal.coe_tsum] using Nnreal.tsum_comp_le_tsum_of_inj hf hi

/-- Comparison test of convergence of series of non-negative real numbers. -/
theorem summable_of_nonneg_of_le {f g : β → ℝ} (hg : ∀ b, 0 ≤ g b) (hgf : ∀ b, g b ≤ f b) (hf : Summable f) :
  Summable g :=
  by 
    lift f to β →  ℝ≥0  using fun b => (hg b).trans (hgf b)
    lift g to β →  ℝ≥0  using hg 
    rw [Nnreal.summable_coe] at hf⊢
    exact Nnreal.summable_of_le (fun b => Nnreal.coe_le_coe.1 (hgf b)) hf

/-- A series of non-negative real numbers converges to `r` in the sense of `has_sum` if and only if
the sequence of partial sum converges to `r`. -/
theorem has_sum_iff_tendsto_nat_of_nonneg {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) (r : ℝ) :
  HasSum f r ↔ tendsto (fun n : ℕ => ∑i in Finset.range n, f i) at_top (𝓝 r) :=
  by 
    lift f to ℕ →  ℝ≥0  using hf 
    simp only [HasSum, ←Nnreal.coe_sum, Nnreal.tendsto_coe']
    exact exists_congr fun hr => Nnreal.has_sum_iff_tendsto_nat

theorem Ennreal.of_real_tsum_of_nonneg {f : α → ℝ} (hf_nonneg : ∀ n, 0 ≤ f n) (hf : Summable f) :
  Ennreal.ofReal (∑'n, f n) = ∑'n, Ennreal.ofReal (f n) :=
  by 
    simpRw [Ennreal.ofReal, Ennreal.tsum_coe_eq (Nnreal.has_sum_of_real_of_nonneg hf_nonneg hf)]

theorem not_summable_iff_tendsto_nat_at_top_of_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
  ¬Summable f ↔ tendsto (fun n : ℕ => ∑i in Finset.range n, f i) at_top at_top :=
  by 
    lift f to ℕ →  ℝ≥0  using hf 
    exactModCast Nnreal.not_summable_iff_tendsto_nat_at_top

theorem summable_iff_not_tendsto_nat_at_top_of_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
  Summable f ↔ ¬tendsto (fun n : ℕ => ∑i in Finset.range n, f i) at_top at_top :=
  by 
    rw [←not_iff_not, not_not, not_summable_iff_tendsto_nat_at_top_of_nonneg hf]

theorem summable_sigma_of_nonneg {β : ∀ x : α, Type _} {f : (Σx, β x) → ℝ} (hf : ∀ x, 0 ≤ f x) :
  Summable f ↔ (∀ x, Summable fun y => f ⟨x, y⟩) ∧ Summable fun x => ∑'y, f ⟨x, y⟩ :=
  by 
    lift f to (Σx, β x) →  ℝ≥0  using hf 
    exactModCast Nnreal.summable_sigma

theorem summable_of_sum_le {ι : Type _} {f : ι → ℝ} {c : ℝ} (hf : 0 ≤ f) (h : ∀ u : Finset ι, (∑x in u, f x) ≤ c) :
  Summable f :=
  ⟨⨆u : Finset ι, ∑x in u, f x, tendsto_at_top_csupr (Finset.sum_mono_set_of_nonneg hf) ⟨c, fun y ⟨u, hu⟩ => hu ▸ h u⟩⟩

theorem summable_of_sum_range_le {f : ℕ → ℝ} {c : ℝ} (hf : ∀ n, 0 ≤ f n) (h : ∀ n, (∑i in Finset.range n, f i) ≤ c) :
  Summable f :=
  by 
    apply (summable_iff_not_tendsto_nat_at_top_of_nonneg hf).2 fun H => _ 
    rcases exists_lt_of_tendsto_at_top H 0 c with ⟨n, -, hn⟩
    exact lt_irreflₓ _ (hn.trans_le (h n))

theorem tsum_le_of_sum_range_le {f : ℕ → ℝ} {c : ℝ} (hf : ∀ n, 0 ≤ f n) (h : ∀ n, (∑i in Finset.range n, f i) ≤ c) :
  (∑'n, f n) ≤ c :=
  le_of_tendsto' ((has_sum_iff_tendsto_nat_of_nonneg hf _).1 (summable_of_sum_range_le hf h).HasSum) h

/-- If a sequence `f` with non-negative terms is dominated by a sequence `g` with summable
series and at least one term of `f` is strictly smaller than the corresponding term in `g`,
then the series of `f` is strictly smaller than the series of `g`. -/
theorem tsum_lt_tsum_of_nonneg {i : ℕ} {f g : ℕ → ℝ} (h0 : ∀ b : ℕ, 0 ≤ f b) (h : ∀ b : ℕ, f b ≤ g b) (hi : f i < g i)
  (hg : Summable g) : (∑'n, f n) < ∑'n, g n :=
  tsum_lt_tsum h hi (summable_of_nonneg_of_le h0 h hg) hg

section 

variable [EmetricSpace β]

open Ennreal Filter Emetric

/-- In an emetric ball, the distance between points is everywhere finite -/
theorem edist_ne_top_of_mem_ball {a : β} {r : ℝ≥0∞} (x y : ball a r) : edist x.1 y.1 ≠ ⊤ :=
  lt_top_iff_ne_top.1$
    calc edist x y ≤ edist a x+edist a y := edist_triangle_left x.1 y.1 a 
      _ < r+r :=
      by 
        rw [edist_comm a x, edist_comm a y] <;> exact add_lt_add x.2 y.2
      _ ≤ ⊤ := le_top
      

/-- Each ball in an extended metric space gives us a metric space, as the edist
is everywhere finite. -/
def metricSpaceEmetricBall (a : β) (r : ℝ≥0∞) : MetricSpace (ball a r) :=
  EmetricSpace.toMetricSpace edist_ne_top_of_mem_ball

attribute [local instance] metricSpaceEmetricBall

theorem nhds_eq_nhds_emetric_ball (a x : β) (r : ℝ≥0∞) (h : x ∈ ball a r) :
  𝓝 x = map (coeₓ : ball a r → β) (𝓝 ⟨x, h⟩) :=
  (map_nhds_subtype_coe_eq _$ IsOpen.mem_nhds Emetric.is_open_ball h).symm

end 

section 

variable [PseudoEmetricSpace α]

open Emetric

theorem tendsto_iff_edist_tendsto_0 {l : Filter β} {f : β → α} {y : α} :
  tendsto f l (𝓝 y) ↔ tendsto (fun x => edist (f x) y) l (𝓝 0) :=
  by 
    simp only [emetric.nhds_basis_eball.tendsto_right_iff, Emetric.mem_ball, @tendsto_order ℝ≥0∞ β _ _,
      forall_prop_of_false Ennreal.not_lt_zero, forall_const, true_andₓ]

-- error in Topology.Instances.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Yet another metric characterization of Cauchy sequences on integers. This one is often the
most efficient. -/
theorem emetric.cauchy_seq_iff_le_tendsto_0
[nonempty β]
[semilattice_sup β]
{s : β → α} : «expr ↔ »(cauchy_seq s, «expr∃ , »((b : β → «exprℝ≥0∞»()), «expr ∧ »(∀
   n m N : β, «expr ≤ »(N, n) → «expr ≤ »(N, m) → «expr ≤ »(edist (s n) (s m), b N), tendsto b at_top (expr𝓝() 0)))) :=
⟨begin
   assume [binders (hs)],
   rw [expr emetric.cauchy_seq_iff] ["at", ident hs],
   let [ident b] [] [":=", expr λ
    N, Sup «expr '' »(λ
     p : «expr × »(β, β), edist (s p.1) (s p.2), {p | «expr ∧ »(«expr ≥ »(p.1, N), «expr ≥ »(p.2, N))})],
   have [ident C] [":", expr ∀ n m N, «expr ≤ »(N, n) → «expr ≤ »(N, m) → «expr ≤ »(edist (s n) (s m), b N)] [],
   { refine [expr λ m n N hm hn, le_Sup _],
     use [expr prod.mk m n],
     simp [] [] ["only"] ["[", expr and_true, ",", expr eq_self_iff_true, ",", expr set.mem_set_of_eq, "]"] [] [],
     exact [expr ⟨hm, hn⟩] },
   have [ident D] [":", expr tendsto b at_top (expr𝓝() 0)] [],
   { refine [expr tendsto_order.2 ⟨λ a ha, absurd ha ennreal.not_lt_zero, λ ε εpos, _⟩],
     rcases [expr exists_between εpos, "with", "⟨", ident δ, ",", ident δpos, ",", ident δlt, "⟩"],
     rcases [expr hs δ δpos, "with", "⟨", ident N, ",", ident hN, "⟩"],
     refine [expr filter.mem_at_top_sets.2 ⟨N, λ n hn, _⟩],
     have [] [":", expr «expr ≤ »(b n, δ)] [":=", expr Sup_le (begin
         simp [] [] ["only"] ["[", expr and_imp, ",", expr set.mem_image, ",", expr set.mem_set_of_eq, ",", expr exists_imp_distrib, ",", expr prod.exists, "]"] [] [],
         intros [ident d, ident p, ident q, ident hp, ident hq, ident hd],
         rw ["<-", expr hd] [],
         exact [expr le_of_lt (hN p q (le_trans hn hp) (le_trans hn hq))]
       end)],
     simpa [] [] [] [] [] ["using", expr lt_of_le_of_lt this δlt] },
   exact [expr ⟨b, ⟨C, D⟩⟩]
 end, begin
   rintros ["⟨", ident b, ",", "⟨", ident b_bound, ",", ident b_lim, "⟩", "⟩"],
   refine [expr emetric.cauchy_seq_iff.2 (λ ε εpos, _)],
   have [] [":", expr «expr∀ᶠ in , »((n), at_top, «expr < »(b n, ε))] [":=", expr (tendsto_order.1 b_lim).2 _ εpos],
   rcases [expr filter.mem_at_top_sets.1 this, "with", "⟨", ident N, ",", ident hN, "⟩"],
   exact [expr ⟨N, λ m n hm hn, calc
       «expr ≤ »(edist (s m) (s n), b N) : b_bound m n N hm hn
       «expr < »(..., ε) : hN _ (le_refl N)⟩]
 end⟩

-- error in Topology.Instances.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem continuous_of_le_add_edist
{f : α → «exprℝ≥0∞»()}
(C : «exprℝ≥0∞»())
(hC : «expr ≠ »(C, «expr⊤»()))
(h : ∀ x y, «expr ≤ »(f x, «expr + »(f y, «expr * »(C, edist x y)))) : continuous f :=
begin
  rcases [expr eq_or_ne C 0, "with", "(", ident rfl, "|", ident C0, ")"],
  { simp [] [] ["only"] ["[", expr zero_mul, ",", expr add_zero, "]"] [] ["at", ident h],
    exact [expr continuous_of_const (λ x y, le_antisymm (h _ _) (h _ _))] },
  { refine [expr continuous_iff_continuous_at.2 (λ x, _)],
    by_cases [expr hx, ":", expr «expr = »(f x, «expr∞»())],
    { have [] [":", expr «expr =ᶠ[ ] »(f, expr𝓝() x, λ _, «expr∞»())] [],
      { filter_upwards ["[", expr emetric.ball_mem_nhds x ennreal.coe_lt_top, "]"] [],
        refine [expr λ (y) (hy : «expr < »(edist y x, «expr⊤»())), _],
        rw [expr edist_comm] ["at", ident hy],
        simpa [] [] [] ["[", expr hx, ",", expr hC, ",", expr hy.ne, "]"] [] ["using", expr h x y] },
      exact [expr this.continuous_at] },
    { refine [expr (ennreal.tendsto_nhds hx).2 (λ (ε) (ε0 : «expr < »(0, ε)), _)],
      filter_upwards ["[", expr emetric.closed_ball_mem_nhds x (ennreal.div_pos_iff.2 ⟨ε0.ne', hC⟩), "]"] [],
      have [ident hεC] [":", expr «expr = »(«expr * »(C, «expr / »(ε, C)), ε)] [":=", expr ennreal.mul_div_cancel' C0 hC],
      refine [expr λ (y) (hy : «expr ≤ »(edist y x, «expr / »(ε, C))), ⟨tsub_le_iff_right.2 _, _⟩],
      { rw [expr edist_comm] ["at", ident hy],
        calc
          «expr ≤ »(f x, «expr + »(f y, «expr * »(C, edist x y))) : h x y
          «expr ≤ »(..., «expr + »(f y, «expr * »(C, «expr / »(ε, C)))) : add_le_add_left (mul_le_mul_left' hy C) (f y)
          «expr = »(..., «expr + »(f y, ε)) : by rw [expr hεC] [] },
      { calc
          «expr ≤ »(f y, «expr + »(f x, «expr * »(C, edist y x))) : h y x
          «expr ≤ »(..., «expr + »(f x, «expr * »(C, «expr / »(ε, C)))) : add_le_add_left (mul_le_mul_left' hy C) (f x)
          «expr = »(..., «expr + »(f x, ε)) : by rw [expr hεC] [] } } }
end

theorem continuous_edist : Continuous fun p : α × α => edist p.1 p.2 :=
  by 
    apply
      continuous_of_le_add_edist 2
        (by 
          normNum)
    rintro ⟨x, y⟩ ⟨x', y'⟩
    calc edist x y ≤ (edist x x'+edist x' y')+edist y' y :=
      edist_triangle4 _ _ _ _ _ = edist x' y'+edist x x'+edist y y' :=
      by 
        simp [edist_comm] <;> cc _ ≤ edist x' y'+edist (x, y) (x', y')+edist (x, y) (x', y') :=
      add_le_add_left (add_le_add (le_max_leftₓ _ _) (le_max_rightₓ _ _)) _ _ = edist x' y'+2*edist (x, y) (x', y') :=
      by 
        rw [←mul_two, mul_commₓ]

@[continuity]
theorem Continuous.edist [TopologicalSpace β] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
  Continuous fun b => edist (f b) (g b) :=
  continuous_edist.comp (hf.prod_mk hg : _)

theorem Filter.Tendsto.edist {f g : β → α} {x : Filter β} {a b : α} (hf : tendsto f x (𝓝 a)) (hg : tendsto g x (𝓝 b)) :
  tendsto (fun x => edist (f x) (g x)) x (𝓝 (edist a b)) :=
  (continuous_edist.Tendsto (a, b)).comp (hf.prod_mk_nhds hg)

theorem cauchy_seq_of_edist_le_of_tsum_ne_top {f : ℕ → α} (d : ℕ → ℝ≥0∞) (hf : ∀ n, edist (f n) (f n.succ) ≤ d n)
  (hd : tsum d ≠ ∞) : CauchySeq f :=
  by 
    lift d to ℕ → Nnreal using fun i => Ennreal.ne_top_of_tsum_ne_top hd i 
    rw [Ennreal.tsum_coe_ne_top_iff_summable] at hd 
    exact cauchy_seq_of_edist_le_of_summable d hf hd

theorem Emetric.is_closed_ball {a : α} {r : ℝ≥0∞} : IsClosed (closed_ball a r) :=
  is_closed_le (continuous_id.edist continuous_const) continuous_const

-- error in Topology.Instances.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem emetric.diam_closure (s : set α) : «expr = »(diam (closure s), diam s) :=
begin
  refine [expr le_antisymm «expr $ »(diam_le, λ x hx y hy, _) (diam_mono subset_closure)],
  have [] [":", expr «expr ∈ »(edist x y, closure (Iic (diam s)))] [],
  from [expr map_mem_closure2 (@continuous_edist α _) hx hy (λ _ _, edist_le_diam_of_mem)],
  rwa [expr closure_Iic] ["at", ident this]
end

@[simp]
theorem Metric.diam_closure {α : Type _} [PseudoMetricSpace α] (s : Set α) : Metric.diam (Closure s) = diam s :=
  by 
    simp only [Metric.diam, Emetric.diam_closure]

theorem is_closed_set_of_lipschitz_on_with {α β} [PseudoEmetricSpace α] [PseudoEmetricSpace β] (K :  ℝ≥0 ) (s : Set α) :
  IsClosed { f:α → β | LipschitzOnWith K f s } :=
  by 
    simp only [LipschitzOnWith, set_of_forall]
    refine' is_closed_bInter fun x hx => is_closed_bInter$ fun y hy => is_closed_le _ _ 
    exacts[Continuous.edist (continuous_apply x) (continuous_apply y), continuous_const]

theorem is_closed_set_of_lipschitz_with {α β} [PseudoEmetricSpace α] [PseudoEmetricSpace β] (K :  ℝ≥0 ) :
  IsClosed { f:α → β | LipschitzWith K f } :=
  by 
    simp only [←lipschitz_on_univ, is_closed_set_of_lipschitz_on_with]

namespace Real

-- error in Topology.Instances.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For a bounded set `s : set ℝ`, its `emetric.diam` is equal to `Sup s - Inf s` reinterpreted as
`ℝ≥0∞`. -/
theorem ediam_eq
{s : set exprℝ()}
(h : bounded s) : «expr = »(emetric.diam s, ennreal.of_real «expr - »(Sup s, Inf s)) :=
begin
  rcases [expr eq_empty_or_nonempty s, "with", ident rfl, "|", ident hne],
  { simp [] [] [] [] [] [] },
  refine [expr le_antisymm «expr $ »(metric.ediam_le_of_forall_dist_le, λ x hx y hy, _) _],
  { have [] [] [":=", expr real.subset_Icc_Inf_Sup_of_bounded h],
    exact [expr real.dist_le_of_mem_Icc (this hx) (this hy)] },
  { apply [expr ennreal.of_real_le_of_le_to_real],
    rw ["[", "<-", expr metric.diam, ",", "<-", expr metric.diam_closure, "]"] [],
    have [ident h'] [] [":=", expr real.bounded_iff_bdd_below_bdd_above.1 h],
    calc
      «expr ≤ »(«expr - »(Sup s, Inf s), dist (Sup s) (Inf s)) : le_abs_self _
      «expr ≤ »(..., diam (closure s)) : dist_le_diam_of_mem h.closure (cSup_mem_closure hne h'.2) (cInf_mem_closure hne h'.1) }
end

/-- For a bounded set `s : set ℝ`, its `metric.diam` is equal to `Sup s - Inf s`. -/
theorem diam_eq {s : Set ℝ} (h : Bounded s) : Metric.diam s = Sup s - Inf s :=
  by 
    rw [Metric.diam, Real.ediam_eq h, Ennreal.to_real_of_real]
    rw [Real.bounded_iff_bdd_below_bdd_above] at h 
    exact sub_nonneg.2 (Real.Inf_le_Sup s h.1 h.2)

@[simp]
theorem ediam_Ioo (a b : ℝ) : Emetric.diam (Ioo a b) = Ennreal.ofReal (b - a) :=
  by 
    rcases le_or_ltₓ b a with (h | h)
    ·
      simp [h]
    ·
      rw [Real.ediam_eq (bounded_Ioo _ _), cSup_Ioo h, cInf_Ioo h]

@[simp]
theorem ediam_Icc (a b : ℝ) : Emetric.diam (Icc a b) = Ennreal.ofReal (b - a) :=
  by 
    rcases le_or_ltₓ a b with (h | h)
    ·
      rw [Real.ediam_eq (bounded_Icc _ _), cSup_Icc h, cInf_Icc h]
    ·
      simp [h, h.le]

@[simp]
theorem ediam_Ico (a b : ℝ) : Emetric.diam (Ico a b) = Ennreal.ofReal (b - a) :=
  le_antisymmₓ (ediam_Icc a b ▸ diam_mono Ico_subset_Icc_self) (ediam_Ioo a b ▸ diam_mono Ioo_subset_Ico_self)

@[simp]
theorem ediam_Ioc (a b : ℝ) : Emetric.diam (Ioc a b) = Ennreal.ofReal (b - a) :=
  le_antisymmₓ (ediam_Icc a b ▸ diam_mono Ioc_subset_Icc_self) (ediam_Ioo a b ▸ diam_mono Ioo_subset_Ioc_self)

end Real

/-- If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ℝ≥0∞`,
then the distance from `f n` to the limit is bounded by `∑'_{k=n}^∞ d k`. -/
theorem edist_le_tsum_of_edist_le_of_tendsto {f : ℕ → α} (d : ℕ → ℝ≥0∞) (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) {a : α}
  (ha : tendsto f at_top (𝓝 a)) (n : ℕ) : edist (f n) a ≤ ∑'m, d (n+m) :=
  by 
    refine' le_of_tendsto (tendsto_const_nhds.edist ha) (mem_at_top_sets.2 ⟨n, fun m hnm => _⟩)
    refine' le_transₓ (edist_le_Ico_sum_of_edist_le hnm fun k _ _ => hf k) _ 
    rw [Finset.sum_Ico_eq_sum_range]
    exact sum_le_tsum _ (fun _ _ => zero_le _) Ennreal.summable

/-- If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ℝ≥0∞`,
then the distance from `f 0` to the limit is bounded by `∑'_{k=0}^∞ d k`. -/
theorem edist_le_tsum_of_edist_le_of_tendsto₀ {f : ℕ → α} (d : ℕ → ℝ≥0∞) (hf : ∀ n, edist (f n) (f n.succ) ≤ d n)
  {a : α} (ha : tendsto f at_top (𝓝 a)) : edist (f 0) a ≤ ∑'m, d m :=
  by 
    simpa using edist_le_tsum_of_edist_le_of_tendsto d hf ha 0

end 

