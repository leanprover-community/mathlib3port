import Mathbin.Topology.MetricSpace.HausdorffDistance 
import Mathbin.Topology.Compacts 
import Mathbin.Analysis.SpecificLimits

/-!
# Closed subsets

This file defines the metric and emetric space structure on the types of closed subsets and nonempty
compact subsets of a metric or emetric space.

The Hausdorff distance induces an emetric space structure on the type of closed subsets
of an emetric space, called `closeds`. Its completeness, resp. compactness, resp.
second-countability, follow from the corresponding properties of the original space.

In a metric space, the type of nonempty compact subsets (called `nonempty_compacts`) also
inherits a metric space structure from the Hausdorff distance, as the Hausdorff edistance is
always finite in this context.
-/


noncomputable theory

open_locale Classical TopologicalSpace Ennreal

universe u

open Classical Set Function TopologicalSpace Filter

namespace Emetric

section 

variable{α : Type u}[EmetricSpace α]{s : Set α}

/-- In emetric spaces, the Hausdorff edistance defines an emetric space structure
on the type of closed subsets -/
instance closeds.emetric_space : EmetricSpace (closeds α) :=
  { edist := fun s t => Hausdorff_edist s.val t.val, edist_self := fun s => Hausdorff_edist_self,
    edist_comm := fun s t => Hausdorff_edist_comm, edist_triangle := fun s t u => Hausdorff_edist_triangle,
    eq_of_edist_eq_zero := fun s t h => Subtype.eq ((Hausdorff_edist_zero_iff_eq_of_closed s.property t.property).1 h) }

/-- The edistance to a closed set depends continuously on the point and the set -/
theorem continuous_inf_edist_Hausdorff_edist : Continuous fun p : α × closeds α => inf_edist p.1 p.2.val :=
  by 
    refine'
      continuous_of_le_add_edist 2
        (by 
          simp )
        _ 
    rintro ⟨x, s⟩ ⟨y, t⟩
    calc inf_edist x s.val ≤ inf_edist x t.val+Hausdorff_edist t.val s.val :=
      inf_edist_le_inf_edist_add_Hausdorff_edist _ ≤ (inf_edist y t.val+edist x y)+Hausdorff_edist t.val s.val :=
      add_le_add_right inf_edist_le_inf_edist_add_edist _ _ = inf_edist y t.val+edist x y+Hausdorff_edist s.val t.val :=
      by 
        simp [add_commₓ, add_left_commₓ, Hausdorff_edist_comm,
          -Subtype.val_eq_coe]_ ≤ inf_edist y t.val+edist (x, s) (y, t)+edist (x, s) (y, t) :=
      add_le_add_left (add_le_add (le_max_leftₓ _ _) (le_max_rightₓ _ _))
        _ _ = inf_edist y t.val+2*edist (x, s) (y, t) :=
      by 
        rw [←mul_two, mul_commₓ]

/-- Subsets of a given closed subset form a closed set -/
theorem is_closed_subsets_of_is_closed (hs : IsClosed s) : IsClosed { t : closeds α | t.val ⊆ s } :=
  by 
    refine' is_closed_of_closure_subset fun t ht x hx => _ 
    have  : x ∈ Closure s
    ·
      refine' mem_closure_iff.2 fun ε εpos => _ 
      rcases mem_closure_iff.1 ht ε εpos with ⟨u, hu, Dtu⟩
      rcases exists_edist_lt_of_Hausdorff_edist_lt hx Dtu with ⟨y, hy, Dxy⟩
      exact ⟨y, hu hy, Dxy⟩
    rwa [hs.closure_eq] at this

/-- By definition, the edistance on `closeds α` is given by the Hausdorff edistance -/
theorem closeds.edist_eq {s t : closeds α} : edist s t = Hausdorff_edist s.val t.val :=
  rfl

/-- In a complete space, the type of closed subsets is complete for the
Hausdorff edistance. -/
instance closeds.complete_space [CompleteSpace α] : CompleteSpace (closeds α) :=
  by 
    let B : ℕ → ℝ≥0∞ := fun n => 2⁻¹ ^ n 
    have B_pos : ∀ n, (0 : ℝ≥0∞) < B n
    ·
      simp [B, Ennreal.pow_pos]
    have B_ne_top : ∀ n, B n ≠ ⊤
    ·
      simp [B, Ennreal.pow_ne_top]
    refine' complete_of_convergent_controlled_sequences B B_pos fun s hs => _ 
    let t0 := ⋂n, Closure (⋃(m : _)(_ : m ≥ n), (s m).val)
    let t : closeds α := ⟨t0, is_closed_Inter fun _ => is_closed_closure⟩
    use t 
    have I1 : ∀ n : ℕ, ∀ x _ : x ∈ (s n).val, ∃ (y : _)(_ : y ∈ t0), edist x y ≤ 2*B n
    ·
      intro n x hx 
      obtain ⟨z, hz₀, hz⟩ : ∃ z : ∀ l, (s (n+l)).val, (z 0 : α) = x ∧ ∀ k, edist (z k : α) (z (k+1) : α) ≤ B n / 2 ^ k
      ·
        have  : ∀ l : ℕ z : (s (n+l)).val, ∃ z' : (s ((n+l)+1)).val, edist (z : α) z' ≤ B n / 2 ^ l
        ·
          intro l z 
          obtain ⟨z', z'_mem, hz'⟩ : ∃ (z' : _)(_ : z' ∈ (s ((n+l)+1)).val), edist (z : α) z' < B n / 2 ^ l
          ·
            apply exists_edist_lt_of_Hausdorff_edist_lt z.2
            simp only [B, Ennreal.inv_pow, div_eq_mul_inv]
            rw [←pow_addₓ]
            apply hs <;> simp 
          exact ⟨⟨z', z'_mem⟩, le_of_ltₓ hz'⟩
        use fun k => Nat.recOn k ⟨x, hx⟩ fun l z => some (this l z), rfl 
        exact fun k => some_spec (this k _)
      have  : CauchySeq fun k => (z k : α)
      exact cauchy_seq_of_edist_le_geometric_two (B n) (B_ne_top n) hz 
      rcases cauchy_seq_tendsto_of_complete this with ⟨y, y_lim⟩
      use y 
      have  : y ∈ t0 :=
        mem_Inter.2
          fun k =>
            mem_closure_of_tendsto y_lim
              (by 
                simp only [exists_prop, Set.mem_Union, Filter.eventually_at_top, Set.mem_preimage, Set.preimage_Union]
                exact ⟨k, fun m hm => ⟨n+m, zero_addₓ k ▸ add_le_add (zero_le n) hm, (z m).2⟩⟩)
      use this 
      rw [←hz₀]
      exact edist_le_of_edist_le_geometric_two_of_tendsto₀ (B n) hz y_lim 
    have I2 : ∀ n : ℕ, ∀ x _ : x ∈ t0, ∃ (y : _)(_ : y ∈ (s n).val), edist x y ≤ 2*B n
    ·
      intro n x xt0 
      have  : x ∈ Closure (⋃(m : _)(_ : m ≥ n), (s m).val)
      ·
        apply mem_Inter.1 xt0 n 
      rcases mem_closure_iff.1 this (B n) (B_pos n) with ⟨z, hz, Dxz⟩
      simp only [exists_prop, Set.mem_Union] at hz 
      rcases hz with ⟨m, ⟨m_ge_n, hm⟩⟩
      have  : Hausdorff_edist (s m).val (s n).val < B n := hs n m n m_ge_n (le_reflₓ n)
      rcases exists_edist_lt_of_Hausdorff_edist_lt hm this with ⟨y, hy, Dzy⟩
      exact
        ⟨y, hy,
          calc edist x y ≤ edist x z+edist z y := edist_triangle _ _ _ 
            _ ≤ B n+B n := add_le_add (le_of_ltₓ Dxz) (le_of_ltₓ Dzy)
            _ = 2*B n := (two_mul _).symm
            ⟩
    have main : ∀ n : ℕ, edist (s n) t ≤ 2*B n := fun n => Hausdorff_edist_le_of_mem_edist (I1 n) (I2 n)
    refine' tendsto_at_top.2 fun ε εpos => _ 
    have  : tendsto (fun n => 2*B n) at_top (𝓝 (2*0))
    exact
      Ennreal.Tendsto.const_mul
        (Ennreal.tendsto_pow_at_top_nhds_0_of_lt_1$
          by 
            simp [Ennreal.one_lt_two])
        (Or.inr$
          by 
            simp )
    rw [mul_zero] at this 
    obtain ⟨N, hN⟩ : ∃ N, ∀ b _ : b ≥ N, ε > 2*B b 
    exact ((tendsto_order.1 this).2 ε εpos).exists_forall_of_at_top 
    exact ⟨N, fun n hn => lt_of_le_of_ltₓ (main n) (hN n hn)⟩

/-- In a compact space, the type of closed subsets is compact. -/
instance closeds.compact_space [CompactSpace α] : CompactSpace (closeds α) :=
  ⟨by 
      refine' compact_of_totally_bounded_is_closed (Emetric.totally_bounded_iff.2 fun ε εpos => _) is_closed_univ 
      rcases exists_between εpos with ⟨δ, δpos, δlt⟩
      rcases Emetric.totally_bounded_iff.1 (compact_iff_totally_bounded_complete.1 (@compact_univ α _ _)).1 δ δpos with
        ⟨s, fs, hs⟩
      have main : ∀ u : Set α, ∃ (v : _)(_ : v ⊆ s), Hausdorff_edist u v ≤ δ
      ·
        intro u 
        let v := { x : α | x ∈ s ∧ ∃ (y : _)(_ : y ∈ u), edist x y < δ }
        exists v, (fun x hx => hx.1 : v ⊆ s)
        refine' Hausdorff_edist_le_of_mem_edist _ _
        ·
          intro x hx 
          have  : x ∈ ⋃(y : _)(_ : y ∈ s), ball y δ :=
            hs
              (by 
                simp )
          rcases mem_bUnion_iff.1 this with ⟨y, ys, dy⟩
          have  : edist y x < δ :=
            by 
              simp  at dy <;> rwa [edist_comm] at dy 
          exact ⟨y, ⟨ys, ⟨x, hx, this⟩⟩, le_of_ltₓ dy⟩
        ·
          rintro x ⟨hx1, ⟨y, yu, hy⟩⟩
          exact ⟨y, yu, le_of_ltₓ hy⟩
      let F := { f : closeds α | f.val ⊆ s }
      use F 
      split 
      ·
        apply @finite_of_finite_image _ _ F fun f => f.val
        ·
          exact subtype.val_injective.inj_on F
        ·
          refine' fs.finite_subsets.subset fun b => _ 
          simp only [and_imp, Set.mem_image, Set.mem_set_of_eq, exists_imp_distrib]
          intro x hx hx' 
          rwa [hx'] at hx
      ·
        intro u _ 
        rcases main u.val with ⟨t0, t0s, Dut0⟩
        have  : IsClosed t0 := (fs.subset t0s).IsCompact.IsClosed 
        let t : closeds α := ⟨t0, this⟩
        have  : t ∈ F := t0s 
        have  : edist u t < ε := lt_of_le_of_ltₓ Dut0 δlt 
        apply mem_bUnion_iff.2 
        exact ⟨t, ‹t ∈ F›, this⟩⟩

/-- In an emetric space, the type of non-empty compact subsets is an emetric space,
where the edistance is the Hausdorff edistance -/
instance nonempty_compacts.emetric_space : EmetricSpace (nonempty_compacts α) :=
  { edist := fun s t => Hausdorff_edist s.val t.val, edist_self := fun s => Hausdorff_edist_self,
    edist_comm := fun s t => Hausdorff_edist_comm, edist_triangle := fun s t u => Hausdorff_edist_triangle,
    eq_of_edist_eq_zero :=
      fun s t h =>
        Subtype.eq$
          by 
            have  : Closure s.val = Closure t.val := Hausdorff_edist_zero_iff_closure_eq_closure.1 h 
            rwa [s.property.2.IsClosed.closure_eq, t.property.2.IsClosed.closure_eq] at this }

/-- `nonempty_compacts.to_closeds` is a uniform embedding (as it is an isometry) -/
theorem nonempty_compacts.to_closeds.uniform_embedding : UniformEmbedding (@nonempty_compacts.to_closeds α _ _) :=
  Isometry.uniform_embedding$ fun x y => rfl

/-- The range of `nonempty_compacts.to_closeds` is closed in a complete space -/
theorem nonempty_compacts.is_closed_in_closeds [CompleteSpace α] :
  IsClosed (range$ @nonempty_compacts.to_closeds α _ _) :=
  by 
    have  : range nonempty_compacts.to_closeds = { s : closeds α | s.val.nonempty ∧ IsCompact s.val }
    exact range_inclusion _ 
    rw [this]
    refine' is_closed_of_closure_subset fun s hs => ⟨_, _⟩
    ·
      rcases mem_closure_iff.1 hs ⊤ Ennreal.coe_lt_top with ⟨t, ht, Dst⟩
      rw [edist_comm] at Dst 
      exact nonempty_of_Hausdorff_edist_ne_top ht.1 (ne_of_ltₓ Dst)
    ·
      refine' compact_iff_totally_bounded_complete.2 ⟨_, s.property.is_complete⟩
      refine' totally_bounded_iff.2 fun ε εpos : 0 < ε => _ 
      rcases mem_closure_iff.1 hs (ε / 2) (Ennreal.half_pos εpos.ne') with ⟨t, ht, Dst⟩
      rcases
        totally_bounded_iff.1 (compact_iff_totally_bounded_complete.1 ht.2).1 (ε / 2) (Ennreal.half_pos εpos.ne') with
        ⟨u, fu, ut⟩
      refine' ⟨u, ⟨fu, fun x hx => _⟩⟩
      rcases exists_edist_lt_of_Hausdorff_edist_lt hx Dst with ⟨z, hz, Dxz⟩
      rcases mem_bUnion_iff.1 (ut hz) with ⟨y, hy, Dzy⟩
      have  : edist x y < ε :=
        calc edist x y ≤ edist x z+edist z y := edist_triangle _ _ _ 
          _ < (ε / 2)+ε / 2 := Ennreal.add_lt_add Dxz Dzy 
          _ = ε := Ennreal.add_halves _ 
          
      exact mem_bUnion hy this

/-- In a complete space, the type of nonempty compact subsets is complete. This follows
from the same statement for closed subsets -/
instance nonempty_compacts.complete_space [CompleteSpace α] : CompleteSpace (nonempty_compacts α) :=
  (complete_space_iff_is_complete_range nonempty_compacts.to_closeds.uniform_embedding.to_uniform_inducing).2$
    nonempty_compacts.is_closed_in_closeds.IsComplete

/-- In a compact space, the type of nonempty compact subsets is compact. This follows from
the same statement for closed subsets -/
instance nonempty_compacts.compact_space [CompactSpace α] : CompactSpace (nonempty_compacts α) :=
  ⟨by 
      rw [nonempty_compacts.to_closeds.uniform_embedding.embedding.is_compact_iff_is_compact_image]
      rw [image_univ]
      exact nonempty_compacts.is_closed_in_closeds.is_compact⟩

/-- In a second countable space, the type of nonempty compact subsets is second countable -/
instance nonempty_compacts.second_countable_topology [second_countable_topology α] :
  second_countable_topology (nonempty_compacts α) :=
  by 
    haveI  : separable_space (nonempty_compacts α) :=
      by 
        rcases exists_countable_dense α with ⟨s, cs, s_dense⟩
        let v0 := { t : Set α | finite t ∧ t ⊆ s }
        let v : Set (nonempty_compacts α) := { t : nonempty_compacts α | t.val ∈ v0 }
        refine' ⟨⟨v, ⟨_, _⟩⟩⟩
        ·
          have  : countable v0 
          exact countable_set_of_finite_subset cs 
          exact this.preimage Subtype.coe_injective
        ·
          refine' fun t => mem_closure_iff.2 fun ε εpos => _ 
          rcases exists_between εpos with ⟨δ, δpos, δlt⟩
          have δpos' : 0 < δ / 2 
          exact Ennreal.half_pos δpos.ne' 
          have Exy : ∀ x, ∃ y, y ∈ s ∧ edist x y < δ / 2
          ·
            intro x 
            rcases mem_closure_iff.1 (s_dense x) (δ / 2) δpos' with ⟨y, ys, hy⟩
            exact ⟨y, ⟨ys, hy⟩⟩
          let F := fun x => some (Exy x)
          have Fspec : ∀ x, F x ∈ s ∧ edist x (F x) < δ / 2 := fun x => some_spec (Exy x)
          have  : TotallyBounded t.val := t.property.2.TotallyBounded 
          rcases totally_bounded_iff.1 this (δ / 2) δpos' with ⟨a, af, ta⟩
          let b := F '' a 
          have  : finite b := af.image _ 
          have tb : ∀ x _ : x ∈ t.val, ∃ (y : _)(_ : y ∈ b), edist x y < δ
          ·
            intro x hx 
            rcases mem_bUnion_iff.1 (ta hx) with ⟨z, za, Dxz⟩
            exists F z, mem_image_of_mem _ za 
            calc edist x (F z) ≤ edist x z+edist z (F z) := edist_triangle _ _ _ _ < (δ / 2)+δ / 2 :=
              Ennreal.add_lt_add Dxz (Fspec z).2_ = δ := Ennreal.add_halves _ 
          let c := { y ∈ b | ∃ (x : _)(_ : x ∈ t.val), edist x y < δ }
          have  : finite c := ‹finite b›.Subset fun x hx => hx.1
          have tc : ∀ x _ : x ∈ t.val, ∃ (y : _)(_ : y ∈ c), edist x y ≤ δ
          ·
            intro x hx 
            rcases tb x hx with ⟨y, yv, Dxy⟩
            have  : y ∈ c :=
              by 
                simp [c, -mem_image] <;> exact ⟨yv, ⟨x, hx, Dxy⟩⟩
            exact ⟨y, this, le_of_ltₓ Dxy⟩
          have ct : ∀ y _ : y ∈ c, ∃ (x : _)(_ : x ∈ t.val), edist y x ≤ δ
          ·
            rintro y ⟨hy1, ⟨x, xt, Dyx⟩⟩
            have  : edist y x ≤ δ :=
              calc edist y x = edist x y := edist_comm _ _ 
                _ ≤ δ := le_of_ltₓ Dyx 
                
            exact ⟨x, xt, this⟩
          have  : Hausdorff_edist t.val c ≤ δ := Hausdorff_edist_le_of_mem_edist Tc ct 
          have Dtc : Hausdorff_edist t.val c < ε := lt_of_le_of_ltₓ this δlt 
          have hc : c.nonempty 
          exact nonempty_of_Hausdorff_edist_ne_top t.property.1 (ne_top_of_lt Dtc)
          let d : nonempty_compacts α := ⟨c, ⟨hc, ‹finite c›.IsCompact⟩⟩
          have  : c ⊆ s
          ·
            intro x hx 
            rcases(mem_image _ _ _).1 hx.1 with ⟨y, ⟨ya, yx⟩⟩
            rw [←yx]
            exact (Fspec y).1
          have  : d ∈ v := ⟨‹finite c›, this⟩
          exact ⟨d, ‹d ∈ v›, Dtc⟩
    apply UniformSpace.second_countable_of_separable

end 

end Emetric

namespace Metric

section 

variable{α : Type u}[MetricSpace α]

/-- `nonempty_compacts α` inherits a metric space structure, as the Hausdorff
edistance between two such sets is finite. -/
instance nonempty_compacts.metric_space : MetricSpace (nonempty_compacts α) :=
  EmetricSpace.toMetricSpace$
    fun x y => Hausdorff_edist_ne_top_of_nonempty_of_bounded x.2.1 y.2.1 x.2.2.Bounded y.2.2.Bounded

/-- The distance on `nonempty_compacts α` is the Hausdorff distance, by construction -/
theorem nonempty_compacts.dist_eq {x y : nonempty_compacts α} : dist x y = Hausdorff_dist x.val y.val :=
  rfl

theorem lipschitz_inf_dist_set (x : α) : LipschitzWith 1 fun s : nonempty_compacts α => inf_dist x s.val :=
  LipschitzWith.of_le_add$
    fun s t =>
      by 
        rw [dist_comm]
        exact inf_dist_le_inf_dist_add_Hausdorff_dist (edist_ne_top t s)

theorem lipschitz_inf_dist : LipschitzWith 2 fun p : α × nonempty_compacts α => inf_dist p.1 p.2.val :=
  @LipschitzWith.uncurry _ _ _ _ _ _ (fun x : α s : nonempty_compacts α => inf_dist x s.val) 1 1
    (fun s => lipschitz_inf_dist_pt s.val) lipschitz_inf_dist_set

theorem uniform_continuous_inf_dist_Hausdorff_dist :
  UniformContinuous fun p : α × nonempty_compacts α => inf_dist p.1 p.2.val :=
  lipschitz_inf_dist.UniformContinuous

end 

end Metric

