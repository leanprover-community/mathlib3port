/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
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


noncomputable section

open_locale Classical TopologicalSpace Ennreal

universe u

open Classical Set Function TopologicalSpace Filter

namespace Emetric

section

variable {α : Type u} [EmetricSpace α] {s : Set α}

/-- In emetric spaces, the Hausdorff edistance defines an emetric space structure
on the type of closed subsets -/
instance Closeds.emetricSpace : EmetricSpace (Closeds α) where
  edist := fun s t => hausdorffEdist (s : Set α) t
  edist_self := fun s => Hausdorff_edist_self
  edist_comm := fun s t => Hausdorff_edist_comm
  edist_triangle := fun s t u => Hausdorff_edist_triangle
  eq_of_edist_eq_zero := fun s t h => closeds.ext <| (Hausdorff_edist_zero_iff_eq_of_closed s.closed t.closed).1 h

/-- The edistance to a closed set depends continuously on the point and the set -/
theorem continuous_inf_edist_Hausdorff_edist : Continuous fun p : α × Closeds α => infEdist p.1 p.2 := by
  refine'
    continuous_of_le_add_edist 2
      (by
        simp )
      _
  rintro ⟨x, s⟩ ⟨y, t⟩
  calc inf_edist x s ≤ inf_edist x t + Hausdorff_edist (t : Set α) s :=
      inf_edist_le_inf_edist_add_Hausdorff_edist _ ≤ inf_edist y t + edist x y + Hausdorff_edist (t : Set α) s :=
      add_le_add_right inf_edist_le_inf_edist_add_edist
        _ _ = inf_edist y t + (edist x y + Hausdorff_edist (s : Set α) t) :=
      by
      rw [add_assocₓ, Hausdorff_edist_comm]_ ≤ inf_edist y t + (edist (x, s) (y, t) + edist (x, s) (y, t)) :=
      add_le_add_left (add_le_add (le_max_leftₓ _ _) (le_max_rightₓ _ _))
        _ _ = inf_edist y t + 2 * edist (x, s) (y, t) :=
      by
      rw [← mul_two, mul_comm]

/-- Subsets of a given closed subset form a closed set -/
theorem is_closed_subsets_of_is_closed (hs : IsClosed s) : IsClosed { t : Closeds α | (t : Set α) ⊆ s } := by
  refine' is_closed_of_closure_subset fun t ht x hx => _
  -- t : closeds α,  ht : t ∈ closure {t : closeds α | t ⊆ s},
  -- x : α,  hx : x ∈ t
  -- goal : x ∈ s
  have : x ∈ Closure s := by
    refine' mem_closure_iff.2 fun ε εpos => _
    rcases mem_closure_iff.1 ht ε εpos with ⟨u, hu, Dtu⟩
    -- u : closeds α,  hu : u ∈ {t : closeds α | t ⊆ s},  hu' : edist t u < ε
    rcases exists_edist_lt_of_Hausdorff_edist_lt hx Dtu with ⟨y, hy, Dxy⟩
    -- y : α,  hy : y ∈ u, Dxy : edist x y < ε
    exact ⟨y, hu hy, Dxy⟩
  rwa [hs.closure_eq] at this

/-- By definition, the edistance on `closeds α` is given by the Hausdorff edistance -/
theorem Closeds.edist_eq {s t : Closeds α} : edist s t = hausdorffEdist (s : Set α) t :=
  rfl

/-- In a complete space, the type of closed subsets is complete for the
Hausdorff edistance. -/
instance Closeds.complete_space [CompleteSpace α] : CompleteSpace (Closeds α) := by
  /- We will show that, if a sequence of sets `s n` satisfies
    `edist (s n) (s (n+1)) < 2^{-n}`, then it converges. This is enough to guarantee
    completeness, by a standard completeness criterion.
    We use the shorthand `B n = 2^{-n}` in ennreal. -/
  let B : ℕ → ℝ≥0∞ := fun n => 2⁻¹ ^ n
  have B_pos : ∀ n, (0 : ℝ≥0∞) < B n := by
    simp [B, Ennreal.pow_pos]
  have B_ne_top : ∀ n, B n ≠ ⊤ := by
    simp [B, Ennreal.pow_ne_top]
  /- Consider a sequence of closed sets `s n` with `edist (s n) (s (n+1)) < B n`.
    We will show that it converges. The limit set is t0 = ⋂n, closure (⋃m≥n, s m).
    We will have to show that a point in `s n` is close to a point in `t0`, and a point
    in `t0` is close to a point in `s n`. The completeness then follows from a
    standard criterion. -/
  refine' complete_of_convergent_controlled_sequences B B_pos fun s hs => _
  let t0 := ⋂ n, Closure (⋃ m ≥ n, s m : Set α)
  let t : closeds α := ⟨t0, is_closed_Inter fun _ => is_closed_closure⟩
  use t
  -- The inequality is written this way to agree with `edist_le_of_edist_le_geometric_of_tendsto₀`
  have I1 : ∀ n, ∀, ∀ x ∈ s n, ∀, ∃ y ∈ t0, edist x y ≤ 2 * B n := by
    /- This is the main difficulty of the proof. Starting from `x ∈ s n`, we want
           to find a point in `t0` which is close to `x`. Define inductively a sequence of
           points `z m` with `z n = x` and `z m ∈ s m` and `edist (z m) (z (m+1)) ≤ B m`. This is
           possible since the Hausdorff distance between `s m` and `s (m+1)` is at most `B m`.
           This sequence is a Cauchy sequence, therefore converging as the space is complete, to
           a limit which satisfies the required properties. -/
    intro n x hx
    obtain ⟨z, hz₀, hz⟩ : ∃ z : ∀ l, s (n + l), (z 0 : α) = x ∧ ∀ k, edist (z k : α) (z (k + 1) : α) ≤ B n / 2 ^ k := by
      -- We prove existence of the sequence by induction.
      have : ∀ l z : s (n + l), ∃ z' : s (n + l + 1), edist (z : α) z' ≤ B n / 2 ^ l := by
        intro l z
        obtain ⟨z', z'_mem, hz'⟩ : ∃ z' ∈ s (n + l + 1), edist (z : α) z' < B n / 2 ^ l := by
          refine' exists_edist_lt_of_Hausdorff_edist_lt _ _
          · exact s (n + l)
            
          · exact z.2
            
          simp only [B, Ennreal.inv_pow, div_eq_mul_inv]
          rw [← pow_addₓ]
          apply hs <;> simp
        exact ⟨⟨z', z'_mem⟩, le_of_ltₓ hz'⟩
      use fun k => Nat.recOn k ⟨x, hx⟩ fun l z => some (this l z), rfl
      exact fun k => some_spec (this k _)
    -- it follows from the previous bound that `z` is a Cauchy sequence
    have : CauchySeq fun k => (z k : α) := cauchy_seq_of_edist_le_geometric_two (B n) (B_ne_top n) hz
    -- therefore, it converges
    rcases cauchy_seq_tendsto_of_complete this with ⟨y, y_lim⟩
    use y
    -- the limit point `y` will be the desired point, in `t0` and close to our initial point `x`.
    -- First, we check it belongs to `t0`.
    have : y ∈ t0 :=
      mem_Inter.2 fun k =>
        mem_closure_of_tendsto y_lim
          (by
            simp only [exists_prop, Set.mem_Union, Filter.eventually_at_top, Set.mem_preimage, Set.preimage_Union]
            exact ⟨k, fun m hm => ⟨n + m, zero_addₓ k ▸ add_le_add (zero_le n) hm, (z m).2⟩⟩)
    use this
    -- Then, we check that `y` is close to `x = z n`. This follows from the fact that `y`
    -- is the limit of `z k`, and the distance between `z n` and `z k` has already been estimated.
    rw [← hz₀]
    exact edist_le_of_edist_le_geometric_two_of_tendsto₀ (B n) hz y_lim
  have I2 : ∀ n, ∀, ∀ x ∈ t0, ∀, ∃ y ∈ s n, edist x y ≤ 2 * B n := by
    /- For the (much easier) reverse inequality, we start from a point `x ∈ t0` and we want
            to find a point `y ∈ s n` which is close to `x`.
            `x` belongs to `t0`, the intersection of the closures. In particular, it is well
            approximated by a point `z` in `⋃m≥n, s m`, say in `s m`. Since `s m` and
            `s n` are close, this point is itself well approximated by a point `y` in `s n`,
            as required. -/
    intro n x xt0
    have : x ∈ Closure (⋃ m ≥ n, s m : Set α) := by
      apply mem_Inter.1 xt0 n
    rcases mem_closure_iff.1 this (B n) (B_pos n) with ⟨z, hz, Dxz⟩
    -- z : α,  Dxz : edist x z < B n,
    simp only [exists_prop, Set.mem_Union] at hz
    rcases hz with ⟨m, ⟨m_ge_n, hm⟩⟩
    -- m : ℕ, m_ge_n : m ≥ n, hm : z ∈ s m
    have : Hausdorff_edist (s m : Set α) (s n) < B n := hs n m n m_ge_n (le_reflₓ n)
    rcases exists_edist_lt_of_Hausdorff_edist_lt hm this with ⟨y, hy, Dzy⟩
    -- y : α,  hy : y ∈ s n,  Dzy : edist z y < B n
    exact
      ⟨y, hy,
        calc
          edist x y ≤ edist x z + edist z y := edist_triangle _ _ _
          _ ≤ B n + B n := add_le_add (le_of_ltₓ Dxz) (le_of_ltₓ Dzy)
          _ = 2 * B n := (two_mul _).symm
          ⟩
  -- Deduce from the above inequalities that the distance between `s n` and `t0` is at most `2 B n`.
  have main : ∀ n : ℕ, edist (s n) t ≤ 2 * B n := fun n => Hausdorff_edist_le_of_mem_edist (I1 n) (I2 n)
  -- from this, the convergence of `s n` to `t0` follows.
  refine' tendsto_at_top.2 fun ε εpos => _
  have : tendsto (fun n => 2 * B n) at_top (𝓝 (2 * 0)) :=
    Ennreal.Tendsto.const_mul
      (Ennreal.tendsto_pow_at_top_nhds_0_of_lt_1 <| by
        simp [Ennreal.one_lt_two])
      (Or.inr <| by
        simp )
  rw [mul_zero] at this
  obtain ⟨N, hN⟩ : ∃ N, ∀, ∀ b ≥ N, ∀, ε > 2 * B b
  exact ((tendsto_order.1 this).2 ε εpos).exists_forall_of_at_top
  exact ⟨N, fun n hn => lt_of_le_of_ltₓ (main n) (hN n hn)⟩

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (v «expr ⊆ » s)
/-- In a compact space, the type of closed subsets is compact. -/
instance Closeds.compact_space [CompactSpace α] : CompactSpace (Closeds α) :=
  ⟨by
    /- by completeness, it suffices to show that it is totally bounded,
        i.e., for all ε>0, there is a finite set which is ε-dense.
        start from a set `s` which is ε-dense in α. Then the subsets of `s`
        are finitely many, and ε-dense for the Hausdorff distance. -/
    refine' compact_of_totally_bounded_is_closed (Emetric.totally_bounded_iff.2 fun ε εpos => _) is_closed_univ
    rcases exists_between εpos with ⟨δ, δpos, δlt⟩
    rcases Emetric.totally_bounded_iff.1 (compact_iff_totally_bounded_complete.1 (@compact_univ α _ _)).1 δ δpos with
      ⟨s, fs, hs⟩
    -- s : set α,  fs : finite s,  hs : univ ⊆ ⋃ (y : α) (H : y ∈ s), eball y δ
    -- we first show that any set is well approximated by a subset of `s`.
    have main : ∀ u : Set α, ∃ (v : _)(_ : v ⊆ s), Hausdorff_edist u v ≤ δ := by
      intro u
      let v := { x : α | x ∈ s ∧ ∃ y ∈ u, edist x y < δ }
      exists v, (fun x hx => hx.1 : v ⊆ s)
      refine' Hausdorff_edist_le_of_mem_edist _ _
      · intro x hx
        have : x ∈ ⋃ y ∈ s, ball y δ :=
          hs
            (by
              simp )
        rcases mem_Union₂.1 this with ⟨y, ys, dy⟩
        have : edist y x < δ := by
          simp at dy <;> rwa [edist_comm] at dy
        exact ⟨y, ⟨ys, ⟨x, hx, this⟩⟩, le_of_ltₓ dy⟩
        
      · rintro x ⟨hx1, ⟨y, yu, hy⟩⟩
        exact ⟨y, yu, le_of_ltₓ hy⟩
        
    -- introduce the set F of all subsets of `s` (seen as members of `closeds α`).
    let F := { f : closeds α | (f : Set α) ⊆ s }
    refine' ⟨F, _, fun u _ => _⟩
    -- `F` is finite
    · apply @finite_of_finite_image _ _ F coe
      · exact set_like.coe_injective.inj_on F
        
      · refine' fs.finite_subsets.subset fun b => _
        simp only [and_imp, Set.mem_image, Set.mem_set_of_eq, exists_imp_distrib]
        intro x hx hx'
        rwa [hx'] at hx
        
      
    -- `F` is ε-dense
    · obtain ⟨t0, t0s, Dut0⟩ := main u
      have : IsClosed t0 := (fs.subset t0s).IsCompact.IsClosed
      let t : closeds α := ⟨t0, this⟩
      have : t ∈ F := t0s
      have : edist u t < ε := lt_of_le_of_ltₓ Dut0 δlt
      apply mem_Union₂.2
      exact ⟨t, ‹t ∈ F›, this⟩
      ⟩

/-- In an emetric space, the type of non-empty compact subsets is an emetric space,
where the edistance is the Hausdorff edistance -/
instance NonemptyCompacts.emetricSpace : EmetricSpace (NonemptyCompacts α) where
  edist := fun s t => hausdorffEdist (s : Set α) t
  edist_self := fun s => Hausdorff_edist_self
  edist_comm := fun s t => Hausdorff_edist_comm
  edist_triangle := fun s t u => Hausdorff_edist_triangle
  eq_of_edist_eq_zero := fun s t h =>
    nonempty_compacts.ext <| by
      have : Closure (s : Set α) = Closure t := Hausdorff_edist_zero_iff_closure_eq_closure.1 h
      rwa [s.compact.is_closed.closure_eq, t.compact.is_closed.closure_eq] at this

/-- `nonempty_compacts.to_closeds` is a uniform embedding (as it is an isometry) -/
theorem NonemptyCompacts.ToCloseds.uniform_embedding : UniformEmbedding (@NonemptyCompacts.toCloseds α _ _) :=
  Isometry.uniform_embedding fun x y => rfl

/-- The range of `nonempty_compacts.to_closeds` is closed in a complete space -/
theorem NonemptyCompacts.is_closed_in_closeds [CompleteSpace α] :
    IsClosed (range <| @NonemptyCompacts.toCloseds α _ _) := by
  have : range nonempty_compacts.to_closeds = { s : closeds α | (s : Set α).Nonempty ∧ IsCompact (s : Set α) } := by
    ext s
    refine' ⟨_, fun h => ⟨⟨⟨s, h.2⟩, h.1⟩, closeds.ext rfl⟩⟩
    rintro ⟨s, hs, rfl⟩
    exact ⟨s.nonempty, s.compact⟩
  rw [this]
  refine' is_closed_of_closure_subset fun s hs => ⟨_, _⟩
  · -- take a set set t which is nonempty and at a finite distance of s
    rcases mem_closure_iff.1 hs ⊤ Ennreal.coe_lt_top with ⟨t, ht, Dst⟩
    rw [edist_comm] at Dst
    -- since `t` is nonempty, so is `s`
    exact nonempty_of_Hausdorff_edist_ne_top ht.1 (ne_of_ltₓ Dst)
    
  · refine' compact_iff_totally_bounded_complete.2 ⟨_, s.closed.is_complete⟩
    refine' totally_bounded_iff.2 fun εpos : 0 < ε => _
    -- we have to show that s is covered by finitely many eballs of radius ε
    -- pick a nonempty compact set t at distance at most ε/2 of s
    rcases mem_closure_iff.1 hs (ε / 2) (Ennreal.half_pos εpos.ne') with ⟨t, ht, Dst⟩
    -- cover this space with finitely many balls of radius ε/2
    rcases totally_bounded_iff.1 (compact_iff_totally_bounded_complete.1 ht.2).1 (ε / 2)
        (Ennreal.half_pos εpos.ne') with
      ⟨u, fu, ut⟩
    refine' ⟨u, ⟨fu, fun x hx => _⟩⟩
    -- u : set α,  fu : finite u,  ut : t ⊆ ⋃ (y : α) (H : y ∈ u), eball y (ε / 2)
    -- then s is covered by the union of the balls centered at u of radius ε
    rcases exists_edist_lt_of_Hausdorff_edist_lt hx Dst with ⟨z, hz, Dxz⟩
    rcases mem_Union₂.1 (ut hz) with ⟨y, hy, Dzy⟩
    have : edist x y < ε :=
      calc
        edist x y ≤ edist x z + edist z y := edist_triangle _ _ _
        _ < ε / 2 + ε / 2 := Ennreal.add_lt_add Dxz Dzy
        _ = ε := Ennreal.add_halves _
        
    exact mem_bUnion hy this
    

/-- In a complete space, the type of nonempty compact subsets is complete. This follows
from the same statement for closed subsets -/
instance NonemptyCompacts.complete_space [CompleteSpace α] : CompleteSpace (NonemptyCompacts α) :=
  (complete_space_iff_is_complete_range NonemptyCompacts.ToCloseds.uniform_embedding.to_uniform_inducing).2 <|
    NonemptyCompacts.is_closed_in_closeds.IsComplete

/-- In a compact space, the type of nonempty compact subsets is compact. This follows from
the same statement for closed subsets -/
instance NonemptyCompacts.compact_space [CompactSpace α] : CompactSpace (NonemptyCompacts α) :=
  ⟨by
    rw [nonempty_compacts.to_closeds.uniform_embedding.embedding.is_compact_iff_is_compact_image]
    rw [image_univ]
    exact nonempty_compacts.is_closed_in_closeds.is_compact⟩

/-- In a second countable space, the type of nonempty compact subsets is second countable -/
instance NonemptyCompacts.second_countable_topology [SecondCountableTopology α] :
    SecondCountableTopology (NonemptyCompacts α) := by
  have : separable_space (nonempty_compacts α) := by
    /- To obtain a countable dense subset of `nonempty_compacts α`, start from
        a countable dense subset `s` of α, and then consider all its finite nonempty subsets.
        This set is countable and made of nonempty compact sets. It turns out to be dense:
        by total boundedness, any compact set `t` can be covered by finitely many small balls, and
        approximations in `s` of the centers of these balls give the required finite approximation
        of `t`. -/
    rcases exists_countable_dense α with ⟨s, cs, s_dense⟩
    let v0 := { t : Set α | finite t ∧ t ⊆ s }
    let v : Set (nonempty_compacts α) := { t : nonempty_compacts α | (t : Set α) ∈ v0 }
    refine' ⟨⟨v, _, _⟩⟩
    · have : countable v0 := countable_set_of_finite_subset cs
      exact this.preimage SetLike.coe_injective
      
    · refine' fun t => mem_closure_iff.2 fun ε εpos => _
      -- t is a compact nonempty set, that we have to approximate uniformly by a a set in `v`.
      rcases exists_between εpos with ⟨δ, δpos, δlt⟩
      have δpos' : 0 < δ / 2 := Ennreal.half_pos δpos.ne'
      -- construct a map F associating to a point in α an approximating point in s, up to δ/2.
      have Exy : ∀ x, ∃ y, y ∈ s ∧ edist x y < δ / 2 := by
        intro x
        rcases mem_closure_iff.1 (s_dense x) (δ / 2) δpos' with ⟨y, ys, hy⟩
        exact ⟨y, ⟨ys, hy⟩⟩
      let F := fun x => some (Exy x)
      have Fspec : ∀ x, F x ∈ s ∧ edist x (F x) < δ / 2 := fun x => some_spec (Exy x)
      -- cover `t` with finitely many balls. Their centers form a set `a`
      have : TotallyBounded (t : Set α) := t.compact.totally_bounded
      rcases totally_bounded_iff.1 this (δ / 2) δpos' with ⟨a, af, ta⟩
      -- a : set α,  af : finite a,  ta : t ⊆ ⋃ (y : α) (H : y ∈ a), eball y (δ / 2)
      -- replace each center by a nearby approximation in `s`, giving a new set `b`
      let b := F '' a
      have : finite b := af.image _
      have tb : ∀, ∀ x ∈ t, ∀, ∃ y ∈ b, edist x y < δ := by
        intro x hx
        rcases mem_Union₂.1 (ta hx) with ⟨z, za, Dxz⟩
        exists F z, mem_image_of_mem _ za
        calc edist x (F z) ≤ edist x z + edist z (F z) := edist_triangle _ _ _ _ < δ / 2 + δ / 2 :=
            Ennreal.add_lt_add Dxz (Fspec z).2_ = δ := Ennreal.add_halves _
      -- keep only the points in `b` that are close to point in `t`, yielding a new set `c`
      let c := { y ∈ b | ∃ x ∈ t, edist x y < δ }
      have : finite c := ‹finite b›.Subset fun x hx => hx.1
      -- points in `t` are well approximated by points in `c`
      have tc : ∀, ∀ x ∈ t, ∀, ∃ y ∈ c, edist x y ≤ δ := by
        intro x hx
        rcases tb x hx with ⟨y, yv, Dxy⟩
        have : y ∈ c := by
          simp [c, -mem_image] <;> exact ⟨yv, ⟨x, hx, Dxy⟩⟩
        exact ⟨y, this, le_of_ltₓ Dxy⟩
      -- points in `c` are well approximated by points in `t`
      have ct : ∀, ∀ y ∈ c, ∀, ∃ x ∈ t, edist y x ≤ δ := by
        rintro y ⟨hy1, x, xt, Dyx⟩
        have : edist y x ≤ δ :=
          calc
            edist y x = edist x y := edist_comm _ _
            _ ≤ δ := le_of_ltₓ Dyx
            
        exact ⟨x, xt, this⟩
      -- it follows that their Hausdorff distance is small
      have : Hausdorff_edist (t : Set α) c ≤ δ := Hausdorff_edist_le_of_mem_edist Tc ct
      have Dtc : Hausdorff_edist (t : Set α) c < ε := this.trans_lt δlt
      -- the set `c` is not empty, as it is well approximated by a nonempty set
      have hc : c.nonempty := nonempty_of_Hausdorff_edist_ne_top t.nonempty (ne_top_of_lt Dtc)
      -- let `d` be the version of `c` in the type `nonempty_compacts α`
      let d : nonempty_compacts α := ⟨⟨c, ‹finite c›.IsCompact⟩, hc⟩
      have : c ⊆ s := by
        intro x hx
        rcases(mem_image _ _ _).1 hx.1 with ⟨y, ⟨ya, yx⟩⟩
        rw [← yx]
        exact (Fspec y).1
      have : d ∈ v := ⟨‹finite c›, this⟩
      -- we have proved that `d` is a good approximation of `t` as requested
      exact ⟨d, ‹d ∈ v›, Dtc⟩
      
  apply UniformSpace.second_countable_of_separable

end

--section
end Emetric

--namespace
namespace Metric

section

variable {α : Type u} [MetricSpace α]

/-- `nonempty_compacts α` inherits a metric space structure, as the Hausdorff
edistance between two such sets is finite. -/
instance NonemptyCompacts.metricSpace : MetricSpace (NonemptyCompacts α) :=
  EmetricSpace.toMetricSpace fun x y =>
    Hausdorff_edist_ne_top_of_nonempty_of_bounded x.Nonempty y.Nonempty x.compact.Bounded y.compact.Bounded

/-- The distance on `nonempty_compacts α` is the Hausdorff distance, by construction -/
theorem NonemptyCompacts.dist_eq {x y : NonemptyCompacts α} : dist x y = hausdorffDist (x : Set α) y :=
  rfl

theorem lipschitz_inf_dist_set (x : α) : LipschitzWith 1 fun s : NonemptyCompacts α => infDist x s :=
  LipschitzWith.of_le_add fun s t => by
    rw [dist_comm]
    exact inf_dist_le_inf_dist_add_Hausdorff_dist (edist_ne_top t s)

theorem lipschitz_inf_dist : LipschitzWith 2 fun p : α × NonemptyCompacts α => infDist p.1 p.2 :=
  @LipschitzWith.uncurry _ _ _ _ _ _ (fun s : NonemptyCompacts α => infDist x s) 1 1 (fun s => lipschitz_inf_dist_pt s)
    lipschitz_inf_dist_set

theorem uniform_continuous_inf_dist_Hausdorff_dist :
    UniformContinuous fun p : α × NonemptyCompacts α => infDist p.1 p.2 :=
  lipschitz_inf_dist.UniformContinuous

end

--section
end Metric

--namespace
