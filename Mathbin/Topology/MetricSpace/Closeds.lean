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

variable {α : Type u} [EmetricSpace α] {s : Set α}

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

-- error in Topology.MetricSpace.Closeds: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Subsets of a given closed subset form a closed set -/
theorem is_closed_subsets_of_is_closed (hs : is_closed s) : is_closed {t : closeds α | «expr ⊆ »(t.val, s)} :=
begin
  refine [expr is_closed_of_closure_subset (λ t ht x hx, _)],
  have [] [":", expr «expr ∈ »(x, closure s)] [],
  { refine [expr mem_closure_iff.2 (λ ε εpos, _)],
    rcases [expr mem_closure_iff.1 ht ε εpos, "with", "⟨", ident u, ",", ident hu, ",", ident Dtu, "⟩"],
    rcases [expr exists_edist_lt_of_Hausdorff_edist_lt hx Dtu, "with", "⟨", ident y, ",", ident hy, ",", ident Dxy, "⟩"],
    exact [expr ⟨y, hu hy, Dxy⟩] },
  rwa [expr hs.closure_eq] ["at", ident this]
end

/-- By definition, the edistance on `closeds α` is given by the Hausdorff edistance -/
theorem closeds.edist_eq {s t : closeds α} : edist s t = Hausdorff_edist s.val t.val :=
  rfl

-- error in Topology.MetricSpace.Closeds: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In a complete space, the type of closed subsets is complete for the
Hausdorff edistance. -/ instance closeds.complete_space [complete_space α] : complete_space (closeds α) :=
begin
  let [ident B] [":", expr exprℕ() → «exprℝ≥0∞»()] [":=", expr λ n, «expr ^ »(«expr ⁻¹»(2), n)],
  have [ident B_pos] [":", expr ∀ n, «expr < »((0 : «exprℝ≥0∞»()), B n)] [],
  by simp [] [] [] ["[", expr B, ",", expr ennreal.pow_pos, "]"] [] [],
  have [ident B_ne_top] [":", expr ∀ n, «expr ≠ »(B n, «expr⊤»())] [],
  by simp [] [] [] ["[", expr B, ",", expr ennreal.pow_ne_top, "]"] [] [],
  refine [expr complete_of_convergent_controlled_sequences B B_pos (λ s hs, _)],
  let [ident t0] [] [":=", expr «expr⋂ , »((n), closure «expr⋃ , »((m «expr ≥ » n), (s m).val))],
  let [ident t] [":", expr closeds α] [":=", expr ⟨t0, is_closed_Inter (λ _, is_closed_closure)⟩],
  use [expr t],
  have [ident I1] [":", expr ∀
   n : exprℕ(), ∀ x «expr ∈ » (s n).val, «expr∃ , »((y «expr ∈ » t0), «expr ≤ »(edist x y, «expr * »(2, B n)))] [],
  { assume [binders (n x hx)],
    obtain ["⟨", ident z, ",", ident hz₀, ",", ident hz, "⟩", ":", expr «expr∃ , »((z : ∀
       l, (s «expr + »(n, l)).val), «expr ∧ »(«expr = »((z 0 : α), x), ∀
       k, «expr ≤ »(edist (z k : α) (z «expr + »(k, 1) : α), «expr / »(B n, «expr ^ »(2, k)))))],
    { have [] [":", expr ∀
       (l : exprℕ())
       (z : (s «expr + »(n, l)).val), «expr∃ , »((z' : (s «expr + »(«expr + »(n, l), 1)).val), «expr ≤ »(edist (z : α) z', «expr / »(B n, «expr ^ »(2, l))))] [],
      { assume [binders (l z)],
        obtain ["⟨", ident z', ",", ident z'_mem, ",", ident hz', "⟩", ":", expr «expr∃ , »((z' «expr ∈ » (s «expr + »(«expr + »(n, l), 1)).val), «expr < »(edist (z : α) z', «expr / »(B n, «expr ^ »(2, l))))],
        { apply [expr exists_edist_lt_of_Hausdorff_edist_lt z.2],
          simp [] [] ["only"] ["[", expr B, ",", expr ennreal.inv_pow, ",", expr div_eq_mul_inv, "]"] [] [],
          rw ["[", "<-", expr pow_add, "]"] [],
          apply [expr hs]; simp [] [] [] [] [] [] },
        exact [expr ⟨⟨z', z'_mem⟩, le_of_lt hz'⟩] },
      use ["[", expr λ k, nat.rec_on k ⟨x, hx⟩ (λ l z, some (this l z)), ",", expr rfl, "]"],
      exact [expr λ k, some_spec (this k _)] },
    have [] [":", expr cauchy_seq (λ k, (z k : α))] [],
    from [expr cauchy_seq_of_edist_le_geometric_two (B n) (B_ne_top n) hz],
    rcases [expr cauchy_seq_tendsto_of_complete this, "with", "⟨", ident y, ",", ident y_lim, "⟩"],
    use [expr y],
    have [] [":", expr «expr ∈ »(y, t0)] [":=", expr mem_Inter.2 (λ
      k, mem_closure_of_tendsto y_lim (begin
         simp [] [] ["only"] ["[", expr exists_prop, ",", expr set.mem_Union, ",", expr filter.eventually_at_top, ",", expr set.mem_preimage, ",", expr set.preimage_Union, "]"] [] [],
         exact [expr ⟨k, λ m hm, ⟨«expr + »(n, m), «expr ▸ »(zero_add k, add_le_add (zero_le n) hm), (z m).2⟩⟩]
       end))],
    use [expr this],
    rw ["[", "<-", expr hz₀, "]"] [],
    exact [expr edist_le_of_edist_le_geometric_two_of_tendsto₀ (B n) hz y_lim] },
  have [ident I2] [":", expr ∀
   n : exprℕ(), ∀ x «expr ∈ » t0, «expr∃ , »((y «expr ∈ » (s n).val), «expr ≤ »(edist x y, «expr * »(2, B n)))] [],
  { assume [binders (n x xt0)],
    have [] [":", expr «expr ∈ »(x, closure «expr⋃ , »((m «expr ≥ » n), (s m).val))] [],
    by apply [expr mem_Inter.1 xt0 n],
    rcases [expr mem_closure_iff.1 this (B n) (B_pos n), "with", "⟨", ident z, ",", ident hz, ",", ident Dxz, "⟩"],
    simp [] [] ["only"] ["[", expr exists_prop, ",", expr set.mem_Union, "]"] [] ["at", ident hz],
    rcases [expr hz, "with", "⟨", ident m, ",", "⟨", ident m_ge_n, ",", ident hm, "⟩", "⟩"],
    have [] [":", expr «expr < »(Hausdorff_edist (s m).val (s n).val, B n)] [":=", expr hs n m n m_ge_n (le_refl n)],
    rcases [expr exists_edist_lt_of_Hausdorff_edist_lt hm this, "with", "⟨", ident y, ",", ident hy, ",", ident Dzy, "⟩"],
    exact [expr ⟨y, hy, calc
        «expr ≤ »(edist x y, «expr + »(edist x z, edist z y)) : edist_triangle _ _ _
        «expr ≤ »(..., «expr + »(B n, B n)) : add_le_add (le_of_lt Dxz) (le_of_lt Dzy)
        «expr = »(..., «expr * »(2, B n)) : (two_mul _).symm⟩] },
  have [ident main] [":", expr ∀
   n : exprℕ(), «expr ≤ »(edist (s n) t, «expr * »(2, B n))] [":=", expr λ
   n, Hausdorff_edist_le_of_mem_edist (I1 n) (I2 n)],
  refine [expr tendsto_at_top.2 (λ ε εpos, _)],
  have [] [":", expr tendsto (λ n, «expr * »(2, B n)) at_top (expr𝓝() «expr * »(2, 0))] [],
  from [expr ennreal.tendsto.const_mul «expr $ »(ennreal.tendsto_pow_at_top_nhds_0_of_lt_1, by simp [] [] [] ["[", expr ennreal.one_lt_two, "]"] [] []) «expr $ »(or.inr, by simp [] [] [] [] [] [])],
  rw [expr mul_zero] ["at", ident this],
  obtain ["⟨", ident N, ",", ident hN, "⟩", ":", expr «expr∃ , »((N), ∀
    b «expr ≥ » N, «expr > »(ε, «expr * »(2, B b)))],
  from [expr ((tendsto_order.1 this).2 ε εpos).exists_forall_of_at_top],
  exact [expr ⟨N, λ n hn, lt_of_le_of_lt (main n) (hN n hn)⟩]
end

-- error in Topology.MetricSpace.Closeds: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In a compact space, the type of closed subsets is compact. -/
instance closeds.compact_space [compact_space α] : compact_space (closeds α) :=
⟨begin
   refine [expr compact_of_totally_bounded_is_closed (emetric.totally_bounded_iff.2 (λ ε εpos, _)) is_closed_univ],
   rcases [expr exists_between εpos, "with", "⟨", ident δ, ",", ident δpos, ",", ident δlt, "⟩"],
   rcases [expr emetric.totally_bounded_iff.1 (compact_iff_totally_bounded_complete.1 (@compact_univ α _ _)).1 δ δpos, "with", "⟨", ident s, ",", ident fs, ",", ident hs, "⟩"],
   have [ident main] [":", expr ∀ u : set α, «expr∃ , »((v «expr ⊆ » s), «expr ≤ »(Hausdorff_edist u v, δ))] [],
   { assume [binders (u)],
     let [ident v] [] [":=", expr {x : α | «expr ∧ »(«expr ∈ »(x, s), «expr∃ , »((y «expr ∈ » u), «expr < »(edist x y, δ)))}],
     existsi ["[", expr v, ",", expr (λ x hx, hx.1 : «expr ⊆ »(v, s)), "]"],
     refine [expr Hausdorff_edist_le_of_mem_edist _ _],
     { assume [binders (x hx)],
       have [] [":", expr «expr ∈ »(x, «expr⋃ , »((y «expr ∈ » s), ball y δ))] [":=", expr hs (by simp [] [] [] [] [] [])],
       rcases [expr mem_bUnion_iff.1 this, "with", "⟨", ident y, ",", ident ys, ",", ident dy, "⟩"],
       have [] [":", expr «expr < »(edist y x, δ)] [":=", expr by simp [] [] [] [] [] ["at", ident dy]; rwa ["[", expr edist_comm, "]"] ["at", ident dy]],
       exact [expr ⟨y, ⟨ys, ⟨x, hx, this⟩⟩, le_of_lt dy⟩] },
     { rintros [ident x, "⟨", ident hx1, ",", "⟨", ident y, ",", ident yu, ",", ident hy, "⟩", "⟩"],
       exact [expr ⟨y, yu, le_of_lt hy⟩] } },
   let [ident F] [] [":=", expr {f : closeds α | «expr ⊆ »(f.val, s)}],
   use [expr F],
   split,
   { apply [expr @finite_of_finite_image _ _ F (λ f, f.val)],
     { exact [expr subtype.val_injective.inj_on F] },
     { refine [expr fs.finite_subsets.subset (λ b, _)],
       simp [] [] ["only"] ["[", expr and_imp, ",", expr set.mem_image, ",", expr set.mem_set_of_eq, ",", expr exists_imp_distrib, "]"] [] [],
       assume [binders (x hx hx')],
       rwa [expr hx'] ["at", ident hx] } },
   { assume [binders (u _)],
     rcases [expr main u.val, "with", "⟨", ident t0, ",", ident t0s, ",", ident Dut0, "⟩"],
     have [] [":", expr is_closed t0] [":=", expr (fs.subset t0s).is_compact.is_closed],
     let [ident t] [":", expr closeds α] [":=", expr ⟨t0, this⟩],
     have [] [":", expr «expr ∈ »(t, F)] [":=", expr t0s],
     have [] [":", expr «expr < »(edist u t, ε)] [":=", expr lt_of_le_of_lt Dut0 δlt],
     apply [expr mem_bUnion_iff.2],
     exact [expr ⟨t, «expr‹ ›»(«expr ∈ »(t, F)), this⟩] }
 end⟩

-- error in Topology.MetricSpace.Closeds: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In an emetric space, the type of non-empty compact subsets is an emetric space,
where the edistance is the Hausdorff edistance -/
instance nonempty_compacts.emetric_space : emetric_space (nonempty_compacts α) :=
{ edist := λ s t, Hausdorff_edist s.val t.val,
  edist_self := λ s, Hausdorff_edist_self,
  edist_comm := λ s t, Hausdorff_edist_comm,
  edist_triangle := λ s t u, Hausdorff_edist_triangle,
  eq_of_edist_eq_zero := λ
  s
  t
  h, «expr $ »(subtype.eq, begin
     have [] [":", expr «expr = »(closure s.val, closure t.val)] [":=", expr Hausdorff_edist_zero_iff_closure_eq_closure.1 h],
     rwa ["[", expr s.property.2.is_closed.closure_eq, ",", expr t.property.2.is_closed.closure_eq, "]"] ["at", ident this]
   end) }

/-- `nonempty_compacts.to_closeds` is a uniform embedding (as it is an isometry) -/
theorem nonempty_compacts.to_closeds.uniform_embedding : UniformEmbedding (@nonempty_compacts.to_closeds α _ _) :=
  Isometry.uniform_embedding$ fun x y => rfl

-- error in Topology.MetricSpace.Closeds: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The range of `nonempty_compacts.to_closeds` is closed in a complete space -/
theorem nonempty_compacts.is_closed_in_closeds
[complete_space α] : is_closed «expr $ »(range, @nonempty_compacts.to_closeds α _ _) :=
begin
  have [] [":", expr «expr = »(range nonempty_compacts.to_closeds, {s : closeds α | «expr ∧ »(s.val.nonempty, is_compact s.val)})] [],
  from [expr range_inclusion _],
  rw [expr this] [],
  refine [expr is_closed_of_closure_subset (λ s hs, ⟨_, _⟩)],
  { rcases [expr mem_closure_iff.1 hs «expr⊤»() ennreal.coe_lt_top, "with", "⟨", ident t, ",", ident ht, ",", ident Dst, "⟩"],
    rw [expr edist_comm] ["at", ident Dst],
    exact [expr nonempty_of_Hausdorff_edist_ne_top ht.1 (ne_of_lt Dst)] },
  { refine [expr compact_iff_totally_bounded_complete.2 ⟨_, s.property.is_complete⟩],
    refine [expr totally_bounded_iff.2 (λ (ε) (εpos : «expr < »(0, ε)), _)],
    rcases [expr mem_closure_iff.1 hs «expr / »(ε, 2) (ennreal.half_pos εpos.ne'), "with", "⟨", ident t, ",", ident ht, ",", ident Dst, "⟩"],
    rcases [expr totally_bounded_iff.1 (compact_iff_totally_bounded_complete.1 ht.2).1 «expr / »(ε, 2) (ennreal.half_pos εpos.ne'), "with", "⟨", ident u, ",", ident fu, ",", ident ut, "⟩"],
    refine [expr ⟨u, ⟨fu, λ x hx, _⟩⟩],
    rcases [expr exists_edist_lt_of_Hausdorff_edist_lt hx Dst, "with", "⟨", ident z, ",", ident hz, ",", ident Dxz, "⟩"],
    rcases [expr mem_bUnion_iff.1 (ut hz), "with", "⟨", ident y, ",", ident hy, ",", ident Dzy, "⟩"],
    have [] [":", expr «expr < »(edist x y, ε)] [":=", expr calc
       «expr ≤ »(edist x y, «expr + »(edist x z, edist z y)) : edist_triangle _ _ _
       «expr < »(..., «expr + »(«expr / »(ε, 2), «expr / »(ε, 2))) : ennreal.add_lt_add Dxz Dzy
       «expr = »(..., ε) : ennreal.add_halves _],
    exact [expr mem_bUnion hy this] }
end

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

-- error in Topology.MetricSpace.Closeds: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In a second countable space, the type of nonempty compact subsets is second countable -/
instance nonempty_compacts.second_countable_topology
[second_countable_topology α] : second_countable_topology (nonempty_compacts α) :=
begin
  haveI [] [":", expr separable_space (nonempty_compacts α)] [":=", expr begin
     rcases [expr exists_countable_dense α, "with", "⟨", ident s, ",", ident cs, ",", ident s_dense, "⟩"],
     let [ident v0] [] [":=", expr {t : set α | «expr ∧ »(finite t, «expr ⊆ »(t, s))}],
     let [ident v] [":", expr set (nonempty_compacts α)] [":=", expr {t : nonempty_compacts α | «expr ∈ »(t.val, v0)}],
     refine [expr ⟨⟨v, ⟨_, _⟩⟩⟩],
     { have [] [":", expr countable v0] [],
       from [expr countable_set_of_finite_subset cs],
       exact [expr this.preimage subtype.coe_injective] },
     { refine [expr λ t, mem_closure_iff.2 (λ ε εpos, _)],
       rcases [expr exists_between εpos, "with", "⟨", ident δ, ",", ident δpos, ",", ident δlt, "⟩"],
       have [ident δpos'] [":", expr «expr < »(0, «expr / »(δ, 2))] [],
       from [expr ennreal.half_pos δpos.ne'],
       have [ident Exy] [":", expr ∀
        x, «expr∃ , »((y), «expr ∧ »(«expr ∈ »(y, s), «expr < »(edist x y, «expr / »(δ, 2))))] [],
       { assume [binders (x)],
         rcases [expr mem_closure_iff.1 (s_dense x) «expr / »(δ, 2) δpos', "with", "⟨", ident y, ",", ident ys, ",", ident hy, "⟩"],
         exact [expr ⟨y, ⟨ys, hy⟩⟩] },
       let [ident F] [] [":=", expr λ x, some (Exy x)],
       have [ident Fspec] [":", expr ∀
        x, «expr ∧ »(«expr ∈ »(F x, s), «expr < »(edist x (F x), «expr / »(δ, 2)))] [":=", expr λ x, some_spec (Exy x)],
       have [] [":", expr totally_bounded t.val] [":=", expr t.property.2.totally_bounded],
       rcases [expr totally_bounded_iff.1 this «expr / »(δ, 2) δpos', "with", "⟨", ident a, ",", ident af, ",", ident ta, "⟩"],
       let [ident b] [] [":=", expr «expr '' »(F, a)],
       have [] [":", expr finite b] [":=", expr af.image _],
       have [ident tb] [":", expr ∀ x «expr ∈ » t.val, «expr∃ , »((y «expr ∈ » b), «expr < »(edist x y, δ))] [],
       { assume [binders (x hx)],
         rcases [expr mem_bUnion_iff.1 (ta hx), "with", "⟨", ident z, ",", ident za, ",", ident Dxz, "⟩"],
         existsi ["[", expr F z, ",", expr mem_image_of_mem _ za, "]"],
         calc
           «expr ≤ »(edist x (F z), «expr + »(edist x z, edist z (F z))) : edist_triangle _ _ _
           «expr < »(..., «expr + »(«expr / »(δ, 2), «expr / »(δ, 2))) : ennreal.add_lt_add Dxz (Fspec z).2
           «expr = »(..., δ) : ennreal.add_halves _ },
       let [ident c] [] [":=", expr {y ∈ b | «expr∃ , »((x «expr ∈ » t.val), «expr < »(edist x y, δ))}],
       have [] [":", expr finite c] [":=", expr «expr‹ ›»(finite b).subset (λ x hx, hx.1)],
       have [ident tc] [":", expr ∀ x «expr ∈ » t.val, «expr∃ , »((y «expr ∈ » c), «expr ≤ »(edist x y, δ))] [],
       { assume [binders (x hx)],
         rcases [expr tb x hx, "with", "⟨", ident y, ",", ident yv, ",", ident Dxy, "⟩"],
         have [] [":", expr «expr ∈ »(y, c)] [":=", expr by simp [] [] [] ["[", expr c, ",", "-", ident mem_image, "]"] [] []; exact [expr ⟨yv, ⟨x, hx, Dxy⟩⟩]],
         exact [expr ⟨y, this, le_of_lt Dxy⟩] },
       have [ident ct] [":", expr ∀ y «expr ∈ » c, «expr∃ , »((x «expr ∈ » t.val), «expr ≤ »(edist y x, δ))] [],
       { rintros [ident y, "⟨", ident hy1, ",", "⟨", ident x, ",", ident xt, ",", ident Dyx, "⟩", "⟩"],
         have [] [":", expr «expr ≤ »(edist y x, δ)] [":=", expr calc
            «expr = »(edist y x, edist x y) : edist_comm _ _
            «expr ≤ »(..., δ) : le_of_lt Dyx],
         exact [expr ⟨x, xt, this⟩] },
       have [] [":", expr «expr ≤ »(Hausdorff_edist t.val c, δ)] [":=", expr Hausdorff_edist_le_of_mem_edist tc ct],
       have [ident Dtc] [":", expr «expr < »(Hausdorff_edist t.val c, ε)] [":=", expr lt_of_le_of_lt this δlt],
       have [ident hc] [":", expr c.nonempty] [],
       from [expr nonempty_of_Hausdorff_edist_ne_top t.property.1 (ne_top_of_lt Dtc)],
       let [ident d] [":", expr nonempty_compacts α] [":=", expr ⟨c, ⟨hc, «expr‹ ›»(finite c).is_compact⟩⟩],
       have [] [":", expr «expr ⊆ »(c, s)] [],
       { assume [binders (x hx)],
         rcases [expr (mem_image _ _ _).1 hx.1, "with", "⟨", ident y, ",", "⟨", ident ya, ",", ident yx, "⟩", "⟩"],
         rw ["<-", expr yx] [],
         exact [expr (Fspec y).1] },
       have [] [":", expr «expr ∈ »(d, v)] [":=", expr ⟨«expr‹ ›»(finite c), this⟩],
       exact [expr ⟨d, «expr‹ ›»(«expr ∈ »(d, v)), Dtc⟩] }
   end],
  apply [expr uniform_space.second_countable_of_separable]
end

end 

end Emetric

namespace Metric

section 

variable {α : Type u} [MetricSpace α]

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

