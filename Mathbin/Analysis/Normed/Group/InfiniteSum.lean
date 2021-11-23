import Mathbin.Analysis.Normed.Group.Basic 
import Mathbin.Topology.Instances.Nnreal

/-!
# Infinite sums in (semi)normed groups

In a complete (semi)normed group,

- `summable_iff_vanishing_norm`: a series `∑' i, f i` is summable if and only if for any `ε > 0`,
  there exists a finite set `s` such that the sum `∑ i in t, f i` over any finite set `t` disjoint
  with `s` has norm less than `ε`;

- `summable_of_norm_bounded`, `summable_of_norm_bounded_eventually`: if `∥f i∥` is bounded above by
  a summable series `∑' i, g i`, then `∑' i, f i` is summable as well; the same is true if the
  inequality hold only off some finite set.

- `tsum_of_norm_bounded`, `has_sum.norm_le_of_bounded`: if `∥f i∥ ≤ g i`, where `∑' i, g i` is a
  summable series, then `∥∑' i, f i∥ ≤ ∑' i, g i`.

## Tags

infinite series, absolute convergence, normed group
-/


open_locale Classical BigOperators TopologicalSpace Nnreal

open Finset Filter Metric

variable{ι α E F : Type _}[SemiNormedGroup E][SemiNormedGroup F]

theorem cauchy_seq_finset_iff_vanishing_norm {f : ι → E} :
  (CauchySeq fun s : Finset ι => ∑i in s, f i) ↔
    ∀ ε _ : ε > (0 : ℝ), ∃ s : Finset ι, ∀ t, Disjoint t s → ∥∑i in t, f i∥ < ε :=
  by 
    rw [cauchy_seq_finset_iff_vanishing, nhds_basis_ball.forall_iff]
    ·
      simp only [ball_zero_eq, Set.mem_set_of_eq]
    ·
      rintro s t hst ⟨s', hs'⟩
      exact ⟨s', fun t' ht' => hst$ hs' _ ht'⟩

theorem summable_iff_vanishing_norm [CompleteSpace E] {f : ι → E} :
  Summable f ↔ ∀ ε _ : ε > (0 : ℝ), ∃ s : Finset ι, ∀ t, Disjoint t s → ∥∑i in t, f i∥ < ε :=
  by 
    rw [summable_iff_cauchy_seq_finset, cauchy_seq_finset_iff_vanishing_norm]

-- error in Analysis.Normed.Group.InfiniteSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cauchy_seq_finset_of_norm_bounded_eventually
{f : ι → E}
{g : ι → exprℝ()}
(hg : summable g)
(h : «expr∀ᶠ in , »((i), cofinite, «expr ≤ »(«expr∥ ∥»(f i), g i))) : cauchy_seq (λ s, «expr∑ in , »((i), s, f i)) :=
begin
  refine [expr cauchy_seq_finset_iff_vanishing_norm.2 (λ ε hε, _)],
  rcases [expr summable_iff_vanishing_norm.1 hg ε hε, "with", "⟨", ident s, ",", ident hs, "⟩"],
  refine [expr ⟨«expr ∪ »(s, h.to_finset), λ t ht, _⟩],
  have [] [":", expr ∀ i «expr ∈ » t, «expr ≤ »(«expr∥ ∥»(f i), g i)] [],
  { intros [ident i, ident hi],
    simp [] [] ["only"] ["[", expr disjoint_left, ",", expr mem_union, ",", expr not_or_distrib, ",", expr h.mem_to_finset, ",", expr set.mem_compl_iff, ",", expr not_not, "]"] [] ["at", ident ht],
    exact [expr (ht hi).2] },
  calc
    «expr ≤ »(«expr∥ ∥»(«expr∑ in , »((i), t, f i)), «expr∑ in , »((i), t, g i)) : norm_sum_le_of_le _ this
    «expr ≤ »(..., «expr∥ ∥»(«expr∑ in , »((i), t, g i))) : le_abs_self _
    «expr < »(..., ε) : hs _ (ht.mono_right le_sup_left)
end

theorem cauchy_seq_finset_of_norm_bounded {f : ι → E} (g : ι → ℝ) (hg : Summable g) (h : ∀ i, ∥f i∥ ≤ g i) :
  CauchySeq fun s : Finset ι => ∑i in s, f i :=
  cauchy_seq_finset_of_norm_bounded_eventually hg$ eventually_of_forall h

theorem cauchy_seq_finset_of_summable_norm {f : ι → E} (hf : Summable fun a => ∥f a∥) :
  CauchySeq fun s : Finset ι => ∑a in s, f a :=
  cauchy_seq_finset_of_norm_bounded _ hf fun i => le_reflₓ _

/-- If a function `f` is summable in norm, and along some sequence of finsets exhausting the space
its sum is converging to a limit `a`, then this holds along all finsets, i.e., `f` is summable
with sum `a`. -/
theorem has_sum_of_subseq_of_summable {f : ι → E} (hf : Summable fun a => ∥f a∥) {s : α → Finset ι} {p : Filter α}
  [ne_bot p] (hs : tendsto s p at_top) {a : E} (ha : tendsto (fun b => ∑i in s b, f i) p (𝓝 a)) : HasSum f a :=
  tendsto_nhds_of_cauchy_seq_of_subseq (cauchy_seq_finset_of_summable_norm hf) hs ha

theorem has_sum_iff_tendsto_nat_of_summable_norm {f : ℕ → E} {a : E} (hf : Summable fun i => ∥f i∥) :
  HasSum f a ↔ tendsto (fun n : ℕ => ∑i in range n, f i) at_top (𝓝 a) :=
  ⟨fun h => h.tendsto_sum_nat, fun h => has_sum_of_subseq_of_summable hf tendsto_finset_range h⟩

/-- The direct comparison test for series:  if the norm of `f` is bounded by a real function `g`
which is summable, then `f` is summable. -/
theorem summable_of_norm_bounded [CompleteSpace E] {f : ι → E} (g : ι → ℝ) (hg : Summable g) (h : ∀ i, ∥f i∥ ≤ g i) :
  Summable f :=
  by 
    rw [summable_iff_cauchy_seq_finset]
    exact cauchy_seq_finset_of_norm_bounded g hg h

theorem HasSum.norm_le_of_bounded {f : ι → E} {g : ι → ℝ} {a : E} {b : ℝ} (hf : HasSum f a) (hg : HasSum g b)
  (h : ∀ i, ∥f i∥ ≤ g i) : ∥a∥ ≤ b :=
  le_of_tendsto_of_tendsto' hf.norm hg$ fun s => norm_sum_le_of_le _$ fun i hi => h i

/-- Quantitative result associated to the direct comparison test for series:  If `∑' i, g i` is
summable, and for all `i`, `∥f i∥ ≤ g i`, then `∥∑' i, f i∥ ≤ ∑' i, g i`. Note that we do not
assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete space. -/
theorem tsum_of_norm_bounded {f : ι → E} {g : ι → ℝ} {a : ℝ} (hg : HasSum g a) (h : ∀ i, ∥f i∥ ≤ g i) :
  ∥∑'i : ι, f i∥ ≤ a :=
  by 
    byCases' hf : Summable f
    ·
      exact hf.has_sum.norm_le_of_bounded hg h
    ·
      rw [tsum_eq_zero_of_not_summable hf, norm_zero]
      exact ge_of_tendsto' hg fun s => sum_nonneg$ fun i hi => (norm_nonneg _).trans (h i)

/-- If `∑' i, ∥f i∥` is summable, then `∥∑' i, f i∥ ≤ (∑' i, ∥f i∥)`. Note that we do not assume
that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete space. -/
theorem norm_tsum_le_tsum_norm {f : ι → E} (hf : Summable fun i => ∥f i∥) : ∥∑'i, f i∥ ≤ ∑'i, ∥f i∥ :=
  tsum_of_norm_bounded hf.has_sum$ fun i => le_rfl

/-- Quantitative result associated to the direct comparison test for series: If `∑' i, g i` is
summable, and for all `i`, `∥f i∥₊ ≤ g i`, then `∥∑' i, f i∥₊ ≤ ∑' i, g i`. Note that we
do not assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete
space. -/
theorem tsum_of_nnnorm_bounded {f : ι → E} {g : ι →  ℝ≥0 } {a :  ℝ≥0 } (hg : HasSum g a) (h : ∀ i, ∥f i∥₊ ≤ g i) :
  ∥∑'i : ι, f i∥₊ ≤ a :=
  by 
    simp only [←Nnreal.coe_le_coe, ←Nnreal.has_sum_coe, coe_nnnorm] at *
    exact tsum_of_norm_bounded hg h

/-- If `∑' i, ∥f i∥₊` is summable, then `∥∑' i, f i∥₊ ≤ ∑' i, ∥f i∥₊`. Note that
we do not assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete
space. -/
theorem nnnorm_tsum_le {f : ι → E} (hf : Summable fun i => ∥f i∥₊) : ∥∑'i, f i∥₊ ≤ ∑'i, ∥f i∥₊ :=
  tsum_of_nnnorm_bounded hf.has_sum fun i => le_rfl

variable[CompleteSpace E]

/-- Variant of the direct comparison test for series:  if the norm of `f` is eventually bounded by a
real function `g` which is summable, then `f` is summable. -/
theorem summable_of_norm_bounded_eventually {f : ι → E} (g : ι → ℝ) (hg : Summable g)
  (h : ∀ᶠi in cofinite, ∥f i∥ ≤ g i) : Summable f :=
  summable_iff_cauchy_seq_finset.2$ cauchy_seq_finset_of_norm_bounded_eventually hg h

theorem summable_of_nnnorm_bounded {f : ι → E} (g : ι →  ℝ≥0 ) (hg : Summable g) (h : ∀ i, ∥f i∥₊ ≤ g i) : Summable f :=
  summable_of_norm_bounded (fun i => (g i : ℝ)) (Nnreal.summable_coe.2 hg)
    fun i =>
      by 
        exactModCast h i

theorem summable_of_summable_norm {f : ι → E} (hf : Summable fun a => ∥f a∥) : Summable f :=
  summable_of_norm_bounded _ hf fun i => le_reflₓ _

theorem summable_of_summable_nnnorm {f : ι → E} (hf : Summable fun a => ∥f a∥₊) : Summable f :=
  summable_of_nnnorm_bounded _ hf fun i => le_reflₓ _

