import Mathbin.MeasureTheory.Constructions.BorelSpace 
import Mathbin.Dynamics.Ergodic.MeasurePreserving 
import Mathbin.Combinatorics.Pigeonhole

/-!
# Conservative systems

In this file we define `f : α → α` to be a *conservative* system w.r.t a measure `μ` if `f` is
non-singular (`measure_theory.quasi_measure_preserving`) and for every measurable set `s` of
positive measure at least one point `x ∈ s` returns back to `s` after some number of iterations of
`f`. There are several properties that look like they are stronger than this one but actually follow
from it:

* `measure_theory.conservative.frequently_measure_inter_ne_zero`,
  `measure_theory.conservative.exists_gt_measure_inter_ne_zero`: if `μ s ≠ 0`, then for infinitely
  many `n`, the measure of `s ∩ (f^[n]) ⁻¹' s` is positive.

* `measure_theory.conservative.measure_mem_forall_ge_image_not_mem_eq_zero`,
  `measure_theory.conservative.ae_mem_imp_frequently_image_mem`: a.e. every point of `s` visits `s`
  infinitely many times (Poincaré recurrence theorem).

We also prove the topological Poincaré recurrence theorem
`measure_theory.conservative.ae_frequently_mem_of_mem_nhds`. Let `f : α → α` be a conservative
dynamical system on a topological space with second countable topology and measurable open
sets. Then almost every point `x : α` is recurrent: it visits every neighborhood `s ∈ 𝓝 x`
infinitely many times.

## Tags

conservative dynamical system, Poincare recurrence theorem
-/


noncomputable theory

open Classical Set Filter MeasureTheory Finset Function TopologicalSpace

open_locale Classical TopologicalSpace

variable {ι : Type _} {α : Type _} [MeasurableSpace α] {f : α → α} {s : Set α} {μ : Measureₓ α}

namespace MeasureTheory

open Measureₓ

/-- We say that a non-singular (`measure_theory.quasi_measure_preserving`) self-map is
*conservative* if for any measurable set `s` of positive measure there exists `x ∈ s` such that `x`
returns back to `s` under some iteration of `f`. -/
structure conservative (f : α → α)
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac) extends
  quasi_measure_preserving f μ μ : Prop where 
  exists_mem_image_mem : ∀ ⦃s⦄, MeasurableSet s → μ s ≠ 0 → ∃ (x : _)(_ : x ∈ s)(m : _)(_ : m ≠ 0), (f^[m]) x ∈ s

/-- A self-map preserving a finite measure is conservative. -/
protected theorem measure_preserving.conservative [is_finite_measure μ] (h : measure_preserving f μ μ) :
  conservative f μ :=
  ⟨h.quasi_measure_preserving, fun s hsm h0 => h.exists_mem_image_mem hsm h0⟩

namespace Conservative

/-- The identity map is conservative w.r.t. any measure. -/
protected theorem id (μ : Measureₓ α) : conservative id μ :=
  { to_quasi_measure_preserving := quasi_measure_preserving.id μ,
    exists_mem_image_mem :=
      fun s hs h0 =>
        let ⟨x, hx⟩ := nonempty_of_measure_ne_zero h0
        ⟨x, hx, 1, one_ne_zero, hx⟩ }

-- error in Dynamics.Ergodic.Conservative: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` is a conservative map and `s` is a measurable set of nonzero measure, then
for infinitely many values of `m` a positive measure of points `x ∈ s` returns back to `s`
after `m` iterations of `f`. -/
theorem frequently_measure_inter_ne_zero
(hf : conservative f μ)
(hs : measurable_set s)
(h0 : «expr ≠ »(μ s, 0)) : «expr∃ᶠ in , »((m), at_top, «expr ≠ »(μ «expr ∩ »(s, «expr ⁻¹' »(«expr ^[ ]»(f, m), s)), 0)) :=
begin
  by_contra [ident H],
  simp [] [] ["only"] ["[", expr not_frequently, ",", expr eventually_at_top, ",", expr ne.def, ",", expr not_not, "]"] [] ["at", ident H],
  rcases [expr H, "with", "⟨", ident N, ",", ident hN, "⟩"],
  induction [expr N] [] ["with", ident N, ident ihN] [],
  { apply [expr h0],
    simpa [] [] [] [] [] ["using", expr hN 0 le_rfl] },
  rw ["[", expr imp_false, "]"] ["at", ident ihN],
  push_neg ["at", ident ihN],
  rcases [expr ihN, "with", "⟨", ident n, ",", ident hn, ",", ident hμn, "⟩"],
  set [] [ident T] [] [":="] [expr «expr ∩ »(s, «expr⋃ , »((n «expr ≥ » «expr + »(N, 1)), «expr ⁻¹' »(«expr ^[ ]»(f, n), s)))] [],
  have [ident hT] [":", expr measurable_set T] [],
  from [expr hs.inter (measurable_set.bUnion (countable_encodable _) (λ _ _, hf.measurable.iterate _ hs))],
  have [ident hμT] [":", expr «expr = »(μ T, 0)] [],
  { convert [] [expr «expr $ »(measure_bUnion_null_iff, countable_encodable _).2 hN] [],
    rw ["<-", expr set.inter_bUnion] [],
    refl },
  have [] [":", expr «expr ≠ »(μ «expr \ »(«expr ∩ »(s, «expr ⁻¹' »(«expr ^[ ]»(f, n), s)), T), 0)] [],
  by rwa ["[", expr measure_diff_null hμT, "]"] [],
  rcases [expr hf.exists_mem_image_mem ((hs.inter (hf.measurable.iterate n hs)).diff hT) this, "with", "⟨", ident x, ",", "⟨", "⟨", ident hxs, ",", ident hxn, "⟩", ",", ident hxT, "⟩", ",", ident m, ",", ident hm0, ",", "⟨", ident hxms, ",", ident hxm, "⟩", ",", ident hxx, "⟩"],
  refine [expr hxT ⟨hxs, mem_bUnion_iff.2 ⟨«expr + »(n, m), _, _⟩⟩],
  { exact [expr add_le_add hn «expr $ »(nat.one_le_of_lt, pos_iff_ne_zero.2 hm0)] },
  { rwa ["[", expr set.mem_preimage, ",", "<-", expr iterate_add_apply, "]"] ["at", ident hxm] }
end

/-- If `f` is a conservative map and `s` is a measurable set of nonzero measure, then
for an arbitrarily large `m` a positive measure of points `x ∈ s` returns back to `s`
after `m` iterations of `f`. -/
theorem exists_gt_measure_inter_ne_zero (hf : conservative f μ) (hs : MeasurableSet s) (h0 : μ s ≠ 0) (N : ℕ) :
  ∃ (m : _)(_ : m > N), μ (s ∩ f^[m] ⁻¹' s) ≠ 0 :=
  let ⟨m, hm, hmN⟩ := ((hf.frequently_measure_inter_ne_zero hs h0).and_eventually (eventually_gt_at_top N)).exists
  ⟨m, hmN, hm⟩

-- error in Dynamics.Ergodic.Conservative: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Poincaré recurrence theorem: given a conservative map `f` and a measurable set `s`, the set
of points `x ∈ s` such that `x` does not return to `s` after `≥ n` iterations has measure zero. -/
theorem measure_mem_forall_ge_image_not_mem_eq_zero
(hf : conservative f μ)
(hs : measurable_set s)
(n : exprℕ()) : «expr = »(μ {x ∈ s | ∀ m «expr ≥ » n, «expr ∉ »(«expr ^[ ]»(f, m) x, s)}, 0) :=
begin
  by_contradiction [ident H],
  have [] [":", expr measurable_set «expr ∩ »(s, {x | ∀ m «expr ≥ » n, «expr ∉ »(«expr ^[ ]»(f, m) x, s)})] [],
  { simp [] [] ["only"] ["[", expr set_of_forall, ",", "<-", expr compl_set_of, "]"] [] [],
    exact [expr hs.inter (measurable_set.bInter (countable_encodable _) (λ m _, hf.measurable.iterate m hs.compl))] },
  rcases [expr hf.exists_gt_measure_inter_ne_zero this H n, "with", "⟨", ident m, ",", ident hmn, ",", ident hm, "⟩"],
  rcases [expr nonempty_of_measure_ne_zero hm, "with", "⟨", ident x, ",", "⟨", ident hxs, ",", ident hxn, "⟩", ",", ident hxm, ",", "-", "⟩"],
  exact [expr hxn m hmn.lt.le hxm]
end

/-- Poincaré recurrence theorem: given a conservative map `f` and a measurable set `s`,
almost every point `x ∈ s` returns back to `s` infinitely many times. -/
theorem ae_mem_imp_frequently_image_mem (hf : conservative f μ) (hs : MeasurableSet s) :
  ∀ᵐx ∂μ, x ∈ s → ∃ᶠn in at_top, (f^[n]) x ∈ s :=
  by 
    simp only [frequently_at_top, @forall_swap (_ ∈ s), ae_all_iff]
    intro n 
    filterUpwards [measure_zero_iff_ae_nmem.1 (hf.measure_mem_forall_ge_image_not_mem_eq_zero hs n)]
    simp 

theorem inter_frequently_image_mem_ae_eq (hf : conservative f μ) (hs : MeasurableSet s) :
  (s ∩ { x | ∃ᶠn in at_top, (f^[n]) x ∈ s } : Set α) =ᵐ[μ] s :=
  inter_eventually_eq_left.2$ hf.ae_mem_imp_frequently_image_mem hs

theorem measure_inter_frequently_image_mem_eq (hf : conservative f μ) (hs : MeasurableSet s) :
  μ (s ∩ { x | ∃ᶠn in at_top, (f^[n]) x ∈ s }) = μ s :=
  measure_congr (hf.inter_frequently_image_mem_ae_eq hs)

/-- Poincaré recurrence theorem: if `f` is a conservative dynamical system and `s` is a measurable
set, then for `μ`-a.e. `x`, if the orbit of `x` visits `s` at least once, then it visits `s`
infinitely many times.  -/
theorem ae_forall_image_mem_imp_frequently_image_mem (hf : conservative f μ) (hs : MeasurableSet s) :
  ∀ᵐx ∂μ, ∀ k, (f^[k]) x ∈ s → ∃ᶠn in at_top, (f^[n]) x ∈ s :=
  by 
    refine' ae_all_iff.2 fun k => _ 
    refine' (hf.ae_mem_imp_frequently_image_mem (hf.measurable.iterate k hs)).mono fun x hx hk => _ 
    rw [←map_add_at_top_eq_nat k, frequently_map]
    refine' (hx hk).mono fun n hn => _ 
    rwa [add_commₓ, iterate_add_apply]

/-- If `f` is a conservative self-map and `s` is a measurable set of positive measure, then
`μ.ae`-frequently we have `x ∈ s` and `s` returns to `s` under infinitely many iterations of `f`. -/
theorem frequently_ae_mem_and_frequently_image_mem (hf : conservative f μ) (hs : MeasurableSet s) (h0 : μ s ≠ 0) :
  ∃ᵐx ∂μ, x ∈ s ∧ ∃ᶠn in at_top, (f^[n]) x ∈ s :=
  ((frequently_ae_mem_iff.2 h0).and_eventually (hf.ae_mem_imp_frequently_image_mem hs)).mono$
    fun x hx => ⟨hx.1, hx.2 hx.1⟩

-- error in Dynamics.Ergodic.Conservative: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Poincaré recurrence theorem. Let `f : α → α` be a conservative dynamical system on a topological
space with second countable topology and measurable open sets. Then almost every point `x : α`
is recurrent: it visits every neighborhood `s ∈ 𝓝 x` infinitely many times. -/
theorem ae_frequently_mem_of_mem_nhds
[topological_space α]
[second_countable_topology α]
[opens_measurable_space α]
{f : α → α}
{μ : measure α}
(h : conservative f μ) : «expr∀ᵐ ∂ , »((x), μ, ∀
 s «expr ∈ » expr𝓝() x, «expr∃ᶠ in , »((n), at_top, «expr ∈ »(«expr ^[ ]»(f, n) x, s))) :=
begin
  have [] [":", expr ∀
   s «expr ∈ » countable_basis α, «expr∀ᵐ ∂ , »((x), μ, «expr ∈ »(x, s) → «expr∃ᶠ in , »((n), at_top, «expr ∈ »(«expr ^[ ]»(f, n) x, s)))] [],
  from [expr λ s hs, h.ae_mem_imp_frequently_image_mem (is_open_of_mem_countable_basis hs).measurable_set],
  refine [expr («expr $ »(ae_ball_iff, countable_countable_basis α).2 this).mono (λ x hx s hs, _)],
  rcases [expr (is_basis_countable_basis α).mem_nhds_iff.1 hs, "with", "⟨", ident o, ",", ident hoS, ",", ident hxo, ",", ident hos, "⟩"],
  exact [expr (hx o hoS hxo).mono (λ n hn, hos hn)]
end

-- error in Dynamics.Ergodic.Conservative: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Iteration of a conservative system is a conservative system. -/
protected
theorem iterate (hf : conservative f μ) (n : exprℕ()) : conservative «expr ^[ ]»(f, n) μ :=
begin
  cases [expr n] [],
  { exact [expr conservative.id μ] },
  refine [expr ⟨hf.1.iterate _, λ s hs hs0, _⟩],
  rcases [expr (hf.frequently_ae_mem_and_frequently_image_mem hs hs0).exists, "with", "⟨", ident x, ",", ident hxs, ",", ident hx, "⟩"],
  rw [expr nat.frequently_at_top_iff_infinite] ["at", ident hx],
  rcases [expr nat.exists_lt_modeq_of_infinite hx n.succ_pos, "with", "⟨", ident k, ",", ident hk, ",", ident l, ",", ident hl, ",", ident hkl, ",", ident hn, "⟩"],
  set [] [ident m] [] [":="] [expr «expr / »(«expr - »(l, k), «expr + »(n, 1))] [],
  have [] [":", expr «expr = »(«expr * »(«expr + »(n, 1), m), «expr - »(l, k))] [],
  { apply [expr nat.mul_div_cancel'],
    exact [expr (nat.modeq_iff_dvd' hkl.le).1 hn] },
  refine [expr ⟨«expr ^[ ]»(f, k) x, hk, m, _, _⟩],
  { intro [ident hm],
    rw ["[", expr hm, ",", expr mul_zero, ",", expr eq_comm, ",", expr tsub_eq_zero_iff_le, "]"] ["at", ident this],
    exact [expr this.not_lt hkl] },
  { rwa ["[", "<-", expr iterate_mul, ",", expr this, ",", "<-", expr iterate_add_apply, ",", expr tsub_add_cancel_of_le, "]"] [],
    exact [expr hkl.le] }
end

end Conservative

end MeasureTheory

