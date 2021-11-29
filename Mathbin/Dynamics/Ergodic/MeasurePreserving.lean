import Mathbin.MeasureTheory.Measure.MeasureSpace

/-!
# Measure preserving maps

We say that `f : α → β` is a measure preserving map w.r.t. measures `μ : measure α` and
`ν : measure β` if `f` is measurable and `map f μ = ν`. In this file we define the predicate
`measure_theory.measure_preserving` and prove its basic properties.

We use the term "measure preserving" because in many applications `α = β` and `μ = ν`.

## References

Partially based on
[this](https://www.isa-afp.org/browser_info/current/AFP/Ergodic_Theory/Measure_Preserving_Transformations.html)
Isabelle formalization.

## Tags

measure preserving map, measure
-/


variable{α β γ δ : Type _}[MeasurableSpace α][MeasurableSpace β][MeasurableSpace γ][MeasurableSpace δ]

namespace MeasureTheory

open Measureₓ Function Set

variable{μa : Measureₓ α}{μb : Measureₓ β}{μc : Measureₓ γ}{μd : Measureₓ δ}

/-- `f` is a measure preserving map w.r.t. measures `μa` and `μb` if `f` is measurable
and `map f μa = μb`. -/
@[protectProj]
structure
  measure_preserving(f : α → β)(μa : Measureₓ α :=  by 
    runTac 
      volume_tac)(μb : Measureₓ β :=  by 
    runTac 
      volume_tac) :
  Prop where 
  Measurable : Measurable f 
  map_eq : map f μa = μb

protected theorem _root_.measurable.measure_preserving {f : α → β} (h : Measurable f) (μa : Measureₓ α) :
  measure_preserving f μa (map f μa) :=
  ⟨h, rfl⟩

namespace MeasurePreserving

protected theorem id (μ : Measureₓ α) : measure_preserving id μ μ :=
  ⟨measurable_id, map_id⟩

theorem symm {e : α ≃ᵐ β} {μa : Measureₓ α} {μb : Measureₓ β} (h : measure_preserving e μa μb) :
  measure_preserving e.symm μb μa :=
  ⟨e.symm.measurable,
    by 
      rw [←h.map_eq, map_map e.symm.measurable e.measurable, e.symm_comp_self, map_id]⟩

theorem restrict_preimage {f : α → β} (hf : measure_preserving f μa μb) {s : Set β} (hs : MeasurableSet s) :
  measure_preserving f (μa.restrict (f ⁻¹' s)) (μb.restrict s) :=
  ⟨hf.measurable,
    by 
      rw [←hf.map_eq, restrict_map hf.measurable hs]⟩

theorem restrict_preimage_emb {f : α → β} (hf : measure_preserving f μa μb) (h₂ : MeasurableEmbedding f) (s : Set β) :
  measure_preserving f (μa.restrict (f ⁻¹' s)) (μb.restrict s) :=
  ⟨hf.measurable,
    by 
      rw [←hf.map_eq, h₂.restrict_map]⟩

theorem restrict_image_emb {f : α → β} (hf : measure_preserving f μa μb) (h₂ : MeasurableEmbedding f) (s : Set α) :
  measure_preserving f (μa.restrict s) (μb.restrict (f '' s)) :=
  by 
    simpa only [preimage_image_eq _ h₂.injective] using hf.restrict_preimage_emb h₂ (f '' s)

theorem ae_measurable_comp_iff {f : α → β} (hf : measure_preserving f μa μb) (h₂ : MeasurableEmbedding f) {g : β → γ} :
  AeMeasurable (g ∘ f) μa ↔ AeMeasurable g μb :=
  by 
    rw [←hf.map_eq, h₂.ae_measurable_map_iff]

protected theorem quasi_measure_preserving {f : α → β} (hf : measure_preserving f μa μb) :
  quasi_measure_preserving f μa μb :=
  ⟨hf.1, hf.2.AbsolutelyContinuous⟩

theorem comp {g : β → γ} {f : α → β} (hg : measure_preserving g μb μc) (hf : measure_preserving f μa μb) :
  measure_preserving (g ∘ f) μa μc :=
  ⟨hg.1.comp hf.1,
    by 
      rw [←map_map hg.1 hf.1, hf.2, hg.2]⟩

protected theorem sigma_finite {f : α → β} (hf : measure_preserving f μa μb) [sigma_finite μb] : sigma_finite μa :=
  sigma_finite.of_map μa hf.1
    (by 
      rwa [hf.map_eq])

theorem measure_preimage {f : α → β} (hf : measure_preserving f μa μb) {s : Set β} (hs : MeasurableSet s) :
  μa (f ⁻¹' s) = μb s :=
  by 
    rw [←hf.map_eq, map_apply hf.1 hs]

theorem measure_preimage_emb {f : α → β} (hf : measure_preserving f μa μb) (hfe : MeasurableEmbedding f) (s : Set β) :
  μa (f ⁻¹' s) = μb s :=
  by 
    rw [←hf.map_eq, hfe.map_apply]

protected theorem iterate {f : α → α} (hf : measure_preserving f μa μa) : ∀ n, measure_preserving (f^[n]) μa μa
| 0 => measure_preserving.id μa
| n+1 => (iterate n).comp hf

variable{μ : Measureₓ α}{f : α → α}{s : Set α}

-- error in Dynamics.Ergodic.MeasurePreserving: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `μ univ < n * μ s` and `f` is a map preserving measure `μ`,
then for some `x ∈ s` and `0 < m < n`, `f^[m] x ∈ s`. -/
theorem exists_mem_image_mem_of_volume_lt_mul_volume
(hf : measure_preserving f μ μ)
(hs : measurable_set s)
{n : exprℕ()}
(hvol : «expr < »(μ (univ : set α), «expr * »(n, μ s))) : «expr∃ , »((x «expr ∈ » s)
 (m «expr ∈ » Ioo 0 n), «expr ∈ »(«expr ^[ ]»(f, m) x, s)) :=
begin
  have [ident A] [":", expr ∀
   m, measurable_set «expr ⁻¹' »(«expr ^[ ]»(f, m), s)] [":=", expr λ m, (hf.iterate m).measurable hs],
  have [ident B] [":", expr ∀ m, «expr = »(μ «expr ⁻¹' »(«expr ^[ ]»(f, m), s), μ s)] [],
  from [expr λ m, (hf.iterate m).measure_preimage hs],
  have [] [":", expr «expr < »(μ (univ : set α), (finset.range n).sum (λ m, μ «expr ⁻¹' »(«expr ^[ ]»(f, m), s)))] [],
  by simpa [] [] ["only"] ["[", expr B, ",", expr nsmul_eq_mul, ",", expr finset.sum_const, ",", expr finset.card_range, "]"] [] [],
  rcases [expr exists_nonempty_inter_of_measure_univ_lt_sum_measure μ (λ
    m
    hm, A m) this, "with", "⟨", ident i, ",", ident hi, ",", ident j, ",", ident hj, ",", ident hij, ",", ident x, ",", ident hxi, ",", ident hxj, "⟩"],
  wlog [ident hlt] [":", expr «expr < »(i, j)] [":=", expr hij.lt_or_lt] ["using", "[", ident i, ident j, ",", ident j, ident i, "]"] tactic.skip,
  { simp [] [] ["only"] ["[", expr set.mem_preimage, ",", expr finset.mem_range, "]"] [] ["at", ident hi, ident hj, ident hxi, ident hxj],
    refine [expr ⟨«expr ^[ ]»(f, i) x, hxi, «expr - »(j, i), ⟨tsub_pos_of_lt hlt, lt_of_le_of_lt (j.sub_le i) hj⟩, _⟩],
    rwa ["[", "<-", expr iterate_add_apply, ",", expr tsub_add_cancel_of_le hlt.le, "]"] [] },
  { exact [expr λ hi hj hij hxi hxj, this hj hi hij.symm hxj hxi] }
end

/-- A self-map preserving a finite measure is conservative: if `μ s ≠ 0`, then at least one point
`x ∈ s` comes back to `s` under iterations of `f`. Actually, a.e. point of `s` comes back to `s`
infinitely many times, see `measure_theory.measure_preserving.conservative` and theorems about
`measure_theory.conservative`. -/
theorem exists_mem_image_mem [is_finite_measure μ] (hf : measure_preserving f μ μ) (hs : MeasurableSet s)
  (hs' : μ s ≠ 0) : ∃ (x : _)(_ : x ∈ s)(m : _)(_ : m ≠ 0), (f^[m]) x ∈ s :=
  by 
    rcases Ennreal.exists_nat_mul_gt hs' (measure_ne_top μ (univ : Set α)) with ⟨N, hN⟩
    rcases hf.exists_mem_image_mem_of_volume_lt_mul_volume hs hN with ⟨x, hx, m, hm, hmx⟩
    exact ⟨x, hx, m, hm.1.ne', hmx⟩

end MeasurePreserving

end MeasureTheory

