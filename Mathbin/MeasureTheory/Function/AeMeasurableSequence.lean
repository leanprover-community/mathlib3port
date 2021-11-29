import Mathbin.MeasureTheory.MeasurableSpace

/-!
# Sequence of measurable functions associated to a sequence of a.e.-measurable functions

We define here tools to prove statements about limits (infi, supr...) of sequences of
`ae_measurable` functions.
Given a sequence of a.e.-measurable functions `f : ι → α → β` with hypothesis
`hf : ∀ i, ae_measurable (f i) μ`, and a pointwise property `p : α → (ι → β) → Prop` such that we
have `hp : ∀ᵐ x ∂μ, p x (λ n, f n x)`, we define a sequence of measurable functions `ae_seq hf p`
and a measurable set `ae_seq_set hf p`, such that
* `μ (ae_seq_set hf p)ᶜ = 0`
* `x ∈ ae_seq_set hf p → ∀ i : ι, ae_seq hf hp i x = f i x`
* `x ∈ ae_seq_set hf p → p x (λ n, f n x)`
-/


open MeasureTheory

open_locale Classical

variable {α β γ ι : Type _} [MeasurableSpace α] [MeasurableSpace β] {f : ι → α → β} {μ : Measureₓ α}
  {p : α → (ι → β) → Prop}

/-- If we have the additional hypothesis `∀ᵐ x ∂μ, p x (λ n, f n x)`, this is a measurable set
whose complement has measure 0 such that for all `x ∈ ae_seq_set`, `f i x` is equal to
`(hf i).mk (f i) x` for all `i` and we have the pointwise property `p x (λ n, f n x)`. -/
def AeSeqSet (hf : ∀ i, AeMeasurable (f i) μ) (p : α → (ι → β) → Prop) : Set α :=
  «expr ᶜ» (to_measurable μ («expr ᶜ» { x | (∀ i, f i x = (hf i).mk (f i) x) ∧ p x fun n => f n x }))

/-- A sequence of measurable functions that are equal to `f` and verify property `p` on the
measurable set `ae_seq_set hf p`. -/
noncomputable def aeSeq (hf : ∀ i, AeMeasurable (f i) μ) (p : α → (ι → β) → Prop) : ι → α → β :=
  fun i x => ite (x ∈ AeSeqSet hf p) ((hf i).mk (f i) x) (⟨f i x⟩ : Nonempty β).some

namespace aeSeq

section MemAeSeqSet

-- error in MeasureTheory.Function.AeMeasurableSequence: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mk_eq_fun_of_mem_ae_seq_set
(hf : ∀ i, ae_measurable (f i) μ)
{x : α}
(hx : «expr ∈ »(x, ae_seq_set hf p))
(i : ι) : «expr = »((hf i).mk (f i) x, f i x) :=
begin
  have [ident h_ss] [":", expr «expr ⊆ »(ae_seq_set hf p, {x | ∀ i, «expr = »(f i x, (hf i).mk (f i) x)})] [],
  { rw ["[", expr ae_seq_set, ",", "<-", expr compl_compl {x | ∀
     i, «expr = »(f i x, (hf i).mk (f i) x)}, ",", expr set.compl_subset_compl, "]"] [],
    refine [expr set.subset.trans (set.compl_subset_compl.mpr (λ x h, _)) (subset_to_measurable _ _)],
    exact [expr h.1] },
  exact [expr (h_ss hx i).symm]
end

theorem ae_seq_eq_mk_of_mem_ae_seq_set (hf : ∀ i, AeMeasurable (f i) μ) {x : α} (hx : x ∈ AeSeqSet hf p) (i : ι) :
  aeSeq hf p i x = (hf i).mk (f i) x :=
  by 
    simp only [aeSeq, hx, if_true]

theorem ae_seq_eq_fun_of_mem_ae_seq_set (hf : ∀ i, AeMeasurable (f i) μ) {x : α} (hx : x ∈ AeSeqSet hf p) (i : ι) :
  aeSeq hf p i x = f i x :=
  by 
    simp only [ae_seq_eq_mk_of_mem_ae_seq_set hf hx i, mk_eq_fun_of_mem_ae_seq_set hf hx i]

-- error in MeasureTheory.Function.AeMeasurableSequence: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prop_of_mem_ae_seq_set
(hf : ∀ i, ae_measurable (f i) μ)
{x : α}
(hx : «expr ∈ »(x, ae_seq_set hf p)) : p x (λ n, ae_seq hf p n x) :=
begin
  simp [] [] ["only"] ["[", expr ae_seq, ",", expr hx, ",", expr if_true, "]"] [] [],
  rw [expr funext (λ n, mk_eq_fun_of_mem_ae_seq_set hf hx n)] [],
  have [ident h_ss] [":", expr «expr ⊆ »(ae_seq_set hf p, {x | p x (λ n, f n x)})] [],
  { rw ["[", "<-", expr compl_compl {x | p x (λ
      n, f n x)}, ",", expr ae_seq_set, ",", expr set.compl_subset_compl, "]"] [],
    refine [expr set.subset.trans (set.compl_subset_compl.mpr _) (subset_to_measurable _ _)],
    exact [expr λ x hx, hx.2] },
  have [ident hx'] [] [":=", expr set.mem_of_subset_of_mem h_ss hx],
  exact [expr hx']
end

-- error in MeasureTheory.Function.AeMeasurableSequence: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fun_prop_of_mem_ae_seq_set
(hf : ∀ i, ae_measurable (f i) μ)
{x : α}
(hx : «expr ∈ »(x, ae_seq_set hf p)) : p x (λ n, f n x) :=
begin
  have [ident h_eq] [":", expr «expr = »(λ n, f n x, λ n, ae_seq hf p n x)] [],
  from [expr funext (λ n, (ae_seq_eq_fun_of_mem_ae_seq_set hf hx n).symm)],
  rw [expr h_eq] [],
  exact [expr prop_of_mem_ae_seq_set hf hx]
end

end MemAeSeqSet

theorem ae_seq_set_measurable_set {hf : ∀ i, AeMeasurable (f i) μ} : MeasurableSet (AeSeqSet hf p) :=
  (measurable_set_to_measurable _ _).Compl

theorem Measurable (hf : ∀ i, AeMeasurable (f i) μ) (p : α → (ι → β) → Prop) (i : ι) : Measurable (aeSeq hf p i) :=
  Measurable.ite ae_seq_set_measurable_set (hf i).measurable_mk$ measurable_const'$ fun x y => rfl

-- error in MeasureTheory.Function.AeMeasurableSequence: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem measure_compl_ae_seq_set_eq_zero
[encodable ι]
(hf : ∀ i, ae_measurable (f i) μ)
(hp : «expr∀ᵐ ∂ , »((x), μ, p x (λ n, f n x))) : «expr = »(μ «expr ᶜ»(ae_seq_set hf p), 0) :=
begin
  rw ["[", expr ae_seq_set, ",", expr compl_compl, ",", expr measure_to_measurable, "]"] [],
  have [ident hf_eq] [] [":=", expr λ i, (hf i).ae_eq_mk],
  simp_rw ["[", expr filter.eventually_eq, ",", "<-", expr ae_all_iff, "]"] ["at", ident hf_eq],
  exact [expr filter.eventually.and hf_eq hp]
end

-- error in MeasureTheory.Function.AeMeasurableSequence: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_seq_eq_mk_ae
[encodable ι]
(hf : ∀ i, ae_measurable (f i) μ)
(hp : «expr∀ᵐ ∂ , »((x), μ, p x (λ
   n, f n x))) : «expr∀ᵐ ∂ , »((a : α), μ, ∀ i : ι, «expr = »(ae_seq hf p i a, (hf i).mk (f i) a)) :=
begin
  have [ident h_ss] [":", expr «expr ⊆ »(ae_seq_set hf p, {a : α | ∀
    i, «expr = »(ae_seq hf p i a, (hf i).mk (f i) a)})] [],
  from [expr λ x hx i, by simp [] [] ["only"] ["[", expr ae_seq, ",", expr hx, ",", expr if_true, "]"] [] []],
  exact [expr le_antisymm (le_trans (measure_mono (set.compl_subset_compl.mpr h_ss)) (le_of_eq (measure_compl_ae_seq_set_eq_zero hf hp))) (zero_le _)]
end

-- error in MeasureTheory.Function.AeMeasurableSequence: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_seq_eq_fun_ae
[encodable ι]
(hf : ∀ i, ae_measurable (f i) μ)
(hp : «expr∀ᵐ ∂ , »((x), μ, p x (λ
   n, f n x))) : «expr∀ᵐ ∂ , »((a : α), μ, ∀ i : ι, «expr = »(ae_seq hf p i a, f i a)) :=
begin
  have [ident h_ss] [":", expr «expr ⊆ »({a : α | «expr¬ »(∀
     i : ι, «expr = »(ae_seq hf p i a, f i a))}, «expr ᶜ»(ae_seq_set hf p))] [],
  from [expr λ x, mt (λ hx i, ae_seq_eq_fun_of_mem_ae_seq_set hf hx i)],
  exact [expr measure_mono_null h_ss (measure_compl_ae_seq_set_eq_zero hf hp)]
end

theorem ae_seq_n_eq_fun_n_ae [Encodable ι] (hf : ∀ i, AeMeasurable (f i) μ) (hp : ∀ᵐx ∂μ, p x fun n => f n x) (n : ι) :
  aeSeq hf p n =ᵐ[μ] f n :=
  ae_all_iff.mp (ae_seq_eq_fun_ae hf hp) n

-- error in MeasureTheory.Function.AeMeasurableSequence: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem supr
[complete_lattice β]
[encodable ι]
(hf : ∀ i, ae_measurable (f i) μ)
(hp : «expr∀ᵐ ∂ , »((x), μ, p x (λ
   n, f n x))) : «expr =ᵐ[ ] »(«expr⨆ , »((n), ae_seq hf p n), μ, «expr⨆ , »((n), f n)) :=
begin
  simp_rw ["[", expr filter.eventually_eq, ",", expr ae_iff, ",", expr supr_apply, "]"] [],
  have [ident h_ss] [":", expr «expr ⊆ »(ae_seq_set hf p, {a : α | «expr = »(«expr⨆ , »((i : ι), ae_seq hf p i a), «expr⨆ , »((i : ι), f i a))})] [],
  { intros [ident x, ident hx],
    congr,
    exact [expr funext (λ i, ae_seq_eq_fun_of_mem_ae_seq_set hf hx i)] },
  exact [expr measure_mono_null (set.compl_subset_compl.mpr h_ss) (measure_compl_ae_seq_set_eq_zero hf hp)]
end

end aeSeq

