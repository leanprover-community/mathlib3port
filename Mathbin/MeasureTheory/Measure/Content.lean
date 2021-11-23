import Mathbin.MeasureTheory.Measure.MeasureSpace 
import Mathbin.MeasureTheory.Measure.Regular 
import Mathbin.Topology.Opens 
import Mathbin.Topology.Compacts

/-!
# Contents

In this file we work with *contents*. A content `λ` is a function from a certain class of subsets
(such as the compact subsets) to `ℝ≥0` that is
* additive: If `K₁` and `K₂` are disjoint sets in the domain of `λ`,
  then `λ(K₁ ∪ K₂) = λ(K₁) + λ(K₂)`;
* subadditive: If `K₁` and `K₂` are in the domain of `λ`, then `λ(K₁ ∪ K₂) ≤ λ(K₁) + λ(K₂)`;
* monotone: If `K₁ ⊆ K₂` are in the domain of `λ`, then `λ(K₁) ≤ λ(K₂)`.

We show that:
* Given a content `λ` on compact sets, let us define a function `λ*` on open sets, by letting
  `λ* U` be the supremum of `λ K` for `K` included in `U`. This is a countably subadditive map that
  vanishes at `∅`. In Halmos (1950) this is called the *inner content* `λ*` of `λ`, and formalized
  as `inner_content`.
* Given an inner content, we define an outer measure `μ*`, by letting `μ* E` be the infimum of
  `λ* U` over the open sets `U` containing `E`. This is indeed an outer measure. It is formalized
  as `outer_measure`.
* Restricting this outer measure to Borel sets gives a regular measure `μ`.

We define bundled contents as `content`.
In this file we only work on contents on compact sets, and inner contents on open sets, and both
contents and inner contents map into the extended nonnegative reals. However, in other applications
other choices can be made, and it is not a priori clear what the best interface should be.

## Main definitions

For `μ : content G`, we define
* `μ.inner_content` : the inner content associated to `μ`.
* `μ.outer_measure` : the outer measure associated to `μ`.
* `μ.measure`       : the Borel measure associated to `μ`.

We prove that, on a locally compact space, the measure `μ.measure` is regular.

## References

* Paul Halmos (1950), Measure Theory, §53
* <https://en.wikipedia.org/wiki/Content_(measure_theory)>
-/


universe u v w

noncomputable theory

open Set TopologicalSpace

open_locale Nnreal Ennreal

namespace MeasureTheory

variable{G : Type w}[TopologicalSpace G]

/-- A content is an additive function on compact sets taking values in `ℝ≥0`. It is a device
from which one can define a measure. -/
structure content(G : Type w)[TopologicalSpace G] where 
  toFun : compacts G →  ℝ≥0 
  mono' : ∀ K₁ K₂ : compacts G, K₁.1 ⊆ K₂.1 → to_fun K₁ ≤ to_fun K₂ 
  sup_disjoint' : ∀ K₁ K₂ : compacts G, Disjoint K₁.1 K₂.1 → to_fun (K₁⊔K₂) = to_fun K₁+to_fun K₂ 
  sup_le' : ∀ K₁ K₂ : compacts G, to_fun (K₁⊔K₂) ≤ to_fun K₁+to_fun K₂

instance  : Inhabited (content G) :=
  ⟨{ toFun := fun K => 0,
      mono' :=
        by 
          simp ,
      sup_disjoint' :=
        by 
          simp ,
      sup_le' :=
        by 
          simp  }⟩

/-- Although the `to_fun` field of a content takes values in `ℝ≥0`, we register a coercion to
functions taking values in `ℝ≥0∞` as most constructions below rely on taking suprs and infs, which
is more convenient in a complete lattice, and aim at constructing a measure. -/
instance  : CoeFun (content G) fun _ => compacts G → ℝ≥0∞ :=
  ⟨fun μ s => μ.to_fun s⟩

namespace Content

variable(μ : content G)

theorem apply_eq_coe_to_fun (K : compacts G) : μ K = μ.to_fun K :=
  rfl

theorem mono (K₁ K₂ : compacts G) (h : K₁.1 ⊆ K₂.1) : μ K₁ ≤ μ K₂ :=
  by 
    simp [apply_eq_coe_to_fun, μ.mono' _ _ h]

theorem sup_disjoint (K₁ K₂ : compacts G) (h : Disjoint K₁.1 K₂.1) : μ (K₁⊔K₂) = μ K₁+μ K₂ :=
  by 
    simp [apply_eq_coe_to_fun, μ.sup_disjoint' _ _ h]

theorem sup_le (K₁ K₂ : compacts G) : μ (K₁⊔K₂) ≤ μ K₁+μ K₂ :=
  by 
    simp only [apply_eq_coe_to_fun]
    normCast 
    exact μ.sup_le' _ _

theorem lt_top (K : compacts G) : μ K < ∞ :=
  Ennreal.coe_lt_top

-- error in MeasureTheory.Measure.Content: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem empty : «expr = »(μ «expr⊥»(), 0) :=
begin
  have [] [] [":=", expr μ.sup_disjoint' «expr⊥»() «expr⊥»()],
  simpa [] [] [] ["[", expr apply_eq_coe_to_fun, "]"] [] ["using", expr this]
end

/-- Constructing the inner content of a content. From a content defined on the compact sets, we
  obtain a function defined on all open sets, by taking the supremum of the content of all compact
  subsets. -/
def inner_content (U : opens G) : ℝ≥0∞ :=
  ⨆(K : compacts G)(h : K.1 ⊆ U), μ K

theorem le_inner_content (K : compacts G) (U : opens G) (h2 : K.1 ⊆ U) : μ K ≤ μ.inner_content U :=
  le_supr_of_le K$ le_supr _ h2

theorem inner_content_le (U : opens G) (K : compacts G) (h2 : (U : Set G) ⊆ K.1) : μ.inner_content U ≤ μ K :=
  bsupr_le$ fun K' hK' => μ.mono _ _ (subset.trans hK' h2)

theorem inner_content_of_is_compact {K : Set G} (h1K : IsCompact K) (h2K : IsOpen K) :
  μ.inner_content ⟨K, h2K⟩ = μ ⟨K, h1K⟩ :=
  le_antisymmₓ (bsupr_le$ fun K' hK' => μ.mono _ ⟨K, h1K⟩ hK') (μ.le_inner_content _ _ subset.rfl)

-- error in MeasureTheory.Measure.Content: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem inner_content_empty : «expr = »(μ.inner_content «expr∅»(), 0) :=
begin
  refine [expr le_antisymm _ (zero_le _)],
  rw ["<-", expr μ.empty] [],
  refine [expr bsupr_le (λ K hK, _)],
  have [] [":", expr «expr = »(K, «expr⊥»())] [],
  { ext1 [] [],
    rw ["[", expr subset_empty_iff.mp hK, ",", expr compacts.bot_val, "]"] [] },
  rw [expr this] [],
  refl'
end

/-- This is "unbundled", because that it required for the API of `induced_outer_measure`. -/
theorem inner_content_mono ⦃U V : Set G⦄ (hU : IsOpen U) (hV : IsOpen V) (h2 : U ⊆ V) :
  μ.inner_content ⟨U, hU⟩ ≤ μ.inner_content ⟨V, hV⟩ :=
  supr_le_supr$ fun K => supr_le_supr_const$ fun hK => subset.trans hK h2

-- error in MeasureTheory.Measure.Content: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem inner_content_exists_compact
{U : opens G}
(hU : «expr ≠ »(μ.inner_content U, «expr∞»()))
{ε : «exprℝ≥0»()}
(hε : «expr ≠ »(ε, 0)) : «expr∃ , »((K : compacts G), «expr ∧ »(«expr ⊆ »(K.1, U), «expr ≤ »(μ.inner_content U, «expr + »(μ K, ε)))) :=
begin
  have [ident h'ε] [] [":=", expr ennreal.coe_ne_zero.2 hε],
  cases [expr le_or_lt (μ.inner_content U) ε] [],
  { exact [expr ⟨«expr⊥»(), empty_subset _, le_add_left h⟩] },
  have [] [] [":=", expr ennreal.sub_lt_self hU h.ne_bot h'ε],
  conv ["at", ident this] [] { to_rhs,
    rw [expr inner_content] },
  simp [] [] ["only"] ["[", expr lt_supr_iff, "]"] [] ["at", ident this],
  rcases [expr this, "with", "⟨", ident U, ",", ident h1U, ",", ident h2U, "⟩"],
  refine [expr ⟨U, h1U, _⟩],
  rw ["[", "<-", expr tsub_le_iff_right, "]"] [],
  exact [expr le_of_lt h2U]
end

-- error in MeasureTheory.Measure.Content: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The inner content of a supremum of opens is at most the sum of the individual inner
contents. -/
theorem inner_content_Sup_nat
[t2_space G]
(U : exprℕ() → opens G) : «expr ≤ »(μ.inner_content «expr⨆ , »((i : exprℕ()), U i), «expr∑' , »((i : exprℕ()), μ.inner_content (U i))) :=
begin
  have [ident h3] [":", expr ∀
   (t : finset exprℕ())
   (K : exprℕ() → compacts G), «expr ≤ »(μ (t.sup K), t.sum (λ i, μ (K i)))] [],
  { intros [ident t, ident K],
    refine [expr finset.induction_on t _ _],
    { simp [] [] ["only"] ["[", expr μ.empty, ",", expr nonpos_iff_eq_zero, ",", expr finset.sum_empty, ",", expr finset.sup_empty, "]"] [] [] },
    { intros [ident n, ident s, ident hn, ident ih],
      rw ["[", expr finset.sup_insert, ",", expr finset.sum_insert hn, "]"] [],
      exact [expr le_trans (μ.sup_le _ _) (add_le_add_left ih _)] } },
  refine [expr bsupr_le (λ K hK, _)],
  rcases [expr is_compact.elim_finite_subcover K.2 _ (λ i, (U i).prop) _, "with", "⟨", ident t, ",", ident ht, "⟩"],
  swap,
  { convert [] [expr hK] [],
    rw ["[", expr opens.supr_def, ",", expr subtype.coe_mk, "]"] [] },
  rcases [expr K.2.finite_compact_cover t «expr ∘ »(coe, U) (λ
    i
    _, (U _).prop) (by simp [] [] ["only"] ["[", expr ht, "]"] [] []), "with", "⟨", ident K', ",", ident h1K', ",", ident h2K', ",", ident h3K', "⟩"],
  let [ident L] [":", expr exprℕ() → compacts G] [":=", expr λ n, ⟨K' n, h1K' n⟩],
  convert [] [expr le_trans (h3 t L) _] [],
  { ext1 [] [],
    simp [] [] ["only"] ["[", expr h3K', ",", expr compacts.finset_sup_val, ",", expr finset.sup_eq_supr, ",", expr set.supr_eq_Union, "]"] [] [] },
  refine [expr le_trans (finset.sum_le_sum _) (ennreal.sum_le_tsum t)],
  intros [ident i, ident hi],
  refine [expr le_trans _ (le_supr _ (L i))],
  refine [expr le_trans _ (le_supr _ (h2K' i))],
  refl'
end

-- error in MeasureTheory.Measure.Content: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The inner content of a union of sets is at most the sum of the individual inner contents.
  This is the "unbundled" version of `inner_content_Sup_nat`.
  It required for the API of `induced_outer_measure`. -/
theorem inner_content_Union_nat
[t2_space G]
{{U : exprℕ() → set G}}
(hU : ∀
 i : exprℕ(), is_open (U i)) : «expr ≤ »(μ.inner_content ⟨«expr⋃ , »((i : exprℕ()), U i), is_open_Union hU⟩, «expr∑' , »((i : exprℕ()), μ.inner_content ⟨U i, hU i⟩)) :=
by { have [] [] [":=", expr μ.inner_content_Sup_nat (λ i, ⟨U i, hU i⟩)],
  rwa ["[", expr opens.supr_def, "]"] ["at", ident this] }

theorem inner_content_comap (f : G ≃ₜ G) (h : ∀ ⦃K : compacts G⦄, μ (K.map f f.continuous) = μ K) (U : opens G) :
  μ.inner_content (U.comap f.continuous) = μ.inner_content U :=
  by 
    refine' supr_congr _ (compacts.equiv f).Surjective _ 
    intro K 
    refine' supr_congr_Prop image_subset_iff _ 
    intro hK 
    simp only [Equiv.coe_fn_mk, Subtype.mk_eq_mk, Ennreal.coe_eq_coe, compacts.equiv]
    apply h

@[toAdditive]
theorem is_mul_left_invariant_inner_content [Groupₓ G] [TopologicalGroup G]
  (h : ∀ g : G {K : compacts G}, μ (K.map _$ continuous_mul_left g) = μ K) (g : G) (U : opens G) :
  μ.inner_content (U.comap$ continuous_mul_left g) = μ.inner_content U :=
  by 
    convert μ.inner_content_comap (Homeomorph.mulLeft g) (fun K => h g) U

-- error in MeasureTheory.Measure.Content: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem inner_content_pos_of_is_mul_left_invariant
[t2_space G]
[group G]
[topological_group G]
(h3 : ∀ (g : G) {K : compacts G}, «expr = »(μ «expr $ »(K.map _, continuous_mul_left g), μ K))
(K : compacts G)
(hK : «expr ≠ »(μ K, 0))
(U : opens G)
(hU : (U : set G).nonempty) : «expr < »(0, μ.inner_content U) :=
begin
  have [] [":", expr (interior (U : set G)).nonempty] [],
  rwa ["[", expr U.prop.interior_eq, "]"] [],
  rcases [expr compact_covered_by_mul_left_translates K.2 this, "with", "⟨", ident s, ",", ident hs, "⟩"],
  suffices [] [":", expr «expr ≤ »(μ K, «expr * »(s.card, μ.inner_content U))],
  { exact [expr «expr $ »(ennreal.mul_pos_iff.mp, hK.bot_lt.trans_le this).2] },
  have [] [":", expr «expr ⊆ »(K.1, «expr↑ »(«expr⨆ , »((g «expr ∈ » s), «expr $ »(U.comap, continuous_mul_left g))))] [],
  { simpa [] [] ["only"] ["[", expr opens.supr_def, ",", expr opens.coe_comap, ",", expr subtype.coe_mk, "]"] [] [] },
  refine [expr (μ.le_inner_content _ _ this).trans _],
  refine [expr (rel_supr_sum μ.inner_content μ.inner_content_empty ((«expr ≤ »)) μ.inner_content_Sup_nat _ _).trans _],
  simp [] [] ["only"] ["[", expr μ.is_mul_left_invariant_inner_content h3, ",", expr finset.sum_const, ",", expr nsmul_eq_mul, ",", expr le_refl, "]"] [] []
end

theorem inner_content_mono' ⦃U V : Set G⦄ (hU : IsOpen U) (hV : IsOpen V) (h2 : U ⊆ V) :
  μ.inner_content ⟨U, hU⟩ ≤ μ.inner_content ⟨V, hV⟩ :=
  supr_le_supr$ fun K => supr_le_supr_const$ fun hK => subset.trans hK h2

/-- Extending a content on compact sets to an outer measure on all sets. -/
protected def outer_measure : outer_measure G :=
  induced_outer_measure (fun U hU => μ.inner_content ⟨U, hU⟩) is_open_empty μ.inner_content_empty

variable[T2Space G]

theorem outer_measure_opens (U : opens G) : μ.outer_measure U = μ.inner_content U :=
  induced_outer_measure_eq' (fun _ => is_open_Union) μ.inner_content_Union_nat μ.inner_content_mono U.2

theorem outer_measure_of_is_open (U : Set G) (hU : IsOpen U) : μ.outer_measure U = μ.inner_content ⟨U, hU⟩ :=
  μ.outer_measure_opens ⟨U, hU⟩

theorem outer_measure_le (U : opens G) (K : compacts G) (hUK : (U : Set G) ⊆ K.1) : μ.outer_measure U ≤ μ K :=
  (μ.outer_measure_opens U).le.trans$ μ.inner_content_le U K hUK

theorem le_outer_measure_compacts (K : compacts G) : μ K ≤ μ.outer_measure K.1 :=
  by 
    rw [content.outer_measure, induced_outer_measure_eq_infi]
    ·
      exact le_infi fun U => le_infi$ fun hU => le_infi$ μ.le_inner_content K ⟨U, hU⟩
    ·
      exact μ.inner_content_Union_nat
    ·
      exact μ.inner_content_mono

theorem outer_measure_eq_infi (A : Set G) :
  μ.outer_measure A = ⨅(U : Set G)(hU : IsOpen U)(h : A ⊆ U), μ.inner_content ⟨U, hU⟩ :=
  induced_outer_measure_eq_infi _ μ.inner_content_Union_nat μ.inner_content_mono A

theorem outer_measure_interior_compacts (K : compacts G) : μ.outer_measure (Interior K.1) ≤ μ K :=
  le_transₓ (le_of_eqₓ$ μ.outer_measure_opens (opens.interior K.1)) (μ.inner_content_le _ _ interior_subset)

theorem outer_measure_exists_compact {U : opens G} (hU : μ.outer_measure U ≠ ∞) {ε :  ℝ≥0 } (hε : ε ≠ 0) :
  ∃ K : compacts G, K.1 ⊆ U ∧ μ.outer_measure U ≤ μ.outer_measure K.1+ε :=
  by 
    rw [μ.outer_measure_opens] at hU⊢
    rcases μ.inner_content_exists_compact hU hε with ⟨K, h1K, h2K⟩
    exact ⟨K, h1K, le_transₓ h2K$ add_le_add_right (μ.le_outer_measure_compacts K) _⟩

theorem outer_measure_exists_open {A : Set G} (hA : μ.outer_measure A ≠ ∞) {ε :  ℝ≥0 } (hε : ε ≠ 0) :
  ∃ U : opens G, A ⊆ U ∧ μ.outer_measure U ≤ μ.outer_measure A+ε :=
  by 
    rcases induced_outer_measure_exists_set _ _ μ.inner_content_mono hA (Ennreal.coe_ne_zero.2 hε) with
      ⟨U, hU, h2U, h3U⟩
    exact ⟨⟨U, hU⟩, h2U, h3U⟩
    swap 
    exact μ.inner_content_Union_nat

theorem outer_measure_preimage (f : G ≃ₜ G) (h : ∀ ⦃K : compacts G⦄, μ (K.map f f.continuous) = μ K) (A : Set G) :
  μ.outer_measure (f ⁻¹' A) = μ.outer_measure A :=
  by 
    refine'
      induced_outer_measure_preimage _ μ.inner_content_Union_nat μ.inner_content_mono _ (fun s => f.is_open_preimage) _ 
    intro s hs 
    convert μ.inner_content_comap f h ⟨s, hs⟩

theorem outer_measure_lt_top_of_is_compact [LocallyCompactSpace G] {K : Set G} (hK : IsCompact K) :
  μ.outer_measure K < ∞ :=
  by 
    rcases exists_compact_superset hK with ⟨F, h1F, h2F⟩
    calc μ.outer_measure K ≤ μ.outer_measure (Interior F) := outer_measure.mono' _ h2F _ ≤ μ ⟨F, h1F⟩ :=
      by 
        apply μ.outer_measure_le ⟨Interior F, is_open_interior⟩ ⟨F, h1F⟩ interior_subset _ < ⊤ :=
      μ.lt_top _

@[toAdditive]
theorem is_mul_left_invariant_outer_measure [Groupₓ G] [TopologicalGroup G]
  (h : ∀ g : G {K : compacts G}, μ (K.map _$ continuous_mul_left g) = μ K) (g : G) (A : Set G) :
  μ.outer_measure ((fun h => g*h) ⁻¹' A) = μ.outer_measure A :=
  by 
    convert μ.outer_measure_preimage (Homeomorph.mulLeft g) (fun K => h g) A

theorem outer_measure_caratheodory (A : Set G) :
  μ.outer_measure.caratheodory.measurable_set' A ↔
    ∀ U : opens G, (μ.outer_measure (U ∩ A)+μ.outer_measure (U \ A)) ≤ μ.outer_measure U :=
  by 
    dsimp [opens]
    rw [Subtype.forall]
    apply induced_outer_measure_caratheodory 
    apply inner_content_Union_nat 
    apply inner_content_mono'

@[toAdditive]
theorem outer_measure_pos_of_is_mul_left_invariant [Groupₓ G] [TopologicalGroup G]
  (h3 : ∀ g : G {K : compacts G}, μ (K.map _$ continuous_mul_left g) = μ K) (K : compacts G) (hK : μ K ≠ 0) {U : Set G}
  (h1U : IsOpen U) (h2U : U.nonempty) : 0 < μ.outer_measure U :=
  by 
    convert μ.inner_content_pos_of_is_mul_left_invariant h3 K hK ⟨U, h1U⟩ h2U 
    exact μ.outer_measure_opens ⟨U, h1U⟩

variable[S : MeasurableSpace G][BorelSpace G]

include S

-- error in MeasureTheory.Measure.Content: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For the outer measure coming from a content, all Borel sets are measurable. -/
theorem borel_le_caratheodory : «expr ≤ »(S, μ.outer_measure.caratheodory) :=
begin
  rw ["[", expr @borel_space.measurable_eq G _ _, "]"] [],
  refine [expr measurable_space.generate_from_le _],
  intros [ident U, ident hU],
  rw [expr μ.outer_measure_caratheodory] [],
  intro [ident U'],
  rw [expr μ.outer_measure_of_is_open «expr ∩ »((U' : set G), U) (is_open.inter U'.prop hU)] [],
  simp [] [] ["only"] ["[", expr inner_content, ",", expr supr_subtype', "]"] [] [],
  rw ["[", expr opens.coe_mk, "]"] [],
  haveI [] [":", expr nonempty {L : compacts G // «expr ⊆ »(L.1, «expr ∩ »(U', U))}] [":=", expr ⟨⟨«expr⊥»(), empty_subset _⟩⟩],
  rw ["[", expr ennreal.supr_add, "]"] [],
  refine [expr supr_le _],
  rintro ["⟨", ident L, ",", ident hL, "⟩"],
  simp [] [] ["only"] ["[", expr subset_inter_iff, "]"] [] ["at", ident hL],
  have [] [":", expr «expr ⊆ »(«expr \ »(«expr↑ »(U'), U), «expr \ »(U', L.1))] [":=", expr diff_subset_diff_right hL.2],
  refine [expr le_trans (add_le_add_left (μ.outer_measure.mono' this) _) _],
  rw [expr μ.outer_measure_of_is_open «expr \ »(«expr↑ »(U'), L.1) (is_open.sdiff U'.2 L.2.is_closed)] [],
  simp [] [] ["only"] ["[", expr inner_content, ",", expr supr_subtype', "]"] [] [],
  rw ["[", expr opens.coe_mk, "]"] [],
  haveI [] [":", expr nonempty {M : compacts G // «expr ⊆ »(M.1, «expr \ »(«expr↑ »(U'), L.1))}] [":=", expr ⟨⟨«expr⊥»(), empty_subset _⟩⟩],
  rw ["[", expr ennreal.add_supr, "]"] [],
  refine [expr supr_le _],
  rintro ["⟨", ident M, ",", ident hM, "⟩"],
  simp [] [] ["only"] ["[", expr subset_diff, "]"] [] ["at", ident hM],
  have [] [":", expr «expr ⊆ »(«expr ⊔ »(L, M).1, U')] [],
  { simp [] [] ["only"] ["[", expr union_subset_iff, ",", expr compacts.sup_val, ",", expr hM, ",", expr hL, ",", expr and_self, "]"] [] [] },
  rw [expr μ.outer_measure_of_is_open «expr↑ »(U') U'.2] [],
  refine [expr le_trans (ge_of_eq _) (μ.le_inner_content _ _ this)],
  exact [expr μ.sup_disjoint _ _ hM.2.symm]
end

/-- The measure induced by the outer measure coming from a content, on the Borel sigma-algebra. -/
protected def Measureₓ : Measureₓ G :=
  μ.outer_measure.to_measure μ.borel_le_caratheodory

theorem measure_apply {s : Set G} (hs : MeasurableSet s) : μ.measure s = μ.outer_measure s :=
  to_measure_apply _ _ hs

-- error in MeasureTheory.Measure.Content: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In a locally compact space, any measure constructed from a content is regular. -/
instance regular [locally_compact_space G] : μ.measure.regular :=
begin
  haveI [] [":", expr μ.measure.outer_regular] [],
  { refine [expr ⟨λ (A hA r) (hr : «expr < »(_, _)), _⟩],
    rw ["[", expr μ.measure_apply hA, ",", expr outer_measure_eq_infi, "]"] ["at", ident hr],
    simp [] [] ["only"] ["[", expr infi_lt_iff, "]"] [] ["at", ident hr],
    rcases [expr hr, "with", "⟨", ident U, ",", ident hUo, ",", ident hAU, ",", ident hr, "⟩"],
    rw ["[", "<-", expr μ.outer_measure_of_is_open U hUo, ",", "<-", expr μ.measure_apply hUo.measurable_set, "]"] ["at", ident hr],
    exact [expr ⟨U, hAU, hUo, hr⟩] },
  split,
  { intros [ident K, ident hK],
    rw ["[", expr measure_apply _ hK.measurable_set, "]"] [],
    exact [expr μ.outer_measure_lt_top_of_is_compact hK] },
  { intros [ident U, ident hU, ident r, ident hr],
    rw ["[", expr measure_apply _ hU.measurable_set, ",", expr μ.outer_measure_of_is_open U hU, "]"] ["at", ident hr],
    simp [] [] ["only"] ["[", expr inner_content, ",", expr lt_supr_iff, "]"] [] ["at", ident hr],
    rcases [expr hr, "with", "⟨", ident K, ",", ident hKU, ",", ident hr, "⟩"],
    refine [expr ⟨K.1, hKU, K.2, hr.trans_le _⟩],
    exact [expr (μ.le_outer_measure_compacts K).trans (le_to_measure_apply _ _ _)] }
end

end Content

end MeasureTheory

