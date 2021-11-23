import Mathbin.Topology.Algebra.Valuation 
import Mathbin.Topology.Algebra.WithZeroTopology 
import Mathbin.Topology.Algebra.UniformField

/-!
# Valued fields and their completions

In this file we study the topology of a field `K` endowed with a valuation (in our application
to adic spaces, `K` will be the valuation field associated to some valuation on a ring, defined in
valuation.basic).

We already know from valuation.topology that one can build a topology on `K` which
makes it a topological ring.

The first goal is to show `K` is a topological *field*, ie inversion is continuous
at every non-zero element.

The next goal is to prove `K` is a *completable* topological field. This gives us
a completion `hat K` which is a topological field. We also prove that `K` is automatically
separated, so the map from `K` to `hat K` is injective.

Then we extend the valuation given on `K` to a valuation on `hat K`.
-/


open Filter Set

open_locale TopologicalSpace

section DivisionRing

variable{K : Type _}[DivisionRing K]

section ValuationTopologicalDivisionRing

section InversionEstimate

variable{Γ₀ : Type _}[LinearOrderedCommGroupWithZero Γ₀](v : Valuation K Γ₀)

-- error in Topology.Algebra.ValuedField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem valuation.inversion_estimate
{x y : K}
{γ : units Γ₀}
(y_ne : «expr ≠ »(y, 0))
(h : «expr < »(v «expr - »(x, y), min «expr * »(γ, «expr * »(v y, v y)) (v y))) : «expr < »(v «expr - »(«expr ⁻¹»(x), «expr ⁻¹»(y)), γ) :=
begin
  have [ident hyp1] [":", expr «expr < »(v «expr - »(x, y), «expr * »(γ, «expr * »(v y, v y)))] [],
  from [expr lt_of_lt_of_le h (min_le_left _ _)],
  have [ident hyp1'] [":", expr «expr < »(«expr * »(v «expr - »(x, y), «expr ⁻¹»(«expr * »(v y, v y))), γ)] [],
  from [expr mul_inv_lt_of_lt_mul₀ hyp1],
  have [ident hyp2] [":", expr «expr < »(v «expr - »(x, y), v y)] [],
  from [expr lt_of_lt_of_le h (min_le_right _ _)],
  have [ident key] [":", expr «expr = »(v x, v y)] [],
  from [expr valuation.map_eq_of_sub_lt v hyp2],
  have [ident x_ne] [":", expr «expr ≠ »(x, 0)] [],
  { intro [ident h],
    apply [expr y_ne],
    rw ["[", expr h, ",", expr v.map_zero, "]"] ["at", ident key],
    exact [expr v.zero_iff.1 key.symm] },
  have [ident decomp] [":", expr «expr = »(«expr - »(«expr ⁻¹»(x), «expr ⁻¹»(y)), «expr * »(«expr * »(«expr ⁻¹»(x), «expr - »(y, x)), «expr ⁻¹»(y)))] [],
  by rw ["[", expr mul_sub_left_distrib, ",", expr sub_mul, ",", expr mul_assoc, ",", expr show «expr = »(«expr * »(y, «expr ⁻¹»(y)), 1), from mul_inv_cancel y_ne, ",", expr show «expr = »(«expr * »(«expr ⁻¹»(x), x), 1), from inv_mul_cancel x_ne, ",", expr mul_one, ",", expr one_mul, "]"] [],
  calc
    «expr = »(v «expr - »(«expr ⁻¹»(x), «expr ⁻¹»(y)), v «expr * »(«expr * »(«expr ⁻¹»(x), «expr - »(y, x)), «expr ⁻¹»(y))) : by rw [expr decomp] []
    «expr = »(..., «expr * »(«expr * »(v «expr ⁻¹»(x), «expr $ »(v, «expr - »(y, x))), v «expr ⁻¹»(y))) : by repeat { rw [expr valuation.map_mul] [] }
    «expr = »(..., «expr * »(«expr * »(«expr ⁻¹»(v x), «expr $ »(v, «expr - »(y, x))), «expr ⁻¹»(v y))) : by rw ["[", expr v.map_inv, ",", expr v.map_inv, "]"] []
    «expr = »(..., «expr * »(«expr $ »(v, «expr - »(y, x)), «expr ⁻¹»(«expr * »(v y, v y)))) : by { rw ["[", expr mul_assoc, ",", expr mul_comm, ",", expr key, ",", expr mul_assoc, ",", expr mul_inv_rev₀, "]"] [] }
    «expr = »(..., «expr * »(«expr $ »(v, «expr - »(y, x)), «expr ⁻¹»(«expr * »(v y, v y)))) : rfl
    «expr = »(..., «expr * »(«expr $ »(v, «expr - »(x, y)), «expr ⁻¹»(«expr * »(v y, v y)))) : by rw [expr valuation.map_sub_swap] []
    «expr < »(..., γ) : hyp1'
end

end InversionEstimate

open Valued

-- error in Topology.Algebra.ValuedField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The topology coming from a valuation on a division ring makes it a topological division ring
    [BouAC, VI.5.1 middle of Proposition 1] -/
@[priority 100]
instance valued.topological_division_ring [valued K] : topological_division_ring K :=
{ continuous_inv := begin
    intros [ident x, ident x_ne, ident s, ident s_in],
    cases [expr valued.mem_nhds.mp s_in] ["with", ident γ, ident hs],
    clear [ident s_in],
    rw ["[", expr mem_map, ",", expr valued.mem_nhds, "]"] [],
    change [expr «expr∃ , »((γ : units (valued.Γ₀ K)), «expr ⊆ »({y : K | «expr < »(v «expr - »(y, x), γ)}, {x : K | «expr ∈ »(«expr ⁻¹»(x), s)}))] [] [],
    have [ident vx_ne] [] [":=", expr «expr $ »(valuation.ne_zero_iff, v).mpr x_ne],
    let [ident γ'] [] [":=", expr units.mk0 _ vx_ne],
    use [expr min «expr * »(γ, «expr * »(γ', γ')) γ'],
    intros [ident y, ident y_in],
    apply [expr hs],
    simp [] [] ["only"] ["[", expr mem_set_of_eq, "]"] [] ["at", ident y_in],
    rw ["[", expr units.min_coe, ",", expr units.coe_mul, ",", expr units.coe_mul, "]"] ["at", ident y_in],
    exact [expr valuation.inversion_estimate _ x_ne y_in]
  end,
  ..(by apply_instance : topological_ring K) }

-- error in Topology.Algebra.ValuedField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A valued division ring is separated. -/
@[priority 100]
instance valued_ring.separated [valued K] : separated_space K :=
begin
  apply [expr topological_add_group.separated_of_zero_sep],
  intros [ident x, ident x_ne],
  refine [expr ⟨{k | «expr < »(v k, v x)}, _, λ h, lt_irrefl _ h⟩],
  rw [expr valued.mem_nhds] [],
  have [ident vx_ne] [] [":=", expr «expr $ »(valuation.ne_zero_iff, v).mpr x_ne],
  let [ident γ'] [] [":=", expr units.mk0 _ vx_ne],
  exact [expr ⟨γ', λ y hy, by simpa [] [] [] [] [] ["using", expr hy]⟩]
end

section 

attribute [local instance] LinearOrderedCommGroupWithZero.topologicalSpace

open Valued

-- error in Topology.Algebra.ValuedField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem valued.continuous_valuation [valued K] : continuous (v : K → Γ₀ K) :=
begin
  rw [expr continuous_iff_continuous_at] [],
  intro [ident x],
  classical,
  by_cases [expr h, ":", expr «expr = »(x, 0)],
  { rw [expr h] [],
    change [expr tendsto _ _ (expr𝓝() (v (0 : K)))] [] [],
    erw [expr valuation.map_zero] [],
    rw [expr linear_ordered_comm_group_with_zero.tendsto_zero] [],
    intro [ident γ],
    rw [expr valued.mem_nhds_zero] [],
    use ["[", expr γ, ",", expr set.subset.refl _, "]"] },
  { change [expr tendsto _ _ _] [] [],
    have [ident v_ne] [":", expr «expr ≠ »(v x, 0)] [],
    from [expr (valuation.ne_zero_iff _).mpr h],
    rw [expr linear_ordered_comm_group_with_zero.tendsto_of_ne_zero v_ne] [],
    apply [expr valued.loc_const v_ne] }
end

end 

end ValuationTopologicalDivisionRing

end DivisionRing

section ValuationOnValuedFieldCompletion

open UniformSpace

variable{K : Type _}[Field K][Valued K]

open Valued UniformSpace

local notation "hat " => completion

-- error in Topology.Algebra.ValuedField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A valued field is completable. -/ @[priority 100] instance valued.completable : completable_top_field K :=
{ nice := begin
    rintros [ident F, ident hF, ident h0],
    have [] [":", expr «expr∃ , »((γ₀ : units (Γ₀ K))
      (M «expr ∈ » F), ∀ x «expr ∈ » M, «expr ≤ »((γ₀ : Γ₀ K), v x))] [],
    { rcases [expr filter.inf_eq_bot_iff.mp h0, "with", "⟨", ident U, ",", ident U_in, ",", ident M, ",", ident M_in, ",", ident H, "⟩"],
      rcases [expr valued.mem_nhds_zero.mp U_in, "with", "⟨", ident γ₀, ",", ident hU, "⟩"],
      existsi ["[", expr γ₀, ",", expr M, ",", expr M_in, "]"],
      intros [ident x, ident xM],
      apply [expr le_of_not_lt _],
      intro [ident hyp],
      have [] [":", expr «expr ∈ »(x, «expr ∩ »(U, M))] [":=", expr ⟨hU hyp, xM⟩],
      rwa [expr H] ["at", ident this] },
    rcases [expr this, "with", "⟨", ident γ₀, ",", ident M₀, ",", ident M₀_in, ",", ident H₀, "⟩"],
    rw [expr valued.cauchy_iff] ["at", ident hF, "⊢"],
    refine [expr ⟨hF.1.map _, _⟩],
    replace [ident hF] [] [":=", expr hF.2],
    intros [ident γ],
    rcases [expr hF (min «expr * »(«expr * »(γ, γ₀), γ₀) γ₀), "with", "⟨", ident M₁, ",", ident M₁_in, ",", ident H₁, "⟩"],
    clear [ident hF],
    use [expr «expr '' »(λ x : K, «expr ⁻¹»(x), «expr ∩ »(M₀, M₁))],
    split,
    { rw [expr mem_map] [],
      apply [expr mem_of_superset (filter.inter_mem M₀_in M₁_in)],
      exact [expr subset_preimage_image _ _] },
    { rintros ["_", "_", "⟨", ident x, ",", "⟨", ident x_in₀, ",", ident x_in₁, "⟩", ",", ident rfl, "⟩", "⟨", ident y, ",", "⟨", ident y_in₀, ",", ident y_in₁, "⟩", ",", ident rfl, "⟩"],
      simp [] [] ["only"] ["[", expr mem_set_of_eq, "]"] [] [],
      specialize [expr H₁ x y x_in₁ y_in₁],
      replace [ident x_in₀] [] [":=", expr H₀ x x_in₀],
      replace [ident y_in₀] [] [":=", expr H₀ y y_in₀],
      clear [ident H₀],
      apply [expr valuation.inversion_estimate],
      { have [] [":", expr «expr ≠ »(v x, 0)] [],
        { intro [ident h],
          rw [expr h] ["at", ident x_in₀],
          simpa [] [] [] [] [] ["using", expr x_in₀] },
        exact [expr (valuation.ne_zero_iff _).mp this] },
      { refine [expr lt_of_lt_of_le H₁ _],
        rw [expr units.min_coe] [],
        apply [expr min_le_min _ x_in₀],
        rw [expr mul_assoc] [],
        have [] [":", expr «expr ≤ »(((«expr * »(γ₀, γ₀) : units (Γ₀ K)) : Γ₀ K), «expr * »(v x, v x))] [],
        from [expr calc
           «expr ≤ »(«expr * »(«expr↑ »(γ₀), «expr↑ »(γ₀)), «expr * »(«expr↑ »(γ₀), v x)) : mul_le_mul_left' x_in₀ «expr↑ »(γ₀)
           «expr ≤ »(..., _) : mul_le_mul_right' x_in₀ (v x)],
        rw [expr units.coe_mul] [],
        exact [expr mul_le_mul_left' this γ] } }
  end,
  ..valued_ring.separated }

attribute [local instance] LinearOrderedCommGroupWithZero.topologicalSpace

/-- The extension of the valuation of a valued field to the completion of the field. -/
noncomputable def Valued.extension : hat  K → Γ₀ K :=
  completion.dense_inducing_coe.extend (v : K → Γ₀ K)

-- error in Topology.Algebra.ValuedField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
theorem valued.continuous_extension : continuous (valued.extension : exprhat() K → Γ₀ K) :=
begin
  refine [expr completion.dense_inducing_coe.continuous_extend _],
  intro [ident x₀],
  by_cases [expr h, ":", expr «expr = »(x₀, coe 0)],
  { refine [expr ⟨0, _⟩],
    erw ["[", expr h, ",", "<-", expr completion.dense_inducing_coe.to_inducing.nhds_eq_comap, "]"] []; try { apply_instance },
    rw [expr linear_ordered_comm_group_with_zero.tendsto_zero] [],
    intro [ident γ₀],
    rw [expr valued.mem_nhds] [],
    exact [expr ⟨γ₀, by simp [] [] [] [] [] []⟩] },
  { have [ident preimage_one] [":", expr «expr ∈ »(«expr ⁻¹' »(v, {(1 : Γ₀ K)}), expr𝓝() (1 : K))] [],
    { have [] [":", expr «expr ≠ »(v (1 : K), 0)] [],
      { rw [expr valuation.map_one] [],
        exact [expr zero_ne_one.symm] },
      convert [] [expr valued.loc_const this] [],
      ext [] [ident x] [],
      rw ["[", expr valuation.map_one, ",", expr mem_preimage, ",", expr mem_singleton_iff, ",", expr mem_set_of_eq, "]"] [] },
    obtain ["⟨", ident V, ",", ident V_in, ",", ident hV, "⟩", ":", expr «expr∃ , »((V «expr ∈ » expr𝓝() (1 : exprhat() K)), ∀
      x : K, «expr ∈ »((x : exprhat() K), V) → «expr = »(v x, 1))],
    { rwa ["[", expr completion.dense_inducing_coe.nhds_eq_comap, ",", expr mem_comap, "]"] ["at", ident preimage_one] },
    have [] [":", expr «expr∃ , »((V' «expr ∈ » expr𝓝() (1 : exprhat() K)), «expr ∧ »(«expr ∉ »((0 : exprhat() K), V'), ∀
       x y «expr ∈ » V', «expr ∈ »(«expr * »(x, «expr ⁻¹»(y)), V)))] [],
    { have [] [":", expr tendsto (λ
        p : «expr × »(exprhat() K, exprhat() K), «expr * »(p.1, «expr ⁻¹»(p.2))) ((expr𝓝() 1).prod (expr𝓝() 1)) (expr𝓝() 1)] [],
      { rw ["<-", expr nhds_prod_eq] [],
        conv [] [] { congr,
          skip,
          skip,
          rw ["<-", expr one_mul (1 : exprhat() K)] },
        refine [expr tendsto.mul continuous_fst.continuous_at (tendsto.comp _ continuous_snd.continuous_at)],
        convert [] [expr topological_division_ring.continuous_inv (1 : exprhat() K) zero_ne_one.symm] [],
        exact [expr inv_one.symm] },
      rcases [expr tendsto_prod_self_iff.mp this V V_in, "with", "⟨", ident U, ",", ident U_in, ",", ident hU, "⟩"],
      let [ident hatKstar] [] [":=", expr («expr ᶜ»({0}) : «expr $ »(set, exprhat() K))],
      have [] [":", expr «expr ∈ »(hatKstar, expr𝓝() (1 : exprhat() K))] [],
      from [expr compl_singleton_mem_nhds zero_ne_one.symm],
      use ["[", expr «expr ∩ »(U, hatKstar), ",", expr filter.inter_mem U_in this, "]"],
      split,
      { rintro ["⟨", ident h, ",", ident h', "⟩"],
        rw [expr mem_compl_singleton_iff] ["at", ident h'],
        exact [expr h' rfl] },
      { rintros [ident x, ident y, "⟨", ident hx, ",", "_", "⟩", "⟨", ident hy, ",", "_", "⟩"],
        apply [expr hU]; assumption } },
    rcases [expr this, "with", "⟨", ident V', ",", ident V'_in, ",", ident zeroV', ",", ident hV', "⟩"],
    have [ident nhds_right] [":", expr «expr ∈ »(«expr '' »(λ x, «expr * »(x, x₀), V'), expr𝓝() x₀)] [],
    { have [ident l] [":", expr function.left_inverse (λ
        x : exprhat() K, «expr * »(x, «expr ⁻¹»(x₀))) (λ x : exprhat() K, «expr * »(x, x₀))] [],
      { intro [ident x],
        simp [] [] ["only"] ["[", expr mul_assoc, ",", expr mul_inv_cancel h, ",", expr mul_one, "]"] [] [] },
      have [ident r] [":", expr function.right_inverse (λ
        x : exprhat() K, «expr * »(x, «expr ⁻¹»(x₀))) (λ x : exprhat() K, «expr * »(x, x₀))] [],
      { intro [ident x],
        simp [] [] ["only"] ["[", expr mul_assoc, ",", expr inv_mul_cancel h, ",", expr mul_one, "]"] [] [] },
      have [ident c] [":", expr continuous (λ x : exprhat() K, «expr * »(x, «expr ⁻¹»(x₀)))] [],
      from [expr continuous_id.mul continuous_const],
      rw [expr image_eq_preimage_of_inverse l r] [],
      rw ["<-", expr mul_inv_cancel h] ["at", ident V'_in],
      exact [expr c.continuous_at V'_in] },
    have [] [":", expr «expr∃ , »((z₀ : K)
      (y₀ «expr ∈ » V'), «expr ∧ »(«expr = »(coe z₀, «expr * »(y₀, x₀)), «expr ≠ »(z₀, 0)))] [],
    { rcases [expr dense_range.mem_nhds completion.dense_range_coe nhds_right, "with", "⟨", ident z₀, ",", ident y₀, ",", ident y₀_in, ",", ident h, "⟩"],
      refine [expr ⟨z₀, y₀, y₀_in, ⟨h.symm, _⟩⟩],
      intro [ident hz],
      rw [expr hz] ["at", ident h],
      cases [expr zero_eq_mul.mp h.symm] []; finish [] [] },
    rcases [expr this, "with", "⟨", ident z₀, ",", ident y₀, ",", ident y₀_in, ",", ident hz₀, ",", ident z₀_ne, "⟩"],
    have [ident vz₀_ne] [":", expr «expr ≠ »(v z₀, 0)] [":=", expr by rwa [expr valuation.ne_zero_iff] []],
    refine [expr ⟨v z₀, _⟩],
    rw ["[", expr linear_ordered_comm_group_with_zero.tendsto_of_ne_zero vz₀_ne, ",", expr mem_comap, "]"] [],
    use ["[", expr «expr '' »(λ x, «expr * »(x, x₀), V'), ",", expr nhds_right, "]"],
    intros [ident x, ident x_in],
    rcases [expr mem_preimage.1 x_in, "with", "⟨", ident y, ",", ident y_in, ",", ident hy, "⟩"],
    clear [ident x_in],
    change [expr «expr = »(«expr * »(y, x₀), coe x)] [] ["at", ident hy],
    have [] [":", expr «expr = »(v «expr * »(x, «expr ⁻¹»(z₀)), 1)] [],
    { apply [expr hV],
      have [] [":", expr «expr = »(((«expr ⁻¹»(z₀) : K) : exprhat() K), «expr ⁻¹»(z₀))] [],
      from [expr ring_hom.map_inv (completion.coe_ring_hom : «expr →+* »(K, exprhat() K)) z₀],
      rw ["[", expr completion.coe_mul, ",", expr this, ",", "<-", expr hy, ",", expr hz₀, ",", expr mul_inv₀, ",", expr mul_comm «expr ⁻¹»(y₀), ",", "<-", expr mul_assoc, ",", expr mul_assoc y, ",", expr mul_inv_cancel h, ",", expr mul_one, "]"] [],
      solve_by_elim [] [] [] [] },
    calc
      «expr = »(v x, v «expr * »(«expr * »(x, «expr ⁻¹»(z₀)), z₀)) : by rw ["[", expr mul_assoc, ",", expr inv_mul_cancel z₀_ne, ",", expr mul_one, "]"] []
      «expr = »(..., «expr * »(v «expr * »(x, «expr ⁻¹»(z₀)), v z₀)) : valuation.map_mul _ _ _
      «expr = »(..., v z₀) : by rw ["[", expr this, ",", expr one_mul, "]"] [] }
end

-- error in Topology.Algebra.ValuedField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[norm_cast #[]] theorem valued.extension_extends (x : K) : «expr = »(valued.extension (x : exprhat() K), v x) :=
begin
  haveI [] [":", expr t2_space (valued.Γ₀ K)] [":=", expr regular_space.t2_space _],
  refine [expr completion.dense_inducing_coe.extend_eq_of_tendsto _],
  rw ["<-", expr completion.dense_inducing_coe.nhds_eq_comap] [],
  exact [expr valued.continuous_valuation.continuous_at]
end

-- error in Topology.Algebra.ValuedField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- the extension of a valuation on a division ring to its completion. -/
noncomputable
def valued.extension_valuation : valuation (exprhat() K) (Γ₀ K) :=
{ to_fun := valued.extension,
  map_zero' := by { simpa [] [] [] ["[", "<-", expr v.map_zero, ",", "<-", expr valued.extension_extends (0 : K), "]"] [] [] },
  map_one' := by { rw ["[", "<-", expr completion.coe_one, ",", expr valued.extension_extends (1 : K), "]"] [],
    exact [expr valuation.map_one _] },
  map_mul' := λ x y, begin
    apply [expr completion.induction_on₂ x y],
    { have [ident c1] [":", expr continuous (λ
        x : «expr × »(exprhat() K, exprhat() K), valued.extension «expr * »(x.1, x.2))] [],
      from [expr valued.continuous_extension.comp (continuous_fst.mul continuous_snd)],
      have [ident c2] [":", expr continuous (λ
        x : «expr × »(exprhat() K, exprhat() K), «expr * »(valued.extension x.1, valued.extension x.2))] [],
      from [expr (valued.continuous_extension.comp continuous_fst).mul (valued.continuous_extension.comp continuous_snd)],
      exact [expr is_closed_eq c1 c2] },
    { intros [ident x, ident y],
      norm_cast [],
      exact [expr valuation.map_mul _ _ _] }
  end,
  map_add' := λ x y, begin
    rw [expr le_max_iff] [],
    apply [expr completion.induction_on₂ x y],
    { have [ident cont] [":", expr continuous (valued.extension : exprhat() K → Γ₀ K)] [":=", expr valued.continuous_extension],
      exact [expr «expr $ »(is_closed_le (cont.comp continuous_add), cont.comp continuous_fst).union «expr $ »(is_closed_le (cont.comp continuous_add), cont.comp continuous_snd)] },
    { intros [ident x, ident y],
      dsimp [] [] [] [],
      norm_cast [],
      rw ["<-", expr le_max_iff] [],
      exact [expr v.map_add x y] }
  end }

end ValuationOnValuedFieldCompletion

