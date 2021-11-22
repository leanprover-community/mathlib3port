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

-- error in Topology.Algebra.ValuedField: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
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

/-- The topology coming from a valuation on a division ring makes it a topological division ring
    [BouAC, VI.5.1 middle of Proposition 1] -/
instance (priority := 100)Valued.topological_division_ring [Valued K] : TopologicalDivisionRing K :=
  { (by 
      infer_instance :
    TopologicalRing K) with
    continuous_inv :=
      by 
        intro x x_ne s s_in 
        cases' valued.mem_nhds.mp s_in with γ hs 
        clear s_in 
        rw [mem_map, Valued.mem_nhds]
        change ∃ γ : Units (Valued.Γ₀ K), { y : K | v (y - x) < γ } ⊆ { x : K | x⁻¹ ∈ s }
        have vx_ne := (Valuation.ne_zero_iff$ v).mpr x_ne 
        let γ' := Units.mk0 _ vx_ne 
        use min (γ*γ'*γ') γ' 
        intro y y_in 
        apply hs 
        simp only [mem_set_of_eq] at y_in 
        rw [Units.min_coe, Units.coe_mul, Units.coe_mul] at y_in 
        exact Valuation.inversion_estimate _ x_ne y_in }

/-- A valued division ring is separated. -/
instance (priority := 100)ValuedRing.separated [Valued K] : SeparatedSpace K :=
  by 
    apply TopologicalAddGroup.separated_of_zero_sep 
    intro x x_ne 
    refine' ⟨{ k | v k < v x }, _, fun h => lt_irreflₓ _ h⟩
    rw [Valued.mem_nhds]
    have vx_ne := (Valuation.ne_zero_iff$ v).mpr x_ne 
    let γ' := Units.mk0 _ vx_ne 
    exact
      ⟨γ',
        fun y hy =>
          by 
            simpa using hy⟩

section 

attribute [local instance] LinearOrderedCommGroupWithZero.topologicalSpace

open Valued

theorem Valued.continuous_valuation [Valued K] : Continuous (v : K → Γ₀ K) :=
  by 
    rw [continuous_iff_continuous_at]
    intro x 
    classical 
    byCases' h : x = 0
    ·
      rw [h]
      change tendsto _ _ (𝓝 (v (0 : K)))
      erw [Valuation.map_zero]
      rw [LinearOrderedCommGroupWithZero.tendsto_zero]
      intro γ 
      rw [Valued.mem_nhds_zero]
      use γ, Set.Subset.refl _
    ·
      change tendsto _ _ _ 
      have v_ne : v x ≠ 0 
      exact (Valuation.ne_zero_iff _).mpr h 
      rw [LinearOrderedCommGroupWithZero.tendsto_of_ne_zero v_ne]
      apply Valued.loc_const v_ne

end 

end ValuationTopologicalDivisionRing

end DivisionRing

section ValuationOnValuedFieldCompletion

open UniformSpace

variable{K : Type _}[Field K][Valued K]

open Valued UniformSpace

local notation "hat " => completion

/-- A valued field is completable. -/
instance (priority := 100)Valued.completable : CompletableTopField K :=
  { ValuedRing.separated with
    nice :=
      by 
        rintro F hF h0 
        have  : ∃ (γ₀ : Units (Γ₀ K))(M : _)(_ : M ∈ F), ∀ x _ : x ∈ M, (γ₀ : Γ₀ K) ≤ v x
        ·
          rcases filter.inf_eq_bot_iff.mp h0 with ⟨U, U_in, M, M_in, H⟩
          rcases valued.mem_nhds_zero.mp U_in with ⟨γ₀, hU⟩
          exists γ₀, M, M_in 
          intro x xM 
          apply le_of_not_ltₓ _ 
          intro hyp 
          have  : x ∈ U ∩ M := ⟨hU hyp, xM⟩
          rwa [H] at this 
        rcases this with ⟨γ₀, M₀, M₀_in, H₀⟩
        rw [Valued.cauchy_iff] at hF⊢
        refine' ⟨hF.1.map _, _⟩
        replace hF := hF.2
        intro γ 
        rcases hF (min ((γ*γ₀)*γ₀) γ₀) with ⟨M₁, M₁_in, H₁⟩
        clear hF 
        use (fun x : K => x⁻¹) '' (M₀ ∩ M₁)
        split 
        ·
          rw [mem_map]
          apply mem_of_superset (Filter.inter_mem M₀_in M₁_in)
          exact subset_preimage_image _ _
        ·
          rintro _ _ ⟨x, ⟨x_in₀, x_in₁⟩, rfl⟩ ⟨y, ⟨y_in₀, y_in₁⟩, rfl⟩
          simp only [mem_set_of_eq]
          specialize H₁ x y x_in₁ y_in₁ 
          replace x_in₀ := H₀ x x_in₀ 
          replace y_in₀ := H₀ y y_in₀ 
          clear H₀ 
          apply Valuation.inversion_estimate
          ·
            have  : v x ≠ 0
            ·
              intro h 
              rw [h] at x_in₀ 
              simpa using x_in₀ 
            exact (Valuation.ne_zero_iff _).mp this
          ·
            refine' lt_of_lt_of_leₓ H₁ _ 
            rw [Units.min_coe]
            apply min_le_min _ x_in₀ 
            rw [mul_assocₓ]
            have  : ((γ₀*γ₀ : Units (Γ₀ K)) : Γ₀ K) ≤ v x*v x 
            exact
              calc («expr↑ » γ₀*«expr↑ » γ₀) ≤ «expr↑ » γ₀*v x := mul_le_mul_left' x_in₀ («expr↑ » γ₀)
                _ ≤ _ := mul_le_mul_right' x_in₀ (v x)
                
            rw [Units.coe_mul]
            exact mul_le_mul_left' this γ }

attribute [local instance] LinearOrderedCommGroupWithZero.topologicalSpace

/-- The extension of the valuation of a valued field to the completion of the field. -/
noncomputable def Valued.extension : hat  K → Γ₀ K :=
  completion.dense_inducing_coe.extend (v : K → Γ₀ K)

-- error in Topology.Algebra.ValuedField: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
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

@[normCast]
theorem Valued.extension_extends (x : K) : Valued.extension (x : hat  K) = v x :=
  by 
    haveI  : T2Space (Valued.Γ₀ K) := RegularSpace.t2_space _ 
    refine' completion.dense_inducing_coe.extend_eq_of_tendsto _ 
    rw [←completion.dense_inducing_coe.nhds_eq_comap]
    exact valued.continuous_valuation.continuous_at

/-- the extension of a valuation on a division ring to its completion. -/
noncomputable def Valued.extensionValuation : Valuation (hat  K) (Γ₀ K) :=
  { toFun := Valued.extension,
    map_zero' :=
      by 
        simpa [←v.map_zero, ←Valued.extension_extends (0 : K)],
    map_one' :=
      by 
        rw [←completion.coe_one, Valued.extension_extends (1 : K)]
        exact Valuation.map_one _,
    map_mul' :=
      fun x y =>
        by 
          apply completion.induction_on₂ x y
          ·
            have c1 : Continuous fun x : hat  K × hat  K => Valued.extension (x.1*x.2)
            exact valued.continuous_extension.comp (continuous_fst.mul continuous_snd)
            have c2 : Continuous fun x : hat  K × hat  K => Valued.extension x.1*Valued.extension x.2 
            exact
              (valued.continuous_extension.comp continuous_fst).mul (valued.continuous_extension.comp continuous_snd)
            exact is_closed_eq c1 c2
          ·
            intro x y 
            normCast 
            exact Valuation.map_mul _ _ _,
    map_add' :=
      fun x y =>
        by 
          rw [le_max_iff]
          apply completion.induction_on₂ x y
          ·
            have cont : Continuous (Valued.extension : hat  K → Γ₀ K) := Valued.continuous_extension 
            exact
              (is_closed_le (cont.comp continuous_add)$ cont.comp continuous_fst).union
                (is_closed_le (cont.comp continuous_add)$ cont.comp continuous_snd)
          ·
            intro x y 
            dsimp 
            normCast 
            rw [←le_max_iff]
            exact v.map_add x y }

end ValuationOnValuedFieldCompletion

