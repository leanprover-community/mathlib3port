import Mathbin.MeasureTheory.Group.Action 
import Mathbin.MeasureTheory.Group.Pointwise 
import Mathbin.MeasureTheory.Integral.SetIntegral

/-!
# Fundamental domain of a group action

A set `s` is said to be a *fundamental domain* of an action of a group `G` on a measurable space `α`
with respect to a measure `μ` if

* `s` is a measurable set;

* the sets `g • s` over all `g : G` cover almost all points of the whole space;

* the sets `g • s`, are pairwise a.e. disjoint, i.e., `μ (g₁ • s ∩ g₂ • s) = 0` whenever `g₁ ≠ g₂`;
  we require this for `g₂ = 1` in the definition, then deduce it for any two `g₁ ≠ g₂`.

In this file we prove that in case of a countable group `G` and a measure preserving action, any two
fundamental domains have the same measure, and for a `G`-invariant function, its integrals over any
two fundamental domains are equal to each other.

We also generate additive versions of all theorems in this file using the `to_additive` attribute.
-/


open_locale Ennreal Pointwise TopologicalSpace Nnreal Ennreal MeasureTheory

open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace

namespace MeasureTheory

/-- A measurable set `s` is a *fundamental domain* for an additive action of an additive group `G`
on a measurable space `α` with respect to a measure `α` if the sets `g +ᵥ s`, `g : G`, are pairwise
a.e. disjoint and cover the whole space. -/
@[protectProj]
structure is_add_fundamental_domain (G : Type _) {α : Type _} [HasZero G] [HasVadd G α] [MeasurableSpace α] (s : Set α)
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac) :
  Prop where 
  MeasurableSet : MeasurableSet s 
  ae_covers : ∀ᵐx ∂μ, ∃ g : G, g +ᵥ x ∈ s 
  ae_disjoint : ∀ g _ : g ≠ (0 : G), μ ((g +ᵥ s) ∩ s) = 0

/-- A measurable set `s` is a *fundamental domain* for an action of a group `G` on a measurable
space `α` with respect to a measure `α` if the sets `g • s`, `g : G`, are pairwise a.e. disjoint and
cover the whole space. -/
@[protectProj, toAdditive is_add_fundamental_domain]
structure is_fundamental_domain (G : Type _) {α : Type _} [HasOne G] [HasScalar G α] [MeasurableSpace α] (s : Set α)
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac) :
  Prop where 
  MeasurableSet : MeasurableSet s 
  ae_covers : ∀ᵐx ∂μ, ∃ g : G, g • x ∈ s 
  ae_disjoint : ∀ g _ : g ≠ (1 : G), μ (g • s ∩ s) = 0

namespace IsFundamentalDomain

variable {G α E : Type _} [Groupₓ G] [MulAction G α] [MeasurableSpace α] [NormedGroup E] {s t : Set α} {μ : Measureₓ α}

@[toAdditive]
theorem Union_smul_ae_eq (h : is_fundamental_domain G s μ) : (⋃g : G, g • s) =ᵐ[μ] univ :=
  Filter.eventually_eq_univ.2$ h.ae_covers.mono$ fun x ⟨g, hg⟩ => mem_Union.2 ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩

@[toAdditive]
theorem mono (h : is_fundamental_domain G s μ) {ν : Measureₓ α} (hle : ν ≪ μ) : is_fundamental_domain G s ν :=
  ⟨h.1, hle h.2, fun g hg => hle (h.3 g hg)⟩

variable [MeasurableSpace G] [HasMeasurableSmul G α]

@[toAdditive]
theorem measurable_set_smul (h : is_fundamental_domain G s μ) (g : G) : MeasurableSet (g • s) :=
  h.measurable_set.const_smul g

variable [smul_invariant_measure G α μ]

@[toAdditive]
theorem pairwise_ae_disjoint (h : is_fundamental_domain G s μ) : Pairwise fun g₁ g₂ : G => μ (g₁ • s ∩ g₂ • s) = 0 :=
  fun g₁ g₂ hne =>
    calc μ (g₁ • s ∩ g₂ • s) = μ (g₂ • ((g₂⁻¹*g₁) • s ∩ s)) :=
      by 
        rw [smul_set_inter, ←mul_smul, mul_inv_cancel_left]
      _ = μ ((g₂⁻¹*g₁) • s ∩ s) := measure_smul_set _ _ _ 
      _ = 0 := h.ae_disjoint _$ mt inv_mul_eq_one.1 hne.symm
      

variable [Encodable G] {ν : Measureₓ α}

@[toAdditive]
theorem sum_restrict_of_ac (h : is_fundamental_domain G s μ) (hν : ν ≪ μ) : (Sum fun g : G => ν.restrict (g • s)) = ν :=
  by 
    rw [←restrict_Union_ae (h.pairwise_ae_disjoint.mono$ fun i j h => hν h) h.measurable_set_smul,
      restrict_congr_set (hν h.Union_smul_ae_eq), restrict_univ]

@[toAdditive]
theorem lintegral_eq_tsum_of_ac (h : is_fundamental_domain G s μ) (hν : ν ≪ μ) (f : α → ℝ≥0∞) :
  (∫⁻x, f x ∂ν) = ∑'g : G, ∫⁻x in g • s, f x ∂ν :=
  by 
    rw [←lintegral_sum_measure, h.sum_restrict_of_ac hν]

@[toAdditive]
theorem set_lintegral_eq_tsum' (h : is_fundamental_domain G s μ) (f : α → ℝ≥0∞) (t : Set α) :
  (∫⁻x in t, f x ∂μ) = ∑'g : G, ∫⁻x in t ∩ g • s, f x ∂μ :=
  calc (∫⁻x in t, f x ∂μ) = ∑'g : G, ∫⁻x in g • s, f x ∂μ.restrict t :=
    h.lintegral_eq_tsum_of_ac restrict_le_self.AbsolutelyContinuous _ 
    _ = ∑'g : G, ∫⁻x in t ∩ g • s, f x ∂μ :=
    by 
      simp only [restrict_restrict, h.measurable_set_smul, inter_comm]
    

@[toAdditive]
theorem set_lintegral_eq_tsum (h : is_fundamental_domain G s μ) (f : α → ℝ≥0∞) (t : Set α) :
  (∫⁻x in t, f x ∂μ) = ∑'g : G, ∫⁻x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
  calc (∫⁻x in t, f x ∂μ) = ∑'g : G, ∫⁻x in t ∩ g • s, f x ∂μ := h.set_lintegral_eq_tsum' f t 
    _ = ∑'g : G, ∫⁻x in t ∩ g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm 
    _ = ∑'g : G, ∫⁻x in g⁻¹ • (g • t ∩ s), f x ∂μ :=
    by 
      simp only [smul_set_inter, inv_smul_smul]
    _ = ∑'g : G, ∫⁻x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
    tsum_congr$
      fun g => ((measure_preserving_smul (g⁻¹) μ).set_lintegral_comp_emb (measurable_embedding_const_smul _) _ _).symm
    

@[toAdditive]
theorem measure_eq_tsum_of_ac (h : is_fundamental_domain G s μ) (hν : ν ≪ μ) (t : Set α) :
  ν t = ∑'g : G, ν (t ∩ g • s) :=
  by 
    simpa only [set_lintegral_one, Pi.one_def, measure.restrict_apply (h.measurable_set_smul _), inter_comm] using
      h.lintegral_eq_tsum_of_ac (measure.restrict_le_self.absolutely_continuous.trans hν) 1

@[toAdditive]
theorem measure_eq_tsum' (h : is_fundamental_domain G s μ) (t : Set α) : μ t = ∑'g : G, μ (t ∩ g • s) :=
  h.measure_eq_tsum_of_ac absolutely_continuous.rfl t

@[toAdditive]
theorem measure_eq_tsum (h : is_fundamental_domain G s μ) (t : Set α) : μ t = ∑'g : G, μ (g • t ∩ s) :=
  by 
    simpa only [set_lintegral_one] using h.set_lintegral_eq_tsum (fun _ => 1) t

@[toAdditive]
protected theorem set_lintegral_eq (hs : is_fundamental_domain G s μ) (ht : is_fundamental_domain G t μ) (f : α → ℝ≥0∞)
  (hf : ∀ g : G x, f (g • x) = f x) : (∫⁻x in s, f x ∂μ) = ∫⁻x in t, f x ∂μ :=
  calc (∫⁻x in s, f x ∂μ) = ∑'g : G, ∫⁻x in s ∩ g • t, f x ∂μ := ht.set_lintegral_eq_tsum' _ _ 
    _ = ∑'g : G, ∫⁻x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
    by 
      simp only [hf, inter_comm]
    _ = ∫⁻x in t, f x ∂μ := (hs.set_lintegral_eq_tsum _ _).symm
    

/-- If `s` and `t` are two fundamental domains of the same action, then their measures are equal. -/
@[toAdditive]
protected theorem measure_eq (hs : is_fundamental_domain G s μ) (ht : is_fundamental_domain G t μ) : μ s = μ t :=
  by 
    simpa only [set_lintegral_one] using hs.set_lintegral_eq ht (fun _ => 1) fun _ _ => rfl

-- error in MeasureTheory.Group.FundamentalDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
protected
theorem ae_measurable_on_iff
{β : Type*}
[measurable_space β]
(hs : is_fundamental_domain G s μ)
(ht : is_fundamental_domain G t μ)
{f : α → β}
(hf : ∀
 (g : G)
 (x), «expr = »(f «expr • »(g, x), f x)) : «expr ↔ »(ae_measurable f (μ.restrict s), ae_measurable f (μ.restrict t)) :=
calc
  «expr ↔ »(ae_measurable f (μ.restrict s), ae_measurable f «expr $ »(measure.sum, λ
    g : G, μ.restrict «expr ∩ »(«expr • »(g, t), s))) : by simp [] [] ["only"] ["[", "<-", expr restrict_restrict (ht.measurable_set_smul _), ",", expr ht.sum_restrict_of_ac restrict_le_self.absolutely_continuous, "]"] [] []
  «expr ↔ »(..., ∀
   g : G, ae_measurable f (μ.restrict «expr • »(g, «expr ∩ »(«expr • »(«expr ⁻¹»(g), s), t)))) : by simp [] [] ["only"] ["[", expr smul_set_inter, ",", expr inter_comm, ",", expr smul_inv_smul, ",", expr ae_measurable_sum_measure_iff, "]"] [] []
  «expr ↔ »(..., ∀
   g : G, ae_measurable f (μ.restrict «expr • »(«expr ⁻¹»(g), «expr ∩ »(«expr • »(«expr ⁻¹»(«expr ⁻¹»(g)), s), t)))) : inv_surjective.forall
  «expr ↔ »(..., ∀
   g : G, ae_measurable f (μ.restrict «expr • »(«expr ⁻¹»(g), «expr ∩ »(«expr • »(g, s), t)))) : by simp [] [] ["only"] ["[", expr inv_inv, "]"] [] []
  «expr ↔ »(..., ∀ g : G, ae_measurable f (μ.restrict «expr ∩ »(«expr • »(g, s), t))) : begin
    refine [expr forall_congr (λ g, _)],
    have [ident he] [":", expr measurable_embedding (((«expr • »)) «expr ⁻¹»(g) : α → α)] [":=", expr measurable_embedding_const_smul _],
    rw ["[", "<-", expr image_smul, ",", "<-", expr ((measure_preserving_smul «expr ⁻¹»(g) μ).restrict_image_emb he _).ae_measurable_comp_iff he, "]"] [],
    simp [] [] ["only"] ["[", expr («expr ∘ »), ",", expr hf, "]"] [] []
  end
  «expr ↔ »(..., ae_measurable f (μ.restrict t)) : by simp [] [] ["only"] ["[", "<-", expr ae_measurable_sum_measure_iff, ",", "<-", expr restrict_restrict (hs.measurable_set_smul _), ",", expr hs.sum_restrict_of_ac restrict_le_self.absolutely_continuous, "]"] [] []

@[toAdditive]
protected theorem has_finite_integral_on_iff (hs : is_fundamental_domain G s μ) (ht : is_fundamental_domain G t μ)
  {f : α → E} (hf : ∀ g : G x, f (g • x) = f x) :
  has_finite_integral f (μ.restrict s) ↔ has_finite_integral f (μ.restrict t) :=
  by 
    dunfold has_finite_integral 
    rw [hs.set_lintegral_eq ht]
    intro g x 
    rw [hf]

variable [MeasurableSpace E]

@[toAdditive]
protected theorem integrable_on_iff (hs : is_fundamental_domain G s μ) (ht : is_fundamental_domain G t μ) {f : α → E}
  (hf : ∀ g : G x, f (g • x) = f x) : integrable_on f s μ ↔ integrable_on f t μ :=
  and_congr (hs.ae_measurable_on_iff ht hf) (hs.has_finite_integral_on_iff ht hf)

variable [NormedSpace ℝ E] [BorelSpace E] [CompleteSpace E] [second_countable_topology E]

-- error in MeasureTheory.Group.FundamentalDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
protected
theorem set_integral_eq
(hs : is_fundamental_domain G s μ)
(ht : is_fundamental_domain G t μ)
{f : α → E}
(hf : ∀
 (g : G)
 (x), «expr = »(f «expr • »(g, x), f x)) : «expr = »(«expr∫ in , ∂ »((x), s, f x, μ), «expr∫ in , ∂ »((x), t, f x, μ)) :=
begin
  by_cases [expr hfs, ":", expr integrable_on f s μ],
  { have [ident hft] [":", expr integrable_on f t μ] [],
    by rwa [expr ht.integrable_on_iff hs hf] [],
    have [ident hac] [":", expr ∀
     {u}, «expr ≪ »(μ.restrict u, μ)] [":=", expr λ u, restrict_le_self.absolutely_continuous],
    calc
      «expr = »(«expr∫ in , ∂ »((x), s, f x, μ), «expr∫ in , ∂ »((x), «expr⋃ , »((g : G), «expr • »(g, t)), f x, μ.restrict s)) : by rw ["[", expr restrict_congr_set (hac ht.Union_smul_ae_eq), ",", expr restrict_univ, "]"] []
      «expr = »(..., «expr∑' , »((g : G), «expr∫ in , ∂ »((x), «expr • »(g, t), f x, μ.restrict s))) : integral_Union_of_null_inter ht.measurable_set_smul «expr $ »(ht.pairwise_ae_disjoint.mono, λ
       i j h, hac h) hfs.integrable.integrable_on
      «expr = »(..., «expr∑' , »((g : G), «expr∫ in , ∂ »((x), «expr ∩ »(s, «expr • »(g, t)), f x, μ))) : by simp [] [] ["only"] ["[", expr restrict_restrict (ht.measurable_set_smul _), ",", expr inter_comm, "]"] [] []
      «expr = »(..., «expr∑' , »((g : G), «expr∫ in , ∂ »((x), «expr ∩ »(s, «expr • »(«expr ⁻¹»(g), t)), f x, μ))) : ((equiv.inv G).tsum_eq _).symm
      «expr = »(..., «expr∑' , »((g : G), «expr∫ in , ∂ »((x), «expr • »(«expr ⁻¹»(g), «expr ∩ »(«expr • »(g, s), t)), f x, μ))) : by simp [] [] ["only"] ["[", expr smul_set_inter, ",", expr inv_smul_smul, "]"] [] []
      «expr = »(..., «expr∑' , »((g : G), «expr∫ in , ∂ »((x), «expr ∩ »(«expr • »(g, s), t), f «expr • »(«expr ⁻¹»(g), x), μ))) : «expr $ »(tsum_congr, λ
       g, (measure_preserving_smul «expr ⁻¹»(g) μ).set_integral_image_emb (measurable_embedding_const_smul _) _ _)
      «expr = »(..., «expr∑' , »((g : G), «expr∫ in , ∂ »((x), «expr • »(g, s), f x, μ.restrict t))) : by simp [] [] ["only"] ["[", expr hf, ",", expr restrict_restrict (hs.measurable_set_smul _), "]"] [] []
      «expr = »(..., «expr∫ in , ∂ »((x), «expr⋃ , »((g : G), «expr • »(g, s)), f x, μ.restrict t)) : (integral_Union_of_null_inter hs.measurable_set_smul «expr $ »(hs.pairwise_ae_disjoint.mono, λ
        i j h, hac h) hft.integrable.integrable_on).symm
      «expr = »(..., «expr∫ in , ∂ »((x), t, f x, μ)) : by rw ["[", expr restrict_congr_set (hac hs.Union_smul_ae_eq), ",", expr restrict_univ, "]"] [] },
  { rw ["[", expr integral_undef hfs, ",", expr integral_undef, "]"] [],
    rwa ["[", expr hs.integrable_on_iff ht hf, "]"] ["at", ident hfs] }
end

end IsFundamentalDomain

end MeasureTheory

