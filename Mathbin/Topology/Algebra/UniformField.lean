import Mathbin.Topology.Algebra.UniformRing 
import Mathbin.Topology.Algebra.Field

/-!
# Completion of topological fields

The goal of this file is to prove the main part of Proposition 7 of Bourbaki GT III 6.8 :

The completion `hat K` of a Hausdorff topological field is a field if the image under
the mapping `x ↦ x⁻¹` of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at `0` is a Cauchy filter
(with respect to the additive uniform structure).

Bourbaki does not give any detail here, he refers to the general discussion of extending
functions defined on a dense subset with values in a complete Hausdorff space. In particular
the subtlety about clustering at zero is totally left to readers.

Note that the separated completion of a non-separated topological field is the zero ring, hence
the separation assumption is needed. Indeed the kernel of the completion map is the closure of
zero which is an ideal. Hence it's either zero (and the field is separated) or the full field,
which implies one is sent to zero and the completion ring is trivial.

The main definition is `completable_top_field` which packages the assumptions as a Prop-valued
type class and the main results are the instances `field_completion` and
`topological_division_ring_completion`.
-/


noncomputable theory

open_locale Classical uniformity TopologicalSpace

open Set UniformSpace UniformSpace.Completion Filter

variable(K : Type _)[Field K][UniformSpace K]

local notation "hat" => completion

instance (priority := 100) [SeparatedSpace K] : Nontrivial (hat K) :=
  ⟨⟨0, 1, fun h => zero_ne_one$ (uniform_embedding_coe K).inj h⟩⟩

/--
A topological field is completable if it is separated and the image under
the mapping x ↦ x⁻¹ of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at 0 is a Cauchy filter
(with respect to the additive uniform structure). This ensures the completion is
a field.
-/
class CompletableTopField extends SeparatedSpace K : Prop where 
  nice : ∀ (F : Filter K), Cauchy F → 𝓝 0⊓F = ⊥ → Cauchy (map (fun x => x⁻¹) F)

variable{K}

-- error in Topology.Algebra.UniformField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- extension of inversion to the completion of a field. -/ def hat_inv : exprhat() K → exprhat() K :=
dense_inducing_coe.extend (λ x : K, (coe «expr ⁻¹»(x) : exprhat() K))

-- error in Topology.Algebra.UniformField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem continuous_hat_inv
[completable_top_field K]
{x : exprhat() K}
(h : «expr ≠ »(x, 0)) : continuous_at hat_inv x :=
begin
  haveI [] [":", expr regular_space (exprhat() K)] [":=", expr completion.regular_space K],
  refine [expr dense_inducing_coe.continuous_at_extend _],
  apply [expr mem_of_superset (compl_singleton_mem_nhds h)],
  intros [ident y, ident y_ne],
  rw [expr mem_compl_singleton_iff] ["at", ident y_ne],
  apply [expr complete_space.complete],
  rw ["<-", expr filter.map_map] [],
  apply [expr cauchy.map _ (completion.uniform_continuous_coe K)],
  apply [expr completable_top_field.nice],
  { haveI [] [] [":=", expr dense_inducing_coe.comap_nhds_ne_bot y],
    apply [expr cauchy_nhds.comap],
    { rw [expr completion.comap_coe_eq_uniformity] [],
      exact [expr le_rfl] } },
  { have [ident eq_bot] [":", expr «expr = »(«expr ⊓ »(expr𝓝() (0 : exprhat() K), expr𝓝() y), «expr⊥»())] [],
    { by_contradiction [ident h],
      exact [expr y_ne «expr $ »(eq_of_nhds_ne_bot, ne_bot_iff.mpr h).symm] },
    erw ["[", expr dense_inducing_coe.nhds_eq_comap (0 : K), ",", "<-", expr comap_inf, ",", expr eq_bot, "]"] [],
    exact [expr comap_bot] }
end

instance Completion.hasInv : HasInv (hat K) :=
  ⟨fun x => if x = 0 then 0 else hatInv x⟩

variable[TopologicalDivisionRing K]

theorem hat_inv_extends {x : K} (h : x ≠ 0) : hatInv (x : hat K) = coeₓ (x⁻¹ : K) :=
  dense_inducing_coe.extend_eq_at ((continuous_coe K).ContinuousAt.comp (TopologicalDivisionRing.continuous_inv x h))

variable[CompletableTopField K]

@[normCast]
theorem coe_inv (x : K) : (x : hat K)⁻¹ = ((x⁻¹ : K) : hat K) :=
  by 
    byCases' h : x = 0
    ·
      rw [h, inv_zero]
      dsimp [HasInv.inv]
      normCast 
      simp [if_pos]
    ·
      convLHS => dsimp [HasInv.inv]
      normCast 
      rw [if_neg]
      ·
        exact hat_inv_extends h
      ·
        exact fun H => h (dense_embedding_coe.inj H)

variable[UniformAddGroup K][TopologicalRing K]

-- error in Topology.Algebra.UniformField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mul_hat_inv_cancel {x : exprhat() K} (x_ne : «expr ≠ »(x, 0)) : «expr = »(«expr * »(x, hat_inv x), 1) :=
begin
  haveI [] [":", expr t1_space (exprhat() K)] [":=", expr t2_space.t1_space],
  let [ident f] [] [":=", expr λ x : exprhat() K, «expr * »(x, hat_inv x)],
  let [ident c] [] [":=", expr (coe : K → exprhat() K)],
  change [expr «expr = »(f x, 1)] [] [],
  have [ident cont] [":", expr continuous_at f x] [],
  { letI [] [":", expr topological_space «expr × »(exprhat() K, exprhat() K)] [":=", expr prod.topological_space],
    have [] [":", expr continuous_at (λ y : exprhat() K, ((y, hat_inv y) : «expr × »(exprhat() K, exprhat() K))) x] [],
    from [expr continuous_id.continuous_at.prod (continuous_hat_inv x_ne)],
    exact [expr (_root_.continuous_mul.continuous_at.comp this : _)] },
  have [ident clo] [":", expr «expr ∈ »(x, closure «expr '' »(c, «expr ᶜ»({0})))] [],
  { have [] [] [":=", expr dense_inducing_coe.dense x],
    rw ["[", "<-", expr image_univ, ",", expr show «expr = »((univ : set K), «expr ∪ »({0}, «expr ᶜ»({0}))), from (union_compl_self _).symm, ",", expr image_union, "]"] ["at", ident this],
    apply [expr mem_closure_of_mem_closure_union this],
    rw [expr image_singleton] [],
    exact [expr compl_singleton_mem_nhds x_ne] },
  have [ident fxclo] [":", expr «expr ∈ »(f x, closure «expr '' »(f, «expr '' »(c, «expr ᶜ»({0}))))] [":=", expr mem_closure_image cont clo],
  have [] [":", expr «expr ⊆ »(«expr '' »(f, «expr '' »(c, «expr ᶜ»({0}))), {1})] [],
  { rw [expr image_image] [],
    rintros ["_", "⟨", ident z, ",", ident z_ne, ",", ident rfl, "⟩"],
    rw [expr mem_singleton_iff] [],
    rw [expr mem_compl_singleton_iff] ["at", ident z_ne],
    dsimp [] ["[", expr c, ",", expr f, "]"] [] [],
    rw [expr hat_inv_extends z_ne] [],
    norm_cast [],
    rw [expr mul_inv_cancel z_ne] [],
    norm_cast [] },
  replace [ident fxclo] [] [":=", expr closure_mono this fxclo],
  rwa ["[", expr closure_singleton, ",", expr mem_singleton_iff, "]"] ["at", ident fxclo]
end

instance fieldCompletion : Field (hat K) :=
  { Completion.hasInv,
    (by 
      infer_instance :
    CommRingₓ (hat K)) with
    exists_pair_ne := ⟨0, 1, fun h => zero_ne_one ((uniform_embedding_coe K).inj h)⟩,
    mul_inv_cancel :=
      fun x x_ne =>
        by 
          dsimp [HasInv.inv]
          simp [if_neg x_ne, mul_hat_inv_cancel x_ne],
    inv_zero :=
      show ((0 : K) : hat K)⁻¹ = ((0 : K) : hat K)by 
        rw [coe_inv, inv_zero] }

-- error in Topology.Algebra.UniformField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance topological_division_ring_completion : topological_division_ring (exprhat() K) :=
{ continuous_inv := begin
    intros [ident x, ident x_ne],
    have [] [":", expr «expr ∈ »({y | «expr = »(hat_inv y, «expr ⁻¹»(y))}, expr𝓝() x)] [],
    { have [] [":", expr «expr ⊆ »(«expr ᶜ»({(0 : exprhat() K)}), {y : exprhat() K | «expr = »(hat_inv y, «expr ⁻¹»(y))})] [],
      { intros [ident y, ident y_ne],
        rw [expr mem_compl_singleton_iff] ["at", ident y_ne],
        dsimp [] ["[", expr has_inv.inv, "]"] [] [],
        rw [expr if_neg y_ne] [] },
      exact [expr mem_of_superset (compl_singleton_mem_nhds x_ne) this] },
    exact [expr continuous_at.congr (continuous_hat_inv x_ne) this]
  end,
  ..completion.top_ring_compl }

