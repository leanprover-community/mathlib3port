import Mathbin.Geometry.Manifold.Algebra.Monoid

/-!
# Lie groups

A Lie group is a group that is also a smooth manifold, in which the group operations of
multiplication and inversion are smooth maps. Smoothness of the group multiplication means that
multiplication is a smooth mapping of the product manifold `G` × `G` into `G`.

Note that, since a manifold here is not second-countable and Hausdorff a Lie group here is not
guaranteed to be second-countable (even though it can be proved it is Hausdorff). Note also that Lie
groups here are not necessarily finite dimensional.

## Main definitions and statements

* `lie_add_group I G` : a Lie additive group where `G` is a manifold on the model with corners `I`.
* `lie_group I G`     : a Lie multiplicative group where `G` is a manifold on the model with
                        corners `I`.
* `normed_space_lie_add_group` : a normed vector space over a nondiscrete normed field
                                 is an additive Lie group.

## Implementation notes

A priori, a Lie group here is a manifold with corners.

The definition of Lie group cannot require `I : model_with_corners 𝕜 E E` with the same space as the
model space and as the model vector space, as one might hope, beause in the product situation,
the model space is `model_prod E E'` and the model vector space is `E × E'`, which are not the same,
so the definition does not apply. Hence the definition should be more general, allowing
`I : model_with_corners 𝕜 E H`.
-/


noncomputable theory

open_locale Manifold

-- error in Geometry.Manifold.Algebra.LieGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A Lie (additive) group is a group and a smooth manifold at the same time in which
the addition and negation operations are smooth. -/
@[ancestor #[ident has_smooth_add]]
class lie_add_group
{𝕜 : Type*}
[nondiscrete_normed_field 𝕜]
{H : Type*}
[topological_space H]
{E : Type*}
[normed_group E]
[normed_space 𝕜 E]
(I : model_with_corners 𝕜 E H)
(G : Type*)
[add_group G]
[topological_space G]
[charted_space H G]extends has_smooth_add I G : exprProp() := (smooth_neg : smooth I I (λ a : G, «expr- »(a)))

-- error in Geometry.Manifold.Algebra.LieGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A Lie group is a group and a smooth manifold at the same time in which
the multiplication and inverse operations are smooth. -/
@[ancestor #[ident has_smooth_mul], to_additive #[]]
class lie_group
{𝕜 : Type*}
[nondiscrete_normed_field 𝕜]
{H : Type*}
[topological_space H]
{E : Type*}
[normed_group E]
[normed_space 𝕜 E]
(I : model_with_corners 𝕜 E H)
(G : Type*)
[group G]
[topological_space G]
[charted_space H G]extends has_smooth_mul I G : exprProp() := (smooth_inv : smooth I I (λ a : G, «expr ⁻¹»(a)))

section LieGroup

variable{𝕜 :
    Type
      _}[NondiscreteNormedField
      𝕜]{H :
    Type
      _}[TopologicalSpace
      H]{E :
    Type
      _}[NormedGroup
      E][NormedSpace 𝕜
      E]{I :
    ModelWithCorners 𝕜 E
      H}{F :
    Type
      _}[NormedGroup
      F][NormedSpace 𝕜
      F]{J :
    ModelWithCorners 𝕜 F
      F}{G :
    Type
      _}[TopologicalSpace
      G][ChartedSpace H
      G][Groupₓ
      G][LieGroup I
      G]{E' :
    Type
      _}[NormedGroup
      E'][NormedSpace 𝕜
      E']{H' :
    Type
      _}[TopologicalSpace
      H']{I' :
    ModelWithCorners 𝕜 E'
      H'}{M :
    Type
      _}[TopologicalSpace
      M][ChartedSpace H'
      M]{E'' :
    Type
      _}[NormedGroup
      E''][NormedSpace 𝕜
      E'']{H'' :
    Type
      _}[TopologicalSpace H'']{I'' : ModelWithCorners 𝕜 E'' H''}{M' : Type _}[TopologicalSpace M'][ChartedSpace H'' M']

section 

variable(I)

-- error in Geometry.Manifold.Algebra.LieGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[to_additive #[]] theorem smooth_inv : smooth I I (λ x : G, «expr ⁻¹»(x)) := lie_group.smooth_inv

/-- A Lie group is a topological group. This is not an instance for technical reasons,
see note [Design choices about smooth algebraic structures]. -/
@[toAdditive
      "An additive Lie group is an additive topological group. This is not an instance for technical\nreasons, see note [Design choices about smooth algebraic structures]."]
theorem topological_group_of_lie_group : TopologicalGroup G :=
  { has_continuous_mul_of_smooth I with continuous_inv := (smooth_inv I).Continuous }

end 

@[toAdditive]
theorem Smooth.inv {f : M → G} (hf : Smooth I' I f) : Smooth I' I fun x => f x⁻¹ :=
  (smooth_inv I).comp hf

@[toAdditive]
theorem SmoothOn.inv {f : M → G} {s : Set M} (hf : SmoothOn I' I f s) : SmoothOn I' I (fun x => f x⁻¹) s :=
  (smooth_inv I).comp_smooth_on hf

@[toAdditive]
theorem Smooth.div {f g : M → G} (hf : Smooth I' I f) (hg : Smooth I' I g) : Smooth I' I (f / g) :=
  by 
    rw [div_eq_mul_inv]
    exact ((smooth_mul I).comp (hf.prod_mk hg.inv) : _)

@[toAdditive]
theorem SmoothOn.div {f g : M → G} {s : Set M} (hf : SmoothOn I' I f s) (hg : SmoothOn I' I g s) :
  SmoothOn I' I (f / g) s :=
  by 
    rw [div_eq_mul_inv]
    exact ((smooth_mul I).comp_smooth_on (hf.prod_mk hg.inv) : _)

end LieGroup

section ProdLieGroup

@[toAdditive]
instance  {𝕜 : Type _} [NondiscreteNormedField 𝕜] {H : Type _} [TopologicalSpace H] {E : Type _} [NormedGroup E]
  [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type _} [TopologicalSpace G] [ChartedSpace H G] [Groupₓ G]
  [LieGroup I G] {E' : Type _} [NormedGroup E'] [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {G' : Type _} [TopologicalSpace G'] [ChartedSpace H' G'] [Groupₓ G']
  [LieGroup I' G'] : LieGroup (I.prod I') (G × G') :=
  { HasSmoothMul.prod _ _ _ _ with smooth_inv := smooth_fst.inv.prod_mk smooth_snd.inv }

end ProdLieGroup

/-! ### Normed spaces are Lie groups -/


instance normed_space_lie_add_group {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E]
  [NormedSpace 𝕜 E] : LieAddGroup 𝓘(𝕜, E) E :=
  { model_space_smooth with smooth_add := smooth_iff.2 ⟨continuous_add, fun x y => times_cont_diff_add.TimesContDiffOn⟩,
    smooth_neg := smooth_iff.2 ⟨continuous_neg, fun x y => times_cont_diff_neg.TimesContDiffOn⟩ }

