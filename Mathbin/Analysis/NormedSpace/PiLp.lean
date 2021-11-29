import Mathbin.Analysis.MeanInequalities

/-!
# `L^p` distance on finite products of metric spaces
Given finitely many metric spaces, one can put the max distance on their product, but there is also
a whole family of natural distances, indexed by a real parameter `p ∈ [1, ∞)`, that also induce
the product topology. We define them in this file. The distance on `Π i, α i` is given by
$$
d(x, y) = \left(\sum d(x_i, y_i)^p\right)^{1/p}.
$$

We give instances of this construction for emetric spaces, metric spaces, normed groups and normed
spaces.

To avoid conflicting instances, all these are defined on a copy of the original Pi type, named
`pi_Lp p α`. The assumpion `[fact (1 ≤ p)]` is required for the metric and normed space instances.

We ensure that the topology and uniform structure on `pi_Lp p α` are (defeq to) the product
topology and product uniformity, to be able to use freely continuity statements for the coordinate
functions, for instance.

## Implementation notes

We only deal with the `L^p` distance on a product of finitely many metric spaces, which may be
distinct. A closely related construction is the `L^p` norm on the space of
functions from a measure space to a normed space, where the norm is
$$
\left(\int ∥f (x)∥^p dμ\right)^{1/p}.
$$
However, the topology induced by this construction is not the product topology, this only
defines a seminorm (as almost everywhere zero functions have zero `L^p` norm), and some functions
have infinite `L^p` norm. All these subtleties are not present in the case of finitely many
metric spaces (which corresponds to the basis which is a finite space with the counting measure),
hence it is worth devoting a file to this specific case which is particularly well behaved.
The general case is not yet formalized in mathlib.

To prove that the topology (and the uniform structure) on a finite product with the `L^p` distance
are the same as those coming from the `L^∞` distance, we could argue that the `L^p` and `L^∞` norms
are equivalent on `ℝ^n` for abstract (norm equivalence) reasons. Instead, we give a more explicit
(easy) proof which provides a comparison between these two norms with explicit constants.

We also set up the theory for `pseudo_emetric_space` and `pseudo_metric_space`.
-/


open Real Set Filter IsROrC

open_locale BigOperators uniformity TopologicalSpace Nnreal Ennreal

noncomputable theory

variable {ι : Type _}

/-- A copy of a Pi type, on which we will put the `L^p` distance. Since the Pi type itself is
already endowed with the `L^∞` distance, we need the type synonym to avoid confusing typeclass
resolution. Also, we let it depend on `p`, to get a whole family of type on which we can put
different distances. -/
@[nolint unused_arguments]
def PiLp {ι : Type _} (p : ℝ) (α : ι → Type _) : Type _ :=
  ∀ i : ι, α i

instance {ι : Type _} (p : ℝ) (α : ι → Type _) [∀ i, Inhabited (α i)] : Inhabited (PiLp p α) :=
  ⟨fun i => default (α i)⟩

theorem fact_one_le_one_real : Fact ((1 : ℝ) ≤ 1) :=
  ⟨rfl.le⟩

theorem fact_one_le_two_real : Fact ((1 : ℝ) ≤ 2) :=
  ⟨one_le_two⟩

namespace PiLp

variable (p : ℝ) [fact_one_le_p : Fact (1 ≤ p)] (α : ι → Type _) (β : ι → Type _)

/-- Canonical bijection between `pi_Lp p α` and the original Pi type. We introduce it to be able
to compare the `L^p` and `L^∞` distances through it. -/
protected def Equiv : PiLp p α ≃ ∀ i : ι, α i :=
  Equiv.refl _

section 

/-!
### The uniformity on finite `L^p` products is the product uniformity

In this section, we put the `L^p` edistance on `pi_Lp p α`, and we check that the uniformity
coming from this edistance coincides with the product uniformity, by showing that the canonical
map to the Pi type (with the `L^∞` distance) is a uniform embedding, as it is both Lipschitz and
antiLipschitz.

We only register this emetric space structure as a temporary instance, as the true instance (to be
registered later) will have as uniformity exactly the product uniformity, instead of the one coming
from the edistance (which is equal to it, but not defeq). See Note [forgetful inheritance]
explaining why having definitionally the right uniformity is often important.
-/


variable [∀ i, EmetricSpace (α i)] [∀ i, PseudoEmetricSpace (β i)] [Fintype ι]

include fact_one_le_p

/-- Endowing the space `pi_Lp p β` with the `L^p` pseudoedistance. This definition is not
satisfactory, as it does not register the fact that the topology and the uniform structure coincide
with the product one. Therefore, we do not register it as an instance. Using this as a temporary
pseudoemetric space instance, we will show that the uniform structure is equal (but not defeq) to
the product one, and then register an instance in which we replace the uniform structure by the
product one using this pseudoemetric space and `pseudo_emetric_space.replace_uniformity`. -/
def pseudo_emetric_aux : PseudoEmetricSpace (PiLp p β) :=
  have pos : 0 < p := lt_of_lt_of_leₓ zero_lt_one fact_one_le_p.out
  { edist := fun f g => (∑i : ι, edist (f i) (g i)^p)^1 / p,
    edist_self :=
      fun f =>
        by 
          simp [edist, Ennreal.zero_rpow_of_pos Pos, Ennreal.zero_rpow_of_pos (inv_pos.2 Pos)],
    edist_comm :=
      fun f g =>
        by 
          simp [edist, edist_comm],
    edist_triangle :=
      fun f g h =>
        calc ((∑i : ι, edist (f i) (h i)^p)^1 / p) ≤ ((∑i : ι, (edist (f i) (g i)+edist (g i) (h i))^p)^1 / p) :=
          by 
            apply Ennreal.rpow_le_rpow _ (one_div_nonneg.2$ le_of_ltₓ Pos)
            refine' Finset.sum_le_sum fun i hi => _ 
            exact Ennreal.rpow_le_rpow (edist_triangle _ _ _) (le_transₓ zero_le_one fact_one_le_p.out)
          _ ≤ ((∑i : ι, edist (f i) (g i)^p)^1 / p)+(∑i : ι, edist (g i) (h i)^p)^1 / p :=
          Ennreal.Lp_add_le _ _ _ fact_one_le_p.out
           }

-- error in Analysis.NormedSpace.PiLp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Endowing the space `pi_Lp p α` with the `L^p` edistance. This definition is not satisfactory,
as it does not register the fact that the topology and the uniform structure coincide with the
product one. Therefore, we do not register it as an instance. Using this as a temporary emetric
space instance, we will show that the uniform structure is equal (but not defeq) to the product
one, and then register an instance in which we replace the uniform structure by the product one
using this emetric space and `emetric_space.replace_uniformity`. -/ def emetric_aux : emetric_space (pi_Lp p α) :=
{ eq_of_edist_eq_zero := λ f g hfg, begin
    have [ident pos] [":", expr «expr < »(0, p)] [":=", expr lt_of_lt_of_le zero_lt_one fact_one_le_p.out],
    letI [ident h] [] [":=", expr pseudo_emetric_aux p α],
    have [ident h] [":", expr «expr = »(edist f g, «expr ^ »(«expr∑ , »((i : ι), «expr ^ »(edist (f i) (g i), p)), «expr / »(1, p)))] [":=", expr rfl],
    simp [] [] [] ["[", expr h, ",", expr ennreal.rpow_eq_zero_iff, ",", expr pos, ",", expr asymm pos, ",", expr finset.sum_eq_zero_iff_of_nonneg, "]"] [] ["at", ident hfg],
    exact [expr funext hfg]
  end,
  ..pseudo_emetric_aux p α }

attribute [local instance] PiLp.emetricAux PiLp.pseudoEmetricAux

-- error in Analysis.NormedSpace.PiLp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lipschitz_with_equiv : lipschitz_with 1 (pi_Lp.equiv p β) :=
begin
  have [ident pos] [":", expr «expr < »(0, p)] [":=", expr lt_of_lt_of_le zero_lt_one fact_one_le_p.out],
  have [ident cancel] [":", expr «expr = »(«expr * »(p, «expr / »(1, p)), 1)] [":=", expr mul_div_cancel' 1 (ne_of_gt pos)],
  assume [binders (x y)],
  simp [] [] ["only"] ["[", expr edist, ",", expr forall_prop_of_true, ",", expr one_mul, ",", expr finset.mem_univ, ",", expr finset.sup_le_iff, ",", expr ennreal.coe_one, "]"] [] [],
  assume [binders (i)],
  calc
    «expr = »(edist (x i) (y i), «expr ^ »(«expr ^ »(edist (x i) (y i), p), «expr / »(1, p))) : by simp [] [] [] ["[", "<-", expr ennreal.rpow_mul, ",", expr cancel, ",", "-", ident one_div, "]"] [] []
    «expr ≤ »(..., «expr ^ »(«expr∑ , »((i : ι), «expr ^ »(edist (x i) (y i), p)), «expr / »(1, p))) : begin
      apply [expr ennreal.rpow_le_rpow _ «expr $ »(one_div_nonneg.2, le_of_lt pos)],
      exact [expr finset.single_le_sum (λ i hi, (bot_le : «expr ≤ »((0 : «exprℝ≥0∞»()), _))) (finset.mem_univ i)]
    end
end

-- error in Analysis.NormedSpace.PiLp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem antilipschitz_with_equiv : antilipschitz_with «expr ^ »((fintype.card ι : «exprℝ≥0»()), «expr / »(1, p)) (pi_Lp.equiv p β) :=
begin
  have [ident pos] [":", expr «expr < »(0, p)] [":=", expr lt_of_lt_of_le zero_lt_one fact_one_le_p.out],
  have [ident nonneg] [":", expr «expr ≤ »(0, «expr / »(1, p))] [":=", expr one_div_nonneg.2 (le_of_lt pos)],
  have [ident cancel] [":", expr «expr = »(«expr * »(p, «expr / »(1, p)), 1)] [":=", expr mul_div_cancel' 1 (ne_of_gt pos)],
  assume [binders (x y)],
  simp [] [] [] ["[", expr edist, ",", "-", ident one_div, "]"] [] [],
  calc
    «expr ≤ »(«expr ^ »(«expr∑ , »((i : ι), «expr ^ »(edist (x i) (y i), p)), «expr / »(1, p)), «expr ^ »(«expr∑ , »((i : ι), «expr ^ »(edist (pi_Lp.equiv p β x) (pi_Lp.equiv p β y), p)), «expr / »(1, p))) : begin
      apply [expr ennreal.rpow_le_rpow _ nonneg],
      apply [expr finset.sum_le_sum (λ i hi, _)],
      apply [expr ennreal.rpow_le_rpow _ (le_of_lt pos)],
      exact [expr finset.le_sup (finset.mem_univ i)]
    end
    «expr = »(..., «expr * »((«expr ^ »((fintype.card ι : «exprℝ≥0»()), «expr / »(1, p)) : «exprℝ≥0»()), edist (pi_Lp.equiv p β x) (pi_Lp.equiv p β y))) : begin
      simp [] [] ["only"] ["[", expr nsmul_eq_mul, ",", expr finset.card_univ, ",", expr ennreal.rpow_one, ",", expr finset.sum_const, ",", expr ennreal.mul_rpow_of_nonneg _ _ nonneg, ",", "<-", expr ennreal.rpow_mul, ",", expr cancel, "]"] [] [],
      have [] [":", expr «expr = »((fintype.card ι : «exprℝ≥0∞»()), (fintype.card ι : «exprℝ≥0»()))] [":=", expr (ennreal.coe_nat (fintype.card ι)).symm],
      rw ["[", expr this, ",", expr ennreal.coe_rpow_of_nonneg _ nonneg, "]"] []
    end
end

-- error in Analysis.NormedSpace.PiLp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem aux_uniformity_eq : «expr = »(expr𝓤() (pi_Lp p β), @uniformity _ (Pi.uniform_space _)) :=
begin
  have [ident A] [":", expr uniform_inducing (pi_Lp.equiv p β)] [":=", expr (antilipschitz_with_equiv p β).uniform_inducing (lipschitz_with_equiv p β).uniform_continuous],
  have [] [":", expr «expr = »(λ
    x : «expr × »(pi_Lp p β, pi_Lp p β), (pi_Lp.equiv p β x.fst, pi_Lp.equiv p β x.snd), id)] [],
  by ext [] [ident i] []; refl,
  rw ["[", "<-", expr A.comap_uniformity, ",", expr this, ",", expr comap_id, "]"] []
end

end 

/-! ### Instances on finite `L^p` products -/


instance UniformSpace [∀ i, UniformSpace (β i)] : UniformSpace (PiLp p β) :=
  Pi.uniformSpace _

variable [Fintype ι]

include fact_one_le_p

/-- pseudoemetric space instance on the product of finitely many pseudoemetric spaces, using the
`L^p` pseudoedistance, and having as uniformity the product uniformity. -/
instance [∀ i, PseudoEmetricSpace (β i)] : PseudoEmetricSpace (PiLp p β) :=
  (pseudo_emetric_aux p β).replaceUniformity (aux_uniformity_eq p β).symm

/-- emetric space instance on the product of finitely many emetric spaces, using the `L^p`
edistance, and having as uniformity the product uniformity. -/
instance [∀ i, EmetricSpace (α i)] : EmetricSpace (PiLp p α) :=
  (emetric_aux p α).replaceUniformity (aux_uniformity_eq p α).symm

omit fact_one_le_p

protected theorem edist {p : ℝ} [Fact (1 ≤ p)] {β : ι → Type _} [∀ i, PseudoEmetricSpace (β i)] (x y : PiLp p β) :
  edist x y = ((∑i : ι, edist (x i) (y i)^p)^1 / p) :=
  rfl

include fact_one_le_p

-- error in Analysis.NormedSpace.PiLp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- pseudometric space instance on the product of finitely many psuedometric spaces, using the
`L^p` distance, and having as uniformity the product uniformity. -/
instance [∀ i, pseudo_metric_space (β i)] : pseudo_metric_space (pi_Lp p β) :=
begin
  have [ident pos] [":", expr «expr < »(0, p)] [":=", expr lt_of_lt_of_le zero_lt_one fact_one_le_p.out],
  refine [expr pseudo_emetric_space.to_pseudo_metric_space_of_dist (λ
    f g, «expr ^ »(«expr∑ , »((i : ι), «expr ^ »(dist (f i) (g i), p)), «expr / »(1, p))) (λ f g, _) (λ f g, _)],
  { simp [] [] [] ["[", expr pi_Lp.edist, ",", expr ennreal.rpow_eq_top_iff, ",", expr asymm pos, ",", expr pos, ",", expr ennreal.sum_eq_top_iff, ",", expr edist_ne_top, "]"] [] [] },
  { have [ident A] [":", expr ∀
     i : ι, «expr ∈ »(i, (finset.univ : finset ι)) → «expr ≠ »(«expr ^ »(edist (f i) (g i), p), «expr⊤»())] [":=", expr λ
     i hi, by simp [] [] [] ["[", expr lt_top_iff_ne_top, ",", expr edist_ne_top, ",", expr le_of_lt pos, "]"] [] []],
    simp [] [] [] ["[", expr dist, ",", "-", ident one_div, ",", expr pi_Lp.edist, ",", "<-", expr ennreal.to_real_rpow, ",", expr ennreal.to_real_sum A, ",", expr dist_edist, "]"] [] [] }
end

-- error in Analysis.NormedSpace.PiLp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- metric space instance on the product of finitely many metric spaces, using the `L^p` distance,
and having as uniformity the product uniformity. -/ instance [∀ i, metric_space (α i)] : metric_space (pi_Lp p α) :=
begin
  have [ident pos] [":", expr «expr < »(0, p)] [":=", expr lt_of_lt_of_le zero_lt_one fact_one_le_p.out],
  refine [expr emetric_space.to_metric_space_of_dist (λ
    f g, «expr ^ »(«expr∑ , »((i : ι), «expr ^ »(dist (f i) (g i), p)), «expr / »(1, p))) (λ f g, _) (λ f g, _)],
  { simp [] [] [] ["[", expr pi_Lp.edist, ",", expr ennreal.rpow_eq_top_iff, ",", expr asymm pos, ",", expr pos, ",", expr ennreal.sum_eq_top_iff, ",", expr edist_ne_top, "]"] [] [] },
  { have [ident A] [":", expr ∀
     i : ι, «expr ∈ »(i, (finset.univ : finset ι)) → «expr ≠ »(«expr ^ »(edist (f i) (g i), p), «expr⊤»())] [":=", expr λ
     i hi, by simp [] [] [] ["[", expr edist_ne_top, ",", expr pos.le, "]"] [] []],
    simp [] [] [] ["[", expr dist, ",", "-", ident one_div, ",", expr pi_Lp.edist, ",", "<-", expr ennreal.to_real_rpow, ",", expr ennreal.to_real_sum A, ",", expr dist_edist, "]"] [] [] }
end

omit fact_one_le_p

protected theorem dist {p : ℝ} [Fact (1 ≤ p)] {β : ι → Type _} [∀ i, PseudoMetricSpace (β i)] (x y : PiLp p β) :
  dist x y = ((∑i : ι, dist (x i) (y i)^p)^1 / p) :=
  rfl

include fact_one_le_p

/-- seminormed group instance on the product of finitely many normed groups, using the `L^p`
norm. -/
instance SemiNormedGroup [∀ i, SemiNormedGroup (β i)] : SemiNormedGroup (PiLp p β) :=
  { Pi.addCommGroup with norm := fun f => (∑i : ι, norm (f i)^p)^1 / p,
    dist_eq :=
      fun x y =>
        by 
          simp [PiLp.dist, dist_eq_norm, sub_eq_add_neg] }

/-- normed group instance on the product of finitely many normed groups, using the `L^p` norm. -/
instance NormedGroup [∀ i, NormedGroup (α i)] : NormedGroup (PiLp p α) :=
  { PiLp.semiNormedGroup p α with  }

omit fact_one_le_p

theorem norm_eq {p : ℝ} [Fact (1 ≤ p)] {β : ι → Type _} [∀ i, SemiNormedGroup (β i)] (f : PiLp p β) :
  ∥f∥ = ((∑i : ι, ∥f i∥^p)^1 / p) :=
  rfl

theorem norm_eq_of_nat {p : ℝ} [Fact (1 ≤ p)] {β : ι → Type _} [∀ i, SemiNormedGroup (β i)] (n : ℕ) (h : p = n)
  (f : PiLp p β) : ∥f∥ = ((∑i : ι, ∥f i∥^n)^1 / (n : ℝ)) :=
  by 
    simp [norm_eq, h, Real.sqrt_eq_rpow, ←Real.rpow_nat_cast]

include fact_one_le_p

variable (𝕜 : Type _) [NormedField 𝕜]

-- error in Analysis.NormedSpace.PiLp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The product of finitely many seminormed spaces is a seminormed space, with the `L^p` norm. -/
instance semi_normed_space
[∀ i, semi_normed_group (β i)]
[∀ i, semi_normed_space 𝕜 (β i)] : semi_normed_space 𝕜 (pi_Lp p β) :=
{ norm_smul_le := begin
    assume [binders (c f)],
    have [] [":", expr «expr = »(«expr * »(p, «expr / »(1, p)), 1)] [":=", expr mul_div_cancel' 1 (lt_of_lt_of_le zero_lt_one fact_one_le_p.out).ne'],
    simp [] [] ["only"] ["[", expr pi_Lp.norm_eq, ",", expr norm_smul, ",", expr mul_rpow, ",", expr norm_nonneg, ",", "<-", expr finset.mul_sum, ",", expr pi.smul_apply, "]"] [] [],
    rw ["[", expr mul_rpow (rpow_nonneg_of_nonneg (norm_nonneg _) _), ",", "<-", expr rpow_mul (norm_nonneg _), ",", expr this, ",", expr rpow_one, "]"] [],
    exact [expr finset.sum_nonneg (λ i hi, rpow_nonneg_of_nonneg (norm_nonneg _) _)]
  end,
  ..pi.module ι β 𝕜 }

/-- The product of finitely many normed spaces is a normed space, with the `L^p` norm. -/
instance NormedSpace [∀ i, NormedGroup (α i)] [∀ i, NormedSpace 𝕜 (α i)] : NormedSpace 𝕜 (PiLp p α) :=
  { PiLp.semiNormedSpace p α 𝕜 with  }

variable {𝕜 p α} [∀ i, SemiNormedGroup (β i)] [∀ i, SemiNormedSpace 𝕜 (β i)] (c : 𝕜) (x y : PiLp p β) (i : ι)

@[simp]
theorem add_apply : (x+y) i = x i+y i :=
  rfl

@[simp]
theorem sub_apply : (x - y) i = x i - y i :=
  rfl

@[simp]
theorem smul_apply : (c • x) i = c • x i :=
  rfl

@[simp]
theorem neg_apply : (-x) i = -x i :=
  rfl

end PiLp

