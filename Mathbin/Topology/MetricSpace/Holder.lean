import Mathbin.Topology.MetricSpace.Lipschitz 
import Mathbin.Analysis.SpecialFunctions.Pow

/-!
# Hölder continuous functions

In this file we define Hölder continuity on a set and on the whole space. We also prove some basic
properties of Hölder continuous functions.

## Main definitions

* `holder_on_with`: `f : X → Y` is said to be *Hölder continuous* with constant `C : ℝ≥0` and
  exponent `r : ℝ≥0` on a set `s`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y ∈ s`;
* `holder_with`: `f : X → Y` is said to be *Hölder continuous* with constant `C : ℝ≥0` and exponent
  `r : ℝ≥0`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y : X`.

## Implementation notes

We use the type `ℝ≥0` (a.k.a. `nnreal`) for `C` because this type has coercion both to `ℝ` and
`ℝ≥0∞`, so it can be easily used both in inequalities about `dist` and `edist`. We also use `ℝ≥0`
for `r` to ensure that `d ^ r` is monotone in `d`. It might be a good idea to use
`ℝ>0` for `r` but we don't have this type in `mathlib` (yet).

## Tags

Hölder continuity, Lipschitz continuity

 -/


variable{X Y Z : Type _}

open Filter Set

open_locale Nnreal Ennreal TopologicalSpace

section Emetric

variable[PseudoEmetricSpace X][PseudoEmetricSpace Y][PseudoEmetricSpace Z]

/-- A function `f : X → Y` between two `pseudo_emetric_space`s is Hölder continuous with constant
`C : ℝ≥0` and exponent `r : ℝ≥0`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y : X`. -/
def HolderWith (C r :  ℝ≥0 ) (f : X → Y) : Prop :=
  ∀ x y, edist (f x) (f y) ≤ C*edist x y^(r : ℝ)

/-- A function `f : X → Y` between two `pseudo_emeteric_space`s is Hölder continuous with constant
`C : ℝ≥0` and exponent `r : ℝ≥0` on a set `s : set X`, if `edist (f x) (f y) ≤ C * edist x y ^ r`
for all `x y ∈ s`. -/
def HolderOnWith (C r :  ℝ≥0 ) (f : X → Y) (s : Set X) : Prop :=
  ∀ x _ : x ∈ s y _ : y ∈ s, edist (f x) (f y) ≤ C*edist x y^(r : ℝ)

@[simp]
theorem holder_on_with_empty (C r :  ℝ≥0 ) (f : X → Y) : HolderOnWith C r f ∅ :=
  fun x hx => hx.elim

@[simp]
theorem holder_on_with_singleton (C r :  ℝ≥0 ) (f : X → Y) (x : X) : HolderOnWith C r f {x} :=
  by 
    rintro a (rfl : a = x) b (rfl : b = a)
    rw [edist_self]
    exact zero_le _

theorem Set.Subsingleton.holder_on_with {s : Set X} (hs : s.subsingleton) (C r :  ℝ≥0 ) (f : X → Y) :
  HolderOnWith C r f s :=
  hs.induction_on (holder_on_with_empty C r f) (holder_on_with_singleton C r f)

theorem holder_on_with_univ {C r :  ℝ≥0 } {f : X → Y} : HolderOnWith C r f univ ↔ HolderWith C r f :=
  by 
    simp only [HolderOnWith, HolderWith, mem_univ, true_implies_iff]

@[simp]
theorem holder_on_with_one {C :  ℝ≥0 } {f : X → Y} {s : Set X} : HolderOnWith C 1 f s ↔ LipschitzOnWith C f s :=
  by 
    simp only [HolderOnWith, LipschitzOnWith, Nnreal.coe_one, Ennreal.rpow_one]

alias holder_on_with_one ↔ _ LipschitzOnWith.holder_on_with

@[simp]
theorem holder_with_one {C :  ℝ≥0 } {f : X → Y} : HolderWith C 1 f ↔ LipschitzWith C f :=
  holder_on_with_univ.symm.trans$ holder_on_with_one.trans lipschitz_on_univ

alias holder_with_one ↔ _ LipschitzWith.holder_with

theorem holder_with_id : HolderWith 1 1 (id : X → X) :=
  LipschitzWith.id.HolderWith

protected theorem HolderWith.holder_on_with {C r :  ℝ≥0 } {f : X → Y} (h : HolderWith C r f) (s : Set X) :
  HolderOnWith C r f s :=
  fun x _ y _ => h x y

namespace HolderOnWith

variable{C r :  ℝ≥0 }{f : X → Y}{s t : Set X}

theorem edist_le (h : HolderOnWith C r f s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
  edist (f x) (f y) ≤ C*edist x y^(r : ℝ) :=
  h x hx y hy

theorem edist_le_of_le (h : HolderOnWith C r f s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) {d : ℝ≥0∞} (hd : edist x y ≤ d) :
  edist (f x) (f y) ≤ C*d^(r : ℝ) :=
  (h.edist_le hx hy).trans (mul_le_mul_left' (Ennreal.rpow_le_rpow hd r.coe_nonneg) _)

theorem comp {Cg rg :  ℝ≥0 } {g : Y → Z} {t : Set Y} (hg : HolderOnWith Cg rg g t) {Cf rf :  ℝ≥0 } {f : X → Y}
  (hf : HolderOnWith Cf rf f s) (hst : maps_to f s t) : HolderOnWith (Cg*Cf^(rg : ℝ)) (rg*rf) (g ∘ f) s :=
  by 
    intro x hx y hy 
    rw [Ennreal.coe_mul, mul_commₓ rg, Nnreal.coe_mul, Ennreal.rpow_mul, mul_assocₓ,
      ←Ennreal.coe_rpow_of_nonneg _ rg.coe_nonneg, ←Ennreal.mul_rpow_of_nonneg _ _ rg.coe_nonneg]
    exact hg.edist_le_of_le (hst hx) (hst hy) (hf.edist_le hx hy)

theorem comp_holder_with {Cg rg :  ℝ≥0 } {g : Y → Z} {t : Set Y} (hg : HolderOnWith Cg rg g t) {Cf rf :  ℝ≥0 }
  {f : X → Y} (hf : HolderWith Cf rf f) (ht : ∀ x, f x ∈ t) : HolderWith (Cg*Cf^(rg : ℝ)) (rg*rf) (g ∘ f) :=
  holder_on_with_univ.mp$ hg.comp (hf.holder_on_with univ) fun x _ => ht x

-- error in Topology.MetricSpace.Holder: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A Hölder continuous function is uniformly continuous -/
protected
theorem uniform_continuous_on (hf : holder_on_with C r f s) (h0 : «expr < »(0, r)) : uniform_continuous_on f s :=
begin
  refine [expr emetric.uniform_continuous_on_iff.2 (λ ε εpos, _)],
  have [] [":", expr tendsto (λ
    d : «exprℝ≥0∞»(), «expr * »((C : «exprℝ≥0∞»()), «expr ^ »(d, (r : exprℝ())))) (expr𝓝() 0) (expr𝓝() 0)] [],
  from [expr ennreal.tendsto_const_mul_rpow_nhds_zero_of_pos ennreal.coe_ne_top h0],
  rcases [expr ennreal.nhds_zero_basis.mem_iff.1 (this (gt_mem_nhds εpos)), "with", "⟨", ident δ, ",", ident δ0, ",", ident H, "⟩"],
  exact [expr ⟨δ, δ0, λ x y hx hy h, (hf.edist_le hx hy).trans_lt (H h)⟩]
end

protected theorem ContinuousOn (hf : HolderOnWith C r f s) (h0 : 0 < r) : ContinuousOn f s :=
  (hf.uniform_continuous_on h0).ContinuousOn

protected theorem mono (hf : HolderOnWith C r f s) (ht : t ⊆ s) : HolderOnWith C r f t :=
  fun x hx y hy => hf.edist_le (ht hx) (ht hy)

theorem ediam_image_le_of_le (hf : HolderOnWith C r f s) {d : ℝ≥0∞} (hd : Emetric.diam s ≤ d) :
  Emetric.diam (f '' s) ≤ C*d^(r : ℝ) :=
  Emetric.diam_image_le_iff.2$ fun x hx y hy => hf.edist_le_of_le hx hy$ (Emetric.edist_le_diam_of_mem hx hy).trans hd

theorem ediam_image_le (hf : HolderOnWith C r f s) : Emetric.diam (f '' s) ≤ C*Emetric.diam s^(r : ℝ) :=
  hf.ediam_image_le_of_le le_rfl

theorem ediam_image_le_of_subset (hf : HolderOnWith C r f s) (ht : t ⊆ s) :
  Emetric.diam (f '' t) ≤ C*Emetric.diam t^(r : ℝ) :=
  (hf.mono ht).ediam_image_le

theorem ediam_image_le_of_subset_of_le (hf : HolderOnWith C r f s) (ht : t ⊆ s) {d : ℝ≥0∞} (hd : Emetric.diam t ≤ d) :
  Emetric.diam (f '' t) ≤ C*d^(r : ℝ) :=
  (hf.mono ht).ediam_image_le_of_le hd

theorem ediam_image_inter_le_of_le (hf : HolderOnWith C r f s) {d : ℝ≥0∞} (hd : Emetric.diam t ≤ d) :
  Emetric.diam (f '' (t ∩ s)) ≤ C*d^(r : ℝ) :=
  hf.ediam_image_le_of_subset_of_le (inter_subset_right _ _)$ (Emetric.diam_mono$ inter_subset_left _ _).trans hd

theorem ediam_image_inter_le (hf : HolderOnWith C r f s) (t : Set X) :
  Emetric.diam (f '' (t ∩ s)) ≤ C*Emetric.diam t^(r : ℝ) :=
  hf.ediam_image_inter_le_of_le le_rfl

end HolderOnWith

namespace HolderWith

variable{C r :  ℝ≥0 }{f : X → Y}

theorem edist_le (h : HolderWith C r f) (x y : X) : edist (f x) (f y) ≤ C*edist x y^(r : ℝ) :=
  h x y

theorem edist_le_of_le (h : HolderWith C r f) {x y : X} {d : ℝ≥0∞} (hd : edist x y ≤ d) :
  edist (f x) (f y) ≤ C*d^(r : ℝ) :=
  (h.holder_on_with univ).edist_le_of_le trivialₓ trivialₓ hd

theorem comp {Cg rg :  ℝ≥0 } {g : Y → Z} (hg : HolderWith Cg rg g) {Cf rf :  ℝ≥0 } {f : X → Y}
  (hf : HolderWith Cf rf f) : HolderWith (Cg*Cf^(rg : ℝ)) (rg*rf) (g ∘ f) :=
  (hg.holder_on_with univ).comp_holder_with hf fun _ => trivialₓ

theorem comp_holder_on_with {Cg rg :  ℝ≥0 } {g : Y → Z} (hg : HolderWith Cg rg g) {Cf rf :  ℝ≥0 } {f : X → Y}
  {s : Set X} (hf : HolderOnWith Cf rf f s) : HolderOnWith (Cg*Cf^(rg : ℝ)) (rg*rf) (g ∘ f) s :=
  (hg.holder_on_with univ).comp hf fun _ _ => trivialₓ

/-- A Hölder continuous function is uniformly continuous -/
protected theorem UniformContinuous (hf : HolderWith C r f) (h0 : 0 < r) : UniformContinuous f :=
  uniform_continuous_on_univ.mp$ (hf.holder_on_with univ).UniformContinuousOn h0

protected theorem Continuous (hf : HolderWith C r f) (h0 : 0 < r) : Continuous f :=
  (hf.uniform_continuous h0).Continuous

theorem ediam_image_le (hf : HolderWith C r f) (s : Set X) : Emetric.diam (f '' s) ≤ C*Emetric.diam s^(r : ℝ) :=
  Emetric.diam_image_le_iff.2$ fun x hx y hy => hf.edist_le_of_le$ Emetric.edist_le_diam_of_mem hx hy

end HolderWith

end Emetric

section Metric

variable[PseudoMetricSpace X][PseudoMetricSpace Y]{C r :  ℝ≥0 }{f : X → Y}

namespace HolderWith

theorem nndist_le_of_le (hf : HolderWith C r f) {x y : X} {d :  ℝ≥0 } (hd : nndist x y ≤ d) :
  nndist (f x) (f y) ≤ C*d^(r : ℝ) :=
  by 
    rw [←Ennreal.coe_le_coe, ←edist_nndist, Ennreal.coe_mul, ←Ennreal.coe_rpow_of_nonneg _ r.coe_nonneg]
    apply hf.edist_le_of_le 
    rwa [edist_nndist, Ennreal.coe_le_coe]

theorem nndist_le (hf : HolderWith C r f) (x y : X) : nndist (f x) (f y) ≤ C*nndist x y^(r : ℝ) :=
  hf.nndist_le_of_le le_rfl

theorem dist_le_of_le (hf : HolderWith C r f) {x y : X} {d : ℝ} (hd : dist x y ≤ d) : dist (f x) (f y) ≤ C*d^(r : ℝ) :=
  by 
    lift d to  ℝ≥0  using dist_nonneg.trans hd 
    rw [dist_nndist] at hd⊢
    normCast  at hd⊢
    exact hf.nndist_le_of_le hd

theorem dist_le (hf : HolderWith C r f) (x y : X) : dist (f x) (f y) ≤ C*dist x y^(r : ℝ) :=
  hf.dist_le_of_le le_rfl

end HolderWith

end Metric

