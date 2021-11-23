import Mathbin.Analysis.Convex.Function 
import Mathbin.Analysis.NormedSpace.Ordered 
import Mathbin.Data.Real.Pointwise

/-!
# Seminorms and Local Convexity

This file defines absorbent sets, balanced sets, seminorms and the Minkowski functional.

An absorbent set is one that "surrounds" the origin. The idea is made precise by requiring that any
point belongs to all large enough scalings of the set. This is the vector world analog of a
topological neighborhood of the origin.

A balanced set is one that is everywhere around the origin. This means that `a • s ⊆ s` for all `a`
of norm less than `1`.

A seminorm is a function to the reals which is positive-semidefinite, absolutely homogeneous, and
subadditive. They are closely related to convex sets and a topological vector space is locally
convex if and only if its topology is induced by a family of seminorms.

The Minkowski functional of a set `s` is the function which associates each point to how much you
need to scale `s` for `x` to be inside it. When `s` is symmetric, convex and absorbent, its gauge is
a seminorm. Reciprocally, any seminorm arises as the gauge of some set, namely its unit ball. This
induces the equivalence of seminorms and locally convex topological vector spaces.

## Main declarations

For a vector space over a normed field:
* `absorbent`: A set `s` is absorbent if every point eventually belongs to all large scalings of
  `s`.
* `balanced`: A set `s` is balanced if `a • s ⊆ s` for all `a` of norm less than `1`.
* `seminorm`: A function to the reals that is positive-semidefinite, absolutely homogeneous, and
  subadditive.
* `gauge`: Aka Minkowksi functional. `gauge s x` is the least (actually, an infimum) `r` such
  that `x ∈ r • s`.
* `gauge_seminorm`: The Minkowski functional as a seminorm, when `s` is symmetric, convex and
  absorbent.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## TODO

Define and show equivalence of two notions of local convexity for a
topological vector space over ℝ or ℂ: that it has a local base of
balanced convex absorbent sets, and that it carries the initial
topology induced by a family of seminorms.

Prove the properties of balanced and absorbent sets of a real vector space.

## Tags

absorbent, balanced, seminorm, Minkowski functional, gauge, locally convex, LCTVS
-/


/-!
### Set Properties

Absorbent and balanced sets in a vector space over a normed field.
-/


open NormedField Set

open_locale Pointwise TopologicalSpace

variable{𝕜 E : Type _}

section NormedField

variable(𝕜)[NormedField 𝕜][AddCommGroupₓ E][Module 𝕜 E]

/-- A set `A` absorbs another set `B` if `B` is contained in all scalings of
`A` by elements of sufficiently large norms. -/
def Absorbs (A B : Set E) :=
  ∃ r, 0 < r ∧ ∀ a : 𝕜, r ≤ ∥a∥ → B ⊆ a • A

/-- A set is absorbent if it absorbs every singleton. -/
def Absorbent (A : Set E) :=
  ∀ x, ∃ r, 0 < r ∧ ∀ a : 𝕜, r ≤ ∥a∥ → x ∈ a • A

/-- A set `A` is balanced if `a • A` is contained in `A` whenever `a`
has norm less than or equal to one. -/
def Balanced (A : Set E) :=
  ∀ a : 𝕜, ∥a∥ ≤ 1 → a • A ⊆ A

variable{𝕜}(a : 𝕜){A B : Set E}

/-- A balanced set absorbs itself. -/
theorem Balanced.absorbs_self (hA : Balanced 𝕜 A) : Absorbs 𝕜 A A :=
  by 
    use 1, zero_lt_one 
    intro a ha x hx 
    rw [mem_smul_set_iff_inv_smul_mem₀]
    ·
      apply hA (a⁻¹)
      ·
        rw [norm_inv]
        exact inv_le_one ha
      ·
        rw [mem_smul_set]
        use x, hx
    ·
      rw [←norm_pos_iff]
      calc 0 < 1 := zero_lt_one _ ≤ ∥a∥ := ha

theorem Balanced.univ : Balanced 𝕜 (univ : Set E) :=
  fun a ha => subset_univ _

theorem Balanced.union {A₁ A₂ : Set E} (hA₁ : Balanced 𝕜 A₁) (hA₂ : Balanced 𝕜 A₂) : Balanced 𝕜 (A₁ ∪ A₂) :=
  by 
    intro a ha t ht 
    rw [smul_set_union] at ht 
    exact ht.imp (fun x => hA₁ _ ha x) fun x => hA₂ _ ha x

theorem Balanced.inter {A₁ A₂ : Set E} (hA₁ : Balanced 𝕜 A₁) (hA₂ : Balanced 𝕜 A₂) : Balanced 𝕜 (A₁ ∩ A₂) :=
  by 
    rintro a ha _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
    exact ⟨hA₁ _ ha ⟨_, hx₁, rfl⟩, hA₂ _ ha ⟨_, hx₂, rfl⟩⟩

theorem Balanced.add {A₁ A₂ : Set E} (hA₁ : Balanced 𝕜 A₁) (hA₂ : Balanced 𝕜 A₂) : Balanced 𝕜 (A₁+A₂) :=
  by 
    rintro a ha _ ⟨_, ⟨x, y, hx, hy, rfl⟩, rfl⟩
    rw [smul_add]
    exact ⟨_, _, hA₁ _ ha ⟨_, hx, rfl⟩, hA₂ _ ha ⟨_, hy, rfl⟩, rfl⟩

theorem Balanced.smul (hA : Balanced 𝕜 A) : Balanced 𝕜 (a • A) :=
  by 
    rintro b hb _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨b • x, hA _ hb ⟨_, hx, rfl⟩, smul_comm _ _ _⟩

theorem Balanced.subset_smul (hA : Balanced 𝕜 A) {a : 𝕜} (ha : 1 ≤ ∥a∥) : A ⊆ a • A :=
  by 
    refine' (subset_set_smul_iff₀ _).2 (hA (a⁻¹) _)
    ·
      rintro rfl 
      rw [norm_zero] at ha 
      exact zero_lt_one.not_le ha
    ·
      rw [norm_inv]
      exact inv_le_one ha

theorem Balanced.smul_eq (hA : Balanced 𝕜 A) {a : 𝕜} (ha : ∥a∥ = 1) : a • A = A :=
  (hA _ ha.le).antisymm$ hA.subset_smul ha.ge

theorem Absorbent.subset (hA : Absorbent 𝕜 A) (hAB : A ⊆ B) : Absorbent 𝕜 B :=
  by 
    rintro x 
    obtain ⟨r, hr, hx⟩ := hA x 
    refine' ⟨r, hr, fun a ha => (set_smul_subset_set_smul_iff₀ _).2 hAB$ hx a ha⟩
    rintro rfl 
    rw [norm_zero] at ha 
    exact hr.not_le ha

theorem absorbent_iff_forall_absorbs_singleton : Absorbent 𝕜 A ↔ ∀ x, Absorbs 𝕜 A {x} :=
  by 
    simp [Absorbs, Absorbent]

theorem absorbent_iff_nonneg_lt : Absorbent 𝕜 A ↔ ∀ x, ∃ r, 0 ≤ r ∧ ∀ a : 𝕜, r < ∥a∥ → x ∈ a • A :=
  by 
    split 
    ·
      rintro hA x 
      obtain ⟨r, hr, hx⟩ := hA x 
      exact ⟨r, hr.le, fun a ha => hx a ha.le⟩
    ·
      rintro hA x 
      obtain ⟨r, hr, hx⟩ := hA x 
      exact
        ⟨r+1, add_pos_of_nonneg_of_pos hr zero_lt_one,
          fun a ha => hx a ((lt_add_of_pos_right r zero_lt_one).trans_le ha)⟩

/-!
Properties of balanced and absorbent sets in a topological vector space:
-/


variable[TopologicalSpace E][HasContinuousSmul 𝕜 E]

-- error in Analysis.Seminorm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Every neighbourhood of the origin is absorbent. -/
theorem absorbent_nhds_zero (hA : «expr ∈ »(A, expr𝓝() (0 : E))) : absorbent 𝕜 A :=
begin
  intro [ident x],
  rcases [expr mem_nhds_iff.mp hA, "with", "⟨", ident w, ",", ident hw₁, ",", ident hw₂, ",", ident hw₃, "⟩"],
  have [ident hc] [":", expr continuous (λ t : 𝕜, «expr • »(t, x))] [],
  from [expr continuous_id.smul continuous_const],
  rcases [expr metric.is_open_iff.mp (hw₂.preimage hc) 0 (by rwa ["[", expr mem_preimage, ",", expr zero_smul, "]"] []), "with", "⟨", ident r, ",", ident hr₁, ",", ident hr₂, "⟩"],
  have [ident hr₃] [] [],
  from [expr inv_pos.mpr (half_pos hr₁)],
  use ["[", expr «expr ⁻¹»(«expr / »(r, 2)), ",", expr hr₃, "]"],
  intros [ident a, ident ha₁],
  have [ident ha₂] [":", expr «expr < »(0, «expr∥ ∥»(a))] [":=", expr hr₃.trans_le ha₁],
  have [ident ha₃] [":", expr «expr ∈ »(«expr • »(«expr ⁻¹»(a), x), w)] [],
  { apply [expr hr₂],
    rw ["[", expr metric.mem_ball, ",", expr dist_zero_right, ",", expr norm_inv, "]"] [],
    calc
      «expr ≤ »(«expr ⁻¹»(«expr∥ ∥»(a)), «expr / »(r, 2)) : (inv_le (half_pos hr₁) ha₂).mp ha₁
      «expr < »(..., r) : half_lt_self hr₁ },
  rw ["[", expr mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.mp ha₂), "]"] [],
  exact [expr hw₁ ha₃]
end

/-- The union of `{0}` with the interior of a balanced set
    is balanced. -/
theorem balanced_zero_union_interior (hA : Balanced 𝕜 A) : Balanced 𝕜 ({(0 : E)} ∪ Interior A) :=
  by 
    intro a ha 
    byCases' a = 0
    ·
      rw [h, zero_smul_set]
      exacts[subset_union_left _ _, ⟨0, Or.inl rfl⟩]
    ·
      rw [←image_smul, image_union]
      apply union_subset_union
      ·
        rw [image_singleton, smul_zero]
      ·
        calc a • Interior A ⊆ Interior (a • A) := (is_open_map_smul₀ h).image_interior_subset A _ ⊆ Interior A :=
          interior_mono (hA _ ha)

/-- The interior of a balanced set is balanced if it contains the origin. -/
theorem Balanced.interior (hA : Balanced 𝕜 A) (h : (0 : E) ∈ Interior A) : Balanced 𝕜 (Interior A) :=
  by 
    rw [←singleton_subset_iff] at h 
    rw [←union_eq_self_of_subset_left h]
    exact balanced_zero_union_interior hA

/-- The closure of a balanced set is balanced. -/
theorem Balanced.closure (hA : Balanced 𝕜 A) : Balanced 𝕜 (Closure A) :=
  fun a ha =>
    calc _ ⊆ Closure (a • A) := image_closure_subset_closure_image (continuous_id.const_smul _)
      _ ⊆ _ := closure_mono (hA _ ha)
      

end NormedField

/-!
### Seminorms
-/


/-- A seminorm on a vector space over a normed field is a function to
the reals that is positive semidefinite, positive homogeneous, and
subadditive. -/
structure Seminorm(𝕜 : Type _)(E : Type _)[NormedField 𝕜][AddCommGroupₓ E][Module 𝕜 E] where 
  toFun : E → ℝ 
  smul' : ∀ a : 𝕜 x : E, to_fun (a • x) = ∥a∥*to_fun x 
  triangle' : ∀ x y : E, to_fun (x+y) ≤ to_fun x+to_fun y

namespace Seminorm

section NormedField

variable[NormedField 𝕜][AddCommGroupₓ E][Module 𝕜 E]

instance  : Inhabited (Seminorm 𝕜 E) :=
  ⟨{ toFun := fun _ => 0, smul' := fun _ _ => (mul_zero _).symm,
      triangle' :=
        fun x y =>
          by 
            rw [add_zeroₓ] }⟩

instance  : CoeFun (Seminorm 𝕜 E) fun _ => E → ℝ :=
  ⟨fun p => p.to_fun⟩

-- error in Analysis.Seminorm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[ext #[]] theorem ext {p q : seminorm 𝕜 E} (h : «expr = »((p : E → exprℝ()), q)) : «expr = »(p, q) :=
begin
  cases [expr p] [],
  cases [expr q] [],
  have [] [":", expr «expr = »(p_to_fun, q_to_fun)] [":=", expr h],
  simp_rw [expr this] []
end

variable(p : Seminorm 𝕜 E)(c : 𝕜)(x y : E)(r : ℝ)

protected theorem smul : p (c • x) = ∥c∥*p x :=
  p.smul' _ _

protected theorem triangle : p (x+y) ≤ p x+p y :=
  p.triangle' _ _

protected theorem sub_le : p (x - y) ≤ p x+p y :=
  calc p (x - y) = p (x+-y) :=
    by 
      rw [sub_eq_add_neg]
    _ ≤ p x+p (-y) := p.triangle x (-y)
    _ = p x+p y :=
    by 
      rw [←neg_one_smul 𝕜 y, p.smul, norm_neg, norm_one, one_mulₓ]
    

@[simp]
protected theorem zero : p 0 = 0 :=
  calc p 0 = p ((0 : 𝕜) • 0) :=
    by 
      rw [zero_smul]
    _ = 0 :=
    by 
      rw [p.smul, norm_zero, zero_mul]
    

@[simp]
protected theorem neg : p (-x) = p x :=
  calc p (-x) = p ((-1 : 𝕜) • x) :=
    by 
      rw [neg_one_smul]
    _ = p x :=
    by 
      rw [p.smul, norm_neg, norm_one, one_mulₓ]
    

theorem nonneg : 0 ≤ p x :=
  have h : 0 ≤ 2*p x :=
    calc 0 = p (x+-x) :=
      by 
        rw [add_neg_selfₓ, p.zero]
      _ ≤ p x+p (-x) := p.triangle _ _ 
      _ = 2*p x :=
      by 
        rw [p.neg, two_mul]
      
  nonneg_of_mul_nonneg_left h zero_lt_two

theorem sub_rev : p (x - y) = p (y - x) :=
  by 
    rw [←neg_sub, p.neg]

/-- The ball of radius `r` at `x` with respect to seminorm `p`
    is the set of elements `y` with `p (y - x) < `r`. -/
def ball (p : Seminorm 𝕜 E) (x : E) (r : ℝ) :=
  { y:E | p (y - x) < r }

theorem mem_ball : y ∈ ball p x r ↔ p (y - x) < r :=
  Iff.rfl

theorem mem_ball_zero : y ∈ ball p 0 r ↔ p y < r :=
  by 
    rw [mem_ball, sub_zero]

theorem ball_zero_eq : ball p 0 r = { y:E | p y < r } :=
  Set.ext$
    fun x =>
      by 
        rw [mem_ball_zero]
        exact Iff.rfl

/-- Seminorm-balls at the origin are balanced. -/
theorem balanced_ball_zero : Balanced 𝕜 (ball p 0 r) :=
  by 
    rintro a ha x ⟨y, hy, hx⟩
    rw [mem_ball_zero, ←hx, p.smul]
    calc _ ≤ p y := mul_le_of_le_one_left (p.nonneg _) ha _ < r :=
      by 
        rwa [mem_ball_zero] at hy

-- error in Analysis.Seminorm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Seminorm-balls at the origin are absorbent. -/
theorem absorbent_ball_zero {r : exprℝ()} (hr : «expr < »(0, r)) : absorbent 𝕜 (ball p (0 : E) r) :=
begin
  rw [expr absorbent_iff_nonneg_lt] [],
  rintro [ident x],
  have [ident hxr] [":", expr «expr ≤ »(0, «expr / »(p x, r))] [":=", expr div_nonneg (p.nonneg _) hr.le],
  refine [expr ⟨«expr / »(p x, r), hxr, λ a ha, _⟩],
  have [ident ha₀] [":", expr «expr < »(0, «expr∥ ∥»(a))] [":=", expr hxr.trans_lt ha],
  refine [expr ⟨«expr • »(«expr ⁻¹»(a), x), _, smul_inv_smul₀ (norm_pos_iff.1 ha₀) x⟩],
  rwa ["[", expr mem_ball_zero, ",", expr p.smul, ",", expr norm_inv, ",", expr inv_mul_lt_iff ha₀, ",", "<-", expr div_lt_iff hr, "]"] []
end

/-- Seminorm-balls containing the origin are absorbent. -/
theorem absorbent_ball (hpr : p x < r) : Absorbent 𝕜 (ball p x r) :=
  by 
    refine' (p.absorbent_ball_zero$ sub_pos.2 hpr).Subset fun y hy => _ 
    rw [p.mem_ball_zero] at hy 
    exact (p.mem_ball _ _ _).2 ((p.sub_le _ _).trans_lt$ add_lt_of_lt_sub_right hy)

theorem symmetric_ball_zero {x : E} (hx : x ∈ ball p 0 r) : -x ∈ ball p 0 r :=
  balanced_ball_zero p r (-1)
    (by 
      rw [norm_neg, norm_one])
    ⟨x, hx,
      by 
        rw [neg_smul, one_smul]⟩

end NormedField

section NormedLinearOrderedField

variable[NormedLinearOrderedField 𝕜][AddCommGroupₓ E][SemiNormedSpace ℝ 𝕜][Module 𝕜 E]

section HasScalar

variable[HasScalar ℝ E][IsScalarTower ℝ 𝕜 E](p : Seminorm 𝕜 E)

/-- A seminorm is convex. Also see `convex_on_norm`. -/
protected theorem ConvexOn : ConvexOn ℝ univ p :=
  by 
    refine' ⟨convex_univ, fun x y _ _ a b ha hb hab => _⟩
    calc p ((a • x)+b • y) ≤ p (a • x)+p (b • y) := p.triangle _ _ _ = (∥a • (1 : 𝕜)∥*p x)+∥b • (1 : 𝕜)∥*p y :=
      by 
        rw [←p.smul, ←p.smul, smul_one_smul, smul_one_smul]_ = (a*p x)+b*p y :=
      by 
        rw [norm_smul, norm_smul, norm_one, mul_oneₓ, mul_oneₓ, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]

end HasScalar

section Module

variable[Module ℝ E][IsScalarTower ℝ 𝕜 E](p : Seminorm 𝕜 E)(x : E)(r : ℝ)

/-- Seminorm-balls are convex. -/
theorem convex_ball : Convex ℝ (ball p x r) :=
  by 
    convert (p.convex_on.translate_left (-x)).convex_lt r 
    ext y 
    rw [preimage_univ, sep_univ, p.mem_ball x y r, sub_eq_add_neg]
    rfl

end Module

end NormedLinearOrderedField

end Seminorm

section gauge

noncomputable theory

variable[AddCommGroupₓ E][Module ℝ E]

/--The Minkowski functional. Given a set `s` in a real vector space, `gauge s` is the functional
which sends `x : E` to the smallest `r : ℝ` such that `x` is in `s` scaled by `r`. -/
def gauge (s : Set E) (x : E) : ℝ :=
  Inf { r:ℝ | 0 < r ∧ x ∈ r • s }

variable{s : Set E}{x : E}

theorem gauge_def : gauge s x = Inf { r∈Set.Ioi 0 | x ∈ r • s } :=
  rfl

/-- An alternative definition of the gauge using scalar multiplication on the element rather than on
the set. -/
theorem gauge_def' : gauge s x = Inf { r∈Set.Ioi 0 | r⁻¹ • x ∈ s } :=
  by 
    unfold gauge 
    congr 1 
    ext r 
    exact and_congr_right fun hr => mem_smul_set_iff_inv_smul_mem₀ hr.ne' _ _

private theorem gauge_set_bdd_below : BddBelow { r:ℝ | 0 < r ∧ x ∈ r • s } :=
  ⟨0, fun r hr => hr.1.le⟩

/-- If the given subset is `absorbent` then the set we take an infimum over in `gauge` is nonempty,
which is useful for proving many properties about the gauge.  -/
theorem Absorbent.gauge_set_nonempty (absorbs : Absorbent ℝ s) : { r:ℝ | 0 < r ∧ x ∈ r • s }.Nonempty :=
  let ⟨r, hr₁, hr₂⟩ := Absorbs x
  ⟨r, hr₁, hr₂ r (Real.norm_of_nonneg hr₁.le).Ge⟩

theorem exists_lt_of_gauge_lt (absorbs : Absorbent ℝ s) {x : E} {a : ℝ} (h : gauge s x < a) :
  ∃ b, 0 < b ∧ b < a ∧ x ∈ b • s :=
  by 
    obtain ⟨b, ⟨hb, hx⟩, hba⟩ := exists_lt_of_cInf_lt absorbs.gauge_set_nonempty h 
    exact ⟨b, hb, hba, hx⟩

/-- The gauge evaluated at `0` is always zero (mathematically this requires `0` to be in the set `s`
but, the real infimum of the empty set in Lean being defined as `0`, it holds unconditionally). -/
@[simp]
theorem gauge_zero : gauge s 0 = 0 :=
  by 
    rw [gauge_def']
    byCases' (0 : E) ∈ s
    ·
      simp only [smul_zero, sep_true, h, cInf_Ioi]
    ·
      simp only [smul_zero, sep_false, h, Real.Inf_empty]

/-- The gauge is always nonnegative. -/
theorem gauge_nonneg (x : E) : 0 ≤ gauge s x :=
  Real.Inf_nonneg _$ fun x hx => hx.1.le

-- error in Analysis.Seminorm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem gauge_neg
(symmetric : ∀ x «expr ∈ » s, «expr ∈ »(«expr- »(x), s))
(x : E) : «expr = »(gauge s «expr- »(x), gauge s x) :=
begin
  have [] [":", expr ∀
   x, «expr ↔ »(«expr ∈ »(«expr- »(x), s), «expr ∈ »(x, s))] [":=", expr λ
   x, ⟨λ h, by simpa [] [] [] [] [] ["using", expr symmetric _ h], symmetric x⟩],
  rw ["[", expr gauge_def', ",", expr gauge_def', "]"] [],
  simp_rw ["[", expr smul_neg, ",", expr this, "]"] []
end

theorem gauge_le_of_mem {r : ℝ} (hr : 0 ≤ r) {x : E} (hx : x ∈ r • s) : gauge s x ≤ r :=
  by 
    obtain rfl | hr' := hr.eq_or_lt
    ·
      rw [mem_singleton_iff.1 (zero_smul_subset _ hx), gauge_zero]
    ·
      exact cInf_le gauge_set_bdd_below ⟨hr', hx⟩

-- error in Analysis.Seminorm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem gauge_le_one_eq'
(hs : convex exprℝ() s)
(zero_mem : «expr ∈ »((0 : E), s))
(absorbs : absorbent exprℝ() s) : «expr = »({x | «expr ≤ »(gauge s x, 1)}, «expr⋂ , »((r : exprℝ())
  (H : «expr < »(1, r)), «expr • »(r, s))) :=
begin
  ext [] [] [],
  simp_rw ["[", expr set.mem_Inter, ",", expr set.mem_set_of_eq, "]"] [],
  split,
  { intros [ident h, ident r, ident hr],
    have [ident hr'] [] [":=", expr zero_lt_one.trans hr],
    rw [expr mem_smul_set_iff_inv_smul_mem₀ hr'.ne'] [],
    obtain ["⟨", ident δ, ",", ident δ_pos, ",", ident hδr, ",", ident hδ, "⟩", ":=", expr exists_lt_of_gauge_lt absorbs (h.trans_lt hr)],
    suffices [] [":", expr «expr ∈ »(«expr • »(«expr * »(«expr ⁻¹»(r), δ), «expr • »(«expr ⁻¹»(δ), x)), s)],
    { rwa ["[", expr smul_smul, ",", expr mul_inv_cancel_right₀ δ_pos.ne', "]"] ["at", ident this] },
    rw [expr mem_smul_set_iff_inv_smul_mem₀ δ_pos.ne'] ["at", ident hδ],
    refine [expr hs.smul_mem_of_zero_mem zero_mem hδ ⟨mul_nonneg (inv_nonneg.2 hr'.le) δ_pos.le, _⟩],
    rw ["[", expr inv_mul_le_iff hr', ",", expr mul_one, "]"] [],
    exact [expr hδr.le] },
  { refine [expr λ h, le_of_forall_pos_lt_add (λ ε hε, _)],
    have [ident hε'] [] [":=", expr (lt_add_iff_pos_right 1).2 (half_pos hε)],
    exact [expr «expr $ »(gauge_le_of_mem (zero_le_one.trans hε'.le), h _ hε').trans_lt (add_lt_add_left (half_lt_self hε) _)] }
end

theorem gauge_le_one_eq (hs : Convex ℝ s) (zero_mem : (0 : E) ∈ s) (absorbs : Absorbent ℝ s) :
  { x | gauge s x ≤ 1 } = ⋂(r : _)(_ : r ∈ Set.Ioi (1 : ℝ)), r • s :=
  gauge_le_one_eq' hs zero_mem Absorbs

theorem gauge_lt_one_eq' (absorbs : Absorbent ℝ s) : { x | gauge s x < 1 } = ⋃(r : ℝ)(H : 0 < r)(H : r < 1), r • s :=
  by 
    ext 
    simpRw [Set.mem_set_of_eq, Set.mem_Union]
    split 
    ·
      intro h 
      obtain ⟨r, hr₀, hr₁, hx⟩ := exists_lt_of_gauge_lt Absorbs h 
      exact ⟨r, hr₀, hr₁, hx⟩
    ·
      exact fun ⟨r, hr₀, hr₁, hx⟩ => (gauge_le_of_mem hr₀.le hx).trans_lt hr₁

theorem gauge_lt_one_eq (absorbs : Absorbent ℝ s) :
  { x | gauge s x < 1 } = ⋃(r : _)(_ : r ∈ Set.Ioo 0 (1 : ℝ)), r • s :=
  by 
    ext 
    simpRw [Set.mem_set_of_eq, Set.mem_Union]
    split 
    ·
      intro h 
      obtain ⟨r, hr₀, hr₁, hx⟩ := exists_lt_of_gauge_lt Absorbs h 
      exact ⟨r, ⟨hr₀, hr₁⟩, hx⟩
    ·
      exact fun ⟨r, ⟨hr₀, hr₁⟩, hx⟩ => (gauge_le_of_mem hr₀.le hx).trans_lt hr₁

theorem gauge_lt_one_subset_self (hs : Convex ℝ s) (h₀ : (0 : E) ∈ s) (absorbs : Absorbent ℝ s) :
  { x | gauge s x < 1 } ⊆ s :=
  by 
    rw [gauge_lt_one_eq Absorbs]
    apply Set.bUnion_subset 
    rintro r hr _ ⟨y, hy, rfl⟩
    exact hs.smul_mem_of_zero_mem h₀ hy (Ioo_subset_Icc_self hr)

theorem gauge_le_one_of_mem {x : E} (hx : x ∈ s) : gauge s x ≤ 1 :=
  gauge_le_of_mem zero_le_one$
    by 
      rwa [one_smul]

theorem self_subset_gauge_le_one : s ⊆ { x | gauge s x ≤ 1 } :=
  fun x => gauge_le_one_of_mem

theorem Convex.gauge_le_one (hs : Convex ℝ s) (h₀ : (0 : E) ∈ s) (absorbs : Absorbent ℝ s) :
  Convex ℝ { x | gauge s x ≤ 1 } :=
  by 
    rw [gauge_le_one_eq hs h₀ Absorbs]
    exact convex_Inter fun i => convex_Inter fun hi : _ < _ => hs.smul _

section TopologicalSpace

variable[TopologicalSpace E][HasContinuousSmul ℝ E]

-- error in Analysis.Seminorm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem interior_subset_gauge_lt_one (s : set E) : «expr ⊆ »(interior s, {x | «expr < »(gauge s x, 1)}) :=
begin
  intros [ident x, ident hx],
  let [ident f] [":", expr exprℝ() → E] [":=", expr λ t, «expr • »(t, x)],
  have [ident hf] [":", expr continuous f] [],
  { continuity [] [] },
  let [ident s'] [] [":=", expr «expr ⁻¹' »(f, interior s)],
  have [ident hs'] [":", expr is_open s'] [":=", expr hf.is_open_preimage _ is_open_interior],
  have [ident one_mem] [":", expr «expr ∈ »((1 : exprℝ()), s')] [],
  { simpa [] [] ["only"] ["[", expr s', ",", expr f, ",", expr set.mem_preimage, ",", expr one_smul, "]"] [] [] },
  obtain ["⟨", ident ε, ",", ident hε₀, ",", ident hε, "⟩", ":=", expr (metric.nhds_basis_closed_ball.1 _).1 (is_open_iff_mem_nhds.1 hs' 1 one_mem)],
  rw [expr real.closed_ball_eq] ["at", ident hε],
  have [ident hε₁] [":", expr «expr < »(0, «expr + »(1, ε))] [":=", expr hε₀.trans (lt_one_add ε)],
  have [] [":", expr «expr < »(«expr ⁻¹»(«expr + »(1, ε)), 1)] [],
  { rw [expr inv_lt_one_iff] [],
    right,
    linarith [] [] [] },
  refine [expr (gauge_le_of_mem (inv_nonneg.2 hε₁.le) _).trans_lt this],
  rw [expr mem_inv_smul_set_iff₀ hε₁.ne'] [],
  exact [expr interior_subset (hε ⟨(sub_le_self _ hε₀.le).trans ((le_add_iff_nonneg_right _).2 hε₀.le), le_rfl⟩)]
end

theorem gauge_lt_one_eq_self_of_open {s : Set E} (hs : Convex ℝ s) (zero_mem : (0 : E) ∈ s) (hs₂ : IsOpen s) :
  { x | gauge s x < 1 } = s :=
  by 
    apply (gauge_lt_one_subset_self hs ‹_›$ absorbent_nhds_zero$ hs₂.mem_nhds zero_mem).antisymm 
    convert interior_subset_gauge_lt_one s 
    exact hs₂.interior_eq.symm

theorem gauge_lt_one_of_mem_of_open {s : Set E} (hs : Convex ℝ s) (zero_mem : (0 : E) ∈ s) (hs₂ : IsOpen s) (x : E)
  (hx : x ∈ s) : gauge s x < 1 :=
  by 
    rwa [←gauge_lt_one_eq_self_of_open hs zero_mem hs₂] at hx

theorem one_le_gauge_of_not_mem {s : Set E} (hs : Convex ℝ s) (zero_mem : (0 : E) ∈ s) (hs₂ : IsOpen s) {x : E}
  (hx : x ∉ s) : 1 ≤ gauge s x :=
  by 
    rw [←gauge_lt_one_eq_self_of_open hs zero_mem hs₂] at hx 
    exact le_of_not_ltₓ hx

end TopologicalSpace

variable{α : Type _}[LinearOrderedField α][MulActionWithZero α ℝ][OrderedSmul α ℝ]

-- error in Analysis.Seminorm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem gauge_smul_of_nonneg
[mul_action_with_zero α E]
[is_scalar_tower α exprℝ() (set E)]
{s : set E}
{r : α}
(hr : «expr ≤ »(0, r))
(x : E) : «expr = »(gauge s «expr • »(r, x), «expr • »(r, gauge s x)) :=
begin
  obtain [ident rfl, "|", ident hr', ":=", expr hr.eq_or_lt],
  { rw ["[", expr zero_smul, ",", expr gauge_zero, ",", expr zero_smul, "]"] [] },
  rw ["[", expr gauge_def', ",", expr gauge_def', ",", "<-", expr real.Inf_smul_of_nonneg hr, "]"] [],
  congr' [1] [],
  ext [] [ident β] [],
  simp_rw ["[", expr set.mem_smul_set, ",", expr set.mem_sep_eq, "]"] [],
  split,
  { rintro ["⟨", ident hβ, ",", ident hx, "⟩"],
    simp_rw ["[", expr mem_Ioi, "]"] ["at", "⊢", ident hβ],
    have [] [] [":=", expr smul_pos (inv_pos.2 hr') hβ],
    refine [expr ⟨«expr • »(«expr ⁻¹»(r), β), ⟨this, _⟩, smul_inv_smul₀ hr'.ne' _⟩],
    rw ["<-", expr mem_smul_set_iff_inv_smul_mem₀] ["at", "⊢", ident hx],
    rwa ["[", expr smul_assoc, ",", expr mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hr'.ne'), ",", expr inv_inv₀, "]"] [],
    { exact [expr this.ne'] },
    { exact [expr hβ.ne'] } },
  { rintro ["⟨", ident β, ",", "⟨", ident hβ, ",", ident hx, "⟩", ",", ident rfl, "⟩"],
    rw [expr mem_Ioi] ["at", "⊢", ident hβ],
    have [] [] [":=", expr smul_pos hr' hβ],
    refine [expr ⟨this, _⟩],
    rw ["<-", expr mem_smul_set_iff_inv_smul_mem₀] ["at", "⊢", ident hx],
    rw [expr smul_assoc] [],
    exact [expr smul_mem_smul_set hx],
    { exact [expr this.ne'] },
    { exact [expr hβ.ne'] } }
end

/-- In textbooks, this is the homogeneity of the Minkowksi functional. -/
theorem gauge_smul [Module α E] [IsScalarTower α ℝ (Set E)] {s : Set E} (symmetric : ∀ x _ : x ∈ s, -x ∈ s) (r : α)
  (x : E) : gauge s (r • x) = abs r • gauge s x :=
  by 
    rw [←gauge_smul_of_nonneg (abs_nonneg r)]
    obtain h | h := abs_choice r
    ·
      rw [h]
    ·
      rw [h, neg_smul, gauge_neg Symmetric]
    ·
      infer_instance

-- error in Analysis.Seminorm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem gauge_add_le
(hs : convex exprℝ() s)
(absorbs : absorbent exprℝ() s)
(x y : E) : «expr ≤ »(gauge s «expr + »(x, y), «expr + »(gauge s x, gauge s y)) :=
begin
  refine [expr le_of_forall_pos_lt_add (λ ε hε, _)],
  obtain ["⟨", ident a, ",", ident ha, ",", ident ha', ",", ident hx, "⟩", ":=", expr exists_lt_of_gauge_lt absorbs (lt_add_of_pos_right (gauge s x) (half_pos hε))],
  obtain ["⟨", ident b, ",", ident hb, ",", ident hb', ",", ident hy, "⟩", ":=", expr exists_lt_of_gauge_lt absorbs (lt_add_of_pos_right (gauge s y) (half_pos hε))],
  rw [expr mem_smul_set_iff_inv_smul_mem₀ ha.ne'] ["at", ident hx],
  rw [expr mem_smul_set_iff_inv_smul_mem₀ hb.ne'] ["at", ident hy],
  suffices [] [":", expr «expr ≤ »(gauge s «expr + »(x, y), «expr + »(a, b))],
  { linarith [] [] [] },
  have [ident hab] [":", expr «expr < »(0, «expr + »(a, b))] [":=", expr add_pos ha hb],
  apply [expr gauge_le_of_mem hab.le],
  have [] [] [":=", expr convex_iff_div.1 hs hx hy ha.le hb.le hab],
  rwa ["[", expr smul_smul, ",", expr smul_smul, ",", expr mul_comm_div', ",", expr mul_comm_div', ",", "<-", expr mul_div_assoc, ",", "<-", expr mul_div_assoc, ",", expr mul_inv_cancel ha.ne', ",", expr mul_inv_cancel hb.ne', ",", "<-", expr smul_add, ",", expr one_div, ",", "<-", expr mem_smul_set_iff_inv_smul_mem₀ hab.ne', "]"] ["at", ident this]
end

/-- `gauge s` as a seminorm when `s` is symmetric, convex and absorbent. -/
@[simps]
def gaugeSeminorm (symmetric : ∀ x _ : x ∈ s, -x ∈ s) (hs : Convex ℝ s) (hs' : Absorbent ℝ s) : Seminorm ℝ E :=
  { toFun := gauge s,
    smul' :=
      fun r x =>
        by 
          rw [gauge_smul Symmetric, Real.norm_eq_abs, smul_eq_mul] <;> infer_instance,
    triangle' := gauge_add_le hs hs' }

-- error in Analysis.Seminorm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any seminorm arises a the gauge of its unit ball. -/
theorem seminorm.gauge_ball (p : seminorm exprℝ() E) : «expr = »(gauge (p.ball 0 1), p) :=
begin
  ext [] [] [],
  obtain [ident hp, "|", ident hp, ":=", expr {r : exprℝ() | «expr ∧ »(«expr < »(0, r), «expr ∈ »(x, «expr • »(r, p.ball 0 1)))}.eq_empty_or_nonempty],
  { rw ["[", expr gauge, ",", expr hp, ",", expr real.Inf_empty, "]"] [],
    by_contra [],
    have [ident hpx] [":", expr «expr < »(0, p x)] [":=", expr (p.nonneg x).lt_of_ne h],
    have [ident hpx₂] [":", expr «expr < »(0, «expr * »(2, p x))] [":=", expr mul_pos zero_lt_two hpx],
    refine [expr hp.subset ⟨hpx₂, «expr • »(«expr ⁻¹»(«expr * »(2, p x)), x), _, smul_inv_smul₀ hpx₂.ne' _⟩],
    rw ["[", expr p.mem_ball_zero, ",", expr p.smul, ",", expr real.norm_eq_abs, ",", expr abs_of_pos (inv_pos.2 hpx₂), ",", expr inv_mul_lt_iff hpx₂, ",", expr mul_one, "]"] [],
    exact [expr lt_mul_of_one_lt_left hpx one_lt_two] },
  refine [expr is_glb.cInf_eq ⟨λ r, _, λ r hr, «expr $ »(le_of_forall_pos_le_add, λ ε hε, _)⟩ hp],
  { rintro ["⟨", ident hr, ",", ident y, ",", ident hy, ",", ident rfl, "⟩"],
    rw [expr p.mem_ball_zero] ["at", ident hy],
    rw ["[", expr p.smul, ",", expr real.norm_eq_abs, ",", expr abs_of_pos hr, "]"] [],
    exact [expr mul_le_of_le_one_right hr.le hy.le] },
  { have [ident hpε] [":", expr «expr < »(0, «expr + »(p x, ε))] [":=", expr add_pos_of_nonneg_of_pos (p.nonneg _) hε],
    refine [expr hr ⟨hpε, «expr • »(«expr ⁻¹»(«expr + »(p x, ε)), x), _, smul_inv_smul₀ hpε.ne' _⟩],
    rw ["[", expr p.mem_ball_zero, ",", expr p.smul, ",", expr real.norm_eq_abs, ",", expr abs_of_pos (inv_pos.2 hpε), ",", expr inv_mul_lt_iff hpε, ",", expr mul_one, "]"] [],
    exact [expr lt_add_of_pos_right _ hε] }
end

theorem Seminorm.gauge_seminorm_ball (p : Seminorm ℝ E) :
  gaugeSeminorm (fun x => p.symmetric_ball_zero 1) (p.convex_ball 0 1) (p.absorbent_ball_zero zero_lt_one) = p :=
  Seminorm.ext p.gauge_ball

end gauge

