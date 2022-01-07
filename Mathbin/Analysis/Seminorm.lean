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

variable {𝕜 E : Type _}

section SemiNormedRing

variable [SemiNormedRing 𝕜]

section HasScalar

variable (𝕜) [HasScalar 𝕜 E]

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

variable {𝕜} {A B : Set E}

theorem Balanced.univ : Balanced 𝕜 (univ : Set E) := fun a ha => subset_univ _

theorem Balanced.union (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B) : Balanced 𝕜 (A ∪ B) := by
  intro a ha t ht
  rw [smul_set_union] at ht
  exact ht.imp (fun x => hA _ ha x) fun x => hB _ ha x

end HasScalar

section AddCommGroupₓ

variable [AddCommGroupₓ E] [Module 𝕜 E] {A B : Set E}

theorem Balanced.inter (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B) : Balanced 𝕜 (A ∩ B) := by
  rintro a ha _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
  exact ⟨hA _ ha ⟨_, hx₁, rfl⟩, hB _ ha ⟨_, hx₂, rfl⟩⟩

theorem Balanced.add (hA₁ : Balanced 𝕜 A) (hA₂ : Balanced 𝕜 B) : Balanced 𝕜 (A + B) := by
  rintro a ha _ ⟨_, ⟨x, y, hx, hy, rfl⟩, rfl⟩
  rw [smul_add]
  exact ⟨_, _, hA₁ _ ha ⟨_, hx, rfl⟩, hA₂ _ ha ⟨_, hy, rfl⟩, rfl⟩

theorem Absorbent.subset (hA : Absorbent 𝕜 A) (hAB : A ⊆ B) : Absorbent 𝕜 B := by
  rintro x
  obtain ⟨r, hr, hx⟩ := hA x
  exact ⟨r, hr, fun a ha => Set.smul_set_mono hAB $ hx a ha⟩

theorem absorbent_iff_forall_absorbs_singleton : Absorbent 𝕜 A ↔ ∀ x, Absorbs 𝕜 A {x} := by
  simp_rw [Absorbs, Absorbent, singleton_subset_iff]

theorem absorbent_iff_nonneg_lt : Absorbent 𝕜 A ↔ ∀ x, ∃ r, 0 ≤ r ∧ ∀ a : 𝕜, r < ∥a∥ → x ∈ a • A := by
  constructor
  · rintro hA x
    obtain ⟨r, hr, hx⟩ := hA x
    exact ⟨r, hr.le, fun a ha => hx a ha.le⟩
    
  · rintro hA x
    obtain ⟨r, hr, hx⟩ := hA x
    exact
      ⟨r + 1, add_pos_of_nonneg_of_pos hr zero_lt_one, fun a ha =>
        hx a ((lt_add_of_pos_right r zero_lt_one).trans_le ha)⟩
    

end AddCommGroupₓ

end SemiNormedRing

section NormedCommRing

variable [NormedCommRing 𝕜] [AddCommMonoidₓ E] [Module 𝕜 E] {A B : Set E} (a : 𝕜)

theorem Balanced.smul (hA : Balanced 𝕜 A) : Balanced 𝕜 (a • A) := by
  rintro b hb _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact ⟨b • x, hA _ hb ⟨_, hx, rfl⟩, smul_comm _ _ _⟩

end NormedCommRing

section NormedField

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] {A B : Set E} {a : 𝕜}

/-- A balanced set absorbs itself. -/
theorem Balanced.absorbs_self (hA : Balanced 𝕜 A) : Absorbs 𝕜 A A := by
  use 1, zero_lt_one
  intro a ha x hx
  rw [mem_smul_set_iff_inv_smul_mem₀]
  · apply hA (a⁻¹)
    · rw [norm_inv]
      exact inv_le_one ha
      
    · rw [mem_smul_set]
      use x, hx
      
    
  · rw [← norm_pos_iff]
    calc 0 < 1 := zero_lt_one _ ≤ ∥a∥ := ha
    

theorem Balanced.subset_smul (hA : Balanced 𝕜 A) (ha : 1 ≤ ∥a∥) : A ⊆ a • A := by
  refine' (subset_set_smul_iff₀ _).2 (hA (a⁻¹) _)
  · rintro rfl
    rw [norm_zero] at ha
    exact zero_lt_one.not_le ha
    
  · rw [norm_inv]
    exact inv_le_one ha
    

theorem Balanced.smul_eq (hA : Balanced 𝕜 A) (ha : ∥a∥ = 1) : a • A = A :=
  (hA _ ha.le).antisymm $ hA.subset_smul ha.ge

/-! #### Topological vector space -/


variable [TopologicalSpace E] [HasContinuousSmul 𝕜 E]

/-- Every neighbourhood of the origin is absorbent. -/
theorem absorbent_nhds_zero (hA : A ∈ 𝓝 (0 : E)) : Absorbent 𝕜 A := by
  intro x
  rcases mem_nhds_iff.mp hA with ⟨w, hw₁, hw₂, hw₃⟩
  have hc : Continuous fun t : 𝕜 => t • x := continuous_id.smul continuous_const
  rcases metric.is_open_iff.mp (hw₂.preimage hc) 0
      (by
        rwa [mem_preimage, zero_smul]) with
    ⟨r, hr₁, hr₂⟩
  have hr₃ := inv_pos.mpr (half_pos hr₁)
  use (r / 2)⁻¹, hr₃
  intro a ha₁
  have ha₂ : 0 < ∥a∥ := hr₃.trans_le ha₁
  rw [mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.mp ha₂)]
  refine' hw₁ (hr₂ _)
  rw [Metric.mem_ball, dist_zero_right, norm_inv]
  calc ∥a∥⁻¹ ≤ r / 2 := (inv_le (half_pos hr₁) ha₂).mp ha₁ _ < r := half_lt_self hr₁

/-- The union of `{0}` with the interior of a balanced set is balanced. -/
theorem balanced_zero_union_interior (hA : Balanced 𝕜 A) : Balanced 𝕜 ({(0 : E)} ∪ Interior A) := by
  intro a ha
  by_cases' a = 0
  · rw [h, zero_smul_set]
    exacts[subset_union_left _ _, ⟨0, Or.inl rfl⟩]
    
  · rw [← image_smul, image_union]
    apply union_subset_union
    · rw [image_singleton, smul_zero]
      
    · calc a • Interior A ⊆ Interior (a • A) := (is_open_map_smul₀ h).image_interior_subset A _ ⊆ Interior A :=
          interior_mono (hA _ ha)
      
    

/-- The interior of a balanced set is balanced if it contains the origin. -/
theorem Balanced.interior (hA : Balanced 𝕜 A) (h : (0 : E) ∈ Interior A) : Balanced 𝕜 (Interior A) := by
  rw [← singleton_subset_iff] at h
  rw [← union_eq_self_of_subset_left h]
  exact balanced_zero_union_interior hA

/-- The closure of a balanced set is balanced. -/
theorem Balanced.closure (hA : Balanced 𝕜 A) : Balanced 𝕜 (Closure A) := fun a ha =>
  calc
    _ ⊆ Closure (a • A) := image_closure_subset_closure_image (continuous_id.const_smul _)
    _ ⊆ _ := closure_mono (hA _ ha)
    

end NormedField

/-!
### Seminorms
-/


/-- A seminorm on a vector space over a normed field is a function to
the reals that is positive semidefinite, positive homogeneous, and
subadditive. -/
structure Seminorm (𝕜 : Type _) (E : Type _) [SemiNormedRing 𝕜] [AddMonoidₓ E] [HasScalar 𝕜 E] where
  toFun : E → ℝ
  smul' : ∀ a : 𝕜 x : E, to_fun (a • x) = ∥a∥ * to_fun x
  triangle' : ∀ x y : E, to_fun (x + y) ≤ to_fun x + to_fun y

namespace Seminorm

section SemiNormedRing

variable [SemiNormedRing 𝕜]

section AddMonoidₓ

variable [AddMonoidₓ E]

section HasScalar

variable [HasScalar 𝕜 E]

instance : Inhabited (Seminorm 𝕜 E) :=
  ⟨{ toFun := fun _ => 0, smul' := fun _ _ => (mul_zero _).symm,
      triangle' := fun x y => by
        rw [add_zeroₓ] }⟩

instance : CoeFun (Seminorm 𝕜 E) fun _ => E → ℝ :=
  ⟨fun p => p.to_fun⟩

@[ext]
theorem ext {p q : Seminorm 𝕜 E} (h : (p : E → ℝ) = q) : p = q := by
  cases p
  cases q
  have : p_to_fun = q_to_fun := h
  simp_rw [this]

variable (p : Seminorm 𝕜 E) (c : 𝕜) (x y : E) (r : ℝ)

protected theorem smul : p (c • x) = ∥c∥ * p x :=
  p.smul' _ _

protected theorem triangle : p (x + y) ≤ p x + p y :=
  p.triangle' _ _

end HasScalar

section SmulWithZero

variable [SmulWithZero 𝕜 E] (p : Seminorm 𝕜 E)

@[simp]
protected theorem zero : p 0 = 0 :=
  calc
    p 0 = p ((0 : 𝕜) • 0) := by
      rw [zero_smul]
    _ = 0 := by
      rw [p.smul, norm_zero, zero_mul]
    

end SmulWithZero

end AddMonoidₓ

section NormOneClass

variable [NormOneClass 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] (p : Seminorm 𝕜 E) (x y : E) (r : ℝ)

@[simp]
protected theorem neg : p (-x) = p x :=
  calc
    p (-x) = p ((-1 : 𝕜) • x) := by
      rw [neg_one_smul]
    _ = p x := by
      rw [p.smul, norm_neg, norm_one, one_mulₓ]
    

protected theorem sub_le : p (x - y) ≤ p x + p y :=
  calc
    p (x - y) = p (x + -y) := by
      rw [sub_eq_add_neg]
    _ ≤ p x + p (-y) := p.triangle x (-y)
    _ = p x + p y := by
      rw [p.neg]
    

theorem nonneg : 0 ≤ p x :=
  have h : 0 ≤ 2 * p x :=
    calc
      0 = p (x + -x) := by
        rw [add_neg_selfₓ, p.zero]
      _ ≤ p x + p (-x) := p.triangle _ _
      _ = 2 * p x := by
        rw [p.neg, two_mul]
      
  nonneg_of_mul_nonneg_left h zero_lt_two

theorem sub_rev : p (x - y) = p (y - x) := by
  rw [← neg_sub, p.neg]

end NormOneClass

/-! ### Seminorm ball -/


section AddCommGroupₓ

variable [AddCommGroupₓ E]

section HasScalar

variable [HasScalar 𝕜 E] (p : Seminorm 𝕜 E)

/-- The ball of radius `r` at `x` with respect to seminorm `p` is the set of elements `y` with
`p (y - x) < `r`. -/
def ball (x : E) (r : ℝ) :=
  { y : E | p (y - x) < r }

variable {x y : E} {r : ℝ}

theorem mem_ball : y ∈ ball p x r ↔ p (y - x) < r :=
  Iff.rfl

theorem mem_ball_zero : y ∈ ball p 0 r ↔ p y < r := by
  rw [mem_ball, sub_zero]

theorem ball_zero_eq : ball p 0 r = { y : E | p y < r } :=
  Set.ext $ fun x => p.mem_ball_zero

end HasScalar

section Module

variable [NormOneClass 𝕜] [Module 𝕜 E] (p : Seminorm 𝕜 E)

/-- Seminorm-balls at the origin are balanced. -/
theorem balanced_ball_zero (r : ℝ) : Balanced 𝕜 (ball p 0 r) := by
  rintro a ha x ⟨y, hy, hx⟩
  rw [mem_ball_zero, ← hx, p.smul]
  calc _ ≤ p y := mul_le_of_le_one_left (p.nonneg _) ha _ < r := by
      rwa [mem_ball_zero] at hy

end Module

end AddCommGroupₓ

end SemiNormedRing

section NormedField

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] (p : Seminorm 𝕜 E) {A B : Set E} {a : 𝕜} {r : ℝ} {x : E}

/-- Seminorm-balls at the origin are absorbent. -/
theorem absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (ball p (0 : E) r) := by
  rw [absorbent_iff_nonneg_lt]
  rintro x
  have hxr : 0 ≤ p x / r := div_nonneg (p.nonneg _) hr.le
  refine' ⟨p x / r, hxr, fun a ha => _⟩
  have ha₀ : 0 < ∥a∥ := hxr.trans_lt ha
  refine' ⟨a⁻¹ • x, _, smul_inv_smul₀ (norm_pos_iff.1 ha₀) x⟩
  rwa [mem_ball_zero, p.smul, norm_inv, inv_mul_lt_iff ha₀, ← div_lt_iff hr]

/-- Seminorm-balls containing the origin are absorbent. -/
theorem absorbent_ball (hpr : p x < r) : Absorbent 𝕜 (ball p x r) := by
  refine' (p.absorbent_ball_zero $ sub_pos.2 hpr).Subset fun y hy => _
  rw [p.mem_ball_zero] at hy
  exact p.mem_ball.2 ((p.sub_le _ _).trans_lt $ add_lt_of_lt_sub_right hy)

theorem symmetric_ball_zero (r : ℝ) (hx : x ∈ ball p 0 r) : -x ∈ ball p 0 r :=
  balanced_ball_zero p r (-1)
    (by
      rw [norm_neg, norm_one])
    ⟨x, hx, by
      rw [neg_smul, one_smul]⟩

end NormedField

section NormedLinearOrderedField

variable [NormedLinearOrderedField 𝕜] [AddCommGroupₓ E] [SemiNormedSpace ℝ 𝕜] [Module 𝕜 E]

section HasScalar

variable [HasScalar ℝ E] [IsScalarTower ℝ 𝕜 E] (p : Seminorm 𝕜 E)

/-- A seminorm is convex. Also see `convex_on_norm`. -/
protected theorem ConvexOn : ConvexOn ℝ univ p := by
  refine' ⟨convex_univ, fun x y _ _ a b ha hb hab => _⟩
  calc p (a • x + b • y) ≤ p (a • x) + p (b • y) := p.triangle _ _ _ = ∥a • (1 : 𝕜)∥ * p x + ∥b • (1 : 𝕜)∥ * p y := by
      rw [← p.smul, ← p.smul, smul_one_smul, smul_one_smul]_ = a * p x + b * p y := by
      rw [norm_smul, norm_smul, norm_one, mul_oneₓ, mul_oneₓ, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]

end HasScalar

section Module

variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E] (p : Seminorm 𝕜 E) (x : E) (r : ℝ)

/-- Seminorm-balls are convex. -/
theorem convex_ball : Convex ℝ (ball p x r) := by
  convert (p.convex_on.translate_left (-x)).convex_lt r
  ext y
  rw [preimage_univ, sep_univ, p.mem_ball, sub_eq_add_neg]
  rfl

end Module

end NormedLinearOrderedField

end Seminorm

section gauge

noncomputable section

variable [AddCommGroupₓ E] [Module ℝ E]

/-- The Minkowski functional. Given a set `s` in a real vector space, `gauge s` is the functional
which sends `x : E` to the smallest `r : ℝ` such that `x` is in `s` scaled by `r`. -/
def gauge (s : Set E) (x : E) : ℝ :=
  Inf { r : ℝ | 0 < r ∧ x ∈ r • s }

variable {s : Set E} {x : E}

theorem gauge_def : gauge s x = Inf { r ∈ Set.Ioi 0 | x ∈ r • s } :=
  rfl

/-- An alternative definition of the gauge using scalar multiplication on the element rather than on
the set. -/
theorem gauge_def' : gauge s x = Inf { r ∈ Set.Ioi 0 | r⁻¹ • x ∈ s } := by
  unfold gauge
  congr 1
  ext r
  exact and_congr_right fun hr => mem_smul_set_iff_inv_smul_mem₀ hr.ne' _ _

private theorem gauge_set_bdd_below : BddBelow { r : ℝ | 0 < r ∧ x ∈ r • s } :=
  ⟨0, fun r hr => hr.1.le⟩

/-- If the given subset is `absorbent` then the set we take an infimum over in `gauge` is nonempty,
which is useful for proving many properties about the gauge.  -/
theorem Absorbent.gauge_set_nonempty (absorbs : Absorbent ℝ s) : { r : ℝ | 0 < r ∧ x ∈ r • s }.Nonempty :=
  let ⟨r, hr₁, hr₂⟩ := Absorbs x
  ⟨r, hr₁, hr₂ r (Real.norm_of_nonneg hr₁.le).Ge⟩

theorem exists_lt_of_gauge_lt (absorbs : Absorbent ℝ s) {x : E} {a : ℝ} (h : gauge s x < a) :
    ∃ b, 0 < b ∧ b < a ∧ x ∈ b • s := by
  obtain ⟨b, ⟨hb, hx⟩, hba⟩ := exists_lt_of_cInf_lt absorbs.gauge_set_nonempty h
  exact ⟨b, hb, hba, hx⟩

/-- The gauge evaluated at `0` is always zero (mathematically this requires `0` to be in the set `s`
but, the real infimum of the empty set in Lean being defined as `0`, it holds unconditionally). -/
@[simp]
theorem gauge_zero : gauge s 0 = 0 := by
  rw [gauge_def']
  by_cases' (0 : E) ∈ s
  · simp only [smul_zero, sep_true, h, cInf_Ioi]
    
  · simp only [smul_zero, sep_false, h, Real.Inf_empty]
    

/-- The gauge is always nonnegative. -/
theorem gauge_nonneg (x : E) : 0 ≤ gauge s x :=
  Real.Inf_nonneg _ $ fun x hx => hx.1.le

theorem gauge_neg (symmetric : ∀, ∀ x ∈ s, ∀, -x ∈ s) (x : E) : gauge s (-x) = gauge s x := by
  have : ∀ x, -x ∈ s ↔ x ∈ s := fun x =>
    ⟨fun h => by
      simpa using Symmetric _ h, Symmetric x⟩
  rw [gauge_def', gauge_def']
  simp_rw [smul_neg, this]

theorem gauge_le_of_mem {r : ℝ} (hr : 0 ≤ r) {x : E} (hx : x ∈ r • s) : gauge s x ≤ r := by
  obtain rfl | hr' := hr.eq_or_lt
  · rw [mem_singleton_iff.1 (zero_smul_subset _ hx), gauge_zero]
    
  · exact cInf_le gauge_set_bdd_below ⟨hr', hx⟩
    

theorem gauge_le_one_eq' (hs : Convex ℝ s) (zero_mem : (0 : E) ∈ s) (absorbs : Absorbent ℝ s) :
    { x | gauge s x ≤ 1 } = ⋂ (r : ℝ) (H : 1 < r), r • s := by
  ext
  simp_rw [Set.mem_Inter, Set.mem_set_of_eq]
  constructor
  · intro h r hr
    have hr' := zero_lt_one.trans hr
    rw [mem_smul_set_iff_inv_smul_mem₀ hr'.ne']
    obtain ⟨δ, δ_pos, hδr, hδ⟩ := exists_lt_of_gauge_lt Absorbs (h.trans_lt hr)
    suffices (r⁻¹ * δ) • δ⁻¹ • x ∈ s by
      rwa [smul_smul, mul_inv_cancel_right₀ δ_pos.ne'] at this
    rw [mem_smul_set_iff_inv_smul_mem₀ δ_pos.ne'] at hδ
    refine' hs.smul_mem_of_zero_mem zero_mem hδ ⟨mul_nonneg (inv_nonneg.2 hr'.le) δ_pos.le, _⟩
    rw [inv_mul_le_iff hr', mul_oneₓ]
    exact hδr.le
    
  · refine' fun h => le_of_forall_pos_lt_add fun ε hε => _
    have hε' := (lt_add_iff_pos_right 1).2 (half_pos hε)
    exact (gauge_le_of_mem (zero_le_one.trans hε'.le) $ h _ hε').trans_lt (add_lt_add_left (half_lt_self hε) _)
    

theorem gauge_le_one_eq (hs : Convex ℝ s) (zero_mem : (0 : E) ∈ s) (absorbs : Absorbent ℝ s) :
    { x | gauge s x ≤ 1 } = ⋂ r ∈ Set.Ioi (1 : ℝ), r • s :=
  gauge_le_one_eq' hs zero_mem Absorbs

theorem gauge_lt_one_eq' (absorbs : Absorbent ℝ s) : { x | gauge s x < 1 } = ⋃ (r : ℝ) (H : 0 < r) (H : r < 1), r • s :=
  by
  ext
  simp_rw [Set.mem_set_of_eq, Set.mem_Union]
  constructor
  · intro h
    obtain ⟨r, hr₀, hr₁, hx⟩ := exists_lt_of_gauge_lt Absorbs h
    exact ⟨r, hr₀, hr₁, hx⟩
    
  · exact fun ⟨r, hr₀, hr₁, hx⟩ => (gauge_le_of_mem hr₀.le hx).trans_lt hr₁
    

theorem gauge_lt_one_eq (absorbs : Absorbent ℝ s) : { x | gauge s x < 1 } = ⋃ r ∈ Set.Ioo 0 (1 : ℝ), r • s := by
  ext
  simp_rw [Set.mem_set_of_eq, Set.mem_Union]
  constructor
  · intro h
    obtain ⟨r, hr₀, hr₁, hx⟩ := exists_lt_of_gauge_lt Absorbs h
    exact ⟨r, ⟨hr₀, hr₁⟩, hx⟩
    
  · exact fun ⟨r, ⟨hr₀, hr₁⟩, hx⟩ => (gauge_le_of_mem hr₀.le hx).trans_lt hr₁
    

theorem gauge_lt_one_subset_self (hs : Convex ℝ s) (h₀ : (0 : E) ∈ s) (absorbs : Absorbent ℝ s) :
    { x | gauge s x < 1 } ⊆ s := by
  rw [gauge_lt_one_eq Absorbs]
  apply Set.bUnion_subset
  rintro r hr _ ⟨y, hy, rfl⟩
  exact hs.smul_mem_of_zero_mem h₀ hy (Ioo_subset_Icc_self hr)

theorem gauge_le_one_of_mem {x : E} (hx : x ∈ s) : gauge s x ≤ 1 :=
  gauge_le_of_mem zero_le_one $ by
    rwa [one_smul]

theorem self_subset_gauge_le_one : s ⊆ { x | gauge s x ≤ 1 } := fun x => gauge_le_one_of_mem

theorem Convex.gauge_le_one (hs : Convex ℝ s) (h₀ : (0 : E) ∈ s) (absorbs : Absorbent ℝ s) :
    Convex ℝ { x | gauge s x ≤ 1 } := by
  rw [gauge_le_one_eq hs h₀ Absorbs]
  exact convex_Inter fun i => convex_Inter fun hi : _ < _ => hs.smul _

section TopologicalSpace

variable [TopologicalSpace E] [HasContinuousSmul ℝ E]

theorem interior_subset_gauge_lt_one (s : Set E) : Interior s ⊆ { x | gauge s x < 1 } := by
  intro x hx
  let f : ℝ → E := fun t => t • x
  have hf : Continuous f := by
    continuity
  let s' := f ⁻¹' Interior s
  have hs' : IsOpen s' := hf.is_open_preimage _ is_open_interior
  have one_mem : (1 : ℝ) ∈ s' := by
    simpa only [s', f, Set.mem_preimage, one_smul]
  obtain ⟨ε, hε₀, hε⟩ := (Metric.nhds_basis_closed_ball.1 _).1 (is_open_iff_mem_nhds.1 hs' 1 one_mem)
  rw [Real.closed_ball_eq_Icc] at hε
  have hε₁ : 0 < 1 + ε := hε₀.trans (lt_one_add ε)
  have : (1 + ε)⁻¹ < 1 := by
    rw [inv_lt_one_iff]
    right
    linarith
  refine' (gauge_le_of_mem (inv_nonneg.2 hε₁.le) _).trans_lt this
  rw [mem_inv_smul_set_iff₀ hε₁.ne']
  exact interior_subset (hε ⟨(sub_le_self _ hε₀.le).trans ((le_add_iff_nonneg_right _).2 hε₀.le), le_rfl⟩)

theorem gauge_lt_one_eq_self_of_open {s : Set E} (hs : Convex ℝ s) (zero_mem : (0 : E) ∈ s) (hs₂ : IsOpen s) :
    { x | gauge s x < 1 } = s := by
  apply (gauge_lt_one_subset_self hs ‹_› $ absorbent_nhds_zero $ hs₂.mem_nhds zero_mem).antisymm
  convert interior_subset_gauge_lt_one s
  exact hs₂.interior_eq.symm

theorem gauge_lt_one_of_mem_of_open {s : Set E} (hs : Convex ℝ s) (zero_mem : (0 : E) ∈ s) (hs₂ : IsOpen s) (x : E)
    (hx : x ∈ s) : gauge s x < 1 := by
  rwa [← gauge_lt_one_eq_self_of_open hs zero_mem hs₂] at hx

theorem one_le_gauge_of_not_mem {s : Set E} (hs : Convex ℝ s) (zero_mem : (0 : E) ∈ s) (hs₂ : IsOpen s) {x : E}
    (hx : x ∉ s) : 1 ≤ gauge s x := by
  rw [← gauge_lt_one_eq_self_of_open hs zero_mem hs₂] at hx
  exact le_of_not_ltₓ hx

end TopologicalSpace

variable {α : Type _} [LinearOrderedField α] [MulActionWithZero α ℝ] [OrderedSmul α ℝ]

theorem gauge_smul_of_nonneg [MulActionWithZero α E] [IsScalarTower α ℝ (Set E)] {s : Set E} {r : α} (hr : 0 ≤ r)
    (x : E) : gauge s (r • x) = r • gauge s x := by
  obtain rfl | hr' := hr.eq_or_lt
  · rw [zero_smul, gauge_zero, zero_smul]
    
  rw [gauge_def', gauge_def', ← Real.Inf_smul_of_nonneg hr]
  congr 1
  ext β
  simp_rw [Set.mem_smul_set, Set.mem_sep_eq]
  constructor
  · rintro ⟨hβ, hx⟩
    simp_rw [mem_Ioi]  at hβ⊢
    have := smul_pos (inv_pos.2 hr') hβ
    refine' ⟨r⁻¹ • β, ⟨this, _⟩, smul_inv_smul₀ hr'.ne' _⟩
    rw [← mem_smul_set_iff_inv_smul_mem₀] at hx⊢
    rwa [smul_assoc, mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hr'.ne'), inv_inv₀]
    · exact this.ne'
      
    · exact hβ.ne'
      
    
  · rintro ⟨β, ⟨hβ, hx⟩, rfl⟩
    rw [mem_Ioi] at hβ⊢
    have := smul_pos hr' hβ
    refine' ⟨this, _⟩
    rw [← mem_smul_set_iff_inv_smul_mem₀] at hx⊢
    rw [smul_assoc]
    exact smul_mem_smul_set hx
    · exact this.ne'
      
    · exact hβ.ne'
      
    

/-- In textbooks, this is the homogeneity of the Minkowksi functional. -/
theorem gauge_smul [Module α E] [IsScalarTower α ℝ (Set E)] {s : Set E} (symmetric : ∀, ∀ x ∈ s, ∀, -x ∈ s) (r : α)
    (x : E) : gauge s (r • x) = abs r • gauge s x := by
  rw [← gauge_smul_of_nonneg (abs_nonneg r)]
  obtain h | h := abs_choice r
  · rw [h]
    
  · rw [h, neg_smul, gauge_neg Symmetric]
    
  · infer_instance
    

theorem gauge_add_le (hs : Convex ℝ s) (absorbs : Absorbent ℝ s) (x y : E) : gauge s (x + y) ≤ gauge s x + gauge s y :=
  by
  refine' le_of_forall_pos_lt_add fun ε hε => _
  obtain ⟨a, ha, ha', hx⟩ := exists_lt_of_gauge_lt Absorbs (lt_add_of_pos_right (gauge s x) (half_pos hε))
  obtain ⟨b, hb, hb', hy⟩ := exists_lt_of_gauge_lt Absorbs (lt_add_of_pos_right (gauge s y) (half_pos hε))
  rw [mem_smul_set_iff_inv_smul_mem₀ ha.ne'] at hx
  rw [mem_smul_set_iff_inv_smul_mem₀ hb.ne'] at hy
  suffices gauge s (x + y) ≤ a + b by
    linarith
  have hab : 0 < a + b := add_pos ha hb
  apply gauge_le_of_mem hab.le
  have := convex_iff_div.1 hs hx hy ha.le hb.le hab
  rwa [smul_smul, smul_smul, mul_comm_div', mul_comm_div', ← mul_div_assoc, ← mul_div_assoc, mul_inv_cancel ha.ne',
    mul_inv_cancel hb.ne', ← smul_add, one_div, ← mem_smul_set_iff_inv_smul_mem₀ hab.ne'] at this

/-- `gauge s` as a seminorm when `s` is symmetric, convex and absorbent. -/
@[simps]
def gaugeSeminorm (symmetric : ∀, ∀ x ∈ s, ∀, -x ∈ s) (hs : Convex ℝ s) (hs' : Absorbent ℝ s) : Seminorm ℝ E where
  toFun := gauge s
  smul' := fun r x => by
    rw [gauge_smul Symmetric, Real.norm_eq_abs, smul_eq_mul] <;> infer_instance
  triangle' := gauge_add_le hs hs'

/-- Any seminorm arises a the gauge of its unit ball. -/
theorem Seminorm.gauge_ball (p : Seminorm ℝ E) : gauge (p.ball 0 1) = p := by
  ext
  obtain hp | hp := { r : ℝ | 0 < r ∧ x ∈ r • p.ball 0 1 }.eq_empty_or_nonempty
  · rw [gauge, hp, Real.Inf_empty]
    by_contra
    have hpx : 0 < p x := (p.nonneg x).lt_of_ne h
    have hpx₂ : 0 < 2 * p x := mul_pos zero_lt_two hpx
    refine' hp.subset ⟨hpx₂, (2 * p x)⁻¹ • x, _, smul_inv_smul₀ hpx₂.ne' _⟩
    rw [p.mem_ball_zero, p.smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpx₂), inv_mul_lt_iff hpx₂, mul_oneₓ]
    exact lt_mul_of_one_lt_left hpx one_lt_two
    
  refine' IsGlb.cInf_eq ⟨fun r => _, fun r hr => le_of_forall_pos_le_add $ fun ε hε => _⟩ hp
  · rintro ⟨hr, y, hy, rfl⟩
    rw [p.mem_ball_zero] at hy
    rw [p.smul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_of_le_one_right hr.le hy.le
    
  · have hpε : 0 < p x + ε := add_pos_of_nonneg_of_pos (p.nonneg _) hε
    refine' hr ⟨hpε, (p x + ε)⁻¹ • x, _, smul_inv_smul₀ hpε.ne' _⟩
    rw [p.mem_ball_zero, p.smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpε), inv_mul_lt_iff hpε, mul_oneₓ]
    exact lt_add_of_pos_right _ hε
    

theorem Seminorm.gauge_seminorm_ball (p : Seminorm ℝ E) :
    gaugeSeminorm (fun x => p.symmetric_ball_zero 1) (p.convex_ball 0 1) (p.absorbent_ball_zero zero_lt_one) = p :=
  Seminorm.ext p.gauge_ball

end gauge

