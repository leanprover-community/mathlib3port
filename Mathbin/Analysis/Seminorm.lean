import Mathbin.Analysis.Convex.Function
import Mathbin.Analysis.Convex.Star
import Mathbin.Analysis.NormedSpace.Ordered
import Mathbin.Analysis.NormedSpace.Pointwise
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
* `norm_seminorm 𝕜 E`: The norm on `E` as a seminorm.
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

open_locale Pointwise TopologicalSpace Nnreal

variable {R 𝕜 𝕝 E F G ι : Type _}

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

theorem balanced_univ : Balanced 𝕜 (univ : Set E) := fun a ha => subset_univ _

theorem Balanced.union (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B) : Balanced 𝕜 (A ∪ B) := by
  intro a ha t ht
  rw [smul_set_union] at ht
  exact ht.imp (fun x => hA _ ha x) fun x => hB _ ha x

end HasScalar

section AddCommGroupₓ

variable [AddCommGroupₓ E] [Module 𝕜 E] {s t u v A B : Set E}

theorem Balanced.inter (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B) : Balanced 𝕜 (A ∩ B) := by
  rintro a ha _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
  exact ⟨hA _ ha ⟨_, hx₁, rfl⟩, hB _ ha ⟨_, hx₂, rfl⟩⟩

theorem Balanced.add (hA₁ : Balanced 𝕜 A) (hA₂ : Balanced 𝕜 B) : Balanced 𝕜 (A + B) := by
  rintro a ha _ ⟨_, ⟨x, y, hx, hy, rfl⟩, rfl⟩
  rw [smul_add]
  exact ⟨_, _, hA₁ _ ha ⟨_, hx, rfl⟩, hA₂ _ ha ⟨_, hy, rfl⟩, rfl⟩

theorem Absorbs.mono (hs : Absorbs 𝕜 s u) (hst : s ⊆ t) (hvu : v ⊆ u) : Absorbs 𝕜 t v :=
  let ⟨r, hr, h⟩ := hs
  ⟨r, hr, fun a ha => hvu.trans <| (h _ ha).trans <| smul_set_mono hst⟩

theorem Absorbs.mono_left (hs : Absorbs 𝕜 s u) (h : s ⊆ t) : Absorbs 𝕜 t u :=
  hs.mono h subset.rfl

theorem Absorbs.mono_right (hs : Absorbs 𝕜 s u) (h : v ⊆ u) : Absorbs 𝕜 s v :=
  hs.mono subset.rfl h

theorem Absorbs.union (hu : Absorbs 𝕜 s u) (hv : Absorbs 𝕜 s v) : Absorbs 𝕜 s (u ∪ v) := by
  obtain ⟨a, ha, hu⟩ := hu
  obtain ⟨b, hb, hv⟩ := hv
  exact
    ⟨max a b, lt_max_of_lt_left ha, fun c hc =>
      union_subset (hu _ <| le_of_max_le_left hc) (hv _ <| le_of_max_le_right hc)⟩

@[simp]
theorem absorbs_union : Absorbs 𝕜 s (u ∪ v) ↔ Absorbs 𝕜 s u ∧ Absorbs 𝕜 s v :=
  ⟨fun h => ⟨h.mono_right <| subset_union_left _ _, h.mono_right <| subset_union_right _ _⟩, fun h => h.1.union h.2⟩

theorem Absorbent.subset (hA : Absorbent 𝕜 A) (hAB : A ⊆ B) : Absorbent 𝕜 B := by
  rintro x
  obtain ⟨r, hr, hx⟩ := hA x
  exact ⟨r, hr, fun a ha => Set.smul_set_mono hAB <| hx a ha⟩

theorem absorbent_iff_forall_absorbs_singleton : Absorbent 𝕜 A ↔ ∀ x, Absorbs 𝕜 A {x} := by
  simp_rw [Absorbs, Absorbent, singleton_subset_iff]

theorem Absorbent.absorbs (hs : Absorbent 𝕜 s) {x : E} : Absorbs 𝕜 s {x} :=
  absorbent_iff_forall_absorbs_singleton.1 hs _

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

variable [NormedField 𝕜] [NormedRing 𝕝] [NormedSpace 𝕜 𝕝] [AddCommGroupₓ E] [Module 𝕜 E] [SmulWithZero 𝕝 E]
  [IsScalarTower 𝕜 𝕝 E] {s t u v A B : Set E} {a b : 𝕜}

/-- Scalar multiplication (by possibly different types) of a balanced set is monotone. -/
theorem Balanced.smul_mono (hs : Balanced 𝕝 s) {a : 𝕝} {b : 𝕜} (h : ∥a∥ ≤ ∥b∥) : a • s ⊆ b • s := by
  obtain rfl | hb := eq_or_ne b 0
  · rw [norm_zero] at h
    rw [norm_eq_zero.1 (h.antisymm <| norm_nonneg _)]
    obtain rfl | h := s.eq_empty_or_nonempty
    · simp_rw [smul_set_empty]
      
    · simp_rw [zero_smul_set h]
      
    
  rintro _ ⟨x, hx, rfl⟩
  refine' ⟨b⁻¹ • a • x, _, smul_inv_smul₀ hb _⟩
  rw [← smul_assoc]
  refine' hs _ _ (smul_mem_smul_set hx)
  rw [norm_smul, norm_inv, ← div_eq_inv_mul]
  exact div_le_one_of_le h (norm_nonneg _)

/-- A balanced set absorbs itself. -/
theorem Balanced.absorbs_self (hA : Balanced 𝕜 A) : Absorbs 𝕜 A A := by
  use 1, zero_lt_one
  intro a ha x hx
  rw [mem_smul_set_iff_inv_smul_mem₀]
  · apply hA a⁻¹
    · rw [norm_inv]
      exact inv_le_one ha
      
    · rw [mem_smul_set]
      use x, hx
      
    
  · rw [← norm_pos_iff]
    calc 0 < 1 := zero_lt_one _ ≤ ∥a∥ := ha
    

theorem Balanced.subset_smul (hA : Balanced 𝕜 A) (ha : 1 ≤ ∥a∥) : A ⊆ a • A := by
  refine' (subset_set_smul_iff₀ _).2 (hA a⁻¹ _)
  · rintro rfl
    rw [norm_zero] at ha
    exact zero_lt_one.not_le ha
    
  · rw [norm_inv]
    exact inv_le_one ha
    

theorem Balanced.smul_eq (hA : Balanced 𝕜 A) (ha : ∥a∥ = 1) : a • A = A :=
  (hA _ ha.le).antisymm <| hA.subset_smul ha.ge

theorem Absorbs.inter (hs : Absorbs 𝕜 s u) (ht : Absorbs 𝕜 t u) : Absorbs 𝕜 (s ∩ t) u := by
  obtain ⟨a, ha, hs⟩ := hs
  obtain ⟨b, hb, ht⟩ := ht
  have h : 0 < max a b := lt_max_of_lt_left ha
  refine' ⟨max a b, lt_max_of_lt_left ha, fun c hc => _⟩
  rw [smul_set_inter₀ (norm_pos_iff.1 <| h.trans_le hc)]
  exact subset_inter (hs _ <| le_of_max_le_left hc) (ht _ <| le_of_max_le_right hc)

@[simp]
theorem absorbs_inter : Absorbs 𝕜 (s ∩ t) u ↔ Absorbs 𝕜 s u ∧ Absorbs 𝕜 t u :=
  ⟨fun h => ⟨h.mono_left <| inter_subset_left _ _, h.mono_left <| inter_subset_right _ _⟩, fun h => h.1.inter h.2⟩

theorem absorbent_univ : Absorbent 𝕜 (univ : Set E) := by
  refine' fun x => ⟨1, zero_lt_one, fun a ha => _⟩
  rw [smul_set_univ₀ (norm_pos_iff.1 <| zero_lt_one.trans_le ha)]
  exact trivialₓ

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
theorem balanced_zero_union_interior (hA : Balanced 𝕜 A) : Balanced 𝕜 ((0 : Set E) ∪ Interior A) := by
  intro a ha
  by_cases' a = 0
  · rw [h, zero_smul_set]
    exacts[subset_union_left _ _, ⟨0, Or.inl rfl⟩]
    
  · rw [← image_smul, image_union]
    apply union_subset_union
    · rw [image_zero, smul_zero]
      rfl
      
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

section NondiscreteNormedField

variable [NondiscreteNormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] {s : Set E}

theorem absorbs_zero_iff : Absorbs 𝕜 s 0 ↔ (0 : E) ∈ s := by
  refine' ⟨_, fun h => ⟨1, zero_lt_one, fun a _ => zero_subset.2 <| zero_mem_smul_set h⟩⟩
  rintro ⟨r, hr, h⟩
  obtain ⟨a, ha⟩ := NormedSpace.exists_lt_norm 𝕜 𝕜 r
  have := h _ ha.le
  rwa [zero_subset, zero_mem_smul_set_iff] at this
  exact norm_ne_zero_iff.1 (hr.trans ha).ne'

theorem Absorbent.zero_mem (hs : Absorbent 𝕜 s) : (0 : E) ∈ s :=
  absorbs_zero_iff.1 <| absorbent_iff_forall_absorbs_singleton.1 hs _

end NondiscreteNormedField

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

instance FunLike : FunLike (Seminorm 𝕜 E) E fun _ => ℝ where
  coe := Seminorm.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr

/-- Helper instance for when there's too many metavariables to apply `to_fun.to_coe_fn`. -/
instance : CoeFun (Seminorm 𝕜 E) fun _ => E → ℝ :=
  ⟨fun p => p.to_fun⟩

@[ext]
theorem ext {p q : Seminorm 𝕜 E} (h : ∀ x, (p : E → ℝ) x = q x) : p = q :=
  FunLike.ext p q h

instance : Zero (Seminorm 𝕜 E) :=
  ⟨{ toFun := 0, smul' := fun _ _ => (mul_zero _).symm, triangle' := fun _ _ => Eq.ge (zero_addₓ _) }⟩

@[simp]
theorem coe_zero : ⇑(0 : Seminorm 𝕜 E) = 0 :=
  rfl

@[simp]
theorem zero_apply (x : E) : (0 : Seminorm 𝕜 E) x = 0 :=
  rfl

instance : Inhabited (Seminorm 𝕜 E) :=
  ⟨0⟩

variable (p : Seminorm 𝕜 E) (c : 𝕜) (x y : E) (r : ℝ)

protected theorem smul : p (c • x) = ∥c∥ * p x :=
  p.smul' _ _

protected theorem triangle : p (x + y) ≤ p x + p y :=
  p.triangle' _ _

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to a seminorm. -/
instance [HasScalar R ℝ] [HasScalar R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] : HasScalar R (Seminorm 𝕜 E) where
  smul := fun r p =>
    { toFun := fun x => r • p x,
      smul' := fun _ _ => by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), Nnreal.smul_def, smul_eq_mul]
        rw [p.smul, mul_left_commₓ],
      triangle' := fun _ _ => by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), Nnreal.smul_def, smul_eq_mul]
        exact (mul_le_mul_of_nonneg_left (p.triangle _ _) (Nnreal.coe_nonneg _)).trans_eq (mul_addₓ _ _ _) }

theorem coe_smul [HasScalar R ℝ] [HasScalar R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p : Seminorm 𝕜 E) :
    ⇑(r • p) = r • p :=
  rfl

@[simp]
theorem smul_apply [HasScalar R ℝ] [HasScalar R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p : Seminorm 𝕜 E) (x : E) :
    (r • p) x = r • p x :=
  rfl

instance : Add (Seminorm 𝕜 E) where
  add := fun p q =>
    { toFun := fun x => p x + q x,
      smul' := fun a x => by
        rw [p.smul, q.smul, mul_addₓ],
      triangle' := fun _ _ =>
        LE.le.trans_eq (add_le_add (p.triangle _ _) (q.triangle _ _)) (add_add_add_commₓ _ _ _ _) }

theorem coe_add (p q : Seminorm 𝕜 E) : ⇑(p + q) = p + q :=
  rfl

@[simp]
theorem add_apply (p q : Seminorm 𝕜 E) (x : E) : (p + q) x = p x + q x :=
  rfl

instance : AddMonoidₓ (Seminorm 𝕜 E) :=
  FunLike.coe_injective.addMonoidSmul _ rfl coe_add fun p n => coe_smul n p

instance : OrderedCancelAddCommMonoid (Seminorm 𝕜 E) :=
  { Seminorm.addMonoid,
    (FunLike.coe_injective.OrderedCancelAddCommMonoid _ rfl coe_add : OrderedCancelAddCommMonoid (Seminorm 𝕜 E)) with
    nsmul := · • · }

instance [Monoidₓ R] [MulAction R ℝ] [HasScalar R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] : MulAction R (Seminorm 𝕜 E) :=
  FunLike.coe_injective.MulAction _ coe_smul

variable (𝕜 E)

/-- `coe_fn` as an `add_monoid_hom`. Helper definition for showing that `seminorm 𝕜 E` is
a module. -/
@[simps]
def coe_fn_add_monoid_hom : AddMonoidHom (Seminorm 𝕜 E) (E → ℝ) :=
  ⟨coeFn, coe_zero, coe_add⟩

theorem coe_fn_add_monoid_hom_injective : Function.Injective (coe_fn_add_monoid_hom 𝕜 E) :=
  show @Function.Injective (Seminorm 𝕜 E) (E → ℝ) coeFn from FunLike.coe_injective

variable {𝕜 E}

instance [Monoidₓ R] [DistribMulAction R ℝ] [HasScalar R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] :
    DistribMulAction R (Seminorm 𝕜 E) :=
  (coe_fn_add_monoid_hom_injective 𝕜 E).DistribMulAction _ coe_smul

instance [Semiringₓ R] [Module R ℝ] [HasScalar R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] : Module R (Seminorm 𝕜 E) :=
  (coe_fn_add_monoid_hom_injective 𝕜 E).Module R _ coe_smul

noncomputable instance : HasSup (Seminorm 𝕜 E) where
  sup := fun p q =>
    { toFun := p⊔q,
      triangle' := fun x y =>
        sup_le ((p.triangle x y).trans <| add_le_add le_sup_left le_sup_left)
          ((q.triangle x y).trans <| add_le_add le_sup_right le_sup_right),
      smul' := fun x v =>
        (congr_arg2ₓ max (p.smul x v) (q.smul x v)).trans <| (mul_max_of_nonneg _ _ <| norm_nonneg x).symm }

@[simp]
theorem coe_sup (p q : Seminorm 𝕜 E) : ⇑(p⊔q) = p⊔q :=
  rfl

instance : PartialOrderₓ (Seminorm 𝕜 E) :=
  PartialOrderₓ.lift _ FunLike.coe_injective

theorem le_def (p q : Seminorm 𝕜 E) : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl

theorem lt_def (p q : Seminorm 𝕜 E) : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl

noncomputable instance : SemilatticeSup (Seminorm 𝕜 E) :=
  Function.Injective.semilatticeSup _ FunLike.coe_injective coe_sup

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

section Module

variable [AddCommGroupₓ E] [AddCommGroupₓ F] [AddCommGroupₓ G]

variable [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]

variable [HasScalar R ℝ] [HasScalar R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ]

/-- Composition of a seminorm with a linear map is a seminorm. -/
def comp (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : Seminorm 𝕜 E where
  toFun := fun x => p (f x)
  smul' := fun _ _ => (congr_argₓ p (f.map_smul _ _)).trans (p.smul _ _)
  triangle' := fun _ _ => Eq.trans_le (congr_argₓ p (f.map_add _ _)) (p.triangle _ _)

theorem coe_comp (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : ⇑p.comp f = p ∘ f :=
  rfl

@[simp]
theorem comp_apply (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (x : E) : (p.comp f) x = p (f x) :=
  rfl

@[simp]
theorem comp_id (p : Seminorm 𝕜 E) : p.comp LinearMap.id = p :=
  ext fun _ => rfl

@[simp]
theorem comp_zero (p : Seminorm 𝕜 F) : p.comp (0 : E →ₗ[𝕜] F) = 0 :=
  ext fun _ => Seminorm.zero _

@[simp]
theorem zero_comp (f : E →ₗ[𝕜] F) : (0 : Seminorm 𝕜 F).comp f = 0 :=
  ext fun _ => rfl

theorem comp_comp (p : Seminorm 𝕜 G) (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) : p.comp (g.comp f) = (p.comp g).comp f :=
  ext fun _ => rfl

theorem add_comp (p q : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : (p + q).comp f = p.comp f + q.comp f :=
  ext fun _ => rfl

theorem comp_triangle (p : Seminorm 𝕜 F) (f g : E →ₗ[𝕜] F) : p.comp (f + g) ≤ p.comp f + p.comp g := fun _ =>
  p.triangle _ _

theorem smul_comp (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (c : R) : (c • p).comp f = c • p.comp f :=
  ext fun _ => rfl

theorem comp_mono {p : Seminorm 𝕜 F} {q : Seminorm 𝕜 F} (f : E →ₗ[𝕜] F) (hp : p ≤ q) : p.comp f ≤ q.comp f := fun _ =>
  hp _

section NormOneClass

variable [NormOneClass 𝕜] (p : Seminorm 𝕜 E) (x y : E) (r : ℝ)

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

instance : OrderBot (Seminorm 𝕜 E) :=
  ⟨0, nonneg⟩

@[simp]
theorem coe_bot : ⇑(⊥ : Seminorm 𝕜 E) = 0 :=
  rfl

theorem bot_eq_zero : (⊥ : Seminorm 𝕜 E) = 0 :=
  rfl

theorem finset_sup_apply (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) :
    s.sup p x = ↑(s.sup fun i => ⟨p i x, nonneg (p i) x⟩ : Nnreal) := by
  induction' s using Finset.cons_induction_on with a s ha ih
  · rw [Finset.sup_empty, Finset.sup_empty, coe_bot, _root_.bot_eq_zero, Pi.zero_apply, Nonneg.coe_zero]
    
  · rw [Finset.sup_cons, Finset.sup_cons, coe_sup, sup_eq_max, Pi.sup_apply, sup_eq_max, Nnreal.coe_max, Subtype.coe_mk,
      ih]
    

end NormOneClass

end Module

end SemiNormedRing

section SemiNormedCommRing

variable [SemiNormedCommRing 𝕜] [AddCommGroupₓ E] [AddCommGroupₓ F] [Module 𝕜 E] [Module 𝕜 F]

theorem comp_smul (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (c : 𝕜) : p.comp (c • f) = ∥c∥₊ • p.comp f :=
  ext fun _ => by
    rw [comp_apply, smul_apply, LinearMap.smul_apply, p.smul, Nnreal.smul_def, coe_nnnorm, smul_eq_mul, comp_apply]

theorem comp_smul_apply (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (c : 𝕜) (x : E) : p.comp (c • f) x = ∥c∥ * p (f x) :=
  p.smul _ _

end SemiNormedCommRing

/-! ### Seminorm ball -/


section SemiNormedRing

variable [SemiNormedRing 𝕜]

section AddCommGroupₓ

variable [AddCommGroupₓ E]

section HasScalar

variable [HasScalar 𝕜 E] (p : Seminorm 𝕜 E)

/-- The ball of radius `r` at `x` with respect to seminorm `p` is the set of elements `y` with
`p (y - x) < `r`. -/
def ball (x : E) (r : ℝ) :=
  { y : E | p (y - x) < r }

variable {x y : E} {r : ℝ}

@[simp]
theorem mem_ball : y ∈ ball p x r ↔ p (y - x) < r :=
  Iff.rfl

theorem mem_ball_zero : y ∈ ball p 0 r ↔ p y < r := by
  rw [mem_ball, sub_zero]

theorem ball_zero_eq : ball p 0 r = { y : E | p y < r } :=
  Set.ext fun x => p.mem_ball_zero

@[simp]
theorem ball_zero' (x : E) (hr : 0 < r) : ball (0 : Seminorm 𝕜 E) x r = Set.Univ := by
  rw [Set.eq_univ_iff_forall, ball]
  simp [hr]

theorem ball_sup (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 E) (e : E) (r : ℝ) : ball (p⊔q) e r = ball p e r ∩ ball q e r := by
  simp_rw [ball, ← Set.set_of_and, coe_sup, Pi.sup_apply, sup_lt_iff]

theorem ball_finset_sup' (p : ι → Seminorm 𝕜 E) (s : Finset ι) (H : s.nonempty) (e : E) (r : ℝ) :
    ball (s.sup' H p) e r = s.inf' H fun i => ball (p i) e r := by
  induction' H using Finset.Nonempty.cons_induction with a a s ha hs ih
  · classical
    simp
    
  · rw [Finset.sup'_cons hs, Finset.inf'_cons hs, ball_sup, inf_eq_inter, ih]
    

theorem ball_mono {p : Seminorm 𝕜 E} {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) : p.ball x r₁ ⊆ p.ball x r₂ := fun _ hx : _ < _ =>
  hx.trans_le h

theorem ball_antitone {p q : Seminorm 𝕜 E} (h : q ≤ p) : p.ball x r ⊆ q.ball x r := fun _ => (h _).trans_lt

theorem ball_add_ball_subset (p : Seminorm 𝕜 E) (r₁ r₂ : ℝ) (x₁ x₂ : E) :
    p.ball (x₁ : E) r₁ + p.ball (x₂ : E) r₂ ⊆ p.ball (x₁ + x₂) (r₁ + r₂) := by
  rintro x ⟨y₁, y₂, hy₁, hy₂, rfl⟩
  rw [mem_ball, add_sub_comm]
  exact (p.triangle _ _).trans_lt (add_lt_add hy₁ hy₂)

end HasScalar

section Module

variable [Module 𝕜 E]

variable [AddCommGroupₓ F] [Module 𝕜 F]

theorem ball_comp (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (x : E) (r : ℝ) : (p.comp f).Ball x r = f ⁻¹' p.ball (f x) r := by
  ext
  simp_rw [ball, mem_preimage, comp_apply, Set.mem_set_of_eq, map_sub]

section NormOneClass

variable [NormOneClass 𝕜] (p : Seminorm 𝕜 E)

@[simp]
theorem ball_bot {r : ℝ} (x : E) (hr : 0 < r) : ball (⊥ : Seminorm 𝕜 E) x r = Set.Univ :=
  ball_zero' x hr

/-- Seminorm-balls at the origin are balanced. -/
theorem balanced_ball_zero (r : ℝ) : Balanced 𝕜 (ball p 0 r) := by
  rintro a ha x ⟨y, hy, hx⟩
  rw [mem_ball_zero, ← hx, p.smul]
  calc _ ≤ p y := mul_le_of_le_one_left (p.nonneg _) ha _ < r := by
      rwa [mem_ball_zero] at hy

theorem ball_finset_sup_eq_Inter (p : ι → Seminorm 𝕜 E) (s : Finset ι) (e : E) {r : ℝ} (hr : 0 < r) :
    ball (s.sup p) e r = ⋂ i ∈ s, ball (p i) e r := by
  lift r to Nnreal using hr.le
  simp_rw [ball, Inter_set_of, finset_sup_apply, Nnreal.coe_lt_coe, Finset.sup_lt_iff (show ⊥ < r from hr), ←
    Nnreal.coe_lt_coe, Subtype.coe_mk]

theorem ball_finset_sup (p : ι → Seminorm 𝕜 E) (s : Finset ι) (e : E) {r : ℝ} (hr : 0 < r) :
    ball (s.sup p) e r = s.inf fun i => ball (p i) e r := by
  rw [Finset.inf_eq_infi]
  exact ball_finset_sup_eq_Inter _ _ _ hr

theorem ball_smul_ball (p : Seminorm 𝕜 E) (r₁ r₂ : ℝ) : Metric.Ball (0 : 𝕜) r₁ • p.ball 0 r₂ ⊆ p.ball 0 (r₁ * r₂) := by
  rw [Set.subset_def]
  intro x hx
  rw [Set.mem_smul] at hx
  rcases hx with ⟨a, y, ha, hy, hx⟩
  rw [← hx, mem_ball_zero, Seminorm.smul]
  exact mul_lt_mul'' (mem_ball_zero_iff.mp ha) (p.mem_ball_zero.mp hy) (norm_nonneg a) (p.nonneg y)

end NormOneClass

end Module

end AddCommGroupₓ

end SemiNormedRing

section NormedField

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] (p : Seminorm 𝕜 E) {A B : Set E} {a : 𝕜} {r : ℝ} {x : E}

/-- Seminorm-balls at the origin are absorbent. -/
protected theorem absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (ball p (0 : E) r) := by
  rw [absorbent_iff_nonneg_lt]
  rintro x
  have hxr : 0 ≤ p x / r := div_nonneg (p.nonneg _) hr.le
  refine' ⟨p x / r, hxr, fun a ha => _⟩
  have ha₀ : 0 < ∥a∥ := hxr.trans_lt ha
  refine' ⟨a⁻¹ • x, _, smul_inv_smul₀ (norm_pos_iff.1 ha₀) x⟩
  rwa [mem_ball_zero, p.smul, norm_inv, inv_mul_lt_iff ha₀, ← div_lt_iff hr]

/-- Seminorm-balls containing the origin are absorbent. -/
protected theorem absorbent_ball (hpr : p x < r) : Absorbent 𝕜 (ball p x r) := by
  refine' (p.absorbent_ball_zero <| sub_pos.2 hpr).Subset fun y hy => _
  rw [p.mem_ball_zero] at hy
  exact p.mem_ball.2 ((p.sub_le _ _).trans_lt <| add_lt_of_lt_sub_right hy)

theorem symmetric_ball_zero (r : ℝ) (hx : x ∈ ball p 0 r) : -x ∈ ball p 0 r :=
  balanced_ball_zero p r (-1)
    (by
      rw [norm_neg, norm_one])
    ⟨x, hx, by
      rw [neg_smul, one_smul]⟩

@[simp]
theorem neg_ball (p : Seminorm 𝕜 E) (r : ℝ) (x : E) : -ball p x r = ball p (-x) r := by
  ext
  rw [mem_neg, mem_ball, mem_ball, ← neg_add', sub_neg_eq_add, p.neg]

@[simp]
theorem smul_ball_preimage (p : Seminorm 𝕜 E) (y : E) (r : ℝ) (a : 𝕜) (ha : a ≠ 0) :
    (· • ·) a ⁻¹' p.ball y r = p.ball (a⁻¹ • y) (r / ∥a∥) :=
  Set.ext fun _ => by
    rw [mem_preimage, mem_ball, mem_ball, lt_div_iff (norm_pos_iff.mpr ha), mul_comm, ← p.smul, smul_sub,
      smul_inv_smul₀ ha]

end NormedField

section NormedLinearOrderedField

variable [NormedLinearOrderedField 𝕜] [AddCommGroupₓ E] [NormedSpace ℝ 𝕜] [Module 𝕜 E]

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

/-! ### The norm as a seminorm -/


section normSeminorm

variable (𝕜 E) [NormedField 𝕜] [SemiNormedGroup E] [NormedSpace 𝕜 E] {r : ℝ}

/-- The norm of a seminormed group as a seminorm. -/
def normSeminorm : Seminorm 𝕜 E :=
  ⟨norm, norm_smul, norm_add_le⟩

@[simp]
theorem coe_norm_seminorm : ⇑normSeminorm 𝕜 E = norm :=
  rfl

@[simp]
theorem ball_norm_seminorm : (normSeminorm 𝕜 E).Ball = Metric.Ball := by
  ext x r y
  simp only [Seminorm.mem_ball, Metric.mem_ball, coe_norm_seminorm, dist_eq_norm]

variable {𝕜 E} {x : E}

/-- Balls at the origin are absorbent. -/
theorem absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (Metric.Ball (0 : E) r) := by
  rw [← ball_norm_seminorm 𝕜]
  exact (normSeminorm _ _).absorbent_ball_zero hr

/-- Balls containing the origin are absorbent. -/
theorem absorbent_ball (hx : ∥x∥ < r) : Absorbent 𝕜 (Metric.Ball x r) := by
  rw [← ball_norm_seminorm 𝕜]
  exact (normSeminorm _ _).absorbent_ball hx

/-- Balls at the origin are balanced. -/
theorem balanced_ball_zero [NormOneClass 𝕜] : Balanced 𝕜 (Metric.Ball (0 : E) r) := by
  rw [← ball_norm_seminorm 𝕜]
  exact (normSeminorm _ _).balanced_ball_zero r

end normSeminorm

/-! ### Minkowksi functional -/


section gauge

noncomputable section

section AddCommGroupₓ

variable [AddCommGroupₓ E] [Module ℝ E]

/-- The Minkowski functional. Given a set `s` in a real vector space, `gauge s` is the functional
which sends `x : E` to the smallest `r : ℝ` such that `x` is in `s` scaled by `r`. -/
def gauge (s : Set E) (x : E) : ℝ :=
  Inf { r : ℝ | 0 < r ∧ x ∈ r • s }

variable {s t : Set E} {a : ℝ} {x : E}

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

theorem gauge_mono (hs : Absorbent ℝ s) (h : s ⊆ t) : gauge t ≤ gauge s := fun x =>
  (cInf_le_cInf gauge_set_bdd_below hs.gauge_set_nonempty) fun r hr => ⟨hr.1, smul_set_mono h hr.2⟩

theorem exists_lt_of_gauge_lt (absorbs : Absorbent ℝ s) (h : gauge s x < a) : ∃ b, 0 < b ∧ b < a ∧ x ∈ b • s := by
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
    

@[simp]
theorem gauge_zero' : gauge (0 : Set E) = 0 := by
  ext
  rw [gauge_def']
  obtain rfl | hx := eq_or_ne x 0
  · simp only [cInf_Ioi, mem_zero, Pi.zero_apply, eq_self_iff_true, sep_true, smul_zero]
    
  · simp only [mem_zero, Pi.zero_apply, inv_eq_zero, smul_eq_zero]
    convert Real.Inf_empty
    exact eq_empty_iff_forall_not_mem.2 fun r hr => hr.2.elim (ne_of_gtₓ hr.1) hx
    

@[simp]
theorem gauge_empty : gauge (∅ : Set E) = 0 := by
  ext
  simp only [gauge_def', Real.Inf_empty, mem_empty_eq, Pi.zero_apply, sep_false]

theorem gauge_of_subset_zero (h : s ⊆ 0) : gauge s = 0 := by
  obtain rfl | rfl := subset_singleton_iff_eq.1 h
  exacts[gauge_empty, gauge_zero']

/-- The gauge is always nonnegative. -/
theorem gauge_nonneg (x : E) : 0 ≤ gauge s x :=
  (Real.Inf_nonneg _) fun x hx => hx.1.le

theorem gauge_neg (symmetric : ∀, ∀ x ∈ s, ∀, -x ∈ s) (x : E) : gauge s (-x) = gauge s x := by
  have : ∀ x, -x ∈ s ↔ x ∈ s := fun x =>
    ⟨fun h => by
      simpa using Symmetric _ h, Symmetric x⟩
  rw [gauge_def', gauge_def']
  simp_rw [smul_neg, this]

theorem gauge_le_of_mem (ha : 0 ≤ a) (hx : x ∈ a • s) : gauge s x ≤ a := by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [mem_singleton_iff.1 (zero_smul_subset _ hx), gauge_zero]
    
  · exact cInf_le gauge_set_bdd_below ⟨ha', hx⟩
    

theorem gauge_le_eq (hs₁ : Convex ℝ s) (hs₀ : (0 : E) ∈ s) (hs₂ : Absorbent ℝ s) (ha : 0 ≤ a) :
    { x | gauge s x ≤ a } = ⋂ (r : ℝ) (H : a < r), r • s := by
  ext
  simp_rw [Set.mem_Inter, Set.mem_set_of_eq]
  constructor
  · intro h r hr
    have hr' := ha.trans_lt hr
    rw [mem_smul_set_iff_inv_smul_mem₀ hr'.ne']
    obtain ⟨δ, δ_pos, hδr, hδ⟩ := exists_lt_of_gauge_lt hs₂ (h.trans_lt hr)
    suffices (r⁻¹ * δ) • δ⁻¹ • x ∈ s by
      rwa [smul_smul, mul_inv_cancel_right₀ δ_pos.ne'] at this
    rw [mem_smul_set_iff_inv_smul_mem₀ δ_pos.ne'] at hδ
    refine' hs₁.smul_mem_of_zero_mem hs₀ hδ ⟨mul_nonneg (inv_nonneg.2 hr'.le) δ_pos.le, _⟩
    rw [inv_mul_le_iff hr', mul_oneₓ]
    exact hδr.le
    
  · refine' fun h => le_of_forall_pos_lt_add fun ε hε => _
    have hε' := (lt_add_iff_pos_right a).2 (half_pos hε)
    exact (gauge_le_of_mem (ha.trans hε'.le) <| h _ hε').trans_lt (add_lt_add_left (half_lt_self hε) _)
    

theorem gauge_lt_eq' (absorbs : Absorbent ℝ s) (a : ℝ) :
    { x | gauge s x < a } = ⋃ (r : ℝ) (H : 0 < r) (H : r < a), r • s := by
  ext
  simp_rw [mem_set_of_eq, mem_Union, exists_prop]
  exact ⟨exists_lt_of_gauge_lt Absorbs, fun ⟨r, hr₀, hr₁, hx⟩ => (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩

theorem gauge_lt_eq (absorbs : Absorbent ℝ s) (a : ℝ) : { x | gauge s x < a } = ⋃ r ∈ Set.Ioo 0 (a : ℝ), r • s := by
  ext
  simp_rw [mem_set_of_eq, mem_Union, exists_prop, mem_Ioo, and_assoc]
  exact ⟨exists_lt_of_gauge_lt Absorbs, fun ⟨r, hr₀, hr₁, hx⟩ => (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩

theorem gauge_lt_one_subset_self (hs : Convex ℝ s) (h₀ : (0 : E) ∈ s) (absorbs : Absorbent ℝ s) :
    { x | gauge s x < 1 } ⊆ s := by
  rw [gauge_lt_eq Absorbs]
  apply Set.Union₂_subset
  rintro r hr _ ⟨y, hy, rfl⟩
  exact hs.smul_mem_of_zero_mem h₀ hy (Ioo_subset_Icc_self hr)

theorem gauge_le_one_of_mem {x : E} (hx : x ∈ s) : gauge s x ≤ 1 :=
  gauge_le_of_mem zero_le_one <| by
    rwa [one_smul]

theorem self_subset_gauge_le_one : s ⊆ { x | gauge s x ≤ 1 } := fun x => gauge_le_one_of_mem

theorem Convex.gauge_le (hs : Convex ℝ s) (h₀ : (0 : E) ∈ s) (absorbs : Absorbent ℝ s) (a : ℝ) :
    Convex ℝ { x | gauge s x ≤ a } := by
  by_cases' ha : 0 ≤ a
  · rw [gauge_le_eq hs h₀ Absorbs ha]
    exact convex_Inter fun i => convex_Inter fun hi => hs.smul _
    
  · convert convex_empty
    exact eq_empty_iff_forall_not_mem.2 fun x hx => ha <| (gauge_nonneg _).trans hx
    

theorem Balanced.star_convex (hs : Balanced ℝ s) : StarConvex ℝ 0 s :=
  star_convex_zero_iff.2 fun x hx a ha₀ ha₁ =>
    hs _
      (by
        rwa [Real.norm_of_nonneg ha₀])
      (smul_mem_smul_set hx)

theorem le_gauge_of_not_mem (hs₀ : StarConvex ℝ 0 s) (hs₂ : Absorbs ℝ s {x}) (hx : x ∉ a • s) : a ≤ gauge s x := by
  rw [star_convex_zero_iff] at hs₀
  obtain ⟨r, hr, h⟩ := hs₂
  refine' le_cInf ⟨r, hr, singleton_subset_iff.1 <| h _ (Real.norm_of_nonneg hr.le).Ge⟩ _
  rintro b ⟨hb, x, hx', rfl⟩
  refine' not_ltₓ.1 fun hba => hx _
  have ha := hb.trans hba
  refine' ⟨(a⁻¹ * b) • x, hs₀ hx' (mul_nonneg (inv_nonneg.2 ha.le) hb.le) _, _⟩
  · rw [← div_eq_inv_mul]
    exact div_le_one_of_le hba.le ha.le
    
  · rw [← mul_smul, mul_inv_cancel_left₀ ha.ne']
    

theorem one_le_gauge_of_not_mem (hs₁ : StarConvex ℝ 0 s) (hs₂ : Absorbs ℝ s {x}) (hx : x ∉ s) : 1 ≤ gauge s x :=
  le_gauge_of_not_mem hs₁ hs₂ <| by
    rwa [one_smul]

section LinearOrderedField

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
    

theorem gauge_smul_left_of_nonneg [MulActionWithZero α E] [SmulCommClass α ℝ ℝ] [IsScalarTower α ℝ ℝ]
    [IsScalarTower α ℝ E] {s : Set E} {a : α} (ha : 0 ≤ a) : gauge (a • s) = a⁻¹ • gauge s := by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [inv_zero, zero_smul, gauge_of_subset_zero (zero_smul_subset _)]
    
  ext
  rw [gauge_def', Pi.smul_apply, gauge_def', ← Real.Inf_smul_of_nonneg (inv_nonneg.2 ha)]
  congr 1
  ext r
  simp_rw [Set.mem_smul_set, Set.mem_sep_eq]
  constructor
  · rintro ⟨hr, y, hy, h⟩
    simp_rw [mem_Ioi]  at hr⊢
    refine' ⟨a • r, ⟨smul_pos ha' hr, _⟩, inv_smul_smul₀ ha'.ne' _⟩
    rwa [smul_inv₀, smul_assoc, ← h, inv_smul_smul₀ ha'.ne']
    
  · rintro ⟨r, ⟨hr, hx⟩, rfl⟩
    rw [mem_Ioi] at hr⊢
    have := smul_pos ha' hr
    refine' ⟨smul_pos (inv_pos.2 ha') hr, r⁻¹ • x, hx, _⟩
    rw [smul_inv₀, smul_assoc, inv_inv₀]
    

theorem gauge_smul_left [Module α E] [SmulCommClass α ℝ ℝ] [IsScalarTower α ℝ ℝ] [IsScalarTower α ℝ E] {s : Set E}
    (symmetric : ∀, ∀ x ∈ s, ∀, -x ∈ s) (a : α) : gauge (a • s) = (abs a)⁻¹ • gauge s := by
  rw [← gauge_smul_left_of_nonneg (abs_nonneg a)]
  obtain h | h := abs_choice a
  · rw [h]
    
  · rw [h, Set.neg_smul_set, ← Set.smul_set_neg]
    congr
    ext y
    refine' ⟨Symmetric _, fun hy => _⟩
    rw [← neg_negₓ y]
    exact Symmetric _ hy
    
  · infer_instance
    

end LinearOrderedField

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

theorem gauge_lt_one_eq_self_of_open (hs₁ : Convex ℝ s) (hs₀ : (0 : E) ∈ s) (hs₂ : IsOpen s) :
    { x | gauge s x < 1 } = s := by
  apply (gauge_lt_one_subset_self hs₁ ‹_› <| absorbent_nhds_zero <| hs₂.mem_nhds hs₀).antisymm
  convert interior_subset_gauge_lt_one s
  exact hs₂.interior_eq.symm

theorem gauge_lt_one_of_mem_of_open (hs₁ : Convex ℝ s) (hs₀ : (0 : E) ∈ s) (hs₂ : IsOpen s) {x : E} (hx : x ∈ s) :
    gauge s x < 1 := by
  rwa [← gauge_lt_one_eq_self_of_open hs₁ hs₀ hs₂] at hx

theorem gauge_lt_of_mem_smul (x : E) (ε : ℝ) (hε : 0 < ε) (hs₀ : (0 : E) ∈ s) (hs₁ : Convex ℝ s) (hs₂ : IsOpen s)
    (hx : x ∈ ε • s) : gauge s x < ε := by
  have : ε⁻¹ • x ∈ s := by
    rwa [← mem_smul_set_iff_inv_smul_mem₀ hε.ne']
  have h_gauge_lt := gauge_lt_one_of_mem_of_open hs₁ hs₀ hs₂ this
  rwa [gauge_smul_of_nonneg (inv_nonneg.2 hε.le), smul_eq_mul, inv_mul_lt_iff hε, mul_oneₓ] at h_gauge_lt
  infer_instance

end TopologicalSpace

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
def gaugeSeminorm (hs₀ : ∀, ∀ x ∈ s, ∀, -x ∈ s) (hs₁ : Convex ℝ s) (hs₂ : Absorbent ℝ s) : Seminorm ℝ E where
  toFun := gauge s
  smul' := fun r x => by
    rw [gauge_smul hs₀, Real.norm_eq_abs, smul_eq_mul] <;> infer_instance
  triangle' := gauge_add_le hs₁ hs₂

section gaugeSeminorm

variable {hs₀ : ∀, ∀ x ∈ s, ∀, -x ∈ s} {hs₁ : Convex ℝ s} {hs₂ : Absorbent ℝ s}

section TopologicalSpace

variable [TopologicalSpace E] [HasContinuousSmul ℝ E]

theorem gauge_seminorm_lt_one_of_open (hs : IsOpen s) {x : E} (hx : x ∈ s) : gaugeSeminorm hs₀ hs₁ hs₂ x < 1 :=
  gauge_lt_one_of_mem_of_open hs₁ hs₂.zero_mem hs hx

end TopologicalSpace

end gaugeSeminorm

/-- Any seminorm arises as the gauge of its unit ball. -/
@[simp]
protected theorem Seminorm.gauge_ball (p : Seminorm ℝ E) : gauge (p.ball 0 1) = p := by
  ext
  obtain hp | hp := { r : ℝ | 0 < r ∧ x ∈ r • p.ball 0 1 }.eq_empty_or_nonempty
  · rw [gauge, hp, Real.Inf_empty]
    by_contra
    have hpx : 0 < p x := (p.nonneg x).lt_of_ne h
    have hpx₂ : 0 < 2 * p x := mul_pos zero_lt_two hpx
    refine' hp.subset ⟨hpx₂, (2 * p x)⁻¹ • x, _, smul_inv_smul₀ hpx₂.ne' _⟩
    rw [p.mem_ball_zero, p.smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpx₂), inv_mul_lt_iff hpx₂, mul_oneₓ]
    exact lt_mul_of_one_lt_left hpx one_lt_two
    
  refine' IsGlb.cInf_eq ⟨fun r => _, fun r hr => le_of_forall_pos_le_add fun ε hε => _⟩ hp
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
  FunLike.coe_injective p.gauge_ball

end AddCommGroupₓ

section Norm

variable [SemiNormedGroup E] [NormedSpace ℝ E] {s : Set E} {r : ℝ} {x : E}

theorem gauge_unit_ball (x : E) : gauge (Metric.Ball (0 : E) 1) x = ∥x∥ := by
  obtain rfl | hx := eq_or_ne x 0
  · rw [norm_zero, gauge_zero]
    
  refine' (le_of_forall_pos_le_add fun ε hε => _).antisymm _
  · have := add_pos_of_nonneg_of_pos (norm_nonneg x) hε
    refine' gauge_le_of_mem this.le _
    rw [smul_ball this.ne', smul_zero, Real.norm_of_nonneg this.le, mul_oneₓ, mem_ball_zero_iff]
    exact lt_add_of_pos_right _ hε
    
  refine' le_gauge_of_not_mem balanced_ball_zero.star_convex (absorbent_ball_zero zero_lt_one).Absorbs fun h => _
  obtain hx' | hx' := eq_or_ne ∥x∥ 0
  · rw [hx'] at h
    exact hx (zero_smul_subset _ h)
    
  · rw [mem_smul_set_iff_inv_smul_mem₀ hx', mem_ball_zero_iff, norm_smul, norm_inv, norm_norm, inv_mul_cancel hx'] at h
    exact lt_irreflₓ _ h
    

theorem smul_unit_ball {r : ℝ} (hr : 0 < r) : r • Metric.Ball (0 : E) 1 = Metric.Ball (0 : E) r := by
  rw [smul_ball hr.ne', smul_zero, mul_oneₓ, Real.norm_of_nonneg hr.le]

theorem gauge_ball (hr : 0 < r) (x : E) : gauge (Metric.Ball (0 : E) r) x = ∥x∥ / r := by
  rw [← smul_unit_ball hr, gauge_smul_left, Pi.smul_apply, gauge_unit_ball, smul_eq_mul, abs_of_nonneg hr.le,
    div_eq_inv_mul]
  simp_rw [mem_ball_zero_iff, norm_neg]
  exact fun _ => id

theorem mul_gauge_le_norm (hs : Metric.Ball (0 : E) r ⊆ s) : r * gauge s x ≤ ∥x∥ := by
  obtain hr | hr := le_or_ltₓ r 0
  · exact (mul_nonpos_of_nonpos_of_nonneg hr <| gauge_nonneg _).trans (norm_nonneg _)
    
  rw [mul_comm, ← le_div_iff hr, ← gauge_ball hr]
  exact gauge_mono (absorbent_ball_zero hr) hs x

end Norm

end gauge

