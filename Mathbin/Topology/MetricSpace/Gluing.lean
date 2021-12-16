import Mathbin.Topology.MetricSpace.Isometry

/-!
# Metric space gluing

Gluing two metric spaces along a common subset. Formally, we are given

```
     Φ
  Z ---> X
  |
  |Ψ
  v
  Y
```
where `hΦ : isometry Φ` and `hΨ : isometry Ψ`.
We want to complete the square by a space `glue_space hΦ hΨ` and two isometries
`to_glue_l hΦ hΨ` and `to_glue_r hΦ hΨ` that make the square commute.
We start by defining a predistance on the disjoint union `X ⊕ Y`, for which
points `Φ p` and `Ψ p` are at distance 0. The (quotient) metric space associated
to this predistance is the desired space.

This is an instance of a more general construction, where `Φ` and `Ψ` do not have to be isometries,
but the distances in the image almost coincide, up to `2ε` say. Then one can almost glue the two
spaces so that the images of a point under `Φ` and `Ψ` are `ε`-close. If `ε > 0`, this yields a
metric space structure on `X ⊕ Y`, without the need to take a quotient. In particular, when `X`
and `Y` are inhabited, this gives a natural metric space structure on `X ⊕ Y`, where the basepoints
are at distance 1, say, and the distances between other points are obtained by going through the two
basepoints.

We also define the inductive limit of metric spaces. Given
```
     f 0        f 1        f 2        f 3
X 0 -----> X 1 -----> X 2 -----> X 3 -----> ...
```
where the `X n` are metric spaces and `f n` isometric embeddings, we define the inductive
limit of the `X n`, also known as the increasing union of the `X n` in this context, if we
identify `X n` and `X (n+1)` through `f n`. This is a metric space in which all `X n` embed
isometrically and in a way compatible with `f n`.

-/


noncomputable section 

universe u v w

open Function Set

open_locale uniformity

namespace Metric

section ApproxGluing

variable {X : Type u} {Y : Type v} {Z : Type w}

variable [MetricSpace X] [MetricSpace Y] {Φ : Z → X} {Ψ : Z → Y} {ε : ℝ}

open _root_.sum(inl inr)

/-- Define a predistance on `X ⊕ Y`, for which `Φ p` and `Ψ p` are at distance `ε` -/
def glue_dist (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) : Sum X Y → Sum X Y → ℝ
| inl x, inl y => dist x y
| inr x, inr y => dist x y
| inl x, inr y => (⨅ p, dist x (Φ p)+dist y (Ψ p))+ε
| inr x, inl y => (⨅ p, dist y (Φ p)+dist x (Ψ p))+ε

private theorem glue_dist_self (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) : ∀ x, glue_dist Φ Ψ ε x x = 0
| inl x => dist_self _
| inr x => dist_self _

theorem glue_dist_glued_points [Nonempty Z] (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (p : Z) :
  glue_dist Φ Ψ ε (inl (Φ p)) (inr (Ψ p)) = ε :=
  by 
    have  : (⨅ q, dist (Φ p) (Φ q)+dist (Ψ p) (Ψ q)) = 0
    ·
      have A : ∀ q, 0 ≤ dist (Φ p) (Φ q)+dist (Ψ p) (Ψ q) :=
        fun q =>
          by 
            rw [←add_zeroₓ (0 : ℝ)] <;> exact add_le_add dist_nonneg dist_nonneg 
      refine' le_antisymmₓ _ (le_cinfi A)
      have  : 0 = dist (Φ p) (Φ p)+dist (Ψ p) (Ψ p)
      ·
        simp 
      rw [this]
      exact cinfi_le ⟨0, forall_range_iff.2 A⟩ p 
    rw [glue_dist, this, zero_addₓ]

private theorem glue_dist_comm (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) : ∀ x y, glue_dist Φ Ψ ε x y = glue_dist Φ Ψ ε y x
| inl x, inl y => dist_comm _ _
| inr x, inr y => dist_comm _ _
| inl x, inr y => rfl
| inr x, inl y => rfl

variable [Nonempty Z]

private theorem glue_dist_triangle (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ)
  (H : ∀ p q, |dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)| ≤ 2*ε) :
  ∀ x y z, glue_dist Φ Ψ ε x z ≤ glue_dist Φ Ψ ε x y+glue_dist Φ Ψ ε y z
| inl x, inl y, inl z => dist_triangle _ _ _
| inr x, inr y, inr z => dist_triangle _ _ _
| inr x, inl y, inl z =>
  by 
    have B : ∀ a b, BddBelow (range fun p : Z => dist a (Φ p)+dist b (Ψ p)) :=
      fun a b => ⟨0, forall_range_iff.2 fun p => add_nonneg dist_nonneg dist_nonneg⟩
    unfold glue_dist 
    have  : (⨅ p, dist z (Φ p)+dist x (Ψ p)) ≤ (⨅ p, dist y (Φ p)+dist x (Ψ p))+dist y z
    ·
      have  :
        ((⨅ p, dist y (Φ p)+dist x (Ψ p))+dist y z) = infi ((fun t => t+dist y z) ∘ fun p => dist y (Φ p)+dist x (Ψ p))
      ·
        refine' map_cinfi_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _ (B _ _)
        intro x y hx 
        simpa 
      rw [this, comp]
      refine' cinfi_le_cinfi (B _ _) fun p => _ 
      calc (dist z (Φ p)+dist x (Ψ p)) ≤ (dist y z+dist y (Φ p))+dist x (Ψ p) :=
        add_le_add (dist_triangle_left _ _ _) (le_reflₓ _)_ = (dist y (Φ p)+dist x (Ψ p))+dist y z :=
        by 
          ring 
    linarith
| inr x, inr y, inl z =>
  by 
    have B : ∀ a b, BddBelow (range fun p : Z => dist a (Φ p)+dist b (Ψ p)) :=
      fun a b => ⟨0, forall_range_iff.2 fun p => add_nonneg dist_nonneg dist_nonneg⟩
    unfold glue_dist 
    have  : (⨅ p, dist z (Φ p)+dist x (Ψ p)) ≤ dist x y+⨅ p, dist z (Φ p)+dist y (Ψ p)
    ·
      have  :
        (dist x y+⨅ p, dist z (Φ p)+dist y (Ψ p)) = infi ((fun t => dist x y+t) ∘ fun p => dist z (Φ p)+dist y (Ψ p))
      ·
        refine' map_cinfi_of_continuous_at_of_monotone (continuous_at_const.add continuous_at_id) _ (B _ _)
        intro x y hx 
        simpa 
      rw [this, comp]
      refine' cinfi_le_cinfi (B _ _) fun p => _ 
      calc (dist z (Φ p)+dist x (Ψ p)) ≤ dist z (Φ p)+dist x y+dist y (Ψ p) :=
        add_le_add (le_reflₓ _) (dist_triangle _ _ _)_ = dist x y+dist z (Φ p)+dist y (Ψ p) :=
        by 
          ring 
    linarith
| inl x, inl y, inr z =>
  by 
    have B : ∀ a b, BddBelow (range fun p : Z => dist a (Φ p)+dist b (Ψ p)) :=
      fun a b => ⟨0, forall_range_iff.2 fun p => add_nonneg dist_nonneg dist_nonneg⟩
    unfold glue_dist 
    have  : (⨅ p, dist x (Φ p)+dist z (Ψ p)) ≤ dist x y+⨅ p, dist y (Φ p)+dist z (Ψ p)
    ·
      have  :
        (dist x y+⨅ p, dist y (Φ p)+dist z (Ψ p)) = infi ((fun t => dist x y+t) ∘ fun p => dist y (Φ p)+dist z (Ψ p))
      ·
        refine' map_cinfi_of_continuous_at_of_monotone (continuous_at_const.add continuous_at_id) _ (B _ _)
        intro x y hx 
        simpa 
      rw [this, comp]
      refine' cinfi_le_cinfi (B _ _) fun p => _ 
      calc (dist x (Φ p)+dist z (Ψ p)) ≤ (dist x y+dist y (Φ p))+dist z (Ψ p) :=
        add_le_add (dist_triangle _ _ _) (le_reflₓ _)_ = dist x y+dist y (Φ p)+dist z (Ψ p) :=
        by 
          ring 
    linarith
| inl x, inr y, inr z =>
  by 
    have B : ∀ a b, BddBelow (range fun p : Z => dist a (Φ p)+dist b (Ψ p)) :=
      fun a b => ⟨0, forall_range_iff.2 fun p => add_nonneg dist_nonneg dist_nonneg⟩
    unfold glue_dist 
    have  : (⨅ p, dist x (Φ p)+dist z (Ψ p)) ≤ (⨅ p, dist x (Φ p)+dist y (Ψ p))+dist y z
    ·
      have  :
        ((⨅ p, dist x (Φ p)+dist y (Ψ p))+dist y z) = infi ((fun t => t+dist y z) ∘ fun p => dist x (Φ p)+dist y (Ψ p))
      ·
        refine' map_cinfi_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _ (B _ _)
        intro x y hx 
        simpa 
      rw [this, comp]
      refine' cinfi_le_cinfi (B _ _) fun p => _ 
      calc (dist x (Φ p)+dist z (Ψ p)) ≤ dist x (Φ p)+dist y z+dist y (Ψ p) :=
        add_le_add (le_reflₓ _) (dist_triangle_left _ _ _)_ = (dist x (Φ p)+dist y (Ψ p))+dist y z :=
        by 
          ring 
    linarith
| inl x, inr y, inl z =>
  le_of_forall_pos_le_add$
    fun δ δpos =>
      by 
        obtain ⟨p, hp⟩ : ∃ p, (dist x (Φ p)+dist y (Ψ p)) < (⨅ p, dist x (Φ p)+dist y (Ψ p))+δ / 2 
        exact
          exists_lt_of_cinfi_lt
            (by 
              linarith)
        obtain ⟨q, hq⟩ : ∃ q, (dist z (Φ q)+dist y (Ψ q)) < (⨅ p, dist z (Φ p)+dist y (Ψ p))+δ / 2 
        exact
          exists_lt_of_cinfi_lt
            (by 
              linarith)
        have  : dist (Φ p) (Φ q) ≤ dist (Ψ p) (Ψ q)+2*ε
        ·
          have  := le_transₓ (le_abs_self _) (H p q)
          ·
            linarith 
        calc dist x z ≤ (dist x (Φ p)+dist (Φ p) (Φ q))+dist (Φ q) z :=
          dist_triangle4 _ _ _ _ _ ≤ ((dist x (Φ p)+dist (Ψ p) (Ψ q))+dist z (Φ q))+2*ε :=
          by 
            rw [dist_comm z] <;> linarith _ ≤ ((dist x (Φ p)+dist y (Ψ p)+dist y (Ψ q))+dist z (Φ q))+2*ε :=
          add_le_add (add_le_add (add_le_add (le_reflₓ _) (dist_triangle_left _ _ _)) le_rfl)
            le_rfl _ ≤ (((⨅ p, dist x (Φ p)+dist y (Ψ p))+ε)+(⨅ p, dist z (Φ p)+dist y (Ψ p))+ε)+δ :=
          by 
            linarith
| inr x, inl y, inr z =>
  le_of_forall_pos_le_add$
    fun δ δpos =>
      by 
        obtain ⟨p, hp⟩ : ∃ p, (dist y (Φ p)+dist x (Ψ p)) < (⨅ p, dist y (Φ p)+dist x (Ψ p))+δ / 2 
        exact
          exists_lt_of_cinfi_lt
            (by 
              linarith)
        obtain ⟨q, hq⟩ : ∃ q, (dist y (Φ q)+dist z (Ψ q)) < (⨅ p, dist y (Φ p)+dist z (Ψ p))+δ / 2 
        exact
          exists_lt_of_cinfi_lt
            (by 
              linarith)
        have  : dist (Ψ p) (Ψ q) ≤ dist (Φ p) (Φ q)+2*ε
        ·
          have  := le_transₓ (neg_le_abs_self _) (H p q)
          ·
            linarith 
        calc dist x z ≤ (dist x (Ψ p)+dist (Ψ p) (Ψ q))+dist (Ψ q) z :=
          dist_triangle4 _ _ _ _ _ ≤ ((dist x (Ψ p)+dist (Φ p) (Φ q))+dist z (Ψ q))+2*ε :=
          by 
            rw [dist_comm z] <;> linarith _ ≤ ((dist x (Ψ p)+dist y (Φ p)+dist y (Φ q))+dist z (Ψ q))+2*ε :=
          add_le_add (add_le_add (add_le_add le_rfl (dist_triangle_left _ _ _)) le_rfl)
            le_rfl _ ≤ (((⨅ p, dist y (Φ p)+dist x (Ψ p))+ε)+(⨅ p, dist y (Φ p)+dist z (Ψ p))+ε)+δ :=
          by 
            linarith

private theorem glue_eq_of_dist_eq_zero (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (ε0 : 0 < ε) :
  ∀ p q : Sum X Y, glue_dist Φ Ψ ε p q = 0 → p = q
| inl x, inl y, h =>
  by 
    rw [eq_of_dist_eq_zero h]
| inl x, inr y, h =>
  by 
    have  : 0 ≤ ⨅ p, dist x (Φ p)+dist y (Ψ p) :=
      le_cinfi
        fun p =>
          by 
            simpa using add_le_add (@dist_nonneg _ _ x _) (@dist_nonneg _ _ y _)
    have  : (0+ε) ≤ glue_dist Φ Ψ ε (inl x) (inr y) := add_le_add this (le_reflₓ ε)
    exfalso 
    linarith
| inr x, inl y, h =>
  by 
    have  : 0 ≤ ⨅ p, dist y (Φ p)+dist x (Ψ p) :=
      le_cinfi
        fun p =>
          by 
            simpa [add_commₓ] using add_le_add (@dist_nonneg _ _ x _) (@dist_nonneg _ _ y _)
    have  : (0+ε) ≤ glue_dist Φ Ψ ε (inr x) (inl y) := add_le_add this (le_reflₓ ε)
    exfalso 
    linarith
| inr x, inr y, h =>
  by 
    rw [eq_of_dist_eq_zero h]

/-- Given two maps `Φ` and `Ψ` intro metric spaces `X` and `Y` such that the distances between
`Φ p` and `Φ q`, and between `Ψ p` and `Ψ q`, coincide up to `2 ε` where `ε > 0`, one can almost
glue the two spaces `X` and `Y` along the images of `Φ` and `Ψ`, so that `Φ p` and `Ψ p` are
at distance `ε`. -/
def glue_metric_approx (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (ε0 : 0 < ε)
  (H : ∀ p q, |dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)| ≤ 2*ε) : MetricSpace (Sum X Y) :=
  { dist := glue_dist Φ Ψ ε, dist_self := glue_dist_self Φ Ψ ε, dist_comm := glue_dist_comm Φ Ψ ε,
    dist_triangle := glue_dist_triangle Φ Ψ ε H, eq_of_dist_eq_zero := glue_eq_of_dist_eq_zero Φ Ψ ε ε0 }

end ApproxGluing

section Sum

variable {X : Type u} {Y : Type v} {Z : Type w}

variable [MetricSpace X] [MetricSpace Y] [Inhabited X] [Inhabited Y]

open sum(inl inr)

/-- Distance on a disjoint union. There are many (noncanonical) ways to put a distance compatible
with each factor.
If the two spaces are bounded, one can say for instance that each point in the first is at distance
`diam X + diam Y + 1` of each point in the second.
Instead, we choose a construction that works for unbounded spaces, but requires basepoints.
We embed isometrically each factor, set the basepoints at distance 1,
arbitrarily, and say that the distance from `a` to `b` is the sum of the distances of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance by default. -/
def sum.dist : Sum X Y → Sum X Y → ℝ
| inl a, inl a' => dist a a'
| inr b, inr b' => dist b b'
| inl a, inr b => (dist a (default X)+1)+dist (default Y) b
| inr b, inl a => (dist b (default Y)+1)+dist (default X) a

theorem sum.dist_eq_glue_dist {p q : Sum X Y} :
  sum.dist p q = glue_dist (fun _ : Unit => default X) (fun _ : Unit => default Y) 1 p q :=
  by 
    cases p <;>
      cases q <;>
        first |
          rfl|
          simp [sum.dist, glue_dist, dist_comm, add_commₓ, add_left_commₓ]

private theorem sum.dist_comm (x y : Sum X Y) : sum.dist x y = sum.dist y x :=
  by 
    cases x <;> cases y <;> simp only [sum.dist, dist_comm, add_commₓ, add_left_commₓ]

theorem sum.one_dist_le {x : X} {y : Y} : 1 ≤ sum.dist (inl x) (inr y) :=
  le_transₓ (le_add_of_nonneg_right dist_nonneg)$ add_le_add_right (le_add_of_nonneg_left dist_nonneg) _

theorem sum.one_dist_le' {x : X} {y : Y} : 1 ≤ sum.dist (inr y) (inl x) :=
  by 
    rw [sum.dist_comm] <;> exact sum.one_dist_le

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (ε «expr > » 0)
private theorem sum.mem_uniformity (s : Set (Sum X Y × Sum X Y)) :
  s ∈ 𝓤 (Sum X Y) ↔ ∃ (ε : _)(_ : ε > 0), ∀ a b, sum.dist a b < ε → (a, b) ∈ s :=
  by 
    constructor
    ·
      rintro ⟨hsX, hsY⟩
      rcases mem_uniformity_dist.1 hsX with ⟨εX, εX0, hX⟩
      rcases mem_uniformity_dist.1 hsY with ⟨εY, εY0, hY⟩
      refine' ⟨min (min εX εY) 1, lt_minₓ (lt_minₓ εX0 εY0) zero_lt_one, _⟩
      rintro (a | a) (b | b) h
      ·
        exact hX (lt_of_lt_of_leₓ h (le_transₓ (min_le_leftₓ _ _) (min_le_leftₓ _ _)))
      ·
        cases not_le_of_lt (lt_of_lt_of_leₓ h (min_le_rightₓ _ _)) sum.one_dist_le
      ·
        cases not_le_of_lt (lt_of_lt_of_leₓ h (min_le_rightₓ _ _)) sum.one_dist_le'
      ·
        exact hY (lt_of_lt_of_leₓ h (le_transₓ (min_le_leftₓ _ _) (min_le_rightₓ _ _)))
    ·
      rintro ⟨ε, ε0, H⟩
      constructor <;>
        rw [Filter.mem_sets, Filter.mem_map, mem_uniformity_dist] <;>
          exact
            ⟨ε, ε0,
              fun x y h =>
                H _ _
                  (by 
                    exact h)⟩

/-- The distance on the disjoint union indeed defines a metric space. All the distance properties
follow from our choice of the distance. The harder work is to show that the uniform structure
defined by the distance coincides with the disjoint union uniform structure. -/
def metric_space_sum : MetricSpace (Sum X Y) :=
  { dist := sum.dist,
    dist_self :=
      fun x =>
        by 
          cases x <;> simp only [sum.dist, dist_self],
    dist_comm := sum.dist_comm,
    dist_triangle :=
      fun p q r =>
        by 
          simp only [dist, sum.dist_eq_glue_dist] <;>
            exact
              glue_dist_triangle _ _ _
                (by 
                  normNum)
                _ _ _,
    eq_of_dist_eq_zero :=
      fun p q =>
        by 
          simp only [dist, sum.dist_eq_glue_dist] <;> exact glue_eq_of_dist_eq_zero _ _ _ zero_lt_one _ _,
    toUniformSpace := Sum.uniformSpace, uniformity_dist := uniformity_dist_of_mem_uniformity _ _ sum.mem_uniformity }

attribute [local instance] metric_space_sum

theorem sum.dist_eq {x y : Sum X Y} : dist x y = sum.dist x y :=
  rfl

/-- The left injection of a space in a disjoint union in an isometry -/
theorem isometry_on_inl : Isometry (Sum.inl : X → Sum X Y) :=
  isometry_emetric_iff_metric.2$ fun x y => rfl

/-- The right injection of a space in a disjoint union in an isometry -/
theorem isometry_on_inr : Isometry (Sum.inr : Y → Sum X Y) :=
  isometry_emetric_iff_metric.2$ fun x y => rfl

end Sum

section Gluing

variable {X : Type u} {Y : Type v} {Z : Type w}

variable [Nonempty Z] [MetricSpace Z] [MetricSpace X] [MetricSpace Y] {Φ : Z → X} {Ψ : Z → Y} {ε : ℝ}

open _root_.sum(inl inr)

attribute [local instance] PseudoMetric.distSetoid

/-- Given two isometric embeddings `Φ : Z → X` and `Ψ : Z → Y`, we define a pseudo metric space
structure on `X ⊕ Y` by declaring that `Φ x` and `Ψ x` are at distance `0`. -/
def glue_premetric (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : PseudoMetricSpace (Sum X Y) :=
  { dist := glue_dist Φ Ψ 0, dist_self := glue_dist_self Φ Ψ 0, dist_comm := glue_dist_comm Φ Ψ 0,
    dist_triangle :=
      glue_dist_triangle Φ Ψ 0$
        fun p q =>
          by 
            rw [hΦ.dist_eq, hΨ.dist_eq] <;> simp  }

/-- Given two isometric embeddings `Φ : Z → X` and `Ψ : Z → Y`, we define a
space  `glue_space hΦ hΨ` by identifying in `X ⊕ Y` the points `Φ x` and `Ψ x`. -/
def glue_space (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Type _ :=
  @PseudoMetricQuot _ (glue_premetric hΦ hΨ)

instance metric_space_glue_space (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : MetricSpace (glue_space hΦ hΨ) :=
  @metricSpaceQuot _ (glue_premetric hΦ hΨ)

/-- The canonical map from `X` to the space obtained by gluing isometric subsets in `X` and `Y`. -/
def to_glue_l (hΦ : Isometry Φ) (hΨ : Isometry Ψ) (x : X) : glue_space hΦ hΨ :=
  by 
    let this' : PseudoMetricSpace (Sum X Y) := glue_premetric hΦ hΨ <;> exact ⟦inl x⟧

/-- The canonical map from `Y` to the space obtained by gluing isometric subsets in `X` and `Y`. -/
def to_glue_r (hΦ : Isometry Φ) (hΨ : Isometry Ψ) (y : Y) : glue_space hΦ hΨ :=
  by 
    let this' : PseudoMetricSpace (Sum X Y) := glue_premetric hΦ hΨ <;> exact ⟦inr y⟧

instance inhabited_left (hΦ : Isometry Φ) (hΨ : Isometry Ψ) [Inhabited X] : Inhabited (glue_space hΦ hΨ) :=
  ⟨to_glue_l _ _ (default _)⟩

instance inhabited_right (hΦ : Isometry Φ) (hΨ : Isometry Ψ) [Inhabited Y] : Inhabited (glue_space hΦ hΨ) :=
  ⟨to_glue_r _ _ (default _)⟩

theorem to_glue_commute (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : (to_glue_l hΦ hΨ ∘ Φ) = (to_glue_r hΦ hΨ ∘ Ψ) :=
  by 
    let this' : PseudoMetricSpace (Sum X Y) := glue_premetric hΦ hΨ 
    funext 
    simp only [comp, to_glue_l, to_glue_r, Quotientₓ.eq]
    exact glue_dist_glued_points Φ Ψ 0 x

theorem to_glue_l_isometry (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Isometry (to_glue_l hΦ hΨ) :=
  isometry_emetric_iff_metric.2$ fun _ _ => rfl

theorem to_glue_r_isometry (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Isometry (to_glue_r hΦ hΨ) :=
  isometry_emetric_iff_metric.2$ fun _ _ => rfl

end Gluing

section InductiveLimit

open Nat

variable {X : ℕ → Type u} [∀ n, MetricSpace (X n)] {f : ∀ n, X n → X (n+1)}

/-- Predistance on the disjoint union `Σ n, X n`. -/
def inductive_limit_dist (f : ∀ n, X n → X (n+1)) (x y : Σ n, X n) : ℝ :=
  dist (le_rec_on (le_max_leftₓ x.1 y.1) f x.2 : X (max x.1 y.1))
    (le_rec_on (le_max_rightₓ x.1 y.1) f y.2 : X (max x.1 y.1))

/-- The predistance on the disjoint union `Σ n, X n` can be computed in any `X k` for large
enough `k`. -/
theorem inductive_limit_dist_eq_dist (I : ∀ n, Isometry (f n)) (x y : Σ n, X n) (m : ℕ) :
  ∀ hx : x.1 ≤ m,
    ∀ hy : y.1 ≤ m, inductive_limit_dist f x y = dist (le_rec_on hx f x.2 : X m) (le_rec_on hy f y.2 : X m) :=
  by 
    induction' m with m hm
    ·
      intro hx hy 
      have A : max x.1 y.1 = 0
      ·
        rw [nonpos_iff_eq_zero.1 hx, nonpos_iff_eq_zero.1 hy]
        simp 
      unfold inductive_limit_dist 
      congr <;> simp only [A]
    ·
      intro hx hy 
      byCases' h : max x.1 y.1 = m.succ
      ·
        unfold inductive_limit_dist 
        congr <;> simp only [h]
      ·
        have  : max x.1 y.1 ≤ succ m :=
          by 
            simp [hx, hy]
        have  : max x.1 y.1 ≤ m :=
          by 
            simpa [h] using of_le_succ this 
        have xm : x.1 ≤ m := le_transₓ (le_max_leftₓ _ _) this 
        have ym : y.1 ≤ m := le_transₓ (le_max_rightₓ _ _) this 
        rw [le_rec_on_succ xm, le_rec_on_succ ym, (I m).dist_eq]
        exact hm xm ym

/-- Premetric space structure on `Σ n, X n`.-/
def inductive_premetric (I : ∀ n, Isometry (f n)) : PseudoMetricSpace (Σ n, X n) :=
  { dist := inductive_limit_dist f,
    dist_self :=
      fun x =>
        by 
          simp [dist, inductive_limit_dist],
    dist_comm :=
      fun x y =>
        by 
          let m := max x.1 y.1
          have hx : x.1 ≤ m := le_max_leftₓ _ _ 
          have hy : y.1 ≤ m := le_max_rightₓ _ _ 
          unfold dist 
          rw [inductive_limit_dist_eq_dist I x y m hx hy, inductive_limit_dist_eq_dist I y x m hy hx, dist_comm],
    dist_triangle :=
      fun x y z =>
        by 
          let m := max (max x.1 y.1) z.1
          have hx : x.1 ≤ m := le_transₓ (le_max_leftₓ _ _) (le_max_leftₓ _ _)
          have hy : y.1 ≤ m := le_transₓ (le_max_rightₓ _ _) (le_max_leftₓ _ _)
          have hz : z.1 ≤ m := le_max_rightₓ _ _ 
          calc inductive_limit_dist f x z = dist (le_rec_on hx f x.2 : X m) (le_rec_on hz f z.2 : X m) :=
            inductive_limit_dist_eq_dist I x z m hx
              hz
                _ ≤
              dist (le_rec_on hx f x.2 : X m)
                  (le_rec_on hy f y.2 : X m)+dist (le_rec_on hy f y.2 : X m) (le_rec_on hz f z.2 : X m) :=
            dist_triangle _ _ _ _ = inductive_limit_dist f x y+inductive_limit_dist f y z :=
            by 
              rw [inductive_limit_dist_eq_dist I x y m hx hy, inductive_limit_dist_eq_dist I y z m hy hz] }

attribute [local instance] inductive_premetric PseudoMetric.distSetoid

/-- The type giving the inductive limit in a metric space context. -/
def inductive_limit (I : ∀ n, Isometry (f n)) : Type _ :=
  @PseudoMetricQuot _ (inductive_premetric I)

/-- Metric space structure on the inductive limit. -/
instance metric_space_inductive_limit (I : ∀ n, Isometry (f n)) : MetricSpace (inductive_limit I) :=
  @metricSpaceQuot _ (inductive_premetric I)

/-- Mapping each `X n` to the inductive limit. -/
def to_inductive_limit (I : ∀ n, Isometry (f n)) (n : ℕ) (x : X n) : Metric.InductiveLimit I :=
  by 
    let this' : PseudoMetricSpace (Σ n, X n) := inductive_premetric I <;> exact ⟦Sigma.mk n x⟧

instance (I : ∀ n, Isometry (f n)) [Inhabited (X 0)] : Inhabited (inductive_limit I) :=
  ⟨to_inductive_limit _ 0 (default _)⟩

/-- The map `to_inductive_limit n` mapping `X n` to the inductive limit is an isometry. -/
theorem to_inductive_limit_isometry (I : ∀ n, Isometry (f n)) (n : ℕ) : Isometry (to_inductive_limit I n) :=
  isometry_emetric_iff_metric.2$
    fun x y =>
      by 
        change inductive_limit_dist f ⟨n, x⟩ ⟨n, y⟩ = dist x y 
        rw [inductive_limit_dist_eq_dist I ⟨n, x⟩ ⟨n, y⟩ n (le_reflₓ n) (le_reflₓ n), le_rec_on_self, le_rec_on_self]

/-- The maps `to_inductive_limit n` are compatible with the maps `f n`. -/
theorem to_inductive_limit_commute (I : ∀ n, Isometry (f n)) (n : ℕ) :
  (to_inductive_limit I n.succ ∘ f n) = to_inductive_limit I n :=
  by 
    funext 
    simp only [comp, to_inductive_limit, Quotientₓ.eq]
    show inductive_limit_dist f ⟨n.succ, f n x⟩ ⟨n, x⟩ = 0
    ·
      rw [inductive_limit_dist_eq_dist I ⟨n.succ, f n x⟩ ⟨n, x⟩ n.succ, le_rec_on_self, le_rec_on_succ, le_rec_on_self,
        dist_self]
      exact le_reflₓ _ 
      exact le_reflₓ _ 
      exact le_succ _

end InductiveLimit

end Metric

