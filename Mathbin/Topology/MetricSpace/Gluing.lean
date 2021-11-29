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


noncomputable theory

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
| inl x, inr y => (⨅p, dist x (Φ p)+dist y (Ψ p))+ε
| inr x, inl y => (⨅p, dist y (Φ p)+dist x (Ψ p))+ε

private theorem glue_dist_self (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) : ∀ x, glue_dist Φ Ψ ε x x = 0
| inl x => dist_self _
| inr x => dist_self _

-- error in Topology.MetricSpace.Gluing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem glue_dist_glued_points
[nonempty Z]
(Φ : Z → X)
(Ψ : Z → Y)
(ε : exprℝ())
(p : Z) : «expr = »(glue_dist Φ Ψ ε (inl (Φ p)) (inr (Ψ p)), ε) :=
begin
  have [] [":", expr «expr = »(«expr⨅ , »((q), «expr + »(dist (Φ p) (Φ q), dist (Ψ p) (Ψ q))), 0)] [],
  { have [ident A] [":", expr ∀
     q, «expr ≤ »(0, «expr + »(dist (Φ p) (Φ q), dist (Ψ p) (Ψ q)))] [":=", expr λ
     q, by rw ["<-", expr add_zero (0 : exprℝ())] []; exact [expr add_le_add dist_nonneg dist_nonneg]],
    refine [expr le_antisymm _ (le_cinfi A)],
    have [] [":", expr «expr = »(0, «expr + »(dist (Φ p) (Φ p), dist (Ψ p) (Ψ p)))] [],
    by simp [] [] [] [] [] [],
    rw [expr this] [],
    exact [expr cinfi_le ⟨0, forall_range_iff.2 A⟩ p] },
  rw ["[", expr glue_dist, ",", expr this, ",", expr zero_add, "]"] []
end

private theorem glue_dist_comm (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) : ∀ x y, glue_dist Φ Ψ ε x y = glue_dist Φ Ψ ε y x
| inl x, inl y => dist_comm _ _
| inr x, inr y => dist_comm _ _
| inl x, inr y => rfl
| inr x, inl y => rfl

variable [Nonempty Z]

-- error in Topology.MetricSpace.Gluing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem glue_dist_triangle
(Φ : Z → X)
(Ψ : Z → Y)
(ε : exprℝ())
(H : ∀
 p
 q, «expr ≤ »(«expr| |»(«expr - »(dist (Φ p) (Φ q), dist (Ψ p) (Ψ q))), «expr * »(2, ε))) : ∀
x y z, «expr ≤ »(glue_dist Φ Ψ ε x z, «expr + »(glue_dist Φ Ψ ε x y, glue_dist Φ Ψ ε y z))
| inl x, inl y, inl z := dist_triangle _ _ _
| inr x, inr y, inr z := dist_triangle _ _ _
| inr x, inl y, inl z := begin
  have [ident B] [":", expr ∀
   a
   b, bdd_below (range (λ
     p : Z, «expr + »(dist a (Φ p), dist b (Ψ p))))] [":=", expr λ
   a b, ⟨0, forall_range_iff.2 (λ p, add_nonneg dist_nonneg dist_nonneg)⟩],
  unfold [ident glue_dist] [],
  have [] [":", expr «expr ≤ »(«expr⨅ , »((p), «expr + »(dist z (Φ p), dist x (Ψ p))), «expr + »(«expr⨅ , »((p), «expr + »(dist y (Φ p), dist x (Ψ p))), dist y z))] [],
  { have [] [":", expr «expr = »(«expr + »(«expr⨅ , »((p), «expr + »(dist y (Φ p), dist x (Ψ p))), dist y z), infi «expr ∘ »(λ
       t, «expr + »(t, dist y z), λ p, «expr + »(dist y (Φ p), dist x (Ψ p))))] [],
    { refine [expr map_cinfi_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _ (B _ _)],
      intros [ident x, ident y, ident hx],
      simpa [] [] [] [] [] [] },
    rw ["[", expr this, ",", expr comp, "]"] [],
    refine [expr cinfi_le_cinfi (B _ _) (λ p, _)],
    calc
      «expr ≤ »(«expr + »(dist z (Φ p), dist x (Ψ p)), «expr + »(«expr + »(dist y z, dist y (Φ p)), dist x (Ψ p))) : add_le_add (dist_triangle_left _ _ _) (le_refl _)
      «expr = »(..., «expr + »(«expr + »(dist y (Φ p), dist x (Ψ p)), dist y z)) : by ring [] },
  linarith [] [] []
end
| inr x, inr y, inl z := begin
  have [ident B] [":", expr ∀
   a
   b, bdd_below (range (λ
     p : Z, «expr + »(dist a (Φ p), dist b (Ψ p))))] [":=", expr λ
   a b, ⟨0, forall_range_iff.2 (λ p, add_nonneg dist_nonneg dist_nonneg)⟩],
  unfold [ident glue_dist] [],
  have [] [":", expr «expr ≤ »(«expr⨅ , »((p), «expr + »(dist z (Φ p), dist x (Ψ p))), «expr + »(dist x y, «expr⨅ , »((p), «expr + »(dist z (Φ p), dist y (Ψ p)))))] [],
  { have [] [":", expr «expr = »(«expr + »(dist x y, «expr⨅ , »((p), «expr + »(dist z (Φ p), dist y (Ψ p)))), infi «expr ∘ »(λ
       t, «expr + »(dist x y, t), λ p, «expr + »(dist z (Φ p), dist y (Ψ p))))] [],
    { refine [expr map_cinfi_of_continuous_at_of_monotone (continuous_at_const.add continuous_at_id) _ (B _ _)],
      intros [ident x, ident y, ident hx],
      simpa [] [] [] [] [] [] },
    rw ["[", expr this, ",", expr comp, "]"] [],
    refine [expr cinfi_le_cinfi (B _ _) (λ p, _)],
    calc
      «expr ≤ »(«expr + »(dist z (Φ p), dist x (Ψ p)), «expr + »(dist z (Φ p), «expr + »(dist x y, dist y (Ψ p)))) : add_le_add (le_refl _) (dist_triangle _ _ _)
      «expr = »(..., «expr + »(dist x y, «expr + »(dist z (Φ p), dist y (Ψ p)))) : by ring [] },
  linarith [] [] []
end
| inl x, inl y, inr z := begin
  have [ident B] [":", expr ∀
   a
   b, bdd_below (range (λ
     p : Z, «expr + »(dist a (Φ p), dist b (Ψ p))))] [":=", expr λ
   a b, ⟨0, forall_range_iff.2 (λ p, add_nonneg dist_nonneg dist_nonneg)⟩],
  unfold [ident glue_dist] [],
  have [] [":", expr «expr ≤ »(«expr⨅ , »((p), «expr + »(dist x (Φ p), dist z (Ψ p))), «expr + »(dist x y, «expr⨅ , »((p), «expr + »(dist y (Φ p), dist z (Ψ p)))))] [],
  { have [] [":", expr «expr = »(«expr + »(dist x y, «expr⨅ , »((p), «expr + »(dist y (Φ p), dist z (Ψ p)))), infi «expr ∘ »(λ
       t, «expr + »(dist x y, t), λ p, «expr + »(dist y (Φ p), dist z (Ψ p))))] [],
    { refine [expr map_cinfi_of_continuous_at_of_monotone (continuous_at_const.add continuous_at_id) _ (B _ _)],
      intros [ident x, ident y, ident hx],
      simpa [] [] [] [] [] [] },
    rw ["[", expr this, ",", expr comp, "]"] [],
    refine [expr cinfi_le_cinfi (B _ _) (λ p, _)],
    calc
      «expr ≤ »(«expr + »(dist x (Φ p), dist z (Ψ p)), «expr + »(«expr + »(dist x y, dist y (Φ p)), dist z (Ψ p))) : add_le_add (dist_triangle _ _ _) (le_refl _)
      «expr = »(..., «expr + »(dist x y, «expr + »(dist y (Φ p), dist z (Ψ p)))) : by ring [] },
  linarith [] [] []
end
| inl x, inr y, inr z := begin
  have [ident B] [":", expr ∀
   a
   b, bdd_below (range (λ
     p : Z, «expr + »(dist a (Φ p), dist b (Ψ p))))] [":=", expr λ
   a b, ⟨0, forall_range_iff.2 (λ p, add_nonneg dist_nonneg dist_nonneg)⟩],
  unfold [ident glue_dist] [],
  have [] [":", expr «expr ≤ »(«expr⨅ , »((p), «expr + »(dist x (Φ p), dist z (Ψ p))), «expr + »(«expr⨅ , »((p), «expr + »(dist x (Φ p), dist y (Ψ p))), dist y z))] [],
  { have [] [":", expr «expr = »(«expr + »(«expr⨅ , »((p), «expr + »(dist x (Φ p), dist y (Ψ p))), dist y z), infi «expr ∘ »(λ
       t, «expr + »(t, dist y z), λ p, «expr + »(dist x (Φ p), dist y (Ψ p))))] [],
    { refine [expr map_cinfi_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _ (B _ _)],
      intros [ident x, ident y, ident hx],
      simpa [] [] [] [] [] [] },
    rw ["[", expr this, ",", expr comp, "]"] [],
    refine [expr cinfi_le_cinfi (B _ _) (λ p, _)],
    calc
      «expr ≤ »(«expr + »(dist x (Φ p), dist z (Ψ p)), «expr + »(dist x (Φ p), «expr + »(dist y z, dist y (Ψ p)))) : add_le_add (le_refl _) (dist_triangle_left _ _ _)
      «expr = »(..., «expr + »(«expr + »(dist x (Φ p), dist y (Ψ p)), dist y z)) : by ring [] },
  linarith [] [] []
end
| inl x, inr y, inl z := «expr $ »(le_of_forall_pos_le_add, λ δ δpos, begin
   obtain ["⟨", ident p, ",", ident hp, "⟩", ":", expr «expr∃ , »((p), «expr < »(«expr + »(dist x (Φ p), dist y (Ψ p)), «expr + »(«expr⨅ , »((p), «expr + »(dist x (Φ p), dist y (Ψ p))), «expr / »(δ, 2))))],
   from [expr exists_lt_of_cinfi_lt (by linarith [] [] [])],
   obtain ["⟨", ident q, ",", ident hq, "⟩", ":", expr «expr∃ , »((q), «expr < »(«expr + »(dist z (Φ q), dist y (Ψ q)), «expr + »(«expr⨅ , »((p), «expr + »(dist z (Φ p), dist y (Ψ p))), «expr / »(δ, 2))))],
   from [expr exists_lt_of_cinfi_lt (by linarith [] [] [])],
   have [] [":", expr «expr ≤ »(dist (Φ p) (Φ q), «expr + »(dist (Ψ p) (Ψ q), «expr * »(2, ε)))] [],
   { have [] [] [":=", expr le_trans (le_abs_self _) (H p q)],
     by linarith [] [] [] },
   calc
     «expr ≤ »(dist x z, «expr + »(«expr + »(dist x (Φ p), dist (Φ p) (Φ q)), dist (Φ q) z)) : dist_triangle4 _ _ _ _
     «expr ≤ »(..., «expr + »(«expr + »(«expr + »(dist x (Φ p), dist (Ψ p) (Ψ q)), dist z (Φ q)), «expr * »(2, ε))) : by rw ["[", expr dist_comm z, "]"] []; linarith [] [] []
     «expr ≤ »(..., «expr + »(«expr + »(«expr + »(dist x (Φ p), «expr + »(dist y (Ψ p), dist y (Ψ q))), dist z (Φ q)), «expr * »(2, ε))) : add_le_add (add_le_add (add_le_add (le_refl _) (dist_triangle_left _ _ _)) le_rfl) le_rfl
     «expr ≤ »(..., «expr + »(«expr + »(«expr + »(«expr⨅ , »((p), «expr + »(dist x (Φ p), dist y (Ψ p))), ε), «expr + »(«expr⨅ , »((p), «expr + »(dist z (Φ p), dist y (Ψ p))), ε)), δ)) : by linarith [] [] []
 end)
| inr x, inl y, inr z := «expr $ »(le_of_forall_pos_le_add, λ δ δpos, begin
   obtain ["⟨", ident p, ",", ident hp, "⟩", ":", expr «expr∃ , »((p), «expr < »(«expr + »(dist y (Φ p), dist x (Ψ p)), «expr + »(«expr⨅ , »((p), «expr + »(dist y (Φ p), dist x (Ψ p))), «expr / »(δ, 2))))],
   from [expr exists_lt_of_cinfi_lt (by linarith [] [] [])],
   obtain ["⟨", ident q, ",", ident hq, "⟩", ":", expr «expr∃ , »((q), «expr < »(«expr + »(dist y (Φ q), dist z (Ψ q)), «expr + »(«expr⨅ , »((p), «expr + »(dist y (Φ p), dist z (Ψ p))), «expr / »(δ, 2))))],
   from [expr exists_lt_of_cinfi_lt (by linarith [] [] [])],
   have [] [":", expr «expr ≤ »(dist (Ψ p) (Ψ q), «expr + »(dist (Φ p) (Φ q), «expr * »(2, ε)))] [],
   { have [] [] [":=", expr le_trans (neg_le_abs_self _) (H p q)],
     by linarith [] [] [] },
   calc
     «expr ≤ »(dist x z, «expr + »(«expr + »(dist x (Ψ p), dist (Ψ p) (Ψ q)), dist (Ψ q) z)) : dist_triangle4 _ _ _ _
     «expr ≤ »(..., «expr + »(«expr + »(«expr + »(dist x (Ψ p), dist (Φ p) (Φ q)), dist z (Ψ q)), «expr * »(2, ε))) : by rw ["[", expr dist_comm z, "]"] []; linarith [] [] []
     «expr ≤ »(..., «expr + »(«expr + »(«expr + »(dist x (Ψ p), «expr + »(dist y (Φ p), dist y (Φ q))), dist z (Ψ q)), «expr * »(2, ε))) : add_le_add (add_le_add (add_le_add le_rfl (dist_triangle_left _ _ _)) le_rfl) le_rfl
     «expr ≤ »(..., «expr + »(«expr + »(«expr + »(«expr⨅ , »((p), «expr + »(dist y (Φ p), dist x (Ψ p))), ε), «expr + »(«expr⨅ , »((p), «expr + »(dist y (Φ p), dist z (Ψ p))), ε)), δ)) : by linarith [] [] []
 end)

-- error in Topology.MetricSpace.Gluing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem glue_eq_of_dist_eq_zero
(Φ : Z → X)
(Ψ : Z → Y)
(ε : exprℝ())
(ε0 : «expr < »(0, ε)) : ∀ p q : «expr ⊕ »(X, Y), «expr = »(glue_dist Φ Ψ ε p q, 0) → «expr = »(p, q)
| inl x, inl y, h := by rw [expr eq_of_dist_eq_zero h] []
| inl x, inr y, h := begin
  have [] [":", expr «expr ≤ »(0, «expr⨅ , »((p), «expr + »(dist x (Φ p), dist y (Ψ p))))] [":=", expr le_cinfi (λ
    p, by simpa [] [] [] [] [] ["using", expr add_le_add (@dist_nonneg _ _ x _) (@dist_nonneg _ _ y _)])],
  have [] [":", expr «expr ≤ »(«expr + »(0, ε), glue_dist Φ Ψ ε (inl x) (inr y))] [":=", expr add_le_add this (le_refl ε)],
  exfalso,
  linarith [] [] []
end
| inr x, inl y, h := begin
  have [] [":", expr «expr ≤ »(0, «expr⨅ , »((p), «expr + »(dist y (Φ p), dist x (Ψ p))))] [":=", expr le_cinfi (λ
    p, by simpa [] [] [] ["[", expr add_comm, "]"] [] ["using", expr add_le_add (@dist_nonneg _ _ x _) (@dist_nonneg _ _ y _)])],
  have [] [":", expr «expr ≤ »(«expr + »(0, ε), glue_dist Φ Ψ ε (inr x) (inl y))] [":=", expr add_le_add this (le_refl ε)],
  exfalso,
  linarith [] [] []
end
| inr x, inr y, h := by rw [expr eq_of_dist_eq_zero h] []

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

private theorem sum.mem_uniformity (s : Set (Sum X Y × Sum X Y)) :
  s ∈ 𝓤 (Sum X Y) ↔ ∃ (ε : _)(_ : ε > 0), ∀ a b, sum.dist a b < ε → (a, b) ∈ s :=
  by 
    split 
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
      split  <;>
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

-- error in Topology.MetricSpace.Gluing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The canonical map from `X` to the space obtained by gluing isometric subsets in `X` and `Y`. -/
def to_glue_l (hΦ : isometry Φ) (hΨ : isometry Ψ) (x : X) : glue_space hΦ hΨ :=
by letI [] [":", expr pseudo_metric_space «expr ⊕ »(X, Y)] [":=", expr glue_premetric hΦ hΨ]; exact [expr «expr⟦ ⟧»(inl x)]

-- error in Topology.MetricSpace.Gluing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The canonical map from `Y` to the space obtained by gluing isometric subsets in `X` and `Y`. -/
def to_glue_r (hΦ : isometry Φ) (hΨ : isometry Ψ) (y : Y) : glue_space hΦ hΨ :=
by letI [] [":", expr pseudo_metric_space «expr ⊕ »(X, Y)] [":=", expr glue_premetric hΦ hΨ]; exact [expr «expr⟦ ⟧»(inr y)]

instance inhabited_left (hΦ : Isometry Φ) (hΨ : Isometry Ψ) [Inhabited X] : Inhabited (glue_space hΦ hΨ) :=
  ⟨to_glue_l _ _ (default _)⟩

instance inhabited_right (hΦ : Isometry Φ) (hΨ : Isometry Ψ) [Inhabited Y] : Inhabited (glue_space hΦ hΨ) :=
  ⟨to_glue_r _ _ (default _)⟩

-- error in Topology.MetricSpace.Gluing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem to_glue_commute
(hΦ : isometry Φ)
(hΨ : isometry Ψ) : «expr = »(«expr ∘ »(to_glue_l hΦ hΨ, Φ), «expr ∘ »(to_glue_r hΦ hΨ, Ψ)) :=
begin
  letI [] [":", expr pseudo_metric_space «expr ⊕ »(X, Y)] [":=", expr glue_premetric hΦ hΨ],
  funext [],
  simp [] [] ["only"] ["[", expr comp, ",", expr to_glue_l, ",", expr to_glue_r, ",", expr quotient.eq, "]"] [] [],
  exact [expr glue_dist_glued_points Φ Ψ 0 x]
end

theorem to_glue_l_isometry (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Isometry (to_glue_l hΦ hΨ) :=
  isometry_emetric_iff_metric.2$ fun _ _ => rfl

theorem to_glue_r_isometry (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Isometry (to_glue_r hΦ hΨ) :=
  isometry_emetric_iff_metric.2$ fun _ _ => rfl

end Gluing

section InductiveLimit

open Nat

variable {X : ℕ → Type u} [∀ n, MetricSpace (X n)] {f : ∀ n, X n → X (n+1)}

/-- Predistance on the disjoint union `Σ n, X n`. -/
def inductive_limit_dist (f : ∀ n, X n → X (n+1)) (x y : Σn, X n) : ℝ :=
  dist (le_rec_on (le_max_leftₓ x.1 y.1) f x.2 : X (max x.1 y.1))
    (le_rec_on (le_max_rightₓ x.1 y.1) f y.2 : X (max x.1 y.1))

-- error in Topology.MetricSpace.Gluing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The predistance on the disjoint union `Σ n, X n` can be computed in any `X k` for large
enough `k`. -/
theorem inductive_limit_dist_eq_dist
(I : ∀ n, isometry (f n))
(x y : «exprΣ , »((n), X n))
(m : exprℕ()) : ∀
hx : «expr ≤ »(x.1, m), ∀
hy : «expr ≤ »(y.1, m), «expr = »(inductive_limit_dist f x y, dist (le_rec_on hx f x.2 : X m) (le_rec_on hy f y.2 : X m)) :=
begin
  induction [expr m] [] ["with", ident m, ident hm] [],
  { assume [binders (hx hy)],
    have [ident A] [":", expr «expr = »(max x.1 y.1, 0)] [],
    { rw ["[", expr nonpos_iff_eq_zero.1 hx, ",", expr nonpos_iff_eq_zero.1 hy, "]"] [],
      simp [] [] [] [] [] [] },
    unfold [ident inductive_limit_dist] [],
    congr; simp [] [] ["only"] ["[", expr A, "]"] [] [] },
  { assume [binders (hx hy)],
    by_cases [expr h, ":", expr «expr = »(max x.1 y.1, m.succ)],
    { unfold [ident inductive_limit_dist] [],
      congr; simp [] [] ["only"] ["[", expr h, "]"] [] [] },
    { have [] [":", expr «expr ≤ »(max x.1 y.1, succ m)] [":=", expr by simp [] [] [] ["[", expr hx, ",", expr hy, "]"] [] []],
      have [] [":", expr «expr ≤ »(max x.1 y.1, m)] [":=", expr by simpa [] [] [] ["[", expr h, "]"] [] ["using", expr of_le_succ this]],
      have [ident xm] [":", expr «expr ≤ »(x.1, m)] [":=", expr le_trans (le_max_left _ _) this],
      have [ident ym] [":", expr «expr ≤ »(y.1, m)] [":=", expr le_trans (le_max_right _ _) this],
      rw ["[", expr le_rec_on_succ xm, ",", expr le_rec_on_succ ym, ",", expr (I m).dist_eq, "]"] [],
      exact [expr hm xm ym] } }
end

-- error in Topology.MetricSpace.Gluing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Premetric space structure on `Σ n, X n`.-/
def inductive_premetric (I : ∀ n, isometry (f n)) : pseudo_metric_space «exprΣ , »((n), X n) :=
{ dist := inductive_limit_dist f,
  dist_self := λ x, by simp [] [] [] ["[", expr dist, ",", expr inductive_limit_dist, "]"] [] [],
  dist_comm := λ x y, begin
    let [ident m] [] [":=", expr max x.1 y.1],
    have [ident hx] [":", expr «expr ≤ »(x.1, m)] [":=", expr le_max_left _ _],
    have [ident hy] [":", expr «expr ≤ »(y.1, m)] [":=", expr le_max_right _ _],
    unfold [ident dist] [],
    rw ["[", expr inductive_limit_dist_eq_dist I x y m hx hy, ",", expr inductive_limit_dist_eq_dist I y x m hy hx, ",", expr dist_comm, "]"] []
  end,
  dist_triangle := λ x y z, begin
    let [ident m] [] [":=", expr max (max x.1 y.1) z.1],
    have [ident hx] [":", expr «expr ≤ »(x.1, m)] [":=", expr le_trans (le_max_left _ _) (le_max_left _ _)],
    have [ident hy] [":", expr «expr ≤ »(y.1, m)] [":=", expr le_trans (le_max_right _ _) (le_max_left _ _)],
    have [ident hz] [":", expr «expr ≤ »(z.1, m)] [":=", expr le_max_right _ _],
    calc
      «expr = »(inductive_limit_dist f x z, dist (le_rec_on hx f x.2 : X m) (le_rec_on hz f z.2 : X m)) : inductive_limit_dist_eq_dist I x z m hx hz
      «expr ≤ »(..., «expr + »(dist (le_rec_on hx f x.2 : X m) (le_rec_on hy f y.2 : X m), dist (le_rec_on hy f y.2 : X m) (le_rec_on hz f z.2 : X m))) : dist_triangle _ _ _
      «expr = »(..., «expr + »(inductive_limit_dist f x y, inductive_limit_dist f y z)) : by rw ["[", expr inductive_limit_dist_eq_dist I x y m hx hy, ",", expr inductive_limit_dist_eq_dist I y z m hy hz, "]"] []
  end }

attribute [local instance] inductive_premetric PseudoMetric.distSetoid

/-- The type giving the inductive limit in a metric space context. -/
def inductive_limit (I : ∀ n, Isometry (f n)) : Type _ :=
  @PseudoMetricQuot _ (inductive_premetric I)

/-- Metric space structure on the inductive limit. -/
instance metric_space_inductive_limit (I : ∀ n, Isometry (f n)) : MetricSpace (inductive_limit I) :=
  @metricSpaceQuot _ (inductive_premetric I)

-- error in Topology.MetricSpace.Gluing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Mapping each `X n` to the inductive limit. -/
def to_inductive_limit (I : ∀ n, isometry (f n)) (n : exprℕ()) (x : X n) : metric.inductive_limit I :=
by letI [] [":", expr pseudo_metric_space «exprΣ , »((n), X n)] [":=", expr inductive_premetric I]; exact [expr «expr⟦ ⟧»(sigma.mk n x)]

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

