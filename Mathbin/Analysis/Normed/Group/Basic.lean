import Mathbin.Order.LiminfLimsup 
import Mathbin.Topology.Algebra.UniformGroup 
import Mathbin.Topology.MetricSpace.Algebra 
import Mathbin.Topology.MetricSpace.Isometry 
import Mathbin.Topology.Sequences

/-!
# Normed (semi)groups

In this file we define four classes:

* `has_norm`, `has_nnnorm`: auxiliary classes endowing a type `α` with a function `norm : α → ℝ`
  (notation: `∥x∥`) and `nnnorm : α → ℝ≥0` (notation: `∥x∥₊`), respectively;
* `semi_normed_group`: a seminormed group is an additive group with a norm and a pseudo metric space
  structures that agree with each other: `∀ x y, dist x y = ∥x - y∥`;
* `normed_group`: a normed group is an additive group with a norm and a metric space structures that
  agree with each other: `∀ x y, dist x y = ∥x - y∥`.

We also prove basic properties of (semi)normed groups and provide some instances.

## Tags

normed group
-/


variable{α ι E F : Type _}

open Filter Metric

open_locale TopologicalSpace BigOperators Nnreal Ennreal uniformity Pointwise

/-- Auxiliary class, endowing a type `E` with a function `norm : E → ℝ`. This class is designed to
be extended in more interesting classes specifying the properties of the norm. -/
class HasNorm(E : Type _) where 
  norm : E → ℝ

export HasNorm(norm)

notation "∥" e "∥" => norm e

/-- A seminormed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥`
defines a pseudometric space structure. -/
class SemiNormedGroup(E : Type _) extends HasNorm E, AddCommGroupₓ E, PseudoMetricSpace E where 
  dist_eq : ∀ (x y : E), dist x y = norm (x - y)

/-- A normed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥` defines
a metric space structure. -/
class NormedGroup(E : Type _) extends HasNorm E, AddCommGroupₓ E, MetricSpace E where 
  dist_eq : ∀ (x y : E), dist x y = norm (x - y)

/-- A normed group is a seminormed group. -/
instance (priority := 100)NormedGroup.toSemiNormedGroup [h : NormedGroup E] : SemiNormedGroup E :=
  { h with  }

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Construct a seminormed group from a translation invariant pseudodistance. -/
def semi_normed_group.of_add_dist
[has_norm E]
[add_comm_group E]
[pseudo_metric_space E]
(H1 : ∀ x : E, «expr = »(«expr∥ ∥»(x), dist x 0))
(H2 : ∀ x y z : E, «expr ≤ »(dist x y, dist «expr + »(x, z) «expr + »(y, z))) : semi_normed_group E :=
{ dist_eq := λ x y, begin
    rw [expr H1] [],
    apply [expr le_antisymm],
    { rw ["[", expr sub_eq_add_neg, ",", "<-", expr add_right_neg y, "]"] [],
      apply [expr H2] },
    { have [] [] [":=", expr H2 «expr - »(x, y) 0 y],
      rwa ["[", expr sub_add_cancel, ",", expr zero_add, "]"] ["at", ident this] }
  end }

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Construct a seminormed group from a translation invariant pseudodistance -/
def semi_normed_group.of_add_dist'
[has_norm E]
[add_comm_group E]
[pseudo_metric_space E]
(H1 : ∀ x : E, «expr = »(«expr∥ ∥»(x), dist x 0))
(H2 : ∀ x y z : E, «expr ≤ »(dist «expr + »(x, z) «expr + »(y, z), dist x y)) : semi_normed_group E :=
{ dist_eq := λ x y, begin
    rw [expr H1] [],
    apply [expr le_antisymm],
    { have [] [] [":=", expr H2 «expr - »(x, y) 0 y],
      rwa ["[", expr sub_add_cancel, ",", expr zero_add, "]"] ["at", ident this] },
    { rw ["[", expr sub_eq_add_neg, ",", "<-", expr add_right_neg y, "]"] [],
      apply [expr H2] }
  end }

/-- A seminormed group can be built from a seminorm that satisfies algebraic properties. This is
formalised in this structure. -/
structure SemiNormedGroup.Core(E : Type _)[AddCommGroupₓ E][HasNorm E] : Prop where 
  norm_zero : ∥(0 : E)∥ = 0
  triangle : ∀ (x y : E), ∥x+y∥ ≤ ∥x∥+∥y∥
  norm_neg : ∀ (x : E), ∥-x∥ = ∥x∥

/-- Constructing a seminormed group from core properties of a seminorm, i.e., registering the
pseudodistance and the pseudometric space structure from the seminorm properties. Note that in most
cases this instance creates bad definitional equalities (e.g., it does not take into account
a possibly existing `uniform_space` instance on `E`). -/
def SemiNormedGroup.ofCore (E : Type _) [AddCommGroupₓ E] [HasNorm E] (C : SemiNormedGroup.Core E) :
  SemiNormedGroup E :=
  { dist := fun x y => ∥x - y∥,
    dist_eq :=
      fun x y =>
        by 
          rfl,
    dist_self :=
      fun x =>
        by 
          simp [C.norm_zero],
    dist_triangle :=
      fun x y z =>
        calc ∥x - z∥ = ∥(x - y)+y - z∥ :=
          by 
            rw [sub_add_sub_cancel]
          _ ≤ ∥x - y∥+∥y - z∥ := C.triangle _ _
          ,
    dist_comm :=
      fun x y =>
        calc ∥x - y∥ = ∥-(y - x)∥ :=
          by 
            simp 
          _ = ∥y - x∥ :=
          by 
            rw [C.norm_neg]
           }

instance  : NormedGroup PUnit :=
  { norm := Function.const _ 0, dist_eq := fun _ _ => rfl }

@[simp]
theorem PUnit.norm_eq_zero (r : PUnit) : ∥r∥ = 0 :=
  rfl

noncomputable instance  : NormedGroup ℝ :=
  { norm := fun x => |x|, dist_eq := fun x y => rfl }

theorem Real.norm_eq_abs (r : ℝ) : ∥r∥ = |r| :=
  rfl

section SemiNormedGroup

variable[SemiNormedGroup E][SemiNormedGroup F]

theorem dist_eq_norm (g h : E) : dist g h = ∥g - h∥ :=
  SemiNormedGroup.dist_eq _ _

theorem dist_eq_norm' (g h : E) : dist g h = ∥h - g∥ :=
  by 
    rw [dist_comm, dist_eq_norm]

@[simp]
theorem dist_zero_right (g : E) : dist g 0 = ∥g∥ :=
  by 
    rw [dist_eq_norm, sub_zero]

@[simp]
theorem dist_zero_left : dist (0 : E) = norm :=
  funext$
    fun g =>
      by 
        rw [dist_comm, dist_zero_right]

theorem tendsto_norm_cocompact_at_top [ProperSpace E] : tendsto norm (cocompact E) at_top :=
  by 
    simpa only [dist_zero_right] using tendsto_dist_right_cocompact_at_top (0 : E)

theorem norm_sub_rev (g h : E) : ∥g - h∥ = ∥h - g∥ :=
  by 
    simpa only [dist_eq_norm] using dist_comm g h

@[simp]
theorem norm_neg (g : E) : ∥-g∥ = ∥g∥ :=
  by 
    simpa using norm_sub_rev 0 g

@[simp]
theorem dist_add_left (g h₁ h₂ : E) : dist (g+h₁) (g+h₂) = dist h₁ h₂ :=
  by 
    simp [dist_eq_norm]

@[simp]
theorem dist_add_right (g₁ g₂ h : E) : dist (g₁+h) (g₂+h) = dist g₁ g₂ :=
  by 
    simp [dist_eq_norm]

@[simp]
theorem dist_neg_neg (g h : E) : dist (-g) (-h) = dist g h :=
  by 
    simp only [dist_eq_norm, neg_sub_neg, norm_sub_rev]

@[simp]
theorem dist_sub_left (g h₁ h₂ : E) : dist (g - h₁) (g - h₂) = dist h₁ h₂ :=
  by 
    simp only [sub_eq_add_neg, dist_add_left, dist_neg_neg]

@[simp]
theorem dist_sub_right (g₁ g₂ h : E) : dist (g₁ - h) (g₂ - h) = dist g₁ g₂ :=
  by 
    simpa only [sub_eq_add_neg] using dist_add_right _ _ _

/-- **Triangle inequality** for the norm. -/
theorem norm_add_le (g h : E) : ∥g+h∥ ≤ ∥g∥+∥h∥ :=
  by 
    simpa [dist_eq_norm] using dist_triangle g 0 (-h)

theorem norm_add_le_of_le {g₁ g₂ : E} {n₁ n₂ : ℝ} (H₁ : ∥g₁∥ ≤ n₁) (H₂ : ∥g₂∥ ≤ n₂) : ∥g₁+g₂∥ ≤ n₁+n₂ :=
  le_transₓ (norm_add_le g₁ g₂) (add_le_add H₁ H₂)

theorem dist_add_add_le (g₁ g₂ h₁ h₂ : E) : dist (g₁+g₂) (h₁+h₂) ≤ dist g₁ h₁+dist g₂ h₂ :=
  by 
    simpa only [dist_add_left, dist_add_right] using dist_triangle (g₁+g₂) (h₁+g₂) (h₁+h₂)

theorem dist_add_add_le_of_le {g₁ g₂ h₁ h₂ : E} {d₁ d₂ : ℝ} (H₁ : dist g₁ h₁ ≤ d₁) (H₂ : dist g₂ h₂ ≤ d₂) :
  dist (g₁+g₂) (h₁+h₂) ≤ d₁+d₂ :=
  le_transₓ (dist_add_add_le g₁ g₂ h₁ h₂) (add_le_add H₁ H₂)

theorem dist_sub_sub_le (g₁ g₂ h₁ h₂ : E) : dist (g₁ - g₂) (h₁ - h₂) ≤ dist g₁ h₁+dist g₂ h₂ :=
  by 
    simpa only [sub_eq_add_neg, dist_neg_neg] using dist_add_add_le g₁ (-g₂) h₁ (-h₂)

theorem dist_sub_sub_le_of_le {g₁ g₂ h₁ h₂ : E} {d₁ d₂ : ℝ} (H₁ : dist g₁ h₁ ≤ d₁) (H₂ : dist g₂ h₂ ≤ d₂) :
  dist (g₁ - g₂) (h₁ - h₂) ≤ d₁+d₂ :=
  le_transₓ (dist_sub_sub_le g₁ g₂ h₁ h₂) (add_le_add H₁ H₂)

theorem abs_dist_sub_le_dist_add_add (g₁ g₂ h₁ h₂ : E) : |dist g₁ h₁ - dist g₂ h₂| ≤ dist (g₁+g₂) (h₁+h₂) :=
  by 
    simpa only [dist_add_left, dist_add_right, dist_comm h₂] using abs_dist_sub_le (g₁+g₂) (h₁+h₂) (h₁+g₂)

@[simp]
theorem norm_nonneg (g : E) : 0 ≤ ∥g∥ :=
  by 
    rw [←dist_zero_right]
    exact dist_nonneg

@[simp]
theorem norm_zero : ∥(0 : E)∥ = 0 :=
  by 
    rw [←dist_zero_right, dist_self]

@[nontriviality]
theorem norm_of_subsingleton [Subsingleton E] (x : E) : ∥x∥ = 0 :=
  by 
    rw [Subsingleton.elimₓ x 0, norm_zero]

theorem norm_sum_le (s : Finset ι) (f : ι → E) : ∥∑i in s, f i∥ ≤ ∑i in s, ∥f i∥ :=
  s.le_sum_of_subadditive norm norm_zero norm_add_le f

theorem norm_sum_le_of_le (s : Finset ι) {f : ι → E} {n : ι → ℝ} (h : ∀ b (_ : b ∈ s), ∥f b∥ ≤ n b) :
  ∥∑b in s, f b∥ ≤ ∑b in s, n b :=
  le_transₓ (norm_sum_le s f) (Finset.sum_le_sum h)

theorem dist_sum_sum_le_of_le (s : Finset ι) {f g : ι → E} {d : ι → ℝ} (h : ∀ b (_ : b ∈ s), dist (f b) (g b) ≤ d b) :
  dist (∑b in s, f b) (∑b in s, g b) ≤ ∑b in s, d b :=
  by 
    simp only [dist_eq_norm, ←Finset.sum_sub_distrib] at *
    exact norm_sum_le_of_le s h

theorem dist_sum_sum_le (s : Finset ι) (f g : ι → E) : dist (∑b in s, f b) (∑b in s, g b) ≤ ∑b in s, dist (f b) (g b) :=
  dist_sum_sum_le_of_le s fun _ _ => le_rfl

theorem norm_sub_le (g h : E) : ∥g - h∥ ≤ ∥g∥+∥h∥ :=
  by 
    simpa [dist_eq_norm] using dist_triangle g 0 h

theorem norm_sub_le_of_le {g₁ g₂ : E} {n₁ n₂ : ℝ} (H₁ : ∥g₁∥ ≤ n₁) (H₂ : ∥g₂∥ ≤ n₂) : ∥g₁ - g₂∥ ≤ n₁+n₂ :=
  le_transₓ (norm_sub_le g₁ g₂) (add_le_add H₁ H₂)

theorem dist_le_norm_add_norm (g h : E) : dist g h ≤ ∥g∥+∥h∥ :=
  by 
    rw [dist_eq_norm]
    apply norm_sub_le

theorem abs_norm_sub_norm_le (g h : E) : |∥g∥ - ∥h∥| ≤ ∥g - h∥ :=
  by 
    simpa [dist_eq_norm] using abs_dist_sub_le g h 0

theorem norm_sub_norm_le (g h : E) : ∥g∥ - ∥h∥ ≤ ∥g - h∥ :=
  le_transₓ (le_abs_self _) (abs_norm_sub_norm_le g h)

theorem dist_norm_norm_le (g h : E) : dist ∥g∥ ∥h∥ ≤ ∥g - h∥ :=
  abs_norm_sub_norm_le g h

theorem norm_le_insert (u v : E) : ∥v∥ ≤ ∥u∥+∥u - v∥ :=
  calc ∥v∥ = ∥u - (u - v)∥ :=
    by 
      abel 
    _ ≤ ∥u∥+∥u - v∥ := norm_sub_le u _
    

theorem norm_le_insert' (u v : E) : ∥u∥ ≤ ∥v∥+∥u - v∥ :=
  by 
    rw [norm_sub_rev]
    exact norm_le_insert v u

theorem norm_le_add_norm_add (u v : E) : ∥u∥ ≤ ∥u+v∥+∥v∥ :=
  calc ∥u∥ = ∥(u+v) - v∥ :=
    by 
      rw [add_sub_cancel]
    _ ≤ ∥u+v∥+∥v∥ := norm_sub_le _ _
    

theorem ball_zero_eq (ε : ℝ) : ball (0 : E) ε = { x | ∥x∥ < ε } :=
  Set.ext$
    fun a =>
      by 
        simp 

theorem mem_ball_iff_norm {g h : E} {r : ℝ} : h ∈ ball g r ↔ ∥h - g∥ < r :=
  by 
    rw [mem_ball, dist_eq_norm]

theorem add_mem_ball_iff_norm {g h : E} {r : ℝ} : (g+h) ∈ ball g r ↔ ∥h∥ < r :=
  by 
    rw [mem_ball_iff_norm, add_sub_cancel']

theorem mem_ball_iff_norm' {g h : E} {r : ℝ} : h ∈ ball g r ↔ ∥g - h∥ < r :=
  by 
    rw [mem_ball', dist_eq_norm]

@[simp]
theorem mem_ball_zero_iff {ε : ℝ} {x : E} : x ∈ ball (0 : E) ε ↔ ∥x∥ < ε :=
  by 
    rw [mem_ball, dist_zero_right]

theorem mem_closed_ball_iff_norm {g h : E} {r : ℝ} : h ∈ closed_ball g r ↔ ∥h - g∥ ≤ r :=
  by 
    rw [mem_closed_ball, dist_eq_norm]

theorem add_mem_closed_ball_iff_norm {g h : E} {r : ℝ} : (g+h) ∈ closed_ball g r ↔ ∥h∥ ≤ r :=
  by 
    rw [mem_closed_ball_iff_norm, add_sub_cancel']

theorem mem_closed_ball_iff_norm' {g h : E} {r : ℝ} : h ∈ closed_ball g r ↔ ∥g - h∥ ≤ r :=
  by 
    rw [mem_closed_ball', dist_eq_norm]

theorem norm_le_of_mem_closed_ball {g h : E} {r : ℝ} (H : h ∈ closed_ball g r) : ∥h∥ ≤ ∥g∥+r :=
  calc ∥h∥ = ∥g+h - g∥ :=
    by 
      rw [add_sub_cancel'_right]
    _ ≤ ∥g∥+∥h - g∥ := norm_add_le _ _ 
    _ ≤ ∥g∥+r :=
    by 
      apply add_le_add_left 
      rw [←dist_eq_norm]
      exact H
    

theorem norm_le_norm_add_const_of_dist_le {a b : E} {c : ℝ} (h : dist a b ≤ c) : ∥a∥ ≤ ∥b∥+c :=
  norm_le_of_mem_closed_ball h

theorem norm_lt_of_mem_ball {g h : E} {r : ℝ} (H : h ∈ ball g r) : ∥h∥ < ∥g∥+r :=
  calc ∥h∥ = ∥g+h - g∥ :=
    by 
      rw [add_sub_cancel'_right]
    _ ≤ ∥g∥+∥h - g∥ := norm_add_le _ _ 
    _ < ∥g∥+r :=
    by 
      apply add_lt_add_left 
      rw [←dist_eq_norm]
      exact H
    

theorem norm_lt_norm_add_const_of_dist_lt {a b : E} {c : ℝ} (h : dist a b < c) : ∥a∥ < ∥b∥+c :=
  norm_lt_of_mem_ball h

theorem bounded_iff_forall_norm_le {s : Set E} : Bounded s ↔ ∃ C, ∀ x (_ : x ∈ s), ∥x∥ ≤ C :=
  by 
    simpa only [Set.subset_def, mem_closed_ball_iff_norm, sub_zero] using bounded_iff_subset_ball (0 : E)

theorem preimage_add_ball (x y : E) (r : ℝ) : (·+·) y ⁻¹' ball x r = ball (x - y) r :=
  by 
    ext z 
    simp only [dist_eq_norm, Set.mem_preimage, mem_ball]
    abel

theorem preimage_add_closed_ball (x y : E) (r : ℝ) : (·+·) y ⁻¹' closed_ball x r = closed_ball (x - y) r :=
  by 
    ext z 
    simp only [dist_eq_norm, Set.mem_preimage, mem_closed_ball]
    abel

@[simp]
theorem mem_sphere_iff_norm (v w : E) (r : ℝ) : w ∈ sphere v r ↔ ∥w - v∥ = r :=
  by 
    simp [dist_eq_norm]

@[simp]
theorem mem_sphere_zero_iff_norm {w : E} {r : ℝ} : w ∈ sphere (0 : E) r ↔ ∥w∥ = r :=
  by 
    simp [dist_eq_norm]

@[simp]
theorem norm_eq_of_mem_sphere {r : ℝ} (x : sphere (0 : E) r) : ∥(x : E)∥ = r :=
  mem_sphere_zero_iff_norm.mp x.2

theorem preimage_add_sphere (x y : E) (r : ℝ) : (·+·) y ⁻¹' sphere x r = sphere (x - y) r :=
  by 
    ext z 
    simp only [Set.mem_preimage, mem_sphere_iff_norm]
    abel

theorem ne_zero_of_norm_pos {g : E} : 0 < ∥g∥ → g ≠ 0 :=
  by 
    intro hpos hzero 
    rw [hzero, norm_zero] at hpos 
    exact lt_irreflₓ 0 hpos

theorem nonzero_of_mem_sphere {r : ℝ} (hr : 0 < r) (x : sphere (0 : E) r) : (x : E) ≠ 0 :=
  by 
    refine' ne_zero_of_norm_pos _ 
    rwa [norm_eq_of_mem_sphere x]

theorem nonzero_of_mem_unit_sphere (x : sphere (0 : E) 1) : (x : E) ≠ 0 :=
  by 
    apply nonzero_of_mem_sphere 
    normNum

/-- We equip the sphere, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance  {r : ℝ} : Neg (sphere (0 : E) r) :=
  { neg :=
      fun w =>
        ⟨-«expr↑ » w,
          by 
            simp ⟩ }

@[simp]
theorem coe_neg_sphere {r : ℝ} (v : sphere (0 : E) r) : ((-v : sphere _ _) : E) = -(v : E) :=
  rfl

namespace Isometric

/-- Addition `y ↦ y + x` as an `isometry`. -/
protected def add_right (x : E) : E ≃ᵢ E :=
  { Equiv.addRight x with isometry_to_fun := isometry_emetric_iff_metric.2$ fun y z => dist_add_right _ _ _ }

@[simp]
theorem add_right_to_equiv (x : E) : (Isometric.addRight x).toEquiv = Equiv.addRight x :=
  rfl

@[simp]
theorem coe_add_right (x : E) : (Isometric.addRight x : E → E) = fun y => y+x :=
  rfl

theorem add_right_apply (x y : E) : (Isometric.addRight x : E → E) y = y+x :=
  rfl

@[simp]
theorem add_right_symm (x : E) : (Isometric.addRight x).symm = Isometric.addRight (-x) :=
  ext$ fun y => rfl

/-- Addition `y ↦ x + y` as an `isometry`. -/
protected def add_left (x : E) : E ≃ᵢ E :=
  { isometry_to_fun := isometry_emetric_iff_metric.2$ fun y z => dist_add_left _ _ _, toEquiv := Equiv.addLeft x }

@[simp]
theorem add_left_to_equiv (x : E) : (Isometric.addLeft x).toEquiv = Equiv.addLeft x :=
  rfl

@[simp]
theorem coe_add_left (x : E) : «expr⇑ » (Isometric.addLeft x) = (·+·) x :=
  rfl

@[simp]
theorem add_left_symm (x : E) : (Isometric.addLeft x).symm = Isometric.addLeft (-x) :=
  ext$ fun y => rfl

variable(E)

/-- Negation `x ↦ -x` as an `isometry`. -/
protected def neg : E ≃ᵢ E :=
  { isometry_to_fun := isometry_emetric_iff_metric.2$ fun x y => dist_neg_neg _ _, toEquiv := Equiv.neg E }

variable{E}

@[simp]
theorem neg_symm : (Isometric.neg E).symm = Isometric.neg E :=
  rfl

@[simp]
theorem neg_to_equiv : (Isometric.neg E).toEquiv = Equiv.neg E :=
  rfl

@[simp]
theorem coe_neg : «expr⇑ » (Isometric.neg E) = Neg.neg :=
  rfl

end Isometric

theorem NormedGroup.tendsto_nhds_zero {f : α → E} {l : Filter α} :
  tendsto f l (𝓝 0) ↔ ∀ ε (_ : ε > 0), ∀ᶠx in l, ∥f x∥ < ε :=
  Metric.tendsto_nhds.trans$
    by 
      simp only [dist_zero_right]

theorem NormedGroup.tendsto_nhds_nhds {f : E → F} {x : E} {y : F} :
  tendsto f (𝓝 x) (𝓝 y) ↔ ∀ ε (_ : ε > 0), ∃ (δ : _)(_ : δ > 0), ∀ x', ∥x' - x∥ < δ → ∥f x' - y∥ < ε :=
  by 
    simpRw [Metric.tendsto_nhds_nhds, dist_eq_norm]

theorem NormedGroup.cauchy_seq_iff [Nonempty α] [SemilatticeSup α] {u : α → E} :
  CauchySeq u ↔ ∀ ε (_ : ε > 0), ∃ N, ∀ m n, N ≤ m → N ≤ n → ∥u m - u n∥ < ε :=
  by 
    simp [Metric.cauchy_seq_iff, dist_eq_norm]

open Finset

/-- A homomorphism `f` of seminormed groups is Lipschitz, if there exists a constant `C` such that
for all `x`, one has `∥f x∥ ≤ C * ∥x∥`. The analogous condition for a linear map of
(semi)normed spaces is in `normed_space.operator_norm`. -/
theorem AddMonoidHom.lipschitz_of_bound (f : E →+ F) (C : ℝ) (h : ∀ x, ∥f x∥ ≤ C*∥x∥) :
  LipschitzWith (Real.toNnreal C) f :=
  LipschitzWith.of_dist_le'$
    fun x y =>
      by 
        simpa only [dist_eq_norm, f.map_sub] using h (x - y)

theorem lipschitz_on_with_iff_norm_sub_le {f : E → F} {C :  ℝ≥0 } {s : Set E} :
  LipschitzOnWith C f s ↔ ∀ x (_ : x ∈ s) y (_ : y ∈ s), ∥f x - f y∥ ≤ C*∥x - y∥ :=
  by 
    simp only [lipschitz_on_with_iff_dist_le_mul, dist_eq_norm]

theorem LipschitzOnWith.norm_sub_le {f : E → F} {C :  ℝ≥0 } {s : Set E} (h : LipschitzOnWith C f s) {x y : E}
  (x_in : x ∈ s) (y_in : y ∈ s) : ∥f x - f y∥ ≤ C*∥x - y∥ :=
  lipschitz_on_with_iff_norm_sub_le.mp h x x_in y y_in

theorem LipschitzOnWith.norm_sub_le_of_le {f : E → F} {C :  ℝ≥0 } {s : Set E} (h : LipschitzOnWith C f s) {x y : E}
  (x_in : x ∈ s) (y_in : y ∈ s) {d : ℝ} (hd : ∥x - y∥ ≤ d) : ∥f x - f y∥ ≤ C*d :=
  (h.norm_sub_le x_in y_in).trans$ mul_le_mul_of_nonneg_left hd C.2

theorem lipschitz_with_iff_norm_sub_le {f : E → F} {C :  ℝ≥0 } : LipschitzWith C f ↔ ∀ x y, ∥f x - f y∥ ≤ C*∥x - y∥ :=
  by 
    simp only [lipschitz_with_iff_dist_le_mul, dist_eq_norm]

alias lipschitz_with_iff_norm_sub_le ↔ LipschitzWith.norm_sub_le _

theorem LipschitzWith.norm_sub_le_of_le {f : E → F} {C :  ℝ≥0 } (h : LipschitzWith C f) {x y : E} {d : ℝ}
  (hd : ∥x - y∥ ≤ d) : ∥f x - f y∥ ≤ C*d :=
  (h.norm_sub_le x y).trans$ mul_le_mul_of_nonneg_left hd C.2

/-- A homomorphism `f` of seminormed groups is continuous, if there exists a constant `C` such that
for all `x`, one has `∥f x∥ ≤ C * ∥x∥`.
The analogous condition for a linear map of normed spaces is in `normed_space.operator_norm`. -/
theorem AddMonoidHom.continuous_of_bound (f : E →+ F) (C : ℝ) (h : ∀ x, ∥f x∥ ≤ C*∥x∥) : Continuous f :=
  (f.lipschitz_of_bound C h).Continuous

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_compact.exists_bound_of_continuous_on
[topological_space α]
{s : set α}
(hs : is_compact s)
{f : α → E}
(hf : continuous_on f s) : «expr∃ , »((C), ∀ x «expr ∈ » s, «expr ≤ »(«expr∥ ∥»(f x), C)) :=
begin
  have [] [":", expr bounded «expr '' »(f, s)] [":=", expr (hs.image_of_continuous_on hf).bounded],
  rcases [expr bounded_iff_forall_norm_le.1 this, "with", "⟨", ident C, ",", ident hC, "⟩"],
  exact [expr ⟨C, λ x hx, hC _ (set.mem_image_of_mem _ hx)⟩]
end

theorem AddMonoidHom.isometry_iff_norm (f : E →+ F) : Isometry f ↔ ∀ x, ∥f x∥ = ∥x∥ :=
  by 
    simp only [isometry_emetric_iff_metric, dist_eq_norm, ←f.map_sub]
    refine' ⟨fun h x => _, fun h x y => h _⟩
    simpa using h x 0

theorem AddMonoidHom.isometry_of_norm (f : E →+ F) (hf : ∀ x, ∥f x∥ = ∥x∥) : Isometry f :=
  f.isometry_iff_norm.2 hf

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem controlled_sum_of_mem_closure
{s : add_subgroup E}
{g : E}
(hg : «expr ∈ »(g, closure (s : set E)))
{b : exprℕ() → exprℝ()}
(b_pos : ∀
 n, «expr < »(0, b n)) : «expr∃ , »((v : exprℕ() → E), «expr ∧ »(tendsto (λ
   n, «expr∑ in , »((i), range «expr + »(n, 1), v i)) at_top (expr𝓝() g), «expr ∧ »(∀
   n, «expr ∈ »(v n, s), «expr ∧ »(«expr < »(«expr∥ ∥»(«expr - »(v 0, g)), b 0), ∀
    n «expr > » 0, «expr < »(«expr∥ ∥»(v n), b n))))) :=
begin
  obtain ["⟨", ident u, ":", expr exprℕ() → E, ",", ident u_in, ":", expr ∀
   n, «expr ∈ »(u n, s), ",", ident lim_u, ":", expr tendsto u at_top (expr𝓝() g), "⟩", ":=", expr mem_closure_iff_seq_limit.mp hg],
  obtain ["⟨", ident n₀, ",", ident hn₀, "⟩", ":", expr «expr∃ , »((n₀), ∀
    n «expr ≥ » n₀, «expr < »(«expr∥ ∥»(«expr - »(u n, g)), b 0))],
  { have [] [":", expr «expr ∈ »({x | «expr < »(«expr∥ ∥»(«expr - »(x, g)), b 0)}, expr𝓝() g)] [],
    { simp_rw ["<-", expr dist_eq_norm] [],
      exact [expr metric.ball_mem_nhds _ (b_pos _)] },
    exact [expr filter.tendsto_at_top'.mp lim_u _ this] },
  set [] [ident z] [":", expr exprℕ() → E] [":="] [expr λ n, u «expr + »(n, n₀)] [],
  have [ident lim_z] [":", expr tendsto z at_top (expr𝓝() g)] [":=", expr lim_u.comp (tendsto_add_at_top_nat n₀)],
  have [ident mem_𝓤] [":", expr ∀
   n, «expr ∈ »({p : «expr × »(E, E) | «expr < »(«expr∥ ∥»(«expr - »(p.1, p.2)), b «expr + »(n, 1))}, expr𝓤() E)] [":=", expr λ
   n, by simpa [] [] [] ["[", "<-", expr dist_eq_norm, "]"] [] ["using", expr metric.dist_mem_uniformity «expr $ »(b_pos, «expr + »(n, 1))]],
  obtain ["⟨", ident φ, ":", expr exprℕ() → exprℕ(), ",", ident φ_extr, ":", expr strict_mono φ, ",", ident hφ, ":", expr ∀
   n, «expr < »(«expr∥ ∥»(«expr - »(z «expr $ »(φ, «expr + »(n, 1)), z (φ n))), b «expr + »(n, 1)), "⟩", ":=", expr lim_z.cauchy_seq.subseq_mem mem_𝓤],
  set [] [ident w] [":", expr exprℕ() → E] [":="] [expr «expr ∘ »(z, φ)] [],
  have [ident hw] [":", expr tendsto w at_top (expr𝓝() g)] [],
  from [expr lim_z.comp φ_extr.tendsto_at_top],
  set [] [ident v] [":", expr exprℕ() → E] [":="] [expr λ
   i, if «expr = »(i, 0) then w 0 else «expr - »(w i, w «expr - »(i, 1))] [],
  refine [expr ⟨v, tendsto.congr (finset.eq_sum_range_sub' w) hw, _, hn₀ _ (n₀.le_add_left _), _⟩],
  { rintro ["⟨", "⟩"],
    { change [expr «expr ∈ »(w 0, s)] [] [],
      apply [expr u_in] },
    { apply [expr s.sub_mem]; apply [expr u_in] } },
  { intros [ident l, ident hl],
    obtain ["⟨", ident k, ",", ident rfl, "⟩", ":", expr «expr∃ , »((k), «expr = »(l, «expr + »(k, 1)))],
    exact [expr nat.exists_eq_succ_of_ne_zero (ne_of_gt hl)],
    apply [expr hφ] }
end

theorem controlled_sum_of_mem_closure_range {j : E →+ F} {h : F} (Hh : h ∈ (Closure$ (j.range : Set F))) {b : ℕ → ℝ}
  (b_pos : ∀ n, 0 < b n) :
  ∃ g : ℕ → E,
    tendsto (fun n => ∑i in range (n+1), j (g i)) at_top (𝓝 h) ∧
      ∥j (g 0) - h∥ < b 0 ∧ ∀ n (_ : n > 0), ∥j (g n)∥ < b n :=
  by 
    rcases controlled_sum_of_mem_closure Hh b_pos with ⟨v, sum_v, v_in, hv₀, hv_pos⟩
    choose g hg using v_in 
    change ∀ (n : ℕ), j (g n) = v n at hg 
    refine'
      ⟨g,
        by 
          simpa [←hg] using sum_v,
        by 
          simpa [hg 0] using hv₀,
        fun n hn =>
          by 
            simpa [hg] using hv_pos n hn⟩

section Nnnorm

/-- Auxiliary class, endowing a type `α` with a function `nnnorm : α → ℝ≥0`. -/
class HasNnnorm(E : Type _) where 
  nnnorm : E →  ℝ≥0 

export HasNnnorm(nnnorm)

notation "∥" e "∥₊" => nnnorm e

instance (priority := 100)SemiNormedGroup.toHasNnnorm : HasNnnorm E :=
  ⟨fun a => ⟨norm a, norm_nonneg a⟩⟩

@[simp, normCast]
theorem coe_nnnorm (a : E) : (∥a∥₊ : ℝ) = norm a :=
  rfl

theorem nndist_eq_nnnorm (a b : E) : nndist a b = ∥a - b∥₊ :=
  Nnreal.eq$ dist_eq_norm _ _

@[simp]
theorem nnnorm_zero : ∥(0 : E)∥₊ = 0 :=
  Nnreal.eq norm_zero

theorem nnnorm_add_le (g h : E) : ∥g+h∥₊ ≤ ∥g∥₊+∥h∥₊ :=
  Nnreal.coe_le_coe.1$ norm_add_le g h

@[simp]
theorem nnnorm_neg (g : E) : ∥-g∥₊ = ∥g∥₊ :=
  Nnreal.eq$ norm_neg g

theorem nndist_nnnorm_nnnorm_le (g h : E) : nndist ∥g∥₊ ∥h∥₊ ≤ ∥g - h∥₊ :=
  Nnreal.coe_le_coe.1$ dist_norm_norm_le g h

theorem of_real_norm_eq_coe_nnnorm (x : E) : Ennreal.ofReal ∥x∥ = (∥x∥₊ : ℝ≥0∞) :=
  Ennreal.of_real_eq_coe_nnreal _

theorem edist_eq_coe_nnnorm_sub (x y : E) : edist x y = (∥x - y∥₊ : ℝ≥0∞) :=
  by 
    rw [edist_dist, dist_eq_norm, of_real_norm_eq_coe_nnnorm]

theorem edist_eq_coe_nnnorm (x : E) : edist x 0 = (∥x∥₊ : ℝ≥0∞) :=
  by 
    rw [edist_eq_coe_nnnorm_sub, _root_.sub_zero]

theorem mem_emetric_ball_zero_iff {x : E} {r : ℝ≥0∞} : x ∈ Emetric.Ball (0 : E) r ↔ «expr↑ » ∥x∥₊ < r :=
  by 
    rw [Emetric.mem_ball, edist_eq_coe_nnnorm]

theorem nndist_add_add_le (g₁ g₂ h₁ h₂ : E) : nndist (g₁+g₂) (h₁+h₂) ≤ nndist g₁ h₁+nndist g₂ h₂ :=
  Nnreal.coe_le_coe.1$ dist_add_add_le g₁ g₂ h₁ h₂

theorem edist_add_add_le (g₁ g₂ h₁ h₂ : E) : edist (g₁+g₂) (h₁+h₂) ≤ edist g₁ h₁+edist g₂ h₂ :=
  by 
    simp only [edist_nndist]
    normCast 
    apply nndist_add_add_le

theorem nnnorm_sum_le (s : Finset ι) (f : ι → E) : ∥∑a in s, f a∥₊ ≤ ∑a in s, ∥f a∥₊ :=
  s.le_sum_of_subadditive nnnorm nnnorm_zero nnnorm_add_le f

theorem AddMonoidHom.lipschitz_of_bound_nnnorm (f : E →+ F) (C :  ℝ≥0 ) (h : ∀ x, ∥f x∥₊ ≤ C*∥x∥₊) :
  LipschitzWith C f :=
  @Real.to_nnreal_coe C ▸ f.lipschitz_of_bound C h

end Nnnorm

namespace LipschitzWith

variable[PseudoEmetricSpace α]{K Kf Kg :  ℝ≥0 }{f g : α → E}

theorem neg (hf : LipschitzWith K f) : LipschitzWith K fun x => -f x :=
  fun x y =>
    by 
      simpa only [edist_dist, dist_neg_neg] using hf x y

theorem add (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : LipschitzWith (Kf+Kg) fun x => f x+g x :=
  fun x y =>
    calc edist (f x+g x) (f y+g y) ≤ edist (f x) (f y)+edist (g x) (g y) := edist_add_add_le _ _ _ _ 
      _ ≤ (Kf*edist x y)+Kg*edist x y := add_le_add (hf x y) (hg x y)
      _ = (Kf+Kg)*edist x y := (add_mulₓ _ _ _).symm
      

theorem sub (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : LipschitzWith (Kf+Kg) fun x => f x - g x :=
  by 
    simpa only [sub_eq_add_neg] using hf.add hg.neg

end LipschitzWith

namespace AntilipschitzWith

variable[PseudoEmetricSpace α]{K Kf Kg :  ℝ≥0 }{f g : α → E}

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem add_lipschitz_with
(hf : antilipschitz_with Kf f)
(hg : lipschitz_with Kg g)
(hK : «expr < »(Kg, «expr ⁻¹»(Kf))) : antilipschitz_with «expr ⁻¹»(«expr - »(«expr ⁻¹»(Kf), Kg)) (λ
 x, «expr + »(f x, g x)) :=
begin
  letI [] [":", expr pseudo_metric_space α] [":=", expr pseudo_emetric_space.to_pseudo_metric_space hf.edist_ne_top],
  refine [expr antilipschitz_with.of_le_mul_dist (λ x y, _)],
  rw ["[", expr nnreal.coe_inv, ",", "<-", expr div_eq_inv_mul, "]"] [],
  rw [expr le_div_iff «expr $ »(nnreal.coe_pos.2, tsub_pos_iff_lt.2 hK)] [],
  rw ["[", expr mul_comm, ",", expr nnreal.coe_sub hK.le, ",", expr sub_mul, "]"] [],
  calc
    «expr ≤ »(«expr - »(«expr * »(«expr↑ »(«expr ⁻¹»(Kf)), dist x y), «expr * »(Kg, dist x y)), «expr - »(dist (f x) (f y), dist (g x) (g y))) : sub_le_sub (hf.mul_le_dist x y) (hg.dist_le_mul x y)
    «expr ≤ »(..., _) : le_trans (le_abs_self _) (abs_dist_sub_le_dist_add_add _ _ _ _)
end

theorem add_sub_lipschitz_with (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg (g - f)) (hK : Kg < Kf⁻¹) :
  AntilipschitzWith ((Kf⁻¹ - Kg)⁻¹) g :=
  by 
    simpa only [Pi.sub_apply, add_sub_cancel'_right] using hf.add_lipschitz_with hg hK

end AntilipschitzWith

/-- A group homomorphism from an `add_comm_group` to a `semi_normed_group` induces a
`semi_normed_group` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def SemiNormedGroup.induced {E} [AddCommGroupₓ E] (f : E →+ F) : SemiNormedGroup E :=
  { PseudoMetricSpace.induced f SemiNormedGroup.toPseudoMetricSpace with norm := fun x => ∥f x∥,
    dist_eq :=
      fun x y =>
        by 
          simpa only [AddMonoidHom.map_sub, ←dist_eq_norm] }

/-- A subgroup of a seminormed group is also a seminormed group,
with the restriction of the norm. -/
instance AddSubgroup.semiNormedGroup (s : AddSubgroup E) : SemiNormedGroup s :=
  SemiNormedGroup.induced s.subtype

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`. -/
@[simp]
theorem coe_norm_subgroup {E : Type _} [SemiNormedGroup E] {s : AddSubgroup E} (x : s) : ∥x∥ = ∥(x : E)∥ :=
  rfl

/-- A submodule of a seminormed group is also a seminormed group, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance Submodule.semiNormedGroup {𝕜 : Type _} {_ : Ringₓ 𝕜} {E : Type _} [SemiNormedGroup E] {_ : Module 𝕜 E}
  (s : Submodule 𝕜 E) : SemiNormedGroup s :=
  { norm := fun x => norm (x : E), dist_eq := fun x y => dist_eq_norm (x : E) (y : E) }

/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `E` is equal to its
norm in `s`.

See note [implicit instance arguments]. -/
@[simp, normCast]
theorem Submodule.norm_coe {𝕜 : Type _} {_ : Ringₓ 𝕜} {E : Type _} [SemiNormedGroup E] {_ : Module 𝕜 E}
  {s : Submodule 𝕜 E} (x : s) : ∥(x : E)∥ = ∥x∥ :=
  rfl

@[simp]
theorem Submodule.norm_mk {𝕜 : Type _} {_ : Ringₓ 𝕜} {E : Type _} [SemiNormedGroup E] {_ : Module 𝕜 E}
  {s : Submodule 𝕜 E} (x : E) (hx : x ∈ s) : ∥(⟨x, hx⟩ : s)∥ = ∥x∥ :=
  rfl

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- seminormed group instance on the product of two seminormed groups, using the sup norm. -/
noncomputable
instance prod.semi_normed_group : semi_normed_group «expr × »(E, F) :=
{ norm := λ x, max «expr∥ ∥»(x.1) «expr∥ ∥»(x.2),
  dist_eq := assume
  x
  y : «expr × »(E, F), show «expr = »(max (dist x.1 y.1) (dist x.2 y.2), max «expr∥ ∥»(«expr - »(x, y).1) «expr∥ ∥»(«expr - »(x, y).2)), by simp [] [] [] ["[", expr dist_eq_norm, "]"] [] [] }

theorem Prod.semi_norm_def (x : E × F) : ∥x∥ = max ∥x.1∥ ∥x.2∥ :=
  rfl

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prod.nnsemi_norm_def (x : «expr × »(E, F)) : «expr = »(«expr∥ ∥₊»(x), max «expr∥ ∥₊»(x.1) «expr∥ ∥₊»(x.2)) :=
by { have [] [] [":=", expr x.semi_norm_def],
  simp [] [] ["only"] ["[", "<-", expr coe_nnnorm, "]"] [] ["at", ident this],
  exact_mod_cast [expr this] }

theorem semi_norm_fst_le (x : E × F) : ∥x.1∥ ≤ ∥x∥ :=
  le_max_leftₓ _ _

theorem semi_norm_snd_le (x : E × F) : ∥x.2∥ ≤ ∥x∥ :=
  le_max_rightₓ _ _

theorem semi_norm_prod_le_iff {x : E × F} {r : ℝ} : ∥x∥ ≤ r ↔ ∥x.1∥ ≤ r ∧ ∥x.2∥ ≤ r :=
  max_le_iff

/-- seminormed group instance on the product of finitely many seminormed groups,
using the sup norm. -/
noncomputable instance Pi.semiNormedGroup {π : ι → Type _} [Fintype ι] [∀ i, SemiNormedGroup (π i)] :
  SemiNormedGroup (∀ i, π i) :=
  { norm := fun f => ((Finset.sup Finset.univ fun b => ∥f b∥₊ :  ℝ≥0 ) : ℝ),
    dist_eq :=
      fun x y =>
        congr_argₓ (coeₓ :  ℝ≥0  → ℝ)$
          congr_argₓ (Finset.sup Finset.univ)$
            funext$ fun a => show nndist (x a) (y a) = ∥x a - y a∥₊ from nndist_eq_nnnorm _ _ }

/-- The seminorm of an element in a product space is `≤ r` if and only if the norm of each
component is. -/
theorem pi_semi_norm_le_iff {π : ι → Type _} [Fintype ι] [∀ i, SemiNormedGroup (π i)] {r : ℝ} (hr : 0 ≤ r)
  {x : ∀ i, π i} : ∥x∥ ≤ r ↔ ∀ i, ∥x i∥ ≤ r :=
  by 
    simp only [←dist_zero_right, dist_pi_le_iff hr, Pi.zero_apply]

/-- The seminorm of an element in a product space is `< r` if and only if the norm of each
component is. -/
theorem pi_semi_norm_lt_iff {π : ι → Type _} [Fintype ι] [∀ i, SemiNormedGroup (π i)] {r : ℝ} (hr : 0 < r)
  {x : ∀ i, π i} : ∥x∥ < r ↔ ∀ i, ∥x i∥ < r :=
  by 
    simp only [←dist_zero_right, dist_pi_lt_iff hr, Pi.zero_apply]

theorem semi_norm_le_pi_norm {π : ι → Type _} [Fintype ι] [∀ i, SemiNormedGroup (π i)] (x : ∀ i, π i) (i : ι) :
  ∥x i∥ ≤ ∥x∥ :=
  (pi_semi_norm_le_iff (norm_nonneg x)).1 (le_reflₓ _) i

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp] theorem pi_semi_norm_const [nonempty ι] [fintype ι] (a : E) : «expr = »(«expr∥ ∥»(λ i : ι, a), «expr∥ ∥»(a)) :=
by simpa [] [] ["only"] ["[", "<-", expr dist_zero_right, "]"] [] ["using", expr dist_pi_const a 0]

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp]
theorem pi_nnsemi_norm_const [nonempty ι] [fintype ι] (a : E) : «expr = »(«expr∥ ∥₊»(λ i : ι, a), «expr∥ ∥₊»(a)) :=
«expr $ »(nnreal.eq, pi_semi_norm_const a)

theorem tendsto_iff_norm_tendsto_zero {f : α → E} {a : Filter α} {b : E} :
  tendsto f a (𝓝 b) ↔ tendsto (fun e => ∥f e - b∥) a (𝓝 0) :=
  by 
    convert tendsto_iff_dist_tendsto_zero 
    simp [dist_eq_norm]

theorem is_bounded_under_of_tendsto {l : Filter α} {f : α → E} {c : E} (h : Filter.Tendsto f l (𝓝 c)) :
  is_bounded_under (· ≤ ·) l fun x => ∥f x∥ :=
  ⟨∥c∥+1,
    @tendsto.eventually α E f _ _ (fun k => ∥k∥ ≤ ∥c∥+1) h
      (Filter.eventually_iff_exists_mem.mpr
        ⟨Metric.ClosedBall c 1, Metric.closed_ball_mem_nhds c zero_lt_one,
          fun y hy => norm_le_norm_add_const_of_dist_le hy⟩)⟩

theorem tendsto_zero_iff_norm_tendsto_zero {f : α → E} {a : Filter α} :
  tendsto f a (𝓝 0) ↔ tendsto (fun e => ∥f e∥) a (𝓝 0) :=
  by 
    rw [tendsto_iff_norm_tendsto_zero]
    simp only [sub_zero]

/-- Special case of the sandwich theorem: if the norm of `f` is eventually bounded by a real
function `g` which tends to `0`, then `f` tends to `0`.
In this pair of lemmas (`squeeze_zero_norm'` and `squeeze_zero_norm`), following a convention of
similar lemmas in `topology.metric_space.basic` and `topology.algebra.ordered`, the `'` version is
phrased using "eventually" and the non-`'` version is phrased absolutely. -/
theorem squeeze_zero_norm' {f : α → E} {g : α → ℝ} {t₀ : Filter α} (h : ∀ᶠn in t₀, ∥f n∥ ≤ g n)
  (h' : tendsto g t₀ (𝓝 0)) : tendsto f t₀ (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (eventually_of_forall fun n => norm_nonneg _) h h')

/-- Special case of the sandwich theorem: if the norm of `f` is bounded by a real function `g` which
tends to `0`, then `f` tends to `0`.  -/
theorem squeeze_zero_norm {f : α → E} {g : α → ℝ} {t₀ : Filter α} (h : ∀ n, ∥f n∥ ≤ g n) (h' : tendsto g t₀ (𝓝 0)) :
  tendsto f t₀ (𝓝 0) :=
  squeeze_zero_norm' (eventually_of_forall h) h'

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem tendsto_norm_sub_self (x : E) : tendsto (λ g : E, «expr∥ ∥»(«expr - »(g, x))) (expr𝓝() x) (expr𝓝() 0) :=
by simpa [] [] [] ["[", expr dist_eq_norm, "]"] [] ["using", expr tendsto_id.dist (tendsto_const_nhds : tendsto (λ
  g, (x : E)) (expr𝓝() x) _)]

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem tendsto_norm {x : E} : tendsto (λ g : E, «expr∥ ∥»(g)) (expr𝓝() x) (expr𝓝() «expr∥ ∥»(x)) :=
by simpa [] [] [] [] [] ["using", expr tendsto_id.dist (tendsto_const_nhds : tendsto (λ g, (0 : E)) _ _)]

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem tendsto_norm_zero : tendsto (λ g : E, «expr∥ ∥»(g)) (expr𝓝() 0) (expr𝓝() 0) :=
by simpa [] [] [] [] [] ["using", expr tendsto_norm_sub_self (0 : E)]

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[continuity #[]] theorem continuous_norm : continuous (λ g : E, «expr∥ ∥»(g)) :=
by simpa [] [] [] [] [] ["using", expr continuous_id.dist (continuous_const : continuous (λ g, (0 : E)))]

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[continuity #[]] theorem continuous_nnnorm : continuous (λ a : E, «expr∥ ∥₊»(a)) :=
continuous_subtype_mk _ continuous_norm

theorem lipschitz_with_one_norm : LipschitzWith 1 (norm : E → ℝ) :=
  by 
    simpa only [dist_zero_left] using LipschitzWith.dist_right (0 : E)

theorem uniform_continuous_norm : UniformContinuous (norm : E → ℝ) :=
  lipschitz_with_one_norm.UniformContinuous

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem uniform_continuous_nnnorm : uniform_continuous (λ a : E, «expr∥ ∥₊»(a)) :=
uniform_continuous_subtype_mk uniform_continuous_norm _

section 

variable{l : Filter α}{f : α → E}{a : E}

theorem Filter.Tendsto.norm (h : tendsto f l (𝓝 a)) : tendsto (fun x => ∥f x∥) l (𝓝 ∥a∥) :=
  tendsto_norm.comp h

theorem Filter.Tendsto.nnnorm (h : tendsto f l (𝓝 a)) : tendsto (fun x => ∥f x∥₊) l (𝓝 ∥a∥₊) :=
  tendsto.comp continuous_nnnorm.ContinuousAt h

end 

section 

variable[TopologicalSpace α]{f : α → E}{s : Set α}{a : α}{b : E}

theorem Continuous.norm (h : Continuous f) : Continuous fun x => ∥f x∥ :=
  continuous_norm.comp h

theorem Continuous.nnnorm (h : Continuous f) : Continuous fun x => ∥f x∥₊ :=
  continuous_nnnorm.comp h

theorem ContinuousAt.norm (h : ContinuousAt f a) : ContinuousAt (fun x => ∥f x∥) a :=
  h.norm

theorem ContinuousAt.nnnorm (h : ContinuousAt f a) : ContinuousAt (fun x => ∥f x∥₊) a :=
  h.nnnorm

theorem ContinuousWithinAt.norm (h : ContinuousWithinAt f s a) : ContinuousWithinAt (fun x => ∥f x∥) s a :=
  h.norm

theorem ContinuousWithinAt.nnnorm (h : ContinuousWithinAt f s a) : ContinuousWithinAt (fun x => ∥f x∥₊) s a :=
  h.nnnorm

theorem ContinuousOn.norm (h : ContinuousOn f s) : ContinuousOn (fun x => ∥f x∥) s :=
  fun x hx => (h x hx).norm

theorem ContinuousOn.nnnorm (h : ContinuousOn f s) : ContinuousOn (fun x => ∥f x∥₊) s :=
  fun x hx => (h x hx).nnnorm

end 

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `∥y∥→∞`, then we can assume `y≠x` for any fixed `x`. -/
theorem eventually_ne_of_tendsto_norm_at_top
{l : filter α}
{f : α → E}
(h : tendsto (λ y, «expr∥ ∥»(f y)) l at_top)
(x : E) : «expr∀ᶠ in , »((y), l, «expr ≠ »(f y, x)) :=
begin
  have [] [":", expr «expr∀ᶠ in , »((y), l, «expr ≤ »(«expr + »(1, «expr∥ ∥»(x)), «expr∥ ∥»(f y)))] [":=", expr h (mem_at_top «expr + »(1, «expr∥ ∥»(x)))],
  refine [expr this.mono (λ y hy hxy, _)],
  subst [expr x],
  exact [expr not_le_of_lt zero_lt_one (add_le_iff_nonpos_left.1 hy)]
end

instance (priority := 100)SemiNormedGroup.has_lipschitz_add : HasLipschitzAdd E :=
  { lipschitz_add := ⟨2, LipschitzWith.prod_fst.add LipschitzWith.prod_snd⟩ }

/-- A seminormed group is a uniform additive group, i.e., addition and subtraction are uniformly
continuous. -/
instance (priority := 100)normed_uniform_group : UniformAddGroup E :=
  ⟨(LipschitzWith.prod_fst.sub LipschitzWith.prod_snd).UniformContinuous⟩

instance (priority := 100)normed_top_group : TopologicalAddGroup E :=
  by 
    infer_instance

theorem Nat.norm_cast_le [HasOne E] : ∀ (n : ℕ), ∥(n : E)∥ ≤ n*∥(1 : E)∥
| 0 =>
  by 
    simp 
| n+1 =>
  by 
    rw [n.cast_succ, n.cast_succ, add_mulₓ, one_mulₓ]
    exact norm_add_le_of_le (Nat.norm_cast_le n) le_rfl

theorem SemiNormedGroup.mem_closure_iff {s : Set E} {x : E} :
  x ∈ Closure s ↔ ∀ ε (_ : ε > 0), ∃ (y : _)(_ : y ∈ s), ∥x - y∥ < ε :=
  by 
    simp [Metric.mem_closure_iff, dist_eq_norm]

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_le_zero_iff' [separated_space E] {g : E} : «expr ↔ »(«expr ≤ »(«expr∥ ∥»(g), 0), «expr = »(g, 0)) :=
begin
  letI [] [":", expr normed_group E] [":=", expr { to_metric_space := of_t2_pseudo_metric_space «expr‹ ›»(_),
     ..«expr‹ ›»(semi_normed_group E) }],
  rw ["[", "<-", expr dist_zero_right, "]"] [],
  exact [expr dist_le_zero]
end

theorem norm_eq_zero_iff' [SeparatedSpace E] {g : E} : ∥g∥ = 0 ↔ g = 0 :=
  (norm_nonneg g).le_iff_eq.symm.trans norm_le_zero_iff'

theorem norm_pos_iff' [SeparatedSpace E] {g : E} : 0 < ∥g∥ ↔ g ≠ 0 :=
  by 
    rw [←not_leₓ, norm_le_zero_iff']

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cauchy_seq_sum_of_eventually_eq
{u v : exprℕ() → E}
{N : exprℕ()}
(huv : ∀ n «expr ≥ » N, «expr = »(u n, v n))
(hv : cauchy_seq (λ
  n, «expr∑ in , »((k), range «expr + »(n, 1), v k))) : cauchy_seq (λ
 n, «expr∑ in , »((k), range «expr + »(n, 1), u k)) :=
begin
  let [ident d] [":", expr exprℕ() → E] [":=", expr λ
   n, «expr∑ in , »((k), range «expr + »(n, 1), «expr - »(u k, v k))],
  rw [expr show «expr = »(λ
    n, «expr∑ in , »((k), range «expr + »(n, 1), u k), «expr + »(d, λ
     n, «expr∑ in , »((k), range «expr + »(n, 1), v k))), by { ext [] [ident n] [],
     simp [] [] [] ["[", expr d, "]"] [] [] }] [],
  have [] [":", expr ∀ n «expr ≥ » N, «expr = »(d n, d N)] [],
  { intros [ident n, ident hn],
    dsimp [] ["[", expr d, "]"] [] [],
    rw [expr eventually_constant_sum _ hn] [],
    intros [ident m, ident hm],
    simp [] [] [] ["[", expr huv m hm, "]"] [] [] },
  exact [expr (tendsto_at_top_of_eventually_const this).cauchy_seq.add hv]
end

end SemiNormedGroup

section NormedGroup

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Construct a normed group from a translation invariant distance -/
def normed_group.of_add_dist
[has_norm E]
[add_comm_group E]
[metric_space E]
(H1 : ∀ x : E, «expr = »(«expr∥ ∥»(x), dist x 0))
(H2 : ∀ x y z : E, «expr ≤ »(dist x y, dist «expr + »(x, z) «expr + »(y, z))) : normed_group E :=
{ dist_eq := λ x y, begin
    rw [expr H1] [],
    apply [expr le_antisymm],
    { rw ["[", expr sub_eq_add_neg, ",", "<-", expr add_right_neg y, "]"] [],
      apply [expr H2] },
    { have [] [] [":=", expr H2 «expr - »(x, y) 0 y],
      rwa ["[", expr sub_add_cancel, ",", expr zero_add, "]"] ["at", ident this] }
  end }

/-- A normed group can be built from a norm that satisfies algebraic properties. This is
formalised in this structure. -/
structure NormedGroup.Core(E : Type _)[AddCommGroupₓ E][HasNorm E] : Prop where 
  norm_eq_zero_iff : ∀ (x : E), ∥x∥ = 0 ↔ x = 0
  triangle : ∀ (x y : E), ∥x+y∥ ≤ ∥x∥+∥y∥
  norm_neg : ∀ (x : E), ∥-x∥ = ∥x∥

/-- The `semi_normed_group.core` induced by a `normed_group.core`. -/
theorem NormedGroup.Core.ToSemiNormedGroup.core {E : Type _} [AddCommGroupₓ E] [HasNorm E] (C : NormedGroup.Core E) :
  SemiNormedGroup.Core E :=
  { norm_zero := (C.norm_eq_zero_iff 0).2 rfl, triangle := C.triangle, norm_neg := C.norm_neg }

/-- Constructing a normed group from core properties of a norm, i.e., registering the distance and
the metric space structure from the norm properties. -/
def NormedGroup.ofCore (E : Type _) [AddCommGroupₓ E] [HasNorm E] (C : NormedGroup.Core E) : NormedGroup E :=
  { SemiNormedGroup.ofCore E (NormedGroup.Core.ToSemiNormedGroup.core C) with
    eq_of_dist_eq_zero :=
      fun x y h =>
        by 
          rw [dist_eq_norm] at h 
          exact sub_eq_zero.mp ((C.norm_eq_zero_iff _).1 h) }

variable[NormedGroup E][NormedGroup F]

@[simp]
theorem norm_eq_zero {g : E} : ∥g∥ = 0 ↔ g = 0 :=
  norm_eq_zero_iff'

@[simp]
theorem norm_pos_iff {g : E} : 0 < ∥g∥ ↔ g ≠ 0 :=
  norm_pos_iff'

@[simp]
theorem norm_le_zero_iff {g : E} : ∥g∥ ≤ 0 ↔ g = 0 :=
  norm_le_zero_iff'

theorem norm_sub_eq_zero_iff {u v : E} : ∥u - v∥ = 0 ↔ u = v :=
  by 
    rw [norm_eq_zero, sub_eq_zero]

theorem eq_of_norm_sub_le_zero {g h : E} (a : ∥g - h∥ ≤ 0) : g = h :=
  by 
    rwa [←sub_eq_zero, ←norm_le_zero_iff]

theorem eq_of_norm_sub_eq_zero {u v : E} (h : ∥u - v∥ = 0) : u = v :=
  norm_sub_eq_zero_iff.1 h

@[simp]
theorem nnnorm_eq_zero {a : E} : ∥a∥₊ = 0 ↔ a = 0 :=
  by 
    rw [←Nnreal.coe_eq_zero, coe_nnnorm, norm_eq_zero]

/-- An injective group homomorphism from an `add_comm_group` to a `normed_group` induces a
`normed_group` structure on the domain.

See note [reducible non-instances]. -/
@[reducible]
def NormedGroup.induced {E} [AddCommGroupₓ E] (f : E →+ F) (h : Function.Injective f) : NormedGroup E :=
  { SemiNormedGroup.induced f, MetricSpace.induced f h NormedGroup.toMetricSpace with  }

/-- A subgroup of a normed group is also a normed group, with the restriction of the norm. -/
instance AddSubgroup.normedGroup (s : AddSubgroup E) : NormedGroup s :=
  NormedGroup.induced s.subtype Subtype.coe_injective

/-- A submodule of a normed group is also a normed group, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance Submodule.normedGroup {𝕜 : Type _} {_ : Ringₓ 𝕜} {E : Type _} [NormedGroup E] {_ : Module 𝕜 E}
  (s : Submodule 𝕜 E) : NormedGroup s :=
  { Submodule.semiNormedGroup s with  }

/-- normed group instance on the product of two normed groups, using the sup norm. -/
noncomputable instance Prod.normedGroup : NormedGroup (E × F) :=
  { Prod.semiNormedGroup with  }

theorem Prod.norm_def (x : E × F) : ∥x∥ = max ∥x.1∥ ∥x.2∥ :=
  rfl

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prod.nnnorm_def (x : «expr × »(E, F)) : «expr = »(«expr∥ ∥₊»(x), max «expr∥ ∥₊»(x.1) «expr∥ ∥₊»(x.2)) :=
by { have [] [] [":=", expr x.norm_def],
  simp [] [] ["only"] ["[", "<-", expr coe_nnnorm, "]"] [] ["at", ident this],
  exact_mod_cast [expr this] }

theorem norm_fst_le (x : E × F) : ∥x.1∥ ≤ ∥x∥ :=
  le_max_leftₓ _ _

theorem norm_snd_le (x : E × F) : ∥x.2∥ ≤ ∥x∥ :=
  le_max_rightₓ _ _

theorem norm_prod_le_iff {x : E × F} {r : ℝ} : ∥x∥ ≤ r ↔ ∥x.1∥ ≤ r ∧ ∥x.2∥ ≤ r :=
  max_le_iff

/-- normed group instance on the product of finitely many normed groups, using the sup norm. -/
noncomputable instance Pi.normedGroup {π : ι → Type _} [Fintype ι] [∀ i, NormedGroup (π i)] : NormedGroup (∀ i, π i) :=
  { Pi.semiNormedGroup with  }

/-- The norm of an element in a product space is `≤ r` if and only if the norm of each
component is. -/
theorem pi_norm_le_iff {π : ι → Type _} [Fintype ι] [∀ i, NormedGroup (π i)] {r : ℝ} (hr : 0 ≤ r) {x : ∀ i, π i} :
  ∥x∥ ≤ r ↔ ∀ i, ∥x i∥ ≤ r :=
  by 
    simp only [←dist_zero_right, dist_pi_le_iff hr, Pi.zero_apply]

/-- The norm of an element in a product space is `< r` if and only if the norm of each
component is. -/
theorem pi_norm_lt_iff {π : ι → Type _} [Fintype ι] [∀ i, NormedGroup (π i)] {r : ℝ} (hr : 0 < r) {x : ∀ i, π i} :
  ∥x∥ < r ↔ ∀ i, ∥x i∥ < r :=
  by 
    simp only [←dist_zero_right, dist_pi_lt_iff hr, Pi.zero_apply]

theorem norm_le_pi_norm {π : ι → Type _} [Fintype ι] [∀ i, NormedGroup (π i)] (x : ∀ i, π i) (i : ι) : ∥x i∥ ≤ ∥x∥ :=
  (pi_norm_le_iff (norm_nonneg x)).1 (le_reflₓ _) i

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp] theorem pi_norm_const [nonempty ι] [fintype ι] (a : E) : «expr = »(«expr∥ ∥»(λ i : ι, a), «expr∥ ∥»(a)) :=
by simpa [] [] ["only"] ["[", "<-", expr dist_zero_right, "]"] [] ["using", expr dist_pi_const a 0]

-- error in Analysis.Normed.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp] theorem pi_nnnorm_const [nonempty ι] [fintype ι] (a : E) : «expr = »(«expr∥ ∥₊»(λ i : ι, a), «expr∥ ∥₊»(a)) :=
«expr $ »(nnreal.eq, pi_norm_const a)

theorem tendsto_norm_nhds_within_zero : tendsto (norm : E → ℝ) (𝓝[«expr ᶜ» {0}] 0) (𝓝[Set.Ioi 0] 0) :=
  (continuous_norm.tendsto' (0 : E) 0 norm_zero).inf$ tendsto_principal_principal.2$ fun x => norm_pos_iff.2

end NormedGroup

