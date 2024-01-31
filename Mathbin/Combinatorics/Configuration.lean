/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Algebra.BigOperators.Order
import Combinatorics.Hall.Basic
import Data.Fintype.BigOperators
import SetTheory.Cardinal.Finite

#align_import combinatorics.configuration from "leanprover-community/mathlib"@"38df578a6450a8c5142b3727e3ae894c2300cae0"

/-!
# Configurations of Points and lines

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file introduces abstract configurations of points and lines, and proves some basic properties.

## Main definitions
* `configuration.nondegenerate`: Excludes certain degenerate configurations,
  and imposes uniqueness of intersection points.
* `configuration.has_points`: A nondegenerate configuration in which
  every pair of lines has an intersection point.
* `configuration.has_lines`:  A nondegenerate configuration in which
  every pair of points has a line through them.
* `configuration.line_count`: The number of lines through a given point.
* `configuration.point_count`: The number of lines through a given line.

## Main statements
* `configuration.has_lines.card_le`: `has_lines` implies `|P| ≤ |L|`.
* `configuration.has_points.card_le`: `has_points` implies `|L| ≤ |P|`.
* `configuration.has_lines.has_points`: `has_lines` and `|P| = |L|` implies `has_points`.
* `configuration.has_points.has_lines`: `has_points` and `|P| = |L|` implies `has_lines`.
Together, these four statements say that any two of the following properties imply the third:
(a) `has_lines`, (b) `has_points`, (c) `|P| = |L|`.

-/


open scoped BigOperators

namespace Configuration

variable (P L : Type _) [Membership P L]

#print Configuration.Dual /-
/-- A type synonym. -/
def Dual :=
  P
#align configuration.dual Configuration.Dual
-/

instance [this : Inhabited P] : Inhabited (Dual P) :=
  this

instance [Finite P] : Finite (Dual P) :=
  ‹Finite P›

instance [this : Fintype P] : Fintype (Dual P) :=
  this

instance : Membership (Dual L) (Dual P) :=
  ⟨Function.swap (Membership.Mem : P → L → Prop)⟩

#print Configuration.Nondegenerate /-
/-- A configuration is nondegenerate if:
  1) there does not exist a line that passes through all of the points,
  2) there does not exist a point that is on all of the lines,
  3) there is at most one line through any two points,
  4) any two lines have at most one intersection point.
  Conditions 3 and 4 are equivalent. -/
class Nondegenerate : Prop where
  exists_point : ∀ l : L, ∃ p, p ∉ l
  exists_line : ∀ p, ∃ l : L, p ∉ l
  eq_or_eq : ∀ {p₁ p₂ : P} {l₁ l₂ : L}, p₁ ∈ l₁ → p₂ ∈ l₁ → p₁ ∈ l₂ → p₂ ∈ l₂ → p₁ = p₂ ∨ l₁ = l₂
#align configuration.nondegenerate Configuration.Nondegenerate
-/

#print Configuration.HasPoints /-
/-- A nondegenerate configuration in which every pair of lines has an intersection point. -/
class HasPoints extends Nondegenerate P L where
  mkPoint : ∀ {l₁ l₂ : L} (h : l₁ ≠ l₂), P
  mkPoint_ax : ∀ {l₁ l₂ : L} (h : l₁ ≠ l₂), mk_point h ∈ l₁ ∧ mk_point h ∈ l₂
#align configuration.has_points Configuration.HasPoints
-/

#print Configuration.HasLines /-
/-- A nondegenerate configuration in which every pair of points has a line through them. -/
class HasLines extends Nondegenerate P L where
  mkLine : ∀ {p₁ p₂ : P} (h : p₁ ≠ p₂), L
  mkLine_ax : ∀ {p₁ p₂ : P} (h : p₁ ≠ p₂), p₁ ∈ mk_line h ∧ p₂ ∈ mk_line h
#align configuration.has_lines Configuration.HasLines
-/

open Nondegenerate

open HasPoints (mkPoint mkPoint_ax)

open HasLines (mkLine mkLine_ax)

instance [Nondegenerate P L] : Nondegenerate (Dual L) (Dual P)
    where
  exists_point := @exists_line P L _ _
  exists_line := @exists_point P L _ _
  eq_or_eq l₁ l₂ p₁ p₂ h₁ h₂ h₃ h₄ := (@eq_or_eq P L _ _ p₁ p₂ l₁ l₂ h₁ h₃ h₂ h₄).symm

instance [HasPoints P L] : HasLines (Dual L) (Dual P) :=
  { Dual.nondegenerate _ _ with
    mkLine := @mkPoint P L _ _
    mkLine_ax := fun _ _ => mkPoint_ax }

instance [HasLines P L] : HasPoints (Dual L) (Dual P) :=
  { Dual.nondegenerate _ _ with
    mkPoint := @mkLine P L _ _
    mkPoint_ax := fun _ _ => mkLine_ax }

#print Configuration.HasPoints.existsUnique_point /-
theorem HasPoints.existsUnique_point [HasPoints P L] (l₁ l₂ : L) (hl : l₁ ≠ l₂) :
    ∃! p, p ∈ l₁ ∧ p ∈ l₂ :=
  ⟨mkPoint hl, mkPoint_ax hl, fun p hp =>
    (eq_or_eq hp.1 (mkPoint_ax hl).1 hp.2 (mkPoint_ax hl).2).resolve_right hl⟩
#align configuration.has_points.exists_unique_point Configuration.HasPoints.existsUnique_point
-/

#print Configuration.HasLines.existsUnique_line /-
theorem HasLines.existsUnique_line [HasLines P L] (p₁ p₂ : P) (hp : p₁ ≠ p₂) :
    ∃! l : L, p₁ ∈ l ∧ p₂ ∈ l :=
  HasPoints.existsUnique_point (Dual L) (Dual P) p₁ p₂ hp
#align configuration.has_lines.exists_unique_line Configuration.HasLines.existsUnique_line
-/

variable {P L}

#print Configuration.Nondegenerate.exists_injective_of_card_le /-
/-- If a nondegenerate configuration has at least as many points as lines, then there exists
  an injective function `f` from lines to points, such that `f l` does not lie on `l`. -/
theorem Nondegenerate.exists_injective_of_card_le [Nondegenerate P L] [Fintype P] [Fintype L]
    (h : Fintype.card L ≤ Fintype.card P) : ∃ f : L → P, Function.Injective f ∧ ∀ l, f l ∉ l := by
  classical
#align configuration.nondegenerate.exists_injective_of_card_le Configuration.Nondegenerate.exists_injective_of_card_le
-/

-- Hall's marriage theorem
-- If `s = ∅`, then `s.card = 0 ≤ (s.bUnion t).card`
-- If `s = {l}`, then pick a point `p ∉ l`
-- Rephrase in terms of complements (uses `h`)
-- At most one line through two points of `s`
-- If `s = univ`, then show `s.bUnion t = univ`
-- If `s < univ`, then consequence of `hs₂`
variable {P} (L)

#print Configuration.lineCount /-
/-- Number of points on a given line. -/
noncomputable def lineCount (p : P) : ℕ :=
  Nat.card { l : L // p ∈ l }
#align configuration.line_count Configuration.lineCount
-/

variable (P) {L}

#print Configuration.pointCount /-
/-- Number of lines through a given point. -/
noncomputable def pointCount (l : L) : ℕ :=
  Nat.card { p : P // p ∈ l }
#align configuration.point_count Configuration.pointCount
-/

variable (P L)

#print Configuration.sum_lineCount_eq_sum_pointCount /-
theorem sum_lineCount_eq_sum_pointCount [Fintype P] [Fintype L] :
    ∑ p : P, lineCount L p = ∑ l : L, pointCount P l := by classical
#align configuration.sum_line_count_eq_sum_point_count Configuration.sum_lineCount_eq_sum_pointCount
-/

variable {P L}

#print Configuration.HasLines.pointCount_le_lineCount /-
theorem HasLines.pointCount_le_lineCount [HasLines P L] {p : P} {l : L} (h : p ∉ l)
    [Finite { l : L // p ∈ l }] : pointCount P l ≤ lineCount L p :=
  by
  by_cases hf : Infinite { p : P // p ∈ l }
  · exact (le_of_eq Nat.card_eq_zero_of_infinite).trans (zero_le (line_count L p))
  haveI := fintypeOfNotInfinite hf
  cases nonempty_fintype { l : L // p ∈ l }
  rw [line_count, point_count, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have : ∀ p' : { p // p ∈ l }, p ≠ p' := fun p' hp' => h ((congr_arg (· ∈ l) hp').mpr p'.2)
  exact
    Fintype.card_le_of_injective (fun p' => ⟨mk_line (this p'), (mk_line_ax (this p')).1⟩)
      fun p₁ p₂ hp =>
      Subtype.ext
        ((eq_or_eq p₁.2 p₂.2 (mk_line_ax (this p₁)).2
              ((congr_arg _ (subtype.ext_iff.mp hp)).mpr (mk_line_ax (this p₂)).2)).resolve_right
          fun h' => (congr_arg _ h').mp h (mk_line_ax (this p₁)).1)
#align configuration.has_lines.point_count_le_line_count Configuration.HasLines.pointCount_le_lineCount
-/

#print Configuration.HasPoints.lineCount_le_pointCount /-
theorem HasPoints.lineCount_le_pointCount [HasPoints P L] {p : P} {l : L} (h : p ∉ l)
    [hf : Finite { p : P // p ∈ l }] : lineCount L p ≤ pointCount P l :=
  @HasLines.pointCount_le_lineCount (Dual L) (Dual P) _ _ l p h hf
#align configuration.has_points.line_count_le_point_count Configuration.HasPoints.lineCount_le_pointCount
-/

variable (P L)

#print Configuration.HasLines.card_le /-
/-- If a nondegenerate configuration has a unique line through any two points, then `|P| ≤ |L|`. -/
theorem HasLines.card_le [HasLines P L] [Fintype P] [Fintype L] : Fintype.card P ≤ Fintype.card L :=
  by classical
#align configuration.has_lines.card_le Configuration.HasLines.card_le
-/

#print Configuration.HasPoints.card_le /-
/-- If a nondegenerate configuration has a unique point on any two lines, then `|L| ≤ |P|`. -/
theorem HasPoints.card_le [HasPoints P L] [Fintype P] [Fintype L] :
    Fintype.card L ≤ Fintype.card P :=
  @HasLines.card_le (Dual L) (Dual P) _ _ _ _
#align configuration.has_points.card_le Configuration.HasPoints.card_le
-/

variable {P L}

#print Configuration.HasLines.exists_bijective_of_card_eq /-
theorem HasLines.exists_bijective_of_card_eq [HasLines P L] [Fintype P] [Fintype L]
    (h : Fintype.card P = Fintype.card L) :
    ∃ f : L → P, Function.Bijective f ∧ ∀ l, pointCount P l = lineCount L (f l) := by classical
#align configuration.has_lines.exists_bijective_of_card_eq Configuration.HasLines.exists_bijective_of_card_eq
-/

#print Configuration.HasLines.lineCount_eq_pointCount /-
theorem HasLines.lineCount_eq_pointCount [HasLines P L] [Fintype P] [Fintype L]
    (hPL : Fintype.card P = Fintype.card L) {p : P} {l : L} (hpl : p ∉ l) :
    lineCount L p = pointCount P l := by classical
#align configuration.has_lines.line_count_eq_point_count Configuration.HasLines.lineCount_eq_pointCount
-/

#print Configuration.HasPoints.lineCount_eq_pointCount /-
theorem HasPoints.lineCount_eq_pointCount [HasPoints P L] [Fintype P] [Fintype L]
    (hPL : Fintype.card P = Fintype.card L) {p : P} {l : L} (hpl : p ∉ l) :
    lineCount L p = pointCount P l :=
  (@HasLines.lineCount_eq_pointCount (Dual L) (Dual P) _ _ _ _ hPL.symm l p hpl).symm
#align configuration.has_points.line_count_eq_point_count Configuration.HasPoints.lineCount_eq_pointCount
-/

#print Configuration.HasLines.hasPoints /-
/-- If a nondegenerate configuration has a unique line through any two points, and if `|P| = |L|`,
  then there is a unique point on any two lines. -/
noncomputable def HasLines.hasPoints [HasLines P L] [Fintype P] [Fintype L]
    (h : Fintype.card P = Fintype.card L) : HasPoints P L :=
  let this : ∀ l₁ l₂ : L, l₁ ≠ l₂ → ∃ p : P, p ∈ l₁ ∧ p ∈ l₂ := fun l₁ l₂ hl => by classical
  { ‹HasLines P L› with
    mkPoint := fun l₁ l₂ hl => Classical.choose (this l₁ l₂ hl)
    mkPoint_ax := fun l₁ l₂ hl => Classical.choose_spec (this l₁ l₂ hl) }
#align configuration.has_lines.has_points Configuration.HasLines.hasPoints
-/

#print Configuration.HasPoints.hasLines /-
/-- If a nondegenerate configuration has a unique point on any two lines, and if `|P| = |L|`,
  then there is a unique line through any two points. -/
noncomputable def HasPoints.hasLines [HasPoints P L] [Fintype P] [Fintype L]
    (h : Fintype.card P = Fintype.card L) : HasLines P L :=
  let this := @HasLines.hasPoints (Dual L) (Dual P) _ _ _ _ h.symm
  { ‹HasPoints P L› with
    mkLine := fun _ _ => this.mkPoint
    mkLine_ax := fun _ _ => this.mkPoint_ax }
#align configuration.has_points.has_lines Configuration.HasPoints.hasLines
-/

variable (P L)

#print Configuration.ProjectivePlane /-
/-- A projective plane is a nondegenerate configuration in which every pair of lines has
  an intersection point, every pair of points has a line through them,
  and which has three points in general position. -/
class ProjectivePlane extends HasPoints P L, HasLines P L where
  exists_config :
    ∃ (p₁ p₂ p₃ : P) (l₁ l₂ l₃ : L),
      p₁ ∉ l₂ ∧ p₁ ∉ l₃ ∧ p₂ ∉ l₁ ∧ p₂ ∈ l₂ ∧ p₂ ∈ l₃ ∧ p₃ ∉ l₁ ∧ p₃ ∈ l₂ ∧ p₃ ∉ l₃
#align configuration.projective_plane Configuration.ProjectivePlane
-/

namespace ProjectivePlane

variable [ProjectivePlane P L]

instance : ProjectivePlane (Dual L) (Dual P) :=
  { Dual.hasPoints _ _, Dual.hasLines _ _ with
    exists_config :=
      let ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _
      ⟨l₁, l₂, l₃, p₁, p₂, p₃, h₂₁, h₃₁, h₁₂, h₂₂, h₃₂, h₁₃, h₂₃, h₃₃⟩ }

#print Configuration.ProjectivePlane.order /-
/-- The order of a projective plane is one less than the number of lines through an arbitrary point.
Equivalently, it is one less than the number of points on an arbitrary line. -/
noncomputable def order : ℕ :=
  lineCount L (Classical.choose (@exists_config P L _ _)) - 1
#align configuration.projective_plane.order Configuration.ProjectivePlane.order
-/

#print Configuration.ProjectivePlane.card_points_eq_card_lines /-
theorem card_points_eq_card_lines [Fintype P] [Fintype L] : Fintype.card P = Fintype.card L :=
  le_antisymm (HasLines.card_le P L) (HasPoints.card_le P L)
#align configuration.projective_plane.card_points_eq_card_lines Configuration.ProjectivePlane.card_points_eq_card_lines
-/

variable {P} (L)

#print Configuration.ProjectivePlane.lineCount_eq_lineCount /-
theorem lineCount_eq_lineCount [Finite P] [Finite L] (p q : P) : lineCount L p = lineCount L q :=
  by
  cases nonempty_fintype P
  cases nonempty_fintype L
  obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := exists_config
  have h := card_points_eq_card_lines P L
  let n := line_count L p₂
  have hp₂ : line_count L p₂ = n := rfl
  have hl₁ : point_count P l₁ = n := (has_lines.line_count_eq_point_count h h₂₁).symm.trans hp₂
  have hp₃ : line_count L p₃ = n := (has_lines.line_count_eq_point_count h h₃₁).trans hl₁
  have hl₃ : point_count P l₃ = n := (has_lines.line_count_eq_point_count h h₃₃).symm.trans hp₃
  have hp₁ : line_count L p₁ = n := (has_lines.line_count_eq_point_count h h₁₃).trans hl₃
  have hl₂ : point_count P l₂ = n := (has_lines.line_count_eq_point_count h h₁₂).symm.trans hp₁
  suffices ∀ p : P, line_count L p = n by exact (this p).trans (this q).symm
  refine' fun p =>
    or_not.elim (fun h₂ => _) fun h₂ => (has_lines.line_count_eq_point_count h h₂).trans hl₂
  refine' or_not.elim (fun h₃ => _) fun h₃ => (has_lines.line_count_eq_point_count h h₃).trans hl₃
  rwa [(eq_or_eq h₂ h₂₂ h₃ h₂₃).resolve_right fun h =>
      h₃₃ ((congr_arg (Membership.Mem p₃) h).mp h₃₂)]
#align configuration.projective_plane.line_count_eq_line_count Configuration.ProjectivePlane.lineCount_eq_lineCount
-/

variable (P) {L}

#print Configuration.ProjectivePlane.pointCount_eq_pointCount /-
theorem pointCount_eq_pointCount [Finite P] [Finite L] (l m : L) :
    pointCount P l = pointCount P m :=
  lineCount_eq_lineCount (Dual P) l m
#align configuration.projective_plane.point_count_eq_point_count Configuration.ProjectivePlane.pointCount_eq_pointCount
-/

variable {P L}

#print Configuration.ProjectivePlane.lineCount_eq_pointCount /-
theorem lineCount_eq_pointCount [Finite P] [Finite L] (p : P) (l : L) :
    lineCount L p = pointCount P l :=
  Exists.elim (exists_point l) fun q hq =>
    (lineCount_eq_lineCount L p q).trans <|
      by
      cases nonempty_fintype P; cases nonempty_fintype L
      exact has_lines.line_count_eq_point_count (card_points_eq_card_lines P L) hq
#align configuration.projective_plane.line_count_eq_point_count Configuration.ProjectivePlane.lineCount_eq_pointCount
-/

variable (P L)

#print Configuration.ProjectivePlane.Dual.order /-
theorem Dual.order [Finite P] [Finite L] : order (Dual L) (Dual P) = order P L :=
  congr_arg (fun n => n - 1) (lineCount_eq_pointCount _ _)
#align configuration.projective_plane.dual.order Configuration.ProjectivePlane.Dual.order
-/

variable {P} (L)

#print Configuration.ProjectivePlane.lineCount_eq /-
theorem lineCount_eq [Finite P] [Finite L] (p : P) : lineCount L p = order P L + 1 := by classical
#align configuration.projective_plane.line_count_eq Configuration.ProjectivePlane.lineCount_eq
-/

variable (P) {L}

#print Configuration.ProjectivePlane.pointCount_eq /-
theorem pointCount_eq [Finite P] [Finite L] (l : L) : pointCount P l = order P L + 1 :=
  (lineCount_eq (Dual P) l).trans (congr_arg (fun n => n + 1) (Dual.order P L))
#align configuration.projective_plane.point_count_eq Configuration.ProjectivePlane.pointCount_eq
-/

variable (P L)

#print Configuration.ProjectivePlane.one_lt_order /-
theorem one_lt_order [Finite P] [Finite L] : 1 < order P L :=
  by
  obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, -, -, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _
  classical
#align configuration.projective_plane.one_lt_order Configuration.ProjectivePlane.one_lt_order
-/

variable {P} (L)

#print Configuration.ProjectivePlane.two_lt_lineCount /-
theorem two_lt_lineCount [Finite P] [Finite L] (p : P) : 2 < lineCount L p := by
  simpa only [line_count_eq L p, Nat.succ_lt_succ_iff] using one_lt_order P L
#align configuration.projective_plane.two_lt_line_count Configuration.ProjectivePlane.two_lt_lineCount
-/

variable (P) {L}

#print Configuration.ProjectivePlane.two_lt_pointCount /-
theorem two_lt_pointCount [Finite P] [Finite L] (l : L) : 2 < pointCount P l := by
  simpa only [point_count_eq P l, Nat.succ_lt_succ_iff] using one_lt_order P L
#align configuration.projective_plane.two_lt_point_count Configuration.ProjectivePlane.two_lt_pointCount
-/

variable (P) (L)

#print Configuration.ProjectivePlane.card_points /-
theorem card_points [Fintype P] [Finite L] : Fintype.card P = order P L ^ 2 + order P L + 1 :=
  by
  cases nonempty_fintype L
  obtain ⟨p, -⟩ := @exists_config P L _ _
  let ϕ : { q // q ≠ p } ≃ Σ l : { l : L // p ∈ l }, { q // q ∈ l.1 ∧ q ≠ p } :=
    { toFun := fun q => ⟨⟨mk_line q.2, (mk_line_ax q.2).2⟩, q, (mk_line_ax q.2).1, q.2⟩
      invFun := fun lq => ⟨lq.2, lq.2.2.2⟩
      left_inv := fun q => Subtype.ext rfl
      right_inv := fun lq =>
        Sigma.subtype_ext
          (Subtype.ext
            ((eq_or_eq (mk_line_ax lq.2.2.2).1 (mk_line_ax lq.2.2.2).2 lq.2.2.1 lq.1.2).resolve_left
              lq.2.2.2))
          rfl }
  classical
#align configuration.projective_plane.card_points Configuration.ProjectivePlane.card_points
-/

#print Configuration.ProjectivePlane.card_lines /-
theorem card_lines [Finite P] [Fintype L] : Fintype.card L = order P L ^ 2 + order P L + 1 :=
  (card_points (Dual L) (Dual P)).trans (congr_arg (fun n => n ^ 2 + n + 1) (Dual.order P L))
#align configuration.projective_plane.card_lines Configuration.ProjectivePlane.card_lines
-/

end ProjectivePlane

end Configuration

