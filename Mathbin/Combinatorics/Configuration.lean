import Mathbin.Combinatorics.Hall.Basic
import Mathbin.Data.Fintype.Card
import Mathbin.SetTheory.Fincard

/-!
# Configurations of Points and lines
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


open_locale BigOperators

namespace Configuration

universe u

variable (P L : Type u) [HasMem P L]

/-- A type synonym. -/
def dual :=
  P

instance [this : Inhabited P] : Inhabited (dual P) :=
  this

instance [this : Fintype P] : Fintype (dual P) :=
  this

instance : HasMem (dual L) (dual P) :=
  ⟨Function.swap (HasMem.Mem : P → L → Prop)⟩

/-- A configuration is nondegenerate if:
  1) there does not exist a line that passes through all of the points,
  2) there does not exist a point that is on all of the lines,
  3) there is at most one line through any two points,
  4) any two lines have at most one intersection point.
  Conditions 3 and 4 are equivalent. -/
class nondegenerate : Prop where
  exists_point : ∀ l : L, ∃ p, p ∉ l
  exists_line : ∀ p, ∃ l : L, p ∉ l
  eq_or_eq : ∀ {p₁ p₂ : P} {l₁ l₂ : L}, p₁ ∈ l₁ → p₂ ∈ l₁ → p₁ ∈ l₂ → p₂ ∈ l₂ → p₁ = p₂ ∨ l₁ = l₂

/-- A nondegenerate configuration in which every pair of lines has an intersection point. -/
class has_points extends nondegenerate P L : Type u where
  mkPoint : ∀ {l₁ l₂ : L} h : l₁ ≠ l₂, P
  mk_point_ax : ∀ {l₁ l₂ : L} h : l₁ ≠ l₂, mk_point h ∈ l₁ ∧ mk_point h ∈ l₂

/-- A nondegenerate configuration in which every pair of points has a line through them. -/
class has_lines extends nondegenerate P L : Type u where
  mkLine : ∀ {p₁ p₂ : P} h : p₁ ≠ p₂, L
  mk_line_ax : ∀ {p₁ p₂ : P} h : p₁ ≠ p₂, p₁ ∈ mk_line h ∧ p₂ ∈ mk_line h

open Nondegenerate HasPoints HasLines

instance [nondegenerate P L] : nondegenerate (dual L) (dual P) where
  exists_point := @exists_line P L _ _
  exists_line := @exists_point P L _ _
  eq_or_eq := fun l₁ l₂ p₁ p₂ h₁ h₂ h₃ h₄ => (@eq_or_eq P L _ _ p₁ p₂ l₁ l₂ h₁ h₃ h₂ h₄).symm

instance [has_points P L] : has_lines (dual L) (dual P) where
  mkLine := @mk_point P L _ _
  mk_line_ax := fun _ _ => mk_point_ax

instance [has_lines P L] : has_points (dual L) (dual P) where
  mkPoint := @mk_line P L _ _
  mk_point_ax := fun _ _ => mk_line_ax

theorem has_points.exists_unique_point [has_points P L] (l₁ l₂ : L) (hl : l₁ ≠ l₂) : ∃! p, p ∈ l₁ ∧ p ∈ l₂ :=
  ⟨mk_point hl, mk_point_ax hl, fun p hp => (eq_or_eq hp.1 (mk_point_ax hl).1 hp.2 (mk_point_ax hl).2).resolve_right hl⟩

theorem has_lines.exists_unique_line [has_lines P L] (p₁ p₂ : P) (hp : p₁ ≠ p₂) : ∃! l : L, p₁ ∈ l ∧ p₂ ∈ l :=
  has_points.exists_unique_point (dual L) (dual P) p₁ p₂ hp

variable {P L}

/-- If a nondegenerate configuration has at least as many points as lines, then there exists
  an injective function `f` from lines to points, such that `f l` does not lie on `l`. -/
theorem nondegenerate.exists_injective_of_card_le [nondegenerate P L] [Fintype P] [Fintype L]
    (h : Fintype.card L ≤ Fintype.card P) : ∃ f : L → P, Function.Injective f ∧ ∀ l, f l ∉ l := by
  classical
  let t : L → Finset P := fun l => Set.toFinset { p | p ∉ l }
  suffices ∀ s : Finset L, s.card ≤ (s.bUnion t).card by
    obtain ⟨f, hf1, hf2⟩ := (Finset.all_card_le_bUnion_card_iff_exists_injective t).mp this
    exact ⟨f, hf1, fun l => set.mem_to_finset.mp (hf2 l)⟩
  intro s
  by_cases' hs₀ : s.card = 0
  · simp_rw [hs₀, zero_le]
    
  by_cases' hs₁ : s.card = 1
  · obtain ⟨l, rfl⟩ := finset.card_eq_one.mp hs₁
    obtain ⟨p, hl⟩ := exists_point l
    rw [Finset.card_singleton, Finset.singleton_bUnion, Nat.one_le_iff_ne_zero]
    exact Finset.card_ne_zero_of_mem (set.mem_to_finset.mpr hl)
    
  suffices s.bUnion tᶜ.card ≤ sᶜ.card by
    rw [Finset.card_compl, Finset.card_compl, tsub_le_iff_left] at this
    replace := h.trans this
    rwa [← add_tsub_assoc_of_le s.card_le_univ, le_tsub_iff_left (le_add_left s.card_le_univ), add_le_add_iff_right] at
      this
  have hs₂ : s.bUnion tᶜ.card ≤ 1 := by
    refine' finset.card_le_one_iff.mpr fun p₁ p₂ hp₁ hp₂ => _
    simp_rw [Finset.mem_compl, Finset.mem_bUnion, exists_prop, not_exists, not_and, Set.mem_to_finset,
      Set.mem_set_of_eq, not_not]  at hp₁ hp₂
    obtain ⟨l₁, l₂, hl₁, hl₂, hl₃⟩ := finset.one_lt_card_iff.mp (nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hs₀, hs₁⟩)
    exact (eq_or_eq (hp₁ l₁ hl₁) (hp₂ l₁ hl₁) (hp₁ l₂ hl₂) (hp₂ l₂ hl₂)).resolve_right hl₃
  by_cases' hs₃ : sᶜ.card = 0
  · rw [hs₃, Nat.le_zero_iffₓ]
    rw [Finset.card_compl, tsub_eq_zero_iff_le, LE.le.le_iff_eq (Finset.card_le_univ _), eq_comm,
      Finset.card_eq_iff_eq_univ, hs₃, Finset.eq_univ_iff_forall] at hs₃⊢
    exact fun p =>
      Exists.elim (exists_line p) fun l hl => finset.mem_bUnion.mpr ⟨l, Finset.mem_univ l, set.mem_to_finset.mpr hl⟩
    
  · exact hs₂.trans (nat.one_le_iff_ne_zero.mpr hs₃)
    

variable {P} (L)

/-- Number of points on a given line. -/
noncomputable def line_count (p : P) : ℕ :=
  Nat.card { l : L // p ∈ l }

variable (P) {L}

/-- Number of lines through a given point. -/
noncomputable def point_count (l : L) : ℕ :=
  Nat.card { p : P // p ∈ l }

variable (P L)

theorem sum_line_count_eq_sum_point_count [Fintype P] [Fintype L] :
    (∑ p : P, line_count L p) = ∑ l : L, point_count P l := by
  classical
  simp only [line_count, point_count, Nat.card_eq_fintype_card, ← Fintype.card_sigma]
  apply Fintype.card_congr
  calc (Σ p, { l : L // p ∈ l }) ≃ { x : P × L // x.1 ∈ x.2 } :=
      (Equivₓ.subtypeProdEquivSigmaSubtype (· ∈ ·)).symm _ ≃ { x : L × P // x.2 ∈ x.1 } :=
      (Equivₓ.prodComm P L).subtypeEquiv fun x => Iff.rfl _ ≃ Σ l, { p // p ∈ l } :=
      Equivₓ.subtypeProdEquivSigmaSubtype fun l : L p : P => p ∈ l

variable {P L}

theorem has_lines.point_count_le_line_count [has_lines P L] {p : P} {l : L} (h : p ∉ l) [Fintype { l : L // p ∈ l }] :
    point_count P l ≤ line_count L p := by
  by_cases' hf : Infinite { p : P // p ∈ l }
  · exact (le_of_eqₓ Nat.card_eq_zero_of_infinite).trans (zero_le (line_count L p))
    
  have := fintypeOfNotInfinite hf
  rw [line_count, point_count, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have : ∀ p' : { p // p ∈ l }, p ≠ p' := fun p' hp' => h ((congr_argₓ (· ∈ l) hp').mpr p'.2)
  exact
    Fintype.card_le_of_injective (fun p' => ⟨mk_line (this p'), (mk_line_ax (this p')).1⟩) fun p₁ p₂ hp =>
      Subtype.ext
        ((eq_or_eq p₁.2 p₂.2 (mk_line_ax (this p₁)).2
              ((congr_argₓ _ (subtype.ext_iff.mp hp)).mpr (mk_line_ax (this p₂)).2)).resolve_right
          fun h' => (congr_argₓ _ h').mp h (mk_line_ax (this p₁)).1)

theorem has_points.line_count_le_point_count [has_points P L] {p : P} {l : L} (h : p ∉ l)
    [hf : Fintype { p : P // p ∈ l }] : line_count L p ≤ point_count P l :=
  @has_lines.point_count_le_line_count (dual L) (dual P) _ _ l p h hf

variable (P L)

/-- If a nondegenerate configuration has a unique line through any two points, then `|P| ≤ |L|`. -/
theorem has_lines.card_le [has_lines P L] [Fintype P] [Fintype L] : Fintype.card P ≤ Fintype.card L := by
  classical
  by_contra hc₂
  obtain ⟨f, hf₁, hf₂⟩ := nondegenerate.exists_injective_of_card_le (le_of_not_leₓ hc₂)
  have :=
    calc
      (∑ p, line_count L p) = ∑ l, point_count P l := sum_line_count_eq_sum_point_count P L
      _ ≤ ∑ l, line_count L (f l) := Finset.sum_le_sum fun l hl => has_lines.point_count_le_line_count (hf₂ l)
      _ = ∑ p in finset.univ.image f, line_count L p :=
        Finset.sum_bij (fun l hl => f l) (fun l hl => Finset.mem_image_of_mem f hl) (fun l hl => rfl)
          (fun l₁ l₂ hl₁ hl₂ hl₃ => hf₁ hl₃) fun p => by
          simp_rw [Finset.mem_image, eq_comm, imp_self]
      _ < ∑ p, line_count L p := _
      
  · exact lt_irreflₓ _ this
    
  · obtain ⟨p, hp⟩ := not_forall.mp (mt (Fintype.card_le_of_surjective f) hc₂)
    refine'
      Finset.sum_lt_sum_of_subset (finset.univ.image f).subset_univ (Finset.mem_univ p) _ _ fun p hp₁ hp₂ =>
        zero_le (line_count L p)
    · simpa only [Finset.mem_image, exists_prop, Finset.mem_univ, true_andₓ]
      
    · rw [line_count, Nat.card_eq_fintype_card, Fintype.card_pos_iff]
      obtain ⟨l, hl⟩ := @exists_line P L _ _ p
      exact
        let this := not_exists.mp hp l
        ⟨⟨mk_line this, (mk_line_ax this).2⟩⟩
      
    

/-- If a nondegenerate configuration has a unique point on any two lines, then `|L| ≤ |P|`. -/
theorem has_points.card_le [has_points P L] [Fintype P] [Fintype L] : Fintype.card L ≤ Fintype.card P :=
  @has_lines.card_le (dual L) (dual P) _ _ _ _

variable {P L}

theorem has_lines.exists_bijective_of_card_eq [has_lines P L] [Fintype P] [Fintype L]
    (h : Fintype.card P = Fintype.card L) :
    ∃ f : L → P, Function.Bijective f ∧ ∀ l, point_count P l = line_count L (f l) := by
  classical
  obtain ⟨f, hf1, hf2⟩ := nondegenerate.exists_injective_of_card_le (ge_of_eq h)
  have hf3 := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf1, h.symm⟩
  refine'
    ⟨f, hf3, fun l =>
      (Finset.sum_eq_sum_iff_of_le fun l hl => has_lines.point_count_le_line_count (hf2 l)).mp
        ((sum_line_count_eq_sum_point_count P L).symm.trans
          (Finset.sum_bij (fun l hl => f l) (fun l hl => Finset.mem_univ (f l)) (fun l hl => refl (line_count L (f l)))
              (fun l₁ l₂ hl₁ hl₂ hl => hf1 hl) fun p hp => _).symm)
        l (Finset.mem_univ l)⟩
  obtain ⟨l, rfl⟩ := hf3.2 p
  exact ⟨l, Finset.mem_univ l, rfl⟩

theorem has_lines.line_count_eq_point_count [has_lines P L] [Fintype P] [Fintype L]
    (hPL : Fintype.card P = Fintype.card L) {p : P} {l : L} (hpl : p ∉ l) : line_count L p = point_count P l := by
  classical
  obtain ⟨f, hf1, hf2⟩ := has_lines.exists_bijective_of_card_eq hPL
  let s : Finset (P × L) := Set.toFinset { i | i.1 ∈ i.2 }
  have step1 : (∑ i : P × L, line_count L i.1) = ∑ i : P × L, point_count P i.2 := by
    rw [← Finset.univ_product_univ, Finset.sum_product_right, Finset.sum_product]
    simp_rw [Finset.sum_const, Finset.card_univ, hPL, sum_line_count_eq_sum_point_count]
  have step2 : (∑ i in s, line_count L i.1) = ∑ i in s, point_count P i.2 := by
    rw [s.sum_finset_product Finset.univ fun p => Set.toFinset { l | p ∈ l }]
    rw [s.sum_finset_product_right Finset.univ fun l => Set.toFinset { p | p ∈ l }]
    refine'
      (Finset.sum_bij (fun l hl => f l) (fun l hl => Finset.mem_univ (f l)) (fun l hl => _) (fun _ _ _ _ h => hf1.1 h)
          fun p hp => _).symm
    · simp_rw [Finset.sum_const, Set.to_finset_card, ← Nat.card_eq_fintype_card]
      change point_count P l • point_count P l = line_count L (f l) • line_count L (f l)
      rw [hf2]
      
    · obtain ⟨l, hl⟩ := hf1.2 p
      exact ⟨l, Finset.mem_univ l, hl.symm⟩
      
    all_goals
      simp_rw [Finset.mem_univ, true_andₓ, Set.mem_to_finset]
      exact fun p => Iff.rfl
  have step3 : (∑ i in sᶜ, line_count L i.1) = ∑ i in sᶜ, point_count P i.2 := by
    rwa [← s.sum_add_sum_compl, ← s.sum_add_sum_compl, step2, add_left_cancel_iffₓ] at step1
  rw [← Set.to_finset_compl] at step3
  exact
    ((Finset.sum_eq_sum_iff_of_le fun i hi => has_lines.point_count_le_line_count (set.mem_to_finset.mp hi)).mp
        step3.symm (p, l) (set.mem_to_finset.mpr hpl)).symm

theorem has_points.line_count_eq_point_count [has_points P L] [Fintype P] [Fintype L]
    (hPL : Fintype.card P = Fintype.card L) {p : P} {l : L} (hpl : p ∉ l) : line_count L p = point_count P l :=
  (@has_lines.line_count_eq_point_count (dual L) (dual P) _ _ _ _ hPL.symm l p hpl).symm

/-- If a nondegenerate configuration has a unique line through any two points, and if `|P| = |L|`,
  then there is a unique point on any two lines. -/
noncomputable def has_lines.has_points [has_lines P L] [Fintype P] [Fintype L] (h : Fintype.card P = Fintype.card L) :
    has_points P L :=
  let this : ∀ l₁ l₂ : L, l₁ ≠ l₂ → ∃ p : P, p ∈ l₁ ∧ p ∈ l₂ := fun l₁ l₂ hl => by
    classical
    obtain ⟨f, hf1, hf2⟩ := has_lines.exists_bijective_of_card_eq h
    have : Nontrivial L := ⟨⟨l₁, l₂, hl⟩⟩
    have := fintype.one_lt_card_iff_nontrivial.mp ((congr_argₓ _ h).mpr Fintype.one_lt_card)
    have h₁ : ∀ p : P, 0 < line_count L p := fun p =>
      Exists.elim (exists_ne p) fun q hq =>
        (congr_argₓ _ Nat.card_eq_fintype_card).mpr (fintype.card_pos_iff.mpr ⟨⟨mk_line hq, (mk_line_ax hq).2⟩⟩)
    have h₂ : ∀ l : L, 0 < point_count P l := fun l => (congr_argₓ _ (hf2 l)).mpr (h₁ (f l))
    obtain ⟨p, hl₁⟩ := fintype.card_pos_iff.mp ((congr_argₓ _ Nat.card_eq_fintype_card).mp (h₂ l₁))
    by_cases' hl₂ : p ∈ l₂
    exact ⟨p, hl₁, hl₂⟩
    have key' : Fintype.card { q : P // q ∈ l₂ } = Fintype.card { l : L // p ∈ l } :=
      ((has_lines.line_count_eq_point_count h hl₂).trans Nat.card_eq_fintype_card).symm.trans Nat.card_eq_fintype_card
    have : ∀ q : { q // q ∈ l₂ }, p ≠ q := fun q hq => hl₂ ((congr_argₓ (· ∈ l₂) hq).mpr q.2)
    let f : { q : P // q ∈ l₂ } → { l : L // p ∈ l } := fun q => ⟨mk_line (this q), (mk_line_ax (this q)).1⟩
    have hf : Function.Injective f := fun q₁ q₂ hq =>
      Subtype.ext
        ((eq_or_eq q₁.2 q₂.2 (mk_line_ax (this q₁)).2
              ((congr_argₓ _ (subtype.ext_iff.mp hq)).mpr (mk_line_ax (this q₂)).2)).resolve_right
          fun h => (congr_argₓ _ h).mp hl₂ (mk_line_ax (this q₁)).1)
    have key' := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, key'⟩).2
    obtain ⟨q, hq⟩ := key' ⟨l₁, hl₁⟩
    exact ⟨q, (congr_argₓ _ (subtype.ext_iff.mp hq)).mp (mk_line_ax (this q)).2, q.2⟩
  { mkPoint := fun l₁ l₂ hl => Classical.some (this l₁ l₂ hl),
    mk_point_ax := fun l₁ l₂ hl => Classical.some_spec (this l₁ l₂ hl) }

/-- If a nondegenerate configuration has a unique point on any two lines, and if `|P| = |L|`,
  then there is a unique line through any two points. -/
noncomputable def has_points.has_lines [has_points P L] [Fintype P] [Fintype L] (h : Fintype.card P = Fintype.card L) :
    has_lines P L :=
  let this := @has_lines.has_points (dual L) (dual P) _ _ _ _ h.symm
  { mkLine := this.mk_point, mk_line_ax := this.mk_point_ax }

variable (P L)

/-- A projective plane is a nondegenerate configuration in which every pair of lines has
  an intersection point, every pair of points has a line through them,
  and which has three points in general position. -/
class projective_plane extends nondegenerate P L : Type u where
  mkPoint : ∀ {l₁ l₂ : L} h : l₁ ≠ l₂, P
  mk_point_ax : ∀ {l₁ l₂ : L} h : l₁ ≠ l₂, mk_point h ∈ l₁ ∧ mk_point h ∈ l₂
  mkLine : ∀ {p₁ p₂ : P} h : p₁ ≠ p₂, L
  mk_line_ax : ∀ {p₁ p₂ : P} h : p₁ ≠ p₂, p₁ ∈ mk_line h ∧ p₂ ∈ mk_line h
  exists_config :
    ∃ (p₁ p₂ p₃ : P)(l₁ l₂ l₃ : L), p₁ ∉ l₂ ∧ p₁ ∉ l₃ ∧ p₂ ∉ l₁ ∧ p₂ ∈ l₂ ∧ p₂ ∈ l₃ ∧ p₃ ∉ l₁ ∧ p₃ ∈ l₂ ∧ p₃ ∉ l₃

namespace ProjectivePlane

instance (priority := 100) has_points [h : projective_plane P L] : has_points P L :=
  { h with }

instance (priority := 100) has_lines [h : projective_plane P L] : has_lines P L :=
  { h with }

instance [projective_plane P L] : projective_plane (dual L) (dual P) :=
  { dual.nondegenerate P L with mkLine := @mk_point P L _ _, mk_line_ax := fun _ _ => mk_point_ax,
    mkPoint := @mk_line P L _ _, mk_point_ax := fun _ _ => mk_line_ax,
    exists_config := by
      obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _
      exact ⟨l₁, l₂, l₃, p₁, p₂, p₃, h₂₁, h₃₁, h₁₂, h₂₂, h₃₂, h₁₃, h₂₃, h₃₃⟩ }

/-- The order of a projective plane is one less than the number of lines through an arbitrary point.
Equivalently, it is one less than the number of points on an arbitrary line. -/
noncomputable def order [projective_plane P L] : ℕ :=
  line_count L (Classical.some (@exists_config P L _ _)) - 1

variable [Fintype P] [Fintype L]

theorem card_points_eq_card_lines [projective_plane P L] : Fintype.card P = Fintype.card L :=
  le_antisymmₓ (has_lines.card_le P L) (has_points.card_le P L)

variable {P} (L)

theorem line_count_eq_line_count [projective_plane P L] (p q : P) : line_count L p = line_count L q := by
  obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := exists_config
  have h := card_points_eq_card_lines P L
  let n := line_count L p₂
  have hp₂ : line_count L p₂ = n := rfl
  have hl₁ : point_count P l₁ = n := (has_lines.line_count_eq_point_count h h₂₁).symm.trans hp₂
  have hp₃ : line_count L p₃ = n := (has_lines.line_count_eq_point_count h h₃₁).trans hl₁
  have hl₃ : point_count P l₃ = n := (has_lines.line_count_eq_point_count h h₃₃).symm.trans hp₃
  have hp₁ : line_count L p₁ = n := (has_lines.line_count_eq_point_count h h₁₃).trans hl₃
  have hl₂ : point_count P l₂ = n := (has_lines.line_count_eq_point_count h h₁₂).symm.trans hp₁
  suffices ∀ p : P, line_count L p = n by
    exact (this p).trans (this q).symm
  refine' fun p => or_not.elim (fun h₂ => _) fun h₂ => (has_lines.line_count_eq_point_count h h₂).trans hl₂
  refine' or_not.elim (fun h₃ => _) fun h₃ => (has_lines.line_count_eq_point_count h h₃).trans hl₃
  rwa [(eq_or_eq h₂ h₂₂ h₃ h₂₃).resolve_right fun h => h₃₃ ((congr_argₓ (HasMem.Mem p₃) h).mp h₃₂)]

variable (P) {L}

theorem point_count_eq_point_count [projective_plane P L] (l m : L) : point_count P l = point_count P m :=
  line_count_eq_line_count (dual P) l m

variable {P L}

theorem line_count_eq_point_count [projective_plane P L] (p : P) (l : L) : line_count L p = point_count P l :=
  Exists.elim (exists_point l) fun q hq =>
    (line_count_eq_line_count L p q).trans (has_lines.line_count_eq_point_count (card_points_eq_card_lines P L) hq)

variable (P L)

theorem dual.order [projective_plane P L] : order (dual L) (dual P) = order P L :=
  congr_argₓ (fun n => n - 1) (line_count_eq_point_count _ _)

variable {P} (L)

theorem line_count_eq [projective_plane P L] (p : P) : line_count L p = order P L + 1 := by
  classical
  obtain ⟨q, -, -, l, -, -, -, -, h, -⟩ := Classical.some_spec (@exists_config P L _ _)
  rw [order, line_count_eq_line_count L p q, line_count_eq_line_count L (Classical.some _) q, line_count,
    Nat.card_eq_fintype_card, Nat.sub_add_cancelₓ]
  exact fintype.card_pos_iff.mpr ⟨⟨l, h⟩⟩

variable (P) {L}

theorem point_count_eq [projective_plane P L] (l : L) : point_count P l = order P L + 1 :=
  (line_count_eq (dual P) l).trans (congr_argₓ (fun n => n + 1) (dual.order P L))

variable (P L)

theorem one_lt_order [projective_plane P L] : 1 < order P L := by
  obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, -, -, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _
  classical
  rw [← add_lt_add_iff_right, ← point_count_eq, point_count, Nat.card_eq_fintype_card]
  simp_rw [Fintype.two_lt_card_iff, Ne, Subtype.ext_iff]
  have h := mk_point_ax fun h => h₂₁ ((congr_argₓ _ h).mpr h₂₂)
  exact
    ⟨⟨mk_point _, h.2⟩, ⟨p₂, h₂₂⟩, ⟨p₃, h₃₂⟩, ne_of_mem_of_not_mem h.1 h₂₁, ne_of_mem_of_not_mem h.1 h₃₁,
      ne_of_mem_of_not_mem h₂₃ h₃₃⟩

variable {P} (L)

theorem two_lt_line_count [projective_plane P L] (p : P) : 2 < line_count L p := by
  simpa only [line_count_eq L p, Nat.succ_lt_succ_iff] using one_lt_order P L

variable (P) {L}

theorem two_lt_point_count [projective_plane P L] (l : L) : 2 < point_count P l := by
  simpa only [point_count_eq P l, Nat.succ_lt_succ_iff] using one_lt_order P L

end ProjectivePlane

end Configuration

