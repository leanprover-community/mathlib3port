import Mathbin.GroupTheory.GeneralCommutator
import Mathbin.GroupTheory.QuotientGroup

/-!

# Nilpotent groups

An API for nilpotent groups, that is, groups for which the upper central series
reaches `⊤`.

## Main definitions

Recall that if `H K : subgroup G` then `⁅H, K⁆ : subgroup G` is the subgroup of `G` generated
by the commutators `hkh⁻¹k⁻¹`. Recall also Lean's conventions that `⊤` denotes the
subgroup `G` of `G`, and `⊥` denotes the trivial subgroup `{1}`.

* `upper_central_series G : ℕ → subgroup G` : the upper central series of a group `G`.
     This is an increasing sequence of normal subgroups `H n` of `G` with `H 0 = ⊥` and
     `H (n + 1) / H n` is the centre of `G / H n`.
* `lower_central_series G : ℕ → subgroup G` : the lower central series of a group `G`.
     This is a decreasing sequence of normal subgroups `H n` of `G` with `H 0 = ⊤` and
     `H (n + 1) = ⁅H n, G⁆`.
* `is_nilpotent` : A group G is nilpotent if its upper central series reaches `⊤`, or
    equivalently if its lower central series reaches `⊥`.
* `nilpotency_class` : the length of the upper central series of a nilpotent group.
* `is_ascending_central_series (H : ℕ → subgroup G) : Prop` and
* `is_descending_central_series (H : ℕ → subgroup G) : Prop` : Note that in the literature
    a "central series" for a group is usually defined to be a *finite* sequence of normal subgroups
    `H 0`, `H 1`, ..., starting at `⊤`, finishing at `⊥`, and with each `H n / H (n + 1)`
    central in `G / H (n + 1)`. In this formalisation it is convenient to have two weaker predicates
    on an infinite sequence of subgroups `H n` of `G`: we say a sequence is a *descending central
    series* if it starts at `G` and `⁅H n, ⊤⁆ ⊆ H (n + 1)` for all `n`. Note that this series
    may not terminate at `⊥`, and the `H i` need not be normal. Similarly a sequence is an
    *ascending central series* if `H 0 = ⊥` and `⁅H (n + 1), ⊤⁆ ⊆ H n` for all `n`, again with no
    requirement that the series reaches `⊤` or that the `H i` are normal.

## Main theorems

`G` is *defined* to be nilpotent if the upper central series reaches `⊤`.
* `nilpotent_iff_finite_ascending_central_series` : `G` is nilpotent iff some ascending central
    series reaches `⊤`.
* `nilpotent_iff_finite_descending_central_series` : `G` is nilpotent iff some descending central
    series reaches `⊥`.
* `nilpotent_iff_lower` : `G` is nilpotent iff the lower central series reaches `⊥`.

## Warning

A "central series" is usually defined to be a finite sequence of normal subgroups going
from `⊥` to `⊤` with the property that each subquotient is contained within the centre of
the associated quotient of `G`. This means that if `G` is not nilpotent, then
none of what we have called `upper_central_series G`, `lower_central_series G` or
the sequences satisfying `is_ascending_central_series` or `is_descending_central_series`
are actually central series. Note that the fact that the upper and lower central series
are not central series if `G` is not nilpotent is a standard abuse of notation.

-/


open Subgroup

variable {G : Type _} [Groupₓ G] (H : Subgroup G) [normal H]

/-- If `H` is a normal subgroup of `G`, then the set `{x : G | ∀ y : G, x*y*x⁻¹*y⁻¹ ∈ H}`
is a subgroup of `G` (because it is the preimage in `G` of the centre of the
quotient group `G/H`.)
-/
def upperCentralSeriesStep : Subgroup G where
  Carrier := { x : G | ∀ y : G, x * y * x⁻¹ * y⁻¹ ∈ H }
  one_mem' := fun y => by
    simp [Subgroup.one_mem]
  mul_mem' := fun a b ha hb y => by
    convert Subgroup.mul_mem _ (ha (b * y * b⁻¹)) (hb y) using 1
    group
  inv_mem' := fun x hx y => by
    specialize hx (y⁻¹)
    rw [mul_assocₓ, inv_invₓ] at hx⊢
    exact Subgroup.Normal.mem_comm inferInstance hx

theorem mem_upper_central_series_step (x : G) : x ∈ upperCentralSeriesStep H ↔ ∀ y, x * y * x⁻¹ * y⁻¹ ∈ H :=
  Iff.rfl

open QuotientGroup

/-- The proof that `upper_central_series_step H` is the preimage of the centre of `G/H` under
the canonical surjection. -/
theorem upper_central_series_step_eq_comap_center :
    upperCentralSeriesStep H = Subgroup.comap (mk' H) (center (G ⧸ H)) := by
  ext
  rw [mem_comap, mem_center_iff, forall_coe]
  apply forall_congrₓ
  intro y
  change x * y * x⁻¹ * y⁻¹ ∈ H ↔ ((y * x : G) : G ⧸ H) = (x * y : G)
  rw [eq_comm, eq_iff_div_mem, div_eq_mul_inv]
  congr 2
  group

instance : normal (upperCentralSeriesStep H) := by
  rw [upper_central_series_step_eq_comap_center]
  infer_instance

variable (G)

/-- An auxiliary type-theoretic definition defining both the upper central series of
a group, and a proof that it is normal, all in one go. -/
def upperCentralSeriesAux : ℕ → Σ' H : Subgroup G, normal H
  | 0 => ⟨⊥, inferInstance⟩
  | n + 1 =>
    let un := upperCentralSeriesAux n
    let un_normal := un.2
    ⟨upperCentralSeriesStep un.1, inferInstance⟩

/-- `upper_central_series G n` is the `n`th term in the upper central series of `G`. -/
def upperCentralSeries (n : ℕ) : Subgroup G :=
  (upperCentralSeriesAux G n).1

instance (n : ℕ) : normal (upperCentralSeries G n) :=
  (upperCentralSeriesAux G n).2

@[simp]
theorem upper_central_series_zero : upperCentralSeries G 0 = ⊥ :=
  rfl

/-- The `n+1`st term of the upper central series `H i` has underlying set equal to the `x` such
that `⁅x,G⁆ ⊆ H n`-/
theorem mem_upper_central_series_succ_iff (n : ℕ) (x : G) :
    x ∈ upperCentralSeries G (n + 1) ↔ ∀ y : G, x * y * x⁻¹ * y⁻¹ ∈ upperCentralSeries G n :=
  Iff.rfl

/-- A group `G` is nilpotent if its upper central series is eventually `G`. -/
class Groupₓ.IsNilpotent (G : Type _) [Groupₓ G] : Prop where
  nilpotent {} : ∃ n : ℕ, upperCentralSeries G n = ⊤

open Groupₓ

section Classical

open_locale Classical

/-- The nilpotency class of a nilpotent group is the small natural `n` such that
the `n`'th term of the upper central series is `G`. -/
noncomputable def Groupₓ.nilpotencyClass (G : Type _) [Groupₓ G] [is_nilpotent G] : ℕ :=
  Nat.findₓ (is_nilpotent.nilpotent G)

end Classical

variable {G}

/-- A sequence of subgroups of `G` is an ascending central series if `H 0` is trivial and
  `⁅H (n + 1), G⁆ ⊆ H n` for all `n`. Note that we do not require that `H n = G` for some `n`. -/
def IsAscendingCentralSeries (H : ℕ → Subgroup G) : Prop :=
  H 0 = ⊥ ∧ ∀ x : G n : ℕ, x ∈ H (n + 1) → ∀ g, x * g * x⁻¹ * g⁻¹ ∈ H n

/-- A sequence of subgroups of `G` is a descending central series if `H 0` is `G` and
  `⁅H n, G⁆ ⊆ H (n + 1)` for all `n`. Note that we do not requre that `H n = {1}` for some `n`. -/
def IsDescendingCentralSeries (H : ℕ → Subgroup G) :=
  H 0 = ⊤ ∧ ∀ x : G n : ℕ, x ∈ H n → ∀ g, x * g * x⁻¹ * g⁻¹ ∈ H (n + 1)

/-- Any ascending central series for a group is bounded above by the upper central series. -/
theorem ascending_central_series_le_upper (H : ℕ → Subgroup G) (hH : IsAscendingCentralSeries H) :
    ∀ n : ℕ, H n ≤ upperCentralSeries G n
  | 0 => hH.1.symm ▸ le_reflₓ ⊥
  | n + 1 => by
    specialize ascending_central_series_le_upper n
    intro x hx
    have := hH.2 x n hx
    rw [mem_upper_central_series_succ_iff]
    intro y
    apply ascending_central_series_le_upper
    apply this

variable (G)

/-- The upper central series of a group is an ascending central series. -/
theorem upper_central_series_is_ascending_central_series : IsAscendingCentralSeries (upperCentralSeries G) :=
  ⟨rfl, fun x n h => h⟩

theorem upper_central_series_mono : Monotone (upperCentralSeries G) := by
  refine' monotone_nat_of_le_succ _
  intro n x hx y
  rw [mul_assocₓ, mul_assocₓ, ← mul_assocₓ y (x⁻¹) (y⁻¹)]
  exact
    mul_mem (upperCentralSeries G n) hx
      (normal.conj_mem (upperCentralSeries.Subgroup.normal G n) (x⁻¹) (inv_mem _ hx) y)

/-- A group `G` is nilpotent iff there exists an ascending central series which reaches `G` in
  finitely many steps. -/
theorem nilpotent_iff_finite_ascending_central_series :
    is_nilpotent G ↔ ∃ H : ℕ → Subgroup G, IsAscendingCentralSeries H ∧ ∃ n : ℕ, H n = ⊤ := by
  constructor
  · intro h
    use upperCentralSeries G
    refine' ⟨upper_central_series_is_ascending_central_series G, h.1⟩
    
  · rintro ⟨H, hH, n, hn⟩
    use n
    have := ascending_central_series_le_upper H hH n
    rw [hn] at this
    exact eq_top_iff.mpr this
    

/-- A group `G` is nilpotent iff there exists a descending central series which reaches the
  trivial group in a finite time. -/
theorem nilpotent_iff_finite_descending_central_series :
    is_nilpotent G ↔ ∃ H : ℕ → Subgroup G, IsDescendingCentralSeries H ∧ ∃ n : ℕ, H n = ⊥ := by
  rw [nilpotent_iff_finite_ascending_central_series]
  constructor
  · rintro ⟨H, ⟨h0, hH⟩, n, hn⟩
    use fun m => H (n - m)
    constructor
    · refine' ⟨hn, fun x m hx g => _⟩
      dsimp  at hx
      by_cases' hm : n ≤ m
      · have hnm : n - m = 0 := tsub_eq_zero_iff_le.mpr hm
        rw [hnm, h0, Subgroup.mem_bot] at hx
        subst hx
        convert Subgroup.one_mem _
        group
        
      · push_neg  at hm
        apply hH
        convert hx
        rw [Nat.sub_succ]
        exact Nat.succ_pred_eq_of_posₓ (tsub_pos_of_lt hm)
        
      
    · use n
      rwa [tsub_self]
      
    
  · rintro ⟨H, ⟨h0, hH⟩, n, hn⟩
    use fun m => H (n - m)
    constructor
    · refine' ⟨hn, fun x m hx g => _⟩
      dsimp only  at hx
      by_cases' hm : n ≤ m
      · have hnm : n - m = 0 := tsub_eq_zero_iff_le.mpr hm
        dsimp only
        rw [hnm, h0]
        exact mem_top _
        
      · push_neg  at hm
        dsimp only
        convert hH x _ hx g
        rw [Nat.sub_succ]
        exact (Nat.succ_pred_eq_of_posₓ (tsub_pos_of_lt hm)).symm
        
      
    · use n
      rwa [tsub_self]
      
    

/-- The lower central series of a group `G` is a sequence `H n` of subgroups of `G`, defined
  by `H 0` is all of `G` and for `n≥1`, `H (n + 1) = ⁅H n, G⁆` -/
def lowerCentralSeries (G : Type _) [Groupₓ G] : ℕ → Subgroup G
  | 0 => ⊤
  | n + 1 => ⁅lowerCentralSeries n,⊤⁆

variable {G}

@[simp]
theorem lower_central_series_zero : lowerCentralSeries G 0 = ⊤ :=
  rfl

theorem mem_lower_central_series_succ_iff (n : ℕ) (q : G) :
    q ∈ lowerCentralSeries G (n + 1) ↔
      q ∈ closure { x | ∃ p ∈ lowerCentralSeries G n, ∃ q ∈ (⊤ : Subgroup G), p * q * p⁻¹ * q⁻¹ = x } :=
  Iff.rfl

theorem lower_central_series_succ (n : ℕ) :
    lowerCentralSeries G (n + 1) =
      closure { x | ∃ p ∈ lowerCentralSeries G n, ∃ q ∈ (⊤ : Subgroup G), p * q * p⁻¹ * q⁻¹ = x } :=
  rfl

instance (n : ℕ) : normal (lowerCentralSeries G n) := by
  induction' n with d hd
  · exact (⊤ : Subgroup G).normal_of_characteristic
    
  · exact general_commutator_normal (lowerCentralSeries G d) ⊤
    

theorem lower_central_series_antitone : Antitone (lowerCentralSeries G) := by
  refine' antitone_nat_of_succ_le fun n x hx => _
  simp only [mem_lower_central_series_succ_iff, exists_prop, mem_top, exists_true_left, true_andₓ] at hx
  refine' closure_induction hx _ (Subgroup.one_mem _) (@Subgroup.mul_mem _ _ _) (@Subgroup.inv_mem _ _ _)
  rintro y ⟨z, hz, a, ha⟩
  rw [← ha, mul_assocₓ, mul_assocₓ, ← mul_assocₓ a (z⁻¹) (a⁻¹)]
  exact
    mul_mem (lowerCentralSeries G n) hz (normal.conj_mem (lowerCentralSeries.Subgroup.normal n) (z⁻¹) (inv_mem _ hz) a)

/-- The lower central series of a group is a descending central series. -/
theorem lower_central_series_is_descending_central_series : IsDescendingCentralSeries (lowerCentralSeries G) := by
  constructor
  rfl
  intro x n hxn g
  exact general_commutator_containment _ _ hxn (Subgroup.mem_top g)

/-- Any descending central series for a group is bounded below by the lower central series. -/
theorem descending_central_series_ge_lower (H : ℕ → Subgroup G) (hH : IsDescendingCentralSeries H) :
    ∀ n : ℕ, lowerCentralSeries G n ≤ H n
  | 0 => hH.1.symm ▸ le_reflₓ ⊤
  | n + 1 => by
    specialize descending_central_series_ge_lower n
    apply (general_commutator_le _ _ _).2
    intro x hx q _
    exact hH.2 x n (descending_central_series_ge_lower hx) q

/-- A group is nilpotent if and only if its lower central series eventually reaches
  the trivial subgroup. -/
theorem nilpotent_iff_lower_central_series : is_nilpotent G ↔ ∃ n, lowerCentralSeries G n = ⊥ := by
  rw [nilpotent_iff_finite_descending_central_series]
  constructor
  · rintro ⟨H, ⟨h0, hs⟩, n, hn⟩
    use n
    have := descending_central_series_ge_lower H ⟨h0, hs⟩ n
    rw [hn] at this
    exact eq_bot_iff.mpr this
    
  · intro h
    use lowerCentralSeries G, lower_central_series_is_descending_central_series, h
    

theorem lower_central_series_map_subtype_le (H : Subgroup G) (n : ℕ) :
    (lowerCentralSeries H n).map H.subtype ≤ lowerCentralSeries G n := by
  induction' n with d hd
  · simp
    
  · rw [lower_central_series_succ, lower_central_series_succ, MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro x1 ⟨x2, ⟨x3, hx3, x4, hx4, rfl⟩, rfl⟩
    exact
      ⟨x3, hd (mem_map.mpr ⟨x3, hx3, rfl⟩), x4, by
        simp ⟩
    

instance Subgroup.is_nilpotent (H : Subgroup G) [hG : is_nilpotent G] : is_nilpotent H := by
  rw [nilpotent_iff_lower_central_series] at *
  rcases hG with ⟨n, hG⟩
  use n
  have := lower_central_series_map_subtype_le H n
  simp only [hG, SetLike.le_def, mem_map, forall_apply_eq_imp_iff₂, exists_imp_distrib] at this
  exact eq_bot_iff.mpr fun x hx => Subtype.ext (this x hx)

instance (priority := 100) is_nilpotent_of_subsingleton [Subsingleton G] : is_nilpotent G :=
  nilpotent_iff_lower_central_series.2 ⟨0, Subsingleton.elimₓ ⊤ ⊥⟩

theorem upperCentralSeries.map {H : Type _} [Groupₓ H] {f : G →* H} (h : Function.Surjective f) (n : ℕ) :
    Subgroup.map f (upperCentralSeries G n) ≤ upperCentralSeries H n := by
  induction' n with d hd
  · simp
    
  · rintro _ ⟨x, hx : x ∈ upperCentralSeries G d.succ, rfl⟩ y'
    rcases h y' with ⟨y, rfl⟩
    simpa using hd (mem_map_of_mem f (hx y))
    

theorem lowerCentralSeries.map {H : Type _} [Groupₓ H] (f : G →* H) (n : ℕ) :
    Subgroup.map f (lowerCentralSeries G n) ≤ lowerCentralSeries H n := by
  induction' n with d hd
  · simp [Nat.nat_zero_eq_zero]
    
  · rintro a ⟨x, hx : x ∈ lowerCentralSeries G d.succ, rfl⟩
    refine'
      closure_induction hx _
        (by
          simp [f.map_one, Subgroup.one_mem _])
        (fun y z hy hz => by
          simp [MonoidHom.map_mul, Subgroup.mul_mem _ hy hz])
        fun y hy => by
        simp [f.map_inv, Subgroup.inv_mem _ hy]
    rintro a ⟨y, hy, z, ⟨-, rfl⟩⟩
    apply mem_closure.mpr
    exact fun K hK =>
      hK
        ⟨f y, hd (mem_map_of_mem f hy), by
          simp ⟩
    

theorem lower_central_series_succ_eq_bot {n : ℕ} (h : lowerCentralSeries G n ≤ center G) :
    lowerCentralSeries G (n + 1) = ⊥ := by
  rw [lower_central_series_succ, closure_eq_bot_iff, Set.subset_singleton_iff]
  rintro x ⟨y, hy1, z, ⟨⟩, rfl⟩
  symm
  rw [eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq, one_mulₓ]
  exact mem_center_iff.mp (h hy1) z

theorem is_nilpotent_of_ker_le_center {H : Type _} [Groupₓ H] {f : G →* H} (hf1 : f.ker ≤ center G)
    (hH : is_nilpotent H) : is_nilpotent G := by
  rw [nilpotent_iff_lower_central_series] at *
  rcases hH with ⟨n, hn⟩
  refine' ⟨n + 1, lower_central_series_succ_eq_bot (le_transₓ ((map_eq_bot_iff _).mp _) hf1)⟩
  exact eq_bot_iff.mpr (hn ▸ lowerCentralSeries.map f n)

