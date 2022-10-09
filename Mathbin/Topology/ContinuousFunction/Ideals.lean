/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathbin.Topology.Algebra.Algebra
import Mathbin.Topology.ContinuousFunction.Compact
import Mathbin.Topology.UrysohnsLemma
import Mathbin.Data.Complex.IsROrC

/-!
# Ideals of continuous functions

For a topological ring `R` and a topological space `X` there is a Galois connection between
`ideal C(X, R)` and `set X` given by sending each `I : ideal C(X, R)` to
`{x : X | ∀ f ∈ I, f x = 0}ᶜ` and mapping `s : set X` to the ideal with carrier
`{f : C(X, R) | ∀ x ∈ sᶜ, f x = 0}`, and we call these maps `continuous_map.set_of_ideal` and
`continuous_map.ideal_of_set`. As long as `R` is Hausdorff, `continuous_map.set_of_ideal I` is open,
and if, in addition, `X` is locally compact, then `continuous_map.set_of_ideal s` is closed.

When `R = 𝕜` with `is_R_or_C 𝕜` and `X` is compact Hausdorff, then this Galois connection can be
improved to a true Galois correspondence (i.e., order isomorphism) between the type `opens X` and
the subtype of closed ideals of `C(X, R)`.

## Main definitions

* `continuous_map.ideal_of_set`: ideal of functions which vanish on the complement of a set.
* `continuous_map.set_of_ideal`: complement of the set on which all functions in the ideal vanish.
* `continuous_map.opens_of_ideal`: `continuous_map.set_of_ideal` as a term of `opens X`.
* `continuous_map.ideal_opens_gi`: The Galois insertion `continuous_map.opens_of_ideal` and
  `λ s, continuous_map.ideal_of_set ↑s`.

## Main statements

* `ideal_of_set_of_ideal_eq_closure`: when `X` is compact Hausdorff and `is_R_or_C 𝕜`,
  `ideal_of_set 𝕜 (set_of_ideal I) = I.closure` for any ideal `I : ideal C(X, 𝕜)`.
* `set_of_ideal_of_set_eq_interior`: when `X` is compact Hausdorff and `is_R_or_C 𝕜`,
  `set_of_ideal (ideal_of_set 𝕜 s) = interior s` for any `s : set X`.

## Implementation details

Because there does not currently exist a bundled type of closed ideals, we don't provide the actual
order isomorphism described above, and instead we only consider the Galois insertion
`continuous_map.ideal_opens_gi`.

## TODO

* Show that maximal ideals in `C(X, 𝕜)` correspond to (complements of) singletons.

## Tags

ideal, continuous function, compact, Hausdorff
-/


open Nnreal

namespace ContinuousMap

open TopologicalSpace

section TopologicalRing

variable {X R : Type _} [TopologicalSpace X] [Ringₓ R] [TopologicalSpace R] [TopologicalRing R]

variable (R)

/-- Given a topological ring `R` and `s : set X`, construct the ideal in `C(X, R)` of functions
which vanish on the complement of `s`. -/
def idealOfSet (s : Set X) : Ideal C(X, R) where
  Carrier := { f : C(X, R) | ∀ x ∈ sᶜ, f x = 0 }
  add_mem' := fun f g hf hg x hx => by simp only [hf x hx, hg x hx, coe_add, Pi.add_apply, add_zeroₓ]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c f hf x hx => mul_zero (c x) ▸ congr_arg (fun y => c x * y) (hf x hx)

theorem ideal_of_set_closed [LocallyCompactSpace X] [T2Space R] (s : Set X) : IsClosed (idealOfSet R s : Set C(X, R)) :=
  by
  simp only [ideal_of_set, Submodule.coe_set_mk, Set.set_of_forall]
  exact is_closed_Inter fun x => is_closed_Inter fun hx => is_closed_eq (continuous_eval_const' x) continuous_const

variable {R}

theorem mem_ideal_of_set {s : Set X} {f : C(X, R)} : f ∈ idealOfSet R s ↔ ∀ ⦃x : X⦄, x ∈ sᶜ → f x = 0 :=
  Iff.rfl

theorem not_mem_ideal_of_set {s : Set X} {f : C(X, R)} : f ∉ idealOfSet R s ↔ ∃ x ∈ sᶜ, f x ≠ 0 := by
  simp_rw [mem_ideal_of_set, exists_propₓ]
  push_neg

/-- Given an ideal `I` of `C(X, R)`, construct the set of points for which every function in the
ideal vanishes on the complement. -/
def SetOfIdeal (I : Ideal C(X, R)) : Set X :=
  { x : X | ∀ f ∈ I, (f : C(X, R)) x = 0 }ᶜ

theorem not_mem_set_of_ideal {I : Ideal C(X, R)} {x : X} : x ∉ SetOfIdeal I ↔ ∀ ⦃f : C(X, R)⦄, f ∈ I → f x = 0 := by
  rw [← Set.mem_compl_iff, set_of_ideal, compl_compl, Set.mem_set_of]

theorem mem_set_of_ideal {I : Ideal C(X, R)} {x : X} : x ∈ SetOfIdeal I ↔ ∃ f ∈ I, (f : C(X, R)) x ≠ 0 := by
  simp_rw [set_of_ideal, Set.mem_compl_iff, Set.mem_set_of, exists_propₓ]
  push_neg

theorem set_of_ideal_open [T2Space R] (I : Ideal C(X, R)) : IsOpen (SetOfIdeal I) := by
  simp only [set_of_ideal, Set.set_of_forall, is_open_compl_iff]
  exact is_closed_Inter fun f => is_closed_Inter fun hf => is_closed_eq (map_continuous f) continuous_const

/-- The open set `set_of_ideal I` realized as a term of `opens X`. -/
@[simps]
def opensOfIdeal [T2Space R] (I : Ideal C(X, R)) : Opens X :=
  ⟨SetOfIdeal I, set_of_ideal_open I⟩

@[simp]
theorem set_of_top_eq_univ [Nontrivial R] : SetOfIdeal (⊤ : Ideal C(X, R)) = Set.Univ :=
  Set.univ_subset_iff.mp fun x hx => mem_set_of_ideal.mpr ⟨1, Submodule.mem_top, one_ne_zero⟩

@[simp]
theorem ideal_of_empty_eq_bot : idealOfSet R (∅ : Set X) = ⊥ :=
  Ideal.ext fun f => by
    simpa only [mem_ideal_of_set, Set.compl_empty, Set.mem_univ, forall_true_left, Ideal.mem_bot, FunLike.ext_iff] using
      Iff.rfl

variable (X R)

theorem ideal_gc : GaloisConnection (SetOfIdeal : Ideal C(X, R) → Set X) (idealOfSet R) := by
  refine' fun I s => ⟨fun h f hf => _, fun h x hx => _⟩
  · by_contra h'
    rcases not_mem_ideal_of_set.mp h' with ⟨x, hx, hfx⟩
    exact hfx (not_mem_set_of_ideal.mp (mt (@h x) hx) hf)
    
  · obtain ⟨f, hf, hfx⟩ := mem_set_of_ideal.mp hx
    by_contra hx'
    exact not_mem_ideal_of_set.mpr ⟨x, hx', hfx⟩ (h hf)
    

end TopologicalRing

section IsROrC

open IsROrC

variable {X 𝕜 : Type _} [IsROrC 𝕜] [TopologicalSpace X]

/-- An auxiliary lemma used in the proof of `ideal_of_set_of_ideal_eq_closure` which may be useful
on its own. -/
theorem exists_mul_le_one_eq_on_ge (f : C(X, ℝ≥0)) {c : ℝ≥0} (hc : 0 < c) :
    ∃ g : C(X, ℝ≥0), (∀ x : X, (g * f) x ≤ 1) ∧ { x : X | c ≤ f x }.EqOn (g * f) 1 :=
  ⟨{ toFun := (f ⊔ const X c)⁻¹,
      continuous_to_fun := ((map_continuous f).sup <| map_continuous _).inv₀ fun _ => (hc.trans_le le_sup_right).ne' },
    fun x => (inv_mul_le_iff (hc.trans_le le_sup_right)).mpr ((mul_oneₓ (f x ⊔ c)).symm ▸ le_sup_left), fun x hx => by
    simpa only [coe_const, coe_mk, Pi.mul_apply, Pi.inv_apply, Pi.sup_apply, Function.const_applyₓ, Pi.one_apply,
      sup_eq_left.mpr (set.mem_set_of.mp hx)] using inv_mul_cancel (hc.trans_le hx).ne'⟩

@[simp]
theorem ideal_of_set_of_ideal_eq_closure [CompactSpace X] [T2Space X] (I : Ideal C(X, 𝕜)) :
    idealOfSet 𝕜 (SetOfIdeal I) = I.closure := by
  /- Since `ideal_of_set 𝕜 (set_of_ideal I)` is closed and contains `I`, it contains `I.closure`.
    For the reverse inclusion, given `f ∈ ideal_of_set 𝕜 (set_of_ideal I)` and `(ε : ℝ≥0) > 0` it
    suffices to show that `f` is within `ε` of `I`.-/
  refine'
    le_antisymmₓ (fun f hf => metric.mem_closure_iff.mpr fun ε hε => _)
      ((ideal_of_set_closed 𝕜 <| set_of_ideal I).closure_subset_iff.mpr fun f hf x hx => not_mem_set_of_ideal.mp hx hf)
  lift ε to ℝ≥0 using hε.lt.le
  replace hε := show (0 : ℝ≥0) < ε from hε
  simp_rw [dist_nndist]
  norm_cast
  -- Let `t := {x : X | ε / 2 ≤ ∥f x∥₊}}` which is closed and disjoint from `set_of_ideal I`.
  set t := { x : X | ε / 2 ≤ ∥f x∥₊ }
  have ht : IsClosed t := is_closed_le continuous_const (map_continuous f).nnnorm
  have htI : Disjoint t (set_of_ideal Iᶜ) := by
    refine' set.subset_compl_iff_disjoint_left.mp fun x hx => _
    simpa only [t, Set.mem_set_of, Set.mem_compl_iff, not_leₓ] using
      (nnnorm_eq_zero.mpr (mem_ideal_of_set.mp hf hx)).trans_lt (half_pos hε)
  /- It suffices to produce `g : C(X, ℝ≥0)` which takes values in `[0,1]` and is constantly `1` on
    `t` such that when composed with the natural embedding of `ℝ≥0` into `𝕜` lies in the ideal `I`.
    Indeed, then `∥f - f * ↑g∥ ≤ ∥f * (1 - ↑g)∥ ≤ ⨆ ∥f * (1 - ↑g) x∥`. When `x ∉ t`, `∥f x∥ < ε / 2`
    and `∥(1 - ↑g) x∥ ≤ 1`, and when `x ∈ t`, `(1 - ↑g) x = 0`, and clearly `f * ↑g ∈ I`. -/
  suffices ∃ g : C(X, ℝ≥0), (algebraMapClm ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g ∈ I ∧ (∀ x, g x ≤ 1) ∧ t.eq_on g 1 by
    obtain ⟨g, hgI, hg, hgt⟩ := this
    refine' ⟨f * (algebraMapClm ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g, I.mul_mem_left f hgI, _⟩
    rw [nndist_eq_nnnorm]
    refine' (nnnorm_lt_iff _ hε).2 fun x => _
    simp only [coe_sub, coe_mul, Pi.sub_apply, Pi.mul_apply]
    by_cases hx:x ∈ t
    · simpa only [hgt hx, comp_apply, Pi.one_apply, ContinuousMap.coe_coe, algebra_map_clm_apply, map_one, mul_oneₓ,
        sub_self, nnnorm_zero] using hε
      
    · refine' lt_of_le_of_ltₓ _ (half_lt_self hε)
      have :=
        calc
          ∥((1 - (algebraMapClm ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g) x : 𝕜)∥₊ = ∥1 - algebraMap ℝ≥0 𝕜 (g x)∥₊ := by
            simp only [coe_sub, coe_one, coe_comp, ContinuousMap.coe_coe, Pi.sub_apply, Pi.one_apply, Function.comp_app,
              algebra_map_clm_apply]
          _ = ∥algebraMap ℝ≥0 𝕜 (1 - g x)∥₊ := by
            simp only [Algebra.algebra_map_eq_smul_one, Nnreal.smul_def, Nnreal.coe_sub (hg x), sub_smul,
              Nonneg.coe_one, one_smul]
          _ ≤ 1 := (nnnorm_algebra_map_nnreal 𝕜 (1 - g x)).trans_le tsub_le_self
          
      calc
        ∥f x - f x * (algebraMapClm ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g x∥₊ =
            ∥f x * (1 - (algebraMapClm ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g) x∥₊ :=
          by simp only [mul_sub, coe_sub, coe_one, Pi.sub_apply, Pi.one_apply, mul_oneₓ]
        _ ≤ ε / 2 * ∥(1 - (algebraMapClm ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g) x∥₊ :=
          (nnnorm_mul_le _ _).trans (mul_le_mul_right' (not_le.mp <| show ¬ε / 2 ≤ ∥f x∥₊ from hx).le _)
        _ ≤ ε / 2 := by simpa only [mul_oneₓ] using mul_le_mul_left' this _
        
      
  /- There is some `g' : C(X, ℝ≥0)` which is strictly positive on `t` such that the composition
    `↑g` with the natural embedding of `ℝ≥0` into `𝕜` lies in `I`. This follows from compactness of
    `t` and that we can do it in any neighborhood of a point `x ∈ t`. Indeed, since `x ∈ t`, then
    `fₓ x ≠ 0` for some `fₓ ∈ I` and so `λ y, ∥(star fₓ * fₓ) y∥₊` is strictly posiive in a
    neighborhood of `y`. Moreover, `(∥(star fₓ * fₓ) y∥₊ : 𝕜) = (star fₓ * fₓ) y`, so composition of
    this map with the natural embedding is just `star fₓ * fₓ ∈ I`. -/
  have : ∃ g' : C(X, ℝ≥0), (algebraMapClm ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g' ∈ I ∧ ∀ x ∈ t, 0 < g' x := by
    refine'
      @IsCompact.induction_on _ _ _ ht.is_compact
        (fun s => ∃ g' : C(X, ℝ≥0), (algebraMapClm ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g' ∈ I ∧ ∀ x ∈ s, 0 < g' x) _ _ _ _
    · refine' ⟨0, _, fun x hx => False.elim hx⟩
      convert I.zero_mem
      ext
      simp only [coe_zero, Pi.zero_apply, ContinuousMap.coe_coe, ContinuousMap.coe_comp, map_zero, Pi.comp_zero]
      
    · rintro s₁ s₂ hs ⟨g, hI, hgt⟩
      exact ⟨g, hI, fun x hx => hgt x (hs hx)⟩
      
    · rintro s₁ s₂ ⟨g₁, hI₁, hgt₁⟩ ⟨g₂, hI₂, hgt₂⟩
      refine' ⟨g₁ + g₂, _, fun x hx => _⟩
      · convert I.add_mem hI₁ hI₂
        ext y
        simp only [coe_add, Pi.add_apply, map_add, coe_comp, Function.comp_app, ContinuousMap.coe_coe]
        
      · rcases hx with (hx | hx)
        simpa only [zero_addₓ] using add_lt_add_of_lt_of_le (hgt₁ x hx) zero_le'
        simpa only [zero_addₓ] using add_lt_add_of_le_of_lt zero_le' (hgt₂ x hx)
        
      
    · intro x hx
      replace hx := htI.subset_compl_right hx
      rw [compl_compl, mem_set_of_ideal] at hx
      obtain ⟨g, hI, hgx⟩ := hx
      have := (map_continuous g).ContinuousAt.eventually_ne hgx
      refine'
        ⟨{ y : X | g y ≠ 0 } ∩ t, mem_nhds_within_iff_exists_mem_nhds_inter.mpr ⟨_, this, Set.Subset.rfl⟩,
          ⟨⟨fun x => ∥g x∥₊ ^ 2, (map_continuous g).nnnorm.pow 2⟩, _, fun x hx => pow_pos (norm_pos_iff.mpr hx.1) 2⟩⟩
      convert I.mul_mem_left (star g) hI
      ext
      simp only [comp_apply, coe_mk, algebra_map_clm_coe, map_pow, coe_mul, coe_star, Pi.mul_apply, Pi.star_apply,
        star_def, ContinuousMap.coe_coe]
      simpa only [norm_sq_eq_def', conj_mul_eq_norm_sq_left, of_real_pow]
      
  /- Get the function `g'` which is guaranteed to exist above. By the extreme value theorem and
    compactness of `t`, there is some `0 < c` such that `c ≤ g' x` for all `x ∈ t`. Then by
    `main_lemma_aux` there is some `g` for which `g * g'` is the desired function. -/
  obtain ⟨g', hI', hgt'⟩ := this
  obtain ⟨c, hc, hgc'⟩ : ∃ (c : _)(hc : 0 < c), ∀ y : X, y ∈ t → c ≤ g' y :=
    t.eq_empty_or_nonempty.elim (fun ht' => ⟨1, zero_lt_one, fun y hy => False.elim (by rwa [ht'] at hy)⟩) fun ht' =>
      let ⟨x, hx, hx'⟩ := ht.is_compact.exists_forall_le ht' (map_continuous g').ContinuousOn
      ⟨g' x, hgt' x hx, hx'⟩
  obtain ⟨g, hg, hgc⟩ := exists_mul_le_one_eq_on_ge g' hc
  refine' ⟨g * g', _, hg, hgc.mono hgc'⟩
  convert I.mul_mem_left ((algebraMapClm ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g) hI'
  ext
  simp only [algebra_map_clm_coe, ContinuousMap.coe_coe, comp_apply, coe_mul, Pi.mul_apply, map_mul]

theorem ideal_of_set_of_ideal_is_closed [CompactSpace X] [T2Space X] {I : Ideal C(X, 𝕜)}
    (hI : IsClosed (I : Set C(X, 𝕜))) : idealOfSet 𝕜 (SetOfIdeal I) = I :=
  (ideal_of_set_of_ideal_eq_closure I).trans (Ideal.ext <| Set.ext_iff.mp hI.closure_eq)

variable (𝕜)

@[simp]
theorem set_of_ideal_of_set_eq_interior [CompactSpace X] [T2Space X] (s : Set X) :
    SetOfIdeal (idealOfSet 𝕜 s) = Interior s := by
  refine'
    Set.Subset.antisymm
      ((set_of_ideal_open (ideal_of_set 𝕜 s)).subset_interior_iff.mpr fun x hx =>
        let ⟨f, hf, hfx⟩ := mem_set_of_ideal.mp hx
        set.not_mem_compl_iff.mp (mt (@hf x) hfx))
      fun x hx => _
  -- If `x ∉ closure sᶜ`, we must produce `f : C(X, 𝕜)` which is zero on `sᶜ` and `f x ≠ 0`.
  rw [← compl_compl (Interior s), ← closure_compl] at hx
  simp_rw [mem_set_of_ideal, mem_ideal_of_set]
  haveI : NormalSpace X := normal_of_compact_t2
  /- Apply Urysohn's lemma to get `g : C(X, ℝ)` which is zero on `sᶜ` and `g x ≠ 0`, then compose
    with the natural embedding `ℝ ↪ 𝕜` to produce the desired `f`. -/
  obtain ⟨g, hgs, hgx : Set.EqOn g 1 {x}, -⟩ :=
    exists_continuous_zero_one_of_closed is_closed_closure is_closed_singleton (set.disjoint_singleton_right.mpr hx)
  exact
    ⟨⟨fun x => g x, continuous_of_real.comp (map_continuous g)⟩, by
      simpa only [coe_mk, of_real_eq_zero] using fun x hx => hgs (subset_closure hx), by
      simpa only [coe_mk, hgx (Set.mem_singleton x), Pi.one_apply, IsROrC.of_real_one] using one_ne_zero⟩

theorem set_of_ideal_of_set_of_is_open [CompactSpace X] [T2Space X] {s : Set X} (hs : IsOpen s) :
    SetOfIdeal (idealOfSet 𝕜 s) = s :=
  (set_of_ideal_of_set_eq_interior 𝕜 s).trans hs.interior_eq

variable (X)

/-- The Galois insertion `continuous_map.opens_of_ideal : ideal C(X, 𝕜) → opens X` and
`λ s, continuous_map.ideal_of_set ↑s`. -/
@[simps]
def idealOpensGi [CompactSpace X] [T2Space X] :
    GaloisInsertion (opensOfIdeal : Ideal C(X, 𝕜) → Opens X) fun s => idealOfSet 𝕜 s where
  choice := fun I hI => opensOfIdeal I.closure
  gc := fun I s => ideal_gc X 𝕜 I s
  le_l_u := fun s => (set_of_ideal_of_set_of_is_open 𝕜 s.Prop).Ge
  choice_eq := fun I hI =>
    congr_arg _ <|
      Ideal.ext
        (Set.ext_iff.mp
          (is_closed_of_closure_subset <| (ideal_of_set_of_ideal_eq_closure I ▸ hI : I.closure ≤ I)).closure_eq)

end IsROrC

end ContinuousMap

