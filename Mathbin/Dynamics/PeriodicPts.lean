import Mathbin.Data.Nat.Prime 
import Mathbin.Dynamics.FixedPoints.Basic 
import Mathbin.Data.Pnat.Basic 
import Mathbin.Data.Set.Lattice

/-!
# Periodic points

A point `x : α` is a periodic point of `f : α → α` of period `n` if `f^[n] x = x`.

## Main definitions

* `is_periodic_pt f n x` : `x` is a periodic point of `f` of period `n`, i.e. `f^[n] x = x`.
  We do not require `n > 0` in the definition.
* `pts_of_period f n` : the set `{x | is_periodic_pt f n x}`. Note that `n` is not required to
  be the minimal period of `x`.
* `periodic_pts f` : the set of all periodic points of `f`.
* `minimal_period f x` : the minimal period of a point `x` under an endomorphism `f` or zero
  if `x` is not a periodic point of `f`.

## Main statements

We provide “dot syntax”-style operations on terms of the form `h : is_periodic_pt f n x` including
arithmetic operations on `n` and `h.map (hg : semiconj_by g f f')`. We also prove that `f`
is bijective on each set `pts_of_period f n` and on `periodic_pts f`. Finally, we prove that `x`
is a periodic point of `f` of period `n` if and only if `minimal_period f x | n`.

## References

* https://en.wikipedia.org/wiki/Periodic_point

-/


open Set

namespace Function

variable{α : Type _}{β : Type _}{f fa : α → α}{fb : β → β}{x y : α}{m n : ℕ}

/-- A point `x` is a periodic point of `f : α → α` of period `n` if `f^[n] x = x`.
Note that we do not require `0 < n` in this definition. Many theorems about periodic points
need this assumption. -/
def is_periodic_pt (f : α → α) (n : ℕ) (x : α) :=
  is_fixed_pt (f^[n]) x

/-- A fixed point of `f` is a periodic point of `f` of any prescribed period. -/
theorem is_fixed_pt.is_periodic_pt (hf : is_fixed_pt f x) (n : ℕ) : is_periodic_pt f n x :=
  hf.iterate n

/-- For the identity map, all points are periodic. -/
theorem is_periodic_id (n : ℕ) (x : α) : is_periodic_pt id n x :=
  (is_fixed_pt_id x).IsPeriodicPt n

/-- Any point is a periodic point of period `0`. -/
theorem is_periodic_pt_zero (f : α → α) (x : α) : is_periodic_pt f 0 x :=
  is_fixed_pt_id x

namespace IsPeriodicPt

instance  [DecidableEq α] {f : α → α} {n : ℕ} {x : α} : Decidable (is_periodic_pt f n x) :=
  is_fixed_pt.decidable

protected theorem is_fixed_pt (hf : is_periodic_pt f n x) : is_fixed_pt (f^[n]) x :=
  hf

protected theorem map (hx : is_periodic_pt fa n x) {g : α → β} (hg : semiconj g fa fb) : is_periodic_pt fb n (g x) :=
  hx.map (hg.iterate_right n)

theorem apply_iterate (hx : is_periodic_pt f n x) (m : ℕ) : is_periodic_pt f n ((f^[m]) x) :=
  hx.map$ commute.iterate_self f m

protected theorem apply (hx : is_periodic_pt f n x) : is_periodic_pt f n (f x) :=
  hx.apply_iterate 1

protected theorem add (hn : is_periodic_pt f n x) (hm : is_periodic_pt f m x) : is_periodic_pt f (n+m) x :=
  by 
    rw [is_periodic_pt, iterate_add]
    exact hn.comp hm

theorem left_of_add (hn : is_periodic_pt f (n+m) x) (hm : is_periodic_pt f m x) : is_periodic_pt f n x :=
  by 
    rw [is_periodic_pt, iterate_add] at hn 
    exact hn.left_of_comp hm

theorem right_of_add (hn : is_periodic_pt f (n+m) x) (hm : is_periodic_pt f n x) : is_periodic_pt f m x :=
  by 
    rw [add_commₓ] at hn 
    exact hn.left_of_add hm

protected theorem sub (hm : is_periodic_pt f m x) (hn : is_periodic_pt f n x) : is_periodic_pt f (m - n) x :=
  by 
    cases' le_totalₓ n m with h h
    ·
      refine' left_of_add _ hn 
      rwa [tsub_add_cancel_of_le h]
    ·
      rw [tsub_eq_zero_iff_le.mpr h]
      apply is_periodic_pt_zero

protected theorem mul_const (hm : is_periodic_pt f m x) (n : ℕ) : is_periodic_pt f (m*n) x :=
  by 
    simp only [is_periodic_pt, iterate_mul, hm.is_fixed_pt.iterate n]

protected theorem const_mul (hm : is_periodic_pt f m x) (n : ℕ) : is_periodic_pt f (n*m) x :=
  by 
    simp only [mul_commₓ n, hm.mul_const n]

theorem trans_dvd (hm : is_periodic_pt f m x) {n : ℕ} (hn : m ∣ n) : is_periodic_pt f n x :=
  let ⟨k, hk⟩ := hn 
  hk.symm ▸ hm.mul_const k

protected theorem iterate (hf : is_periodic_pt f n x) (m : ℕ) : is_periodic_pt (f^[m]) n x :=
  by 
    rw [is_periodic_pt, ←iterate_mul, mul_commₓ, iterate_mul]
    exact hf.is_fixed_pt.iterate m

protected theorem mod (hm : is_periodic_pt f m x) (hn : is_periodic_pt f n x) : is_periodic_pt f (m % n) x :=
  by 
    rw [←Nat.mod_add_divₓ m n] at hm 
    exact hm.left_of_add (hn.mul_const _)

protected theorem gcd (hm : is_periodic_pt f m x) (hn : is_periodic_pt f n x) : is_periodic_pt f (m.gcd n) x :=
  by 
    revert hm hn 
    refine' Nat.gcdₓ.induction m n (fun n h0 hn => _) fun m n hm ih hm hn => _
    ·
      rwa [Nat.gcd_zero_leftₓ]
    ·
      rw [Nat.gcd_recₓ]
      exact ih (hn.mod hm) hm

/-- If `f` sends two periodic points `x` and `y` of the same positive period to the same point,
then `x = y`. For a similar statement about points of different periods see `eq_of_apply_eq`. -/
theorem eq_of_apply_eq_same (hx : is_periodic_pt f n x) (hy : is_periodic_pt f n y) (hn : 0 < n) (h : f x = f y) :
  x = y :=
  by 
    rw [←hx.eq, ←hy.eq, ←iterate_pred_comp_of_pos f hn, comp_app, h]

/-- If `f` sends two periodic points `x` and `y` of positive periods to the same point,
then `x = y`. -/
theorem eq_of_apply_eq (hx : is_periodic_pt f m x) (hy : is_periodic_pt f n y) (hm : 0 < m) (hn : 0 < n)
  (h : f x = f y) : x = y :=
  (hx.mul_const n).eq_of_apply_eq_same (hy.const_mul m) (mul_pos hm hn) h

end IsPeriodicPt

/-- The set of periodic points of a given (possibly non-minimal) period. -/
def pts_of_period (f : α → α) (n : ℕ) : Set α :=
  { x:α | is_periodic_pt f n x }

@[simp]
theorem mem_pts_of_period : x ∈ pts_of_period f n ↔ is_periodic_pt f n x :=
  Iff.rfl

theorem semiconj.maps_to_pts_of_period {g : α → β} (h : semiconj g fa fb) (n : ℕ) :
  maps_to g (pts_of_period fa n) (pts_of_period fb n) :=
  (h.iterate_right n).maps_to_fixed_pts

theorem bij_on_pts_of_period (f : α → α) {n : ℕ} (hn : 0 < n) : bij_on f (pts_of_period f n) (pts_of_period f n) :=
  ⟨(Commute.refl f).maps_to_pts_of_period n, fun x hx y hy hxy => hx.eq_of_apply_eq_same hy hn hxy,
    fun x hx =>
      ⟨(f^[n.pred]) x, hx.apply_iterate _,
        by 
          rw [←comp_app f, comp_iterate_pred_of_pos f hn, hx.eq]⟩⟩

-- error in Dynamics.PeriodicPts: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem directed_pts_of_period_pnat (f : α → α) : directed ((«expr ⊆ »)) (λ n : «exprℕ+»(), pts_of_period f n) :=
λ m n, ⟨«expr * »(m, n), λ x hx, hx.mul_const n, λ x hx, hx.const_mul m⟩

/-- The set of periodic points of a map `f : α → α`. -/
def periodic_pts (f : α → α) : Set α :=
  { x:α | ∃ (n : _)(_ : n > 0), is_periodic_pt f n x }

theorem mk_mem_periodic_pts (hn : 0 < n) (hx : is_periodic_pt f n x) : x ∈ periodic_pts f :=
  ⟨n, hn, hx⟩

theorem mem_periodic_pts : x ∈ periodic_pts f ↔ ∃ (n : _)(_ : n > 0), is_periodic_pt f n x :=
  Iff.rfl

variable(f)

theorem bUnion_pts_of_period : (⋃(n : _)(_ : n > 0), pts_of_period f n) = periodic_pts f :=
  Set.ext$
    fun x =>
      by 
        simp [mem_periodic_pts]

theorem Union_pnat_pts_of_period : (⋃n : ℕ+, pts_of_period f n) = periodic_pts f :=
  supr_subtype.trans$ bUnion_pts_of_period f

theorem bij_on_periodic_pts : bij_on f (periodic_pts f) (periodic_pts f) :=
  Union_pnat_pts_of_period f ▸
    bij_on_Union_of_directed (directed_pts_of_period_pnat f) fun i => bij_on_pts_of_period f i.pos

variable{f}

theorem semiconj.maps_to_periodic_pts {g : α → β} (h : semiconj g fa fb) :
  maps_to g (periodic_pts fa) (periodic_pts fb) :=
  fun x ⟨n, hn, hx⟩ => ⟨n, hn, hx.map h⟩

open_locale Classical

noncomputable theory

/-- Minimal period of a point `x` under an endomorphism `f`. If `x` is not a periodic point of `f`,
then `minimal_period f x = 0`. -/
def minimal_period (f : α → α) (x : α) :=
  if h : x ∈ periodic_pts f then Nat.findₓ h else 0

theorem is_periodic_pt_minimal_period (f : α → α) (x : α) : is_periodic_pt f (minimal_period f x) x :=
  by 
    delta' minimal_period 
    splitIfs with hx
    ·
      exact (Nat.find_specₓ hx).snd
    ·
      exact is_periodic_pt_zero f x

theorem iterate_eq_mod_minimal_period : (f^[n]) x = (f^[n % minimal_period f x]) x :=
  by 
    convLHS => rw [←Nat.mod_add_divₓ n (minimal_period f x)]
    rw [iterate_add, mul_commₓ, iterate_mul, comp_app]
    congr 
    exact is_periodic_pt.iterate (is_periodic_pt_minimal_period _ _) _

theorem minimal_period_pos_of_mem_periodic_pts (hx : x ∈ periodic_pts f) : 0 < minimal_period f x :=
  by 
    simp only [minimal_period, dif_pos hx, gt_iff_lt.1 (Nat.find_specₓ hx).fst]

theorem is_periodic_pt.minimal_period_pos (hn : 0 < n) (hx : is_periodic_pt f n x) : 0 < minimal_period f x :=
  minimal_period_pos_of_mem_periodic_pts$ mk_mem_periodic_pts hn hx

theorem minimal_period_pos_iff_mem_periodic_pts : 0 < minimal_period f x ↔ x ∈ periodic_pts f :=
  ⟨not_imp_not.1$
      fun h =>
        by 
          simp only [minimal_period, dif_neg h, lt_irreflₓ 0, not_false_iff],
    minimal_period_pos_of_mem_periodic_pts⟩

theorem is_periodic_pt.minimal_period_le (hn : 0 < n) (hx : is_periodic_pt f n x) : minimal_period f x ≤ n :=
  by 
    rw [minimal_period, dif_pos (mk_mem_periodic_pts hn hx)]
    exact Nat.find_min'ₓ (mk_mem_periodic_pts hn hx) ⟨hn, hx⟩

theorem minimal_period_id : minimal_period id x = 1 :=
  ((is_periodic_id _ _).minimal_period_le Nat.one_posₓ).antisymm
    (Nat.succ_le_of_ltₓ ((is_periodic_id _ _).minimal_period_pos Nat.one_posₓ))

theorem is_fixed_point_iff_minimal_period_eq_one : minimal_period f x = 1 ↔ is_fixed_pt f x :=
  by 
    refine' ⟨fun h => _, fun h => _⟩
    ·
      rw [←iterate_one f]
      refine' Function.IsPeriodicPt.is_fixed_pt _ 
      rw [←h]
      exact is_periodic_pt_minimal_period f x
    ·
      exact
        ((h.is_periodic_pt 1).minimal_period_le Nat.one_posₓ).antisymm
          (Nat.succ_le_of_ltₓ ((h.is_periodic_pt 1).minimal_period_pos Nat.one_posₓ))

theorem is_periodic_pt.eq_zero_of_lt_minimal_period (hx : is_periodic_pt f n x) (hn : n < minimal_period f x) : n = 0 :=
  Eq.symm$ (eq_or_lt_of_le$ n.zero_le).resolve_right$ fun hn0 => not_ltₓ.2 (hx.minimal_period_le hn0) hn

theorem not_is_periodic_pt_of_pos_of_lt_minimal_period :
  ∀ {n : ℕ} (n0 : n ≠ 0) (hn : n < minimal_period f x), ¬is_periodic_pt f n x
| 0, n0, _ => (n0 rfl).elim
| n+1, _, hn => fun hp => Nat.succ_ne_zero _ (hp.eq_zero_of_lt_minimal_period hn)

theorem is_periodic_pt.minimal_period_dvd (hx : is_periodic_pt f n x) : minimal_period f x ∣ n :=
  ((eq_or_lt_of_le$ n.zero_le).elim fun hn0 => hn0 ▸ dvd_zero _)$
    fun hn0 =>
      (Nat.dvd_iff_mod_eq_zeroₓ _ _).2$
        (hx.mod$ is_periodic_pt_minimal_period f x).eq_zero_of_lt_minimal_period$
          Nat.mod_ltₓ _$ hx.minimal_period_pos hn0

theorem is_periodic_pt_iff_minimal_period_dvd : is_periodic_pt f n x ↔ minimal_period f x ∣ n :=
  ⟨is_periodic_pt.minimal_period_dvd, fun h => (is_periodic_pt_minimal_period f x).trans_dvd h⟩

open Nat

theorem minimal_period_eq_minimal_period_iff {g : β → β} {y : β} :
  minimal_period f x = minimal_period g y ↔ ∀ n, is_periodic_pt f n x ↔ is_periodic_pt g n y :=
  by 
    simpRw [is_periodic_pt_iff_minimal_period_dvd, dvd_right_iff_eq]

theorem minimal_period_eq_prime {p : ℕ} [hp : Fact p.prime] (hper : is_periodic_pt f p x) (hfix : ¬is_fixed_pt f x) :
  minimal_period f x = p :=
  (hp.out.2 _ hper.minimal_period_dvd).resolve_left (mt is_fixed_point_iff_minimal_period_eq_one.1 hfix)

theorem minimal_period_eq_prime_pow {p k : ℕ} [hp : Fact p.prime] (hk : ¬is_periodic_pt f (p ^ k) x)
  (hk1 : is_periodic_pt f (p ^ k+1) x) : minimal_period f x = p ^ k+1 :=
  by 
    apply Nat.eq_prime_pow_of_dvd_least_prime_pow hp.out <;> rwa [←is_periodic_pt_iff_minimal_period_dvd]

theorem commute.minimal_period_of_comp_dvd_lcm {g : α → α} (h : Function.Commute f g) :
  minimal_period (f ∘ g) x ∣ Nat.lcmₓ (minimal_period f x) (minimal_period g x) :=
  by 
    rw [←is_periodic_pt_iff_minimal_period_dvd, is_periodic_pt, h.comp_iterate]
    refine' is_fixed_pt.comp _ _ <;>
      rw [←is_periodic_pt, is_periodic_pt_iff_minimal_period_dvd] <;>
        first |
          exact Nat.dvd_lcm_leftₓ _ _|
          exact dvd_lcm_right _ _

private theorem minimal_period_iterate_eq_div_gcd_aux (h : 0 < gcd (minimal_period f x) n) :
  minimal_period (f^[n]) x = minimal_period f x / Nat.gcdₓ (minimal_period f x) n :=
  by 
    apply Nat.dvd_antisymm
    ·
      apply is_periodic_pt.minimal_period_dvd 
      rw [is_periodic_pt, is_fixed_pt, ←iterate_mul, ←Nat.mul_div_assocₓ _ (gcd_dvd_left _ _), mul_commₓ,
        Nat.mul_div_assocₓ _ (gcd_dvd_right _ _), mul_commₓ, iterate_mul]
      exact (is_periodic_pt_minimal_period f x).iterate _
    ·
      apply coprime.dvd_of_dvd_mul_right (coprime_div_gcd_div_gcd h)
      apply dvd_of_mul_dvd_mul_right h 
      rw [Nat.div_mul_cancelₓ (gcd_dvd_left _ _), mul_assocₓ, Nat.div_mul_cancelₓ (gcd_dvd_right _ _), mul_commₓ]
      apply is_periodic_pt.minimal_period_dvd 
      rw [is_periodic_pt, is_fixed_pt, iterate_mul]
      exact is_periodic_pt_minimal_period _ _

theorem minimal_period_iterate_eq_div_gcd (h : n ≠ 0) :
  minimal_period (f^[n]) x = minimal_period f x / Nat.gcdₓ (minimal_period f x) n :=
  minimal_period_iterate_eq_div_gcd_aux$ gcd_pos_of_pos_right _ (Nat.pos_of_ne_zeroₓ h)

theorem minimal_period_iterate_eq_div_gcd' (h : x ∈ periodic_pts f) :
  minimal_period (f^[n]) x = minimal_period f x / Nat.gcdₓ (minimal_period f x) n :=
  minimal_period_iterate_eq_div_gcd_aux$ gcd_pos_of_pos_left n (minimal_period_pos_iff_mem_periodic_pts.mpr h)

end Function

