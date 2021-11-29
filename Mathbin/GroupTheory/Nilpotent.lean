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

variable{G : Type _}[Groupₓ G](H : Subgroup G)[normal H]

/-- If `H` is a normal subgroup of `G`, then the set `{x : G | ∀ y : G, x*y*x⁻¹*y⁻¹ ∈ H}`
is a subgroup of `G` (because it is the preimage in `G` of the centre of the
quotient group `G/H`.)
-/
def upperCentralSeriesStep : Subgroup G :=
  { Carrier := { x:G | ∀ (y : G), (((x*y)*x⁻¹)*y⁻¹) ∈ H },
    one_mem' :=
      fun y =>
        by 
          simp [Subgroup.one_mem],
    mul_mem' :=
      fun a b ha hb y =>
        by 
          convert Subgroup.mul_mem _ (ha ((b*y)*b⁻¹)) (hb y) using 1
          group,
    inv_mem' :=
      fun x hx y =>
        by 
          specialize hx (y⁻¹)
          rw [mul_assocₓ, inv_invₓ] at hx⊢
          exact Subgroup.Normal.mem_comm inferInstance hx }

theorem mem_upper_central_series_step (x : G) : x ∈ upperCentralSeriesStep H ↔ ∀ y, (((x*y)*x⁻¹)*y⁻¹) ∈ H :=
  Iff.rfl

open QuotientGroup

/-- The proof that `upper_central_series_step H` is the preimage of the centre of `G/H` under
the canonical surjection. -/
theorem upper_central_series_step_eq_comap_center :
  upperCentralSeriesStep H = Subgroup.comap (mk' H) (center (Quotientₓ H)) :=
  by 
    ext 
    rw [mem_comap, mem_center_iff, forall_coe]
    apply forall_congrₓ 
    intro y 
    change (((x*y)*x⁻¹)*y⁻¹) ∈ H ↔ ((y*x : G) : Quotientₓ H) = (x*y : G)
    rw [eq_comm, eq_iff_div_mem, div_eq_mul_inv]
    congr 2
    group

instance  : normal (upperCentralSeriesStep H) :=
  by 
    rw [upper_central_series_step_eq_comap_center]
    infer_instance

variable(G)

/-- An auxiliary type-theoretic definition defining both the upper central series of
a group, and a proof that it is normal, all in one go. -/
def upperCentralSeriesAux : ℕ → Σ'H : Subgroup G, normal H
| 0 => ⟨⊥, inferInstance⟩
| n+1 =>
  let un := upperCentralSeriesAux n 
  let un_normal := un.2
  by 
    exact ⟨upperCentralSeriesStep un.1, inferInstance⟩

/-- `upper_central_series G n` is the `n`th term in the upper central series of `G`. -/
def upperCentralSeries (n : ℕ) : Subgroup G :=
  (upperCentralSeriesAux G n).1

instance  (n : ℕ) : normal (upperCentralSeries G n) :=
  (upperCentralSeriesAux G n).2

@[simp]
theorem upper_central_series_zero : upperCentralSeries G 0 = ⊥ :=
  rfl

/-- The `n+1`st term of the upper central series `H i` has underlying set equal to the `x` such
that `⁅x,G⁆ ⊆ H n`-/
theorem mem_upper_central_series_succ_iff (n : ℕ) (x : G) :
  x ∈ upperCentralSeries G (n+1) ↔ ∀ (y : G), (((x*y)*x⁻¹)*y⁻¹) ∈ upperCentralSeries G n :=
  Iff.rfl

/-- A group `G` is nilpotent if its upper central series is eventually `G`. -/
class Groupₓ.IsNilpotent(G : Type _)[Groupₓ G] : Prop where 
  nilpotent{} : ∃ n : ℕ, upperCentralSeries G n = ⊤

open Groupₓ

section Classical

open_locale Classical

/-- The nilpotency class of a nilpotent group is the small natural `n` such that
the `n`'th term of the upper central series is `G`. -/
noncomputable def Groupₓ.nilpotencyClass (G : Type _) [Groupₓ G] [is_nilpotent G] : ℕ :=
  Nat.findₓ (is_nilpotent.nilpotent G)

end Classical

variable{G}

/-- A sequence of subgroups of `G` is an ascending central series if `H 0` is trivial and
  `⁅H (n + 1), G⁆ ⊆ H n` for all `n`. Note that we do not require that `H n = G` for some `n`. -/
def IsAscendingCentralSeries (H : ℕ → Subgroup G) : Prop :=
  H 0 = ⊥ ∧ ∀ (x : G) (n : ℕ), x ∈ H (n+1) → ∀ g, (((x*g)*x⁻¹)*g⁻¹) ∈ H n

/-- A sequence of subgroups of `G` is a descending central series if `H 0` is `G` and
  `⁅H n, G⁆ ⊆ H (n + 1)` for all `n`. Note that we do not requre that `H n = {1}` for some `n`. -/
def IsDescendingCentralSeries (H : ℕ → Subgroup G) :=
  H 0 = ⊤ ∧ ∀ (x : G) (n : ℕ), x ∈ H n → ∀ g, (((x*g)*x⁻¹)*g⁻¹) ∈ H (n+1)

-- error in GroupTheory.Nilpotent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any ascending central series for a group is bounded above by the upper central series. -/
theorem ascending_central_series_le_upper
(H : exprℕ() → subgroup G)
(hH : is_ascending_central_series H) : ∀ n : exprℕ(), «expr ≤ »(H n, upper_central_series G n)
| 0 := «expr ▸ »(hH.1.symm, le_refl «expr⊥»())
| «expr + »(n, 1) := begin
  specialize [expr ascending_central_series_le_upper n],
  intros [ident x, ident hx],
  have [] [] [":=", expr hH.2 x n hx],
  rw [expr mem_upper_central_series_succ_iff] [],
  intro [ident y],
  apply [expr ascending_central_series_le_upper],
  apply [expr this]
end

variable(G)

/-- The upper central series of a group is an ascending central series. -/
theorem upper_central_series_is_ascending_central_series : IsAscendingCentralSeries (upperCentralSeries G) :=
  ⟨rfl, fun x n h => h⟩

theorem upper_central_series_mono : Monotone (upperCentralSeries G) :=
  by 
    refine' monotone_nat_of_le_succ _ 
    intro n x hx y 
    rw [mul_assocₓ, mul_assocₓ, ←mul_assocₓ y (x⁻¹) (y⁻¹)]
    exact
      mul_mem (upperCentralSeries G n) hx
        (normal.conj_mem (upperCentralSeries.Subgroup.normal G n) (x⁻¹) (inv_mem _ hx) y)

-- error in GroupTheory.Nilpotent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A group `G` is nilpotent iff there exists an ascending central series which reaches `G` in
  finitely many steps. -/
theorem nilpotent_iff_finite_ascending_central_series : «expr ↔ »(is_nilpotent G, «expr∃ , »((H : exprℕ() → subgroup G), «expr ∧ »(is_ascending_central_series H, «expr∃ , »((n : exprℕ()), «expr = »(H n, «expr⊤»()))))) :=
begin
  split,
  { intro [ident h],
    use [expr upper_central_series G],
    refine [expr ⟨upper_central_series_is_ascending_central_series G, h.1⟩] },
  { rintro ["⟨", ident H, ",", ident hH, ",", ident n, ",", ident hn, "⟩"],
    use [expr n],
    have [] [] [":=", expr ascending_central_series_le_upper H hH n],
    rw [expr hn] ["at", ident this],
    exact [expr eq_top_iff.mpr this] }
end

-- error in GroupTheory.Nilpotent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A group `G` is nilpotent iff there exists a descending central series which reaches the
  trivial group in a finite time. -/
theorem nilpotent_iff_finite_descending_central_series : «expr ↔ »(is_nilpotent G, «expr∃ , »((H : exprℕ() → subgroup G), «expr ∧ »(is_descending_central_series H, «expr∃ , »((n : exprℕ()), «expr = »(H n, «expr⊥»()))))) :=
begin
  rw [expr nilpotent_iff_finite_ascending_central_series] [],
  split,
  { rintro ["⟨", ident H, ",", "⟨", ident h0, ",", ident hH, "⟩", ",", ident n, ",", ident hn, "⟩"],
    use [expr λ m, H «expr - »(n, m)],
    split,
    { refine [expr ⟨hn, λ x m hx g, _⟩],
      dsimp [] [] [] ["at", ident hx],
      by_cases [expr hm, ":", expr «expr ≤ »(n, m)],
      { have [ident hnm] [":", expr «expr = »(«expr - »(n, m), 0)] [":=", expr tsub_eq_zero_iff_le.mpr hm],
        rw ["[", expr hnm, ",", expr h0, ",", expr subgroup.mem_bot, "]"] ["at", ident hx],
        subst [expr hx],
        convert [] [expr subgroup.one_mem _] [],
        group [] },
      { push_neg ["at", ident hm],
        apply [expr hH],
        convert [] [expr hx] [],
        rw [expr nat.sub_succ] [],
        exact [expr nat.succ_pred_eq_of_pos (tsub_pos_of_lt hm)] } },
    { use [expr n],
      rwa [expr tsub_self] [] } },
  { rintro ["⟨", ident H, ",", "⟨", ident h0, ",", ident hH, "⟩", ",", ident n, ",", ident hn, "⟩"],
    use [expr λ m, H «expr - »(n, m)],
    split,
    { refine [expr ⟨hn, λ x m hx g, _⟩],
      dsimp ["only"] [] [] ["at", ident hx],
      by_cases [expr hm, ":", expr «expr ≤ »(n, m)],
      { have [ident hnm] [":", expr «expr = »(«expr - »(n, m), 0)] [":=", expr tsub_eq_zero_iff_le.mpr hm],
        dsimp ["only"] [] [] [],
        rw ["[", expr hnm, ",", expr h0, "]"] [],
        exact [expr mem_top _] },
      { push_neg ["at", ident hm],
        dsimp ["only"] [] [] [],
        convert [] [expr hH x _ hx g] [],
        rw [expr nat.sub_succ] [],
        exact [expr (nat.succ_pred_eq_of_pos (tsub_pos_of_lt hm)).symm] } },
    { use [expr n],
      rwa [expr tsub_self] [] } }
end

/-- The lower central series of a group `G` is a sequence `H n` of subgroups of `G`, defined
  by `H 0` is all of `G` and for `n≥1`, `H (n + 1) = ⁅H n, G⁆` -/
def lowerCentralSeries (G : Type _) [Groupₓ G] : ℕ → Subgroup G
| 0 => ⊤
| n+1 => ⁅lowerCentralSeries n,⊤⁆

variable{G}

@[simp]
theorem lower_central_series_zero : lowerCentralSeries G 0 = ⊤ :=
  rfl

theorem mem_lower_central_series_succ_iff (n : ℕ) (q : G) :
  q ∈ lowerCentralSeries G (n+1) ↔
    q ∈
      closure
        { x | ∃ (p : _)(_ : p ∈ lowerCentralSeries G n)(q : _)(_ : q ∈ (⊤ : Subgroup G)), (((p*q)*p⁻¹)*q⁻¹) = x } :=
  Iff.rfl

theorem lower_central_series_succ (n : ℕ) :
  lowerCentralSeries G (n+1) =
    closure { x | ∃ (p : _)(_ : p ∈ lowerCentralSeries G n)(q : _)(_ : q ∈ (⊤ : Subgroup G)), (((p*q)*p⁻¹)*q⁻¹) = x } :=
  rfl

instance  (n : ℕ) : normal (lowerCentralSeries G n) :=
  by 
    induction' n with d hd
    ·
      exact (⊤ : Subgroup G).normal_of_characteristic
    ·
      exact general_commutator_normal (lowerCentralSeries G d) ⊤

theorem lower_central_series_antitone : Antitone (lowerCentralSeries G) :=
  by 
    refine' antitone_nat_of_succ_le fun n x hx => _ 
    simp only [mem_lower_central_series_succ_iff, exists_prop, mem_top, exists_true_left, true_andₓ] at hx 
    refine' closure_induction hx _ (Subgroup.one_mem _) (@Subgroup.mul_mem _ _ _) (@Subgroup.inv_mem _ _ _)
    rintro y ⟨z, hz, a, ha⟩
    rw [←ha, mul_assocₓ, mul_assocₓ, ←mul_assocₓ a (z⁻¹) (a⁻¹)]
    exact
      mul_mem (lowerCentralSeries G n) hz
        (normal.conj_mem (lowerCentralSeries.Subgroup.normal n) (z⁻¹) (inv_mem _ hz) a)

/-- The lower central series of a group is a descending central series. -/
theorem lower_central_series_is_descending_central_series : IsDescendingCentralSeries (lowerCentralSeries G) :=
  by 
    split 
    rfl 
    intro x n hxn g 
    exact general_commutator_containment _ _ hxn (Subgroup.mem_top g)

/-- Any descending central series for a group is bounded below by the lower central series. -/
theorem descending_central_series_ge_lower (H : ℕ → Subgroup G) (hH : IsDescendingCentralSeries H) :
  ∀ (n : ℕ), lowerCentralSeries G n ≤ H n
| 0 => hH.1.symm ▸ le_reflₓ ⊤
| n+1 =>
  by 
    specialize descending_central_series_ge_lower n 
    apply (general_commutator_le _ _ _).2
    intro x hx q _ 
    exact hH.2 x n (descending_central_series_ge_lower hx) q

-- error in GroupTheory.Nilpotent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A group is nilpotent if and only if its lower central series eventually reaches
  the trivial subgroup. -/
theorem nilpotent_iff_lower_central_series : «expr ↔ »(is_nilpotent G, «expr∃ , »((n), «expr = »(lower_central_series G n, «expr⊥»()))) :=
begin
  rw [expr nilpotent_iff_finite_descending_central_series] [],
  split,
  { rintro ["⟨", ident H, ",", "⟨", ident h0, ",", ident hs, "⟩", ",", ident n, ",", ident hn, "⟩"],
    use [expr n],
    have [] [] [":=", expr descending_central_series_ge_lower H ⟨h0, hs⟩ n],
    rw [expr hn] ["at", ident this],
    exact [expr eq_bot_iff.mpr this] },
  { intro [ident h],
    use ["[", expr lower_central_series G, ",", expr lower_central_series_is_descending_central_series, ",", expr h, "]"] }
end

theorem lower_central_series_map_subtype_le (H : Subgroup G) (n : ℕ) :
  (lowerCentralSeries H n).map H.subtype ≤ lowerCentralSeries G n :=
  by 
    induction' n with d hd
    ·
      simp 
    ·
      rw [lower_central_series_succ, lower_central_series_succ, MonoidHom.map_closure]
      apply Subgroup.closure_mono 
      rintro x1 ⟨x2, ⟨x3, hx3, x4, hx4, rfl⟩, rfl⟩
      exact
        ⟨x3, hd (mem_map.mpr ⟨x3, hx3, rfl⟩), x4,
          by 
            simp ⟩

-- error in GroupTheory.Nilpotent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance subgroup.is_nilpotent (H : subgroup G) [hG : is_nilpotent G] : is_nilpotent H :=
begin
  rw [expr nilpotent_iff_lower_central_series] ["at", "*"],
  rcases [expr hG, "with", "⟨", ident n, ",", ident hG, "⟩"],
  use [expr n],
  have [] [] [":=", expr lower_central_series_map_subtype_le H n],
  simp [] [] ["only"] ["[", expr hG, ",", expr set_like.le_def, ",", expr mem_map, ",", expr forall_apply_eq_imp_iff₂, ",", expr exists_imp_distrib, "]"] [] ["at", ident this],
  exact [expr eq_bot_iff.mpr (λ x hx, subtype.ext (this x hx))]
end

instance (priority := 100)is_nilpotent_of_subsingleton [Subsingleton G] : is_nilpotent G :=
  nilpotent_iff_lower_central_series.2 ⟨0, Subsingleton.elimₓ ⊤ ⊥⟩

theorem upperCentralSeries.map {H : Type _} [Groupₓ H] {f : G →* H} (h : Function.Surjective f) (n : ℕ) :
  Subgroup.map f (upperCentralSeries G n) ≤ upperCentralSeries H n :=
  by 
    induction' n with d hd
    ·
      simp 
    ·
      rintro _ ⟨x, hx : x ∈ upperCentralSeries G d.succ, rfl⟩ y' 
      rcases h y' with ⟨y, rfl⟩
      simpa using hd (mem_map_of_mem f (hx y))

theorem lowerCentralSeries.map {H : Type _} [Groupₓ H] (f : G →* H) (n : ℕ) :
  Subgroup.map f (lowerCentralSeries G n) ≤ lowerCentralSeries H n :=
  by 
    induction' n with d hd
    ·
      simp [Nat.nat_zero_eq_zero]
    ·
      rintro a ⟨x, hx : x ∈ lowerCentralSeries G d.succ, rfl⟩
      refine'
        closure_induction hx _
          (by 
            simp [f.map_one, Subgroup.one_mem _])
          (fun y z hy hz =>
            by 
              simp [MonoidHom.map_mul, Subgroup.mul_mem _ hy hz])
          fun y hy =>
            by 
              simp [f.map_inv, Subgroup.inv_mem _ hy]
      rintro a ⟨y, hy, z, ⟨-, rfl⟩⟩
      apply mem_closure.mpr 
      exact
        fun K hK =>
          hK
            ⟨f y, hd (mem_map_of_mem f hy),
              by 
                simp ⟩

theorem lower_central_series_succ_eq_bot {n : ℕ} (h : lowerCentralSeries G n ≤ center G) :
  lowerCentralSeries G (n+1) = ⊥ :=
  by 
    rw [lower_central_series_succ, closure_eq_bot_iff, Set.subset_singleton_iff]
    rintro x ⟨y, hy1, z, ⟨⟩, rfl⟩
    symm 
    rw [eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq, one_mulₓ]
    exact mem_center_iff.mp (h hy1) z

theorem is_nilpotent_of_ker_le_center {H : Type _} [Groupₓ H] {f : G →* H} (hf1 : f.ker ≤ center G)
  (hH : is_nilpotent H) : is_nilpotent G :=
  by 
    rw [nilpotent_iff_lower_central_series] at *
    rcases hH with ⟨n, hn⟩
    refine' ⟨n+1, lower_central_series_succ_eq_bot (le_transₓ ((map_eq_bot_iff _).mp _) hf1)⟩
    exact eq_bot_iff.mpr (hn ▸ lowerCentralSeries.map f n)

