import Mathbin.Analysis.Asymptotics.Asymptotics 
import Mathbin.Analysis.NormedSpace.Ordered

/-!
# Asymptotic equivalence

In this file, we define the relation `is_equivalent u v l`, which means that `u-v` is little o of
`v` along the filter `l`.

Unlike `is_[oO]` relations, this one requires `u` and `v` to have the same codomain `β`. While the
definition only requires `β` to be a `normed_group`, most interesting properties require it to be a
`normed_field`.

## Notations

We introduce the notation `u ~[l] v := is_equivalent u v l`, which you can use by opening the
`asymptotics` locale.

## Main results

If `β` is a `normed_group` :

- `_ ~[l] _` is an equivalence relation
- Equivalent statements for `u ~[l] const _ c` :
  - If `c ≠ 0`, this is true iff `tendsto u l (𝓝 c)` (see `is_equivalent_const_iff_tendsto`)
  - For `c = 0`, this is true iff `u =ᶠ[l] 0` (see `is_equivalent_zero_iff_eventually_zero`)

If `β` is a `normed_field` :

- Alternative characterization of the relation (see `is_equivalent_iff_exists_eq_mul`) :

  `u ~[l] v ↔ ∃ (φ : α → β) (hφ : tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v`

- Provided some non-vanishing hypothesis, this can be seen as `u ~[l] v ↔ tendsto (u/v) l (𝓝 1)`
  (see `is_equivalent_iff_tendsto_one`)
- For any constant `c`, `u ~[l] v` implies `tendsto u l (𝓝 c) ↔ tendsto v l (𝓝 c)`
  (see `is_equivalent.tendsto_nhds_iff`)
- `*` and `/` are compatible with `_ ~[l] _` (see `is_equivalent.mul` and `is_equivalent.div`)

If `β` is a `normed_linear_ordered_field` :

- If `u ~[l] v`, we have `tendsto u l at_top ↔ tendsto v l at_top`
  (see `is_equivalent.tendsto_at_top_iff`)

-/


namespace Asymptotics

open Filter Function

open_locale TopologicalSpace

section NormedGroup

variable{α β : Type _}[NormedGroup β]

/-- Two functions `u` and `v` are said to be asymptotically equivalent along a filter `l` when
    `u x - v x = o(v x)` as x converges along `l`. -/
def is_equivalent (u v : α → β) (l : Filter α) :=
  is_o (u - v) v l

localized [Asymptotics] notation:50 u " ~[" l:50 "] " v:50 => Asymptotics.IsEquivalent u v l

variable{u v w : α → β}{l : Filter α}

theorem is_equivalent.is_o (h : u ~[l] v) : is_o (u - v) v l :=
  h

theorem is_equivalent.is_O (h : u ~[l] v) : is_O u v l :=
  (is_O.congr_of_sub h.is_O.symm).mp (is_O_refl _ _)

theorem is_equivalent.is_O_symm (h : u ~[l] v) : is_O v u l :=
  by 
    convert h.is_o.right_is_O_add 
    ext 
    simp 

@[refl]
theorem is_equivalent.refl : u ~[l] u :=
  by 
    rw [is_equivalent, sub_self]
    exact is_o_zero _ _

@[symm]
theorem is_equivalent.symm (h : u ~[l] v) : v ~[l] u :=
  (h.is_o.trans_is_O h.is_O_symm).symm

@[trans]
theorem is_equivalent.trans (huv : u ~[l] v) (hvw : v ~[l] w) : u ~[l] w :=
  (huv.is_o.trans_is_O hvw.is_O).triangle hvw.is_o

theorem is_equivalent.congr_left {u v w : α → β} {l : Filter α} (huv : u ~[l] v) (huw : u =ᶠ[l] w) : w ~[l] v :=
  is_o.congr' (huw.sub (eventually_eq.refl _ _)) (eventually_eq.refl _ _) huv

theorem is_equivalent.congr_right {u v w : α → β} {l : Filter α} (huv : u ~[l] v) (hvw : v =ᶠ[l] w) : u ~[l] w :=
  (huv.symm.congr_left hvw).symm

theorem is_equivalent_zero_iff_eventually_zero : u ~[l] 0 ↔ u =ᶠ[l] 0 :=
  by 
    rw [is_equivalent, sub_zero]
    exact is_o_zero_right_iff

theorem is_equivalent_zero_iff_is_O_zero : u ~[l] 0 ↔ is_O u (0 : α → β) l :=
  by 
    refine' ⟨is_equivalent.is_O, fun h => _⟩
    rw [is_equivalent_zero_iff_eventually_zero, eventually_eq_iff_exists_mem]
    exact ⟨{ x:α | u x = 0 }, is_O_zero_right_iff.mp h, fun x hx => hx⟩

-- error in Analysis.Asymptotics.AsymptoticEquivalent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_equivalent_const_iff_tendsto
{c : β}
(h : «expr ≠ »(c, 0)) : «expr ↔ »(«expr ~[ ] »(u, l, const _ c), tendsto u l (expr𝓝() c)) :=
begin
  rw ["[", expr is_equivalent, ",", expr is_o_const_iff h, "]"] [],
  split; intro [ident h]; [{ have [] [] [":=", expr h.sub tendsto_const_nhds],
     rw [expr zero_sub «expr- »(c)] ["at", ident this] }, { have [] [] [":=", expr h.sub tendsto_const_nhds],
     rw ["<-", expr sub_self c] [] }]; convert [] [expr this] []; try { ext [] [] [] }; simp [] [] [] [] [] []
end

theorem is_equivalent.tendsto_const {c : β} (hu : u ~[l] const _ c) : tendsto u l (𝓝 c) :=
  by 
    rcases em$ c = 0 with ⟨rfl, h⟩
    ·
      exact (tendsto_congr'$ is_equivalent_zero_iff_eventually_zero.mp hu).mpr tendsto_const_nhds
    ·
      exact (is_equivalent_const_iff_tendsto h).mp hu

theorem is_equivalent.tendsto_nhds {c : β} (huv : u ~[l] v) (hu : tendsto u l (𝓝 c)) : tendsto v l (𝓝 c) :=
  by 
    byCases' h : c = 0
    ·
      rw [h, ←is_o_one_iff ℝ] at *
      convert (huv.symm.is_o.trans hu).add hu 
      simp 
    ·
      rw [←is_equivalent_const_iff_tendsto h] at hu⊢
      exact huv.symm.trans hu

theorem is_equivalent.tendsto_nhds_iff {c : β} (huv : u ~[l] v) : tendsto u l (𝓝 c) ↔ tendsto v l (𝓝 c) :=
  ⟨huv.tendsto_nhds, huv.symm.tendsto_nhds⟩

theorem is_equivalent.add_is_o (huv : u ~[l] v) (hwv : is_o w v l) : (w+u) ~[l] v :=
  by 
    rw [is_equivalent] at *
    convert hwv.add huv 
    ext 
    simp [add_sub]

theorem is_o.is_equivalent (huv : is_o (u - v) v l) : u ~[l] v :=
  huv

theorem is_equivalent.neg (huv : u ~[l] v) : (fun x => -u x) ~[l] fun x => -v x :=
  by 
    rw [is_equivalent]
    convert huv.is_o.neg_left.neg_right 
    ext 
    simp 

end NormedGroup

open_locale Asymptotics

section NormedField

variable{α β : Type _}[NormedField β]{t u v w : α → β}{l : Filter α}

theorem is_equivalent_iff_exists_eq_mul : u ~[l] v ↔ ∃ (φ : α → β)(hφ : tendsto φ l (𝓝 1)), u =ᶠ[l] φ*v :=
  by 
    rw [is_equivalent, is_o_iff_exists_eq_mul]
    split  <;> rintro ⟨φ, hφ, h⟩ <;> [use φ+1, use φ - 1] <;> split 
    ·
      conv  in 𝓝 _ => rw [←zero_addₓ (1 : β)]
      exact hφ.add tendsto_const_nhds
    ·
      convert h.add (eventually_eq.refl l v) <;> ext <;> simp [add_mulₓ]
    ·
      conv  in 𝓝 _ => rw [←sub_self (1 : β)]
      exact hφ.sub tendsto_const_nhds
    ·
      convert h.sub (eventually_eq.refl l v) <;> ext <;> simp [sub_mul]

theorem is_equivalent.exists_eq_mul (huv : u ~[l] v) : ∃ (φ : α → β)(hφ : tendsto φ l (𝓝 1)), u =ᶠ[l] φ*v :=
  is_equivalent_iff_exists_eq_mul.mp huv

theorem is_equivalent_of_tendsto_one (hz : ∀ᶠx in l, v x = 0 → u x = 0) (huv : tendsto (u / v) l (𝓝 1)) : u ~[l] v :=
  by 
    rw [is_equivalent_iff_exists_eq_mul]
    refine' ⟨u / v, huv, hz.mono$ fun x hz' => (div_mul_cancel_of_imp hz').symm⟩

theorem is_equivalent_of_tendsto_one' (hz : ∀ x, v x = 0 → u x = 0) (huv : tendsto (u / v) l (𝓝 1)) : u ~[l] v :=
  is_equivalent_of_tendsto_one (eventually_of_forall hz) huv

-- error in Analysis.Asymptotics.AsymptoticEquivalent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_equivalent_iff_tendsto_one
(hz : «expr∀ᶠ in , »((x), l, «expr ≠ »(v x, 0))) : «expr ↔ »(«expr ~[ ] »(u, l, v), tendsto «expr / »(u, v) l (expr𝓝() 1)) :=
begin
  split,
  { intro [ident hequiv],
    have [] [] [":=", expr hequiv.is_o.tendsto_0],
    simp [] [] ["only"] ["[", expr pi.sub_apply, ",", expr sub_div, "]"] [] ["at", ident this],
    have [ident key] [":", expr tendsto (λ x, «expr / »(v x, v x)) l (expr𝓝() 1)] [],
    { exact [expr «expr $ »(tendsto_congr', «expr $ »(hz.mono, λ
         x hnz, @div_self _ _ (v x) hnz)).mpr tendsto_const_nhds] },
    convert [] [expr this.add key] [],
    { ext [] [] [],
      simp [] [] [] [] [] [] },
    { norm_num [] [] } },
  { exact [expr is_equivalent_of_tendsto_one «expr $ »(hz.mono, λ x hnvz hz, (hnvz hz).elim)] }
end

end NormedField

section Smul

-- error in Analysis.Asymptotics.AsymptoticEquivalent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_equivalent.smul
{α E 𝕜 : Type*}
[normed_field 𝕜]
[normed_group E]
[normed_space 𝕜 E]
{a b : α → 𝕜}
{u v : α → E}
{l : filter α}
(hab : «expr ~[ ] »(a, l, b))
(huv : «expr ~[ ] »(u, l, v)) : «expr ~[ ] »(λ x, «expr • »(a x, u x), l, λ x, «expr • »(b x, v x)) :=
begin
  rcases [expr hab.exists_eq_mul, "with", "⟨", ident φ, ",", ident hφ, ",", ident habφ, "⟩"],
  have [] [":", expr «expr =ᶠ[ ] »(«expr - »(λ
     x : α, «expr • »(a x, u x), λ
     x : α, «expr • »(b x, v x)), l, λ x, «expr • »(b x, «expr - »(«expr • »(φ x, u x), v x)))] [],
  { convert [] [expr «expr $ »(habφ.comp₂ ((«expr • »)), eventually_eq.refl _ u).sub (eventually_eq.refl _ (λ
       x, «expr • »(b x, v x)))] [],
    ext [] [] [],
    rw ["[", expr pi.mul_apply, ",", expr mul_comm, ",", expr mul_smul, ",", "<-", expr smul_sub, "]"] [] },
  refine [expr «expr $ »(is_o_congr this.symm, eventually_eq.rfl).mp ((is_O_refl b l).smul_is_o _)],
  rcases [expr huv.is_O.exists_pos, "with", "⟨", ident C, ",", ident hC, ",", ident hCuv, "⟩"],
  rw [expr is_equivalent] ["at", "*"],
  rw [expr is_o_iff] ["at", "*"],
  rw [expr is_O_with] ["at", ident hCuv],
  simp [] [] ["only"] ["[", expr metric.tendsto_nhds, ",", expr dist_eq_norm, "]"] [] ["at", ident hφ],
  intros [ident c, ident hc],
  specialize [expr hφ «expr / »(«expr / »(c, 2), C) (div_pos (by linarith [] [] []) hC)],
  specialize [expr huv (show «expr < »(0, «expr / »(c, 2)), by linarith [] [] [])],
  refine [expr hφ.mp «expr $ »(huv.mp, «expr $ »(hCuv.mono, λ x hCuvx huvx hφx, _))],
  have [ident key] [] [":=", expr calc
     «expr ≤ »(«expr * »(«expr∥ ∥»(«expr - »(φ x, 1)), «expr∥ ∥»(u x)), «expr * »(«expr / »(«expr / »(c, 2), C), «expr∥ ∥»(u x))) : mul_le_mul_of_nonneg_right hφx.le «expr $ »(norm_nonneg, u x)
     «expr ≤ »(..., «expr * »(«expr / »(«expr / »(c, 2), C), «expr * »(C, «expr∥ ∥»(v x)))) : mul_le_mul_of_nonneg_left hCuvx (div_pos (by linarith [] [] []) hC).le
     «expr = »(..., «expr * »(«expr / »(c, 2), «expr∥ ∥»(v x))) : by { field_simp [] ["[", expr hC.ne.symm, "]"] [] [],
       ring [] }],
  calc
    «expr = »(«expr∥ ∥»(«expr - »(λ
       x : α, «expr • »(φ x, u x), v) x), «expr∥ ∥»(«expr + »(«expr • »(«expr - »(φ x, 1), u x), «expr - »(u x, v x)))) : by simp [] [] [] ["[", expr sub_smul, ",", expr sub_add, "]"] [] []
    «expr ≤ »(..., «expr + »(«expr∥ ∥»(«expr • »(«expr - »(φ x, 1), u x)), «expr∥ ∥»(«expr - »(u x, v x)))) : norm_add_le _ _
    «expr = »(..., «expr + »(«expr * »(«expr∥ ∥»(«expr - »(φ x, 1)), «expr∥ ∥»(u x)), «expr∥ ∥»(«expr - »(u x, v x)))) : by rw [expr norm_smul] []
    «expr ≤ »(..., «expr + »(«expr * »(«expr / »(c, 2), «expr∥ ∥»(v x)), «expr∥ ∥»(«expr - »(u x, v x)))) : add_le_add_right key _
    «expr ≤ »(..., «expr + »(«expr * »(«expr / »(c, 2), «expr∥ ∥»(v x)), «expr * »(«expr / »(c, 2), «expr∥ ∥»(v x)))) : add_le_add_left huvx _
    «expr = »(..., «expr * »(c, «expr∥ ∥»(v x))) : by ring []
end

end Smul

section mul_inv

variable{α β : Type _}[NormedField β]{t u v w : α → β}{l : Filter α}

theorem is_equivalent.mul (htu : t ~[l] u) (hvw : v ~[l] w) : (t*v) ~[l] u*w :=
  htu.smul hvw

theorem is_equivalent.inv (huv : u ~[l] v) : (fun x => u x⁻¹) ~[l] fun x => v x⁻¹ :=
  by 
    rw [is_equivalent_iff_exists_eq_mul] at *
    rcases huv with ⟨φ, hφ, h⟩
    rw [←inv_one]
    refine'
      ⟨fun x => φ x⁻¹,
        tendsto.inv₀ hφ
          (by 
            normNum),
        _⟩
    convert h.inv 
    ext 
    simp [mul_inv₀]

theorem is_equivalent.div (htu : t ~[l] u) (hvw : v ~[l] w) : (fun x => t x / v x) ~[l] fun x => u x / w x :=
  by 
    simpa only [div_eq_mul_inv] using htu.mul hvw.inv

end mul_inv

section NormedLinearOrderedField

variable{α β : Type _}[NormedLinearOrderedField β]{u v : α → β}{l : Filter α}

theorem is_equivalent.tendsto_at_top [OrderTopology β] (huv : u ~[l] v) (hu : tendsto u l at_top) :
  tendsto v l at_top :=
  let ⟨φ, hφ, h⟩ := huv.symm.exists_eq_mul 
  tendsto.congr' h.symm (mul_commₓ u φ ▸ hu.at_top_mul zero_lt_one hφ)

theorem is_equivalent.tendsto_at_top_iff [OrderTopology β] (huv : u ~[l] v) : tendsto u l at_top ↔ tendsto v l at_top :=
  ⟨huv.tendsto_at_top, huv.symm.tendsto_at_top⟩

theorem is_equivalent.tendsto_at_bot [OrderTopology β] (huv : u ~[l] v) (hu : tendsto u l at_bot) :
  tendsto v l at_bot :=
  by 
    convert tendsto_neg_at_top_at_bot.comp (huv.neg.tendsto_at_top$ tendsto_neg_at_bot_at_top.comp hu)
    ext 
    simp 

theorem is_equivalent.tendsto_at_bot_iff [OrderTopology β] (huv : u ~[l] v) : tendsto u l at_bot ↔ tendsto v l at_bot :=
  ⟨huv.tendsto_at_bot, huv.symm.tendsto_at_bot⟩

end NormedLinearOrderedField

end Asymptotics

open Filter Asymptotics

open_locale Asymptotics

variable{α β : Type _}[NormedGroup β]

theorem Filter.EventuallyEq.is_equivalent {u v : α → β} {l : Filter α} (h : u =ᶠ[l] v) : u ~[l] v :=
  is_o.congr' h.sub_eq.symm (eventually_eq.refl _ _) (is_o_zero v l)

