import Mathbin.Data.Real.Ennreal 
import Mathbin.Order.Filter.CountableInter 
import Mathbin.Order.LiminfLimsup

/-!
# Order properties of extended non-negative reals

This file compiles filter-related results about `ℝ≥0∞` (see data/real/ennreal.lean).
-/


open Filter

open_locale Filter Ennreal

namespace Ennreal

variable{α : Type _}{f : Filter α}

-- error in Order.Filter.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eventually_le_limsup
[countable_Inter_filter f]
(u : α → «exprℝ≥0∞»()) : «expr∀ᶠ in , »((y), f, «expr ≤ »(u y, f.limsup u)) :=
begin
  by_cases [expr hx_top, ":", expr «expr = »(f.limsup u, «expr⊤»())],
  { simp_rw [expr hx_top] [],
    exact [expr eventually_of_forall (λ a, le_top)] },
  have [ident h_forall_le] [":", expr «expr∀ᶠ in , »((y), f, ∀
    n : exprℕ(), «expr < »(u y, «expr + »(f.limsup u, «expr / »((1 : «exprℝ≥0∞»()), n))))] [],
  { rw [expr eventually_countable_forall] [],
    refine [expr λ n, eventually_lt_of_limsup_lt _],
    nth_rewrite [0] ["<-", expr add_zero (f.limsup u)] [],
    exact [expr (add_lt_add_iff_left hx_top).mpr (by simp [] [] [] [] [] [])] },
  refine [expr h_forall_le.mono (λ y hy, le_of_forall_pos_le_add (λ r hr_pos hx_top, _))],
  have [ident hr_ne_zero] [":", expr «expr ≠ »((r : «exprℝ≥0∞»()), 0)] [],
  { rw ["[", expr ne.def, ",", expr coe_eq_zero, "]"] [],
    exact [expr (ne_of_lt hr_pos).symm] },
  cases [expr exists_inv_nat_lt hr_ne_zero] ["with", ident i, ident hi],
  rw [expr inv_eq_one_div] ["at", ident hi],
  exact [expr (hy i).le.trans (add_le_add_left hi.le (f.limsup u))]
end

-- error in Order.Filter.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem limsup_eq_zero_iff
[countable_Inter_filter f]
{u : α → «exprℝ≥0∞»()} : «expr ↔ »(«expr = »(f.limsup u, 0), «expr =ᶠ[ ] »(u, f, 0)) :=
begin
  split; intro [ident h],
  { have [ident hu_zero] [] [":=", expr eventually_le.trans (eventually_le_limsup u) (eventually_of_forall (λ
       _, le_of_eq h))],
    exact [expr hu_zero.mono (λ x hx, le_antisymm hx (zero_le _))] },
  { rw [expr limsup_congr h] [],
    simp_rw ["[", expr pi.zero_apply, ",", "<-", expr ennreal.bot_eq_zero, ",", expr limsup_const_bot, "]"] [] }
end

-- error in Order.Filter.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem limsup_const_mul_of_ne_top
{u : α → «exprℝ≥0∞»()}
{a : «exprℝ≥0∞»()}
(ha_top : «expr ≠ »(a, «expr⊤»())) : «expr = »(f.limsup (λ x : α, «expr * »(a, u x)), «expr * »(a, f.limsup u)) :=
begin
  by_cases [expr ha_zero, ":", expr «expr = »(a, 0)],
  { simp_rw ["[", expr ha_zero, ",", expr zero_mul, ",", "<-", expr ennreal.bot_eq_zero, "]"] [],
    exact [expr limsup_const_bot] },
  let [ident g] [] [":=", expr λ x : «exprℝ≥0∞»(), «expr * »(a, x)],
  have [ident hg_bij] [":", expr function.bijective g] [],
  from [expr function.bijective_iff_has_inverse.mpr ⟨λ
    x, «expr * »(«expr ⁻¹»(a), x), ⟨λ
     x, by simp [] [] [] ["[", "<-", expr mul_assoc, ",", expr inv_mul_cancel ha_zero ha_top, "]"] [] [], λ
     x, by simp [] [] [] ["[", expr g, ",", "<-", expr mul_assoc, ",", expr mul_inv_cancel ha_zero ha_top, "]"] [] []⟩⟩],
  have [ident hg_mono] [":", expr strict_mono g] [],
  from [expr monotone.strict_mono_of_injective (λ _ _ _, by rwa [expr mul_le_mul_left ha_zero ha_top] []) hg_bij.1],
  let [ident g_iso] [] [":=", expr strict_mono.order_iso_of_surjective g hg_mono hg_bij.2],
  refine [expr (order_iso.limsup_apply g_iso _ _ _ _).symm],
  all_goals { by is_bounded_default }
end

-- error in Order.Filter.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem limsup_const_mul
[countable_Inter_filter f]
{u : α → «exprℝ≥0∞»()}
{a : «exprℝ≥0∞»()} : «expr = »(f.limsup (λ x : α, «expr * »(a, u x)), «expr * »(a, f.limsup u)) :=
begin
  by_cases [expr ha_top, ":", expr «expr ≠ »(a, «expr⊤»())],
  { exact [expr limsup_const_mul_of_ne_top ha_top] },
  push_neg ["at", ident ha_top],
  by_cases [expr hu, ":", expr «expr =ᶠ[ ] »(u, f, 0)],
  { have [ident hau] [":", expr «expr =ᶠ[ ] »(λ x, «expr * »(a, u x), f, 0)] [],
    { refine [expr hu.mono (λ x hx, _)],
      rw [expr pi.zero_apply] ["at", ident hx],
      simp [] [] [] ["[", expr hx, "]"] [] [] },
    simp [] [] ["only"] ["[", expr limsup_congr hu, ",", expr limsup_congr hau, ",", expr pi.zero_apply, ",", "<-", expr bot_eq_zero, ",", expr limsup_const_bot, "]"] [] [],
    simp [] [] [] [] [] [] },
  { simp_rw ["[", expr ha_top, ",", expr top_mul, "]"] [],
    have [ident hu_mul] [":", expr «expr∃ᶠ in , »((x : α), f, «expr ≤ »(«expr⊤»(), ite «expr = »(u x, 0) (0 : «exprℝ≥0∞»()) «expr⊤»()))] [],
    { rw ["[", expr eventually_eq, ",", expr not_eventually, "]"] ["at", ident hu],
      refine [expr hu.mono (λ x hx, _)],
      rw [expr pi.zero_apply] ["at", ident hx],
      simp [] [] [] ["[", expr hx, "]"] [] [] },
    have [ident h_top_le] [":", expr «expr = »(f.limsup (λ
       x : α, ite «expr = »(u x, 0) (0 : «exprℝ≥0∞»()) «expr⊤»()), «expr⊤»())] [],
    from [expr eq_top_iff.mpr (le_limsup_of_frequently_le hu_mul)],
    have [ident hfu] [":", expr «expr ≠ »(f.limsup u, 0)] [],
    from [expr mt limsup_eq_zero_iff.1 hu],
    simp [] [] ["only"] ["[", expr h_top_le, ",", expr hfu, ",", expr if_false, "]"] [] [] }
end

theorem limsup_add_le [CountableInterFilter f] (u v : α → ℝ≥0∞) : f.limsup (u+v) ≤ f.limsup u+f.limsup v :=
  Inf_le ((eventually_le_limsup u).mp ((eventually_le_limsup v).mono fun _ hxg hxf => add_le_add hxf hxg))

-- error in Order.Filter.Ennreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem limsup_liminf_le_liminf_limsup
{β}
[encodable β]
{f : filter α}
[countable_Inter_filter f]
{g : filter β}
(u : α → β → «exprℝ≥0∞»()) : «expr ≤ »(f.limsup (λ
  a : α, g.liminf (λ b : β, u a b)), g.liminf (λ b, f.limsup (λ a, u a b))) :=
begin
  have [ident h1] [":", expr «expr∀ᶠ in , »((a), f, ∀ b, «expr ≤ »(u a b, f.limsup (λ a', u a' b)))] [],
  by { rw [expr eventually_countable_forall] [],
    exact [expr λ b, ennreal.eventually_le_limsup (λ a, u a b)] },
  refine [expr Inf_le (h1.mono (λ x hx, filter.liminf_le_liminf (filter.eventually_of_forall hx) _))],
  filter.is_bounded_default
end

end Ennreal

