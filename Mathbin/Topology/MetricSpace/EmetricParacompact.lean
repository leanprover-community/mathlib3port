import Mathbin.Topology.MetricSpace.EmetricSpace 
import Mathbin.Topology.Paracompact 
import Mathbin.SetTheory.Ordinal

/-!
# (Extended) metric spaces are paracompact

In this file we provide two instances:

* `emetric.paracompact_space`: a `pseudo_emetric_space` is paracompact; formalization is based
  on [MR0236876];
* `emetric.normal_of_metric`: an `emetric_space` is a normal topological space.

## Tags

metric space, paracompact space, normal space
-/


variable{α : Type _}

open_locale Ennreal TopologicalSpace

open Set

namespace Emetric

-- error in Topology.MetricSpace.EmetricParacompact: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A `pseudo_emetric_space` is always a paracompact space. Formalization is based
on [MR0236876]. -/ @[priority 100] instance [pseudo_emetric_space α] : paracompact_space α :=
begin
  classical,
  have [ident pow_pos] [":", expr ∀ k : exprℕ(), «expr < »((0 : «exprℝ≥0∞»()), «expr ^ »(«expr ⁻¹»(2), k))] [],
  from [expr λ k, ennreal.pow_pos (ennreal.inv_pos.2 ennreal.two_ne_top) _],
  have [ident hpow_le] [":", expr ∀
   {m
    n : exprℕ()}, «expr ≤ »(m, n) → «expr ≤ »(«expr ^ »((«expr ⁻¹»(2) : «exprℝ≥0∞»()), n), «expr ^ »(«expr ⁻¹»(2), m))] [],
  from [expr λ m n h, ennreal.pow_le_pow_of_le_one (ennreal.inv_le_one.2 ennreal.one_lt_two.le) h],
  have [ident h2pow] [":", expr ∀
   n : exprℕ(), «expr = »(«expr * »(2, «expr ^ »((«expr ⁻¹»(2) : «exprℝ≥0∞»()), «expr + »(n, 1))), «expr ^ »(«expr ⁻¹»(2), n))] [],
  by { intro [ident n],
    simp [] [] [] ["[", expr pow_succ, ",", "<-", expr mul_assoc, ",", expr ennreal.mul_inv_cancel, "]"] [] [] },
  refine [expr ⟨λ ι s ho hcov, _⟩],
  simp [] [] ["only"] ["[", expr Union_eq_univ_iff, "]"] [] ["at", ident hcov],
  letI [] [":", expr linear_order ι] [":=", expr linear_order_of_STO' well_ordering_rel],
  have [ident wf] [":", expr well_founded ((«expr < ») : ι → ι → exprProp())] [":=", expr @is_well_order.wf ι well_ordering_rel _],
  set [] [ident ind] [":", expr α → ι] [":="] [expr λ x, wf.min {i : ι | «expr ∈ »(x, s i)} (hcov x)] [],
  have [ident mem_ind] [":", expr ∀ x, «expr ∈ »(x, s (ind x))] [],
  from [expr λ x, wf.min_mem _ (hcov x)],
  have [ident nmem_of_lt_ind] [":", expr ∀ {x i}, «expr < »(i, ind x) → «expr ∉ »(x, s i)] [],
  from [expr λ x i hlt hxi, wf.not_lt_min _ (hcov x) hxi hlt],
  set [] [ident D] [":", expr exprℕ() → ι → set α] [":="] [expr λ
   n, nat.strong_rec_on' n (λ
    n
    D'
    i, «expr⋃ , »((x : α)
     (hxs : «expr = »(ind x, i))
     (hb : «expr ⊆ »(ball x «expr * »(3, «expr ^ »(«expr ⁻¹»(2), n)), s i))
     (hlt : ∀ (m «expr < » n) (j : ι), «expr ∉ »(x, D' m «expr‹ ›»(_) j)), ball x «expr ^ »(«expr ⁻¹»(2), n)))] [],
  have [ident Dn] [":", expr ∀
   n
   i, «expr = »(D n i, «expr⋃ , »((x : α)
     (hxs : «expr = »(ind x, i))
     (hb : «expr ⊆ »(ball x «expr * »(3, «expr ^ »(«expr ⁻¹»(2), n)), s i))
     (hlt : ∀ (m «expr < » n) (j : ι), «expr ∉ »(x, D m j)), ball x «expr ^ »(«expr ⁻¹»(2), n)))] [],
  from [expr λ n s, by { simp [] [] ["only"] ["[", expr D, "]"] [] [], rw [expr nat.strong_rec_on_beta'] [] }],
  have [ident memD] [":", expr ∀
   {n
    i
    y}, «expr ↔ »(«expr ∈ »(y, D n i), «expr∃ , »((x)
     (hi : «expr = »(ind x, i))
     (hb : «expr ⊆ »(ball x «expr * »(3, «expr ^ »(«expr ⁻¹»(2), n)), s i))
     (hlt : ∀ (m «expr < » n) (j : ι), «expr ∉ »(x, D m j)), «expr < »(edist y x, «expr ^ »(«expr ⁻¹»(2), n))))] [],
  { intros [ident n, ident i, ident y],
    rw ["[", expr Dn n i, "]"] [],
    simp [] [] ["only"] ["[", expr mem_Union, ",", expr mem_ball, "]"] [] [] },
  have [ident Dcov] [":", expr ∀ x, «expr∃ , »((n i), «expr ∈ »(x, D n i))] [],
  { intro [ident x],
    obtain ["⟨", ident n, ",", ident hn, "⟩", ":", expr «expr∃ , »((n : exprℕ()), «expr ⊆ »(ball x «expr * »(3, «expr ^ »(«expr ⁻¹»(2), n)), s (ind x)))],
    { rcases [expr is_open_iff.1 «expr $ »(ho, ind x) x (mem_ind x), "with", "⟨", ident ε, ",", ident ε0, ",", ident hε, "⟩"],
      have [] [":", expr «expr < »(0, «expr / »(ε, 3))] [":=", expr ennreal.div_pos_iff.2 ⟨ε0.lt.ne', ennreal.coe_ne_top⟩],
      rcases [expr ennreal.exists_inv_two_pow_lt this.ne', "with", "⟨", ident n, ",", ident hn, "⟩"],
      refine [expr ⟨n, subset.trans (ball_subset_ball _) hε⟩],
      simpa [] [] ["only"] ["[", expr div_eq_mul_inv, ",", expr mul_comm, "]"] [] ["using", expr (ennreal.mul_lt_of_lt_div hn).le] },
    by_contra [ident h],
    push_neg ["at", ident h],
    apply [expr h n (ind x)],
    exact [expr memD.2 ⟨x, rfl, hn, λ _ _ _, h _ _, mem_ball_self (pow_pos _)⟩] },
  have [ident Dopen] [":", expr ∀ n i, is_open (D n i)] [],
  { intros [ident n, ident i],
    rw [expr Dn] [],
    iterate [4] { refine [expr is_open_Union (λ _, _)] },
    exact [expr is_open_ball] },
  have [ident HDS] [":", expr ∀ n i, «expr ⊆ »(D n i, s i)] [],
  { intros [ident n, ident s, ident x],
    rw [expr memD] [],
    rintro ["⟨", ident y, ",", ident rfl, ",", ident hsub, ",", "-", ",", ident hyx, "⟩"],
    refine [expr hsub (lt_of_lt_of_le hyx _)],
    calc
      «expr = »(«expr ^ »(«expr ⁻¹»(2), n), «expr * »(1, «expr ^ »(«expr ⁻¹»(2), n))) : (one_mul _).symm
      «expr ≤ »(..., «expr * »(3, «expr ^ »(«expr ⁻¹»(2), n))) : ennreal.mul_le_mul _ le_rfl,
    have [] [":", expr «expr ≤ »(((1 : exprℕ()) : «exprℝ≥0∞»()), (3 : exprℕ()))] [],
    from [expr ennreal.coe_nat_le_coe_nat.2 (by norm_num1 [])],
    exact_mod_cast [expr this] },
  refine [expr ⟨«expr × »(exprℕ(), ι), λ ni, D ni.1 ni.2, λ _, Dopen _ _, _, _, λ ni, ⟨ni.2, HDS _ _⟩⟩],
  { refine [expr Union_eq_univ_iff.2 (λ x, _)],
    rcases [expr Dcov x, "with", "⟨", ident n, ",", ident i, ",", ident h, "⟩"],
    exact [expr ⟨⟨n, i⟩, h⟩] },
  { intro [ident x],
    rcases [expr Dcov x, "with", "⟨", ident n, ",", ident i, ",", ident hn, "⟩"],
    have [] [":", expr «expr ∈ »(D n i, expr𝓝() x)] [],
    from [expr is_open.mem_nhds (Dopen _ _) hn],
    rcases [expr (nhds_basis_uniformity uniformity_basis_edist_inv_two_pow).mem_iff.1 this, "with", "⟨", ident k, ",", "-", ",", ident hsub, ":", expr «expr ⊆ »(ball x «expr ^ »(«expr ⁻¹»(2), k), D n i), "⟩"],
    set [] [ident B] [] [":="] [expr ball x «expr ^ »(«expr ⁻¹»(2), «expr + »(«expr + »(n, k), 1))] [],
    refine [expr ⟨B, ball_mem_nhds _ (pow_pos _), _⟩],
    have [ident Hgt] [":", expr ∀ (m «expr ≥ » «expr + »(«expr + »(n, k), 1)) (i : ι), disjoint (D m i) B] [],
    { rintros [ident m, ident hm, ident i, ident y, "⟨", ident hym, ",", ident hyx, "⟩"],
      rcases [expr memD.1 hym, "with", "⟨", ident z, ",", ident rfl, ",", ident hzi, ",", ident H, ",", ident hz, "⟩"],
      have [] [":", expr «expr ∉ »(z, ball x «expr ^ »(«expr ⁻¹»(2), k))] [],
      from [expr λ hz, H n (by linarith [] [] []) i (hsub hz)],
      apply [expr this],
      calc
        «expr ≤ »(edist z x, «expr + »(edist y z, edist y x)) : edist_triangle_left _ _ _
        «expr < »(..., «expr + »(«expr ^ »(«expr ⁻¹»(2), m), «expr ^ »(«expr ⁻¹»(2), «expr + »(«expr + »(n, k), 1)))) : ennreal.add_lt_add hz hyx
        «expr ≤ »(..., «expr + »(«expr ^ »(«expr ⁻¹»(2), «expr + »(k, 1)), «expr ^ »(«expr ⁻¹»(2), «expr + »(k, 1)))) : add_le_add «expr $ »(hpow_le, by linarith [] [] []) «expr $ »(hpow_le, by linarith [] [] [])
        «expr = »(..., «expr ^ »(«expr ⁻¹»(2), k)) : by rw ["[", "<-", expr two_mul, ",", expr h2pow, "]"] [] },
    have [ident Hle] [":", expr ∀ m «expr ≤ » «expr + »(n, k), set.subsingleton {j | «expr ∩ »(D m j, B).nonempty}] [],
    { rintros [ident m, ident hm, ident j₁, "⟨", ident y, ",", ident hyD, ",", ident hyB, "⟩", ident j₂, "⟨", ident z, ",", ident hzD, ",", ident hzB, "⟩"],
      by_contra [ident h],
      wlog [ident h] [":", expr «expr < »(j₁, j₂)] [":=", expr ne.lt_or_lt h] ["using", "[", ident j₁, ident j₂, ident y, ident z, ",", ident j₂, ident j₁, ident z, ident y, "]"],
      rcases [expr memD.1 hyD, "with", "⟨", ident y', ",", ident rfl, ",", ident hsuby, ",", "-", ",", ident hdisty, "⟩"],
      rcases [expr memD.1 hzD, "with", "⟨", ident z', ",", ident rfl, ",", "-", ",", "-", ",", ident hdistz, "⟩"],
      suffices [] [":", expr «expr < »(edist z' y', «expr * »(3, «expr ^ »(«expr ⁻¹»(2), m)))],
      from [expr nmem_of_lt_ind h (hsuby this)],
      calc
        «expr ≤ »(edist z' y', «expr + »(edist z' x, edist x y')) : edist_triangle _ _ _
        «expr ≤ »(..., «expr + »(«expr + »(edist z z', edist z x), «expr + »(edist y x, edist y y'))) : add_le_add (edist_triangle_left _ _ _) (edist_triangle_left _ _ _)
        «expr < »(..., «expr + »(«expr + »(«expr ^ »(«expr ⁻¹»(2), m), «expr ^ »(«expr ⁻¹»(2), «expr + »(«expr + »(n, k), 1))), «expr + »(«expr ^ »(«expr ⁻¹»(2), «expr + »(«expr + »(n, k), 1)), «expr ^ »(«expr ⁻¹»(2), m)))) : by apply_rules ["[", expr ennreal.add_lt_add, "]"]
        «expr = »(..., «expr * »(2, «expr + »(«expr ^ »(«expr ⁻¹»(2), m), «expr ^ »(«expr ⁻¹»(2), «expr + »(«expr + »(n, k), 1))))) : by simp [] [] ["only"] ["[", expr two_mul, ",", expr add_comm, "]"] [] []
        «expr ≤ »(..., «expr * »(2, «expr + »(«expr ^ »(«expr ⁻¹»(2), m), «expr ^ »(«expr ⁻¹»(2), «expr + »(m, 1))))) : «expr $ »(ennreal.mul_le_mul le_rfl, «expr $ »(add_le_add le_rfl, hpow_le (add_le_add hm le_rfl)))
        «expr = »(..., «expr * »(3, «expr ^ »(«expr ⁻¹»(2), m))) : by rw ["[", expr mul_add, ",", expr h2pow, ",", expr bit1, ",", expr add_mul, ",", expr one_mul, "]"] [] },
    have [] [":", expr «expr⋃ , »((m «expr ≤ » «expr + »(n, k))
      (i «expr ∈ » {i : ι | «expr ∩ »(D m i, B).nonempty}), {(m, i)}).finite] [],
    from [expr (finite_le_nat _).bUnion (λ i hi, (Hle i hi).finite.bUnion (λ _ _, finite_singleton _))],
    refine [expr this.subset (λ I hI, _)],
    simp [] [] ["only"] ["[", expr mem_Union, "]"] [] [],
    refine [expr ⟨I.1, _, I.2, hI, prod.mk.eta.symm⟩],
    exact [expr not_lt.1 (λ hlt, Hgt I.1 hlt I.2 hI.some_spec)] }
end

instance (priority := 100)normal_of_emetric [EmetricSpace α] : NormalSpace α :=
  normal_of_paracompact_t2

end Emetric

