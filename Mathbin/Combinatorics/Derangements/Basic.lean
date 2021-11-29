import Mathbin.Data.Equiv.Basic 
import Mathbin.Data.Equiv.Option 
import Mathbin.Dynamics.FixedPoints.Basic 
import Mathbin.GroupTheory.Perm.Option

/-!
# Derangements on types

In this file we define `derangements α`, the set of derangements on a type `α`.

We also define some equivalences involving various subtypes of `perm α` and `derangements α`:
* `derangements_option_equiv_sigma_at_most_one_fixed_point`: An equivalence between
  `derangements (option α)` and the sigma-type `Σ a : α, {f : perm α // fixed_points f ⊆ a}`.
* `derangements_recursion_equiv`: An equivalence between `derangements (option α)` and the
  sigma-type `Σ a : α, (derangements (({a}ᶜ : set α) : Type _) ⊕ derangements α)` which is later
  used to inductively count the number of derangements.

In order to prove the above, we also prove some results about the effect of `equiv.remove_none`
on derangements: `remove_none.fiber_none` and `remove_none.fiber_some`.
-/


open Equiv Function

/-- A permutation is a derangement if it has no fixed points. -/
def Derangements (α : Type _) : Set (perm α) :=
  { f:perm α | ∀ x : α, f x ≠ x }

variable {α β : Type _}

theorem mem_derangements_iff_fixed_points_eq_empty {f : perm α} : f ∈ Derangements α ↔ fixed_points f = ∅ :=
  Set.eq_empty_iff_forall_not_mem.symm

/-- If `α` is equivalent to `β`, then `derangements α` is equivalent to `derangements β`. -/
def Equiv.derangementsCongr (e : α ≃ β) : Derangements α ≃ Derangements β :=
  e.perm_congr.subtype_equiv$
    fun f =>
      e.forall_congr$
        by 
          simp 

namespace Derangements

/-- Derangements on a subtype are equivalent to permutations on the original type where points are
fixed iff they are not in the subtype. -/
protected def subtype_equiv (p : α → Prop) [DecidablePred p] :
  Derangements (Subtype p) ≃ { f : perm α // ∀ a, ¬p a ↔ a ∈ fixed_points f } :=
  calc
    Derangements (Subtype p) ≃
      { f : { f : perm α // ∀ a, ¬p a → a ∈ fixed_points f } // ∀ a, a ∈ fixed_points f → ¬p a } :=
    by 
      refine' (perm.subtype_equiv_subtype_perm p).subtypeEquiv fun f => ⟨fun hf a hfa ha => _, _⟩
      ·
        refine' hf ⟨a, ha⟩ (Subtype.ext _)
        rwa [mem_fixed_points, is_fixed_pt, perm.subtype_equiv_subtype_perm, @coe_fn_coe_base', Equiv.coe_fn_mk,
          Subtype.coe_mk, Equiv.Perm.of_subtype_apply_of_mem] at hfa 
      rintro hf ⟨a, ha⟩ hfa 
      refine' hf _ _ ha 
      change perm.subtype_equiv_subtype_perm p f a = a 
      rw [perm.subtype_equiv_subtype_perm_apply_of_mem f ha, hfa, Subtype.coe_mk]
    _ ≃ { f : perm α // ∃ h : ∀ a, ¬p a → a ∈ fixed_points f, ∀ a, a ∈ fixed_points f → ¬p a } :=
    subtype_subtype_equiv_subtype_exists _ _ 
    _ ≃ { f : perm α // ∀ a, ¬p a ↔ a ∈ fixed_points f } :=
    subtype_equiv_right
      fun f =>
        by 
          simpRw [exists_prop, ←forall_and_distrib, ←iff_iff_implies_and_implies]
    

/-- The set of permutations that fix either `a` or nothing is equivalent to the sum of:
    - derangements on `α`
    - derangements on `α` minus `a`. -/
def at_most_one_fixed_point_equiv_sum_derangements [DecidableEq α] (a : α) :
  { f : perm α // fixed_points f ⊆ {a} } ≃ Sum (Derangements («expr ᶜ» {a} : Set α)) (Derangements α) :=
  calc
    { f : perm α // fixed_points f ⊆ {a} } ≃
      Sum { f : { f : perm α // fixed_points f ⊆ {a} } // a ∈ fixed_points f }
        { f : { f : perm α // fixed_points f ⊆ {a} } // a ∉ fixed_points f } :=
    (Equiv.sumCompl _).symm 
    _ ≃
      Sum { f : perm α // fixed_points f ⊆ {a} ∧ a ∈ fixed_points f }
        { f : perm α // fixed_points f ⊆ {a} ∧ a ∉ fixed_points f } :=
    by 
      refine' Equiv.sumCongr _ _ <;>
        ·
          convert subtype_subtype_equiv_subtype_inter _ _ 
          ext f 
          rfl 
    _ ≃ Sum { f : perm α // fixed_points f = {a} } { f : perm α // fixed_points f = ∅ } :=
    by 
      refine' Equiv.sumCongr (subtype_equiv_right$ fun f => _) (subtype_equiv_right$ fun f => _)
      ·
        rw [Set.eq_singleton_iff_unique_mem, and_comm]
        rfl
      ·
        rw [Set.eq_empty_iff_forall_not_mem]
        refine' ⟨fun h x hx => h.2 (h.1 hx ▸ hx), fun h => ⟨fun x hx => (h _ hx).elim, h _⟩⟩
    _ ≃ Sum (Derangements («expr ᶜ» {a} : Set α)) (Derangements α) :=
    by 
      refine'
        Equiv.sumCongr ((Derangements.subtypeEquiv _).trans$ subtype_equiv_right$ fun x => _).symm
          (subtype_equiv_right$ fun f => mem_derangements_iff_fixed_points_eq_empty.symm)
      rw [eq_comm, Set.ext_iff]
      simpRw [Set.mem_compl_iff, not_not]
    

namespace Equiv

variable [DecidableEq α]

/-- The set of permutations `f` such that the preimage of `(a, f)` under
    `equiv.perm.decompose_option` is a derangement. -/
def remove_none.fiber (a : Option α) : Set (perm α) :=
  { f:perm α | (a, f) ∈ Equiv.Perm.decomposeOption '' Derangements (Option α) }

theorem remove_none.mem_fiber (a : Option α) (f : perm α) :
  f ∈ remove_none.fiber a ↔ ∃ F : perm (Option α), F ∈ Derangements (Option α) ∧ F none = a ∧ remove_none F = f :=
  by 
    simp [remove_none.fiber, Derangements]

theorem remove_none.fiber_none : remove_none.fiber (@none α) = ∅ :=
  by 
    rw [Set.eq_empty_iff_forall_not_mem]
    intro f hyp 
    rw [remove_none.mem_fiber] at hyp 
    rcases hyp with ⟨F, F_derangement, F_none, _⟩
    exact F_derangement none F_none

-- error in Combinatorics.Derangements.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For any `a : α`, the fiber over `some a` is the set of permutations
    where `a` is the only possible fixed point. -/
theorem remove_none.fiber_some
(a : α) : «expr = »(remove_none.fiber (some a), {f : perm α | «expr ⊆ »(fixed_points f, {a})}) :=
begin
  ext [] [ident f] [],
  split,
  { rw [expr remove_none.mem_fiber] [],
    rintro ["⟨", ident F, ",", ident F_derangement, ",", ident F_none, ",", ident rfl, "⟩", ident x, ident x_fixed],
    rw [expr mem_fixed_points_iff] ["at", ident x_fixed],
    apply_fun [expr some] ["at", ident x_fixed] [],
    cases [expr Fx, ":", expr F (some x)] ["with", ident y],
    { rwa ["[", expr remove_none_none F Fx, ",", expr F_none, ",", expr option.some_inj, ",", expr eq_comm, "]"] ["at", ident x_fixed] },
    { exfalso,
      rw [expr remove_none_some F ⟨y, Fx⟩] ["at", ident x_fixed],
      exact [expr F_derangement _ x_fixed] } },
  { intro [ident h_opfp],
    use [expr equiv.perm.decompose_option.symm (some a, f)],
    split,
    { intro [ident x],
      apply_fun [expr swap none (some a)] [] [],
      simp [] [] ["only"] ["[", expr perm.decompose_option_symm_apply, ",", expr swap_apply_self, ",", expr perm.coe_mul, "]"] [] [],
      cases [expr x] [],
      { simp [] [] [] [] [] [] },
      simp [] [] ["only"] ["[", expr equiv_functor.map_equiv_apply, ",", expr equiv_functor.map, ",", expr option.map_eq_map, ",", expr option.map_some', "]"] [] [],
      by_cases [expr x_vs_a, ":", expr «expr = »(x, a)],
      { rw ["[", expr x_vs_a, ",", expr swap_apply_right, "]"] [],
        apply [expr option.some_ne_none] },
      have [ident ne_1] [":", expr «expr ≠ »(some x, none)] [":=", expr option.some_ne_none _],
      have [ident ne_2] [":", expr «expr ≠ »(some x, some a)] [":=", expr (option.some_injective α).ne_iff.mpr x_vs_a],
      rw ["[", expr swap_apply_of_ne_of_ne ne_1 ne_2, ",", expr (option.some_injective α).ne_iff, "]"] [],
      intro [ident contra],
      exact [expr x_vs_a (h_opfp contra)] },
    { rw [expr apply_symm_apply] [] } }
end

end Equiv

section Option

variable [DecidableEq α]

-- error in Combinatorics.Derangements.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The set of derangements on `option α` is equivalent to the union over `a : α`
    of "permutations with `a` the only possible fixed point". -/
def derangements_option_equiv_sigma_at_most_one_fixed_point : «expr ≃ »(derangements (option α), «exprΣ , »((a : α), {f : perm α | «expr ⊆ »(fixed_points f, {a})})) :=
begin
  have [ident fiber_none_is_false] [":", expr equiv.remove_none.fiber (@none α) → false] [],
  { rw [expr equiv.remove_none.fiber_none] [],
    exact [expr is_empty.false] },
  calc
    «expr ≃ »(derangements (option α), «expr '' »(equiv.perm.decompose_option, derangements (option α))) : equiv.image _ _
    «expr ≃ »(..., «exprΣ , »((a : option α), «expr↥ »(equiv.remove_none.fiber a))) : set_prod_equiv_sigma _
    «expr ≃ »(..., «exprΣ , »((a : α), «expr↥ »(equiv.remove_none.fiber (some a)))) : sigma_option_equiv_of_some _ fiber_none_is_false
    «expr ≃ »(..., «exprΣ , »((a : α), {f : perm α | «expr ⊆ »(fixed_points f, {a})})) : by simp_rw [expr equiv.remove_none.fiber_some] []
end

/-- The set of derangements on `option α` is equivalent to the union over all `a : α` of
    "derangements on `α` ⊕ derangements on `{a}ᶜ`". -/
def derangements_recursion_equiv :
  Derangements (Option α) ≃ Σa : α, Sum (Derangements ((«expr ᶜ» {a} : Set α) : Type _)) (Derangements α) :=
  derangements_option_equiv_sigma_at_most_one_fixed_point.trans
    (sigma_congr_right at_most_one_fixed_point_equiv_sum_derangements)

end Option

end Derangements

