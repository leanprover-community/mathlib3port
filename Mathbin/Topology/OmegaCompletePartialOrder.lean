import Mathbin.Topology.Basic 
import Mathbin.Order.OmegaCompletePartialOrder

/-!
# Scott Topological Spaces

A type of topological spaces whose notion
of continuity is equivalent to continuity in ωCPOs.

## Reference

 * https://ncatlab.org/nlab/show/Scott+topology

-/


open OmegaCompletePartialOrder

open_locale Classical

universe u

namespace Scott

/-- `x` is an `ω`-Sup of a chain `c` if it is the least upper bound of the range of `c`. -/
def is_ωSup {α : Type u} [Preorderₓ α] (c : chain α) (x : α) : Prop :=
  (∀ i, c i ≤ x) ∧ ∀ y, (∀ i, c i ≤ y) → x ≤ y

theorem is_ωSup_iff_is_lub {α : Type u} [Preorderₓ α] {c : chain α} {x : α} : is_ωSup c x ↔ IsLub (Set.Range c) x :=
  by 
    simp [is_ωSup, IsLub, IsLeast, UpperBounds, LowerBounds]

variable(α : Type u)[OmegaCompletePartialOrder α]

attribute [local irreducible] Set

/-- The characteristic function of open sets is monotone and preserves
the limits of chains. -/
def IsOpen (s : Set α) : Prop :=
  continuous' fun x => x ∈ s

theorem is_open_univ : IsOpen α Set.Univ :=
  ⟨fun x y h =>
      by 
        simp only [Set.mem_univ] <;> rfl',
    by 
      convert @CompleteLattice.top_continuous α Prop _ _ <;> ext <;> simp ⟩

-- error in Topology.OmegaCompletePartialOrder: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
theorem is_open.inter (s t : set α) : is_open α s → is_open α t → is_open α «expr ∩ »(s, t) :=
begin
  simp [] [] ["only"] ["[", expr is_open, ",", expr exists_imp_distrib, ",", expr continuous', "]"] [] [],
  intros [ident h₀, ident h₁, ident h₂, ident h₃],
  rw ["<-", expr set.inf_eq_inter] [],
  let [ident s'] [":", expr «expr →ₘ »(α, exprProp())] [":=", expr ⟨λ x, «expr ∈ »(x, s), h₀⟩],
  let [ident t'] [":", expr «expr →ₘ »(α, exprProp())] [":=", expr ⟨λ x, «expr ∈ »(x, t), h₂⟩],
  split,
  { change [expr omega_complete_partial_order.continuous «expr ⊓ »(s', t')] [] [],
    haveI [] [":", expr is_total exprProp() ((«expr ≤ »))] [":=", expr ⟨@le_total exprProp() _⟩],
    apply [expr complete_lattice.inf_continuous]; assumption },
  { intros [ident x, ident y, ident h],
    apply [expr and_implies]; solve_by_elim [] [] ["[", expr h₀ h, ",", expr h₂ h, "]"] [] }
end

-- error in Topology.OmegaCompletePartialOrder: ././Mathport/Syntax/Translate/Basic.lean:340:40: in introv: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem is_open_sUnion : ∀ s, ∀ t «expr ∈ » s, is_open α t → is_open α «expr⋃₀ »(s) :=
begin
  introv [ident h₀],
  suffices [] [":", expr is_open α {x | Sup «expr '' »(flip ((«expr ∈ »)), s) x}],
  { convert [] [expr this] [],
    ext [] [] [],
    simp [] [] ["only"] ["[", expr set.sUnion, ",", expr Sup, ",", expr set.mem_image, ",", expr set.mem_set_of_eq, ",", expr supr, ",", expr conditionally_complete_lattice.Sup, ",", expr exists_exists_and_eq_and, ",", expr complete_lattice.Sup, ",", expr exists_prop, ",", expr set.mem_range, ",", expr set_coe.exists, ",", expr eq_iff_iff, ",", expr subtype.coe_mk, "]"] [] [],
    tauto [] },
  dsimp [] ["[", expr is_open, "]"] [] ["at", "*"],
  apply [expr complete_lattice.Sup_continuous' _],
  introv [ident ht],
  specialize [expr h₀ {x | f x} _],
  { simp [] [] ["only"] ["[", expr flip, ",", expr set.mem_image, "]"] [] ["at", "*"],
    rcases [expr ht, "with", "⟨", ident x, ",", ident h₀, ",", ident h₁, "⟩"],
    subst [expr h₁],
    simpa [] [] [] [] [] [] },
  { simpa [] [] [] [] [] ["using", expr h₀] }
end

end Scott

/-- A Scott topological space is defined on preorders
such that their open sets, seen as a function `α → Prop`,
preserves the joins of ω-chains  -/
@[reducible]
def Scott (α : Type u) :=
  α

instance Scott.topologicalSpace (α : Type u) [OmegaCompletePartialOrder α] : TopologicalSpace (Scott α) :=
  { IsOpen := Scott.IsOpen α, is_open_univ := Scott.is_open_univ α, is_open_inter := Scott.IsOpen.inter α,
    is_open_sUnion := Scott.is_open_sUnion α }

section NotBelow

variable{α : Type _}[OmegaCompletePartialOrder α](y : Scott α)

/-- `not_below` is an open set in `Scott α` used
to prove the monotonicity of continuous functions -/
def NotBelow :=
  { x | ¬x ≤ y }

theorem not_below_is_open : IsOpen (NotBelow y) :=
  by 
    have h : Monotone (NotBelow y)
    ·
      intro x y' h 
      simp only [NotBelow, SetOf, le_Prop_eq]
      intro h₀ h₁ 
      apply h₀ (le_transₓ h h₁)
    exists h 
    rintro c 
    apply eq_of_forall_ge_iff 
    intro z 
    rw [ωSup_le_iff]
    simp only [ωSup_le_iff, NotBelow, Set.mem_set_of_eq, le_Prop_eq, PreorderHom.coe_fun_mk, chain.map_coe,
      Function.comp_app, exists_imp_distrib, not_forall]

end NotBelow

open Scott hiding IsOpen

open OmegaCompletePartialOrder

theorem is_ωSup_ωSup {α} [OmegaCompletePartialOrder α] (c : chain α) : is_ωSup c (ωSup c) :=
  by 
    split 
    ·
      apply le_ωSup
    ·
      apply ωSup_le

-- error in Topology.OmegaCompletePartialOrder: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contradiction: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem Scott_continuous_of_continuous
{α β}
[omega_complete_partial_order α]
[omega_complete_partial_order β]
(f : Scott α → Scott β)
(hf : continuous f) : omega_complete_partial_order.continuous' f :=
begin
  simp [] [] ["only"] ["[", expr continuous_def, ",", expr («expr ⁻¹' »), "]"] [] ["at", ident hf],
  have [ident h] [":", expr monotone f] [],
  { intros [ident x, ident y, ident h],
    cases [expr hf {x | «expr¬ »(«expr ≤ »(x, f y))} (not_below_is_open _)] ["with", ident hf, ident hf'],
    clear [ident hf'],
    specialize [expr hf h],
    simp [] [] ["only"] ["[", expr set.preimage, ",", expr set_of, ",", expr («expr ∈ »), ",", expr set.mem, ",", expr le_Prop_eq, "]"] [] ["at", ident hf],
    by_contradiction [ident H],
    apply [expr hf H (le_refl (f y))] },
  existsi [expr h],
  intro [ident c],
  apply [expr eq_of_forall_ge_iff],
  intro [ident z],
  specialize [expr hf _ (not_below_is_open z)],
  cases [expr hf] [],
  specialize [expr hf_h c],
  simp [] [] ["only"] ["[", expr not_below, ",", expr preorder_hom.coe_fun_mk, ",", expr eq_iff_iff, ",", expr set.mem_set_of_eq, "]"] [] ["at", ident hf_h],
  rw ["[", "<-", expr not_iff_not, "]"] [],
  simp [] [] ["only"] ["[", expr ωSup_le_iff, ",", expr hf_h, ",", expr ωSup, ",", expr supr, ",", expr Sup, ",", expr complete_lattice.Sup, ",", expr complete_semilattice_Sup.Sup, ",", expr exists_prop, ",", expr set.mem_range, ",", expr preorder_hom.coe_fun_mk, ",", expr chain.map_coe, ",", expr function.comp_app, ",", expr eq_iff_iff, ",", expr not_forall, "]"] [] [],
  tauto []
end

theorem continuous_of_Scott_continuous {α β} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
  (f : Scott α → Scott β) (hf : OmegaCompletePartialOrder.Continuous' f) : Continuous f :=
  by 
    rw [continuous_def]
    intro s hs 
    change continuous' (s ∘ f)
    cases' hs with hs hs' 
    cases' hf with hf hf' 
    apply continuous.of_bundled 
    apply continuous_comp _ _ hf' hs'

