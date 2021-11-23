import Mathbin.Tactic.ApplyFun 
import Mathbin.Data.Set.Pairwise 
import Mathbin.Topology.UniformSpace.Basic 
import Mathbin.Topology.Separation

/-!
# Hausdorff properties of uniform spaces. Separation quotient.

This file studies uniform spaces whose underlying topological spaces are separated
(also known as Hausdorff or T₂).
This turns out to be equivalent to asking that the intersection of all entourages
is the diagonal only. This condition actually implies the stronger separation property
that the space is regular (T₃), hence those conditions are equivalent for topologies coming from
a uniform structure.

More generally, the intersection `𝓢 X` of all entourages of `X`, which has type `set (X × X)` is an
equivalence relation on `X`. Points which are equivalent under the relation are basically
undistinguishable from the point of view of the uniform structure. For instance any uniformly
continuous function will send equivalent points to the same value.

The quotient `separation_quotient X` of `X` by `𝓢 X` has a natural uniform structure which is
separated, and satisfies a universal property: every uniformly continuous function
from `X` to a separated uniform space uniquely factors through `separation_quotient X`.
As usual, this allows to turn `separation_quotient` into a functor (but we don't use the
category theory library in this file).

These notions admit relative versions, one can ask that `s : set X` is separated, this
is equivalent to asking that the uniform structure induced on `s` is separated.

## Main definitions

* `separation_relation X : set (X × X)`: the separation relation
* `separated_space X`: a predicate class asserting that `X` is separated
* `is_separated s`: a predicate asserting that `s : set X` is separated
* `separation_quotient X`: the maximal separated quotient of `X`.
* `separation_quotient.lift f`: factors a map `f : X → Y` through the separation quotient of `X`.
* `separation_quotient.map f`: turns a map `f : X → Y` into a map between the separation quotients
  of `X` and `Y`.

## Main results

* `separated_iff_t2`: the equivalence between being separated and being Hausdorff for uniform
  spaces.
* `separation_quotient.uniform_continuous_lift`: factoring a uniformly continuous map through the
  separation quotient gives a uniformly continuous map.
* `separation_quotient.uniform_continuous_map`: maps induced between separation quotients are
  uniformly continuous.

## Notations

Localized in `uniformity`, we have the notation `𝓢 X` for the separation relation
on a uniform space `X`,

## Implementation notes

The separation setoid `separation_setoid` is not declared as a global instance.
It is made a local instance while building the theory of `separation_quotient`.
The factored map `separation_quotient.lift f` is defined without imposing any condition on
`f`, but returns junk if `f` is not uniformly continuous (constant junk hence it is always
uniformly continuous).

-/


open Filter TopologicalSpace Set Classical Function UniformSpace

open_locale Classical TopologicalSpace uniformity Filter

noncomputable theory

set_option eqn_compiler.zeta true

universe u v w

variable{α : Type u}{β : Type v}{γ : Type w}

variable[UniformSpace α][UniformSpace β][UniformSpace γ]

/-!
### Separated uniform spaces
-/


/-- The separation relation is the intersection of all entourages.
  Two points which are related by the separation relation are "indistinguishable"
  according to the uniform structure. -/
protected def SeparationRel (α : Type u) [u : UniformSpace α] :=
  ⋂₀(𝓤 α).Sets

localized [uniformity] notation "𝓢" => SeparationRel

theorem separated_equiv : Equivalenceₓ fun x y => (x, y) ∈ 𝓢 α :=
  ⟨fun x => fun s => refl_mem_uniformity,
    fun x y =>
      fun h s : Set (α × α) hs =>
        have  : preimage Prod.swap s ∈ 𝓤 α := symm_le_uniformity hs 
        h _ this,
    fun x y z hxy : (x, y) ∈ 𝓢 α hyz : (y, z) ∈ 𝓢 α s hs : s ∈ 𝓤 α =>
      let ⟨t, ht, (h_ts : CompRel t t ⊆ s)⟩ := comp_mem_uniformity_sets hs 
      h_ts$ show (x, z) ∈ CompRel t t from ⟨y, hxy t ht, hyz t ht⟩⟩

/-- A uniform space is separated if its separation relation is trivial (each point
is related only to itself). -/
class SeparatedSpace(α : Type u)[UniformSpace α] : Prop where 
  out : 𝓢 α = IdRel

theorem separated_space_iff {α : Type u} [UniformSpace α] : SeparatedSpace α ↔ 𝓢 α = IdRel :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem separated_def {α : Type u} [UniformSpace α] : SeparatedSpace α ↔ ∀ x y, (∀ r _ : r ∈ 𝓤 α, (x, y) ∈ r) → x = y :=
  by 
    simp [separated_space_iff, id_rel_subset.2 separated_equiv.1, subset.antisymm_iff] <;>
      simp [subset_def, SeparationRel]

theorem separated_def' {α : Type u} [UniformSpace α] :
  SeparatedSpace α ↔ ∀ x y, x ≠ y → ∃ (r : _)(_ : r ∈ 𝓤 α), (x, y) ∉ r :=
  separated_def.trans$
    forall_congrₓ$
      fun x =>
        forall_congrₓ$
          fun y =>
            by 
              rw [←not_imp_not] <;> simp [not_forall]

theorem eq_of_uniformity {α : Type _} [UniformSpace α] [SeparatedSpace α] {x y : α} (h : ∀ {V}, V ∈ 𝓤 α → (x, y) ∈ V) :
  x = y :=
  separated_def.mp ‹SeparatedSpace α› x y fun _ => h

theorem eq_of_uniformity_basis {α : Type _} [UniformSpace α] [SeparatedSpace α] {ι : Type _} {p : ι → Prop}
  {s : ι → Set (α × α)} (hs : (𝓤 α).HasBasis p s) {x y : α} (h : ∀ {i}, p i → (x, y) ∈ s i) : x = y :=
  eq_of_uniformity
    fun V V_in =>
      let ⟨i, hi, H⟩ := hs.mem_iff.mp V_in 
      H (h hi)

theorem eq_of_forall_symmetric {α : Type _} [UniformSpace α] [SeparatedSpace α] {x y : α}
  (h : ∀ {V}, V ∈ 𝓤 α → SymmetricRel V → (x, y) ∈ V) : x = y :=
  eq_of_uniformity_basis has_basis_symmetric
    (by 
      simpa [and_imp] using fun _ => h)

theorem id_rel_sub_separation_relation (α : Type _) [UniformSpace α] : IdRel ⊆ 𝓢 α :=
  by 
    unfold SeparationRel 
    rw [id_rel_subset]
    intro x 
    suffices  : ∀ t _ : t ∈ 𝓤 α, (x, x) ∈ t
    ·
      simpa only [refl_mem_uniformity]
    exact fun t => refl_mem_uniformity

theorem separation_rel_comap {f : α → β} (h : ‹UniformSpace α› = UniformSpace.comap f ‹UniformSpace β›) :
  𝓢 α = Prod.mapₓ f f ⁻¹' 𝓢 β :=
  by 
    dsimp [SeparationRel]
    simpRw [uniformity_comap h, (Filter.comap_has_basis (Prod.mapₓ f f) (𝓤 β)).sInter_sets, ←preimage_Inter,
      sInter_eq_bInter]
    rfl

protected theorem Filter.HasBasis.separation_rel {ι : Sort _} {p : ι → Prop} {s : ι → Set (α × α)}
  (h : has_basis (𝓤 α) p s) : 𝓢 α = ⋂(i : _)(hi : p i), s i :=
  by 
    unfold SeparationRel 
    rw [h.sInter_sets]

theorem separation_rel_eq_inter_closure : 𝓢 α = ⋂₀(Closure '' (𝓤 α).Sets) :=
  by 
    simp [uniformity_has_basis_closure.separation_rel]

theorem is_closed_separation_rel : IsClosed (𝓢 α) :=
  by 
    rw [separation_rel_eq_inter_closure]
    apply is_closed_sInter 
    rintro _ ⟨t, t_in, rfl⟩
    exact is_closed_closure

theorem separated_iff_t2 : SeparatedSpace α ↔ T2Space α :=
  by 
    classical 
    split  <;> intro h
    ·
      rw [t2_iff_is_closed_diagonal, ←show 𝓢 α = diagonal α from h.1]
      exact is_closed_separation_rel
    ·
      rw [separated_def']
      intro x y hxy 
      rcases t2_separation hxy with ⟨u, v, uo, vo, hx, hy, h⟩
      rcases is_open_iff_ball_subset.1 uo x hx with ⟨r, hrU, hr⟩
      exact ⟨r, hrU, fun H => disjoint_iff.2 h ⟨hr H, hy⟩⟩

-- error in Topology.UniformSpace.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[priority 100] instance separated_regular [separated_space α] : regular_space α :=
{ t0 := by { haveI [] [] [":=", expr separated_iff_t2.mp «expr‹ ›»(_)],
    exact [expr t1_space.t0_space.t0] },
  regular := λ s a hs ha, have «expr ∈ »(«expr ᶜ»(s), expr𝓝() a), from is_open.mem_nhds hs.is_open_compl ha,
  have «expr ∈ »({p : «expr × »(α, α) | «expr = »(p.1, a) → «expr ∈ »(p.2, «expr ᶜ»(s))}, expr𝓤() α), from mem_nhds_uniformity_iff_right.mp this,
  let ⟨d, hd, h⟩ := comp_mem_uniformity_sets this in
  let e := {y : α | «expr ∈ »((a, y), d)} in
  have hae : «expr ∈ »(a, closure e), from «expr $ »(subset_closure, refl_mem_uniformity hd),
  have «expr ⊆ »(set.prod (closure e) (closure e), comp_rel d (comp_rel (set.prod e e) d)), begin
    rw ["[", "<-", expr closure_prod_eq, ",", expr closure_eq_inter_uniformity, "]"] [],
    change [expr «expr ≤ »(«expr⨅ , »((d' «expr ∈ » expr𝓤() α), _), comp_rel d (comp_rel _ d))] [] [],
    exact [expr «expr $ »(infi_le_of_le d, «expr $ »(infi_le_of_le hd, le_refl _))]
  end,
  have e_subset : «expr ⊆ »(closure e, «expr ᶜ»(s)), from assume
  a'
  ha', let ⟨x, (hx : «expr ∈ »((a, x), d)), y, ⟨hx₁, hx₂⟩, (hy : «expr ∈ »((y, _), d))⟩ := @this ⟨a, a'⟩ ⟨hae, ha'⟩ in
  have «expr ∈ »((a, a'), comp_rel d d), from ⟨y, hx₂, hy⟩,
  h this rfl,
  have «expr ∈ »(closure e, expr𝓝() a), from (expr𝓝() a).sets_of_superset (mem_nhds_left a hd) subset_closure,
  have «expr = »(«expr ⊓ »(expr𝓝() a, expr𝓟() «expr ᶜ»(closure e)), «expr⊥»()), from (is_compl_principal (closure e)).inf_right_eq_bot_iff.2 (le_principal_iff.2 this),
  ⟨«expr ᶜ»(closure e), is_closed_closure.is_open_compl, assume x h₁ h₂, @e_subset x h₂ h₁, this⟩,
  ..@t2_space.t1_space _ _ (separated_iff_t2.mp «expr‹ ›»(_)) }

theorem is_closed_of_spaced_out [SeparatedSpace α] {V₀ : Set (α × α)} (V₀_in : V₀ ∈ 𝓤 α) {s : Set α}
  (hs : s.pairwise fun x y => (x, y) ∉ V₀) : IsClosed s :=
  by 
    rcases comp_symm_mem_uniformity_sets V₀_in with ⟨V₁, V₁_in, V₁_symm, h_comp⟩
    apply is_closed_of_closure_subset 
    intro x hx 
    rw [mem_closure_iff_ball] at hx 
    rcases hx V₁_in with ⟨y, hy, hy'⟩
    suffices  : x = y
    ·
      rwa [this]
    apply eq_of_forall_symmetric 
    intro V V_in V_symm 
    rcases hx (inter_mem V₁_in V_in) with ⟨z, hz, hz'⟩
    obtain rfl : z = y
    ·
      byContra hzy 
      exact hs z hz' y hy' hzy (h_comp$ mem_comp_of_mem_ball V₁_symm (ball_inter_left x _ _ hz) hy)
    exact ball_inter_right x _ _ hz

theorem is_closed_range_of_spaced_out {ι} [SeparatedSpace α] {V₀ : Set (α × α)} (V₀_in : V₀ ∈ 𝓤 α) {f : ι → α}
  (hf : Pairwise fun x y => (f x, f y) ∉ V₀) : IsClosed (range f) :=
  is_closed_of_spaced_out V₀_in$
    by 
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h 
      exact hf x y (mt (congr_argₓ f) h)

/-!
### Separated sets
-/


/-- A set `s` in a uniform space `α` is separated if the separation relation `𝓢 α`
induces the trivial relation on `s`. -/
def IsSeparated (s : Set α) : Prop :=
  ∀ x y _ : x ∈ s _ : y ∈ s, (x, y) ∈ 𝓢 α → x = y

theorem is_separated_def (s : Set α) : IsSeparated s ↔ ∀ x y _ : x ∈ s _ : y ∈ s, (x, y) ∈ 𝓢 α → x = y :=
  Iff.rfl

theorem is_separated_def' (s : Set α) : IsSeparated s ↔ s.prod s ∩ 𝓢 α ⊆ IdRel :=
  by 
    rw [is_separated_def]
    split 
    ·
      rintro h ⟨x, y⟩ ⟨⟨x_in, y_in⟩, H⟩
      simp [h x y x_in y_in H]
    ·
      intro h x y x_in y_in xy_in 
      rw [←mem_id_rel]
      exact h ⟨mk_mem_prod x_in y_in, xy_in⟩

theorem IsSeparated.mono {s t : Set α} (hs : IsSeparated s) (hts : t ⊆ s) : IsSeparated t :=
  fun x y hx hy => hs x y (hts hx) (hts hy)

theorem univ_separated_iff : IsSeparated (univ : Set α) ↔ SeparatedSpace α :=
  by 
    simp only [IsSeparated, mem_univ, true_implies_iff, separated_space_iff]
    split 
    ·
      intro h 
      exact subset.antisymm (fun ⟨x, y⟩ xy_in => h x y xy_in) (id_rel_sub_separation_relation α)
    ·
      intro h x y xy_in 
      rwa [h] at xy_in

theorem is_separated_of_separated_space [SeparatedSpace α] (s : Set α) : IsSeparated s :=
  by 
    rw [IsSeparated, SeparatedSpace.out]
    tauto

-- error in Topology.UniformSpace.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_separated_iff_induced {s : set α} : «expr ↔ »(is_separated s, separated_space s) :=
begin
  rw [expr separated_space_iff] [],
  change [expr «expr ↔ »(_, «expr = »(expr𝓢() {x // «expr ∈ »(x, s)}, _))] [] [],
  rw ["[", expr separation_rel_comap rfl, ",", expr is_separated_def', "]"] [],
  split; intro [ident h],
  { ext [] ["⟨", "⟨", ident x, ",", ident x_in, "⟩", ",", "⟨", ident y, ",", ident y_in, "⟩", "⟩"] [],
    suffices [] [":", expr «expr ↔ »(«expr ∈ »((x, y), expr𝓢() α), «expr = »(x, y))],
    by simpa [] [] ["only"] ["[", expr mem_id_rel, "]"] [] [],
    refine [expr ⟨λ H, h ⟨mk_mem_prod x_in y_in, H⟩, _⟩],
    rintro [ident rfl],
    exact [expr id_rel_sub_separation_relation α rfl] },
  { rintros ["⟨", ident x, ",", ident y, "⟩", "⟨", "⟨", ident x_in, ",", ident y_in, "⟩", ",", ident hS, "⟩"],
    have [ident A] [":", expr «expr ∈ »((⟨⟨x, x_in⟩, ⟨y, y_in⟩⟩ : «expr × »(«expr↥ »(s), «expr↥ »(s))), «expr ⁻¹' »(prod.map (coe : s → α) (coe : s → α), expr𝓢() α))] [],
    from [expr hS],
    simpa [] [] [] [] [] ["using", expr h.subset A] }
end

-- error in Topology.UniformSpace.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_of_uniformity_inf_nhds_of_is_separated
{s : set α}
(hs : is_separated s) : ∀
{x y : α}, «expr ∈ »(x, s) → «expr ∈ »(y, s) → cluster_pt (x, y) (expr𝓤() α) → «expr = »(x, y) :=
begin
  intros [ident x, ident y, ident x_in, ident y_in, ident H],
  have [] [":", expr ∀ V «expr ∈ » expr𝓤() α, «expr ∈ »((x, y), closure V)] [],
  { intros [ident V, ident V_in],
    rw [expr mem_closure_iff_cluster_pt] [],
    have [] [":", expr «expr ≤ »(expr𝓤() α, expr𝓟() V)] [],
    by rwa [expr le_principal_iff] [],
    exact [expr H.mono this] },
  apply [expr hs x y x_in y_in],
  simpa [] [] [] ["[", expr separation_rel_eq_inter_closure, "]"] [] []
end

-- error in Topology.UniformSpace.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_of_uniformity_inf_nhds [separated_space α] : ∀ {x y : α}, cluster_pt (x, y) (expr𝓤() α) → «expr = »(x, y) :=
begin
  have [] [":", expr is_separated (univ : set α)] [],
  { rw [expr univ_separated_iff] [],
    assumption },
  introv [],
  simpa [] [] [] [] [] ["using", expr eq_of_uniformity_inf_nhds_of_is_separated this]
end

/-!
### Separation quotient
-/


namespace UniformSpace

/-- The separation relation of a uniform space seen as a setoid. -/
def separation_setoid (α : Type u) [UniformSpace α] : Setoidₓ α :=
  ⟨fun x y => (x, y) ∈ 𝓢 α, separated_equiv⟩

attribute [local instance] separation_setoid

-- error in Topology.UniformSpace.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance separation_setoid.uniform_space
{α : Type u}
[u : uniform_space α] : uniform_space (quotient (separation_setoid α)) :=
{ to_topological_space := u.to_topological_space.coinduced (λ x, «expr⟦ ⟧»(x)),
  uniformity := map (λ p : «expr × »(α, α), («expr⟦ ⟧»(p.1), «expr⟦ ⟧»(p.2))) u.uniformity,
  refl := le_trans (by simp [] [] [] ["[", expr quotient.exists_rep, "]"] [] []) (filter.map_mono refl_le_uniformity),
  symm := «expr $ »(tendsto_map', by simp [] [] [] ["[", expr prod.swap, ",", expr («expr ∘ »), "]"] [] []; exact [expr tendsto_map.comp tendsto_swap_uniformity]),
  comp := calc
    «expr = »((map (λ
       p : «expr × »(α, α), («expr⟦ ⟧»(p.fst), «expr⟦ ⟧»(p.snd))) u.uniformity).lift' (λ
      s, comp_rel s s), u.uniformity.lift' «expr ∘ »(λ
      s, comp_rel s s, image (λ
       p : «expr × »(α, α), («expr⟦ ⟧»(p.fst), «expr⟦ ⟧»(p.snd))))) : «expr $ »(map_lift'_eq2, monotone_comp_rel monotone_id monotone_id)
    «expr ≤ »(..., u.uniformity.lift' «expr ∘ »(image (λ
       p : «expr × »(α, α), («expr⟦ ⟧»(p.fst), «expr⟦ ⟧»(p.snd))), λ
      s : set «expr × »(α, α), comp_rel s (comp_rel s s))) : «expr $ »(lift'_mono', assume
     (s hs)
     ⟨a, b⟩
     ⟨c, ⟨⟨a₁, a₂⟩, ha, a_eq⟩, ⟨⟨b₁, b₂⟩, hb, b_eq⟩⟩, begin
       simp [] [] [] [] [] ["at", ident a_eq],
       simp [] [] [] [] [] ["at", ident b_eq],
       have [ident h] [":", expr «expr = »(«expr⟦ ⟧»(a₂), «expr⟦ ⟧»(b₁))] [],
       { rw ["[", expr a_eq.right, ",", expr b_eq.left, "]"] [] },
       have [ident h] [":", expr «expr ∈ »((a₂, b₁), expr𝓢() α)] [":=", expr quotient.exact h],
       simp [] [] [] ["[", expr function.comp, ",", expr set.image, ",", expr comp_rel, ",", expr and.comm, ",", expr and.left_comm, ",", expr and.assoc, "]"] [] [],
       exact [expr ⟨a₁, a_eq.left, b₂, b_eq.right, a₂, ha, b₁, h s hs, hb⟩]
     end)
    «expr = »(..., map (λ
      p : «expr × »(α, α), («expr⟦ ⟧»(p.1), «expr⟦ ⟧»(p.2))) (u.uniformity.lift' (λ
       s : set «expr × »(α, α), comp_rel s (comp_rel s s)))) : by rw ["[", expr map_lift'_eq, "]"] []; exact [expr monotone_comp_rel monotone_id (monotone_comp_rel monotone_id monotone_id)]
    «expr ≤ »(..., map (λ
      p : «expr × »(α, α), («expr⟦ ⟧»(p.1), «expr⟦ ⟧»(p.2))) u.uniformity) : map_mono comp_le_uniformity3,
  is_open_uniformity := assume
  s, have ∀
  a, «expr ∈ »(«expr⟦ ⟧»(a), s) → «expr ↔ »(«expr ∈ »({p : «expr × »(α, α) | «expr = »(p.1, a) → «expr ∈ »(«expr⟦ ⟧»(p.2), s)}, expr𝓤() α), «expr ∈ »({p : «expr × »(α, α) | «expr ≈ »(p.1, a) → «expr ∈ »(«expr⟦ ⟧»(p.2), s)}, expr𝓤() α)), from assume
  a
  ha, ⟨assume h, let ⟨t, ht, hts⟩ := comp_mem_uniformity_sets h in
   have hts : ∀
   {a₁
    a₂}, «expr ∈ »((a, a₁), t) → «expr ∈ »((a₁, a₂), t) → «expr ∈ »(«expr⟦ ⟧»(a₂), s), from assume
   a₁ a₂ ha₁ ha₂, @hts (a, a₂) ⟨a₁, ha₁, ha₂⟩ rfl,
   have ht' : ∀ {a₁ a₂}, «expr ≈ »(a₁, a₂) → «expr ∈ »((a₁, a₂), t), from assume a₁ a₂ h, sInter_subset_of_mem ht h,
   «expr $ »(u.uniformity.sets_of_superset ht, assume
    ⟨a₁, a₂⟩
    (h₁
     h₂), hts «expr $ »(ht', setoid.symm h₂) h₁), assume
   h, «expr $ »(u.uniformity.sets_of_superset h, by simp [] [] [] [] [] [] { contextual := tt })⟩,
  begin
    simp [] [] [] ["[", expr topological_space.coinduced, ",", expr u.is_open_uniformity, ",", expr uniformity, ",", expr forall_quotient_iff, "]"] [] [],
    exact [expr ⟨λ h a ha, «expr $ »((this a ha).mp, h a ha), λ h a ha, «expr $ »((this a ha).mpr, h a ha)⟩]
  end }

theorem uniformity_quotient :
  𝓤 (Quotientₓ (separation_setoid α)) = (𝓤 α).map fun p : α × α => («expr⟦ ⟧» p.1, «expr⟦ ⟧» p.2) :=
  rfl

theorem uniform_continuous_quotient_mk : UniformContinuous (Quotientₓ.mk : α → Quotientₓ (separation_setoid α)) :=
  le_reflₓ _

theorem uniform_continuous_quotient {f : Quotientₓ (separation_setoid α) → β}
  (hf : UniformContinuous fun x => f («expr⟦ ⟧» x)) : UniformContinuous f :=
  hf

theorem uniform_continuous_quotient_lift {f : α → β} {h : ∀ a b, (a, b) ∈ 𝓢 α → f a = f b} (hf : UniformContinuous f) :
  UniformContinuous fun a => Quotientₓ.lift f h a :=
  uniform_continuous_quotient hf

theorem uniform_continuous_quotient_lift₂ {f : α → β → γ} {h : ∀ a c b d, (a, b) ∈ 𝓢 α → (c, d) ∈ 𝓢 β → f a c = f b d}
  (hf : UniformContinuous fun p : α × β => f p.1 p.2) :
  UniformContinuous fun p : _ × _ => Quotientₓ.lift₂ f h p.1 p.2 :=
  by 
    rw [UniformContinuous, uniformity_prod_eq_prod, uniformity_quotient, uniformity_quotient, Filter.prod_map_map_eq,
      Filter.tendsto_map'_iff, Filter.tendsto_map'_iff]
    rwa [UniformContinuous, uniformity_prod_eq_prod, Filter.tendsto_map'_iff] at hf

theorem comap_quotient_le_uniformity :
  ((𝓤$ Quotientₓ$ separation_setoid α).comap fun p : α × α => («expr⟦ ⟧» p.fst, «expr⟦ ⟧» p.snd)) ≤ 𝓤 α :=
  fun t' ht' =>
    let ⟨t, ht, tt_t'⟩ := comp_mem_uniformity_sets ht' 
    let ⟨s, hs, ss_t⟩ := comp_mem_uniformity_sets ht
    ⟨(fun p : α × α => («expr⟦ ⟧» p.1, «expr⟦ ⟧» p.2)) '' s, (𝓤 α).sets_of_superset hs$ fun x hx => ⟨x, hx, rfl⟩,
      fun ⟨a₁, a₂⟩ ⟨⟨b₁, b₂⟩, hb, ab_eq⟩ =>
        have  : «expr⟦ ⟧» b₁ = «expr⟦ ⟧» a₁ ∧ «expr⟦ ⟧» b₂ = «expr⟦ ⟧» a₂ := Prod.mk.inj ab_eq 
        have  : b₁ ≈ a₁ ∧ b₂ ≈ a₂ := And.imp Quotientₓ.exact Quotientₓ.exact this 
        have ab₁ : (a₁, b₁) ∈ t := (Setoidₓ.symm this.left) t ht 
        have ba₂ : (b₂, a₂) ∈ s := this.right s hs 
        tt_t' ⟨b₁, show ((a₁, a₂).1, b₁) ∈ t from ab₁, ss_t ⟨b₂, show ((b₁, a₂).1, b₂) ∈ s from hb, ba₂⟩⟩⟩

theorem comap_quotient_eq_uniformity :
  ((𝓤$ Quotientₓ$ separation_setoid α).comap fun p : α × α => («expr⟦ ⟧» p.fst, «expr⟦ ⟧» p.snd)) = 𝓤 α :=
  le_antisymmₓ comap_quotient_le_uniformity le_comap_map

instance separated_separation : SeparatedSpace (Quotientₓ (separation_setoid α)) :=
  ⟨Set.ext$
      fun ⟨a, b⟩ =>
        Quotientₓ.induction_on₂ a b$
          fun a b =>
            ⟨fun h =>
                have  : a ≈ b :=
                  fun s hs =>
                    have  :
                      s ∈ (𝓤$ Quotientₓ$ separation_setoid α).comap fun p : α × α => («expr⟦ ⟧» p.1, «expr⟦ ⟧» p.2) :=
                      comap_quotient_le_uniformity hs 
                    let ⟨t, ht, hts⟩ := this 
                    hts
                      (by 
                        dsimp [preimage]
                        exact h t ht)
                show «expr⟦ ⟧» a = «expr⟦ ⟧» b from Quotientₓ.sound this,
              fun heq : «expr⟦ ⟧» a = «expr⟦ ⟧» b => fun h hs => HEq ▸ refl_mem_uniformity hs⟩⟩

theorem separated_of_uniform_continuous {f : α → β} {x y : α} (H : UniformContinuous f) (h : x ≈ y) : f x ≈ f y :=
  fun _ h' => h _ (H h')

theorem eq_of_separated_of_uniform_continuous [SeparatedSpace β] {f : α → β} {x y : α} (H : UniformContinuous f)
  (h : x ≈ y) : f x = f y :=
  separated_def.1
      (by 
        infer_instance)
      _ _$
    separated_of_uniform_continuous H h

theorem _root_.is_separated.eq_of_uniform_continuous {f : α → β} {x y : α} {s : Set β} (hs : IsSeparated s)
  (hxs : f x ∈ s) (hys : f y ∈ s) (H : UniformContinuous f) (h : x ≈ y) : f x = f y :=
  (is_separated_def _).mp hs _ _ hxs hys$ fun _ h' => h _ (H h')

/-- The maximal separated quotient of a uniform space `α`. -/
def separation_quotient (α : Type _) [UniformSpace α] :=
  Quotientₓ (separation_setoid α)

namespace SeparationQuotient

instance  : UniformSpace (separation_quotient α) :=
  by 
    dunfold separation_quotient <;> infer_instance

instance  : SeparatedSpace (separation_quotient α) :=
  by 
    dunfold separation_quotient <;> infer_instance

instance  [Inhabited α] : Inhabited (separation_quotient α) :=
  by 
    unfold separation_quotient <;> infer_instance

/-- Factoring functions to a separated space through the separation quotient. -/
def lift [SeparatedSpace β] (f : α → β) : separation_quotient α → β :=
  if h : UniformContinuous f then Quotientₓ.lift f fun x y => eq_of_separated_of_uniform_continuous h else
    fun x => f (Nonempty.some ⟨x.out⟩)

theorem lift_mk [SeparatedSpace β] {f : α → β} (h : UniformContinuous f) (a : α) : lift f («expr⟦ ⟧» a) = f a :=
  by 
    rw [lift, dif_pos h] <;> rfl

theorem uniform_continuous_lift [SeparatedSpace β] (f : α → β) : UniformContinuous (lift f) :=
  by 
    byCases' hf : UniformContinuous f
    ·
      rw [lift, dif_pos hf]
      exact uniform_continuous_quotient_lift hf
    ·
      rw [lift, dif_neg hf]
      exact uniform_continuous_of_const fun a b => rfl

/-- The separation quotient functor acting on functions. -/
def map (f : α → β) : separation_quotient α → separation_quotient β :=
  lift (Quotientₓ.mk ∘ f)

theorem map_mk {f : α → β} (h : UniformContinuous f) (a : α) : map f («expr⟦ ⟧» a) = «expr⟦ ⟧» (f a) :=
  by 
    rw [map, lift_mk (uniform_continuous_quotient_mk.comp h)]

theorem uniform_continuous_map (f : α → β) : UniformContinuous (map f) :=
  uniform_continuous_lift (Quotientₓ.mk ∘ f)

theorem map_unique {f : α → β} (hf : UniformContinuous f) {g : separation_quotient α → separation_quotient β}
  (comm : (Quotientₓ.mk ∘ f) = (g ∘ Quotientₓ.mk)) : map f = g :=
  by 
    ext ⟨a⟩ <;> calc map f («expr⟦ ⟧» a) = «expr⟦ ⟧» (f a) := map_mk hf a _ = g («expr⟦ ⟧» a) := congr_funₓ comm a

theorem map_id : map (@id α) = id :=
  map_unique uniform_continuous_id rfl

theorem map_comp {f : α → β} {g : β → γ} (hf : UniformContinuous f) (hg : UniformContinuous g) :
  (map g ∘ map f) = map (g ∘ f) :=
  (map_unique (hg.comp hf)$
      by 
        simp only [· ∘ ·, map_mk, hf, hg]).symm

end SeparationQuotient

-- error in Topology.UniformSpace.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem separation_prod
{a₁ a₂ : α}
{b₁ b₂ : β} : «expr ↔ »(«expr ≈ »((a₁, b₁), (a₂, b₂)), «expr ∧ »(«expr ≈ »(a₁, a₂), «expr ≈ »(b₁, b₂))) :=
begin
  split,
  { assume [binders (h)],
    exact [expr ⟨separated_of_uniform_continuous uniform_continuous_fst h, separated_of_uniform_continuous uniform_continuous_snd h⟩] },
  { rintros ["⟨", ident eqv_α, ",", ident eqv_β, "⟩", ident r, ident r_in],
    rw [expr uniformity_prod] ["at", ident r_in],
    rcases [expr r_in, "with", "⟨", ident t_α, ",", "⟨", ident r_α, ",", ident r_α_in, ",", ident h_α, "⟩", ",", ident t_β, ",", "⟨", ident r_β, ",", ident r_β_in, ",", ident h_β, "⟩", ",", ident rfl, "⟩"],
    let [ident p_α] [] [":=", expr λ p : «expr × »(«expr × »(α, β), «expr × »(α, β)), (p.1.1, p.2.1)],
    let [ident p_β] [] [":=", expr λ p : «expr × »(«expr × »(α, β), «expr × »(α, β)), (p.1.2, p.2.2)],
    have [ident key_α] [":", expr «expr ∈ »(p_α ((a₁, b₁), (a₂, b₂)), r_α)] [],
    { simp [] [] [] ["[", expr p_α, ",", expr eqv_α r_α r_α_in, "]"] [] [] },
    have [ident key_β] [":", expr «expr ∈ »(p_β ((a₁, b₁), (a₂, b₂)), r_β)] [],
    { simp [] [] [] ["[", expr p_β, ",", expr eqv_β r_β r_β_in, "]"] [] [] },
    exact [expr ⟨h_α key_α, h_β key_β⟩] }
end

instance separated.prod [SeparatedSpace α] [SeparatedSpace β] : SeparatedSpace (α × β) :=
  separated_def.2$
    fun x y H =>
      Prod.extₓ (eq_of_separated_of_uniform_continuous uniform_continuous_fst H)
        (eq_of_separated_of_uniform_continuous uniform_continuous_snd H)

theorem _root_.is_separated.prod {s : Set α} {t : Set β} (hs : IsSeparated s) (ht : IsSeparated t) :
  IsSeparated (s.prod t) :=
  (is_separated_def _).mpr$
    fun x y hx hy H =>
      Prod.extₓ (hs.eq_of_uniform_continuous hx.1 hy.1 uniform_continuous_fst H)
        (ht.eq_of_uniform_continuous hx.2 hy.2 uniform_continuous_snd H)

end UniformSpace

