import Mathbin.Topology.Algebra.Ordered.Basic 
import Mathbin.Algebra.Order.WithZero

/-!
# The topology on linearly ordered commutative groups with zero

Let `Γ₀` be a linearly ordered commutative group to which we have adjoined a zero element.
Then `Γ₀` may naturally be endowed with a topology that turns `Γ₀` into a topological monoid.
Neighborhoods of zero are sets containing `{γ | γ < γ₀}` for some invertible element `γ₀`
and every invertible element is open.
In particular the topology is the following:
"a subset `U ⊆ Γ₀` is open if `0 ∉ U` or if there is an invertible
`γ₀ ∈ Γ₀ such that {γ | γ < γ₀} ⊆ U`", but this fact is not proven here since the neighborhoods
description is what is actually useful.

We prove this topology is ordered and regular (in addition to be compatible with the monoid
structure).

All this is useful to extend a valuation to a completion. This is an abstract version of how the
absolute value (resp. `p`-adic absolute value) on `ℚ` is extended to `ℝ` (resp. `ℚₚ`).

## Implementation notes

This topology is not defined as an instance since it may not be the desired topology on
a linearly ordered commutative group with zero. You can locally activate this topology using
`local attribute [instance] linear_ordered_comm_group_with_zero.topological_space`
All other instances will (`ordered_topology`, `regular_space`, `has_continuous_mul`) then follow.

-/


open_locale TopologicalSpace

open TopologicalSpace Filter Set

namespace LinearOrderedCommGroupWithZero

variable(Γ₀ : Type _)[LinearOrderedCommGroupWithZero Γ₀]

/-- The neighbourhoods around γ ∈ Γ₀, used in the definition of the topology on Γ₀.
These neighbourhoods are defined as follows:
A set s is a neighbourhood of 0 if there is an invertible γ₀ ∈ Γ₀ such that {γ | γ < γ₀} ⊆ s.
If γ ≠ 0, then every set that contains γ is a neighbourhood of γ. -/
def nhds_fun (x : Γ₀) : Filter Γ₀ :=
  if x = 0 then ⨅γ₀ : Units Γ₀, principal { γ | γ < γ₀ } else pure x

/-- The topology on a linearly ordered commutative group with a zero element adjoined.
A subset U is open if 0 ∉ U or if there is an invertible element γ₀ such that {γ | γ < γ₀} ⊆ U. -/
protected def TopologicalSpace : TopologicalSpace Γ₀ :=
  TopologicalSpace.mkOfNhds (nhds_fun Γ₀)

attribute [local instance] LinearOrderedCommGroupWithZero.topologicalSpace

-- error in Topology.Algebra.WithZeroTopology: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The neighbourhoods {γ | γ < γ₀} of 0 form a directed set indexed by the invertible 
elements γ₀. -/ theorem directed_lt : directed ((«expr ≥ »)) (λ γ₀ : units Γ₀, principal {γ : Γ₀ | «expr < »(γ, γ₀)}) :=
begin
  intros [ident γ₁, ident γ₂],
  use [expr linear_order.min γ₁ γ₂]; dsimp ["only"] [] [] [],
  split; rw ["[", expr ge_iff_le, ",", expr principal_mono, "]"] []; intros [ident x, ident x_in],
  { calc
      «expr < »(x, «expr↑ »(linear_order.min γ₁ γ₂)) : x_in
      «expr ≤ »(..., γ₁) : min_le_left γ₁ γ₂ },
  { calc
      «expr < »(x, «expr↑ »(linear_order.min γ₁ γ₂)) : x_in
      «expr ≤ »(..., γ₂) : min_le_right γ₁ γ₂ }
end

/-- At all points of a linearly ordered commutative group with a zero element adjoined,
the pure filter is smaller than the filter given by nhds_fun. -/
theorem pure_le_nhds_fun : pure ≤ nhds_fun Γ₀ :=
  fun x =>
    by 
      byCases' hx : x = 0 <;> simp [hx, nhds_fun]

/-- For every point Γ₀, and every “neighbourhood” s of it (described by nhds_fun), there is a
smaller “neighbourhood” t ⊆ s, such that s is a “neighbourhood“ of all the points in t. -/
theorem nhds_fun_ok (x : Γ₀) {s} (s_in : s ∈ nhds_fun Γ₀ x) :
  ∃ (t : _)(_ : t ∈ nhds_fun Γ₀ x), t ⊆ s ∧ ∀ y (_ : y ∈ t), s ∈ nhds_fun Γ₀ y :=
  by 
    byCases' hx : x = 0
    ·
      simp only [hx, nhds_fun, exists_prop, if_true, eq_self_iff_true] at s_in⊢
      cases' (mem_infi_of_directed (directed_lt Γ₀) _).mp s_in with γ₀ h 
      use { γ:Γ₀ | γ < γ₀ }
      rw [mem_principal] at h 
      split 
      ·
        apply mem_infi_of_mem γ₀ 
        rw [mem_principal]
      ·
        refine' ⟨h, fun y y_in => _⟩
        byCases' hy : y = 0
        ·
          simp only [hy, if_true, eq_self_iff_true]
          apply mem_infi_of_mem γ₀ 
          rwa [mem_principal]
        ·
          simp [hy, h y_in]
    ·
      simp only [hx, nhds_fun, exists_prop, if_false, mem_pure] at s_in⊢
      refine' ⟨{x}, mem_singleton _, singleton_subset_iff.2 s_in, fun y y_in => _⟩
      simpa [mem_singleton_iff.mp y_in, hx]

variable{Γ₀}

/-- The neighbourhood filter of an invertible element consists of all sets containing that 
element. -/
theorem nhds_coe_units (γ : Units Γ₀) : 𝓝 (γ : Γ₀) = pure (γ : Γ₀) :=
  calc 𝓝 (γ : Γ₀) = nhds_fun Γ₀ γ := nhds_mk_of_nhds (nhds_fun Γ₀) γ (pure_le_nhds_fun Γ₀) (nhds_fun_ok Γ₀)
    _ = pure (γ : Γ₀) := if_neg γ.ne_zero
    

/-- The neighbourhood filter of a nonzero element consists of all sets containing that 
element. -/
@[simp]
theorem nhds_of_ne_zero (γ : Γ₀) (h : γ ≠ 0) : 𝓝 γ = pure γ :=
  nhds_coe_units (Units.mk0 _ h)

/-- If γ is an invertible element of a linearly ordered group with zero element adjoined,
then {γ} is a neighbourhood of γ. -/
theorem singleton_nhds_of_units (γ : Units Γ₀) : ({γ} : Set Γ₀) ∈ 𝓝 (γ : Γ₀) :=
  by 
    simp 

/-- If γ is a nonzero element of a linearly ordered group with zero element adjoined,
then {γ} is a neighbourhood of γ. -/
theorem singleton_nhds_of_ne_zero (γ : Γ₀) (h : γ ≠ 0) : ({γ} : Set Γ₀) ∈ 𝓝 (γ : Γ₀) :=
  by 
    simp [h]

-- error in Topology.Algebra.WithZeroTopology: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- If U is a neighbourhood of 0 in a linearly ordered group with zero element adjoined,
then there exists an invertible element γ₀ such that {γ | γ < γ₀} ⊆ U. -/
theorem has_basis_nhds_zero : has_basis (expr𝓝() (0 : Γ₀)) (λ _, true) (λ γ₀ : units Γ₀, {γ : Γ₀ | «expr < »(γ, γ₀)}) :=
⟨begin
   intro [ident U],
   rw [expr nhds_mk_of_nhds (nhds_fun Γ₀) 0 (pure_le_nhds_fun Γ₀) (nhds_fun_ok Γ₀)] [],
   simp [] [] ["only"] ["[", expr nhds_fun, ",", expr if_true, ",", expr eq_self_iff_true, ",", expr exists_true_left, "]"] [] [],
   simp_rw ["[", expr mem_infi_of_directed (directed_lt Γ₀), ",", expr mem_principal, "]"] []
 end⟩

/-- If γ is an invertible element of a linearly ordered group with zero element adjoined,
then {x | x < γ} is a neighbourhood of 0. -/
theorem nhds_zero_of_units (γ : Units Γ₀) : { x:Γ₀ | x < γ } ∈ 𝓝 (0 : Γ₀) :=
  by 
    rw [has_basis_nhds_zero.mem_iff]
    use γ 
    simp 

theorem tendsto_zero {α : Type _} {F : Filter α} {f : α → Γ₀} :
  tendsto f F (𝓝 (0 : Γ₀)) ↔ ∀ (γ₀ : Units Γ₀), { x:α | f x < γ₀ } ∈ F :=
  by 
    simpa using has_basis_nhds_zero.tendsto_right_iff

/-- If γ is a nonzero element of a linearly ordered group with zero element adjoined,
then {x | x < γ} is a neighbourhood of 0. -/
theorem nhds_zero_of_ne_zero (γ : Γ₀) (h : γ ≠ 0) : { x:Γ₀ | x < γ } ∈ 𝓝 (0 : Γ₀) :=
  nhds_zero_of_units (Units.mk0 _ h)

-- error in Topology.Algebra.WithZeroTopology: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem has_basis_nhds_units (γ : units Γ₀) : has_basis (expr𝓝() (γ : Γ₀)) (λ i : unit, true) (λ i, {γ}) :=
begin
  rw [expr nhds_of_ne_zero _ γ.ne_zero] [],
  exact [expr has_basis_pure γ]
end

-- error in Topology.Algebra.WithZeroTopology: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem has_basis_nhds_of_ne_zero
{x : Γ₀}
(h : «expr ≠ »(x, 0)) : has_basis (expr𝓝() x) (λ i : unit, true) (λ i, {x}) :=
has_basis_nhds_units (units.mk0 x h)

theorem tendsto_units {α : Type _} {F : Filter α} {f : α → Γ₀} {γ₀ : Units Γ₀} :
  tendsto f F (𝓝 (γ₀ : Γ₀)) ↔ { x:α | f x = γ₀ } ∈ F :=
  by 
    rw [(has_basis_nhds_units γ₀).tendsto_right_iff]
    simpa

theorem tendsto_of_ne_zero {α : Type _} {F : Filter α} {f : α → Γ₀} {γ : Γ₀} (h : γ ≠ 0) :
  tendsto f F (𝓝 γ) ↔ { x:α | f x = γ } ∈ F :=
  @tendsto_units _ _ _ F f (Units.mk0 γ h)

variable(Γ₀)

-- error in Topology.Algebra.WithZeroTopology: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The topology on a linearly ordered group with zero element adjoined
is compatible with the order structure. -/ @[priority 100] instance ordered_topology : order_closed_topology Γ₀ :=
{ is_closed_le' := begin
    rw ["<-", expr is_open_compl_iff] [],
    show [expr is_open {p : «expr × »(Γ₀, Γ₀) | «expr¬ »(«expr ≤ »(p.fst, p.snd))}],
    simp [] [] ["only"] ["[", expr not_le, "]"] [] [],
    rw [expr is_open_iff_mem_nhds] [],
    rintros ["⟨", ident a, ",", ident b, "⟩", ident hab],
    change [expr «expr < »(b, a)] [] ["at", ident hab],
    have [ident ha] [":", expr «expr ≠ »(a, 0)] [":=", expr ne_zero_of_lt hab],
    rw ["[", expr nhds_prod_eq, ",", expr mem_prod_iff, "]"] [],
    by_cases [expr hb, ":", expr «expr = »(b, 0)],
    { subst [expr b],
      use ["[", expr {a}, ",", expr singleton_nhds_of_ne_zero _ ha, ",", expr {x : Γ₀ | «expr < »(x, a)}, ",", expr nhds_zero_of_ne_zero _ ha, "]"],
      intros [ident p, ident p_in],
      cases [expr mem_prod.1 p_in] ["with", ident h1, ident h2],
      rw [expr mem_singleton_iff] ["at", ident h1],
      change [expr «expr < »(p.2, p.1)] [] [],
      rwa [expr h1] [] },
    { use ["[", expr {a}, ",", expr singleton_nhds_of_ne_zero _ ha, ",", expr {b}, ",", expr singleton_nhds_of_ne_zero _ hb, "]"],
      intros [ident p, ident p_in],
      cases [expr mem_prod.1 p_in] ["with", ident h1, ident h2],
      rw [expr mem_singleton_iff] ["at", ident h1, ident h2],
      change [expr «expr < »(p.2, p.1)] [] [],
      rwa ["[", expr h1, ",", expr h2, "]"] [] }
  end }

-- error in Topology.Algebra.WithZeroTopology: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The topology on a linearly ordered group with zero element adjoined is T₃ (aka regular). -/
@[priority 100]
instance regular_space : regular_space Γ₀ :=
begin
  haveI [] [":", expr t1_space Γ₀] [":=", expr t2_space.t1_space],
  split,
  intros [ident s, ident x, ident s_closed, ident x_not_in_s],
  by_cases [expr hx, ":", expr «expr = »(x, 0)],
  { refine [expr ⟨s, _, subset.rfl, _⟩],
    { subst [expr x],
      rw [expr is_open_iff_mem_nhds] [],
      intros [ident y, ident hy],
      by_cases [expr hy', ":", expr «expr = »(y, 0)],
      { subst [expr y],
        contradiction },
      simpa [] [] [] ["[", expr hy', "]"] [] [] },
    { erw [expr inf_eq_bot_iff] [],
      use [expr «expr ᶜ»(s)],
      simp [] [] ["only"] ["[", expr exists_prop, ",", expr mem_principal, "]"] [] [],
      exact [expr ⟨s_closed.compl_mem_nhds x_not_in_s, ⟨s, subset.refl s, by simp [] [] [] [] [] []⟩⟩] } },
  { simp [] [] ["only"] ["[", expr nhds_within, ",", expr inf_eq_bot_iff, ",", expr exists_prop, ",", expr mem_principal, "]"] [] [],
    exact [expr ⟨«expr ᶜ»({x}), is_open_compl_iff.mpr is_closed_singleton, by rwa [expr subset_compl_singleton_iff] [], {x}, singleton_nhds_of_ne_zero x hx, «expr ᶜ»({x}), by simp [] [] [] ["[", expr subset.refl, "]"] [] []⟩] }
end

-- error in Topology.Algebra.WithZeroTopology: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The topology on a linearly ordered group with zero element adjoined makes it a topological
monoid. -/ @[priority 100] instance : has_continuous_mul Γ₀ :=
⟨begin
   have [ident common] [":", expr ∀
    y «expr ≠ » (0 : Γ₀), continuous_at (λ p : «expr × »(Γ₀, Γ₀), «expr * »(p.fst, p.snd)) (0, y)] [],
   { intros [ident y, ident hy],
     set [] [ident γ] [] [":="] [expr units.mk0 y hy] [],
     suffices [] [":", expr tendsto (λ
       p : «expr × »(Γ₀, Γ₀), «expr * »(p.fst, p.snd)) ((expr𝓝() 0).prod (expr𝓝() γ)) (expr𝓝() 0)],
     by simpa [] [] [] ["[", expr continuous_at, ",", expr nhds_prod_eq, "]"] [] [],
     suffices [] [":", expr ∀
      γ' : units Γ₀, «expr∃ , »((γ'' : units Γ₀), ∀
       a b : Γ₀, «expr < »(a, γ'') → «expr = »(b, y) → «expr < »(«expr * »(a, b), γ'))],
     { rw [expr «expr $ »(has_basis_nhds_zero.prod, has_basis_nhds_units γ).tendsto_iff has_basis_nhds_zero] [],
       simpa [] [] [] [] [] [] },
     intros [ident γ'],
     use [expr «expr * »(«expr ⁻¹»(γ), γ')],
     rintros [ident a, ident b, ident ha, ident hb],
     rw ["[", expr hb, ",", expr mul_comm, "]"] [],
     rw ["[", expr units.coe_mul, "]"] ["at", ident ha],
     simpa [] [] [] [] [] ["using", expr inv_mul_lt_of_lt_mul₀ ha] },
   rw [expr continuous_iff_continuous_at] [],
   rintros ["⟨", ident x, ",", ident y, "⟩"],
   by_cases [expr hx, ":", expr «expr = »(x, 0)]; by_cases [expr hy, ":", expr «expr = »(y, 0)],
   { suffices [] [":", expr tendsto (λ p : «expr × »(Γ₀, Γ₀), «expr * »(p.fst, p.snd)) (expr𝓝() (0, 0)) (expr𝓝() 0)],
     by simpa [] [] [] ["[", expr hx, ",", expr hy, ",", expr continuous_at, "]"] [] [],
     suffices [] [":", expr ∀
      γ : units Γ₀, «expr∃ , »((γ' : units Γ₀), ∀
       a b : Γ₀, «expr < »(a, γ') → «expr < »(b, γ') → «expr < »(«expr * »(a, b), γ))],
     by simpa [] [] [] ["[", expr nhds_prod_eq, ",", expr has_basis_nhds_zero.prod_self.tendsto_iff has_basis_nhds_zero, "]"] [] [],
     intros [ident γ],
     rcases [expr exists_square_le γ, "with", "⟨", ident γ', ",", ident h, "⟩"],
     use [expr γ'],
     intros [ident a, ident b, ident ha, ident hb],
     calc
       «expr < »(«expr * »(a, b), «expr * »(γ', γ')) : mul_lt_mul₀ ha hb
       «expr ≤ »(..., γ) : by exact_mod_cast [expr h] },
   { rw [expr hx] [],
     exact [expr common y hy] },
   { rw [expr hy] [],
     have [] [":", expr «expr = »(λ
       p : «expr × »(Γ₀, Γ₀), «expr * »(p.fst, p.snd), «expr ∘ »(λ
        p : «expr × »(Γ₀, Γ₀), «expr * »(p.fst, p.snd), λ p : «expr × »(Γ₀, Γ₀), (p.2, p.1)))] [],
     by { ext [] [] [],
       rw ["[", expr mul_comm, "]"] [] },
     rw [expr this] [],
     apply [expr continuous_at.comp _ continuous_swap.continuous_at],
     exact [expr common x hx] },
   { change [expr tendsto _ _ _] [] [],
     rw ["[", expr nhds_prod_eq, "]"] [],
     rw [expr ((has_basis_nhds_of_ne_zero hx).prod (has_basis_nhds_of_ne_zero hy)).tendsto_iff «expr $ »(has_basis_nhds_of_ne_zero, mul_ne_zero hx hy)] [],
     suffices [] [":", expr ∀
      a b : Γ₀, «expr = »(a, x) → «expr = »(b, y) → «expr = »(«expr * »(a, b), «expr * »(x, y))],
     by simpa [] [] [] [] [] [],
     rintros [ident a, ident b, ident rfl, ident rfl],
     refl }
 end⟩

end LinearOrderedCommGroupWithZero

