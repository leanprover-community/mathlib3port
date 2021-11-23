import Mathbin.Topology.Separation

/-!
# Extending a function from a subset

The main definition of this file is `extend_from A f` where `f : X → Y`
and `A : set X`. This defines a new function `g : X → Y` which maps any
`x₀ : X` to the limit of `f` as `x` tends to `x₀`, if such a limit exists.

This is analoguous to the way `dense_inducing.extend` "extends" a function
`f : X → Z` to a function `g : Y → Z` along a dense inducing `i : X → Y`.

The main theorem we prove about this definition is `continuous_on_extend_from`
which states that, for `extend_from A f` to be continuous on a set `B ⊆ closure A`,
it suffices that `f` converges within `A` at any point of `B`, provided that
`f` is a function to a regular space.

-/


noncomputable theory

open_locale TopologicalSpace

open Filter Set

variable{X Y : Type _}[TopologicalSpace X][TopologicalSpace Y]

/-- Extend a function from a set `A`. The resulting function `g` is such that
at any `x₀`, if `f` converges to some `y` as `x` tends to `x₀` within `A`,
then `g x₀` is defined to be one of these `y`. Else, `g x₀` could be anything. -/
def extendFrom (A : Set X) (f : X → Y) : X → Y :=
  fun x => @limₓ _ ⟨f x⟩ (𝓝[A] x) f

/-- If `f` converges to some `y` as `x` tends to `x₀` within `A`,
then `f` tends to `extend_from A f x` as `x` tends to `x₀`. -/
theorem tendsto_extend_from {A : Set X} {f : X → Y} {x : X} (h : ∃ y, tendsto f (𝓝[A] x) (𝓝 y)) :
  tendsto f (𝓝[A] x) (𝓝$ extendFrom A f x) :=
  tendsto_nhds_lim h

-- error in Topology.ExtendFrom: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem extend_from_eq
[t2_space Y]
{A : set X}
{f : X → Y}
{x : X}
{y : Y}
(hx : «expr ∈ »(x, closure A))
(hf : tendsto f «expr𝓝[ ] »(A, x) (expr𝓝() y)) : «expr = »(extend_from A f x, y) :=
begin
  haveI [] [] [":=", expr mem_closure_iff_nhds_within_ne_bot.mp hx],
  exact [expr tendsto_nhds_unique (tendsto_nhds_lim ⟨y, hf⟩) hf]
end

theorem extend_from_extends [T2Space Y] {f : X → Y} {A : Set X} (hf : ContinuousOn f A) :
  ∀ x _ : x ∈ A, extendFrom A f x = f x :=
  fun x x_in => extend_from_eq (subset_closure x_in) (hf x x_in)

-- error in Topology.ExtendFrom: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` is a function to a regular space `Y` which has a limit within `A` at any
point of a set `B ⊆ closure A`, then `extend_from A f` is continuous on `B`. -/
theorem continuous_on_extend_from
[regular_space Y]
{f : X → Y}
{A B : set X}
(hB : «expr ⊆ »(B, closure A))
(hf : ∀ x «expr ∈ » B, «expr∃ , »((y), tendsto f «expr𝓝[ ] »(A, x) (expr𝓝() y))) : continuous_on (extend_from A f) B :=
begin
  set [] [ident φ] [] [":="] [expr extend_from A f] [],
  intros [ident x, ident x_in],
  suffices [] [":", expr ∀ V' «expr ∈ » expr𝓝() (φ x), is_closed V' → «expr ∈ »(«expr ⁻¹' »(φ, V'), «expr𝓝[ ] »(B, x))],
  by simpa [] [] [] ["[", expr continuous_within_at, ",", expr (closed_nhds_basis _).tendsto_right_iff, "]"] [] [],
  intros [ident V', ident V'_in, ident V'_closed],
  obtain ["⟨", ident V, ",", ident V_in, ",", ident V_op, ",", ident hV, "⟩", ":", expr «expr∃ , »((V «expr ∈ » expr𝓝() x), «expr ∧ »(is_open V, «expr ⊆ »(«expr ∩ »(V, A), «expr ⁻¹' »(f, V'))))],
  { have [] [] [":=", expr tendsto_extend_from (hf x x_in)],
    rcases [expr (nhds_within_basis_open x A).tendsto_left_iff.mp this V' V'_in, "with", "⟨", ident V, ",", "⟨", ident hxV, ",", ident V_op, "⟩", ",", ident hV, "⟩"],
    use ["[", expr V, ",", expr is_open.mem_nhds V_op hxV, ",", expr V_op, ",", expr hV, "]"] },
  suffices [] [":", expr ∀ y «expr ∈ » «expr ∩ »(V, B), «expr ∈ »(φ y, V')],
  from [expr mem_of_superset «expr $ »(inter_mem_inf V_in, mem_principal_self B) this],
  rintros [ident y, "⟨", ident hyV, ",", ident hyB, "⟩"],
  haveI [] [] [":=", expr mem_closure_iff_nhds_within_ne_bot.mp (hB hyB)],
  have [ident limy] [":", expr tendsto f «expr𝓝[ ] »(A, y) «expr $ »(expr𝓝(), φ y)] [":=", expr tendsto_extend_from (hf y hyB)],
  have [ident hVy] [":", expr «expr ∈ »(V, expr𝓝() y)] [":=", expr is_open.mem_nhds V_op hyV],
  have [] [":", expr «expr ∈ »(«expr ∩ »(V, A), «expr𝓝[ ] »(A, y))] [],
  by simpa [] [] [] ["[", expr inter_comm, "]"] [] ["using", expr inter_mem_nhds_within _ hVy],
  exact [expr V'_closed.mem_of_tendsto limy (mem_of_superset this hV)]
end

/-- If a function `f` to a regular space `Y` has a limit within a
dense set `A` for any `x`, then `extend_from A f` is continuous. -/
theorem continuous_extend_from [RegularSpace Y] {f : X → Y} {A : Set X} (hA : Dense A)
  (hf : ∀ x, ∃ y, tendsto f (𝓝[A] x) (𝓝 y)) : Continuous (extendFrom A f) :=
  by 
    rw [continuous_iff_continuous_on_univ]
    exact
      continuous_on_extend_from (fun x _ => hA x)
        (by 
          simpa using hf)

