import Mathbin.Topology.Category.Profinite.Default 
import Mathbin.Topology.LocallyConstant.Basic 
import Mathbin.Topology.DiscreteQuotient

/-!
# Cofiltered limits of profinite sets.

This file contains some theorems about cofiltered limits of profinite sets.

## Main Results

- `exists_clopen_of_cofiltered` shows that any clopen set in a cofiltered limit of profinite
  sets is the pullback of a clopen set from one of the factors in the limit.
- `exists_locally_constant` shows that any locally constant function from a cofiltered limit
  of profinite sets factors through one of the components.
-/


namespace Profinite

open_locale Classical

open CategoryTheory

open CategoryTheory.Limits

universe u

variable{J : Type u}[small_category J][is_cofiltered J]{F : J ⥤ Profinite.{u}}(C : cone F)(hC : is_limit C)

include hC

-- error in Topology.Category.Profinite.CofilteredLimit: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/--
If `X` is a cofiltered limit of profinite sets, then any clopen subset of `X` arises from
a clopen set in one of the terms in the limit.
-/
theorem exists_clopen_of_cofiltered
{U : set C.X}
(hU : is_clopen U) : «expr∃ , »((j : J)
 (V : set (F.obj j))
 (hV : is_clopen V), «expr = »(U, «expr ⁻¹' »(C.π.app j, V))) :=
begin
  have [ident hB] [] [":=", expr Top.is_topological_basis_cofiltered_limit «expr ⋙ »(F, Profinite.to_Top) (Profinite.to_Top.map_cone C) (is_limit_of_preserves _ hC) (λ
    j, {W | is_clopen W}) _ (λ i, is_clopen_univ) (λ i U1 U2 hU1 hU2, hU1.inter hU2) _],
  rotate,
  { intros [ident i],
    change [expr topological_space.is_topological_basis {W : set (F.obj i) | is_clopen W}] [] [],
    apply [expr is_topological_basis_clopen] },
  { rintros [ident i, ident j, ident f, ident V, "(", ident hV, ":", expr is_clopen _, ")"],
    refine [expr ⟨hV.1.preimage _, hV.2.preimage _⟩]; continuity [] [] },
  obtain ["⟨", ident S, ",", ident hS, ",", ident h, "⟩", ":=", expr hB.open_eq_sUnion hU.1],
  clear [ident hB],
  let [ident j] [":", expr S → J] [":=", expr λ s, (hS s.2).some],
  let [ident V] [":", expr ∀ s : S, set (F.obj (j s))] [":=", expr λ s, (hS s.2).some_spec.some],
  have [ident hV] [":", expr ∀
   s : S, «expr ∧ »(is_clopen (V s), «expr = »(s.1, «expr ⁻¹' »(C.π.app (j s), V s)))] [":=", expr λ
   s, (hS s.2).some_spec.some_spec],
  have [] [] [":=", expr hU.2.is_compact.elim_finite_subcover (λ s : S, «expr ⁻¹' »(C.π.app (j s), V s)) _ _],
  rotate,
  { intros [ident s],
    refine [expr (hV s).1.1.preimage _],
    continuity [] [] },
  { dsimp ["only"] [] [] [],
    rw [expr h] [],
    rintro [ident x, "⟨", ident T, ",", ident hT, ",", ident hx, "⟩"],
    refine [expr ⟨_, ⟨⟨T, hT⟩, rfl⟩, _⟩],
    dsimp ["only"] [] [] [],
    rwa ["<-", expr (hV ⟨T, hT⟩).2] [] },
  obtain ["⟨", ident G, ",", ident hG, "⟩", ":=", expr this],
  obtain ["⟨", ident j0, ",", ident hj0, "⟩", ":=", expr is_cofiltered.inf_objs_exists (G.image j)],
  let [ident f] [":", expr ∀
   (s : S)
   (hs : «expr ∈ »(s, G)), «expr ⟶ »(j0, j s)] [":=", expr λ s hs, (hj0 (finset.mem_image.mpr ⟨s, hs, rfl⟩)).some],
  let [ident W] [":", expr S → set (F.obj j0)] [":=", expr λ
   s, if hs : «expr ∈ »(s, G) then «expr ⁻¹' »(F.map (f s hs), V s) else set.univ],
  refine [expr ⟨j0, «expr⋃ , »((s : S) (hs : «expr ∈ »(s, G)), W s), _, _⟩],
  { apply [expr is_clopen_bUnion],
    intros [ident s, ident hs],
    dsimp ["only"] ["[", expr W, "]"] [] [],
    rw [expr dif_pos hs] [],
    refine [expr ⟨(hV s).1.1.preimage _, (hV s).1.2.preimage _⟩]; continuity [] [] },
  { ext [] [ident x] [],
    split,
    { intro [ident hx],
      simp_rw ["[", expr set.preimage_Union, ",", expr set.mem_Union, "]"] [],
      obtain ["⟨", "_", ",", "⟨", ident s, ",", ident rfl, "⟩", ",", "_", ",", "⟨", ident hs, ",", ident rfl, "⟩", ",", ident hh, "⟩", ":=", expr hG hx],
      refine [expr ⟨s, hs, _⟩],
      dsimp ["only"] ["[", expr W, "]"] [] ["at", ident hh, "⊢"],
      rwa ["[", expr dif_pos hs, ",", "<-", expr set.preimage_comp, ",", "<-", expr Profinite.coe_comp, ",", expr C.w, "]"] [] },
    { intro [ident hx],
      simp_rw ["[", expr set.preimage_Union, ",", expr set.mem_Union, "]"] ["at", ident hx],
      obtain ["⟨", ident s, ",", ident hs, ",", ident hx, "⟩", ":=", expr hx],
      rw [expr h] [],
      refine [expr ⟨s.1, s.2, _⟩],
      rw [expr (hV s).2] [],
      dsimp ["only"] ["[", expr W, "]"] [] ["at", ident hx],
      rwa ["[", expr dif_pos hs, ",", "<-", expr set.preimage_comp, ",", "<-", expr Profinite.coe_comp, ",", expr C.w, "]"] ["at", ident hx] } }
end

-- error in Topology.Category.Profinite.CofilteredLimit: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_locally_constant_fin_two
(f : locally_constant C.X (fin 2)) : «expr∃ , »((j : J)
 (g : locally_constant (F.obj j) (fin 2)), «expr = »(f, g.comap (C.π.app _))) :=
begin
  let [ident U] [] [":=", expr «expr ⁻¹' »(f, {0})],
  have [ident hU] [":", expr is_clopen U] [":=", expr f.is_locally_constant.is_clopen_fiber _],
  obtain ["⟨", ident j, ",", ident V, ",", ident hV, ",", ident h, "⟩", ":=", expr exists_clopen_of_cofiltered C hC hU],
  use ["[", expr j, ",", expr locally_constant.of_clopen hV, "]"],
  apply [expr locally_constant.locally_constant_eq_of_fiber_zero_eq],
  rw [expr locally_constant.coe_comap _ _ (C.π.app j).continuous] [],
  conv_rhs [] [] { rw [expr set.preimage_comp] },
  rw ["[", expr locally_constant.of_clopen_fiber_zero hV, ",", "<-", expr h, "]"] []
end

-- error in Topology.Category.Profinite.CofilteredLimit: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_locally_constant_fintype_aux
{α : Type*}
[fintype α]
(f : locally_constant C.X α) : «expr∃ , »((j : J)
 (g : locally_constant (F.obj j) (α → fin 2)), «expr = »(f.map (λ
   a b, if «expr = »(a, b) then (0 : fin 2) else 1), g.comap (C.π.app _))) :=
begin
  let [ident ι] [":", expr α → α → fin 2] [":=", expr λ x y, if «expr = »(x, y) then 0 else 1],
  let [ident ff] [] [":=", expr (f.map ι).flip],
  have [ident hff] [] [":=", expr λ a : α, exists_locally_constant_fin_two _ hC (ff a)],
  choose [] [ident j] [ident g, ident h] ["using", expr hff],
  let [ident G] [":", expr finset J] [":=", expr finset.univ.image j],
  obtain ["⟨", ident j0, ",", ident hj0, "⟩", ":=", expr is_cofiltered.inf_objs_exists G],
  have [ident hj] [":", expr ∀ a, «expr ∈ »(j a, G)] [],
  { intros [ident a],
    simp [] [] [] ["[", expr G, "]"] [] [] },
  let [ident fs] [":", expr ∀ a : α, «expr ⟶ »(j0, j a)] [":=", expr λ a, (hj0 (hj a)).some],
  let [ident gg] [":", expr α → locally_constant (F.obj j0) (fin 2)] [":=", expr λ a, (g a).comap (F.map (fs _))],
  let [ident ggg] [] [":=", expr locally_constant.unflip gg],
  refine [expr ⟨j0, ggg, _⟩],
  have [] [":", expr «expr = »(f.map ι, locally_constant.unflip (f.map ι).flip)] [],
  by simp [] [] [] [] [] [],
  rw [expr this] [],
  clear [ident this],
  have [] [":", expr «expr = »(locally_constant.comap (C.π.app j0) ggg, locally_constant.unflip (locally_constant.comap (C.π.app j0) ggg).flip)] [],
  by simp [] [] [] [] [] [],
  rw [expr this] [],
  clear [ident this],
  congr' [1] [],
  ext1 [] [ident a],
  change [expr «expr = »(ff a, _)] [] [],
  rw [expr h] [],
  dsimp [] ["[", expr ggg, ",", expr gg, "]"] [] [],
  ext1 [] [],
  repeat { rw [expr locally_constant.coe_comap] [],
    dsimp [] ["[", expr locally_constant.flip, ",", expr locally_constant.unflip, "]"] [] [] },
  { congr' [1] [],
    change [expr «expr = »(_, «expr ≫ »(C.π.app j0, F.map (fs a)) x)] [] [],
    rw [expr C.w] [] },
  all_goals { continuity [] [] }
end

-- error in Topology.Category.Profinite.CofilteredLimit: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_locally_constant_fintype_nonempty
{α : Type*}
[fintype α]
[nonempty α]
(f : locally_constant C.X α) : «expr∃ , »((j : J)
 (g : locally_constant (F.obj j) α), «expr = »(f, g.comap (C.π.app _))) :=
begin
  inhabit [expr α] [],
  obtain ["⟨", ident j, ",", ident gg, ",", ident h, "⟩", ":=", expr exists_locally_constant_fintype_aux _ hC f],
  let [ident ι] [":", expr α → α → fin 2] [":=", expr λ a b, if «expr = »(a, b) then 0 else 1],
  let [ident σ] [":", expr (α → fin 2) → α] [":=", expr λ
   f, if h : «expr∃ , »((a : α), «expr = »(ι a, f)) then h.some else arbitrary _],
  refine [expr ⟨j, gg.map σ, _⟩],
  ext [] [] [],
  rw [expr locally_constant.coe_comap _ _ (C.π.app j).continuous] [],
  dsimp [] ["[", expr σ, "]"] [] [],
  have [ident h1] [":", expr «expr = »(ι (f x), gg (C.π.app j x))] [],
  { change [expr «expr = »(f.map (λ a b, if «expr = »(a, b) then (0 : fin 2) else 1) x, _)] [] [],
    rw ["[", expr h, ",", expr locally_constant.coe_comap _ _ (C.π.app j).continuous, "]"] [] },
  have [ident h2] [":", expr «expr∃ , »((a : α), «expr = »(ι a, gg (C.π.app j x)))] [":=", expr ⟨f x, h1⟩],
  rw [expr dif_pos h2] [],
  apply_fun [expr ι] [] [],
  { rw [expr h2.some_spec] [],
    exact [expr h1] },
  { intros [ident a, ident b, ident hh],
    apply_fun [expr λ e, e a] ["at", ident hh] [],
    dsimp [] ["[", expr ι, "]"] [] ["at", ident hh],
    rw [expr if_pos rfl] ["at", ident hh],
    split_ifs ["at", ident hh] ["with", ident hh1, ident hh1],
    { exact [expr hh1.symm] },
    { exact [expr false.elim (bot_ne_top hh)] } }
end

-- error in Topology.Category.Profinite.CofilteredLimit: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any locally constant function from a cofiltered limit of profinite sets factors through
one of the components. -/
theorem exists_locally_constant
{α : Type*}
(f : locally_constant C.X α) : «expr∃ , »((j : J)
 (g : locally_constant (F.obj j) α), «expr = »(f, g.comap (C.π.app _))) :=
begin
  let [ident S] [] [":=", expr f.discrete_quotient],
  let [ident ff] [":", expr S → α] [":=", expr f.lift],
  casesI [expr is_empty_or_nonempty S] [],
  { suffices [] [":", expr «expr∃ , »((j), is_empty (F.obj j))],
    { refine [expr this.imp (λ j hj, _)],
      refine [expr ⟨⟨hj.elim, λ A, _⟩, _⟩],
      { convert [] [expr is_open_empty] [],
        exact [expr @set.eq_empty_of_is_empty _ hj _] },
      { ext [] [ident x] [],
        exact [expr hj.elim' (C.π.app j x)] } },
    simp [] [] ["only"] ["[", "<-", expr not_nonempty_iff, ",", "<-", expr not_forall, "]"] [] [],
    intros [ident h],
    haveI [] [":", expr ∀ j : J, nonempty («expr ⋙ »(F, Profinite.to_Top).obj j)] [":=", expr h],
    haveI [] [":", expr ∀
     j : J, t2_space («expr ⋙ »(F, Profinite.to_Top).obj j)] [":=", expr λ j, (infer_instance : t2_space (F.obj j))],
    haveI [] [":", expr ∀
     j : J, compact_space («expr ⋙ »(F, Profinite.to_Top).obj j)] [":=", expr λ
     j, (infer_instance : compact_space (F.obj j))],
    have [ident cond] [] [":=", expr Top.nonempty_limit_cone_of_compact_t2_cofiltered_system «expr ⋙ »(F, Profinite.to_Top)],
    suffices [] [":", expr nonempty C.X],
    from [expr is_empty.false (S.proj this.some)],
    let [ident D] [] [":=", expr Profinite.to_Top.map_cone C],
    have [ident hD] [":", expr is_limit D] [":=", expr is_limit_of_preserves Profinite.to_Top hC],
    have [ident CD] [] [":=", expr (hD.cone_point_unique_up_to_iso (Top.limit_cone_is_limit _)).inv],
    exact [expr cond.map CD] },
  { let [ident f'] [":", expr locally_constant C.X S] [":=", expr ⟨S.proj, S.proj_is_locally_constant⟩],
    obtain ["⟨", ident j, ",", ident g', ",", ident hj, "⟩", ":=", expr exists_locally_constant_fintype_nonempty _ hC f'],
    refine [expr ⟨j, ⟨«expr ∘ »(ff, g'), g'.is_locally_constant.comp _⟩, _⟩],
    ext1 [] [ident t],
    apply_fun [expr λ e, e t] ["at", ident hj] [],
    rw [expr locally_constant.coe_comap _ _ (C.π.app j).continuous] ["at", ident hj, "⊢"],
    dsimp [] [] [] ["at", ident hj, "⊢"],
    rw ["<-", expr hj] [],
    refl }
end

end Profinite

